import Mathlib
import Zcash.Snark.Msm

/-!
# The inner-product-argument opening

The IPA opening (`poly/commitment/verifier.rs`) is the last stage of the verifier's MSM assembly. It
contributes to the fingerprint MSM through two scalar computations over the `k` round challenges `uⱼ`
and a fold that accumulates the opening proof's terms:

* `computeS u init` — halo2 `compute_s`: the `2 ^ k` coefficients of `init · ∏ᵢ (1 + u_{k-1-i} X^{2ⁱ})`,
  added to the SRS-generator coefficients (with `init = -c`).
* `computeB x u` — halo2 `compute_b`: the scalar `∏ᵢ (1 + u_{k-1-i} x^{2ⁱ})`, used in the `u`-generator
  coefficient `-c · b · z`.
* `ipaFold` — the IPA opening's transformation of the incoming MSM: `[-v]` into `g₀`, `[ξ] S`, the
  per-round `[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ`, `[-c · b · z] U`, `[-f] W`, and `computeS u (-c)` into the
  `g`-scalars.

All are transcribed structurally from the Rust, so the assembled MSM matches the captured one without a
separate equivalence proof.
-/

namespace Zcash.Snark

/-- halo2 `compute_s`: the `2 ^ u.length` coefficients of `init · ∏ᵢ (1 + u_{k-1-i} · X^{2ⁱ})` — the IPA
opening's contribution to the SRS-generator coefficients. Built by the Rust's left-half doubling:
start from `[init]`, then for each round challenge (in reverse) append the current vector scaled by it. -/
def computeS {F : Type*} [CommRing F] (u : List F) (init : F) : List F :=
  u.reverse.foldl (fun v uⱼ => v ++ v.map (· * uⱼ)) [init]

/-- halo2 `compute_b`: `∏ᵢ (1 + u_{k-1-i} · x^{2ⁱ})`, the scalar in the IPA opening's `u`-generator
coefficient `-c · b · z`. The fold squares `x` each round (giving `x^{2ⁱ}`) and multiplies in the
factor `1 + uⱼ · x^{2ⁱ}`. -/
def computeB {F : Type*} [CommRing F] (x : F) (u : List F) : F :=
  (u.reverse.foldl (fun acc uⱼ => (acc.1 * (1 + uⱼ * acc.2), acc.2 * acc.2)) ((1 : F), x)).1

/-- The inner-product-argument opening's contribution to the MSM (halo2
`poly/commitment/verifier.rs`). Starting from the incoming `msm` — the multiopen commitment to be
opened at `x` to the value `v` — it adds: `[-v]` to `g₀` (`add_constant_term`); `[ξ] S`; for each round
`[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ`; the `u`-generator coefficient `-c · b · z` with `b = computeB x u`; `[-f] W`;
and `computeS u (-c)` into the `g`-scalars (`use_challenges`). `rounds` pairs `(Lⱼ, Rⱼ)` with `u`. -/
def ipaFold {F G : Type*} [Field F] {k : ℕ} (x v c f xi z : F) (u : List F)
    (S : G) (rounds : List (G × G)) (m : Msm k F G) : Msm k F G :=
  let m := m.addToGScalars [-v]
  let m := m.appendTerm xi S
  let m := (rounds.zip u).foldl
    (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m
  let m := m.addToUScalar (-c * computeB x u * z)
  let m := m.addToWScalar (-f)
  m.addToGScalars (computeS u (-c))

/-- The per-round `[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ` fold contributes exactly `Σⱼ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)` to the
evaluation. By induction over the rounds, using `Msm.eval_appendTerm`. -/
theorem eval_foldl_rounds {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (srs : SRS G) (l : List ((G × G) × F)) (m0 : Msm srs.k F G) :
    (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m0).eval srs
      = m0.eval srs + (l.map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum := by
  induction l generalizing m0 with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih]
    simp only [Msm.eval_appendTerm, List.map_cons, List.sum_cons]
    abel

/-- **The IPA opening's MSM is the IPA verification equation.** Evaluating the assembled IPA fingerprint
against the SRS yields, in clean closed form, the incoming multiopen commitment plus the verifier's IPA
contributions: `[-v]` at `g₀`, `[ξ] S`, the per-round `[uⱼ⁻¹] Lⱼ + [uⱼ] Rⱼ`, `[-c·b·z] U`, `[-f] W`, and
`computeS u (-c)` (i.e. `[-c]` times the folded generators). The deployed accept (`eval … = 0`) is exactly
this expression vanishing — a symbolic check of the §1 IPA assembly, complementing the one-proof
`native_decide` match. Proven by `Msm.eval_*` distribution + `eval_foldl_rounds`. -/
theorem eval_ipaFold {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (srs : SRS G) (x v c f xi z : F) (u : List F) (S : G) (rounds : List (G × G))
    (m : Msm srs.k F G) :
    (ipaFold x v c f xi z u S rounds m).eval srs
      = m.eval srs
        + (∑ i, ([-v].getD i.val 0) • srs.g i)
        + xi • S
        + ((rounds.zip u).map (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-c * computeB x u * z) • srs.u
        + (-f) • srs.w
        + (∑ i, ((computeS u (-c)).getD i.val 0) • srs.g i) := by
  simp only [ipaFold, Msm.eval_addToGScalars, Msm.eval_appendTerm, Msm.eval_addToUScalar,
    Msm.eval_addToWScalar, eval_foldl_rounds]

end Zcash.Snark
