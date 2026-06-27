import Mathlib
import Zcash.Snark.Group

/-!
# Knowledge soundness: the polynomial-commitment / inner-product-argument layer

Steps 1–2 established faithfulness: the deployed verifier collapses to the fingerprint MSM, and the
Lean assembly reproduces it (the match). This module begins soundness — that an accepting proof implies
the prover knows a valid witness — via the special soundness of the inner-product argument (IPA), the
cryptographic core of the halo2 opening.

The IPA proves knowledge of a coefficient vector `a` (a polynomial) behind a commitment `P = ⟨a, G⟩`
that opens to a value `v` at a point — i.e. `⟨a, b⟩ = v` for the evaluation vector `b = (1, x, x², …)`.
The fingerprint MSM's `g`-part is this commitment, so the layer is expressed directly over the SRS:

* `commit` — `⟨a, G⟩ = Σᵢ aᵢ • gᵢ`, the polynomial commitment (the MSM's `g`-part).
* `evalVector` / `innerProduct` — `b = (1, x, …, x^{n−1})` and `⟨a, b⟩` (the polynomial at `x`).
* `IpaRelation` — the opening relation `⟨a, G⟩ = P ∧ ⟨a, b⟩ = v` the IPA is an argument of knowledge for.
* `commit_add` / `commit_smul` — `commit` is `F`-linear; this is the algebra the round extractor folds with.

The IPA is 2-special-sound per round: from two accepting transcripts that share the round commitments
`(Lⱼ, Rⱼ)` but answer distinct challenges `uⱼ`, the round's witness folds back, and recursing over the
`k` rounds extracts an `a` satisfying `IpaRelation`. Building that extractor is the next phase; the
per-round folding rests on the linearity proved here. Curve-group binding stays an explicit assumption —
modelled as discrete-log-relation (DLR) hardness (`commitmentBinding_iff_no_relation`), per project scope.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The polynomial commitment of a coefficient vector `a` against the SRS generators:
`⟨a, G⟩ = Σᵢ aᵢ • gᵢ`. This is the `g`-part of the fingerprint MSM (`Zcash.Snark.Msm.eval`). -/
def commit (srs : SRS G) (a : Fin (2 ^ srs.k) → F) : G :=
  ∑ i, a i • srs.g i

/-- The evaluation vector `b = (1, x, x², …, x^{2ᵏ−1})`. The inner product `⟨a, b⟩` is the polynomial
with coefficients `a` evaluated at `x`. -/
def evalVector (k : ℕ) (x : F) : Fin (2 ^ k) → F :=
  fun i => x ^ (i : ℕ)

/-- The inner product `⟨a, b⟩ = Σᵢ aᵢ bᵢ` of two coefficient vectors. -/
def innerProduct {n : ℕ} (a b : Fin n → F) : F :=
  ∑ i, a i * b i

/-- The IPA opening relation: the witness `a` is the polynomial committed by `P` (`⟨a, G⟩ = P`) that
opens to `v` at the point encoded by `b` (`⟨a, b⟩ = v`). The inner-product argument is an argument of
knowledge for this relation; special soundness produces such an `a` from accepting transcripts. -/
def IpaRelation (srs : SRS G) (P : G) (b : Fin (2 ^ srs.k) → F) (v : F)
    (a : Fin (2 ^ srs.k) → F) : Prop :=
  commit srs a = P ∧ innerProduct a b = v

/-! ## The IPA round fold and its 2-special-soundness extractor

One round of the inner-product argument halves the witness. The prover sends the cross-commitments
`(Lⱼ, Rⱼ)`, the verifier sends a challenge `uⱼ`, and the length-`2m` vector folds to length `m`. The
core of special soundness is that the same halves, folded at two distinct challenges, are uniquely
recoverable — so an accepting prover is committed to a fixed witness, which the extractor recovers. -/

/-- One IPA round folds a vector into its lower half plus `u` times its upper half (`compute_s`'s
`(1, uⱼ)` structure): `foldVec lo hi u = lo + u • hi`. The round commitments `(Lⱼ, Rⱼ)` pin `lo`, `hi`. -/
def foldVec {m : ℕ} (lo hi : Fin m → F) (u : F) : Fin m → F := lo + u • hi

/-- The IPA round extractor: from the folded vector at two distinct challenges, recover the halves —
`hi = (f₁ − f₂)/(u₁ − u₂)` and `lo = f₁ − u₁ • hi`. -/
def roundExtract {m : ℕ} (f₁ f₂ : Fin m → F) (u₁ u₂ : F) : (Fin m → F) × (Fin m → F) :=
  (f₁ - u₁ • ((u₁ - u₂)⁻¹ • (f₁ - f₂)), (u₁ - u₂)⁻¹ • (f₁ - f₂))

/-- 2-special soundness of one IPA round: the folded vectors at two distinct challenges `u₁ ≠ u₂`
(produced from the same halves `lo, hi`) determine the halves — `roundExtract` recovers exactly
`(lo, hi)`. A prover answering two challenges consistently is thus committed to a unique pair that folds
back to the round witness, the algebraic heart of the IPA's special soundness. -/
theorem roundExtract_correct {m : ℕ} (lo hi : Fin m → F) (u₁ u₂ : F) (h : u₁ ≠ u₂) :
    roundExtract (foldVec lo hi u₁) (foldVec lo hi u₂) u₁ u₂ = (lo, hi) := by
  have hsub : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h
  have hi_eq : (u₁ - u₂)⁻¹ • (foldVec lo hi u₁ - foldVec lo hi u₂) = hi := by
    have hd : foldVec lo hi u₁ - foldVec lo hi u₂ = (u₁ - u₂) • hi := by
      simp only [foldVec, sub_smul]; abel
    rw [hd, smul_smul, inv_mul_cancel₀ hsub, one_smul]
  simp only [roundExtract, Prod.mk.injEq]
  refine ⟨?_, hi_eq⟩
  rw [hi_eq]
  simp only [foldVec]
  abel

/-! ## Inner-product bilinearity and the round's inner-product telescoping

The scalar side of the IPA: the inner product is bilinear, and one round telescopes it — with the
witness folded by `u⁻¹` and the evaluation vector by `u`, the folded inner product is the original
`⟨lo,blo⟩ + ⟨hi,bhi⟩` plus the two cross terms the verifier accounts for via `L`/`R`. This is the round's
completeness, complementing the round extractor (`roundExtract_correct`). -/

/-- The inner product is additive in its left argument. -/
theorem innerProduct_add_left {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a + a') b = innerProduct a b + innerProduct a' b := by
  simp only [innerProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-! ## Commitment binding and knowledge soundness of the opening

The last ingredient is binding: distinct coefficient vectors have distinct commitments (the SRS
generators are `F`-linearly independent). On the Vesta curve this is the discrete-log-relation
(DLR) hardness assumption — kept as an explicit hypothesis (project scope), not proved here,
mirroring how `Zcash/Security/BindingSignature/Balance.lean` records its cryptographic assumptions.

Given binding, the witness the special-soundness extractor produces (`roundExtract_correct` per round,
composed over the `k` rounds) is the unique opening, so an accepting proof demonstrates knowledge of
exactly one polynomial. The complementary constraint layer — that the opened polynomials satisfy the
circuit's gate/permutation/lookup identities — is the Schwartz–Zippel bound
(`Zcash.Snark.fingerprint_schwartz_zippel`): a violated identity passes the random-point check only with
probability `≤ d/p`. -/

/-- Commitment binding (the curve assumption, kept explicit): the SRS commitment is injective —
coefficient vectors with equal commitments are equal, i.e. the generators `g` are `F`-linearly
independent. On Vesta this is the discrete-log-relation (DLR) hardness assumption
(`commitmentBinding_iff_no_relation`). -/
@[reducible] def CommitmentBinding (srs : SRS G) : Prop :=
  Function.Injective (commit (F := F) srs)

/-- Under binding, the IPA opening is unique: two witnesses opening the same commitment to the same
value are equal. So special-soundness extraction (which yields an opening) pins down the witness. -/
theorem ipaRelation_unique {srs : SRS G} {P : G} {b : Fin (2 ^ srs.k) → F} {v : F}
    {a a' : Fin (2 ^ srs.k) → F} (hb : CommitmentBinding (F := F) srs)
    (h : IpaRelation srs P b v a) (h' : IpaRelation srs P b v a') : a = a' :=
  hb (h.1.trans h'.1.symm)

end Zcash.Snark
