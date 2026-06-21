import Mathlib
import Zcash.Snark.Group

/-!
# Knowledge soundness: the polynomial-commitment / inner-product-argument layer

Steps 1–2 established *faithfulness*: the deployed verifier collapses to the fingerprint MSM, and the
Lean assembly reproduces it (the match). This module begins *soundness* — that an accepting proof
implies the prover knows a valid witness — via the **special soundness** of the inner-product argument
(IPA), the cryptographic core of the halo2 opening.

The IPA proves knowledge of a coefficient vector `a` (a polynomial) behind a commitment `P = ⟨a, G⟩`
that opens to a value `v` at a point — i.e. `⟨a, b⟩ = v` for the evaluation vector `b = (1, x, x², …)`.
The fingerprint MSM's `g`-part *is* this commitment, so the layer is expressed directly over the SRS:

* `commit` — `⟨a, G⟩ = Σᵢ aᵢ • gᵢ`, the polynomial commitment (the MSM's `g`-part).
* `evalVector` / `innerProduct` — `b = (1, x, …, x^{n−1})` and `⟨a, b⟩` (the polynomial at `x`).
* `IpaRelation` — the opening relation `⟨a, G⟩ = P ∧ ⟨a, b⟩ = v` the IPA is an argument of knowledge for.
* `commit_add` / `commit_smul` — `commit` is `F`-linear; this is the algebra the round extractor folds with.

**Special soundness (the Step-3 goal).** The IPA is 2-special-sound per round: from two accepting
transcripts that share the round commitments `(Lⱼ, Rⱼ)` but answer distinct challenges `uⱼ`, the round's
witness folds back, and recursing over the `k` rounds extracts an `a` satisfying `IpaRelation`. Building
that extractor is the next phase; the per-round folding rests on the linearity proved here. (Curve-group
binding / the AGM stays an explicit assumption, per project scope.)
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The polynomial commitment of a coefficient vector `a` against the SRS generators:
`⟨a, G⟩ = Σᵢ aᵢ • gᵢ`. This is exactly the `g`-part of the fingerprint MSM (`Zcash.Snark.Msm.eval`). -/
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

/-- The commitment is additive: `⟨a + a', G⟩ = ⟨a, G⟩ + ⟨a', G⟩`. -/
theorem commit_add (srs : SRS G) (a a' : Fin (2 ^ srs.k) → F) :
    commit srs (a + a') = commit srs a + commit srs a' := by
  simp only [commit, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The commitment is homogeneous: `⟨c • a, G⟩ = c • ⟨a, G⟩`. -/
theorem commit_smul (srs : SRS G) (c : F) (a : Fin (2 ^ srs.k) → F) :
    commit srs (c • a) = c • commit srs a := by
  simp only [commit, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Linearity of the commitment in one combinator (`⟨c•a + c'•a', G⟩ = c•⟨a,G⟩ + c'•⟨a',G⟩`): the
folding step of the IPA round extractor combines two committed vectors exactly this way. -/
theorem commit_linear (srs : SRS G) (c c' : F) (a a' : Fin (2 ^ srs.k) → F) :
    commit srs (c • a + c' • a') = c • commit srs a + c' • commit srs a' := by
  rw [commit_add, commit_smul, commit_smul]

/-! ## The IPA round fold and its 2-special-soundness extractor

One round of the inner-product argument halves the witness. The prover sends the cross-commitments
`(Lⱼ, Rⱼ)`, the verifier sends a challenge `uⱼ`, and the length-`2m` vector folds to length `m`. The
core of special soundness is that the *same* halves, folded at two *distinct* challenges, are uniquely
recoverable — so an accepting prover is committed to a fixed witness, which the extractor recovers. -/

/-- One IPA round folds a vector into its lower half plus `u` times its upper half (`compute_s`'s
`(1, uⱼ)` structure): `foldVec lo hi u = lo + u • hi`. The round commitments `(Lⱼ, Rⱼ)` pin `lo`, `hi`. -/
def foldVec {m : ℕ} (lo hi : Fin m → F) (u : F) : Fin m → F := lo + u • hi

/-- The IPA round extractor: from the folded vector at two distinct challenges, recover the halves —
`hi = (f₁ − f₂)/(u₁ − u₂)` and `lo = f₁ − u₁ • hi`. -/
def roundExtract {m : ℕ} (f₁ f₂ : Fin m → F) (u₁ u₂ : F) : (Fin m → F) × (Fin m → F) :=
  (f₁ - u₁ • ((u₁ - u₂)⁻¹ • (f₁ - f₂)), (u₁ - u₂)⁻¹ • (f₁ - f₂))

/-- **2-special soundness of one IPA round.** The folded vectors at two *distinct* challenges `u₁ ≠ u₂`
(produced from the same halves `lo, hi`) determine the halves: `roundExtract` recovers exactly `(lo, hi)`.
A prover answering two challenges consistently is thus committed to a unique pair that folds back to the
round witness — the algebraic heart of the IPA's special soundness. -/
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

The scalar side of the IPA: the inner product is bilinear, and one round *telescopes* it — with the
witness folded by `u⁻¹` and the evaluation vector by `u`, the folded inner product is the original
`⟨lo,blo⟩ + ⟨hi,bhi⟩` plus the two cross terms the verifier accounts for via `L`/`R`. This is the round's
*completeness*, complementing the round *extractor* (`roundExtract_correct`). -/

/-- The inner product is additive in its left argument. -/
theorem innerProduct_add_left {n : ℕ} (a a' b : Fin n → F) :
    innerProduct (a + a') b = innerProduct a b + innerProduct a' b := by
  simp only [innerProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The inner product is additive in its right argument. -/
theorem innerProduct_add_right {n : ℕ} (a b b' : Fin n → F) :
    innerProduct a (b + b') = innerProduct a b + innerProduct a b' := by
  simp only [innerProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The inner product is homogeneous in its left argument. -/
theorem innerProduct_smul_left {n : ℕ} (c : F) (a b : Fin n → F) :
    innerProduct (c • a) b = c * innerProduct a b := by
  simp only [innerProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The inner product is homogeneous in its right argument. -/
theorem innerProduct_smul_right {n : ℕ} (c : F) (a b : Fin n → F) :
    innerProduct a (c • b) = c * innerProduct a b := by
  simp only [innerProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- One IPA round telescopes the inner product: with the witness folded by `u⁻¹` and the evaluation
vector by `u` (`u ≠ 0`), `⟨a', b'⟩` equals the original `⟨lo,blo⟩ + ⟨hi,bhi⟩` plus the two cross terms
the verifier tracks through `L`/`R`. -/
theorem innerProduct_round {m : ℕ} (lo hi blo bhi : Fin m → F) {u : F} (hu : u ≠ 0) :
    innerProduct (foldVec lo hi u⁻¹) (foldVec blo bhi u)
      = innerProduct lo blo + innerProduct hi bhi
        + u⁻¹ * innerProduct hi blo + u * innerProduct lo bhi := by
  simp only [foldVec, innerProduct_add_left, innerProduct_add_right,
    innerProduct_smul_left, innerProduct_smul_right]
  field_simp
  ring

end Zcash.Snark
