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

end Zcash.Snark
