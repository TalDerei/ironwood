import Mathlib
import Zcash.Snark.Field

/-!
# The constraint layer: Schwartz–Zippel soundness of the vanishing check

The verifier's vanishing argument checks the quotient identity at the random evaluation point `x`: the
claimed quotient `h` satisfies `numerator = h · (Xⁿ − 1)`, where `numerator` is the gate / permutation /
lookup combination (the constraints combined by the challenge `y`, as assembled into `expected_h_eval`).
This module proves the soundness of that check by **univariate** Schwartz–Zippel (root counting): the
verifier samples *one* challenge, so the relevant bound is the number of roots of the constraint
polynomial.

* `quotientCheck` — the verifier's check at `x`: `numerator(x) = h(x) · (xⁿ − 1)`.
* `quotientCheck_sound` — if the identity fails *as polynomials* (the committed polynomials violate the
  constraint system), the check passes for at most `deg / |F|` of the challenges.
* `quotientCheck_complete` — if it holds as polynomials, the check passes at every challenge.

`numerator` and `h` are the polynomials carried by the proof; modeling `numerator` from the specific
Orchard gate `Expr`s (lifting `Zcash.Snark.Expr` to `Polynomial`) is the remaining connection to the
assembly — the soundness *mechanism* (root counting ⇒ `d/p`) is what this establishes.
-/

namespace Zcash.Snark

open Polynomial Finset

/-- The verifier's vanishing/quotient check at the challenge `x`: the claimed quotient `h` satisfies the
constraint identity `numerator(x) = h(x) · (xⁿ − 1)`. `numerator` is the gate/permutation/lookup
combination; the verifier opens `h` to `numerator(x) / (xⁿ − 1)`. -/
@[reducible] def quotientCheck (numerator h : Polynomial Fp) (n : ℕ) (x : Fp) : Prop :=
  numerator.eval x = h.eval x * (x ^ n - 1)

/-- **Constraint soundness (Schwartz–Zippel, univariate).** If the quotient identity fails *as
polynomials* — `numerator ≠ h · (Xⁿ − 1)`, i.e. the committed polynomials violate the constraint system
— then the verifier's check passes for at most a `deg / |F|` fraction of the challenges. So a violated
constraint system is accepted with probability `≤ d / p` (`p = scalarFieldOrder ≈ 2²⁵⁴`). -/
theorem quotientCheck_sound (numerator h : Polynomial Fp) (n : ℕ)
    (hne : numerator ≠ h * (X ^ n - 1)) :
    ((univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0) / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) := by
  have hC : numerator - h * (X ^ n - 1) ≠ 0 := sub_ne_zero.mpr hne
  have hset : (univ.filter fun x => quotientCheck numerator h n x)
      = univ.filter fun x => (numerator - h * (X ^ n - 1)).eval x = 0 := by
    apply Finset.filter_congr
    intro x _
    simp only [quotientCheck, eval_sub, eval_mul, eval_pow, eval_X, eval_one, sub_eq_zero]
  rw [hset]
  have hcard : (univ.filter fun x => (numerator - h * (X ^ n - 1)).eval x = 0).card
      ≤ (numerator - h * (X ^ n - 1)).natDegree := by
    have he : (univ.filter fun x => (numerator - h * (X ^ n - 1)).eval x = 0)
        = (numerator - h * (X ^ n - 1)).roots.toFinset := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Multiset.mem_toFinset,
        Polynomial.mem_roots hC, IsRoot.def]
    rw [he]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
  gcongr

/-- **Completeness:** if the quotient identity holds as polynomials, the verifier's check passes at
every challenge. -/
theorem quotientCheck_complete (numerator h : Polynomial Fp) (n : ℕ)
    (heq : numerator = h * (X ^ n - 1)) (x : Fp) : quotientCheck numerator h n x := by
  simp only [quotientCheck, heq, eval_mul, eval_sub, eval_pow, eval_X, eval_one]

end Zcash.Snark
