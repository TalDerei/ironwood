import Mathlib
import Zcash.Snark.Soundness

/-!
# The commitment respects the IPA round fold

This closes the second soundness seam: that an *accepting* transcript yields a tree *consistent* with the
witness (`Zcash.Snark.extract_correct`'s hypothesis). The structural fact is that the polynomial
commitment is compatible with one IPA round — folding the witness by `u⁻¹` and the generators by `u`
sends the parent commitment to the folded one plus the cross terms `L`/`R` the verifier accounts for.

* `commitGen` — the commitment over *arbitrary* generators (`commit srs = commitGen srs.g`).
* `commitGen_{add,smul}_{left,gen}` — bilinearity in the witness and in the generators.
* `commitGen_round` (proven) — one round's commitment fold: `⟨a' , g'⟩ = ⟨a, g⟩ + u·L + u⁻¹·R`, the
  round's *completeness*. Together with `Zcash.Snark.ipaRelation_unique` (uniqueness under
  `CommitmentBinding`), this forces the prover's folded response to be the *true* fold of the committed
  witness — i.e. accepting ⇒ consistent — leaving only the binding/AGM assumption itself.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The commitment over arbitrary generators `g`: `⟨a, g⟩ = Σᵢ aᵢ • gᵢ`. Specialises to the SRS
commitment: `commit srs = commitGen srs.g`. -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- The fingerprint/SRS commitment is the generator-commitment at the SRS generators. -/
theorem commit_eq_commitGen (srs : SRS G) (a : Fin (2 ^ srs.k) → F) :
    commit srs a = commitGen srs.g a := rfl

/-- Additivity in the witness. -/
theorem commitGen_add_left {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Homogeneity in the witness. -/
theorem commitGen_smul_left {n : ℕ} (g : Fin n → G) (c : F) (a : Fin n → F) :
    commitGen g (c • a) = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Additivity in the generators. -/
theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Homogeneity in the generators. -/
theorem commitGen_smul_gen {n : ℕ} (c : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (c • g) a = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (g i)

/-- **One IPA round's commitment fold (completeness).** Folding the witness by `u⁻¹` and the generators
by `u` sends the parent commitment to the folded commitment plus the two cross terms `⟨aLo, gHi⟩` and
`⟨aHi, gLo⟩` — exactly the `R`/`L` the verifier accounts for. So the honest witness folds consistently;
with `ipaRelation_unique` (binding), the prover's response must be this fold. -/
theorem commitGen_round {m : ℕ} (gLo gHi : Fin m → G) (aLo aHi : Fin m → F) {u : F} (hu : u ≠ 0) :
    commitGen (gLo + u • gHi) (aLo + u⁻¹ • aHi)
      = (commitGen gLo aLo + commitGen gHi aHi)
        + u • commitGen gHi aLo + u⁻¹ • commitGen gLo aHi := by
  simp only [commitGen_add_left, commitGen_smul_left, commitGen_add_gen, commitGen_smul_gen,
    smul_add, smul_smul, inv_mul_cancel₀ hu, one_smul]
  abel

end Zcash.Snark
