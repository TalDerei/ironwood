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

/-! ## Binding as a discrete-log-relation hardness assumption

Rather than *assuming* the commitment is binding outright, we model it as a **reduction** to a hardness
assumption — the same shape as the binding-signature argument's `relation_of_imbalance`: prove the
*counterfactual* that breaking binding produces a nontrivial discrete-log relation among the SRS
generators, and claim **DLR hardness** (no such relation exists on the Pasta generators) in the docs to
close it. `commitmentBinding_iff_no_relation` makes precise that `CommitmentBinding` *is* exactly DLR
hardness, so the assumption is the standard, named one — with the reduction itself proven. -/

/-- A discrete-log relation among the SRS generators: a coefficient vector the generators send to `0`.
It is *nontrivial* when `r ≠ 0`. **DLR hardness** is the assumption that no nontrivial relation exists. -/
@[reducible] def DLRelation (srs : SRS G) (r : Fin (2 ^ srs.k) → F) : Prop :=
  commitGen srs.g r = 0

/-- Additivity over subtraction in the witness. -/
theorem commitGen_sub {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a - a') = commitGen g a - commitGen g a' := by
  simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- **The binding reduction (counterfactual).** A binding collision — two distinct openings of one
commitment — yields a *nontrivial* discrete-log relation `a − a'` among the SRS generators. So DLR
hardness closes binding, exactly as `relation_of_imbalance` closes the binding-signature argument: the
collision is reduced to a relation the hardness assumption forbids. -/
theorem relation_of_collision (srs : SRS G) {a a' : Fin (2 ^ srs.k) → F}
    (hcol : commit srs a = commit srs a') (hne : a ≠ a') :
    a - a' ≠ 0 ∧ DLRelation srs (a - a') := by
  refine ⟨sub_ne_zero.mpr hne, ?_⟩
  show commitGen srs.g (a - a') = 0
  rw [commitGen_sub, ← commit_eq_commitGen, ← commit_eq_commitGen, hcol, sub_self]

/-- **Binding is exactly DLR hardness.** The commitment is binding iff every discrete-log relation among
the generators is trivial — so assuming DLR hardness *is* assuming `CommitmentBinding`, and the binding
hypothesis used by `ipaRelation_unique` / `opening_knowledge_sound` is precisely the standard,
named hardness assumption (with `relation_of_collision` the proven reduction). -/
theorem commitmentBinding_iff_no_relation (srs : SRS G) :
    CommitmentBinding (F := F) srs ↔ ∀ r : Fin (2 ^ srs.k) → F, DLRelation srs r → r = 0 := by
  constructor
  · intro hb r hr
    have hr' : commitGen srs.g r = 0 := hr
    apply hb
    rw [commit_eq_commitGen, commit_eq_commitGen, hr']
    simp [commitGen]
  · intro hnr a a' hcol
    have hr : DLRelation srs (a - a') := by
      show commitGen srs.g (a - a') = 0
      rw [commitGen_sub, ← commit_eq_commitGen, ← commit_eq_commitGen, hcol, sub_self]
    exact sub_eq_zero.mp (hnr _ hr)

end Zcash.Snark
