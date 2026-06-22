import Zcash.Snark.Extraction
import Zcash.Snark.CommitFold

/-!
# From an accepting transcript to a consistent tree (C3-Consistent)

`Zcash.Snark.accepting_fold_eq_foldVec` is the per-node binding step: an accepting round response *is* the
true fold. This module composes it over the whole tree, closing the `accepting ⇒ Consistent` seam that
`Zcash.Snark.extract_correct` takes as a hypothesis.

* `WTree` — a witness tree carrying the prover's *response* at every node (what the prover actually sent),
  with the round challenges; `WTree.toTree` forgets the witnesses down to the challenge tree
  `Zcash.Snark.Tree`.
* `foldGens` / `foldedCommitment` — the folded generators (`gLo + u⁻¹·gHi`) and the verifier's folded
  commitment a round produces from the parent witness.
* `Accepting g wt` — at every node the two child responses **open** the folded commitments, the challenges
  are distinct and nonzero, and the folded-generator commitment is binding.
* `WConsistent wt` — at every node each child response *is* the true fold of the parent
  (`roundFold`).
* `accepting_imp_wconsistent` (proven) — binding promotes `Accepting` to `WConsistent`, node by node via
  `accepting_fold_eq_foldVec`.
* `accepting_extract` (proven) — therefore the extractor recovers the prover's root response from the
  challenge tree: `extract wt.toTree = wt.witness`. This is `accepting ⇒ consistent ⇒ extracted`, with the
  only assumption the binding (DLR hardness) carried in `Accepting`.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The folded generators for one IPA round, in the extractor's `foldVec` convention (generators by
`u⁻¹`): `gLo + u⁻¹ • gHi`. -/
def foldGens {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (u : F) : Fin (2 ^ k) → G :=
  loHalf g + u⁻¹ • hiHalf g

/-- The verifier's folded commitment for one round, from the parent generators `g` and witness `a`:
the folded parent commitment plus the two cross terms the prover's `L`/`R` account for. This is exactly
the right-hand side `accepting_fold_eq_foldVec` checks the response against. -/
def foldedCommitment {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) (u : F) : G :=
  (commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a))
    + u⁻¹ • commitGen (hiHalf g) (loHalf a) + u • commitGen (loHalf g) (hiHalf a)

/-- A witness tree: the prover's response at every node (length `2 ^ k`) together with the two round
challenges; the leaf carries the fully-folded scalar. -/
inductive WTree (F : Type*) : ℕ → Type _ where
  | leaf : (Fin 1 → F) → WTree F 0
  | node {k : ℕ} : (Fin (2 ^ (k + 1)) → F) → F → F → WTree F k → WTree F k → WTree F (k + 1)

/-- The prover's response at the root of a witness tree. -/
def WTree.witness {F : Type*} : {k : ℕ} → WTree F k → (Fin (2 ^ k) → F)
  | _, .leaf a => a
  | _, .node a _ _ _ _ => a

/-- Forget the responses, keeping the challenge tree consumed by `Zcash.Snark.extract`. -/
def WTree.toTree {F : Type*} : {k : ℕ} → WTree F k → Tree F k
  | _, .leaf a => .leaf (a 0)
  | _, .node _ u₁ u₂ t₁ t₂ => .node u₁ u₂ t₁.toTree t₂.toTree

/-- The transcript is **accepting** over generators `g`: at every node the two child responses open the
folded commitments (`foldedCommitment`), the challenges are distinct and nonzero, and the folded-generator
commitment is binding (DLR hardness at the folded generators). -/
def Accepting : {k : ℕ} → (Fin (2 ^ k) → G) → WTree F k → Prop
  | _, _, .leaf _ => True
  | _, g, .node a u₁ u₂ t₁ t₂ =>
      u₁ ≠ u₂ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧
      Function.Injective (commitGen (F := F) (foldGens g u₁)) ∧
      Function.Injective (commitGen (F := F) (foldGens g u₂)) ∧
      commitGen (foldGens g u₁) t₁.witness = foldedCommitment g a u₁ ∧
      commitGen (foldGens g u₂) t₂.witness = foldedCommitment g a u₂ ∧
      Accepting (foldGens g u₁) t₁ ∧ Accepting (foldGens g u₂) t₂

/-- The witness tree is **consistent**: at every node each child response is the true fold of the parent
(`roundFold`). This is `Zcash.Snark.Consistent` transported to the witness tree. -/
def WConsistent : {k : ℕ} → WTree F k → Prop
  | _, .leaf _ => True
  | _, .node a u₁ u₂ t₁ t₂ =>
      u₁ ≠ u₂ ∧ t₁.witness = roundFold a u₁ ∧ t₂.witness = roundFold a u₂ ∧
      WConsistent t₁ ∧ WConsistent t₂

/-- **Binding promotes accepting to consistent.** Over an accepting transcript, the per-node binding step
(`accepting_fold_eq_foldVec`) forces each child response to be the true fold; recursion gives consistency
of the whole tree. The only assumption is the binding carried in `Accepting` (DLR hardness). -/
theorem accepting_imp_wconsistent :
    {k : ℕ} → (g : Fin (2 ^ k) → G) → (wt : WTree F k) → Accepting g wt → WConsistent wt
  | _, _, .leaf _, _ => trivial
  | _, g, .node a u₁ u₂ t₁ t₂, h => by
      obtain ⟨hne, hu₁, hu₂, hb₁, hb₂, ha₁, ha₂, hr₁, hr₂⟩ := h
      refine ⟨hne, ?_, ?_, ?_, ?_⟩
      · exact accepting_fold_eq_foldVec (loHalf g) (hiHalf g) (loHalf a) (hiHalf a) t₁.witness hu₁ hb₁ ha₁
      · exact accepting_fold_eq_foldVec (loHalf g) (hiHalf g) (loHalf a) (hiHalf a) t₂.witness hu₂ hb₂ ha₂
      · exact accepting_imp_wconsistent (foldGens g u₁) t₁ hr₁
      · exact accepting_imp_wconsistent (foldGens g u₂) t₂ hr₂

/-- Consistency of the witness tree is consistency of its challenge tree with the root response. -/
theorem wconsistent_imp_consistent :
    {k : ℕ} → (wt : WTree F k) → WConsistent wt → Consistent wt.toTree wt.witness
  | _, .leaf a, _ => by simp only [WTree.toTree, WTree.witness, Consistent]
  | _, .node a u₁ u₂ t₁ t₂, h => by
      obtain ⟨hne, h₁, h₂, hc₁, hc₂⟩ := h
      show Consistent (Tree.node u₁ u₂ t₁.toTree t₂.toTree) a
      refine ⟨hne, ?_, ?_⟩
      · have := wconsistent_imp_consistent t₁ hc₁; rwa [h₁] at this
      · have := wconsistent_imp_consistent t₂ hc₂; rwa [h₂] at this

/-- **Accepting ⇒ extracted.** From an accepting transcript (with binding), the extractor recovers the
prover's root response from the challenge tree — the `Consistent`-hypothesis of `extract_correct` is now
*discharged* from acceptance, leaving only the binding (DLR hardness) assumption. -/
theorem accepting_extract {k : ℕ} (g : Fin (2 ^ k) → G) (wt : WTree F k) (h : Accepting g wt) :
    extract wt.toTree = wt.witness :=
  extract_correct wt.toTree wt.witness (wconsistent_imp_consistent wt (accepting_imp_wconsistent g wt h))

end Zcash.Snark
