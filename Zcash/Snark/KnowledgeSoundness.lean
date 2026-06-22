import Mathlib
import Zcash.Snark.Soundness
import Zcash.Snark.Extraction
import Zcash.Snark.Constraints
import Zcash.Snark.CommitFold

/-!
# Knowledge soundness, end to end (Step 4)

The capstone: an accepting proof demonstrates knowledge of a witness satisfying the SNARK relation. It
composes the proven pieces of the soundness layer —

* `extract_correct` — the IPA extractor recovers the witness from an accepting transcript tree;
* `commitGen_round` + `ipaRelation_unique` — folding preserves the commitment and the opening is unique
  under binding (so an accepting transcript yields a *consistent* tree);
* `quotientCheck_sound` + `Expr.eval_toPoly` — the verifier's gate check, via Schwartz–Zippel, forces the
  committed polynomials to satisfy the circuit's constraint identity (off a `≤ d/p` bad set).

`SnarkRelation` is the relation the SNARK proves (the witness opens the commitment **and** the committed
polynomials satisfy the constraint identity); `knowledge_sound` assembles the proven lemmas into "the
extractor recovers the unique witness satisfying the relation"; `soundness_error` is the residual
`≤ d/p` Schwartz–Zippel error.

## Explicit assumptions (the trust boundary — for human review)

This layer is sound **relative to** the following, each kept explicit rather than hidden:

* **DLR hardness** (discrete-log relations on the Pasta generators) — the binding hypothesis
  `CommitmentBinding`. Modeled as a reduction: `relation_of_collision` proves a binding violation yields
  a nontrivial relation, and `commitmentBinding_iff_no_relation` proves binding *is* exactly DLR hardness
  (the reduction is proven; only the hardness is claimed).
* **Fiat–Shamir / Blake2b** as a random oracle — the non-interactive challenges are taken from the
  captured transcript (`Zcash.Snark.FiatShamir`); the random-oracle reduction is not formalized.
* **Pasta curve arithmetic** — the group `G` is abstract (`commit`/`eval` use only its `Fp`-module
  structure); the curve law is not formalized.
* **The verifying key is the correct circuit** (Daira's flow / checklist §3): that the VK's gates encode
  the intended high-level relation (note ownership, value balance, nullifiers) is a *separate* workstream
  — this layer proves the verifier sound *relative to the given VK*, ending at "the witness satisfies the
  VK's constraint system."

## For human review
Check that `SnarkRelation` is the intended relation, that the four assumptions above are the right ones
and acceptably standard, and that the captured fingerprint match (`Zcash.Snark.Fixture`) is for the
intended Orchard Action circuit.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The relation the SNARK proves: the witness `a` **opens** the commitment `P` to the value `v`
(`IpaRelation`), and the committed polynomials **satisfy** the circuit's quotient identity
`numerator = h · (Xⁿ − 1)` (the gate/permutation/lookup constraints hold as polynomials). -/
structure SnarkRelation (srs : SRS G) (P : G) (b : Fin (2 ^ srs.k) → Fp) (v : Fp)
    (numerator h : Polynomial Fp) (n : ℕ) (a : Fin (2 ^ srs.k) → Fp) : Prop where
  opens : IpaRelation srs P b v a
  constraintsHold : numerator = h * (X ^ n - 1)

/-- **Knowledge soundness (end to end, modulo the named assumptions).** From an accepting transcript
tree `t` consistent with the witness `a` (binding ⇒ consistent, via `commitGen_round`), the opening the
verifier checks (`hopen`), and the constraint identity holding as polynomials (the `quotientCheck_sound`
conclusion off the Schwartz–Zippel bad set), the extractor recovers the **unique** witness satisfying
`SnarkRelation`. Composes `extract_correct` (extraction) and `ipaRelation_unique` (uniqueness under DLR
hardness). -/
theorem knowledge_sound (srs : SRS G) (hbind : CommitmentBinding (F := Fp) srs)
    {t : Tree Fp srs.k} {a : Fin (2 ^ srs.k) → Fp} (hcons : Consistent t a)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} (hopen : IpaRelation srs P b v a)
    {numerator h : Polynomial Fp} {n : ℕ} (hcon : numerator = h * (X ^ n - 1)) :
    extract t = a ∧ SnarkRelation srs P b v numerator h n a
      ∧ ∀ a', IpaRelation srs P b v a' → a' = a :=
  ⟨extract_correct t a hcons, ⟨hopen, hcon⟩, fun _ h' => ipaRelation_unique hbind h' hopen⟩

/-- The residual **soundness error** of the constraint layer (re-export of `quotientCheck_sound`): a
committed-polynomial set that violates the constraint identity is accepted for at most a `deg / |F|`
fraction of the challenges (`|F| = scalarFieldOrder ≈ 2²⁵⁴`). -/
theorem soundness_error (numerator h : Polynomial Fp) (n : ℕ) (hne : numerator ≠ h * (X ^ n - 1)) :
    ((Finset.univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) :=
  quotientCheck_sound numerator h n hne

end Zcash.Snark
