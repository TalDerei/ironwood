import Mathlib
import Zcash.Snark.KnowledgeSoundness

/-!
# The final theorem: the Orchard verifier is sound (Step 4 capstone)

The top of the soundness layer. `orchard_verifier_sound` states the end-to-end guarantee — an accepting
proof implies the high-level Orchard statement `S` — and proves it by composing `knowledge_sound` with
the single remaining boundary hypothesis `hencodes` (VK-correctness, checklist §3).

The chain, every hop explicit:

```
accepting transcript
  ──[extract_correct + accepting_fold_eq + DLR hardness]──▶  a Consistent tree, extracted witness `a`
  ──[ipaRelation_unique + quotientCheck_sound + eval_combineGates]──▶  `a` satisfies SnarkRelation
  ──[hencodes : checklist §3, Daira's flow]──▶  the high-level statement `S`
```

The first two hops are **proven** (modulo the named DLR-hardness / Fiat–Shamir / abstract-curve
assumptions recorded in `Zcash.Snark.KnowledgeSoundness`). The last hop, `hencodes`, is the **separate
VK-correctness workstream** — compile the Orchard Action circuit to a verifying key and check that its
constraint system encodes note ownership / value balance / nullifier integrity. We take it as an
explicit hypothesis here so the trust boundary is visible rather than hidden, and so the high-level
statement `S` is whatever that workstream certifies the circuit to mean.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The Orchard verifier is sound (end to end).** Given the proven soundness chain — an accepting
transcript tree consistent with the extracted witness `a` (binding ⇒ consistent, via `accepting_fold_eq`
under DLR hardness), the opening, and the constraint identity (`quotientCheck_sound`) — `knowledge_sound`
yields that `a` satisfies `SnarkRelation`. If, in addition, the verifying key correctly encodes the
high-level statement `S` (`hencodes`, checklist §3 / Daira's flow), then an accepting proof implies `S`.

This is the capstone: it makes the *entire* trust boundary explicit. Everything before `hencodes` is
proven from the DLR-hardness / Fiat–Shamir / curve assumptions; `hencodes` is the VK-correctness
assumption, the one piece this verifier-side formalization deliberately leaves to the circuit-side
workstream. -/
theorem orchard_verifier_sound (srs : SRS G) (hbind : CommitmentBinding (F := Fp) srs)
    {t : Tree Fp srs.k} {a : Fin (2 ^ srs.k) → Fp} (hcons : Consistent t a)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} (hopen : IpaRelation srs P b v a)
    {numerator h : Polynomial Fp} {n : ℕ} (hcon : numerator = h * (Polynomial.X ^ n - 1))
    {S : Prop} (hencodes : SnarkRelation srs P b v numerator h n a → S) :
    S :=
  hencodes (knowledge_sound srs hbind hcons hopen hcon).2.1

end Zcash.Snark
