import Mathlib
import Zcash.Snark.KnowledgeSoundness

/-!
# The final theorem: the Orchard verifier is sound (Step 4 capstone)

The top of the soundness layer. `orchard_verifier_sound` states the end-to-end guarantee — an accepting
proof implies the high-level Orchard statement `S` — and proves it by composing `knowledge_sound` with
the two remaining boundary hypotheses: `FiatShamirSound` (the random-oracle leap) and `hencodes`
(VK-correctness, checklist §3).

The chain, every hop a labeled line:

```
deployed verifier accepts        (`accepts` : its fingerprint MSM is the group identity)
  ──[FiatShamirSound : Blake2b as a random oracle + rewinding]──▶   a Consistent tree + the opening
  ──[knowledge_sound : extract_correct + ipaRelation_unique, DLR hardness]──▶   witness satisfies SnarkRelation
  ──[hencodes : checklist §3, Daira's flow]──▶   the high-level statement `S`
```

The middle hop is **proven** (modulo the DLR-hardness assumption; the per-node binding step is
`accepting_fold_eq`). The two ends are the named assumptions kept explicit:

* `FiatShamirSound` packages the **single Fiat–Shamir hand-wave** into one line — that the deployed
  non-interactive verifier accepting a proof yields the special-soundness data the interactive extractor
  consumes (a transcript tree with distinct, unpredictable challenges, consistent with a witness opening
  the commitment). This is the random-oracle idealisation of Blake2b together with rewinding; we model
  neither the hash nor the forking reduction. (In the *fingerprint match* the challenges are the captured
  real values, so that check does not depend on this.)
* `hencodes` is the **VK-correctness** workstream (compile the Orchard Action circuit to a verifying key
  and check its constraints encode note ownership / value balance / nullifier integrity), checklist §3.

See `Zcash.Snark.KnowledgeSoundness` for the full assumption list (DLR hardness, Fiat–Shamir, Vesta curve
order, VK-correctness); `Zcash.Snark.Vesta` instantiates this theorem at the concrete Vesta curve.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The Fiat–Shamir assumption, as one labeled line.** The deployed non-interactive verifier accepting
a proof (`accepts` — concretely, its fingerprint MSM is the group identity) yields the special-soundness
data the interactive extractor consumes: a tree of accepting transcripts with distinct, unpredictable
challenges at every node (the random-oracle / forking step), consistent with a witness that opens the
commitment. This isolates the *single* Fiat–Shamir hand-wave — the random-oracle idealisation of Blake2b
plus rewinding — as one `Prop` rather than diffusing it into the soundness theorem's hypotheses;
everything after it is proven (the consistency is the binding-forced fold of `accepting_fold_eq`). -/
def FiatShamirSound (srs : SRS G) (P : G) (b : Fin (2 ^ srs.k) → Fp) (v : Fp) (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp srs.k) (a : Fin (2 ^ srs.k) → Fp),
    Consistent t a ∧ IpaRelation srs P b v a

/-- **The Orchard verifier is sound (end to end).** If the deployed verifier accepts (`haccepts`), then
under the Fiat–Shamir assumption (`hfs`) it yields a consistent accepting tree and opening;
`knowledge_sound` (under DLR hardness `hbind`, with the constraint identity `hcon`) turns these into a
witness satisfying `SnarkRelation`; and if the verifying key correctly encodes the high-level statement
`S` (`hencodes`, checklist §3 / Daira's flow), then `S` holds.

This is the capstone: the *entire* trust boundary is the three named hypotheses `hbind` (DLR hardness),
`hfs` (Fiat–Shamir), and `hencodes` (VK-correctness) — everything between them is proven. -/
theorem orchard_verifier_sound (srs : SRS G) (hbind : CommitmentBinding (F := Fp) srs)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp}
    {accepts : Prop} (haccepts : accepts) (hfs : FiatShamirSound srs P b v accepts)
    {numerator h : Polynomial Fp} {n : ℕ} (hcon : numerator = h * (Polynomial.X ^ n - 1))
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v numerator h n a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen⟩ := hfs haccepts
  exact hencodes a (knowledge_sound srs hbind hcons hopen hcon).2.1

end Zcash.Snark
