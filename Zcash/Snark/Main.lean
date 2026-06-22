import Mathlib
import Zcash.Snark.KnowledgeSoundness

/-!
# Soundness composition — CONDITIONAL, not yet completed (§2, in progress)

⚠️ **Status.** This is a *conditional composition*, not finished SNARK soundness, and it does not yet share
a formal object with the fingerprint MSM (§1). It is named with a `_conditional` suffix to avoid
overclaiming. The gaps (tracked in `notes/fv-review-checklist.md`):

* `accepts` is an opaque `Prop`; it is **not** instantiated to the deployed accept condition
  `(assemble vk ps ch).eval … = 0`, so the theorem says nothing about the fingerprint (checklist C1).
* `ExtractableFromAcceptance` assumes the **IPA knowledge-soundness conclusion** (a consistent transcript
  tree + a valid opening) — i.e. it bundles Fiat–Shamir *and* the extraction that `accepting_fold_eq` /
  `extract_correct` were meant to prove, so those proven lemmas are **off this path** (C3).
* the constraint identity `hcon` is a hypothesis (not derived via `quotientCheck_sound`), and
  `numerator/h/n` are not tied to the witness `a`, so `SnarkRelation` does not yet state "the extracted
  witness satisfies the circuit" (C2).
* `hbind` (DLR hardness) is passed to `knowledge_sound` but only feeds its uniqueness conjunct, which this
  proof discards — so binding is currently inert on the path to `S`.

What *is* proven lives in the component lemmas (`extract_correct`, `accepting_fold_eq`, `commitGen_round`,
`quotientCheck_sound`, `ipaRelation_unique`, the binding reduction, `eval_combineGates`); the open work is
wiring them onto this path. `Zcash.Snark.Vesta` instantiates this conditional theorem at the concrete
Vesta curve. See `Zcash.Snark.KnowledgeSoundness` for the assumption list.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **Assumed: acceptance yields the IPA extraction data** (stronger than "just Fiat–Shamir"). Given
`accepts`, this hands over a consistent transcript tree and a valid opening — i.e. it assumes the IPA
knowledge-soundness *conclusion* that `accepting_fold_eq` / `extract_correct` were meant to produce,
bundled with Fiat–Shamir. Honest reading: "assume IPA knowledge soundness + FS," not "hand-wave only FS."
Splitting this into the genuine FS step (`accept → ∃ tree`) and the proven extraction — so the residual
assumption narrows to "challenges are uniform and unpredictable" — is open §2 work (checklist C3). -/
def ExtractableFromAcceptance (srs : SRS G) (P : G) (b : Fin (2 ^ srs.k) → Fp) (v : Fp)
    (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp srs.k) (a : Fin (2 ^ srs.k) → Fp),
    Consistent t a ∧ IpaRelation srs P b v a

/-- **Conditional soundness composition (NOT completed soundness).** From the *assumed* extraction data
(`hextract haccepts`) and the *assumed* constraint identity (`hcon`), conclude `S` via `hencodes`.

⚠️ This assumes what §2 should prove: `accepts` is opaque (not the fingerprint MSM); the extraction is
assumed (so `accepting_fold_eq` / `extract_correct` are off-path); `hcon` is assumed (so
`quotientCheck_sound` is unused) and untied to the witness; and `hbind`'s binding only feeds the discarded
uniqueness conjunct. It is the scaffold for the composition, not the composition — see the module
docstring and `notes/fv-review-checklist.md`. -/
theorem orchard_verifier_sound_conditional (srs : SRS G) (hbind : CommitmentBinding (F := Fp) srs)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp}
    {accepts : Prop} (haccepts : accepts) (hextract : ExtractableFromAcceptance srs P b v accepts)
    {numerator h : Polynomial Fp} {n : ℕ} (hcon : numerator = h * (Polynomial.X ^ n - 1))
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v numerator h n a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen⟩ := hextract haccepts
  exact hencodes a (knowledge_sound srs hbind hcons hopen hcon).2.1

end Zcash.Snark
