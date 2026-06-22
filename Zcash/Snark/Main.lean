import Mathlib
import Zcash.Snark.KnowledgeSoundness
import Zcash.Snark.Assemble
import Zcash.Snark.Consistency
import Zcash.Snark.IpaSoundness

/-!
# Soundness composition — CONDITIONAL, not yet completed (§2, in progress)

**Status.** This is a *conditional composition*, not finished SNARK soundness, and it does not yet share
a formal object with the fingerprint MSM (§1). It is named with a `_conditional` suffix to avoid
overclaiming. The gaps (tracked in `notes/fv-review-checklist.md`):

* `accepts` is an opaque `Prop`; it is **not** instantiated to the deployed accept condition
  `(assemble vk ps ch).eval … = 0`, so the theorem says nothing about the fingerprint (checklist C1).
* `ExtractableFromAcceptance` assumes the **IPA knowledge-soundness conclusion** (a consistent transcript
  tree + a valid opening) — i.e. it bundles Fiat–Shamir *and* the extraction that `accepting_fold_eq` /
  `extract_correct` were meant to prove, so those proven lemmas are **off this path** (C3).
* `SnarkRelation` now ties both conjuncts to the *same* witness `a` (opens `P` **and** `circuitSat a`) —
  C2 done; but `circuitSat a` is currently supplied by `ExtractableFromAcceptance` (assumed), not
  *derived* from the deployed constraint check via `constraint_identity_of_accept` and the multiopen
  decode (C3, open).
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
assumption narrows to "challenges are uniform and unpredictable" — is open §2 work (checklist C3). It now
also bundles `circuitSat a` (the extracted witness satisfies the circuit); deriving that from the deployed
constraint check rather than assuming it is likewise open (C3). -/
def ExtractableFromAcceptance (srs : SRS G) (P : G) (b : Fin (2 ^ srs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop) (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp srs.k) (a : Fin (2 ^ srs.k) → Fp),
    Consistent t a ∧ IpaRelation srs P b v a ∧ circuitSat a

-- TODO(Step 4 / semantic adequacy): `hencodes`/`S` below are the seam from circuit-satisfiability to the
-- high-level Orchard relation. Currently `S` is a free `Prop` and `hencodes` is an assumed hypothesis, so
-- the chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and never reaches
-- "…therefore a valid Orchard action" (note well-formed, value balances, nullifier correctly derived,
-- spend authorized). Closing it: instantiate `S` to the concrete Orchard statement and *prove* `hencodes`.
-- Beyond §2 (C1–C3 only reach `SnarkRelation`); the output-side dual of the input-side VK-correctness gap
-- (see `Assemble.lean`). Large; not started.
/-- **Conditional soundness composition (NOT completed soundness).** From the *assumed* extraction data
(`hextract haccepts` — which now also yields `circuitSat a`), conclude `S` via `hencodes`.

This assumes what §2 should prove: `accepts` is opaque (the `_deployed` variant fixes that); the
extraction + circuit-satisfaction are assumed (so `accepting_fold_eq` / `extract_correct` /
`constraint_identity_of_accept` are off-path); and `hbind`'s binding only feeds the discarded uniqueness
conjunct. It is the scaffold for the composition, not the composition — see the module docstring and
`notes/fv-review-checklist.md`. -/
theorem orchard_verifier_sound_conditional (srs : SRS G) (hbind : CommitmentBinding (F := Fp) srs)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance srs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen, hsat⟩ := hextract haccepts
  exact hencodes a (knowledge_sound srs hbind hcons hopen hsat).2.1

/-- The deployed verifier's **accept condition**, as a concrete predicate: the assembled fingerprint MSM
`assemble vk ps ch` (the §1 object) evaluates to the group identity against the SRS. This is what
`accepts` *should* be — the formal object §1 and §2 must share. (`hk` aligns the circuit shape's `k` with
the SRS's `k`.) -/
def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (srs : SRS G)
    (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  (hk ▸ assemble vk ps ch : Msm srs.k Fp G).eval srs = 0

/-- **Conditional soundness, now *about the fingerprint* (checklist C1, interim).** This is
`orchard_verifier_sound_conditional` with `accepts` instantiated to the real deployed accept condition
`DeployedAccepts` — so §1's `assemble` / `Msm.eval` and the §2 soundness theorem finally share a formal
object (previously `accepts` was a free `Prop`).

Still conditional: the bridge `hextract : DeployedAccepts … → ∃ t a, Consistent t a ∧ IpaRelation …`
is **assumed**. Proving it — `(assemble vk ps ch).eval srs = 0 → ∃ t a, Consistent t a ∧ IpaRelation …`
— is the hard remaining seam (the full C1), the actual IPA/multiopen soundness connecting the assembled
MSM to the opening. -/
theorem orchard_verifier_sound_deployed [DecidableEq G] [Inhabited G] {shape : Shape}
    (srs : SRS G) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (hbind : CommitmentBinding (F := Fp) srs)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hextract : ExtractableFromAcceptance srs P b v circuitSat (DeployedAccepts srs hk vk ps ch))
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional srs hbind haccepts hextract hencodes

/-- **Soundness from an accepting IPA transcript — the extraction now PROVEN, not assumed.** Given an
accepting witness tree over the SRS generators (`haccept`; the per-node binding/DLR hardness lives inside
`Accepting`), the root response opening the commitment (`hopen`), and its circuit-satisfaction (`hsat`),
the **extracted** witness `extract wt.toTree` satisfies `SnarkRelation`, hence `S`.

This is the payoff of the C3 work: `accepting_extract` (the IPA extraction, `accepting_imp_wconsistent` +
`extract_correct`) is **on the path** — the conclusion is about the *extracted* witness, so the extractor
genuinely contributes (unlike `orchard_verifier_sound_conditional`, where it was discarded). The residual
assumption is now only the **structural** `accept → ∃ Accepting tree` (the multiopen decode, checklist
C1-full) together with the response's opening (`hopen`) and circuit-satisfaction (`hsat` — itself
dischargeable by `circuitSatViaGates_of_check`). -/
theorem orchard_sound_via_transcript (srs : SRS G)
    (wt : WTree Fp srs.k) (haccept : Accepting srs.g wt)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} (hopen : IpaRelation srs P b v wt.witness)
    {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop} (hsat : circuitSat wt.witness)
    {S : Prop} (hencodes : SnarkRelation srs P b v circuitSat (extract wt.toTree) → S) :
    S := by
  have hext : extract wt.toTree = wt.witness := accepting_extract srs.g wt haccept
  have hrel : SnarkRelation srs P b v circuitSat (extract wt.toTree) := by
    rw [hext]; exact ⟨hopen, hsat⟩
  exact hencodes hrel

/-! ## C1 closed: `IpaRelation` is derived from the transcript tree, not assumed

`Zcash.Snark.ipa_soundV` derives the *full* opening relation — `commit g a = P` **and** `⟨a,b⟩ = v` — from
an accepting IPA transcript tree (`IpaAcceptV`), binding-free, by 3-special soundness. So the bridge no
longer *assumes* `IpaRelation` (review item C1). Honest caveat: the tree-bridge (`FiatShamirTree`) is **not**
purely the rewinding — it also absorbs (i) the MSM↔tree structural correspondence (that `assemble.eval = 0`
unfolds into the recursive checks for the proof's actual `P,b,v,L,R`), which is *provable* via
`eval_assembleFinalMsm` but not yet wired (checklist B), and (ii) the pinning of free `P,b,v` to the proof.
The cryptographic opening is genuinely derived; the residual bundle is structural/mechanical. -/

/-- `IpaAcceptV` over the SRS generators derives the existing `IpaRelation`: the witness `ipa_soundV`
extracts opens `P` (`commit srs a = commitGen srs.g a`) and gives the inner product
(`commitGen b a = ⟨a,b⟩`). The IPA opening is now *derived*, not assumed. -/
theorem ipaRelation_of_acceptV (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G srs.k) (h : IpaAcceptV srs.g b P v t) :
    ∃ a, IpaRelation srs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV srs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- **The transcript-tree bridge — SUPERSEDED by `Zcash.Snark.DeployedIpaRewind`.** Acceptance yields a
*clean* `IpaAcceptV` tree. This absorbed two things beyond the rewinding: (i) the MSM↔tree structural
correspondence and (ii) the `U`/`W`/`S` separation (since `IpaAcceptV` is the blinding-free IPA). Of these,
(ii) is now genuinely *proven and on-path* (`Zcash.Snark.deployed_ipa_soundV`), and the flat half of (i) is
proven (`foldAll = G'₀`, `compute_b = ⟨sFun, evalVector⟩`; `deployed_verification_eq`). `DeployedIpaRewind`
(`Zcash.Snark.Weld`) is the replacement bridge — but it is **not yet** pure rewinding: it still bundles the
MSM↔tree correspondence (the proven flat fact is a sidecar, not composed in — see its docstring). Prefer the
capstones `orchard_verifier_sound_deployed_full`/`_pinned`/`_closed` over the `_C1`/`_C3` theorems that use
this, but read their honest residual notes. -/
def FiatShamirTree (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (P : G) (v : Fp) (accepts : Prop) : Prop :=
  accepts → ∃ t : IpaTreeV Fp G srs.k, IpaAcceptV srs.g b P v t

/-- **The deployed Orchard verifier is sound — C1 closed.** From the deployed accept
(`assemble.eval = 0`), the minimal Fiat–Shamir bridge `hFS` (acceptance yields the transcript tree —
the *only* IPA assumption), and the circuit-satisfaction of the opening (`hcirc`, the constraint side /
checklist C3, dischargeable by `circuitSatViaGates_of_check`), conclude `S`.

The IPA opening (`IpaRelation`) is **derived** here via `ipaRelation_of_acceptV`/`ipa_soundV` — it is no
longer assumed (the earlier conditional bridges that bundled it have been removed). Honest scope:
`hFS` still absorbs the MSM↔tree correspondence + `P,b,v` pinning (see `FiatShamirTree`; checklist B), and
`hcirc` is the assumed constraint side — `orchard_verifier_sound_deployed_C3` derives it from the gate check.
Superseded by `orchard_verifier_sound_deployed_full`/`_closed` (`Zcash.Snark.Weld`), which peel `U`/`W`/`S`
and wire the multiopen decode; prefer those.
Named assumptions: the bridge (`hFS`), the constraint side (`hcirc`, C3), DLR hardness (for *uniqueness*,
unused on this path), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_deployed_C1 [DecidableEq G] [Inhabited G] {shape : Shape}
    (srs : SRS G) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp}
    {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hFS : FiatShamirTree srs b P v (DeployedAccepts srs hk vk ps ch))
    (hcirc : ∀ a, IpaRelation srs P b v a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, ht⟩ := hFS haccepts
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV srs b P v t ht
  exact hencodes a ⟨hrel, hcirc a hrel⟩

/-! ## C3 closed: `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

The constraint side mirrors C1. The verifier checks the gate identity only at the challenge `x` — a *point*
check (`quotientCheck`, `numerator.eval x = h.eval x · (xⁿ−1)`). `circuitSatViaGates_of_check` lifts that
point check to the polynomial identity `circuitSatViaGates` (the witness's decoded columns satisfy the
gates) provided `x` avoids the Schwartz–Zippel bad set (`hgood`). So `circuitSat`, instantiated to the
concrete `circuitSatViaGates`, is *derived* from the verifier's actual gate check — no black-box `hcirc`. -/

open Polynomial in
/-- **The deployed Orchard verifier is sound — C1 and C3 closed.** Both conjuncts of `SnarkRelation` are
*derived*, not assumed: `IpaRelation` (the opening) from the transcript tree via `ipa_soundV` (C1); and
`circuitSat` — instantiated to `circuitSatViaGates` — from the verifier's quotient/gate **point** check
`hquot` at the challenge `x`, lifted to the polynomial identity by Schwartz–Zippel (`hgood`), via
`circuitSatViaGates_of_check` (C3).

The black-box `hcirc` is gone. What remains are the verifier's actual checks and the standard assumptions:
the special-soundness rewinding tree (`hFS`), the gate point-check (`hquot`), the SZ good challenge
(`hgood`), and VK-correctness (`hencodes`). `hquot`/`hgood` are the constraint-side analog of `hFS` — the
gate check is part of `assemble.eval = 0` modulo the multiopen decode that ties the opened columns to it. -/
theorem orchard_verifier_sound_deployed_C3 [DecidableEq G] [Inhabited G] {shape : Shape}
    (srs : SRS G) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ srs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hFS : FiatShamirTree srs b P v (DeployedAccepts srs hk vk ps ch))
    (hquot : ∀ a, IpaRelation srs P b v a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation srs P b v a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation srs P b v
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S := by
  obtain ⟨t, ht⟩ := hFS haccepts
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV srs b P v t ht
  have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
      (hquot a hrel) (hgood a hrel)
  exact hencodes a ⟨hrel, hsat⟩

end Zcash.Snark
