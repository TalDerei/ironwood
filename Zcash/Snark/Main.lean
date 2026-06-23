import Mathlib
import Zcash.Snark.KnowledgeSoundness
import Zcash.Snark.Assemble
import Zcash.Snark.Consistency
import Zcash.Snark.IpaSoundness

/-!
# Soundness composition: conditional, and the deployed accept condition

This module formalizes the composition that turns IPA knowledge soundness into the SNARK relation, in
two layers: a `_conditional` family over an opaque `accepts : Prop`, and a `_deployed` family over the
concrete accept condition `(assemble vk ps ch).eval … = 0` (the §1 fingerprint MSM). The conditional
theorems are named with a `_conditional` suffix to avoid overclaiming: they are scaffolds, not finished
soundness. The deployed soundness is carried to the named floor in `Zcash.Snark.Weld` (the AGM opening,
the multiopen decode, the derived constraint).

## Assumptions (the conditional family)

* **Opaque accept.** `accepts` is a free `Prop`, not instantiated to the deployed accept condition, so
  `orchard_verifier_sound_conditional` says nothing about the fingerprint. The `_deployed` variants fix
  this by taking `DeployedAccepts`.
* **Extraction bundled with Fiat–Shamir.** `ExtractableFromAcceptance` assumes the IPA
  knowledge-soundness conclusion (a consistent transcript tree + a valid opening), bundling Fiat–Shamir
  with the extraction that `accepting_fold_eq` / `extract_correct` prove — so those proven lemmas are
  off this path.
* **Circuit satisfaction assumed, not derived.** `ExtractableFromAcceptance` also supplies `circuitSat a`
  rather than deriving it from the deployed constraint check via `constraint_identity_of_accept` and the
  multiopen decode.
* **Binding inert.** `hbind` (DLR hardness) reaches `knowledge_sound` but only feeds its uniqueness
  conjunct, which this proof discards.

What is proven lives in the component lemmas (`extract_correct`, `accepting_fold_eq`, `commitGen_round`,
`quotientCheck_sound`, `ipaRelation_unique`, the binding reduction, `eval_combineGates`); the open work
is wiring them onto this path. `Zcash.Snark.Vesta` instantiates these at the concrete Vesta curve. See
`Zcash.Snark.KnowledgeSoundness` for the assumption list.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Assumed: acceptance yields the IPA extraction data, which is stronger than just Fiat–Shamir. Given
`accepts`, this hands over a consistent transcript tree and a valid opening — i.e. it assumes the IPA
knowledge-soundness *conclusion* that `accepting_fold_eq` / `extract_correct` produce, bundled with
Fiat–Shamir. Honest reading: assume IPA knowledge soundness + FS, not hand-wave only FS. Splitting this
into the genuine FS step (`accept → ∃ tree`) and the proven extraction — narrowing the residual to
"challenges are uniform and unpredictable" — is open. It also bundles `circuitSat a` (the extracted
witness satisfies the circuit); deriving that from the deployed constraint check is likewise open. -/
def ExtractableFromAcceptance (srs : SRS G) (P : G) (b : Fin (2 ^ srs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop) (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp srs.k) (a : Fin (2 ^ srs.k) → Fp),
    Consistent t a ∧ IpaRelation srs P b v a ∧ circuitSat a

-- TODO(semantic adequacy): `hencodes`/`S` below are the seam from circuit-satisfiability to the
-- high-level Orchard relation. `S` is a free `Prop` and `hencodes` is an assumed hypothesis, so the
-- chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and never reaches
-- "…therefore a valid Orchard action" (note well-formed, value balances, nullifier correctly derived,
-- spend authorized). Closing it: instantiate `S` to the concrete Orchard statement and prove `hencodes`.
-- The composition reaches only `SnarkRelation`; this is the output-side dual of the input-side
-- VK-correctness gap (see `Assemble.lean`). Large; not started.
/-- Conditional soundness composition (not completed soundness). From the assumed extraction data
(`hextract haccepts`, which also yields `circuitSat a`), conclude `S` via `hencodes`.

This assumes what §2 should prove: `accepts` is opaque (the `_deployed` variant fixes that); the
extraction + circuit-satisfaction are assumed (so `accepting_fold_eq` / `extract_correct` /
`constraint_identity_of_accept` are off-path); and `hbind`'s binding only feeds the discarded uniqueness
conjunct. The scaffold for the composition, not the composition — see the module docstring, and
`Zcash.Snark.Weld` for the deployed closures. -/
theorem orchard_verifier_sound_conditional (srs : SRS G) (hbind : CommitmentBinding (F := Fp) srs)
    {P : G} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance srs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen, hsat⟩ := hextract haccepts
  exact hencodes a (knowledge_sound srs hbind hcons hopen hsat).2.1

/-- The deployed verifier's accept condition as a concrete predicate: the assembled fingerprint MSM
`assemble vk ps ch` (the §1 object) evaluates to the group identity against the SRS. This is what
`accepts` should be — the formal object §1 and §2 share. (`hk` aligns the circuit shape's `k` with the
SRS's `k`.) -/
def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (srs : SRS G)
    (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  (hk ▸ assemble vk ps ch : Msm srs.k Fp G).eval srs = 0

/-! ## `IpaRelation` is derived from the transcript tree, not assumed

`Zcash.Snark.ipa_soundV` derives the full opening relation — `commit g a = P` and `⟨a,b⟩ = v` — from an
accepting IPA transcript tree (`IpaAcceptV`), binding-free, by 3-special soundness. So the bridge no
longer assumes `IpaRelation`. Honest caveat for `FiatShamirTree` below: it is not purely the rewinding —
it also absorbs (i) the MSM↔tree structural correspondence (that `assemble.eval = 0` unfolds into the
recursive checks for the proof's actual `P,b,v,L,R`) and (ii) the pinning of free `P,b,v` to the proof.
The cryptographic opening is genuinely derived; the residual bundle is structural. The flat half of (i) —
`assemble.eval` equals halo2's explicit IPA verifier equation with `G'₀ = foldAll` — is proven by
`deployed_verification_eq` (`Zcash.Snark.Weld`) and is load-bearing in `orchard_verifier_sound_deployed_pinned`,
which rewinds that explicit equation rather than the opaque accept. -/

/-- `IpaAcceptV` over the SRS generators derives `IpaRelation`: the witness `ipa_soundV` extracts opens
`P` (`commit srs a = commitGen srs.g a`) and gives the inner product (`commitGen b a = ⟨a,b⟩`). The IPA
opening is derived, not assumed. -/
theorem ipaRelation_of_acceptV (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G srs.k) (h : IpaAcceptV srs.g b P v t) :
    ∃ a, IpaRelation srs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV srs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- The transcript-tree bridge, superseded by `Zcash.Snark.DeployedIpaRewind`. Acceptance yields a clean
`IpaAcceptV` tree. This absorbed two things beyond the rewinding: (i) the MSM↔tree structural
correspondence and (ii) the `U`/`W`/`S` separation (since `IpaAcceptV` is the blinding-free IPA). Of
these, (ii) is now proven and on-path (`Zcash.Snark.deployed_ipa_soundV`), and the flat half of (i) is
proven (`foldAll = G'₀`, `compute_b = ⟨sFun, evalVector⟩`; `deployed_verification_eq`). That flat fact is
wired in `orchard_verifier_sound_deployed_pinned`, which rewinds halo2's explicit IPA verifier equation
(`DeployedIpaVerifierEq`) rather than the opaque accept; what `deployed_verification_eq` does not by itself
remove is the rewinding (the flat→recursive-tree forking). Prefer the capstones
`orchard_verifier_sound_deployed_full`/`_pinned`/`_closed` over the `_opening`/`_constraint` theorems that
use this, but read their residual notes. -/
def FiatShamirTree (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (P : G) (v : Fp) (accepts : Prop) : Prop :=
  accepts → ∃ t : IpaTreeV Fp G srs.k, IpaAcceptV srs.g b P v t

/-- The deployed Orchard verifier is sound, opening derived. From the deployed accept (`assemble.eval = 0`),
the minimal Fiat–Shamir bridge `hFS` (acceptance yields the transcript tree — the only IPA assumption),
and the circuit-satisfaction of the opening (`hcirc`, the constraint side, dischargeable by
`circuitSatViaGates_of_check`), conclude `S`.

The IPA opening (`IpaRelation`) is derived here via `ipaRelation_of_acceptV`/`ipa_soundV`, not assumed (the
earlier conditional bridges that bundled it have been removed). Honest scope: `hFS` still absorbs the
MSM↔tree correspondence + `P,b,v` pinning (see `FiatShamirTree`), and `hcirc` is the assumed constraint
side, which `orchard_verifier_sound_deployed_constraint` derives from the gate check. Superseded by
`orchard_verifier_sound_deployed_full`/`_pinned`/`_closed` (`Zcash.Snark.Weld`), which peel `U`/`W`/`S`,
wire the multiopen decode, and (in `_pinned`) rewind halo2's explicit IPA equation; prefer those. Named
assumptions: the bridge (`hFS`), the constraint side (`hcirc`), DLR hardness (for uniqueness, unused on
this path), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_deployed_opening [DecidableEq G] [Inhabited G] {shape : Shape}
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

/-! ## `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

The constraint side mirrors the opening side. The verifier checks the gate identity only at the challenge
`x` — a point check (`quotientCheck`, `numerator.eval x = h.eval x · (xⁿ−1)`). `circuitSatViaGates_of_check`
lifts that point check to the polynomial identity `circuitSatViaGates` (the witness's decoded columns
satisfy the gates) provided `x` avoids the Schwartz–Zippel bad set (`hgood`). So `circuitSat`, instantiated
to the concrete `circuitSatViaGates`, is derived from the verifier's actual gate check — no black-box
`hcirc`. -/

open Polynomial in
/-- The deployed Orchard verifier is sound, opening and constraint both derived. Both conjuncts of
`SnarkRelation` are derived, not assumed: `IpaRelation` (the opening) from the transcript tree via
`ipa_soundV`; and `circuitSat` — instantiated to `circuitSatViaGates` — from the verifier's quotient/gate
point check `hquot` at the challenge `x`, lifted to the polynomial identity by Schwartz–Zippel (`hgood`),
via `circuitSatViaGates_of_check`.

The black-box `hcirc` is gone. What remains are the verifier's actual checks and the standard assumptions:
the special-soundness rewinding tree (`hFS`), the gate point-check (`hquot`), the SZ good challenge
(`hgood`), and VK-correctness (`hencodes`). `hquot`/`hgood` are the constraint-side analog of `hFS` — the
gate check is part of `assemble.eval = 0` modulo the multiopen decode that ties the opened columns to it. -/
theorem orchard_verifier_sound_deployed_constraint [DecidableEq G] [Inhabited G] {shape : Shape}
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
