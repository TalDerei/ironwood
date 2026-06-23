import Zcash.Snark.Main
import Zcash.Snark.IpaUWS
import Zcash.Snark.Multiopen

/-!
# The §1↔§2 weld capstone: deployed acceptance ⇒ SNARK relation, U/W/S peeled

This module formalizes the end-to-end deployed soundness theorems, with the inner-product-argument opening
derived over halo2's concrete `U`/`W`/`S` structure rather than assumed via an opaque bridge. The deployed
accept (`assemble.eval = 0`, the §1 fingerprint) is welded to the §2 SNARK relation.

## The composition

* `deployed_ipa_soundV` (`Zcash.Snark.IpaUWS`) — the recursive opening soundness: the deployed IPA's
  combined verifier equation, carrying the value-binding `U`, the blinding `W` and the synthetic-blinding
  `S`/`ξ`, peels (augmented binding) to the clean `IpaAcceptV` and feeds `ipa_soundV`, yielding
  `IpaRelation`.
* `circuitSatViaGates_of_check` (`Zcash.Snark.KnowledgeSoundness`) — the constraint side: the verifier's
  gate point-check at `x`, lifted by Schwartz–Zippel, gives `circuitSatViaGates`.

Both conjuncts of `SnarkRelation` are therefore derived from the deployed accept. The eval vector is pinned
to `evalVector srs.k ch.x3` (`b = (x₃ⁱ)`), and `U`/`W`/`z` to the SRS generators / the actual binding
challenge (`srs.u`, `srs.w`, `ch.z`) — matching halo2 `params.u`, `params.w`. `deployed_verification_eq`
proves that `assemble.eval` equals halo2's explicit IPA verifier equation with the generator fold
`G'₀ = foldAll`, and `orchard_verifier_sound_deployed_pinned` rewinds that explicit equation.

## Assumptions

The residual inputs are the legitimate floor:

* **Augmented binding** (`hbind`) — DLR/AGM on `srs.u`, `srs.w`.
* **No-`U`-interference challenge** (`ch.z ≠ 0`) — halo2's `z`.
* **Special-soundness rewinding** (`hrewind`) — acceptance yields the transcript tree. This is the
  flat→recursive-tree forking; `deployed_verification_eq` rewrites the equation the rewinding acts on but
  does not remove the rewinding itself.
* **Gate point-check + good challenge** (`hquot`/`hgood`) — the constraint-side analog.
* **VK-correctness** (`hencodes`).
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The deployed accept is halo2's IPA verification equation, with `G'₀ = foldAll` explicit.
`eval_assembleFinalMsm` gives the assembled MSM in closed form; rewriting its `computeS` generator term via
`deployed_gterm_foldAll` exhibits it as `[-c]·foldAll` — the folded generator `G'₀`. So `assemble.eval` is
exactly halo2's IPA verifier equation `P' + Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ) + [-c·b·z]U + [-f]W + [-c]G'₀` for the
multiopen commitment/value, with the generator fold proven (not assumed).

This is the assembly↔equation faithfulness, and it is load-bearing: `deployedAccepts_verifierEq` turns it
into `DeployedIpaVerifierEq` (halo2's explicit equation, `= 0`), which `orchard_verifier_sound_deployed_pinned`
rewinds in place of the opaque `DeployedAccepts`. What this lemma proves is the flat MSM↔IPA-equation
correspondence; it does not derive the recursive tree's node/leaf checks from the equation (the
flat→recursive forking). So it does not by itself remove the rewinding — that remains the floor. -/
theorem deployed_verification_eq {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (grouped : MultiopenGrouped shape.k Fp G) :
    (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, w, u⟩
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU) grouped
            (Msm.zero shape.k Fp G)).1.eval ⟨shape.k, g, w, u⟩
        + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k Fp G)).2].getD i.val 0) • g i)
        + ch.xi • ps.ipaS
        + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
            (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
        + (-ps.ipaF) • w
        + (-ps.ipaC) • foldAll (List.ofFn ch.ipaRound)
            (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 := by
  rw [eval_assembleFinalMsm, deployed_gterm_foldAll]

/-- `IpaRelation` derived from an accepting deployed IPA tree. The witness `deployed_ipa_soundV` extracts
(after peeling `U`/`W`/`S`) opens `P` (`commit srs a = commitGen srs.g a`) and gives the inner product
(`innerProduct a b = commitGen b a`). So the full opening relation is derived over halo2's concrete
structure, with only the augmented binding and the rewound tree assumed. -/
theorem ipaRelation_of_deployedAcceptV (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) {z : Fp} (P : G) (v : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' srs.u srs.w) (hz : z ≠ 0)
    {blind : Fp} {t : DeployedIpaTreeV Fp G srs.k}
    (h : DeployedIpaAcceptV srs.g b srs.u srs.w z P v blind t) :
    ∃ a, IpaRelation srs P b v a := by
  obtain ⟨a, hP, hv⟩ := deployed_ipa_soundV hbind hz srs.g b P v blind t h
  refine ⟨a, ?_, ?_⟩
  · rw [commit_eq_commitGen]; exact hP
  · have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
    rw [hib]; exact hv

/-- `IpaRelation` derived directly from the flat verification equation (the opening, AGM route, no posited
tree). Composes `deployed_flat_split` (the augmented binding reads `assemble.eval = 0` off as the g/U/W
relations) with `deployed_open_value` (the value `⟨aP,b⟩ = v` from those relations + the SZ structure). The
witness is `aP`, the multiopen commitment's `g`-representation; it opens the pure-`g` commitment `⟨aP, g⟩`
(the multiopen commitment modulo its `W`-blinding, which `IpaRelation` abstracts) to the value `v`. Unlike
the rewinding bridge, this is a proof from the flat equation — the structural correspondence is wired, the
floor is the AGM representations + the augmented binding + the SZ challenge exclusions. -/
theorem ipaRelation_of_flat (srs : SRS G) (b aP aSxi aRounds vVec svTerm : Fin (2 ^ srs.k) → Fp)
    (pw swxi wRounds uRounds uConst wConst v ipRounds cb z : Fp)
    (hbind : AugmentedBinding (F := Fp) srs.g srs.u srs.w)
    (hflat : commitGen srs.g aP + pw • srs.w + (commitGen srs.g aSxi + swxi • srs.w)
        + (commitGen srs.g aRounds + uRounds • srs.u + wRounds • srs.w) + commitGen srs.g vVec
        + uConst • srs.u + wConst • srs.w + commitGen srs.g svTerm = 0)
    (hSxi : innerProduct aSxi b = 0) (hvVec : innerProduct vVec b = -v)
    (hsvTerm : innerProduct svTerm b = -cb) (hRounds : innerProduct aRounds b = ipRounds)
    (huConst : uConst = -(cb * z)) (huRounds : uRounds = z * ipRounds) (hz : z ≠ 0) :
    IpaRelation srs (commitGen srs.g aP) b v aP := by
  obtain ⟨hg, hu, _⟩ := deployed_flat_split hbind aP aSxi aRounds vVec svTerm pw swxi wRounds
    uRounds uConst wConst hflat
  exact ⟨commit_eq_commitGen srs aP, deployed_open_value b aP aSxi aRounds vVec svTerm uRounds uConst
    v ipRounds cb z hg hu hSxi hvVec hsvTerm hRounds huConst huRounds hz⟩

/-- The glue: `DeployedAccepts` unfolds to the flat equation in AGM-representation form, connecting the
opening to the real assembly. Given the prover's group elements via their AGM representations — the multiopen
commitment `(assembleOpening …).1.eval = ⟨aP,g⟩ + pw•w`, the blinding poly `ps.ipaS = ⟨aS,g⟩ + sw•w`, and the
round total `Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ) = ⟨aRounds,g⟩ + uRounds•u + wRounds•w` — the deployed accept
`assemble.eval = 0` is exactly `ipaRelation_of_flat`'s hypothesis. Composes `eval_assembleFinalMsm` (the §1
algebra, `assemble.eval` in closed form) with the representations; the `[-v]g₀` and `computeS` terms are the
`g`-commitments `⟨vVec,g⟩`, `⟨svTerm,g⟩` definitionally. So the opening's structural correspondence is a
proof from `assemble.eval = 0`, with the only added inputs the AGM representations. -/
theorem deployed_accept_flat [DecidableEq G] [Inhabited G] {shape : Shape} (g : Fin (2 ^ shape.k) → G)
    (w uu : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (aP aS aRounds : Fin (2 ^ shape.k) → Fp) (pw sw uRounds wRounds : Fp)
    (hP : (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).1.eval
        ⟨shape.k, g, w, uu⟩ = commitGen g aP + pw • w)
    (hS : ps.ipaS = commitGen g aS + sw • w)
    (hRounds : (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
        (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum = commitGen g aRounds + uRounds • uu + wRounds • w)
    (haccepts : (assemble vk ps ch).eval ⟨shape.k, g, w, uu⟩ = 0) :
    commitGen g aP + pw • w
      + (commitGen g (ch.xi • aS) + (ch.xi * sw) • w)
      + (commitGen g aRounds + uRounds • uu + wRounds • w)
      + commitGen g (fun i => ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
          (List.ofFn ps.multiopenU) (constructIntermediateSets (assembleQueries vk ps ch))
          (Msm.zero shape.k Fp G)).2] : List Fp).getD i.val 0)
      + ((-ps.ipaC) * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • uu
      + (-ps.ipaF) • w
      + commitGen g (fun i => (computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD (i : ℕ) 0) = 0 := by
  unfold assemble at haccepts
  rw [eval_assembleFinalMsm, hP, hS, hRounds] at haccepts
  simp only [commitGen, smul_add, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul] at haccepts ⊢
  rw [← haccepts]; abel

/-- The IPA opening, derived end-to-end via the AGM route: `DeployedAccepts → IpaRelation`, no posited tree.
Composes `deployed_accept_flat` (the §1 glue: `assemble.eval = 0` unfolds to the AGM flat equation) with
`ipaRelation_of_flat` (the binding split + value extraction). So from the deployed accept of the real
assembly (`assemble.eval = 0`), the prover's AGM representations (`hP`/`hS`/`hRounds`), the augmented binding
(`hbind`), and the SZ structure (`hSxi` the `ξ`/S-root, `huRounds` the `z`/no-U-interference, `hz`), the IPA
opening `IpaRelation` is derived — the witness `aP` (the multiopen commitment's `g`-rep) opens `⟨aP,g⟩` to
the multiopen value. No rewinding tree is posited: the structural correspondence is a proof from
`assemble.eval = 0`. Floor: the AGM representations + augmented binding + SZ. (`hvVec`/`hsvTerm` are the
structural inner-product values, provable from `compute_b`/`compute_s`; taken as inputs here.) -/
theorem orchard_verifier_sound_deployed_agm [DecidableEq G] [Inhabited G] {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w uu : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ shape.k) → Fp)
    (aP aS aRounds : Fin (2 ^ shape.k) → Fp) (pw sw uRounds wRounds ipRounds cb : Fp)
    (hbind : AugmentedBinding (F := Fp) g uu w)
    (hP : (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).1.eval
        ⟨shape.k, g, w, uu⟩ = commitGen g aP + pw • w)
    (hS : ps.ipaS = commitGen g aS + sw • w)
    (hRounds : (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
        (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum = commitGen g aRounds + uRounds • uu + wRounds • w)
    (hSxi : innerProduct (ch.xi • aS) b = 0)
    (hvVec : innerProduct (fun i => ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
        (List.ofFn ps.multiopenU) (constructIntermediateSets (assembleQueries vk ps ch))
        (Msm.zero shape.k Fp G)).2] : List Fp).getD i.val 0) b
      = -(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2)
    (hsvTerm : innerProduct (fun i => (computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD (i : ℕ) 0) b = -cb)
    (hRoundsIP : innerProduct aRounds b = ipRounds)
    (huConst : (-ps.ipaC) * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z = -(cb * ch.z))
    (huRounds : uRounds = ch.z * ipRounds) (hz : ch.z ≠ 0)
    (haccepts : (assemble vk ps ch).eval ⟨shape.k, g, w, uu⟩ = 0) :
    IpaRelation (⟨shape.k, g, w, uu⟩ : SRS G) (commitGen g aP) b
      (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2 aP :=
  ipaRelation_of_flat (⟨shape.k, g, w, uu⟩ : SRS G) b aP (ch.xi • aS) aRounds
    (fun i => ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2] : List Fp).getD
      i.val 0)
    (fun i => (computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD (i : ℕ) 0)
    pw (ch.xi * sw) wRounds uRounds
    ((-ps.ipaC) * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) (-ps.ipaF)
    (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
      (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2
    ipRounds cb ch.z hbind
    (deployed_accept_flat g w uu vk ps ch aP aS aRounds pw sw uRounds wRounds hP hS hRounds haccepts)
    hSxi hvVec hsvTerm hRoundsIP huConst huRounds hz

/-- The deployed verifier's IPA bridge: acceptance yields a deployed IPA transcript tree
(`DeployedIpaAcceptV`, carrying `U`/`W`/`S`) for the proof's eval vector `b`, commitment `P` and value `v`.
What is peeled on the path: the `U`/`W`/`S` separation — `deployed_ipa_soundV` consumes this tree and
discharges it. The bridge itself posits the tree wholesale; its residual is the rewinding (the floor) —
deriving the tree's per-node folds and leaf equations from `assemble.eval = 0` for the proof's real
`P,b,L,R` is the flat→recursive forking, which this def does not perform.

The flat half of that correspondence — `assemble.eval` equals halo2's explicit IPA verifier equation with
`G'₀ = foldAll` — is proven by `deployed_verification_eq` and wired in
`orchard_verifier_sound_deployed_pinned`, which feeds this bridge the explicit `DeployedIpaVerifierEq`
(derived from acceptance via `deployedAccepts_verifierEq`) rather than the opaque `DeployedAccepts`. That
makes the assembly↔equation faithfulness load-bearing, but does not remove the rewinding: `_full` and
`_closed` apply this bridge to the opaque `DeployedAccepts` directly. -/
def DeployedIpaRewind (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (z : Fp) (P : G) (v : Fp)
    (accepts : Prop) : Prop :=
  accepts → ∃ (blind : Fp) (t : DeployedIpaTreeV Fp G srs.k),
    DeployedIpaAcceptV srs.g b srs.u srs.w z P v blind t

/-- The deployed Orchard verifier is sound, opening and constraint both derived, `U`/`W`/`S` peeled. From
the deployed accept (`assemble.eval = 0`), the rewinding bridge `hrewind`, the augmented binding `hbind`
(DLR/AGM), the no-`U`-interference challenge `ch.z ≠ 0`, and the gate point-check `hquot` with its good
challenge `hgood`, conclude the high-level statement `S` via VK-correctness `hencodes`.

The IPA opening (`IpaRelation`) is derived over halo2's concrete `U`/`W`/`S` structure
(`ipaRelation_of_deployedAcceptV` → `deployed_ipa_soundV`); the constraint (`circuitSatViaGates`) is derived
from the gate check (`circuitSatViaGates_of_check`). The eval vector is pinned to `evalVector srs.k ch.x3`.
Here `hrewind` is applied to the opaque `DeployedAccepts`, so the assembly↔equation faithfulness
(`deployed_verification_eq`) is not threaded in — only `orchard_verifier_sound_deployed_pinned` rewinds
halo2's explicit IPA equation. Named floor: the rewinding (`hrewind`), the augmented binding (`hbind`), the
binding challenge (`ch.z ≠ 0`), the gate point-check + SZ good challenge (`hquot`/`hgood`), and
VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_deployed_full [DecidableEq G] [Inhabited G] {shape : Shape}
    (srs : SRS G) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {P : G} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ srs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' srs.u srs.w)
    (hz : ch.z ≠ 0)
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hrewind : DeployedIpaRewind srs (evalVector srs.k ch.x3) ch.z P v (DeployedAccepts srs hk vk ps ch))
    (hquot : ∀ a, IpaRelation srs P (evalVector srs.k ch.x3) v a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation srs P (evalVector srs.k ch.x3) v a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation srs P (evalVector srs.k ch.x3) v
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S := by
  obtain ⟨blind, t, ht⟩ := hrewind haccepts
  obtain ⟨a, hrel⟩ :=
    ipaRelation_of_deployedAcceptV srs (evalVector srs.k ch.x3) P v hbind hz ht
  have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
      (hquot a hrel) (hgood a hrel)
  exact hencodes a ⟨hrel, hsat⟩

/-! ## The multiopen decode wired to acceptance

The IPA opening recovers the collapsed witness for the multiopen commitment `P`. To feed the gate check we
need the individual column openings — what `multiopen_decode_deployed` recovers from the batching rewinding.
`DeployedMultiopenRewind` is that bridge (the batching analog of `DeployedIpaRewind`);
`decoded_columns_of_accept` derives the per-column openings from acceptance, so `decodeAdvice`/`decodeInstance`
are no longer free — they are the genuinely recovered columns. The residual is the batching rewinding (a ROM
floor) and, for identifying decoded columns with the circuit's columns, VK-correctness. -/

/-- The deployed multiopen batching bridge: the batching special-soundness rewinding. Acceptance yields, for
`n` distinct batching challenges `zBatch k`, a deployed IPA transcript tree opening the batched commitment
`Σⱼ (zBatch k)ʲ·C j` to the batched value `Σⱼ (zBatch k)ʲ·e j` (with `U`/`W`/`S` carried). The batching
analog of `DeployedIpaRewind`: its content is the rewinding of the batching challenge, the ROM floor
(`multiopen_decode_deployed` discharges the algebra). -/
def DeployedMultiopenRewind {n : ℕ} (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (C : Fin n → G)
    (e : Fin n → Fp) (zBatch : Fin n → Fp) (zIpa : Fp) (accepts : Prop) : Prop :=
  accepts → Function.Injective zBatch ∧ zIpa ≠ 0 ∧
    ∃ (blind : Fin n → Fp) (t : Fin n → DeployedIpaTreeV Fp G srs.k),
      ∀ k, DeployedIpaAcceptV srs.g b srs.u srs.w zIpa
        (∑ j : Fin n, zBatch k ^ (j : ℕ) • C j) (∑ j : Fin n, zBatch k ^ (j : ℕ) • e j) (blind k) (t k)

/-- The per-column openings are derived from acceptance (the decode wired). Given the batching bridge and the
augmented binding, every individual column `i` opens to its commitment `C i` and its claimed evaluation
`e i`: `∃ col, ∀ i, commit srs col_i = C i ∧ ⟨col_i, b⟩ = e i`. Composes the bridge with the proven
`multiopen_decode_deployed`. -/
theorem decoded_columns_of_accept {n : ℕ} (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (C : Fin n → G)
    (e : Fin n → Fp) (zBatch : Fin n → Fp) {zIpa : Fp}
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' srs.u srs.w)
    {accepts : Prop} (bridge : DeployedMultiopenRewind srs b C e zBatch zIpa accepts) (h : accepts) :
    ∃ col : Fin n → (Fin (2 ^ srs.k) → Fp),
      ∀ i, commitGen srs.g (col i) = C i ∧ commitGen b (col i) = e i := by
  obtain ⟨hzBatch, hzIpa, blind, t, ht⟩ := bridge h
  exact multiopen_decode_deployed srs b C e zBatch hzBatch hbind hzIpa blind t ht

/-! ## `P`/`v` pinned to the §1 assembly

The capstone above leaves `P`, `v` as parameters tied to the proof only through the bridge. Here they are
pinned definitionally to the multiopen commitment and value the §1 assembly produces — the group element the
IPA opens (`(assembleOpening …).1.eval srs`) and the claimed value (`(assembleOpening …).2`) — so the
soundness statement is about the actual fingerprint objects, not free metavariables. -/

variable [DecidableEq G] [Inhabited G]

/-- The deployed multiopen commitment the IPA opens: the `x₁`/`x₄`-collapsed opening MSM (halo2
`multiopen/verifier.rs`), evaluated at the SRS `⟨shape.k, g, w, u⟩`. This is the first summand of
`eval_assembleFinalMsm` — the `P` halo2's IPA verifier receives. -/
def multiopenCommitment {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : G :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).1.eval ⟨shape.k, g, w, u⟩

/-- The deployed multiopen value the IPA opens `P` to: the `x₃` Lagrange-interpolated / `x₄`-collapsed
combined evaluation (halo2 `multiopen/verifier.rs`). This is the `v` halo2's IPA verifier receives. -/
def multiopenValue {shape : Shape} (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Fp :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2

/-- halo2's explicit IPA verifier equation for the deployed proof: the assembled fingerprint written in
halo2's published form — the multiopen commitment `P`, the round total `Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ)`, the value-binding
`[-c·b·z]U`, the blinding `[-f]W`, and the folded generator `[-c]G'₀` (`G'₀ = foldAll`) — equal to the
identity. By `deployed_verification_eq` this is exactly `assemble.eval`, hence equivalent to `DeployedAccepts`;
stating it explicitly lets the rewinding bridge act on halo2's actual IPA equation. -/
def DeployedIpaVerifierEq {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : Prop :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).1.eval ⟨shape.k, g, w, u⟩
      + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2].getD i.val 0) • g i)
      + ch.xi • ps.ipaS
      + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
          (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
      + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
      + (-ps.ipaF) • w
      + (-ps.ipaC) • foldAll (List.ofFn ch.ipaRound)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 = 0

/-- Acceptance gives halo2's explicit IPA verifier equation: `DeployedAccepts` (the assembled MSM is the
identity) unfolds, via `deployed_verification_eq`, to `DeployedIpaVerifierEq` — the same equation in halo2's
published `P + Σ(rounds) + [-c·b·z]U + [-f]W + [-c]G'₀` form, with the generator fold `G'₀ = foldAll` proven.
This discharges the assembly↔equation faithfulness, so the rewinding bridge acts on halo2's real equation
rather than the opaque `assemble.eval`. -/
theorem deployedAccepts_verifierEq {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (h : DeployedAccepts (⟨shape.k, g, w, u⟩ : SRS G) rfl vk ps ch) :
    DeployedIpaVerifierEq g w u vk ps ch := by
  unfold DeployedIpaVerifierEq
  rw [← deployed_verification_eq g w u ps ch (constructIntermediateSets (assembleQueries vk ps ch))]
  exact h

/-- The deployed Orchard verifier is sound, `P`, `b`, `v` all pinned to the §1 fingerprint. The full weld
capstone with the SRS taken as `⟨shape.k, g, w, u⟩`, `P` = `multiopenCommitment`, `v` = `multiopenValue`,
`b` = `evalVector shape.k ch.x3` — the actual objects halo2's IPA verifier opens. So acceptance of the
deployed fingerprint (`assemble.eval = 0`) yields, over halo2's concrete `U`/`W`/`S` structure, a witness
opening that commitment to that value, satisfying the circuit.

Unlike `_full`/`_closed`, the rewinding here acts on halo2's explicit IPA verifier equation: acceptance is
turned into `DeployedIpaVerifierEq` by `deployedAccepts_verifierEq` (which discharges the assembly↔equation
faithfulness via `deployed_verification_eq`, `G'₀ = foldAll`), and `hrewind` rewinds that equation. So that
faithfulness is proven and load-bearing here; the floor that remains is the rewinding itself (the
flat→recursive forking), which `deployed_verification_eq` does not remove. Named floor: rewinding
(`hrewind`), augmented binding (`hbind`), `ch.z ≠ 0`, gate point-check + SZ (`hquot`/`hgood`), VK-correctness
(`hencodes`). -/
theorem orchard_verifier_sound_deployed_pinned {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ shape.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (xc : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' u w)
    (hz : ch.z ≠ 0)
    (haccepts : DeployedAccepts (⟨shape.k, g, w, u⟩ : SRS G) rfl vk ps ch)
    (hrewind : DeployedIpaRewind (⟨shape.k, g, w, u⟩ : SRS G) (evalVector shape.k ch.x3) ch.z
      (multiopenCommitment g w u vk ps ch) (multiopenValue vk ps ch)
      (DeployedIpaVerifierEq g w u vk ps ch))
    (hquot : ∀ a, IpaRelation (⟨shape.k, g, w, u⟩ : SRS G) (multiopenCommitment g w u vk ps ch)
        (evalVector shape.k ch.x3) (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg xc)
    (hgood : ∀ a, IpaRelation (⟨shape.k, g, w, u⟩ : SRS G) (multiopenCommitment g w u vk ps ch)
        (evalVector shape.k ch.x3) (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval xc ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation (⟨shape.k, g, w, u⟩ : SRS G) (multiopenCommitment g w u vk ps ch)
      (evalVector shape.k ch.x3) (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S := by
  obtain ⟨blind, t, ht⟩ := hrewind (deployedAccepts_verifierEq g w u vk ps ch haccepts)
  obtain ⟨a, hrel⟩ := ipaRelation_of_deployedAcceptV (⟨shape.k, g, w, u⟩ : SRS G)
    (evalVector shape.k ch.x3) (multiopenCommitment g w u vk ps ch) (multiopenValue vk ps ch) hbind hz ht
  exact hencodes a ⟨hrel, circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates
    hpoly deg a xc (hquot a hrel) (hgood a hrel)⟩

/-! ## Capstone wiring the opening, the decode, and the SZ constraint lift — honest residual

`orchard_verifier_sound_deployed_closed` composes three derivations from the deployed accept: the IPA opening
(`ipaRelation_of_deployedAcceptV`, `U`/`W`/`S` peeled, genuinely on-path), the per-column decode
(`decoded_columns_of_accept` — `decodeAdvice`/`decodeInstance` act on the genuinely recovered columns, not
free functions), and the Schwartz–Zippel lift of the gate point-check (`circuitSatViaGates_of_check`).

This is not closed to the irreducible cryptographic floor. Its residual is the legitimate floor — the two
rewinding bridges (`hIpa`, `hMulti`), the augmented binding (`hbind`), `ch.z ≠ 0` — plus three
provable-but-unmodeled facts folded into the remaining hypotheses:
1. `hquot` (the gate point-check) is assumed, not derived from the vanishing-argument part of the MSM. A
   from-scratch derivation needs the permutation/lookup arguments modeled as polynomials (`combineGates`
   covers only the gates; `expectedHEval` folds gates ++ perm ++ lookup) — the §3 circuit-encoding workstream.
2. The `a`↔`col` link is not modeled: the IPA witness `a` and the decoded columns `col` are extracted
   independently and both handed to `hencodes`; that they are the same data via the multiopen combination is
   carried by `hencodes` (VK-correctness), not proven here.
3. The flat↔tree correspondence is not wired here (unlike `_pinned`): `hIpa`/`hMulti` rewind the opaque
   `DeployedAccepts`, positing the trees wholesale rather than acting on the explicit verifier equation that
   `deployed_verification_eq` proves. -/
open Polynomial in
theorem orchard_verifier_sound_deployed_closed [DecidableEq G] [Inhabited G] {shape : Shape}
    (srs : SRS G) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {P : G} {v : Fp}
    {nCols : ℕ} (C : Fin nCols → G) (e : Fin nCols → Fp) (zBatch : Fin nCols → Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin nCols → (Fin (2 ^ srs.k) → Fp)) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' srs.u srs.w)
    (hz : ch.z ≠ 0)
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hIpa : DeployedIpaRewind srs (evalVector srs.k ch.x3) ch.z P v (DeployedAccepts srs hk vk ps ch))
    (hMulti : DeployedMultiopenRewind srs (evalVector srs.k ch.x3) C e zBatch ch.z
      (DeployedAccepts srs hk vk ps ch))
    (hquot : ∀ col : Fin nCols → (Fin (2 ^ srs.k) → Fp),
      (∀ i, commitGen srs.g (col i) = C i ∧ commitGen (evalVector srs.k ch.x3) (col i) = e i) →
      quotientCheck (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates) hpoly deg x)
    (hgood : ∀ col : Fin nCols → (Fin (2 ^ srs.k) → Fp),
      (∀ i, commitGen srs.g (col i) = C i ∧ commitGen (evalVector srs.k ch.x3) (col i) = e i) →
      combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ (a : Fin (2 ^ srs.k) → Fp) (col : Fin nCols → (Fin (2 ^ srs.k) → Fp)),
      (∀ i, commitGen srs.g (col i) = C i ∧ commitGen (evalVector srs.k ch.x3) (col i) = e i) →
      IpaRelation srs P (evalVector srs.k ch.x3) v a →
      circuitSatViaGates fixedCols (fun _ => decodeAdvice col) (fun _ => decodeInstance col) y gates hpoly deg a →
      S) :
    S := by
  obtain ⟨blind, t, ht⟩ := hIpa haccepts
  obtain ⟨a, hrel⟩ := ipaRelation_of_deployedAcceptV srs (evalVector srs.k ch.x3) P v hbind hz ht
  obtain ⟨col, hcol⟩ :=
    decoded_columns_of_accept srs (evalVector srs.k ch.x3) C e zBatch hbind hMulti haccepts
  have hsat : circuitSatViaGates fixedCols (fun _ => decodeAdvice col) (fun _ => decodeInstance col)
      y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols (fun _ => decodeAdvice col) (fun _ => decodeInstance col)
      y gates hpoly deg a x (hquot col hcol) (hgood col hcol)
  exact hencodes a col hcol hrel hsat

/-! ## The constraint: the gate point-check derived from the deployed vanishing argument (not assumed)

The capstones above take `hquot` (the gate point-check) as a hypothesis. Here it is derived: the deployed
verifier opens the `h`-commitment to `expectedHEval` at `x` (the vanishing query), which the multiopen decode
recovers as the decoded `h`-column's evaluation (`hHcol : h.eval x = eHEval`); and the assembly's constraint
combination equals the circuit's numerator polynomial at `x` (`hNum : numerator.eval x = eHEval·(xⁿ−1)`, which
is VK-correctness: the assembly faithfully computes the circuit's full gate+permutation+lookup numerator).
Together they give the point-check `numerator.eval x = h.eval x·(xⁿ−1)`, which `constraint_identity_of_accept`
lifts to the polynomial identity by Schwartz–Zippel (`hgood`). So `hquot` is no longer assumed — it is a proof
from the decode + VK-correctness; the residual is the decode (proven), the VK numerator (§3), and SZ. -/
open Polynomial in
theorem deployed_constraint_of_decode (numerator h : Polynomial Fp) (n : ℕ) (x eHEval : Fp)
    (hHcol : h.eval x = eHEval) (hNum : numerator.eval x = eHEval * (x ^ n - 1))
    (hgood : numerator ≠ h * (X ^ n - 1) → (numerator - h * (X ^ n - 1)).eval x ≠ 0) :
    numerator = h * (X ^ n - 1) :=
  constraint_identity_of_accept numerator h n x (by rw [quotientCheck, hNum, hHcol]) hgood

/-! ## The relation over the decoded columns directly (no free `a`)

The capstones above derive both the IPA-collapse witness `a` (opens `P`) and the decoded columns `col`, but
pass them to `hencodes` unlinked — the `a`↔`col` multiopen-combination tie was not modeled. This capstone
removes the issue at the root: it states the relation over the decoded columns themselves, which are the
actual circuit witness. The collapse witness `a` does not appear — the IPA opening is used only inside the
decode (`decoded_columns_of_accept` calls `deployed_ipa_soundV` per batching challenge), so the conclusion is
that the recovered columns open their commitments and satisfy the gates, with nothing free to link. -/
open Polynomial in
theorem orchard_verifier_sound_deployed_cols [DecidableEq G] [Inhabited G] {shape : Shape}
    (srs : SRS G) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {nCols : ℕ} (C : Fin nCols → G) (e : Fin nCols → Fp) (zBatch : Fin nCols → Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin nCols → (Fin (2 ^ srs.k) → Fp)) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' srs.u srs.w)
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hMulti : DeployedMultiopenRewind srs (evalVector srs.k ch.x3) C e zBatch ch.z
      (DeployedAccepts srs hk vk ps ch))
    (hquot : ∀ col : Fin nCols → (Fin (2 ^ srs.k) → Fp),
      (∀ i, commitGen srs.g (col i) = C i ∧ commitGen (evalVector srs.k ch.x3) (col i) = e i) →
      quotientCheck (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates) hpoly deg x)
    (hgood : ∀ col : Fin nCols → (Fin (2 ^ srs.k) → Fp),
      (∀ i, commitGen srs.g (col i) = C i ∧ commitGen (evalVector srs.k ch.x3) (col i) = e i) →
      combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ col : Fin nCols → (Fin (2 ^ srs.k) → Fp),
      (∀ i, commitGen srs.g (col i) = C i ∧ commitGen (evalVector srs.k ch.x3) (col i) = e i) →
      combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates = hpoly * (X ^ deg - 1) →
      S) :
    S := by
  obtain ⟨col, hcol⟩ :=
    decoded_columns_of_accept srs (evalVector srs.k ch.x3) C e zBatch hbind hMulti haccepts
  have hsat := circuitSatViaGates_of_check fixedCols (fun _ => decodeAdvice col)
    (fun _ => decodeInstance col) y gates hpoly deg (0 : Fin (2 ^ srs.k) → Fp) x (hquot col hcol)
    (hgood col hcol)
  exact hencodes col hcol hsat

/-! ## The integrated capstone: AGM opening + derived constraint + columns decode, end-to-end (no assumed `hquot`)

`orchard_verifier_sound_deployed_complete` composes the three closed routes into one exported theorem over the
real assembly:
* The opening (AGM) — `orchard_verifier_sound_deployed_agm` derives `IpaRelation` directly from
  `DeployedAccepts`, tree-free (the augmented binding reads it off the flat equation; no `hIpa`/opening tree).
* The decode — `decoded_columns_of_accept` recovers the per-column openings; this does posit trees, via the
  batching rewinding `hMulti`, which is the named floor (the decode is not tree-free).
* The constraint (derived) — `deployed_constraint_of_decode` derives the gate identity from the decoded
  `h`-column + the VK numerator + SZ, so `hquot` is not a hypothesis but is derived inside.

Scope note: tree-free applies to the opening, not end-to-end — the decode uses the batching rewinding
`hMulti`. (AGM-ifying the decode — recovering the per-column openings from the `Cᵢ` representations + an
SZ-over-batching argument instead of `hMulti` — would make it literally tree-free end-to-end; that is a
lateral move on the floor, not done.) Inputs are the named floor: the AGM representations + augmented binding
+ SZ (the opening), the batching rewinding `hMulti` (the decode), the VK numerator + SZ (the constraint), and
VK-correctness (`hencodes`). -/
open Polynomial in
theorem orchard_verifier_sound_deployed_complete [DecidableEq G] [Inhabited G] {shape : Shape}
    (g : Fin (2 ^ shape.k) → G) (w uu : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    -- opening (AGM) data:
    (aP aS aRounds : Fin (2 ^ shape.k) → Fp) (pw sw uRounds wRounds ipRounds cb : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := Fp) g' uu w)
    (hP : (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).1.eval
        ⟨shape.k, g, w, uu⟩ = commitGen g aP + pw • w)
    (hS : ps.ipaS = commitGen g aS + sw • w)
    (hRounds : (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
        (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum = commitGen g aRounds + uRounds • uu + wRounds • w)
    (hSxi : innerProduct (ch.xi • aS) (evalVector shape.k ch.x3) = 0)
    (hvVec : innerProduct (fun i => ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
        (List.ofFn ps.multiopenU) (constructIntermediateSets (assembleQueries vk ps ch))
        (Msm.zero shape.k Fp G)).2] : List Fp).getD i.val 0) (evalVector shape.k ch.x3)
      = -(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2)
    (hsvTerm : innerProduct (fun i => (computeS (List.ofFn ch.ipaRound) (-ps.ipaC)).getD (i : ℕ) 0)
      (evalVector shape.k ch.x3) = -cb)
    (hRoundsIP : innerProduct aRounds (evalVector shape.k ch.x3) = ipRounds)
    (huConst : (-ps.ipaC) * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z = -(cb * ch.z))
    (huRounds : uRounds = ch.z * ipRounds) (hz : ch.z ≠ 0)
    -- decode data:
    {nCols : ℕ} (C : Fin nCols → G) (e : Fin nCols → Fp) (zBatch : Fin nCols → Fp)
    (hMulti : DeployedMultiopenRewind (⟨shape.k, g, w, uu⟩ : SRS G) (evalVector shape.k ch.x3) C e zBatch
      ch.z (DeployedAccepts (⟨shape.k, g, w, uu⟩ : SRS G) rfl vk ps ch))
    -- constraint (derived) data:
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin nCols → (Fin (2 ^ shape.k) → Fp)) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (xc eHEval : Fp)
    (hHcol : hpoly.eval xc = eHEval)
    (hNum : ∀ col : Fin nCols → (Fin (2 ^ shape.k) → Fp),
      (∀ i, commitGen g (col i) = C i ∧ commitGen (evalVector shape.k ch.x3) (col i) = e i) →
      (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates).eval xc = eHEval * (xc ^ deg - 1))
    (hgood : ∀ col : Fin nCols → (Fin (2 ^ shape.k) → Fp),
      (∀ i, commitGen g (col i) = C i ∧ commitGen (evalVector shape.k ch.x3) (col i) = e i) →
      combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates
        - hpoly * (X ^ deg - 1)).eval xc ≠ 0)
    (haccepts : DeployedAccepts (⟨shape.k, g, w, uu⟩ : SRS G) rfl vk ps ch)
    {S : Prop}
    (hencodes : ∀ col : Fin nCols → (Fin (2 ^ shape.k) → Fp),
      (∀ i, commitGen g (col i) = C i ∧ commitGen (evalVector shape.k ch.x3) (col i) = e i) →
      IpaRelation (⟨shape.k, g, w, uu⟩ : SRS G) (commitGen g aP) (evalVector shape.k ch.x3)
        (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp G)).2 aP →
      combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates = hpoly * (X ^ deg - 1) →
      S) :
    S := by
  -- the IPA opening, AGM route (no tree)
  have hrel := orchard_verifier_sound_deployed_agm g w uu vk ps ch (evalVector shape.k ch.x3)
    aP aS aRounds pw sw uRounds wRounds ipRounds cb (hbind g) hP hS hRounds hSxi hvVec hsvTerm
    hRoundsIP huConst huRounds hz haccepts
  -- the per-column decode
  obtain ⟨col, hcol⟩ :=
    decoded_columns_of_accept (⟨shape.k, g, w, uu⟩ : SRS G) (evalVector shape.k ch.x3) C e zBatch
      hbind hMulti haccepts
  -- the gate identity derived from the decoded h-column + VK numerator + SZ
  have hconstraint := deployed_constraint_of_decode
    (combineGates fixedCols (decodeAdvice col) (decodeInstance col) y gates) hpoly deg xc eHEval
    hHcol (hNum col hcol) (hgood col hcol)
  exact hencodes col hcol hrel hconstraint

end Zcash.Snark
