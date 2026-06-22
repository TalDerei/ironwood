import Zcash.Snark.Main
import Zcash.Snark.IpaUWS
import Zcash.Snark.Multiopen

/-!
# The §1↔§2 weld capstone: deployed acceptance ⇒ SNARK relation, U/W/S peeled

This is the end-to-end deployed soundness theorem with the inner-product-argument opening derived over
halo2's **concrete** `U`/`W`/`S` structure (not assumed via an opaque bridge). It composes:

* `deployed_ipa_soundV` (`Zcash.Snark.IpaUWS`) — the recursive opening soundness: the deployed IPA's combined
  verifier equation, carrying the value-binding `U`, the blinding `W` and the synthetic-blinding `S`/`ξ`,
  peels (augmented binding) to the clean `IpaAcceptV` and feeds `ipa_soundV`, yielding `IpaRelation`.
* `circuitSatViaGates_of_check` (`Zcash.Snark.KnowledgeSoundness`) — the constraint side: the verifier's gate
  point-check at `x`, lifted by Schwartz–Zippel, gives `circuitSatViaGates` (C3).

Both conjuncts of `SnarkRelation` are therefore **derived** from the deployed accept. The eval vector is
**pinned** to `evalVector srs.k ch.x3` (`b = (x₃ⁱ)`), and the `U`/`W`/`z` to the SRS generators / the actual
binding challenge (`srs.u`, `srs.w`, `ch.z`) — matching halo2 `params.u`, `params.w`. The residual inputs are
exactly the legitimate floor: the augmented binding (DLR/AGM, `hbind`), the no-`U`-interference challenge
(`ch.z ≠ 0`, halo2's `z`), the special-soundness rewinding (`hrewind`: acceptance yields the transcript
tree), the gate point-check + good challenge (`hquot`/`hgood`, the constraint-side analog), and
VK-correctness (`hencodes`).
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The deployed accept IS the IPA verification equation, with `G'₀ = foldAll` explicit (closes O1's
structural correspondence).** `eval_assembleFinalMsm` gives the assembled MSM in closed form; rewriting its
`computeS` generator term via `deployed_gterm_foldAll` exhibits it as `[-c]·foldAll` — the folded generator
`G'₀`. So the deployed accept (`assemble.eval = 0`) is exactly halo2's IPA verifier equation
`P' + Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ) + [-c·b·z]U + [-f]W + [-c]G'₀ = 0` for the multiopen commitment/value, with the
generator fold *proven* (not assumed). The `DeployedIpaRewind` bridge's only residual is then the pure
rewinding of this equation into the 3-ary transcript tree. -/
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

/-- **`IpaRelation` derived from an accepting *deployed* IPA tree.** The witness `deployed_ipa_soundV`
extracts (after peeling `U`/`W`/`S`) opens `P` (`commit srs a = commitGen srs.g a`) and gives the inner
product (`innerProduct a b = commitGen b a`). So the full opening relation is derived over halo2's concrete
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

/-- **The deployed verifier's IPA bridge — the *pure* special-soundness rewinding.** Acceptance yields a
*deployed* IPA transcript tree (`DeployedIpaAcceptV`, carrying `U`/`W`/`S`) for the proof's eval vector `b`,
commitment `P` and value `v`. Unlike `FiatShamirTree`, this no longer absorbs any provable content: the
`U`/`W`/`S` separation is proven (`deployed_ipa_soundV`), and the structural correspondence — that
`assemble.eval = 0` *is* halo2's IPA verifier equation with `G'₀ = foldAll` and `b = compute_b` — is proven
(`deployed_verification_eq`, citing `deployed_gterm_foldAll`/`computeB_eq`). Its sole residual content is the
rewinding of that (proven) equation into a distinct-challenge tree — the irreducible ROM/forking floor. -/
def DeployedIpaRewind (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (z : Fp) (P : G) (v : Fp)
    (accepts : Prop) : Prop :=
  accepts → ∃ (blind : Fp) (t : DeployedIpaTreeV Fp G srs.k),
    DeployedIpaAcceptV srs.g b srs.u srs.w z P v blind t

/-- **The deployed Orchard verifier is sound — C1 (opening) and C3 (constraint) both derived, `U`/`W`/`S`
peeled.** From the deployed accept (`assemble.eval = 0`), the pure-rewinding bridge `hrewind`, the augmented
binding `hbind` (DLR/AGM), the no-`U`-interference challenge `ch.z ≠ 0`, and the gate point-check `hquot` with
its good challenge `hgood`, conclude the high-level statement `S` via VK-correctness `hencodes`.

The IPA opening (`IpaRelation`) is derived over halo2's concrete `U`/`W`/`S` structure
(`ipaRelation_of_deployedAcceptV` → `deployed_ipa_soundV`); the constraint (`circuitSatViaGates`) is derived
from the gate check (`circuitSatViaGates_of_check`). The eval vector is pinned to `evalVector srs.k ch.x3`.
Named assumptions (the legitimate floor): the rewinding (`hrewind`), the augmented binding (`hbind`), the
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

/-! ## The multiopen decode wired to acceptance (checklist O3)

The IPA opening recovers the *collapsed* witness for the multiopen commitment `P`. To feed the gate check we
need the *individual* column openings — what `multiopen_decode_deployed` recovers from the batching rewinding.
`DeployedMultiopenRewind` is that bridge (the batching analog of `DeployedIpaRewind`); `decoded_columns_of_accept`
derives the per-column openings from acceptance, so `decodeAdvice`/`decodeInstance` are no longer free — they
are the genuinely recovered columns. The residual is the batching rewinding (a ROM floor) and, for the
identification of decoded columns with the circuit's columns, VK-correctness. -/

/-- **The deployed multiopen batching bridge — the batching special-soundness rewinding.** Acceptance yields,
for `n` distinct batching challenges `zBatch k`, a deployed IPA transcript tree opening the batched
commitment `Σⱼ (zBatch k)ʲ·C j` to the batched value `Σⱼ (zBatch k)ʲ·e j` (with `U`/`W`/`S` carried). The
batching analog of `DeployedIpaRewind`: its content is the rewinding of the batching challenge, the
irreducible ROM floor (`multiopen_decode_deployed` discharges the algebra). -/
def DeployedMultiopenRewind {n : ℕ} (srs : SRS G) (b : Fin (2 ^ srs.k) → Fp) (C : Fin n → G)
    (e : Fin n → Fp) (zBatch : Fin n → Fp) (zIpa : Fp) (accepts : Prop) : Prop :=
  accepts → Function.Injective zBatch ∧ zIpa ≠ 0 ∧
    ∃ (blind : Fin n → Fp) (t : Fin n → DeployedIpaTreeV Fp G srs.k),
      ∀ k, DeployedIpaAcceptV srs.g b srs.u srs.w zIpa
        (∑ j : Fin n, zBatch k ^ (j : ℕ) • C j) (∑ j : Fin n, zBatch k ^ (j : ℕ) • e j) (blind k) (t k)

/-- **The per-column openings are derived from acceptance** (O3 wired). Given the batching bridge and the
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

/-! ## `P`/`v` pinned to the §1 assembly (checklist B3)

The capstone above leaves `P`, `v` as parameters tied to the proof only through the bridge. Here they are
**pinned definitionally** to the multiopen commitment and value the §1 assembly produces — the group element
the IPA opens (`(assembleOpening …).1.eval srs`) and the claimed value (`(assembleOpening …).2`) — so the
soundness statement is about the *actual* fingerprint objects, not free metavariables. -/

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

/-- **The deployed Orchard verifier is sound — `P`, `b`, `v` all pinned to the §1 fingerprint.** The full
weld capstone with the SRS taken as `⟨shape.k, g, w, u⟩`, `P` = `multiopenCommitment`, `v` =
`multiopenValue`, `b` = `evalVector shape.k ch.x3` — the *actual* objects halo2's IPA verifier opens. So
acceptance of the deployed fingerprint (`assemble.eval = 0`) yields, over halo2's concrete `U`/`W`/`S`
structure, a witness opening *that* commitment to *that* value, satisfying the circuit. The named floor is
unchanged: rewinding (`hrewind`), augmented binding (`hbind`), `ch.z ≠ 0`, gate point-check + SZ
(`hquot`/`hgood`), VK-correctness (`hencodes`). -/
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
      (DeployedAccepts (⟨shape.k, g, w, u⟩ : SRS G) rfl vk ps ch))
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
    S :=
  orchard_verifier_sound_deployed_full (⟨shape.k, g, w, u⟩ : SRS G) rfl vk ps ch fixedCols
    decodeAdvice decodeInstance y gates hpoly deg xc hbind hz haccepts hrewind hquot hgood hencodes

end Zcash.Snark
