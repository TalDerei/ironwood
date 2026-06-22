import Zcash.Snark.Main
import Zcash.Snark.IpaUWS

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

/-- **The deployed verifier's IPA bridge — now the *pure* special-soundness rewinding.** Acceptance yields a
*deployed* IPA transcript tree (`DeployedIpaAcceptV`, carrying `U`/`W`/`S`) for the proof's eval vector `b`,
commitment `P` and value `v`. Unlike `FiatShamirTree`, this no longer absorbs the `U`/`W`/`S` separation or
the generator-fold correspondence (both now *proven* — `deployed_ipa_soundV`, `foldAll`/`computeB`): its sole
content is the rewinding (one accepting transcript → a distinct-challenge tree), the irreducible ROM floor. -/
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

end Zcash.Snark
