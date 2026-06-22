import Mathlib
import Zcash.Snark.Main
import Zcash.Snark.Weld
import CompElliptic.Curves.Pasta

/-!
# The verifier group instantiated at the concrete Vesta curve

`Zcash.Snark.orchard_verifier_sound` is proven for an abstract `Fp`-module `G`. Here we pin `G` to the
*actual* Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`), whose group law CompElliptic/mathlib have
already proven (associativity transported from `WeierstrassCurve.Affine.Point`). The only structure the
`Fp`-action needs that the curve does not already carry is the Vesta **group order**: every point is
`p`-torsion (`p = scalarFieldOrder`, the published Vesta order — equivalently the order divides `p`, and
being a nontrivial prime it equals `p`).

We treat this **exactly like the field modulus** — as a `Fact`, the same idiom as
`Fact (Nat.Prime scalarFieldOrder)`. The one difference is provenance: CompElliptic *discharges* the field
`Fact` with a Pratt primality certificate (cheap to check), whereas the curve order has no analogous
certificate in the library — pinning it is point-counting (Schoof / Hasse), not formalized. So the
curve-order `Fact` stays an *assumption* (a hypothesis of the Vesta theorem) rather than a proven global
instance, which is what keeps the development axiom-free. Given that `Fact`, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the end-to-end theorem applies verbatim.
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass

/-- The verifier group `E_q`, concretely: the points of the Vesta curve `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- **The Vesta group order, as a proposition** (cf. `Nat.Prime scalarFieldOrder` for the field): every
Vesta point is `p`-torsion, i.e. the group order divides `p = scalarFieldOrder`. Carried as a `Fact`,
exactly like the field modulus — but, lacking a point-counting certificate, left as an assumption. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module: `AddCommGroup.zmodModule`
on the `p`-torsion. A *conditional* instance — it fires only when the order `Fact` is in scope, so it adds
no axiom (the `Fact` is supplied as a hypothesis, never globally). -/
noncomputable instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **The conditional soundness composition, over the concrete Vesta curve.** This is
`orchard_verifier_sound_conditional` with the abstract `Fp`-module specialised to `SWPoint Vesta.curve`:
the *abstract-curve* assumption is replaced by `Fact VestaOrder` (the published Vesta group order), treated
exactly as the field modulus is — a `Fact`, kept axiom-free. It inherits the **conditional** status of
`orchard_verifier_sound_conditional` (assumed extraction + constraint identity; `accepts` not tied to the
fingerprint); see that theorem's docstring and `notes/fv-review-checklist.md`. -/
theorem orchard_verifier_sound_vesta_conditional [Fact VestaOrder]
    (srs : SRS VestaG) (hbind : CommitmentBinding (F := Fp) srs)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance srs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional srs hbind haccepts hextract hencodes

/-- The deployed soundness theorem over the concrete Vesta curve — `orchard_verifier_sound_deployed_final`
specialised to `SWPoint Vesta.curve`, so the statement is about the actual fingerprint `assemble.eval = 0`.
It carries the same explicit assumptions: `Fact VestaOrder` (the curve order), the
`ExtractableFromDeployedAccept` bridge (rewinding + the IPA opening + circuit-satisfaction — the latter two
still assumed, not derived; see that definition), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_deployed [Fact VestaOrder] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (srs : SRS VestaG) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hbridge : ExtractableFromDeployedAccept srs P b v circuitSat (DeployedAccepts srs hk vk ps ch))
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_deployed_final srs hk vk ps ch haccepts hbridge hencodes

/-- **The deployed Orchard verifier is sound over Vesta, with the IPA opening derived (C1 closed).**
`orchard_verifier_sound_deployed_C1` specialised to `SWPoint Vesta.curve`: the bridge `hFS` supplies only
the special-soundness transcript tree (the minimal Fiat–Shamir assumption), and `IpaRelation` is *derived*
from it (`ipa_soundV`), not assumed. The remaining named assumptions are the rewinding (`hFS`), the circuit
side (`hcirc`, C3), the Vesta curve order (`Fact VestaOrder`), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_C1 [Fact VestaOrder] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (srs : SRS VestaG) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hFS : FiatShamirTree srs b P v (DeployedAccepts srs hk vk ps ch))
    (hcirc : ∀ a, IpaRelation srs P b v a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_deployed_C1 srs hk vk ps ch haccepts hFS hcirc hencodes

open Polynomial in
/-- **The deployed Orchard verifier is sound over Vesta — C1 and C3.** `orchard_verifier_sound_deployed_C3`
specialised to `SWPoint Vesta.curve`: both conjuncts of `SnarkRelation` are derived — `IpaRelation` via
`ipa_soundV` and `circuitSat` (concrete `circuitSatViaGates`) from the verifier's gate point-check `hquot`
lifted by Schwartz–Zippel (`hgood`). Named assumptions: the rewinding (`hFS`), the gate check (`hquot`), the
SZ good challenge (`hgood`), the Vesta curve order, and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_C3 [Fact VestaOrder] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (srs : SRS VestaG) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp}
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
    S :=
  orchard_verifier_sound_deployed_C3 srs hk vk ps ch fixedCols decodeAdvice decodeInstance y gates
    hpoly deg x haccepts hFS hquot hgood hencodes

open Polynomial in
/-- **The deployed Orchard verifier is sound over Vesta — full weld, `U`/`W`/`S` peeled.**
`orchard_verifier_sound_deployed_full` specialised to `SWPoint Vesta.curve`: the IPA opening is derived over
halo2's concrete `U`/`W`/`S` structure (`deployed_ipa_soundV` — the value-binding `U`, blinding `W` and
synthetic-blinding `S`/`ξ` peeled via the augmented binding), the constraint via the gate point-check; the
eval vector is pinned to `evalVector srs.k ch.x3`. Named assumptions (the floor): the pure rewinding
(`hrewind`), the augmented binding (`hbind`, DLR/AGM on `srs.u`,`srs.w`), the binding challenge
(`ch.z ≠ 0`), the gate point-check + SZ good challenge (`hquot`/`hgood`), the Vesta curve order
(`Fact VestaOrder`), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_full [Fact VestaOrder] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (srs : SRS VestaG) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp) {P : VestaG} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ srs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hbind : ∀ {m : ℕ} (g' : Fin m → VestaG), AugmentedBinding (F := Fp) g' srs.u srs.w)
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
    S :=
  orchard_verifier_sound_deployed_full srs hk vk ps ch fixedCols decodeAdvice decodeInstance y gates
    hpoly deg x hbind hz haccepts hrewind hquot hgood hencodes

end Zcash.Snark
