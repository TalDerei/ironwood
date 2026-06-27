import Mathlib
import Zcash.Snark.Main
import CompElliptic.Curves.Pasta

/-!
# Vesta instantiation: the verifier group at the deployed curve

The soundness theorems of `Zcash.Snark.Main` are proven for an abstract
`Fp`-module `G`. Here `G` is pinned to the actual Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`),
whose group law CompElliptic/mathlib have already proven (associativity transported from
`WeierstrassCurve.Affine.Point`). The deployed Orchard verifier runs over Vesta, so these theorems are
the concrete-curve forms of the abstract capstones.

## The setting

The only structure the `Fp`-action needs that the curve does not already carry is the Vesta group
order: every point is `p`-torsion (`p = scalarFieldOrder`, the published Vesta order — the order
divides `p`, and being a nontrivial prime it equals `p`). Given that, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the end-to-end theorems apply verbatim.

## Assumptions

* **Vesta group order** (`Fact VestaOrder`) — every point is `p`-torsion. Treated as the field
  modulus is, via a `Fact` (the idiom of `Fact (Nat.Prime scalarFieldOrder)`). The difference is
  provenance: CompElliptic discharges the field `Fact` with a Pratt primality certificate (cheap to
  check), whereas the curve order has no analogous certificate in the library. Pinning it does not need
  point-counting, though: for a non-identity point `P`, a single check `scalarFieldOrder • P = 0` shows
  `scalarFieldOrder` divides the group order, and as it is prime with `2·scalarFieldOrder` above the
  upper Hasse bound, the order must equal it. That is not yet formalized, so it stays a hypothesis of
  each Vesta theorem rather than a proven global instance, which keeps the development axiom-free.
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass

/-- The verifier group `E_q`, concretely: the points of the Vesta curve `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group order as a proposition (cf. `Nat.Prime scalarFieldOrder` for the field): every
Vesta point is `p`-torsion, i.e. the group order divides `p = scalarFieldOrder`. Carried as a `Fact`,
like the field modulus — but, lacking a point-counting certificate, left as an assumption. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module: `AddCommGroup.zmodModule`
on the `p`-torsion. A conditional instance — it fires only when the order `Fact` is in scope, so it adds
no axiom (the `Fact` is supplied as a hypothesis, never globally). -/
noncomputable instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- The conditional soundness composition over the concrete Vesta curve:
`orchard_verifier_sound_conditional` with the abstract `Fp`-module specialised to `SWPoint Vesta.curve`,
the abstract-curve assumption replaced by `Fact VestaOrder` (the published Vesta group order). It
inherits the conditional status of `orchard_verifier_sound_conditional` (assumed extraction + constraint
identity; `accepts` not tied to the fingerprint); see that docstring. The deployed Vesta capstones are
`orchard_verifier_sound_vesta_opening`/`_constraint` below. -/
theorem orchard_verifier_sound_vesta_conditional [Fact VestaOrder]
    (srs : SRS VestaG) (hbind : CommitmentBinding (F := Fp) srs)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance srs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional srs hbind haccepts hextract hencodes

/-- The deployed Orchard verifier is sound over Vesta, with the IPA opening derived.
`orchard_verifier_sound_deployed_opening` specialised to `SWPoint Vesta.curve`: the bridge `hFS` supplies
only the special-soundness transcript tree (the minimal Fiat–Shamir assumption), and `IpaRelation` is
derived from it (`ipa_soundV`), not assumed. Named assumptions: the rewinding (`hFS`), the circuit side
(`hcirc`), the Vesta curve order (`Fact VestaOrder`), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_opening [Fact VestaOrder] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (srs : SRS VestaG) (hk : shape.k = srs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ srs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts srs hk vk ps ch)
    (hFS : FiatShamirTree srs b P v (DeployedAccepts srs hk vk ps ch))
    (hcirc : ∀ a, IpaRelation srs P b v a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_deployed_opening srs hk vk ps ch haccepts hFS hcirc hencodes

open Polynomial in
/-- The deployed Orchard verifier is sound over Vesta, opening and constraint both derived.
`orchard_verifier_sound_deployed_constraint` specialised to `SWPoint Vesta.curve`: both conjuncts of
`SnarkRelation` are derived — `IpaRelation` via `ipa_soundV`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel (`hgood`).
Named assumptions: the rewinding (`hFS`), the gate check (`hquot`), the SZ good challenge (`hgood`), the
Vesta curve order, and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_constraint [Fact VestaOrder] [DecidableEq VestaG] [Inhabited VestaG]
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
  orchard_verifier_sound_deployed_constraint srs hk vk ps ch fixedCols decodeAdvice decodeInstance y gates
    hpoly deg x haccepts hFS hquot hgood hencodes

end Zcash.Snark
