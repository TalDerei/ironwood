import Mathlib
import Zcash.Snark.Main
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
exactly as the field modulus is — a `Fact`, kept axiom-free. ⚠️ It inherits the **conditional** status of
`orchard_verifier_sound_conditional` (assumed extraction + constraint identity; `accepts` not tied to the
fingerprint); see that theorem's docstring and `notes/fv-review-checklist.md`. -/
theorem orchard_verifier_sound_vesta_conditional [Fact VestaOrder]
    (srs : SRS VestaG) (hbind : CommitmentBinding (F := Fp) srs)
    {P : VestaG} {b : Fin (2 ^ srs.k) → Fp} {v : Fp}
    {accepts : Prop} (haccepts : accepts) (hextract : ExtractableFromAcceptance srs P b v accepts)
    {numerator h : Polynomial Fp} {n : ℕ} (hcon : numerator = h * (Polynomial.X ^ n - 1))
    {S : Prop} (hencodes : ∀ a, SnarkRelation srs P b v numerator h n a → S) :
    S :=
  orchard_verifier_sound_conditional srs hbind haccepts hextract hcon hencodes

end Zcash.Snark
