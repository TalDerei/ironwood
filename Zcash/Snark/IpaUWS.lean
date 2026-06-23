import Zcash.Snark.IpaSoundness
import Zcash.Snark.IpaDeployed

/-!
# The deployed IPA's `U`/`W`/`S` structure peels to the clean recursive IPA

`Zcash.Snark.ipa_soundV` proves knowledge soundness of the *clean* inner-product argument (`IpaAcceptV`:
fold `g`, `b`, `P`, `v`; leaf `P = [c]g₀ ∧ v = [c]b₀`). halo2's deployed IPA
(`poly/commitment/verifier.rs`) is the same recursion *plus* three blinding/binding generators, verified in
ONE group equation:

* `U` — the inner-product binding. The value `v` is checked through `[-c·b·z]U` (`z` a challenge ensuring the
  prover cannot interfere with `U`), with `b = compute_b = ⟨sFun u 1, evalVector x⟩` (`computeB_eq`).
* `W` — the commitment blinding. The prover's synthetic blinding factor `f` rides on `[-f]W`.
* `S`/`ξ` — the synthetic blinding of the *opening* (zero-knowledge): `P' = P − [v]g₀ + [ξ]S`, with `S` a
  commitment to a random polynomial vanishing at `x` (`create_proof`).

This module models that apparatus and **proves it peels off**: under the **augmented binding** (the SRS
generators together with `U`, `W` are linearly independent — the discrete-log assumption extended to the two
extra fixed generators), a deployed group equation
`⟨a, g⟩ + α•U + β•W = ⟨a', g⟩ + α'•U + β'•W` splits coordinate-wise into `a = a'`, `α = α'`, `β = β'`. So the
deployed verifier's combined check separates into the clean `IpaAcceptV` checks (the `g`-side commitment and
the `U`-side value) plus a discarded `W`-side blinding identity — closing the `U`/`W`/`S` structure down to
`ipa_soundV`. The residual floor is the standard one: the special-soundness rewinding (the transcript tree)
and the discrete-log/AGM binding.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **Augmented commitment binding** — the SRS generators `g` together with the IPA generator `U` and the
blinding generator `W` are jointly `F`-linearly independent: a combination `⟨a, g⟩ + α•U + β•W` is `0` only
trivially. This is the discrete-log-relation hardness assumption (`CommitmentBinding`) extended to the two
extra fixed generators `U`, `W` that the deployed IPA verifier uses — exactly the generators halo2 treats as
independent (`params.u`, `params.w` are sampled independently of `params.g`). -/
def AugmentedBinding {n : ℕ} (g : Fin n → G) (U W : G) : Prop :=
  ∀ (a : Fin n → F) (α β : F), commitGen g a + α • U + β • W = 0 → a = 0 ∧ α = 0 ∧ β = 0

/-- **The augmented binding separates a deployed group equation coordinate-wise.** Two `(g, U, W)`-combinations
that are equal as group elements have equal `g`-coordinates, `U`-coordinate, and `W`-coordinate. This is the
peeling lemma: it lets the deployed verifier's single combined equation be read off as the independent
`g`-side, `U`-side, and `W`-side identities. -/
theorem AugmentedBinding.separate {n : ℕ} {g : Fin n → G} {U W : G} (h : AugmentedBinding (F := F) g U W)
    {a a' : Fin n → F} {α α' β β' : F}
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    a = a' ∧ α = α' ∧ β = β' := by
  have hz : commitGen g (a - a') + (α - α') • U + (β - β') • W = 0 := by
    have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
        = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
      rw [commitGen_sub, sub_smul, sub_smul]; abel
    rw [hrw, e, sub_self]
  obtain ⟨ha, hα, hβ⟩ := h _ _ _ hz
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hα, sub_eq_zero.mp hβ⟩

/-- **The deployed flat verification equation splits into its `g`/`U`/`W` relations — derived from
`assemble.eval = 0`, no posited tree (the opening, AGM route).** With the prover's group elements given via their AGM
representations over `(g, U, W)` — the multiopen commitment `commitGen g aP + pw•W`, the blinding poly
`commitGen g aSxi + swxi•W` (the `ξ`-scaled `S`), the round total `commitGen g aRounds + uRounds•U + wRounds•W`,
the `[-v]g₀` term `commitGen g vVec`, the `[-c·b·z]U` and `[-f]W` constants, and the folded generator
`commitGen g svTerm` (`= [-c]·G'₀`, via `foldAll = commitGen g (sFun u 1)`) — the augmented binding reads
`assemble.eval = 0` off as three independent identities: the `g`-relation (the opening constraint), the
`U`-relation (the value/inner-product binding), and the `W`-relation (blinding). This is exactly the
MSM↔structured-checks connection: it is now a *proof from* `assemble.eval = 0`,
not a posited bridge. Floor: the AGM representations + the augmented binding. -/
theorem deployed_flat_split {k : ℕ} {g : Fin (2 ^ k) → G} {U W : G}
    (hbind : AugmentedBinding (F := F) g U W)
    (aP aSxi aRounds vVec svTerm : Fin (2 ^ k) → F)
    (pw swxi wRounds uRounds uConst wConst : F)
    (hflat : commitGen g aP + pw • W
        + (commitGen g aSxi + swxi • W)
        + (commitGen g aRounds + uRounds • U + wRounds • W)
        + commitGen g vVec
        + uConst • U + wConst • W
        + commitGen g svTerm = 0) :
    aP + aSxi + aRounds + vVec + svTerm = 0
      ∧ uRounds + uConst = 0
      ∧ pw + swxi + wRounds + wConst = 0 := by
  have key : commitGen g (aP + aSxi + aRounds + vVec + svTerm)
      + (uRounds + uConst) • U + (pw + swxi + wRounds + wConst) • W = 0 := by
    have expand : commitGen g (aP + aSxi + aRounds + vVec + svTerm)
        + (uRounds + uConst) • U + (pw + swxi + wRounds + wConst) • W
        = commitGen g aP + pw • W + (commitGen g aSxi + swxi • W)
          + (commitGen g aRounds + uRounds • U + wRounds • W) + commitGen g vVec
          + uConst • U + wConst • W + commitGen g svTerm := by
      simp only [commitGen_add_left, add_smul]; abel
    rw [expand]; exact hflat
  exact hbind _ _ _ key

/-- **The value `⟨aP, b⟩ = v` follows from the split relations (the opening's value extraction).** From the `g`-relation
(`deployed_flat_split`'s first conjunct), taken in inner product with `b`, plus the `U`-relation and the
honest/SZ structure: the blinding poly vanishes at the point (`⟨aSxi, b⟩ = 0` — `S` has a root at `x`, the
`ξ`-challenge's job), the round `U`-coefficient is `z·⟨aRounds, b⟩` (the `z`-challenge ensures the prover
cannot interfere with `U`), and the constants are `⟨vVec,b⟩ = -v` (the `[-v]g₀` term, `b₀ = 1`) and
`⟨svTerm,b⟩ = -cb` (`cb = c·compute_b`, the folded generator's value). The `U`-relation forces
`⟨aRounds,b⟩ = cb` (`z ≠ 0`), and the `g`-relation then collapses to `⟨aP,b⟩ = v`. So the extracted witness
opens to the claimed value. Floor: the SZ challenge exclusions (`z`, `ξ`) named as `huRounds`/`hSxi`. -/
theorem deployed_open_value {k : ℕ} (b aP aSxi aRounds vVec svTerm : Fin (2 ^ k) → F)
    (uRounds uConst v ipRounds cb z : F)
    (hg : aP + aSxi + aRounds + vVec + svTerm = 0)
    (hu : uRounds + uConst = 0)
    (hSxi : innerProduct aSxi b = 0) (hvVec : innerProduct vVec b = -v)
    (hsvTerm : innerProduct svTerm b = -cb) (hRounds : innerProduct aRounds b = ipRounds)
    (huConst : uConst = -(cb * z)) (huRounds : uRounds = z * ipRounds) (hz : z ≠ 0) :
    innerProduct aP b = v := by
  have hir : ipRounds = cb := by
    have hzz : z * (ipRounds - cb) = 0 := by rw [mul_sub]; linear_combination hu - huRounds - huConst
    rcases mul_eq_zero.mp hzz with h | h
    · exact absurd h hz
    · exact sub_eq_zero.mp h
  have hgi : innerProduct aP b + innerProduct aSxi b + innerProduct aRounds b
      + innerProduct vVec b + innerProduct svTerm b = 0 := by
    have h0 : innerProduct (aP + aSxi + aRounds + vVec + svTerm) b = 0 := by
      rw [hg]; simp [innerProduct]
    rwa [innerProduct_add_left, innerProduct_add_left, innerProduct_add_left,
      innerProduct_add_left] at h0
  rw [hSxi, hvVec, hsvTerm, hRounds, hir] at hgi
  linear_combination hgi

/-- **The deployed leaf check peels to the clean `IpaAcceptV` leaf.** halo2's fully-folded verifier equation
is `P + [z·v]U + [blind]W = [c](g₀ + [z·b₀]U) + [f]W` (the `g`-commitment, the value bound to `U` by the
challenge `z`, the blinding on `W`). With `P = ⟨aP, g⟩` (the commitment's `g`-representation) the augmented
binding separates it into the two clean leaf checks `⟨aP, g⟩ = [c]g₀` and `v = [c]b₀`, plus the discarded
blinding identity `blind = f`. The `z ≠ 0` cancellation is exactly halo2's "challenge that ensures the prover
did not interfere with the `U` term". -/
theorem deployed_leaf_peel {n : ℕ} {g : Fin n → G} {b : Fin n → F} {U W : G} {z : F}
    {aP : Fin n → F} {v blind c f : F}
    (hbind : AugmentedBinding (F := F) g U W) (hz : z ≠ 0)
    (e : commitGen g aP + (z * v) • U + blind • W
       = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W) :
    commitGen g aP = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c) := by
  obtain ⟨ha, hα, _⟩ := hbind.separate e
  exact ⟨congrArg (commitGen g) ha, mul_left_cancel₀ hz hα⟩

/-! ## The deployed recursion peels to the clean recursive IPA -/

/-- A **deployed** 3-ary IPA transcript tree: like `IpaTreeV` but each node also carries the blinding
cross-terms `Lw`, `Rw` (the `W`-side of the prover's `L`/`R`) and the leaf carries the synthetic blinding
scalar `f`. The `U`/`W` generators and the binding challenge `z` are global (carried in `DeployedIpaAcceptV`),
matching halo2 (`params.u`, `params.w`, the challenge `z` are fixed across the rounds). -/
inductive DeployedIpaTreeV (F G : Type*) : ℕ → Type _ where
  | leaf : F → F → DeployedIpaTreeV F G 0
  | node {d : ℕ} : G → G → F → F → F → F → F → F → F →
      DeployedIpaTreeV F G d → DeployedIpaTreeV F G d → DeployedIpaTreeV F G d → DeployedIpaTreeV F G (d + 1)

/-- Forget the deployed blinding decorations (`Lw`, `Rw`, `f`), recovering the clean `IpaTreeV` that
`ipa_soundV` consumes. -/
def projTree : {d : ℕ} → DeployedIpaTreeV F G d → IpaTreeV F G d
  | _, .leaf c _ => .leaf c
  | _, .node L R Lv Rv _ _ u₁ u₂ u₃ t₁ t₂ t₃ =>
      .node L R Lv Rv u₁ u₂ u₃ (projTree t₁) (projTree t₂) (projTree t₃)

/-- **Acceptance for the deployed IPA, carrying the `U`/`W`/`S` apparatus.** The recursion folds the
generators `g`, the eval vector `b`, the commitment `P` (by `L`,`R`), the value `v` (by `Lv`,`Rv`) and the
blinding `blind` (by `Lw`,`Rw`) — the `g`/`b`/`P`/`v` folds are exactly `IpaAcceptV`'s; `U`, `W`, `z` are
fixed. The **leaf** is halo2's single combined verifier equation
`P + [z·v]U + [blind]W = [c]g₀ + [z·c·b₀]U + [f]W`, with `P` given in its `g`-representation `⟨aP, g⟩` (the
AGM: the folded commitment is a known combination of the SRS generators). -/
def DeployedIpaAcceptV : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → G → F → G → F → F →
    DeployedIpaTreeV F G d → Prop
  | 0, g, b, U, W, z, P, v, blind, .leaf c f =>
      ∃ aP : Fin (2 ^ 0) → F, P = commitGen g aP ∧
        commitGen g aP + (z * v) • U + blind • W
          = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, g, b, U, W, z, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        DeployedIpaAcceptV (foldGens g u₁) (foldGens b u₁) U W z
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) (blind + u₁⁻¹ • Lw + u₁ • Rw) t₁ ∧
        DeployedIpaAcceptV (foldGens g u₂) (foldGens b u₂) U W z
          (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) (blind + u₂⁻¹ • Lw + u₂ • Rw) t₂ ∧
        DeployedIpaAcceptV (foldGens g u₃) (foldGens b u₃) U W z
          (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) (blind + u₃⁻¹ • Lw + u₃ • Rw) t₃

/-- **The deployed recursion peels to the clean `IpaAcceptV`.** Under the augmented binding (at every
folded-generator family — `U`,`W` are independent of all generators the recursion produces) and `z ≠ 0`, the
deployed combined verifier accepts only if the clean recursive verifier does: nodes carry over verbatim (the
`g`/`b`/`P`/`v` folds coincide; the blinding fold is discarded), and each leaf's combined equation peels via
`deployed_leaf_peel` into the clean leaf checks `P = [c]g₀ ∧ v = [c]b₀`. This is the `U`/`W`/`S` structure
closing onto `ipa_soundV`. -/
theorem deployed_to_acceptV {U W : G} {z : F}
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := F) g' U W) (hz : z ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → DeployedIpaAcceptV g b U W z P v blind t →
      IpaAcceptV g b P v (projTree t)
  | 0, g, b, P, v, blind, .leaf c f, h => by
      obtain ⟨aP, hP, he⟩ := h
      obtain ⟨h1, h2⟩ := deployed_leaf_peel (hbind g) hz he
      exact ⟨hP.trans h1, h2⟩
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      exact ⟨h12, h13, h23, hu₁, hu₂, hu₃,
        deployed_to_acceptV hbind hz _ _ _ _ _ t₁ ha₁,
        deployed_to_acceptV hbind hz _ _ _ _ _ t₂ ha₂,
        deployed_to_acceptV hbind hz _ _ _ _ _ t₃ ha₃⟩

/-- **Recursive opening soundness over halo2's concrete `U`/`W`/`S` structure.** An accepting deployed IPA
transcript tree yields a witness opening the commitment to the claimed value: `∃ a, ⟨a,g⟩ = P ∧ ⟨a,b⟩ = v`.
Composes `deployed_to_acceptV` (the `U`/`W`/`S` peeling) with the proven clean-IPA soundness `ipa_soundV`. The
only inputs are the legitimate floor: the augmented binding (DLR/AGM, `hbind`) and the transcript tree itself
(the special-soundness rewinding). -/
theorem deployed_ipa_soundV {U W : G} {z : F}
    (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := F) g' U W) (hz : z ≠ 0)
    {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : DeployedIpaAcceptV g b U W z P v blind t) :
    ∃ a : Fin (2 ^ d) → F, commitGen g a = P ∧ commitGen b a = v :=
  ipa_soundV g b P v (projTree t) (deployed_to_acceptV hbind hz g b P v blind t h)

end Zcash.Snark
