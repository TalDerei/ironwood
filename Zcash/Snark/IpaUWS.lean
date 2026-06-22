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

end Zcash.Snark
