import Zcash.Snark.IpaUWS

/-!
# The multiopen decode over the deployed IPA (closing O3)

`Zcash.Snark.multiopen_decode_of_trees` proves the multiopen decode for the *clean* IPA. Here we wire it to
the *deployed* IPA (with `U`/`W`/`S`): from deployed transcript trees opening the batched commitment at `n`
distinct batching challenges, the per-column openings are recovered — composing `deployed_ipa_soundV` (the
`U`/`W`/`S`-peeled IPA opening at each batching challenge) with `batch_open_soundV` (the Vandermonde decode).

This is the multiopen analog of the IPA layer: the deployed verifier batches the per-column commitments by
powers of a challenge (the halo2 `x₁`/`x₄` folds) and opens the single batched commitment; rewinding the
batching challenge and solving the Vandermonde system recovers each column. The residual floor is the
batching rewinding (the trees) and the augmented binding — the same standard assumptions as the IPA layer.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **The multiopen decode, derived over the deployed IPA.** Given, for each of `n` distinct batching
challenges `zBatch k`, a *deployed* IPA transcript tree opening the batched commitment `Σⱼ (zBatch k)ʲ·C j`
to the batched value `Σⱼ (zBatch k)ʲ·e j`, every individual column `i` opens to its commitment `C i` and its
claimed evaluation `e i`. Composes `deployed_ipa_soundV` (the per-batching-challenge opening, `U`/`W`/`S`
peeled) with `batch_open_soundV` (the per-column Vandermonde decode), all binding-free beyond the augmented
binding `deployed_ipa_soundV` consumes. -/
theorem multiopen_decode_deployed {n : ℕ} (srs : SRS G) (b : Fin (2 ^ srs.k) → F)
    (C : Fin n → G) (e : Fin n → F) (zBatch : Fin n → F) (hzBatch : Function.Injective zBatch)
    {zIpa : F} (hbind : ∀ {m : ℕ} (g' : Fin m → G), AugmentedBinding (F := F) g' srs.u srs.w)
    (hzIpa : zIpa ≠ 0) (blind : Fin n → F) (t : Fin n → DeployedIpaTreeV F G srs.k)
    (ht : ∀ k, DeployedIpaAcceptV srs.g b srs.u srs.w zIpa
      (∑ j : Fin n, zBatch k ^ (j : ℕ) • C j) (∑ j : Fin n, zBatch k ^ (j : ℕ) • e j) (blind k) (t k)) :
    ∃ col : Fin n → (Fin (2 ^ srs.k) → F),
      ∀ i, commitGen srs.g (col i) = C i ∧ commitGen b (col i) = e i := by
  choose a hac hae using fun k => deployed_ipa_soundV hbind hzIpa srs.g b
    (∑ j : Fin n, zBatch k ^ (j : ℕ) • C j) (∑ j : Fin n, zBatch k ^ (j : ℕ) • e j) (blind k) (t k) (ht k)
  exact batch_open_soundV srs.g b C e zBatch hzBatch a hac hae

end Zcash.Snark
