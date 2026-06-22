import Zcash.Snark.IpaSoundness
import Zcash.Snark.Ipa

/-!
# The §1↔§2 weld: the deployed flattened IPA MSM unfolds into the recursive verifier

`eval_ipaFold` gives the *flattened* deployed verification equation; `ipa_soundV` proves soundness of the
*recursive* verifier. This module connects them — closing the structural correspondence the bridge used to
absorb (checklist B).

The key is the `compute_s` correspondence: the deployed `g`-scalars `computeS u init` halve at each round
exactly as `commitGen_append` splits a commitment, so `commitGen g (sFun u init)` folds recursively with the
generator step `loHalf g + uⱼ • hiHalf g`. That step is `Consistency.foldGens` at the **inverted** challenge
(`foldGens g (uⱼ⁻¹) = loHalf g + uⱼ • hiHalf g`), which reconciles the deployed `u`-convention with
`ipa_soundV`'s `u⁻¹`-convention.

* `computeS_cons` — `computeS (uⱼ :: rest) = computeS rest ++ (computeS rest).map (· * uⱼ)`.
* `computeS_length` — `|computeS u init| = 2 ^ |u|`.
* `sFun` — the deployed `g`-scalar vector as a `Fin (2 ^ k) → F` function (`computeS` indexed by `getD`).
-/

namespace Zcash.Snark

variable {F : Type*} [Field F]

/-- The round recursion of `computeS` (in the `foldr` direction): one challenge doubles the vector, the new
half scaled by `uⱼ`. From `computeS u init = u.reverse.foldl …`, via `reverse_cons` + `foldl_append`. -/
theorem computeS_cons (uⱼ : F) (rest : List F) (init : F) :
    computeS (uⱼ :: rest) init = computeS rest init ++ (computeS rest init).map (· * uⱼ) := by
  simp only [computeS, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `computeS u init` has `2 ^ |u|` entries (it doubles each round). -/
theorem computeS_length (u : List F) (init : F) : (computeS u init).length = 2 ^ u.length := by
  induction u generalizing init with
  | nil => simp [computeS]
  | cons a t ih => rw [computeS_cons, List.length_append, List.length_map, ih, List.length_cons]; ring

/-- The deployed `g`-scalar vector `computeS u init` as a `Fin (2 ^ |u|) → F` function, defined
*recursively* so that it `append`s its two halves — making `loHalf`/`hiHalf` definitional
(`loHalf_append`/`hiHalf_append`) and the commitment recursion clean. `sFun_getD` ties it back to the
deployed `getD`-indexed form used in `eval_ipaFold`. -/
def sFun : (u : List F) → F → Fin (2 ^ u.length) → F
  | [], init => fun _ => init
  | uⱼ :: rest, init => append (sFun rest init) (uⱼ • sFun rest init)

/-- `getD` commutes with a scalar-multiply map (default `0` maps to `0 * c = 0`). -/
theorem getD_map_mul (l : List F) (c : F) (j : ℕ) :
    (l.map (· * c)).getD j 0 = l.getD j 0 * c := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> simp

/-- `sFun` agrees with the deployed `getD`-indexed `computeS`. -/
theorem sFun_getD (u : List F) (init : F) (i : Fin (2 ^ u.length)) :
    sFun u init i = (computeS u init).getD i.val 0 := by
  induction u with
  | nil => simp [sFun, computeS]
  | cons uⱼ rest ih =>
    have hlen : (computeS rest init).length = 2 ^ rest.length := computeS_length rest init
    rw [computeS_cons, sFun]
    by_cases h : i.val < 2 ^ rest.length
    · rw [append, dif_pos h, ih, List.getD_append _ _ _ _ (by rw [hlen]; exact h)]
    · rw [append, dif_neg h, Pi.smul_apply, ih, smul_eq_mul,
        List.getD_append_right _ _ _ _ (by rw [hlen]; omega), getD_map_mul, hlen]
      ring

end Zcash.Snark
