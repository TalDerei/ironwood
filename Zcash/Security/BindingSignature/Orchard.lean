import Zcash.Security.BindingSignature.Balance

/-!
# Orchard no-overflow bound (spec §4.14)

The Orchard action count is bounded *directly* by a dedicated consensus rule `n ≤ 2^16 − 1`,
independent of the transaction size (the spec notes this is technically redundant given the
2 MB limit, but it stands on its own). Each action commits to the signed *net* value
`v = v_spend − v_output`, range-proven by the Action statement to lie in
`SignedValueDifferenceType = [−2^64+1, 2^64−1]`, i.e. `|v| ≤ 2^64 − 1`.

This module instantiates the generic `natAbs_lt_of_abs_le` from `Balance` at those concrete bounds,
discharging the `hbound` hypothesis of `bundle_integer_balances` for Orchard.
-/

namespace Zcash.Security.BindingSignature

/-- The Pallas scalar field order `r_ℙ` — the order of the Pallas group, which is the scalar field of
the Orchard value commitment (spec § Pallas and Vesta). -/
def pallasScalarOrder : ℕ := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- The Orchard `vSum` magnitude bound = the spec's `ValueCommitTypeOrchard` subrange endpoint
`(2^16 − 1)·(2^64 − 1) + 2^63`, from `|v| ≤ 2^64 − 1` per action, the consensus rule `n ≤ 2^16 − 1`,
and the signed-64-bit `vBalance`. -/
def orchardVSumBound : ℤ := vSumBound (2^16 - 1)

/-- The bound equals the spec's quoted endpoint. -/
example : orchardVSumBound = 1208916596242592319864833 := by norm_num [orchardVSumBound, vSumBound]

/-- **Orchard no-overflow bound.** With `|v| ≤ 2^64 − 1` per action, `n ≤ 2^16 − 1` actions, and
`|vBalance| ≤ 2^63`, the net sum `vSum = ∑ v − vBalance` has `vSum.natAbs < r` once
`orchardVSumBound < r` — directly from the shared `natAbs_lt_of_vSumBound`. This is the `hbound` of
`bundle_integer_balances` for Orchard. -/
theorem orchard_natAbs_lt {r : ℕ} (vs : List ℤ) (vBalance : ℤ)
    (hv : ∀ v ∈ vs, |v| ≤ 2^64 - 1)
    (hn : vs.length ≤ 2^16 - 1)
    (hvb : |vBalance| ≤ 2^63)
    (hr : orchardVSumBound < (r : ℤ)) :
    (vs.sum - vBalance).natAbs < r :=
  natAbs_lt_of_vSumBound vs vBalance (2^16 - 1) hv hn hvb hr

/-- The bound fits the Pallas scalar field: the `hr` that instantiates `orchard_natAbs_lt` at
`r = pallasScalarOrder` (and witnesses that the lemma is not vacuous). -/
theorem orchardVSumBound_lt_pallasScalarOrder : orchardVSumBound < (pallasScalarOrder : ℤ) := by
  norm_num [orchardVSumBound, vSumBound, pallasScalarOrder]

end Zcash.Security.BindingSignature
