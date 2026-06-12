import Zcash.Security.BindingSignature.Balance

/-!
# Sapling no-overflow bound (spec §4.13)

Sapling note values are *unsigned* 64-bit (`ValueType = {0..2^64−1}`), but the no-overflow argument
only needs `|v| ≤ 2^64 − 1` — the same per-element magnitude bound Orchard's signed net values
satisfy — so we bound `|vSum|` uniformly rather than reproducing the spec's tighter asymmetric range.
Any bound far below the Jubjub scalar field order suffices, and this one is.

The action counts are bounded *indirectly* by the 2 MB transaction-size limit (a transaction cannot
exceed the maximum block size of `2000000` bytes) against the minimum size of each description. We
reproduce those minimum sizes by summing the encoded field sizes (spec § Spend Description Encoding
and Consensus / § Output Description Encoding and Consensus) so a reviewer can check them, and — as
the spec does — we treat both v4 and v5 transactions: a v4 Spend carries a per-spend `anchor`
(32 bytes) that a v5 Spend omits (it is shared once per transaction), so the minimum Spend size is
384 bytes (v4) or 352 (v5).

Each byte/count magnitude is a named constant tied to the spec's quoted value by a single `example`.
This module discharges the `hbound` of `bundle_integer_balances` for Sapling, via `sapling_natAbs_lt`
(general) and the `_v4` / `_v5` corollaries.
-/

namespace Zcash.Security.BindingSignature

/-- The Jubjub scalar field order `ℓ` — the prime-order subgroup order, which is the scalar field of
the Sapling value commitment (spec § Jubjub). -/
def jubjubScalarOrder : ℕ := 0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7

/-- Maximum transaction size in bytes: a transaction cannot exceed the maximum block size
(`2000000` bytes, a consensus rule). -/
def maxTxBytes : ℕ := 2000000

/-- Minimum bytes of a Sapling v4 Spend description (spec § Spend Description Encoding). -/
def saplingSpendBytesV4 : ℕ :=
  32 +    -- cv            byte[32]
  32 +    -- anchor        byte[32]   (per-spend in v4)
  32 +    -- nullifier     byte[32]
  32 +    -- rk            byte[32]
  192 +   -- zkproof       byte[192]
  64      -- spendAuthSig  byte[64]

/-- Minimum bytes a Sapling Spend contributes to a v5 transaction. The `zkproof` (192) and
`spendAuthSig` (64) move to per-spend transaction-level vectors (`vSpendProofsSapling`,
`vSpendAuthSigs`) but are still counted once per spend; only the `anchor` (32) becomes shared across
the transaction, so the per-spend minimum is `384 − 32 = 352`. -/
def saplingSpendBytesV5 : ℕ :=
  32 +    -- cv            byte[32]
  32 +    -- nullifier     byte[32]
  32 +    -- rk            byte[32]
  192 +   -- zkproof       byte[192]  (in vSpendProofsSapling, per spend)
  64      -- spendAuthSig  byte[64]   (in vSpendAuthSigs, per spend)

/-- Minimum bytes of a Sapling Output description (spec § Output Description Encoding); identical for
v4 and v5 (the v5 `zkproof` moves to `vOutputProofsSapling` but stays per-output). -/
def saplingOutputBytes : ℕ :=
  32 +    -- cv             byte[32]
  32 +    -- cmu            byte[32]
  32 +    -- ephemeralKey   byte[32]
  580 +   -- encCiphertext  byte[580]
  80 +    -- outCiphertext  byte[80]
  192     -- zkproof        byte[192]

example : saplingSpendBytesV4 = 384 := by norm_num [saplingSpendBytesV4]
example : saplingSpendBytesV5 = 352 := by norm_num [saplingSpendBytesV5]
example : saplingOutputBytes = 948 := by norm_num [saplingOutputBytes]

/-- Maximum number of Spend descriptions in a v4 transaction: `⌊maxTxBytes / 384⌋`. -/
def saplingMaxSpendsV4 : ℕ := maxTxBytes / saplingSpendBytesV4

/-- Maximum number of Spend descriptions in a v5 transaction: `⌊maxTxBytes / 352⌋`. -/
def saplingMaxSpendsV5 : ℕ := maxTxBytes / saplingSpendBytesV5

/-- Maximum number of Output descriptions (either version): `⌊maxTxBytes / 948⌋`. -/
def saplingMaxOutputs : ℕ := maxTxBytes / saplingOutputBytes

example : saplingMaxSpendsV4 = 5208 := by norm_num [saplingMaxSpendsV4, maxTxBytes, saplingSpendBytesV4]
example : saplingMaxSpendsV5 = 5681 := by norm_num [saplingMaxSpendsV5, maxTxBytes, saplingSpendBytesV5]
example : saplingMaxOutputs = 2109 := by norm_num [saplingMaxOutputs, maxTxBytes, saplingOutputBytes]

/-- Spend count from the byte budget: `n` spends of `≥ size` bytes fit in `≤ maxTxBytes` only if
`n ≤ maxTxBytes / size`. -/
theorem sapling_spend_count_v4 (n : ℕ) (h : saplingSpendBytesV4 * n ≤ maxTxBytes) :
    n ≤ saplingMaxSpendsV4 := by
  simp only [saplingSpendBytesV4, saplingMaxSpendsV4, maxTxBytes] at h ⊢; omega

theorem sapling_spend_count_v5 (n : ℕ) (h : saplingSpendBytesV5 * n ≤ maxTxBytes) :
    n ≤ saplingMaxSpendsV5 := by
  simp only [saplingSpendBytesV5, saplingMaxSpendsV5, maxTxBytes] at h ⊢; omega

theorem sapling_output_count (m : ℕ) (h : saplingOutputBytes * m ≤ maxTxBytes) :
    m ≤ saplingMaxOutputs := by
  simp only [saplingOutputBytes, saplingMaxOutputs, maxTxBytes] at h ⊢; omega

/-- The Sapling `vSum` magnitude bound for `nspend` spends and `saplingMaxOutputs` outputs: each
value (spend or output) has `|v| ≤ 2^64 − 1` and `vBalance` has `|vBalance| ≤ 2^63`, so
`|vSum| ≤ (nspend + saplingMaxOutputs)·(2^64 − 1) + 2^63`. This is coarser than the spec's asymmetric
range, but any bound below the field order suffices for the no-overflow lift. -/
def saplingVSumBound (nspend : ℕ) : ℤ := ((nspend : ℤ) + saplingMaxOutputs) * (2^64 - 1) + 2^63

/-- **Sapling no-overflow bound (general).** Spend/output values are range-proven to
`0 ≤ v ≤ 2^64 − 1` (hence `|v| ≤ 2^64 − 1`); there are `≤ nspend` spends and `≤ saplingMaxOutputs`
outputs; and `vBalance` is signed 64-bit (`|vBalance| ≤ 2^63`). Bounding `|vSum|` by the uniform
per-element magnitude — as Orchard does for its signed net values — gives `vSum.natAbs < r` once `r`
exceeds `saplingVSumBound nspend`. The `v4` / `v5` corollaries instantiate `nspend`. -/
theorem sapling_natAbs_lt {r : ℕ} (olds news : List ℤ) (vBalance : ℤ) (nspend : ℕ)
    (hold : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hno : olds.length ≤ nspend)
    (hmo : news.length ≤ saplingMaxOutputs)
    (hvb : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound nspend < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r := by
  refine natAbs_lt_of_abs_le ?_ hr
  have habs : ∀ {l : List ℤ} {n : ℕ}, (∀ v ∈ l, 0 ≤ v ∧ v ≤ 2^64 - 1) → l.length ≤ n →
      |l.sum| ≤ (n : ℤ) * (2^64 - 1) := by
    intro l n hl hlen
    refine le_trans (abs_listSum_le fun v hv => ?_)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by norm_num))
    exact abs_le.mpr ⟨by linarith [(hl v hv).1, show (0:ℤ) ≤ 2^64 - 1 by norm_num], (hl v hv).2⟩
  have ho := habs hold hno
  have hn := habs hnew hmo
  calc |olds.sum - news.sum - vBalance|
      ≤ |olds.sum - news.sum| + |vBalance| := abs_sub _ _
    _ ≤ |olds.sum| + |news.sum| + |vBalance| := by linarith [abs_sub olds.sum news.sum]
    _ ≤ (nspend : ℤ) * (2^64 - 1) + (saplingMaxOutputs : ℤ) * (2^64 - 1) + 2^63 := by
        linarith [ho, hn, hvb]
    _ = saplingVSumBound nspend := by simp only [saplingVSumBound]; ring

/-- **Sapling v4**: feed the spend/output byte budgets (from the 2 MB limit), derive the counts
(`n ≤ 5208`, `m ≤ 2109`), and conclude `vSum.natAbs < r` once `r` exceeds
`saplingVSumBound saplingMaxSpendsV4`. -/
theorem sapling_natAbs_lt_v4 {r : ℕ} (olds news : List ℤ) (vBalance : ℤ)
    (hold : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hspend : saplingSpendBytesV4 * olds.length ≤ maxTxBytes)
    (houtput : saplingOutputBytes * news.length ≤ maxTxBytes)
    (hvb : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound saplingMaxSpendsV4 < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r :=
  sapling_natAbs_lt olds news vBalance saplingMaxSpendsV4 hold hnew
    (sapling_spend_count_v4 _ hspend) (sapling_output_count _ houtput) hvb hr

/-- **Sapling v5**: as v4 but with the smaller v5 Spend size, giving `n ≤ 5681`. -/
theorem sapling_natAbs_lt_v5 {r : ℕ} (olds news : List ℤ) (vBalance : ℤ)
    (hold : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hspend : saplingSpendBytesV5 * olds.length ≤ maxTxBytes)
    (houtput : saplingOutputBytes * news.length ≤ maxTxBytes)
    (hvb : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound saplingMaxSpendsV5 < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r :=
  sapling_natAbs_lt olds news vBalance saplingMaxSpendsV5 hold hnew
    (sapling_spend_count_v5 _ hspend) (sapling_output_count _ houtput) hvb hr

/-- The larger v5 bound fits the Jubjub scalar field, so the corollaries are not vacuous (the v4
bound is smaller, so it fits too). -/
example : saplingVSumBound saplingMaxSpendsV5 < (jubjubScalarOrder : ℤ) := by
  norm_num [saplingVSumBound, saplingMaxSpendsV5, saplingSpendBytesV5, saplingMaxOutputs,
    saplingOutputBytes, maxTxBytes, jubjubScalarOrder]

end Zcash.Security.BindingSignature
