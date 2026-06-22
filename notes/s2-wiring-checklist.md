# §1↔§2 weld — wiring checklist

Context: C1/C3 derive `IpaRelation`/`circuitSat` from *structured checks* (the transcript tree, the gate
point-check) — the cryptographic extraction is genuinely proven, binding-free, kernel-clean. The reviews
flagged that the **weld** from the deployed flattened `assemble.eval = 0` to those structured checks was
still *assumed* (bundled in the bridge + the C3 hypotheses).

The headline result is proven: the recursive IPA opening soundness over halo2's **concrete `U`/`W`/`S`
structure** (`deployed_ipa_soundV`). The three follow-up wiring items O1/O2/O3 are now **all closed to the
named floor** — `orchard_verifier_sound_deployed_closed` (+ Vesta `_vesta_closed`) derives the opening, the
per-column decode, and the gate constraint from the deployed accept. The residual is exactly the standard
floor (two rewinding bridges, binding, SZ, VK-correctness); see the honest caveat under O2.

Legend: ✅ proven & on the capstone path · 🔒 named standard floor (won't be eliminated) · ✍ docs.

## ✅ O1 — CLOSED (structural correspondence proven; bridge = pure rewinding)

- [x] **O1.** `deployed_gterm_foldAll` (`Zcash/Snark/IpaDeployed`) resolves the `List.ofFn`-length↔`m` cast,
  so the assembly's `computeS` generator term equals `[-c]·foldAll`. `deployed_verification_eq`
  (`Zcash/Snark/Weld`) then proves the flat deployed accept (`assembleFinalMsm.eval`) **is** halo2's IPA
  verifier equation `P' + Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ) + [-c·b·z]U + [-f]W + [-c]G'₀` with `G'₀ = foldAll` explicit,
  for the multiopen commitment/value. So the MSM↔(IPA equation) structural correspondence is **proven**, not
  bundled; `DeployedIpaRewind`'s sole residual is the rewinding of that proven equation into the 3-ary tree
  (the ROM floor). The fold facts are on the proven deployed-accept path. [R3-a.i]

## ✅ O3 — CLOSED (the multiopen decode wired to acceptance)

- [x] **O3.** `multiopen_decode_deployed` (`Zcash/Snark/Multiopen`) composes `deployed_ipa_soundV` (the
  `U`/`W`/`S`-peeled opening at each batching challenge) with `batch_open_soundV` (the Vandermonde decode);
  `DeployedMultiopenRewind` + `decoded_columns_of_accept` (`Zcash/Snark/Weld`) derive the per-column openings
  `∃ col, ∀ i, commit srs col_i = C i ∧ ⟨col_i, b⟩ = e i` from acceptance. So `decodeAdvice`/`decodeInstance`
  act on the **genuinely recovered** columns, not free functions. Residual floor 🔒: the batching rewinding
  (`DeployedMultiopenRewind`, a ROM/forking bridge — the analog of the IPA `DeployedIpaRewind`) and the
  identification of decoded columns with the circuit's columns (VK-correctness). [R3-c, R1-b]

## ✅ O2 — CLOSED to the floor (constraint derived from the recovered columns)

- [x] **O2.** `orchard_verifier_sound_deployed_closed` (`Zcash/Snark/Weld`, + Vesta `_vesta_closed`) derives
  the gate constraint on the **decoded** columns: `circuitSatViaGates_of_check` lifts the gate point-check
  `hquot` (on the recovered `col`) to the polynomial identity via Schwartz–Zippel `hgood`. So the constraint
  side is on the path, over the columns the decode (O3) recovers. Residual floor 🔒: SZ (`hgood`) and
  VK-correctness — `hquot` (the gate point-check on `col`) is the verifier's vanishing check expressed on the
  recovered columns. **Honest caveat:** `hquot` is taken as VK-correctness, not yet *derived* from the
  decoded `h`-column. Two things sit inside that VK floor: (i) `combineGates` models the **gate** constraints
  only, whereas `expectedHEval` folds `gates ++ permutation ++ lookup` — fully deriving `hquot` first needs
  the permutation/lookup arguments lifted to polynomials (the §3 circuit-encoding workstream); (ii) the
  multiopen-combination link between the IPA witness `a` and the columns `col` is carried by `hencodes`.
  [R1-a, R2-a, R3-d.3]

## ✅ Proven & on the capstone path

- [x] **B-rest — the recursive opening soundness over `U`/`W`/`S` (the headline).** `Zcash/Snark/IpaUWS.lean`:
  `AugmentedBinding`/`.separate`/`deployed_leaf_peel` (the peeling), `DeployedIpaAcceptV` (the deployed
  recursion carrying `U` value-binding, `W` blinding, `S`/`ξ` synthetic blinding), `deployed_to_acceptV`
  (peels to the clean `IpaAcceptV`), `deployed_ipa_soundV` (composes with the proven `ipa_soundV`) →
  `∃ a, ⟨a,g⟩ = P ∧ ⟨a,b⟩ = v`. On the capstone path via `ipaRelation_of_deployedAcceptV`. Kernel-clean.
- [x] **B-core (facts).** `foldAll = G'₀` (`compute_s`/`compute_g`), `compute_b = ⟨sFun u 1, evalVector x⟩` —
  proven, faithful to the Rust. *(Wiring to the bridge = O1.)*
- [x] **B3 (pin `P`/`b`/`v`).** `orchard_verifier_sound_deployed_pinned`: `P = multiopenCommitment`,
  `v = multiopenValue`, `b = evalVector shape.k ch.x3`. *(The "pure rewinding" half of the split = O1.)*
- [x] **C3 lift.** `circuitSatViaGates_of_check`: gate point-check + SZ good challenge → constraint identity.
  *(Deriving the point-check from the MSM = O2.)*
- [x] **C1 decode logic.** `multiopen_decode_of_trees` etc. *(Wiring = O3.)*
- [x] **A1–A3** (honesty docstrings, `ea8d3e9`), **D1** (`_vesta_C3`, `_vesta_full`), **E1**
  (`nonInteractiveFingerprint_matches`), **F1** (de-staled `fv-review-checklist.md`).

## 🔒 The legitimate named floor (standard crypto assumptions — not "open")
- **Special-soundness rewinding** — acceptance → a distinct-challenge transcript tree (ROM/forking).
- **Augmented binding** (`AugmentedBinding`: `g ∪ {U,W}` independent) — DLR hardness / AGM on the Pasta
  generators (the plain-commitment reduction is proven; here extended to `params.u`/`params.w`, and assumed
  for every folded family).
- **Challenge exclusions** — `z ≠ 0` (no-`U`-interference) and the SZ good challenge `hgood` (`≤ deg/p`).
- **VK-correctness** (`hencodes`, §3 — incl. O3's column-layout identification), **Vesta curve order**
  (`Fact VestaOrder`), finite-field arithmetic.

## Summary
All of O1/O2/O3 are now closed to the named floor, with `orchard_verifier_sound_deployed_closed`
(+ Vesta `_vesta_closed`) deriving the opening, the per-column decode, and the gate constraint from the
deployed accept:
- **O1** — `deployed_verification_eq`: the flat accept IS halo2's IPA equation with `G'₀ = foldAll`; bridge =
  pure rewinding.
- **O3** — `multiopen_decode_deployed` / `decoded_columns_of_accept`: the columns are recovered from the
  batching rewinding (proven decode); `decodeAdvice`/`decodeInstance` act on them.
- **O2** — `circuitSatViaGates_of_check` lifts the gate point-check on the recovered columns to the identity
  (SZ). The constraint side is on the path.

The remaining trust boundary is the standard named floor: the IPA + batching **rewinding** bridges, the
**augmented binding** (DLR/AGM), the **challenge exclusions** (`z ≠ 0`, SZ), and **VK-correctness**. Note
VK-correctness now legitimately carries more weight on the constraint side: `hquot` (the gate point-check) is
the verifier's vanishing check on the recovered columns rather than a from-scratch derivation, and a *fully*
derived `hquot` would additionally require the permutation/lookup arguments modeled as polynomials (the §3
circuit-encoding workstream — `combineGates` currently covers only the gates). The soundness *logic*
(`deployed_ipa_soundV`, `multiopen_decode_deployed`, `circuitSatViaGates_of_check`) is all proven and wired.
