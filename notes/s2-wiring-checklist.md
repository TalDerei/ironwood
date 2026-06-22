# §1↔§2 weld — wiring checklist

Context: C1/C3 derive `IpaRelation`/`circuitSat` from *structured checks* (the transcript tree, the gate
point-check) — the cryptographic extraction is genuinely proven, binding-free, kernel-clean. The reviews
flagged that the **weld** from the deployed flattened `assemble.eval = 0` to those structured checks was
still *assumed* (bundled in the bridge + the C3 hypotheses).

The headline result is now proven: the recursive IPA opening soundness over halo2's **concrete `U`/`W`/`S`
structure** (`deployed_ipa_soundV`). But three wiring items remain genuinely open (proven-but-unwired or
assumed-not-derived) — they are **not** the irreducible floor; they are algebra still to connect. They are
listed first.

Legend: ✅ proven & on the capstone path · ⚠️ OPEN (proven-but-unwired / assumed-not-derived) ·
🔒 named standard floor (won't be eliminated) · ✍ docs.

## ✅ O1 — CLOSED (structural correspondence proven; bridge = pure rewinding)

- [x] **O1.** `deployed_gterm_foldAll` (`Zcash/Snark/IpaDeployed`) resolves the `List.ofFn`-length↔`m` cast,
  so the assembly's `computeS` generator term equals `[-c]·foldAll`. `deployed_verification_eq`
  (`Zcash/Snark/Weld`) then proves the flat deployed accept (`assembleFinalMsm.eval`) **is** halo2's IPA
  verifier equation `P' + Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ) + [-c·b·z]U + [-f]W + [-c]G'₀` with `G'₀ = foldAll` explicit,
  for the multiopen commitment/value. So the MSM↔(IPA equation) structural correspondence is **proven**, not
  bundled; `DeployedIpaRewind`'s sole residual is the rewinding of that proven equation into the 3-ary tree
  (the ROM floor). The fold facts are on the proven deployed-accept path. [R3-a.i]

## ⚠️ STILL OPEN — O2/O3 are the constraint/multiopen **assembly-soundness** workstream

These are not quick wiring. The soundness *logic* is proven (`circuitSatViaGates_of_check`, `eval_combineGates`,
`multiopen_decode_of_trees`), but connecting it to the deployed assembly needs substantial new **modeling**
and ultimately bottoms out at VK-correctness 🔒. Scoped precisely below.

- [ ] **O2. Derive the constraint check from `assemble.eval = 0`.** Two sub-gaps:
  - **O2a (modeling gap, newly identified).** The deployed vanishing check uses `expectedHEval` =
    `(allExpressions.foldl (acc·y+v) 0)·(xⁿ−1)⁻¹`, where `allExpressions = gates ++ permutation ++ lookup`
    (per sub-proof). The modeled `circuitSatViaGates`/`combineGates` covers **only the gates**. Closing O2
    first needs the permutation- and lookup-argument constraints lifted to polynomials (à la `Expr.toPoly`)
    and folded into the numerator so the modeled numerator = `expectedHEval`'s (incl. the `y`-power order and
    the `(xⁿ−1)⁻¹`).
  - **O2b (derivation).** Then derive `hquot` (the point-check) from the deployed accept: the vanishing query
    in `assembleQueries`, once opened via the multiopen decode (O3), forces `expectedHEval = h(x)·(xⁿ−1)`,
    i.e. the numerator point-check. Currently `hquot` is a capstone hypothesis. [R1-a, R2-a, R3-d.3]

- [ ] **O3. Connect the multiopen decode to `decodeAdvice`/`decodeInstance`.** `multiopen_decode_of_trees`
  recovers per-column openings from the **batching** rewinding (one challenge layer above the IPA opening).
  The capstone's IPA witness `a` opens the *collapsed* commitment; turning it into the circuit's advice/
  instance column polynomials needs (i) the two-layer multiopen structure (`x₁` compression + `x₄` collapse)
  modeled so the decode applies, (ii) a batching-rewinding bridge (another ROM floor), and (iii) the
  identification of decoded columns with the circuit's columns — VK-correctness 🔒. So `decodeAdvice`/
  `decodeInstance` stay the abstract decode interface; the logic is proven, the wiring is the assembly model.
  [R3-c, R1-b]

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
Closed: the U/W/S recursive opening soundness (`deployed_ipa_soundV`, kernel-clean, on-path), `P`/`b`/`v`
pinning, and **O1** (the MSM↔IPA-equation structural correspondence — `deployed_verification_eq` — so the
bridge is pure rewinding). What remains is **O2/O3**, the constraint/multiopen *assembly*-soundness
workstream: it needs genuinely new modeling (the permutation/lookup constraints as polynomials for O2a; the
two-layer multiopen + a batching-rewinding bridge for O3) and bottoms out at VK-correctness — not quick
wiring, and comparable in size to the IPA weld itself. The soundness logic those would consume
(`circuitSatViaGates_of_check`, `eval_combineGates`, `multiopen_decode_of_trees`) is already proven.
