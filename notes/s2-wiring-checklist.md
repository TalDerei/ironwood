# §1↔§2 weld — wiring checklist

Context: C1/C3 derive `IpaRelation`/`circuitSat` from *structured checks* (the transcript tree, the gate
point-check) — the cryptographic extraction is genuinely proven, binding-free, kernel-clean. The reviews
flagged that the **weld** from the deployed flattened `assemble.eval = 0` to those structured checks was
still *assumed* (bundled in the bridge + the C3 hypotheses).

The headline result is proven: the recursive IPA opening soundness over halo2's **concrete `U`/`W`/`S`
structure** (`deployed_ipa_soundV`, genuinely on-path). `orchard_verifier_sound_deployed_closed` (+ Vesta
`_vesta_closed`) composes it with the multiopen decode and the SZ constraint lift.

**Honest status (do not overclaim "closed to floor").** A round of review correctly showed the capstone is
*not* closed to the irreducible cryptographic floor. Its residual = the legitimate floor (two rewinding
bridges, binding, SZ, VK-correctness) **plus three provable-but-unmodeled facts**: (O1) the MSM↔tree
correspondence is proven *flat* (`deployed_verification_eq`) but is a **sidecar** — not composed into the
bridge, which posits the tree wholesale; (O2) `hquot` (the gate point-check) is **assumed**, not derived from
the vanishing argument; (O3-link) the IPA witness `a` and the decoded columns `col` are **not linked** (the
multiopen combination is carried by `hencodes`). What *is* genuinely done is marked below.

Legend: ✅ proven & on-path · ◑ partial (proven core, residual noted) · 🔒 named standard floor · ✍ docs.

## ◑ O1 — structural fact PROVEN, but a sidecar (not wired into the bridge)

- [~] **O1.** `deployed_gterm_foldAll` (`Zcash/Snark/IpaDeployed`) resolves the `List.ofFn`-length↔`m` cast,
  and `deployed_verification_eq` (`Zcash/Snark/Weld`) proves the flat deployed accept (`assembleFinalMsm.eval`)
  **is** halo2's IPA verifier equation `P' + Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ) + [-c·b·z]U + [-f]W + [-c]G'₀` with
  `G'₀ = foldAll`. So the *flat* MSM↔IPA-equation correspondence is **proven**. **But it is a sidecar**: it is
  not composed into `DeployedIpaRewind`, which still posits the `DeployedIpaAcceptV` tree wholesale. Reducing
  the bridge to pure rewinding needs the lemma threaded in so the tree's node/leaf checks are *derived* from
  the verification equation — the flat↔recursive forking reduction, **not done**. [R3-a.i]

## ◑ O3 — decode WIRED on-path; the `a`↔`col` link not modeled

- [~] **O3.** `multiopen_decode_deployed` (`Zcash/Snark/Multiopen`) composes `deployed_ipa_soundV` with
  `batch_open_soundV`; `DeployedMultiopenRewind` + `decoded_columns_of_accept` (`Zcash/Snark/Weld`) derive the
  per-column openings `∃ col, ∀ i, commit srs col_i = C i ∧ ⟨col_i, b⟩ = e i` from acceptance — genuinely
  on-path, so `decodeAdvice`/`decodeInstance` act on the recovered columns, not free functions. **Residual:**
  the batching rewinding (`DeployedMultiopenRewind`, a ROM bridge) 🔒; the column↔circuit identification
  (VK-correctness) 🔒; and — flagged by review — the IPA witness `a` and the decoded `col` are extracted
  **independently** and not linked (the multiopen combination `a = Σ x₄ⁱ·(Σ x₁ʲ col)` is not modeled; carried
  by `hencodes`). [R3-c, R1-b]

## ◑ O2 — SZ lift PROVEN & on-path; `hquot` still assumed (§3 territory)

- [~] **O2.** `orchard_verifier_sound_deployed_closed` (`Zcash/Snark/Weld`, + Vesta `_vesta_closed`) lifts the
  gate point-check `hquot` on the recovered columns to the polynomial identity via Schwartz–Zippel
  (`circuitSatViaGates_of_check`/`hgood`) — proven and on-path. **But `hquot` itself is assumed**, not derived
  from the vanishing-argument part of the MSM. A from-scratch derivation needs (i) the permutation/lookup
  arguments lifted to polynomials (`combineGates` covers only gates; `expectedHEval` folds gates ++ perm ++
  lookup) — the §3 circuit-encoding workstream — and (ii) the decoded `h`-column connected to `expectedHEval`.
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
What is genuinely proven and on the capstone path: the `U`/`W`/`S` recursive opening soundness
(`deployed_ipa_soundV`), the multiopen decode (`multiopen_decode_deployed`/`decoded_columns_of_accept`), and
the SZ constraint lift (`circuitSatViaGates_of_check`). What is proven but **off-path (sidecar)**: the flat
MSM↔IPA-equation correspondence (`deployed_verification_eq`). `orchard_verifier_sound_deployed_closed`
(+ Vesta `_vesta_closed`) composes the on-path pieces.

What is **NOT** closed (per review — accurate): the capstone is not closed to the *irreducible* floor. Its
residual = the legitimate floor (two rewinding bridges, augmented binding, `z ≠ 0`, SZ, VK-correctness)
**plus** three provable-but-unmodeled facts: O1 the flat↔tree correspondence is not wired into the bridge
(forking reduction); O2 `hquot` is assumed, not derived (needs the perm/lookup polynomial modeling, §3); the
`a`↔`col` multiopen-combination link is not modeled (carried by `hencodes`). Each is substantial modeling
(comparable to the IPA weld), not quick wiring — and O2 bottoms out at the §3 circuit-encoding workstream.
