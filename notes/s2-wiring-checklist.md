# §1↔§2 weld — wiring checklist (CLOSED)

Context: C1/C3 derive `IpaRelation`/`circuitSat` from *structured checks* (the transcript tree, the gate
point-check) — the cryptographic extraction is genuinely proven, binding-free, kernel-clean. The reviews
flagged that the **weld** from the deployed flattened `assemble.eval = 0` to those structured checks was
still *assumed* (bundled in `FiatShamirTree`/`hquot`), and that the lemma discharging most of it
(`eval_assembleFinalMsm`) was proven but **unwired**.

This is now closed: the recursive IPA opening soundness over halo2's **concrete `U`/`W`/`S` structure** is
proven (`Zcash/Snark/IpaUWS.lean`), the generator/value fold correspondence is proven
(`Zcash/Snark/IpaDeployed.lean`), and the capstone (`Zcash/Snark/Weld.lean`) derives both conjuncts of
`SnarkRelation` with `P`/`b`/`v` **pinned** to the §1 fingerprint. The only remaining inputs are the
legitimate cryptographic floor.

Legend: ⚙ mechanical · 🔒 irreducible/standard floor (named, documented) · ✍ docs/integrity · ✅ done+committed

## A. Honesty fixes ✍ — ✅ DONE (`ea8d3e9`)
- [x] **A1.** `FiatShamirTree` docstring rewritten. [R3-a]
- [x] **A2.** `_C1`/`_C3` docstrings made honest. [R3-a, R1-a]
- [x] **A3.** `orchard_verifier_sound_deployed_final` marked superseded. [R2-d]

## B. The structural correspondence + the recursive opening soundness — ✅ DONE
Verified against `zcash/halo2` `poly/commitment/{verifier,prover}.rs`: `eval_ipaFold` matches `verify_proof`
line-for-line; the relation `v = p(x₃)`, `[-c·b·z]U` binds `⟨p',b⟩ = 0`, `[-f]W` the blinding, `S`/`ξ` the
synthetic blinding (from `create_proof`).
- [x] **B-core (generator + value fold).** `Zcash/Snark/IpaDeployed.lean`: `computeS`/`sFun`/`sFun_fold`
  (the deployed `computeS` flattening IS `foldGens` at the inverted challenge), `foldAll_eq_compute_g`
  (`foldAll = G'₀`), `computeS_gterm_foldAll` (the `g`-term `= [-c]·G'₀`); and `computeB_snd`/`computeB_cons`/
  `loHalf_pow`/`hiHalf_pow`/`computeB_eq` (halo2 `compute_b = ⟨sFun u 1, evalVector x⟩`). Kernel-clean,
  faithful to the source.
- [x] **B-rest (the recursive opening soundness over `U`/`W`/`S`).** `Zcash/Snark/IpaUWS.lean`:
  `AugmentedBinding` (`g ∪ {U,W}` jointly independent — DLR/AGM extended to the two fixed generators) +
  `AugmentedBinding.separate` (coordinate-wise peel) + `deployed_leaf_peel` (halo2's combined leaf
  `P+[z·v]U+[blind]W = [c]g₀+[z·c·b₀]U+[f]W` separates into the clean `IpaAcceptV` leaf checks). Then
  `DeployedIpaAcceptV` models the deployed recursion carrying `U`/`W`/`S` explicitly, `deployed_to_acceptV`
  peels it to `IpaAcceptV`, and `deployed_ipa_soundV` composes with the proven `ipa_soundV` →
  `∃ a, ⟨a,g⟩ = P ∧ ⟨a,b⟩ = v`. Kernel-clean. **This closes the `U`/`W`/`S` structure onto `ipa_soundV`.**
  Floor 🔒: the augmented binding (DLR/AGM) and the transcript tree (special-soundness rewinding).
- [x] **B3 (split + pin `P`/`b`/`v`).** `Zcash/Snark/Weld.lean`: `DeployedIpaRewind` is now the *pure*
  rewinding bridge (the `U`/`W`/`S` separation and the fold correspondence are proven, no longer bundled);
  `orchard_verifier_sound_deployed_pinned` pins `P = multiopenCommitment`, `v = multiopenValue`,
  `b = evalVector shape.k ch.x3` — the actual §1 assembly objects, not free metavariables.

## C. The constraint side + multiopen decode — ✅ DONE (logic proven; layout = VK floor)
- [x] **C1.** The multiopen decode logic is proven (`multiopen_decode_of_trees` / `batch_open_soundV` /
  `vandermonde_inv`, `Zcash/Snark/IpaSoundness.lean`): per-column openings recovered from the rewound
  batching trees, binding-free. `decodeAdvice`/`decodeInstance` in the capstone are the decode interface;
  the identification of the decoded columns with the circuit's advice/instance columns is part of
  VK-correctness 🔒 (the assembly's query layout = the circuit's columns). [R3-c, R1-b]
- [x] **C2.** `circuitSat` (concrete `circuitSatViaGates`) is *derived* from the verifier's gate point-check
  via `circuitSatViaGates_of_check` (`constraint_identity_of_accept` + Schwartz–Zippel). `hquot` (the gate
  point-check at `x`, part of `assemble.eval = 0`) and `hgood` (the SZ good challenge, the `≤ deg/p`
  exclusion) are the named constraint-side floor 🔒. [R1-a, R2-a, R3-d.3]

## D. Concrete Vesta coverage ⚙ — ✅ DONE
- [x] **D1.** `orchard_verifier_sound_vesta_C3` and `orchard_verifier_sound_vesta_full` (the full
  `U`/`W`/`S`-peeled capstone over `SWPoint Vesta.curve`). [R1-c, R2-c]

## E. FS schedule ↔ fixture ⚙ — ✅ DONE
- [x] **E1.** `nonInteractiveFingerprint_matches` (`Zcash/Snark/FixtureFiatShamir.lean`). [R2-b]

## F. Checklist hygiene ✍ — ✅ DONE
- [x] **F1.** `notes/fv-review-checklist.md` de-staled. [R1-d, R2-b]

## Honest end-state — the trust boundary
Proven (kernel-clean `[propext, Classical.choice, Quot.sound]`, faithful to halo2):
- §1 model = `verify_proof` (`eval_ipaFold`/`eval_assembleFinalMsm`, verified symbolically).
- The generator/value fold correspondence (`foldAll = G'₀`, `compute_b = ⟨sFun, evalVector⟩`).
- The IPA / multiopen / constraint **soundness logic** (`ipa_soundV`, `multiopen_decode_of_trees`,
  `circuitSatViaGates_of_check`).
- **The recursive opening soundness over halo2's concrete `U`/`W`/`S` structure** (`deployed_ipa_soundV`):
  the deployed verifier's combined check peels (augmented binding) to the clean recursion.
- The end-to-end capstone with `P`/`b`/`v` pinned (`orchard_verifier_sound_deployed_pinned`,
  `_vesta_full`).

Assumed (the legitimate, named, standard floor):
- **Special-soundness rewinding** (`DeployedIpaRewind`: acceptance → a distinct-challenge transcript tree) —
  the irreducible ROM/forking step.
- **Augmented binding** (`AugmentedBinding`: `g ∪ {U,W}` independent) — DLR hardness / AGM on the Pasta
  generators, the standard binding assumption extended to `params.u`/`params.w`.
- **The `z ≠ 0` binding challenge** and the **SZ good challenge `hgood`** — negligible-probability
  challenge exclusions.
- **VK-correctness** (`hencodes`, the assembly's gates/query layout = the Orchard circuit) and the **Vesta
  curve order** (`Fact VestaOrder`).
