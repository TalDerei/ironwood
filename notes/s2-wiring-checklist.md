# §1↔§2 weld — wiring checklist

Context: C1/C3 derive `IpaRelation`/`circuitSat` from *structured checks* (the transcript tree, the gate
point-check) — the cryptographic extraction is genuinely proven, binding-free, kernel-clean. The reviews
flagged that the **weld** from the deployed flattened `assemble.eval = 0` to those structured checks was
still *assumed* (bundled in the bridge + the C3 hypotheses).

Two soundness routes are proven. (a) The **recursive** route: the IPA opening soundness over halo2's concrete
`U`/`W`/`S` structure (`deployed_ipa_soundV`) + the multiopen decode + the SZ lift, via a rewinding-tree
bridge. (b) The **AGM** route — what genuinely closes O1/O2/O3 *without a posited tree*: the structured
relations are derived *from* `assemble.eval = 0` by the augmented binding. The findings are addressed below.

Legend: ✅ closed (to the named floor) · 🔒 named standard floor (won't be eliminated) · ✍ docs.

## ✅ O1 — CLOSED via the AGM route: `DeployedAccepts → IpaRelation`, no posited tree

- [x] **O1.** Chain (all in `Zcash/Snark/{IpaUWS,Weld}`, kernel-clean):
  `deployed_flat_split` (the augmented binding reads `assemble.eval = 0` off as the g/U/W relations) →
  `deployed_open_value` (the value `⟨aP,b⟩ = v` from those relations + SZ) → `ipaRelation_of_flat`
  (`IpaRelation` from the flat equation) → `deployed_accept_flat` (the §1 glue:
  `assemble.eval = 0` unfolds to that flat equation under the AGM representations, via `eval_assembleFinalMsm`)
  → `orchard_verifier_sound_deployed_agm` (**`DeployedAccepts → IpaRelation`**). No `DeployedIpaAcceptV` tree
  is posited; the MSM↔structured-relations correspondence is a *proof from* `assemble.eval = 0`. Floor 🔒: the
  AGM representations (`hP`/`hS`/`hRounds` — the prover's elements have `(g,U,W)`-reps), the augmented binding
  (DLR), and the SZ exclusions (`hSxi` the `ξ`/S-root, `huRounds` the `z`/no-`U`-interference). [R3-a.i]

## ✅ O3 — CLOSED: decode wired + the relation stated over the columns (no free `a`)

- [x] **O3.** `multiopen_decode_deployed` / `decoded_columns_of_accept` recover the per-column openings on-path
  (the proven decode). `orchard_verifier_sound_deployed_cols` states the conclusion **over the decoded columns
  themselves** (the circuit witness), with no free collapse witness `a` — the `a`↔`col` link review flagged is
  dissolved (the IPA opening lives inside the decode). Floor 🔒: the batching rewinding
  (`DeployedMultiopenRewind`, a ROM bridge) and the column↔circuit identification (VK-correctness). [R3-c, R1-b]

## ✅ O2 — CLOSED: the gate point-check DERIVED from the vanishing argument (not assumed)

- [x] **O2.** `deployed_constraint_of_decode` (`Zcash/Snark/Weld`) derives the constraint identity: the decoded
  `h`-column's eval (`h.eval x = expectedHEval`, from the decode — the deployed vanishing query) plus the
  VK-correctness point-eval (`numerator.eval x = expectedHEval·(xⁿ−1)`) give the point-check, which
  `constraint_identity_of_accept` lifts to the polynomial identity by Schwartz–Zippel. So `hquot` is **derived**
  from the decode + VK + SZ, no longer a free hypothesis. Floor 🔒: the decode (proven), the VK numerator
  (the assembly's full gate+permutation+lookup constraint = the circuit's — the §3 boundary; the perm/lookup
  polynomials are subsumed here, not modeled in Lean), and SZ. [R1-a, R2-a, R3-d.3]

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

## Integrated capstone (the end-to-end composition)
`orchard_verifier_sound_deployed_complete` (+ Vesta `orchard_verifier_sound_vesta_complete`) composes all
three into **one exported theorem** over the real assembly: O1 (AGM) derives `IpaRelation` from
`DeployedAccepts` with **no posited tree**, O3 recovers the columns, and O2 derives the gate identity from the
decoded `h`-column + the VK numerator + SZ — so the capstone has **no `hIpa`/tree bridge and no assumed
`hquot`**. Its inputs are exactly the named floor.

Open nudges (clearly marked, not hidden gaps): (i) `hSxi`/`huRounds` are named SZ exclusions (the `ξ`/`z`
challenge arguments) — proving them from the SZ bound would shrink O1's floor to pure AGM+binding, but they
bottom at the same good-challenge floor as `hgood`. (ii) the perm/lookup polynomials sit in O2's VK numerator
(`hNum`), the §3 boundary.

## Summary
O1/O2/O3 are now closed to the named floor via the AGM route (no posited tree):
- **O1** — `orchard_verifier_sound_deployed_agm`: `DeployedAccepts → IpaRelation`, the structured relations
  derived from `assemble.eval = 0` by the augmented binding (`deployed_flat_split`/`deployed_open_value`/
  `ipaRelation_of_flat`/`deployed_accept_flat`). No tree posited.
- **O2** — `deployed_constraint_of_decode`: the gate point-check derived from the decoded `h`-column + the VK
  numerator + SZ; `hquot` no longer assumed.
- **O3** — `decoded_columns_of_accept` + `orchard_verifier_sound_deployed_cols`: decode on-path, conclusion
  over the recovered columns, no free `a`.

The residual is the standard named floor: the **AGM representations** (route b) / the **rewinding** (route a),
the **augmented binding** (DLR), the **SZ challenge exclusions** (`z`, `ξ`, the good challenge), and
**VK-correctness** — which, for O2, legitimately carries the permutation/lookup constraints (the assembly's
numerator = the circuit's full constraint polynomial), the §3 circuit-encoding boundary, rather than
re-deriving them as Lean polynomials. All soundness *logic* connecting these is proven and kernel-clean.
