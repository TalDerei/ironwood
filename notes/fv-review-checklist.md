# Ironwood SNARK FV — Review Findings Checklist (rounds 1 + 2, consolidated)

Net verdict from review: **§1 sufficiently implemented; §2 not yet.** The component lemmas are correct
and present, but the end-to-end soundness theorem (a) assumes what it should prove, (b) leaves the proven
lemmas off the proof path, and (c) shares no formal object with the fingerprint MSM. None of this is a
falsifiable bug — it's a gap between the artifact and its advertised guarantee.

Legend: `[ ]` open · `[~]` in progress · `[x]` done. Tags reference the finding (R1-n / R2-Fn).

---

## P0 — Integrity (stop the artifact from overclaiming) — cheap, do first ✅ DONE (commit 4e70890)
- [x] **I1. Honest docstrings.** Rewrite `Main.lean` / `KnowledgeSoundness.lean` docstrings to state the
  actual conditional status; drop "everything between them is proven" / "the middle hop is proven". [R2-F2 prose]
- [x] **I2. Reframe the capstone.** Rename `orchard_verifier_sound`(`_vesta`) → `_conditional` and state
  it is a conditional composition, not completed soundness. [R2-F1, R1-1]
- [x] **I3. Honest FS assumption.** Rename/relabel `FiatShamirSound` → `ExtractableFromAcceptance`; it
  bundles the IPA knowledge-soundness conclusion (consistent tree + opening), i.e. "IPA knowledge
  soundness + FS", not "just FS". [R2-F3]

## P1 — The §2 composition (the real soundness work) — substantial
- [x] **C1. Connect §1↔§2 — opening DERIVED, bridge narrowed (closed).** The IPA knowledge soundness is now
  *proven*, binding-free, in `Zcash/Snark/IpaSoundness.lean`: `vandermonde3` (3-point linear-coefficient
  functional) → `ipa_round_commit_with_coeffs` (the round is 3-special-sound for the commitment; two
  challenges leave `commit g a − P = (u₁+u₂)·X` undetermined, three kill it) → `ipa_soundV`
  (`IpaAcceptV g b P v t → ∃ a, commit g a = P ∧ ⟨a,b⟩ = v`, the full `IpaRelation`, by induction; the
  inner-product side is the same theorem at `G := F` since `commitGen b a = ⟨a,b⟩`). `ipaRelation_of_acceptV`
  + `orchard_verifier_sound_deployed_C1` wire it in: the bridge is now `FiatShamirTree` (accept → ∃ tree),
  **just the special-soundness rewinding** — `IpaRelation` is derived, no longer bundled. Kernel-clean
  (`[propext, Classical.choice, Quot.sound]`). Residual: `circuitSat` is still a separate hypothesis
  (`hcirc`, the constraint side = C3), and `accept → ∃ tree` is the irreducible standard-model rewinding.
  [R2-F1 HIGH]
- [x] **C2. Make `SnarkRelation` the right relation.** Done — `circuitSat` / `circuitSatViaGates` tie the
  constraint conjunct to the witness. [R2-F2a HIGH]
- [x] **C3. Put the proven lemmas on the path + derive `circuitSat`.** Done — `circuitSat` (instantiated to
  the concrete `circuitSatViaGates`) is now *derived*, not a black box: `orchard_verifier_sound_deployed_C3`
  (`c1d8f84`) discharges it via `circuitSatViaGates_of_check` from the verifier's gate **point** check
  (`hquot`, `numerator.eval x = h.eval x·(xⁿ−1)`) lifted to the polynomial identity by Schwartz–Zippel
  (`hgood`). The black-box `hcirc` is gone; kernel-clean. The **multiopen decode** is now *also proven*
  (`d2e59c7`, binding-free): `vandermonde_inv` (general `n`-point inverse) → `batch_open_soundV` (each
  column opens from the batched opening at `n` distinct challenges) → `multiopen_decode_of_trees` (composes
  `ipa_soundV` per rewound batching challenge — the full two-layer multiopen knowledge soundness). So all
  three soundness layers (IPA / multiopen / constraint) are proven as logic. Residual: the deployed *model
  reconciliation* (the combined IPA witness `a` ↔ the decoded columns, via the multiopen combination) plus
  the irreducible FS rewinding `hFS`. [R2-F2b, R2-F2c, R1-1]

## P2 — §1 fingerprint faithfulness
- [x] **F1. Identity-key commitments.** Done (`9b3f44f`) — `CommitmentId` slot identity threaded through
  the query builders; `constructIntermediateSets` groups by it (halo2 `ptr::eq`). `fingerprint_matches`
  still passes (real proof has no equal-valued distinct slots). Forks only needed to *exercise* the
  equal-value adversarial case. [R1-2, R2-F5]
- [x] **F2. Instantiate the SZ bound.** Done (honest downgrade to "agrees on this one proof"; full
  instantiation optional). [R1-3, R2-F5]
- [x] **F3. Document the curve boundary.** Done. [R2-F5]

## P3 — Process / hygiene
- [x] **H1. CI runs the match.** Done — `FixtureCheck` default target. [R2-F4 MEDIUM]
- [x] **H3. Remove stale `Scratch.olean`** — done. [R2-F6]

---

## Honest framing to keep
- The assumption is "soundness in the ROM, relative to DLR hardness + VK-correctness" — not unconditional.
- `native_decide` for the match = compiler trust (standard, but the only thing certifying §1's match).
- The proven lemmas (`extract_correct`, `accepting_fold_eq`, `commitGen_round`, `quotientCheck_sound`,
  `ipaRelation_unique`, binding reduction, `eval_combineGates`) are correct — the work is wiring them in.

---

## Progress
- [x] **P0 (I1–I3)** — `4e70890` honest framing; renamed `orchard_verifier_sound` → `_conditional`,
  `FiatShamirSound` → `ExtractableFromAcceptance`; docstrings de-overclaimed.
- [~] **C1** — NOT closed (honest, `b8f123a`). `orchard_verifier_sound_deployed_final` ties `S` to the real
  accept and puts extraction on-path, but the bridge `ExtractableFromDeployedAccept` still bundles the IPA
  opening + `circuitSat` as **assumptions** (`Accepting` can't imply them — no `P/b/v`). Genuine closure
  (derive them from `assemble.eval=0` via `eval_ipaFold` peel-back + `circuitSatViaGates_of_check`, removing
  the conjuncts) is substantial IPA-soundness work, open. `eval_ipaFold` is the lever but currently unused
  downstream.
- [x] **C2** — `99a3332`: `SnarkRelation` now ties both conjuncts to the same witness
  (`circuitSat a`); `circuitSatViaGates` = the intended concrete instantiation (decoded columns satisfy
  the `y`-combined gates). Fixes F2a (relation was on free polynomials).
- [x] **C3** — done. *Constraint side:* `constraint_identity_of_accept` (`f020979`) +
  `circuitSatViaGates_of_check` (`3a1293d`) — `circuitSat` derived from the deployed check. *Opening side:*
  per-node bridge `accepting_fold_eq_foldVec` (`37e607f`) → the recursion `accepting_imp_wconsistent` /
  `wconsistent_imp_consistent` / `accepting_extract` (`77c204b`, module `Consistency`): `accepting ⇒
  consistent ⇒ extracted`, only binding assumed. Wired into `orchard_sound_via_transcript` (`6bcff70`) —
  extraction now on the path.
- [x] **F2** — `e833847` honest downgrade ("agrees on this one proof"; SZ not instantiated). (Full
  instantiation on `assemble`'s coefficients still optional/open.)
- [x] **F3** — `e833847` curve-boundary documented (`G := ℕ` ⇒ says nothing about the curve).
- [x] **H1** — `1cb4dd9`: dedicated `FixtureCheck` target in `defaultTargets`, so `lake build` (CI) now
  compiles `fingerprint_matches`; `lake build Zcash` stays fast.
- [x] **H3** — orphan `Scratch.*` build artifacts removed.

### The §1↔§2 weld — U/W/S soundness closed; 3 wiring items open (details in `s2-wiring-checklist.md`)
The IPA / multiopen / constraint **soundness logic is fully proven** (binding-free, kernel-clean):
`ipa_soundV` (opening), `multiopen_decode_of_trees` / `batch_open_soundV` (per-column decode),
`circuitSatViaGates_of_check` (constraint). On top of that:

- **PROVEN — the recursive opening soundness over halo2's concrete `U`/`W`/`S` structure**
  (`Zcash/Snark/IpaUWS.lean`): `deployed_ipa_soundV` — the deployed verifier's single combined check
  (value-binding `U`, blinding `W`, synthetic-blinding `S`/`ξ`) peels via the augmented binding
  (`AugmentedBinding.separate`, `deployed_leaf_peel`, `deployed_to_acceptV`) onto the proven `ipa_soundV`.
  On the capstone path. The headline result.
- **PROVEN — the fold facts** (`Zcash/Snark/IpaDeployed.lean`): `foldAll = G'₀` (`compute_s`/`compute_g`) and
  `compute_b = ⟨sFun u 1, evalVector x⟩`, faithful to the Rust. **The capstone** (`Zcash/Snark/Weld.lean`):
  `orchard_verifier_sound_deployed_full` / `_pinned` (+ Vesta `_vesta_full`) derive both conjuncts of
  `SnarkRelation` with `P`/`b`/`v` pinned to the §1 assembly.
- **PARTIAL — O1 (`s2-wiring-checklist.md`):** `deployed_verification_eq` proves the flat deployed accept IS
  halo2's IPA verifier equation with `G'₀ = foldAll`. But (per review, accurate) it is a **sidecar** — not
  composed into `DeployedIpaRewind`, which still posits the tree wholesale. So the bridge still bundles the
  flat↔tree correspondence; reducing it to pure rewinding needs the forking reduction (not done).
- **PARTIAL — O2/O3 (`s2-wiring-checklist.md`):** O3 — `decoded_columns_of_accept` recovers the per-column
  openings on-path (proven decode), but the IPA witness `a` and the columns `col` are not linked (the
  multiopen combination is carried by `hencodes`). O2 — `circuitSatViaGates_of_check` lifts `hquot` via SZ
  (on-path), but `hquot` itself is **assumed**, not derived from the vanishing argument (needs the
  permutation/lookup arguments modeled as polynomials — the §3 workstream). So `orchard_verifier_sound_deployed_closed`
  is **not** closed to the irreducible floor; its residual is the floor + these unmodeled facts.

What remains is the standard named cryptographic floor PLUS the unmodeled facts above (O1 flat↔tree wiring,
O2 hquot derivation, the a↔col link):
- **Special-soundness rewinding** (`DeployedIpaRewind`: accept → distinct-challenge tree) — irreducible ROM.
- **Augmented binding** (`AugmentedBinding`: `g ∪ {U,W}` independent) — DLR hardness / AGM on the Pasta
  generators (reduction proven for the plain commitment; extended to `params.u`/`params.w`).
- **Challenge exclusions**: `z ≠ 0` (no-`U`-interference) and the SZ good challenge `hgood` (`≤ deg/p`).
- **VK-correctness** (`hencodes`, §3 — incl. the decode's column-layout identification), Vesta curve order
  (`Fact VestaOrder`), finite-field arithmetic.

### §1 faithfulness (done)
`eval_ipaFold`, `eval_accumulateCommitment`, `eval_compressSet_fst` (x₁ Horner),
`eval_multiopenCombine_fst` (x₄ Horner), and `eval_assembleFinalMsm` verify the assembly *is* the
verification equation, symbolically (all inputs) — stronger than the one-proof `native_decide`
(`fingerprint_matches`), and now also connected to the FS-derived fingerprint
(`nonInteractiveFingerprint_matches`, modulo the FS schedule assumption). The SZ random-eval match is the
generic `fingerprint_schwartz_zippel`; the numeric link is the one captured proof (`fingerprint_matches`).
