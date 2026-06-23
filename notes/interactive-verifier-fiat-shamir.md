# Interactive verifier, Fiat-Shamir, and the fingerprint match

**Goal.** Establish that the deployed (non-interactive) Ironwood verifier is the Fiat-Shamir image of
an explicit *interactive* verifier formalized in Lean, by showing the two produce the **same
fingerprint** (the assembled MSM). Match ⇒ the soundness we prove about the interactive verifier
(Schwartz–Zippel now; special-soundness and witness extraction later) transfers to the deployed code,
without a line-by-line translation proof.

Background: the error-path audit established that the MSM *is* the verifier — accept ⇔
`MSM = identity`, with no prover-controlled branch in between.

## The interactive verifier vs the deployed one

The deployed halo2 verifier is a public-coin interactive protocol with the verifier's coins replaced
by Fiat-Shamir hashes. Stripping Fiat-Shamir back off gives the **interactive verifier**: identical
message / round structure and identical MSM assembly, but the challenges
`θ, β, γ, y, x, x₁…x₄, ξ, z, {uⱼ}` are the verifier's genuine random coins, sent after each prover
message —

- prover → advice commitments; verifier → θ
- prover → lookup permuted commitments; verifier → β, γ
- prover → permutation / lookup product commitments, vanishing random commitment; verifier → y
- prover → quotient `h` pieces; verifier → x
- prover → instance/advice/fixed evals + permutation/lookup evals; (multiopen) verifier → x₁, x₂;
  prover → q′; verifier → x₃; prover → u; verifier → x₄
- IPA: prover → S; verifier → ξ, z; per round prover → (Lⱼ, Rⱼ), verifier → uⱼ; prover → c, f
- the verifier assembles one MSM and accepts iff it is the identity.

So the **only** difference between interactive and deployed is the *source* of the challenges. The
MSM-assembly — the `proof string + challenges → MSM` function deferred in the fingerprint work — is
shared. Formalizing the interactive verifier therefore means formalizing that assembly in Lean
(`assemble : Shape → SRS → ProofString → Challenges → Msm`), with the challenges as inputs.

## Fiat-Shamir (hand-waved)

The transform sets each challenge to a hash of the transcript so far. In the deployed code the hash is
**Blake2b** (`transcript.rs`, personalization `"Halo2-Transcript"`) — **not BLAKE3**, contrary to the
README (BLAKE3 is Ironwood's *txid* hash, not the SNARK transcript). Per scope, Fiat-Shamir is
hand-waved: we do not formalize Blake2b or the random-oracle reduction. In the match the challenges are
taken from the real transcript (captured alongside the MSM), so the match never re-derives them — it
validates the *assembly*, with the Fiat-Shamir step assumed to carry interactive soundness to the
non-interactive setting.

## The fingerprint match

Both verifiers assemble the same MSM as a function of `(proof string, challenges)`. So
"FS(interactive) = deployed" reduces to: **the Lean assembly equals the Rust assembly.** We check this
without transpilation, via the fingerprint:

- Run the deployed Rust verifier on a proof, capturing both the assembled MSM and the challenges it
  drew (the `FingerprintStrategy` capture, extended to also record the challenges).
- Run the Lean `assemble` on the same proof string and those challenges.
- Compare the two MSMs — either **full** (every coefficient) or via a **random evaluation** (one
  value, sound up to `d / p` by `Zcash.Snark.fingerprint_schwartz_zippel`).

A match means the two assembly *formulas* agree (a random-evaluation check makes one random proof
enough). This is the cross-check that replaces proving the Rust↔Lean translation correct.

## What the assembly needs (scope)

Reproducing the MSM assembly in Lean requires the **verifying-key–level circuit structure** (not the
prover's witness generation):

- the custom gate polynomials and their evaluation at the advice / fixed / instance evals (the
  vanishing argument, divided by `xⁿ − 1`);
- the permutation-argument and lookup-argument expressions;
- the query structure (column at rotation → point `x·ωᵃ`) and the fixed / permutation commitments from
  the VK;
- the multiopen compression (`x₁…x₄`, `construct_intermediate_sets`, the `q′` fold) and the IPA fold
  (`compute_s`, the `(Lⱼ, Rⱼ)` terms, the `u` / `w` coefficients).

This is the largest piece of the whole development — effectively the verifier re-expressed
symbolically. The fingerprint match is what keeps it honest: any divergence from the deployed assembly
surfaces as a mismatch rather than a silent error.

## Gating questions / risks

1. **Faithfulness of the assembly** — caught by the match, so divergences are detectable, not silent.
   Unlike the audit, no separate go/no-go is needed here: the match *is* the check.
2. **The capture must include the challenges**, not just the MSM, so the Lean side assembles at
   identical challenges. (Extends the current Rust capture.)
3. **The real Ironwood VK**, not the toy `plonk_api` circuit, is needed for the final claim — the toy
   circuit only validates the assembly *mechanism*; the assembly should be circuit-generic and
   validated on the toy VK first, then on Ironwood.
4. **Hand-waves**: Fiat-Shamir / Blake2b (the random-oracle step); the assembly's correctness rests on
   the match rather than a transpilation proof; curve / `pasta_curves` arithmetic remains hand-waved.

## Plan

1. **Capture the real Ironwood fingerprint + challenges** from `../orchard` (extend the existing
   Rust capture to record the challenges and run on the Ironwood circuit).
2. **Formalize the interactive verifier's assembly** in Lean —
   `assemble : Shape → SRS → ProofString → Challenges → Msm` — reproducing the halo2 construction,
   parameterized by the VK structure.
3. **Model Fiat-Shamir** as an opaque challenge-derivation (Blake2b hand-waved); the non-interactive
   verifier is `assemble` at FS-derived challenges.
4. **The fingerprint match**: show the Lean assembled MSM equals the captured Rust MSM on the same
   proof (full, or random-evaluation via `fingerprint_schwartz_zippel`). Match ⇒ the deployed verifier
   is the Fiat-Shamir image of our interactive verifier.
