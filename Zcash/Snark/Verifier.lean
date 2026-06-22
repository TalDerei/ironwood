import Mathlib
import Zcash.Snark.Msm

/-!
# The verifier's MSM assembly

This module assembles the fingerprint MSM the way the deployed verifier does (`plonk/verifier.rs`
together with the `poly/{multiopen,commitment}` openings): build the per-argument query commitments,
compress them through the multiopen folds, and finish with the inner-product-argument opening
(`Zcash.Snark.ipaFold`). It is filled in incrementally.

What this file currently provides:
* `CommitmentRef`, `VerifierQuery` — the shared query types (halo2 `CommitmentReference` / `VerifierQuery`).
* `vanishingHCommitment` — the vanishing argument's `h` commitment.
* `accumulateCommitment`, `compressQCommitments`, `multiopenCombine` — the multiopen `x₁` compression and
  `x₄` collapse (`multiopen/verifier.rs`).
* `lagrangeEval`, `multiopenEval` — the multiopen combined value `v` (the Lagrange interpolation step).

The point-set grouping (`construct_intermediate_sets`) is still taken as input — it is VK-fixed
bookkeeping that depends only on the query layout, and supplies the per-set commitment and evaluation
lists. Everything downstream (the `x₁`/`x₄` folds and the combined value `v`) is computed here.
-/

namespace Zcash.Snark

/-- A multiopen query's commitment reference (halo2 `CommitmentReference`): either a single group
element, or an MSM — the vanishing argument's folded `h` commitment is supplied as an MSM. -/
inductive CommitmentRef (k : ℕ) (F G : Type*) where
  | point : G → CommitmentRef k F G
  | msm : Msm k F G → CommitmentRef k F G
  deriving DecidableEq

/-- A commitment's **slot identity** — which commitment *object* it is, independent of its curve value.
This models halo2's pointer identity (`construct_intermediate_sets` keys by `std::ptr::eq`): the multiopen
grouping must treat two distinct proof/VK slots as distinct even if their curve values coincide, which a
value-equality key (`DecidableEq G`) would wrongly merge. Each constructor names a commitment source with
its structural indices (proof, column / set / lookup index). -/
inductive CommitmentId where
  | instanceCol : ℕ → ℕ → CommitmentId
  | adviceCol : ℕ → ℕ → CommitmentId
  | fixedCol : ℕ → CommitmentId
  | permProduct : ℕ → ℕ → CommitmentId
  | lookupProduct : ℕ → ℕ → CommitmentId
  | lookupPermInput : ℕ → ℕ → CommitmentId
  | lookupPermTable : ℕ → ℕ → CommitmentId
  | permCommon : ℕ → CommitmentId
  | vanishingH : CommitmentId
  | randomPoly : CommitmentId
  deriving DecidableEq

/-- A multiopen query (halo2 `VerifierQuery`): open `commitment` at `point`, claiming the value `eval`.
`commId` is the commitment's slot identity, used as the multiopen grouping key (halo2's pointer identity)
rather than the curve value `commitment`. -/
structure VerifierQuery (k : ℕ) (F G : Type*) where
  point : F
  commitment : CommitmentRef k F G
  eval : F
  commId : CommitmentId

/-- The vanishing argument's `h` commitment (halo2 `vanishing/verifier.rs`): fold the quotient pieces by
`xⁿ` into `Σᵢ hᵢ · (xⁿ)ⁱ`, built as the Rust does — scale the accumulator by `xⁿ` and append the next
piece, over the pieces in reverse. -/
def vanishingHCommitment {F G : Type*} [Field F] (k : ℕ) (xn : F) (hPieces : List G) : Msm k F G :=
  hPieces.reverse.foldl (fun acc c => (acc.scale xn).appendTerm (1 : F) c) (Msm.zero k F G)

/-- Accumulate one query commitment into a point set's compressed commitment, weighted by the current
`x₁` power (the multiopen `accumulate` closure): a plain commitment is appended as a term, an MSM
commitment is scaled by the power and added. -/
def accumulateCommitment {k : ℕ} {F G : Type*} [Field F] (pow : F) (c : CommitmentRef k F G)
    (acc : Msm k F G) : Msm k F G :=
  match c with
  | .point p => acc.appendTerm pow p
  | .msm m => acc.add (m.scale pow)

/-- The multiopen `x₁` compression (`multiopen/verifier.rs`): for each point set, fold its commitments
(in processing order) into `Σⱼ x₁ʲ · cⱼ`. `sets` lists, per point set, the commitments grouped into it by
`construct_intermediate_sets` (taken as input — it is VK-fixed bookkeeping). -/
def compressQCommitments {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (sets : List (List (CommitmentRef k F G))) : List (Msm k F G) :=
  sets.map fun setCommitments =>
    (setCommitments.foldl (fun (st : Msm k F G × F) c => (accumulateCommitment st.2 c st.1, st.2 * x1))
      (Msm.zero k F G, (1 : F))).1

/-- The multiopen `x₄` collapse (`multiopen/verifier.rs`): append the quotient commitment `q'`, then fold
the per-set compressed commitments `qCommitments` (paired with the prover's claimed evaluations `u`) by
`x₄`, accumulating both the MSM and the combined value `v` (starting from the Lagrange base `msmEval`). -/
def multiopenCombine {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F)
    (incoming : Msm k F G) : Msm k F G × F :=
  (qCommitments.zip u).foldl
    (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
    (incoming.appendTerm (1 : F) qPrime, msmEval)

/-- The value at `x` of the polynomial interpolating `(points, evals)`, in barycentric Lagrange form
`Σᵢ evalsᵢ · ∏_{j≠i} (x − pⱼ)/(pᵢ − pⱼ)`. This is the same field element as halo2's
`eval_polynomial (lagrange_interpolate points evals) x` (the unique interpolant evaluated at `x`). -/
def lagrangeEval {F : Type*} [Field F] (x : F) (points evals : List F) : F :=
  let n := points.length
  (List.range n).foldl (fun acc i =>
    let pi := points.getD i 0
    let li := (List.range n).foldl (fun p j =>
      if j = i then p else p * (x - points.getD j 0) / (pi - points.getD j 0)) (1 : F)
    acc + evals.getD i 0 * li) (0 : F)

/-- The multiopen combined evaluation `msm_eval` — the base of the opening value `v` (`multiopen/verifier.rs`).
For each point set (`s = (points, evals, u)`, with `evals` the `x₁`-compressed per-point evaluations and
`u` the prover's claimed quotient evaluation), subtract the Lagrange value of `evals` at `x₃`, divide out
the vanishing factors `∏ (x₃ − pt)⁻¹`, and combine the sets by `x₂`. -/
def multiopenEval {F : Type*} [Field F] (x2 x3 : F) (sets : List (List F × List F × F)) : F :=
  sets.foldl (fun msmEval s =>
    let rEval := lagrangeEval x3 s.1 s.2.1
    let evalSet := s.1.foldl (fun e point => e * (x3 - point)⁻¹) (s.2.2 - rEval)
    msmEval * x2 + evalSet) (0 : F)

end Zcash.Snark
