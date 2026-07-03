import Mathlib
import Zcash.Snark.Soundness.Main

/-!
# Fixture: the decoded-column hypotheses are dischargeable

Regression guard for the decoded-column capstones' hypothesis shapes: every hypothesis of the terminal
decoded lemmas is discharged *concretely* on a toy instance, so a future reshape that reintroduces an
unsatisfiable form (the ∀-families `hquot ∧ hgood` vacuity described in the `MultiopenDecode` scope
section) breaks this file instead of passing silently.

The instance is the smallest single-point, rotation-free one in the model's documented scope: `k = 0`
(one URS generator, over `G := Fp` itself, where `commit` has trivial kernel), one column, all data
zero — the zero column satisfies the one-gate circuit `advice 0` with zero quotient at the opened
point. Both terminal entry points are exercised: `decoded_constraint_of_relation_and_batch` on a bare
batch, and `decoded_constraint_of_opening_or_relation` with its `hbatch` *derived* from a family of
accepting IPA transcripts (`multiopenRewindForRelation_of_acceptedFamily`), not assumed.
-/

namespace Zcash.Snark
namespace MultiopenDecodeFixture

open Polynomial

/-- Toy URS at `k = 0` over the scalar field itself: the single generator is `1`. -/
abbrev toyUrs : URS Fp := ⟨0, fun _ => 1, 0, 0⟩

/-- The toy index type is a singleton. -/
theorem toy_fin_eq_zero (j : Fin (2 ^ toyUrs.k)) : j = 0 := by
  cases j using Fin.cases with
  | zero => rfl
  | succ i => exact i.elim0

/-- At `k = 0` with generator `1`, a commitment is its single coefficient: `commit` has trivial
kernel, so the canonical decode is pinned by its spec alone. -/
theorem toy_commit_eq (a : Fin 1 → Fp) : commit toyUrs a = a 0 := by
  simp [commit, toyUrs]

/-- One column, everything zero: the batch family whose decode the fixture checks. -/
noncomputable def toyBatch :
    BatchOpeningsForWitness toyUrs (evalVector 0 0) (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) (fun _ => 0) where
  batchChallenge := fun _ => 0
  challengesDistinct := fun r s _ => Subsingleton.elim r s
  batched := fun _ _ => 0
  current := 0
  current_eq := rfl
  commitment := fun r => by simp [commit, toyUrs]
  value := fun r => by simp [commitGen]

/-- Any zero-column batch over the toy URS decodes to the zero columns — from the decode's spec and
the trivial kernel, without unfolding the Vandermonde inverse. -/
theorem toy_decode_zero {bvec : Fin 1 → Fp} {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs bvec (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) w) :
    decodedCols hb = fun _ => 0 := by
  funext i
  have hfam := (decodedCols_spec hb).decodedColumns
  have hz : hfam.coeffs i = fun _ => 0 := by
    funext j
    have h0 : hfam.coeffs i 0 = 0 := by
      have hc := hfam.commitment i
      rwa [toy_commit_eq] at hc
    have hj : j = 0 := toy_fin_eq_zero j
    rw [hj]; exact h0
  rw [hfam.polynomial i, hz]
  simp [coeffsToPoly]

/-- The one-gate circuit: read advice column `0`. -/
def toyGates : Fin 1 → Expr Fp := fun _ => Expr.advice 0

/-- The zero witness opens the zero statement over the toy URS. -/
theorem toy_opens :
    IpaRelation toyUrs (0 : Fp) (evalVector 0 (0 : Fp)) (0 : Fp) (fun _ => (0 : Fp)) := by
  constructor
  · simp [commit, toyUrs]
  · simp [innerProduct]

/-- The combined gate numerator over the decoded (zero) columns is the zero polynomial. -/
theorem toy_numerator {w : Fin 1 → Fp}
    (hb : BatchOpeningsForWitness toyUrs (evalVector 0 0) (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) w) :
    combineGates (fun _ => 0) (selectedPolys (decodedCols hb) (fun i : Fin 1 => i))
      (selectedPolys (decodedCols hb) (fun i : Fin 1 => i)) 0 toyGates = 0 := by
  rw [toy_decode_zero hb]
  simp [combineGates, gatePolys, toyGates, Expr.toPoly, selectedPolys, finFn]

/-- All hypotheses of `decoded_constraint_of_relation_and_batch` discharged concretely: the
regression guard that the decoded hypothesis shapes stay satisfiable. -/
theorem toy_relation_and_batch_discharged : True :=
  decoded_constraint_of_relation_and_batch (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 0 toy_opens toyBatch
    (by rw [toy_numerator toyBatch]; simp [quotientCheck])
    (by rw [toy_numerator toyBatch]; intro h; simp at h)
    (fun _ _ _ => trivial)

/-- Accepting transcripts for every batching challenge of the zero batch: the depth-`0` leaf `0`. -/
noncomputable def toyFamily :
    AcceptedBatchFamily toyUrs 0 (evalVector 0 0) 0 (fun _ : Fin 1 => (0 : Fp))
      (fun _ => 0) where
  batchChallenge := fun _ => 0
  challengesDistinct := fun r s _ => Subsingleton.elim r s
  trees := fun _ => .leaf 0
  accepts := fun r => ⟨by simp [commitGen], by simp [commitGen]⟩
  current := 0
  current_P := by simp
  current_v := by simp

/-- The opening-or-relation terminal endpoint discharged end-to-end, with `hbatch` *derived* from
accepting transcripts (`multiopenRewindForRelation_of_acceptedFamily toyFamily`), not assumed. -/
theorem toy_terminal_discharged :
    True ∨ HasNontrivialRelation (F := Fp) toyUrs.g toyUrs.u toyUrs.w :=
  decoded_constraint_of_opening_or_relation (urs := toyUrs)
    (fun _ : Fin 1 => (0 : Fp)) (fun _ => 0) (fun i : Fin 1 => i) (fun i : Fin 1 => i)
    (fun _ => 0) 0 toyGates 0 1 0
    (Or.inl ⟨fun _ => 0, toy_opens⟩)
    (multiopenRewindForRelation_of_acceptedFamily toyFamily)
    (fun a hrel => by rw [toy_numerator]; simp [quotientCheck])
    (fun a hrel => by rw [toy_numerator]; intro h; simp at h)
    (fun _ _ _ => trivial)

end MultiopenDecodeFixture
end Zcash.Snark
