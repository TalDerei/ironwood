import Mathlib
import Zcash.Snark.CommitFold
import Zcash.Snark.Consistency

/-!
# IPA knowledge soundness: the commitment-soundness of one round (3-special)

This begins the genuine inner-product-argument knowledge-soundness proof — deriving the *opening relation*
`commit g a = P` from the verifier's accept, rather than assuming it.

The key fact (worked out by hand, then here): one IPA round is **3-special-sound** for the *commitment*. At
a round the verifier folds `g' = g_lo + u⁻¹·g_hi` and `P' = P + u⁻¹·L + u·R` (the prover's cross-terms
`L`,`R` fixed before the challenge). Given three sub-openings at three distinct challenges,
`commit g' cᵢ = P + uᵢ⁻¹·L + uᵢ·R`, the parent commitment is pinned: `commit g a = P` for an `a` assembled
from the `cᵢ` by the Vandermonde combination that extracts the *linear-in-u* coefficient. Two challenges
suffice to extract the witness but leave `commit g a − P = (u₁+u₂)·X` undetermined — three kill it.

Notably this round step needs **no binding** — it is pure module linear algebra. (Binding enters only for
*uniqueness* of the opening.)

* `vandermonde3` — three distinct points admit coefficients `lᵢ` with `Σ lᵢ uᵢᵏ = δ_{k,1}` (`k=0,1,2`):
  the functional extracting the linear coefficient of a degree-≤2 polynomial from its three samples.
* `ipa_round_commit_sound` — from three sub-openings `commit (g_lo + uᵢ⁻¹·g_hi) cᵢ = P + uᵢ⁻¹·L + uᵢ·R` at
  distinct nonzero challenges, the parent commitment `P` is the commitment of `a = (Σ lᵢuᵢ·cᵢ ‖ Σ lᵢ·cᵢ)`:
  `commit g_lo a_lo + commit g_hi a_hi = P`. Pure module linear algebra (the `vandermonde3` combination),
  no binding.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- **Three-point linear-coefficient functional.** For distinct `u₁,u₂,u₃` there are coefficients
`l₁,l₂,l₃` with `Σ lᵢ = 0`, `Σ lᵢuᵢ = 1`, `Σ lᵢuᵢ² = 0` — i.e. `p ↦ Σ lᵢ·p(uᵢ)` reads off the
coefficient of `u` from any degree-≤2 `p`. (The `lᵢ` are the `u`-coefficients of the Lagrange basis.) -/
theorem vandermonde3 (u₁ u₂ u₃ : F) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) :
    ∃ l₁ l₂ l₃ : F, (l₁ + l₂ + l₃ = 0) ∧ (l₁ * u₁ + l₂ * u₂ + l₃ * u₃ = 1)
      ∧ (l₁ * u₁ ^ 2 + l₂ * u₂ ^ 2 + l₃ * u₃ ^ 2 = 0) := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)), -(u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)),
    -(u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **The IPA round is 3-special-sound for the commitment.** Three sub-openings of the folded commitment
`P' = P + uᵢ⁻¹·L + uᵢ·R` against the folded generators `g_lo + uᵢ⁻¹·g_hi`, at three distinct nonzero
challenges, pin the *parent* opening: the witness `a = (Σ lᵢuᵢ·cᵢ ‖ Σ lᵢ·cᵢ)` (assembled by the
`vandermonde3` linear-coefficient combination) opens `P`, i.e. `commit g_lo a_lo + commit g_hi a_hi = P`.

The proof multiplies each opening by `uᵢ` to clear the inverse (`uᵢ·A_i + B_i = uᵢ·P + L + uᵢ²·R`), then
combines by `lᵢ`: the `P`-coefficient becomes `Σ lᵢuᵢ = 1`, while `L` (`Σ lᵢ = 0`) and `R`
(`Σ lᵢuᵢ² = 0`) cancel, and the `cᵢ`-terms cancel pairwise. No binding is used — this is the linear
algebra that two challenges cannot do (they leave `commit g a − P = (u₁+u₂)·X` undetermined). -/
theorem ipa_round_commit_sound {m : ℕ} (g_lo g_hi : Fin m → G) (P L R : G)
    (c₁ c₂ c₃ : Fin m → F) (u₁ u₂ u₃ : F)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (e₁ : commitGen (g_lo + u₁⁻¹ • g_hi) c₁ = P + u₁⁻¹ • L + u₁ • R)
    (e₂ : commitGen (g_lo + u₂⁻¹ • g_hi) c₂ = P + u₂⁻¹ • L + u₂ • R)
    (e₃ : commitGen (g_lo + u₃⁻¹ • g_hi) c₃ = P + u₃⁻¹ • L + u₃ • R) :
    ∃ a_lo a_hi : Fin m → F, commitGen g_lo a_lo + commitGen g_hi a_hi = P := by
  obtain ⟨l₁, l₂, l₃, hl0, hl1, hl2⟩ := vandermonde3 u₁ u₂ u₃ h12 h13 h23
  rw [commitGen_add_gen, commitGen_smul_gen] at e₁ e₂ e₃
  have s₁ : u₁ • commitGen g_lo c₁ + commitGen g_hi c₁ = u₁ • P + L + (u₁ * u₁) • R := by
    have h := congrArg (u₁ • ·) e₁
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₁, one_smul] at h; exact h
  have s₂ : u₂ • commitGen g_lo c₂ + commitGen g_hi c₂ = u₂ • P + L + (u₂ * u₂) • R := by
    have h := congrArg (u₂ • ·) e₂
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₂, one_smul] at h; exact h
  have s₃ : u₃ • commitGen g_lo c₃ + commitGen g_hi c₃ = u₃ • P + L + (u₃ * u₃) • R := by
    have h := congrArg (u₃ • ·) e₃
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hu₃, one_smul] at h; exact h
  have hB₁ : commitGen g_hi c₁ = u₁ • P + L + (u₁ * u₁) • R - u₁ • commitGen g_lo c₁ := by
    rw [← s₁]; abel
  have hB₂ : commitGen g_hi c₂ = u₂ • P + L + (u₂ * u₂) • R - u₂ • commitGen g_lo c₂ := by
    rw [← s₂]; abel
  have hB₃ : commitGen g_hi c₃ = u₃ • P + L + (u₃ * u₃) • R - u₃ • commitGen g_lo c₃ := by
    rw [← s₃]; abel
  refine ⟨l₁ • (u₁ • c₁) + l₂ • (u₂ • c₂) + l₃ • (u₃ • c₃), l₁ • c₁ + l₂ • c₂ + l₃ • c₃, ?_⟩
  simp only [commitGen_add_left, commitGen_smul_left, hB₁, hB₂, hB₃]
  match_scalars <;>
    first
      | linear_combination hl1
      | linear_combination hl0
      | linear_combination hl2
      | ring

/-- A length-`2^{k+1}` commitment splits over the two halves:
`commit g a = commit (loHalf g) (loHalf a) + commit (hiHalf g) (hiHalf a)`. The IPA recursion's bridge from
a round's folded-generator openings back to the parent generators. -/
theorem commitGen_split {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a : Fin (2 ^ (k + 1)) → F) :
    commitGen g a = commitGen (loHalf g) (loHalf a) + commitGen (hiHalf g) (hiHalf a) := by
  have e : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  let φ : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) := finSumFinEquiv.trans (finCongr e)
  simp only [commitGen]
  rw [← φ.sum_comp (fun j => a j • g j), Fintype.sum_sum_type]
  congr 1

/-- The lower half of an `append` is the lower part. -/
theorem loHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : loHalf (append lo hi) = lo := by
  funext i; simp only [loHalf, append, dif_pos i.isLt]

/-- The upper half of an `append` is the upper part. -/
theorem hiHalf_append {α : Type*} {k : ℕ} (lo hi : Fin (2 ^ k) → α) : hiHalf (append lo hi) = hi := by
  funext i
  have h : ¬ (2 ^ k + i.val < 2 ^ k) := by omega
  simp only [hiHalf, append, dif_neg h]
  congr 1; apply Fin.ext; simp

/-- A commitment of an `append` splits over the parent halves:
`commit g (append a_lo a_hi) = commit (loHalf g) a_lo + commit (hiHalf g) a_hi`. -/
theorem commitGen_append {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (a_lo a_hi : Fin (2 ^ k) → F) :
    commitGen g (append a_lo a_hi) = commitGen (loHalf g) a_lo + commitGen (hiHalf g) a_hi := by
  rw [commitGen_split, loHalf_append, hiHalf_append]

/-! ## The IPA soundness recursion -/

/-- A **3-ary IPA transcript tree** for `d` rounds. At each round the prover's two cross-commitments
`L`, `R` (fixed before the challenge) and three sub-transcripts answering three challenges; at a leaf the
final scalar. The 3-arity is exactly what `ipa_round_commit_sound` consumes (two challenges extract the
witness, the third pins the commitment). -/
inductive IpaTree (F G : Type*) : ℕ → Type _ where
  | leaf : F → IpaTree F G 0
  | node {d : ℕ} : G → G → F → F → F →
      IpaTree F G d → IpaTree F G d → IpaTree F G d → IpaTree F G (d + 1)

/-- The IPA verifier **accepts** a transcript tree against generators `g` and commitment `P`: at a leaf,
the final check `P = [c]·g₀` (`= commit g (const c)`); at a node, the three challenges are distinct and
nonzero and each sub-transcript opens the verifier's folded commitment `P + uᵢ⁻¹·L + uᵢ·R` against the
folded generators `foldGens g uᵢ`. This is the verifier's actual recursion (external `P`, prover `L`/`R`),
the object the soundness peels back. -/
def IpaAccept : {d : ℕ} → (Fin (2 ^ d) → G) → G → IpaTree F G d → Prop
  | 0, g, P, .leaf c => P = commitGen g (fun _ => c)
  | _ + 1, g, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        IpaAccept (foldGens g u₁) (P + u₁⁻¹ • L + u₁ • R) t₁ ∧
        IpaAccept (foldGens g u₂) (P + u₂⁻¹ • L + u₂ • R) t₂ ∧
        IpaAccept (foldGens g u₃) (P + u₃⁻¹ • L + u₃ • R) t₃

/-- **IPA knowledge soundness — the opening, derived (not assumed).** An accepting transcript tree yields a
witness opening the commitment: `∃ a, commit g a = P`. By induction on the tree: the leaf gives `a = const c`
directly; a node takes the three sub-witnesses from the IH, pins the parent commitment with
`ipa_round_commit_sound`, and reassembles via `commitGen_append`. The whole argument uses **no binding** —
3-special soundness alone pins the opening. (Binding/DLR enters only for *uniqueness*, `ipaRelation_unique`.) -/
theorem ipa_sound : {d : ℕ} → (g : Fin (2 ^ d) → G) → (P : G) → (t : IpaTree F G d) →
    IpaAccept g P t → ∃ a : Fin (2 ^ d) → F, commitGen g a = P
  | 0, g, P, .leaf c, h => ⟨fun _ => c, h.symm⟩
  | _ + 1, g, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      obtain ⟨c₁, hc₁⟩ := ipa_sound (foldGens g u₁) _ t₁ ha₁
      obtain ⟨c₂, hc₂⟩ := ipa_sound (foldGens g u₂) _ t₂ ha₂
      obtain ⟨c₃, hc₃⟩ := ipa_sound (foldGens g u₃) _ t₃ ha₃
      obtain ⟨a_lo, a_hi, hP⟩ := ipa_round_commit_sound (loHalf g) (hiHalf g) P L R c₁ c₂ c₃
        u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ hc₁ hc₂ hc₃
      exact ⟨append a_lo a_hi, by rw [commitGen_append]; exact hP⟩

end Zcash.Snark
