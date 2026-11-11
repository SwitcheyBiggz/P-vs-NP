/-
  Cross-reduction corollaries for the benchmark CNFs.

  These are finite facts about one 3-variable gadget and the subset-sum slack
  identity. A single finite CNF is not an NP-complete language. Nothing in this
  file is a proof that P = NP.
-/
import Benchmarks

namespace Benchmarks

/-- First clause of `cook_levin_gadget_3v`: positive literals on variables 1, 2, and 3. -/
def cookLevinFirstClause : Clause :=
  [mkLit 1 false, mkLit 2 false, mkLit 3 false]

theorem cook_levin_gadget_3v_first_clause :
    cook_levin_gadget_3v = cookLevinFirstClause ::
      [[mkLit 1 true, mkLit 2 true, mkLit 3 false],
       [mkLit 1 false, mkLit 2 true, mkLit 3 true],
       [mkLit 1 true, mkLit 2 false, mkLit 3 false]] := rfl

/-- Mask 7 is all-true on variables 1, 2, and 3, so every literal of the first clause
evaluates to true. -/
theorem cook_levin_first_clause_literal_true
    (l : Literal) (hl : l ∈ cookLevinFirstClause) :
    evalLiteral (assignOfMask 7) l = true := by
  simp only [cookLevinFirstClause, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · decide
  · decide
  · decide

/-- Every pair of literals from the first clause of `cook_levin_gadget_3v` is true
under `assignOfMask 7` and therefore `compatibleLiterals`, by `true_literals_compatible`. -/
theorem cook_levin_first_clause_true_pairs_compatible
    (l₁ l₂ : Literal)
    (h₁ : l₁ ∈ cookLevinFirstClause)
    (h₂ : l₂ ∈ cookLevinFirstClause) :
    evalLiteral (assignOfMask 7) l₁ = true ∧
    evalLiteral (assignOfMask 7) l₂ = true ∧
    compatibleLiterals l₁ l₂ = true := by
  have t₁ := cook_levin_first_clause_literal_true l₁ h₁
  have t₂ := cook_levin_first_clause_literal_true l₂ h₂
  exact ⟨t₁, t₂, true_literals_compatible (assignOfMask 7) l₁ l₂ t₁ t₂⟩

/-- The three concrete pairs of true literals in that clause. -/
theorem cook_levin_first_clause_concrete_pairs :
    compatibleLiterals (mkLit 1 false) (mkLit 2 false) = true ∧
    compatibleLiterals (mkLit 1 false) (mkLit 3 false) = true ∧
    compatibleLiterals (mkLit 2 false) (mkLit 3 false) = true := by
  have h12 := cook_levin_first_clause_true_pairs_compatible
    (mkLit 1 false) (mkLit 2 false) (by decide) (by decide)
  have h13 := cook_levin_first_clause_true_pairs_compatible
    (mkLit 1 false) (mkLit 3 false) (by decide) (by decide)
  have h23 := cook_levin_first_clause_true_pairs_compatible
    (mkLit 2 false) (mkLit 3 false) (by decide) (by decide)
  exact ⟨h12.2.2, h13.2.2, h23.2.2⟩

/-- Subset-sum slack reaches target 4 at `count = 1`, by `subset_sum_slack_iff`. -/
theorem subset_sum_slack_count_1 :
    ∃ b₁ b₂ : Bool, 1 + (if b₁ then 1 else 0) + (if b₂ then 2 else 0) = 4 :=
  (subset_sum_slack_iff 1 (by decide)).mpr (by decide)

/-- Subset-sum slack reaches target 4 at `count = 2`, by `subset_sum_slack_iff`. -/
theorem subset_sum_slack_count_2 :
    ∃ b₁ b₂ : Bool, 2 + (if b₁ then 1 else 0) + (if b₂ then 2 else 0) = 4 :=
  (subset_sum_slack_iff 2 (by decide)).mpr (by decide)

/-- Subset-sum slack reaches target 4 at `count = 3`, by `subset_sum_slack_iff`. -/
theorem subset_sum_slack_count_3 :
    ∃ b₁ b₂ : Bool, 3 + (if b₁ then 1 else 0) + (if b₂ then 2 else 0) = 4 :=
  (subset_sum_slack_iff 3 (by decide)).mpr (by decide)

/-- At `count = 0` the slack bits cannot reach target 4, by `subset_sum_slack_iff`. -/
theorem subset_sum_slack_count_0 :
    ¬ ∃ b₁ b₂ : Bool, 0 + (if b₁ then 1 else 0) + (if b₂ then 2 else 0) = 4 := by
  intro h
  have hle : 1 ≤ (0 : ℕ) := (subset_sum_slack_iff 0 (by decide)).mp h
  exact absurd hle (by decide)

/-- Satisfying the finite gadget `cook_levin_gadget_3v` under mask 7 is one CNF
evaluation. It does not yield `True` as a stand-in for P = NP, and this theorem
does not assert P = NP. A single finite CNF is not an NP-complete language. -/
theorem cross_reduce_not_p_eq_np :
    evalCNF cook_levin_gadget_3v (assignOfMask 7) = true := by
  decide

end Benchmarks
