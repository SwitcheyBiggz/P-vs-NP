/-
  PvnpReal.Hierarchy — the diagonal/padding argument of the time hierarchy theorem, giving
  P ≠ EXP **conditionally** on a universal clocked interpreter.

  `P_ne_EXP_of_universal`: if an interpreter `U` (code, input, clock) ↦ answer
  (1) reproduces every polytime decider on infinitely many self-codes once the clock passes a
      polynomial, and
  (2) its exponentially-clocked diagonal language is in EXP,
  then P ≠ EXP. Neither hypothesis is discharged in this file.
-/
import PvnpReal.Clock
import Mathlib.Analysis.SpecificLimits.Normed

namespace PvnpReal

open Turing Computability Filter Topology

/-- `P ≠ EXP`, stated as: some language is in EXP but not in P. -/
def P_ne_EXP : Prop := ∃ L : Language, InEXP L ∧ ¬ InP L

/-- Every polynomial is eventually below `2ⁿ`. -/
theorem poly_le_two_pow_eventually (p : Polynomial ℕ) : ∃ n0, ∀ n ≥ n0, p.eval n ≤ 2 ^ n := by
  -- step 1: `p.eval n ≤ A * n^k` for `n ≥ 1`
  have hA : ∃ A k : ℕ, ∀ n ≥ 1, p.eval n ≤ A * n ^ k := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨A, k, h⟩ := hp
      obtain ⟨B, l, g⟩ := hq
      refine ⟨A + B, k + l, fun n hn => ?_⟩
      have e1 : n ^ k ≤ n ^ (k + l) := Nat.pow_le_pow_right hn (by omega)
      have e2 : n ^ l ≤ n ^ (k + l) := Nat.pow_le_pow_right hn (by omega)
      have := h n hn
      have := g n hn
      simp only [Polynomial.eval_add, Nat.add_mul]
      have : A * n ^ k ≤ A * n ^ (k + l) := Nat.mul_le_mul_left _ e1
      have : B * n ^ l ≤ B * n ^ (k + l) := Nat.mul_le_mul_left _ e2
      omega
    | monomial j c => exact ⟨c, j, fun n _ => by simp⟩
  obtain ⟨A, k, hA⟩ := hA
  -- step 2: `(A+1) n^k < 2^n` eventually
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) (by norm_num)
  have hpos : (0 : ℝ) < 1 / ((A : ℝ) + 1) := by positivity
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max n0 1, fun n hn => ?_⟩
  have h1 := hn0 n (le_of_max_le_left hn)
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ h2] at h1
  have h3 : ((A : ℝ) + 1) * (n : ℝ) ^ k < 2 ^ n := by
    have hA1 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
    calc ((A : ℝ) + 1) * (n : ℝ) ^ k < ((A : ℝ) + 1) * (1 / ((A : ℝ) + 1) * 2 ^ n) :=
          mul_lt_mul_of_pos_left h1 hA1
      _ = 2 ^ n := by field_simp
  have h4 : (A + 1) * n ^ k < 2 ^ n := by exact_mod_cast h3
  have h5 := hA n (le_of_max_le_right hn)
  have : A * n ^ k ≤ (A + 1) * n ^ k := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The exponentially clocked diagonal language of an interpreter. -/
def diagLang (U : List Bool → List Bool → ℕ → Option Bool) : Language :=
  fun x => U x x (2 ^ x.length) ≠ some true

/-- `U` reproduces every polytime decider on arbitrarily long self-codes, once the clock is at
least a polynomial in the input length. -/
def Reproduces (U : List Bool → List Bool → ℕ → Option Bool) : Prop :=
  ∀ f : List Bool → Bool, Nonempty (TM2ComputableInPolyTime strEnc encodeBool f) →
    ∃ T0 : Polynomial ℕ, ∀ n0, ∃ x : List Bool, n0 ≤ x.length ∧
      ∀ t, T0.eval x.length ≤ t → U x x t = some (f x)

/-- **Diagonalization**: the diagonal language of a reproducing interpreter is not in P. -/
theorem diagLang_not_in_P {U : List Bool → List Bool → ℕ → Option Bool} (hU : Reproduces U) :
    ¬ InP (diagLang U) := by
  rintro ⟨f, hf, hL⟩
  obtain ⟨T0, hT0⟩ := hU f hf
  obtain ⟨n0, hn0⟩ := poly_le_two_pow_eventually T0
  obtain ⟨x, hx, hrun⟩ := hT0 n0
  have e := hrun (2 ^ x.length) (hn0 _ hx)
  have := hL x
  unfold diagLang at this
  rw [e] at this
  cases hfx : f x <;> simp [hfx] at this

/-- **P ≠ EXP, conditionally** on a universal clocked interpreter whose diagonal is in EXP. -/
theorem P_ne_EXP_of_universal {U : List Bool → List Bool → ℕ → Option Bool}
    (hU : Reproduces U) (hE : InEXP (diagLang U)) : P_ne_EXP :=
  ⟨diagLang U, hE, diagLang_not_in_P hU⟩

end PvnpReal
