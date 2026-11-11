/-
  PvnpReal.BruteBits — pure lemmas for brute-force SAT search (binary enumeration of
  witnesses) and a small OR machine.
-/
import PvnpReal.Classes

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

/-! ### Binary enumeration of witnesses -/

/-- Little-endian binary digits of `n` (no trailing zeros). -/
def binL : ℕ → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: binL ((n + 1) / 2)
decreasing_by omega

theorem binL_zero : binL 0 = [] := by rw [binL]

theorem binL_pos {n : ℕ} (hn : 0 < n) : binL n = (n % 2 == 1) :: binL (n / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [binL]

/-- Little-endian value of a bit list. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * bval w

theorem bval_lt (w : List Bool) : bval w < 2 ^ w.length := by
  induction w with
  | nil => simp [bval]
  | cons b w ih => simp only [bval, List.length_cons, Nat.pow_succ]; split <;> omega

theorem asg_nil (v : ℕ) : asg [] v = false := rfl
theorem asg_cons_zero (b : Bool) (w : List Bool) : asg (b :: w) 0 = b := rfl
theorem asg_cons_succ (b : Bool) (w : List Bool) (v : ℕ) : asg (b :: w) (v + 1) = asg w v := rfl

theorem asg_binL_bval (w : List Bool) : asg (binL (bval w)) = asg w := by
  induction w with
  | nil => simp [bval, binL_zero]
  | cons b w ih =>
    funext v
    by_cases h0 : bval (b :: w) = 0
    · have hb : b = false := by cases b <;> simp_all [bval]
      have hw : bval w = 0 := by subst hb; simp [bval] at h0; exact h0
      rw [h0, binL_zero]
      rcases v with _ | v
      · simp [asg, hb]
      · rw [asg_cons_succ, ← ih, hw, binL_zero]; rfl
    · rw [binL_pos (by omega)]
      have e1 : (bval (b :: w) % 2 == 1) = b := by cases b <;> simp [bval] <;> omega
      have e2 : bval (b :: w) / 2 = bval w := by cases b <;> simp [bval] <;> omega
      rw [e1, e2]
      rcases v with _ | v
      · rfl
      · rw [asg_cons_succ, asg_cons_succ, ih]

theorem run_congr {w w' : List Bool} (h : asg w = asg w') :
    ∀ (r : List Bool) (m : Mode) (fok cok ng : Bool) (c : ℕ),
      run w m fok cok ng c r = run w' m fok cok ng c r := by
  intro r
  induction r with
  | nil => intro m fok cok ng c; cases m <;> rfl
  | cons b r ih =>
    intro m fok cok ng c
    cases m <;> cases b <;> simp only [run, ih, h]

theorem verify_congr (x : List Bool) {w w' : List Bool} (h : asg w = asg w') :
    verify x w = verify x w' := run_congr h x _ _ _ _ _

/-- **SAT by brute force over `2^|x|` binary witnesses.** -/
theorem SATLang_iff_exists_bin (x : List Bool) :
    SATLang x ↔ ∃ i < 2 ^ x.length, verify x (binL i) = true := by
  constructor
  · intro hx
    obtain ⟨w, hw, hv⟩ := (SATLang_iff_verify x).1 hx
    refine ⟨bval w, lt_of_lt_of_le (bval_lt w) (Nat.pow_le_pow_right (by norm_num) hw), ?_⟩
    rw [verify_congr x (asg_binL_bval w)]; exact hv
  · rintro ⟨i, -, hv⟩
    obtain ⟨φ, hφe, hφ⟩ := verify_sound _ _ hv
    rw [hφe]
    exact (SATLang_encode_iff φ).2 ⟨asg _, hφ⟩

/-! ### OR of a bit list -/

namespace SmallTM

open TM2.Stmt

def orStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o)
      (branch isS (branch isT (goto fun _ => .l2) (goto fun _ => .l1))
        (push UK.out (fun _ => false) halt))
  | .l2 => pop UK.inp (fun _ o => o)
      (branch isS (goto fun _ => .l2) (push UK.out (fun _ => true) halt))

def orF (y : List Bool) : List Bool := [y.contains true]

theorem or_l2 (l : List Bool) (v : Option Bool) :
    (flip bind (TM2.step orStmt))^[l.length + 1] (some ⟨some .l2, v, st l []⟩) =
      some ⟨none, none, st [] [true]⟩ := by
  induction l generalizing v with
  | nil => simp [TM2.step, orStmt, TM2.stepAux, isS, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step orStmt) (some ⟨some .l2, v, st (b :: l) []⟩) =
        some ⟨some .l2, some b, st l []⟩ := by
      simp [TM2.step, orStmt, TM2.stepAux, isS, flip]
    rw [e, ih]

theorem or_l1 (l : List Bool) (v : Option Bool) :
    ∃ n ≤ l.length + 1, (flip bind (TM2.step orStmt))^[n] (some ⟨some .l1, v, st l []⟩) =
      some ⟨none, none, st [] (orF l)⟩ := by
  induction l generalizing v with
  | nil => exact ⟨1, le_rfl, by simp [TM2.step, orStmt, TM2.stepAux, isS, flip, orF]⟩
  | cons b l ih =>
    cases b
    · obtain ⟨n, hn, h⟩ := ih (some false)
      refine ⟨n + 1, by simp; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step orStmt) (some ⟨some .l1, v, st (false :: l) []⟩) =
          some ⟨some .l1, some false, st l []⟩ := by
        simp [TM2.step, orStmt, TM2.stepAux, isS, isT, flip]
      rw [e, h]; simp [orF]
    · refine ⟨l.length + 1 + 1, by simp, ?_⟩
      rw [Function.iterate_succ_apply]
      have e : flip bind (TM2.step orStmt) (some ⟨some .l1, v, st (true :: l) []⟩) =
          some ⟨some .l2, some true, st l []⟩ := by
        simp [TM2.step, orStmt, TM2.stepAux, isS, isT, flip]
      rw [e, or_l2]; simp [orF]

end SmallTM

noncomputable def orComputable : TM2ComputableInPolyTime strEnc strEnc SmallTM.orF where
  tm := SmallTM.mk SmallTM.orStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun y :=
    { steps := Classical.choose (SmallTM.or_l1 y none)
      evals_in_steps := by
        erw [List.map_id, List.map_id, SmallTM.initList_eq, Option.map_some,
          SmallTM.haltList_eq]
        exact (Classical.choose_spec (SmallTM.or_l1 y none)).2
      steps_le_m := by
        have := (Classical.choose_spec (SmallTM.or_l1 y none)).1
        simpa [strEnc] using this }

end PvnpReal
