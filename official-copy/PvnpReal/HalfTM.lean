/-
  PvnpReal.HalfTM — unary to binary: `1ⁿ0y ↦ binL n` (little-endian) in polynomial time,
  by repeated halving.
-/
import PvnpReal.BruteBits

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

namespace HalfTM

open TM2.Stmt

inductive HK | inp | A | B | out
  deriving DecidableEq

instance : Fintype HK := ⟨{.inp, .A, .B, .out}, fun k => by cases k <;> simp⟩

inductive HL | c | clr | h0 | h1 | h2 | mv
  deriving DecidableEq

instance : Fintype HL := ⟨{.c, .clr, .h0, .h1, .h2, .mv}, fun k => by cases k <;> simp⟩

abbrev Γ : HK → Type := fun _ => Bool
abbrev St := TM2.Stmt Γ HL (Option Bool)
abbrev Cfg := TM2.Cfg Γ HL (Option Bool)

def st (i a b o : List Bool) : ∀ k : HK, List (Γ k)
  | .inp => i
  | .A => a
  | .B => b
  | .out => o

@[simp] theorem st_inp (i a b o) : st i a b o .inp = i := rfl
@[simp] theorem st_A (i a b o) : st i a b o .A = a := rfl
@[simp] theorem st_B (i a b o) : st i a b o .B = b := rfl
@[simp] theorem st_out (i a b o) : st i a b o .out = o := rfl

@[simp] theorem upd_inp (i a b o x) : Function.update (st i a b o) .inp x = st x a b o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_A (i a b o x) : Function.update (st i a b o) .A x = st i x b o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_B (i a b o x) : Function.update (st i a b o) .B x = st i a x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i a b o x) : Function.update (st i a b o) .out x = st i a b x := by
  funext k; cases k <;> rfl

def isS : Option Bool → Bool := fun o => o.isSome
def isT : Option Bool → Bool
  | some true => true
  | _ => false

def stmt : HL → St
  | .c => pop .inp (fun _ o => o)
      (branch isT (push .A (fun _ => true) (goto fun _ => .c)) (goto fun _ => .clr))
  | .clr => pop .inp (fun _ o => o) (branch isS (goto fun _ => .clr) (goto fun _ => .h0))
  | .h0 => pop .A (fun _ o => o) (branch isS (goto fun _ => .h1) halt)
  | .h1 => pop .A (fun _ o => o) (branch isS (push .B (fun _ => true) (goto fun _ => .h2))
      (push .out (fun _ => true) (goto fun _ => .mv)))
  | .h2 => pop .A (fun _ o => o) (branch isS (goto fun _ => .h1)
      (push .out (fun _ => false) (goto fun _ => .mv)))
  | .mv => pop .B (fun _ o => o) (branch isS (push .A (fun _ => true) (goto fun _ => .mv))
      (goto fun _ => .h0))

def tm : FinTM2 where
  K := HK
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := HL
  main := .c
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt

local notation "F" => flip bind (TM2.step stmt)

abbrev ones (n : ℕ) : List Bool := List.replicate n true

theorem run_c (l : List Bool) (v : Option Bool) (a : ℕ) :
    ∃ v', F^[lpN l + 1] (some ⟨some .c, v, st l (ones a) [] []⟩) =
      some ⟨some .clr, v', st (lpX l) (ones (a + lpN l)) [] []⟩ := by
  induction l generalizing v a with
  | nil => exact ⟨none, by simp [TM2.step, stmt, TM2.stepAux, isT, flip, lpN, lpX]⟩
  | cons b l ih =>
    cases b
    · exact ⟨some false, by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, LoopTM.lpN_cons_false,
          LoopTM.lpX_cons_false]⟩
    · obtain ⟨v', h⟩ := ih (some true) (a + 1)
      refine ⟨v', ?_⟩
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply]
      have e : F (some ⟨some .c, v, st (true :: l) (ones a) [] []⟩) =
          some ⟨some .c, some true, st l (ones (a + 1)) [] []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, List.replicate_succ]
      rw [e, h, show a + 1 + lpN l = a + (lpN l + 1) by omega]

theorem run_clr (l : List Bool) (v : Option Bool) (a : List Bool) :
    F^[l.length + 1] (some ⟨some .clr, v, st l a [] []⟩) =
      some ⟨some .h0, none, st [] a [] []⟩ := by
  induction l generalizing v with
  | nil => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .clr, v, st (b :: l) a [] []⟩) = some ⟨some .clr, some b, st l a [] []⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip]
    rw [e, ih]

theorem run_pair (k : ℕ) : ∀ (v : Option Bool) (b : ℕ) (o : List Bool),
    F^[k + 1] (some ⟨some .h1, v, st [] (ones k) (ones b) o⟩) =
      some ⟨some .mv, none, st [] [] (ones (b + (k + 1) / 2)) ((k % 2 == 0) :: o)⟩ ∧
    F^[k + 1] (some ⟨some .h2, v, st [] (ones k) (ones b) o⟩) =
      some ⟨some .mv, none, st [] [] (ones (b + k / 2)) ((k % 2 == 1) :: o)⟩ := by
  induction k with
  | zero => intro v b o; constructor <;> simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | succ k ih =>
    intro v b o
    constructor
    · rw [Function.iterate_succ_apply]
      have e : F (some ⟨some .h1, v, st [] (ones (k + 1)) (ones b) o⟩) =
          some ⟨some .h2, some true, st [] (ones k) (ones (b + 1)) o⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
      rw [e, (ih _ _ _).2]
      have h1 : b + 1 + k / 2 = b + (k + 1 + 1) / 2 := by omega
      have h2 : (k % 2 == 1) = ((k + 1) % 2 == 0) := by
        rcases Nat.mod_two_eq_zero_or_one k with h | h
        · rw [h, show (k + 1) % 2 = 1 by omega]; rfl
        · rw [h, show (k + 1) % 2 = 0 by omega]; rfl
      rw [h1, h2]
    · rw [Function.iterate_succ_apply]
      have e : F (some ⟨some .h2, v, st [] (ones (k + 1)) (ones b) o⟩) =
          some ⟨some .h1, some true, st [] (ones k) (ones b) o⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
      rw [e, (ih _ _ _).1]
      have h2 : (k % 2 == 0) = ((k + 1) % 2 == 1) := by
        rcases Nat.mod_two_eq_zero_or_one k with h | h
        · rw [h, show (k + 1) % 2 = 1 by omega]; rfl
        · rw [h, show (k + 1) % 2 = 0 by omega]; rfl
      rw [h2]

theorem run_mv (b : ℕ) (v : Option Bool) (a : ℕ) (o : List Bool) :
    F^[b + 1] (some ⟨some .mv, v, st [] (ones a) (ones b) o⟩) =
      some ⟨some .h0, none, st [] (ones (a + b)) [] o⟩ := by
  induction b generalizing v a with
  | zero => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | succ b ih =>
    rw [Function.iterate_succ_apply]
    have e : F (some ⟨some .mv, v, st [] (ones a) (ones (b + 1)) o⟩) =
        some ⟨some .mv, some true, st [] (ones (a + 1)) (ones b) o⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    rw [e, ih, show a + 1 + b = a + (b + 1) by omega]

theorem run_h0 (n : ℕ) : ∀ (v : Option Bool) (o : List Bool),
    ∃ s ≤ 6 * n + 5, F^[s] (some ⟨some .h0, v, st [] (ones n) [] o⟩) =
      some ⟨none, none, st [] [] [] ((binL n).reverse ++ o)⟩ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v o
    rcases n with _ | k
    · exact ⟨1, by omega, by simp [TM2.step, stmt, TM2.stepAux, isS, flip, binL_zero]⟩
    · -- one pop, then pairing, then move back
      have e0 : F (some ⟨some .h0, v, st [] (ones (k + 1)) [] o⟩) =
          some ⟨some .h1, some true, st [] (ones k) [] o⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
      have hP := (run_pair k (some true) 0 o).1
      have hM := run_mv ((k + 1) / 2) none 0 ((k % 2 == 0) :: o)
      obtain ⟨s, hs, hR⟩ := ih ((k + 1) / 2) (by omega) none ((k % 2 == 0) :: o)
      refine ⟨s + (((k + 1) / 2 + 1) + ((k + 1) + 1)), by omega, ?_⟩
      have h1 : F^[1] (some ⟨some .h0, v, st [] (ones (k + 1)) [] o⟩) =
          some ⟨some .h1, some true, st [] (ones k) [] o⟩ := e0
      have hP' : F^[k + 1] (some ⟨some .h1, some true, st [] (ones k) [] o⟩) = _ := hP
      simp only [Nat.zero_add] at hP' hM
      have := iter_chain (iter_chain (iter_chain h1 hP') hM) hR
      rw [this, binL_pos (by omega : 0 < k + 1)]
      have hb : ((k + 1) % 2 == 1) = (k % 2 == 0) := by
        rcases Nat.mod_two_eq_zero_or_one k with h | h
        · rw [h, show (k + 1) % 2 = 1 by omega]; rfl
        · rw [h, show (k + 1) % 2 = 0 by omega]; rfl
      simp [hb]

end HalfTM

/-- `1ⁿ0y ↦ binL n`, before reversal. -/
def halfF (z : List Bool) : List Bool := (binL (lpN z)).reverse

noncomputable def halfComputable : TM2ComputableInPolyTime strEnc strEnc halfF where
  tm := HalfTM.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 8 * Polynomial.X + 7
  outputsFun z :=
    have hex : ∃ s ≤ 8 * z.length + 7,
        (flip bind (TM2.step HalfTM.stmt))^[s] (some ⟨some .c, none, HalfTM.st z [] [] []⟩) =
          some ⟨none, none, HalfTM.st [] [] [] (halfF z)⟩ := by
      obtain ⟨v1, h1⟩ := HalfTM.run_c z none 0
      have h2 := HalfTM.run_clr (lpX z) v1 (HalfTM.ones (lpN z))
      obtain ⟨s, hs, h3⟩ := HalfTM.run_h0 (lpN z) none []
      simp only [Nat.zero_add] at h1
      have := iter_chain (iter_chain h1 h2) h3
      have hl := LoopTM.lp_len z
      refine ⟨_, ?_, this.trans (by simp [halfF])⟩
      omega
    { steps := Classical.choose hex
      evals_in_steps := by
        have := (Classical.choose_spec hex).2
        have ei : initList HalfTM.tm (z : List Bool) =
            (⟨some .c, none, HalfTM.st z [] [] []⟩ : HalfTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList HalfTM.tm (halfF z : List Bool) =
            (⟨none, none, HalfTM.st [] [] [] (halfF z)⟩ : HalfTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact this
      steps_le_m := by
        have := (Classical.choose_spec hex).1
        simpa [strEnc] using this }

/-- `1ⁿ0y ↦ binL n` is polynomial-time. -/
theorem PS.binL : PS (fun z => binL (lpN z)) :=
  (PS.comp ⟨halfComputable⟩ ⟨SmallTM.revComputable⟩).congr (fun z => by simp [halfF])

end PvnpReal
