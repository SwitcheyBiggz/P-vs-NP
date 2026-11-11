/-
  PvnpReal.PadTM — an exponential-time padding machine `x ↦ 1^{2^|x|} 0 x`.
-/
import PvnpReal.Decode

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

def padF (x : List Bool) : List Bool := List.replicate (2 ^ x.length) true ++ false :: x

namespace PadTM

open TM2.Stmt

inductive PK | inp | T | A | B | C | out
  deriving DecidableEq

instance : Fintype PK := ⟨{.inp, .T, .A, .B, .C, .out}, fun k => by cases k <;> simp⟩

inductive PL | l1 | l2 | l3 | l4 | l5 | l6
  deriving DecidableEq

instance : Fintype PL := ⟨{.l1, .l2, .l3, .l4, .l5, .l6}, fun k => by cases k <;> simp⟩

abbrev Γ : PK → Type := fun _ => Bool
abbrev St := TM2.Stmt Γ PL (Option Bool)
abbrev Cfg := TM2.Cfg Γ PL (Option Bool)

def st (i t a b c o : List Bool) : ∀ k : PK, List (Γ k)
  | .inp => i
  | .T => t
  | .A => a
  | .B => b
  | .C => c
  | .out => o

@[simp] theorem upd_inp (i t a b c o x) : Function.update (st i t a b c o) .inp x = st x t a b c o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_T (i t a b c o x) : Function.update (st i t a b c o) .T x = st i x a b c o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_A (i t a b c o x) : Function.update (st i t a b c o) .A x = st i t x b c o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_B (i t a b c o x) : Function.update (st i t a b c o) .B x = st i t a x c o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_C (i t a b c o x) : Function.update (st i t a b c o) .C x = st i t a b x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i t a b c o x) : Function.update (st i t a b c o) .out x = st i t a b c x := by
  funext k; cases k <;> rfl
@[simp] theorem st_inp (i t a b c o) : st i t a b c o .inp = i := rfl
@[simp] theorem st_T (i t a b c o) : st i t a b c o .T = t := rfl
@[simp] theorem st_A (i t a b c o) : st i t a b c o .A = a := rfl
@[simp] theorem st_B (i t a b c o) : st i t a b c o .B = b := rfl
@[simp] theorem st_C (i t a b c o) : st i t a b c o .C = c := rfl
@[simp] theorem st_out (i t a b c o) : st i t a b c o .out = o := rfl

def isS : Option Bool → Bool := fun o => o.isSome

def stmt : PL → St
  | .l1 => pop .inp (fun _ o => o) (branch isS (push .T (fun s => s.getD false) (goto fun _ => .l1))
      (goto fun _ => .l2))
  | .l2 => pop .T (fun _ o => o) (branch isS
      (push .out (fun s => s.getD false) (push .A (fun _ => true) (goto fun _ => .l2)))
      (push .out (fun _ => false) (push .B (fun _ => true) (goto fun _ => .l3))))
  | .l3 => pop .A (fun _ o => o) (branch isS (goto fun _ => .l4) (goto fun _ => .l6))
  | .l4 => pop .B (fun _ o => o) (branch isS
      (push .C (fun _ => true) (push .C (fun _ => true) (goto fun _ => .l4))) (goto fun _ => .l5))
  | .l5 => pop .C (fun _ o => o) (branch isS (push .B (fun _ => true) (goto fun _ => .l5))
      (goto fun _ => .l3))
  | .l6 => pop .B (fun _ o => o) (branch isS (push .out (fun _ => true) (goto fun _ => .l6)) halt)

def tm : FinTM2 where
  K := PK
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := PL
  main := .l1
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt

local notation "F" => flip bind (TM2.step stmt)

abbrev ones (n : ℕ) : List Bool := List.replicate n true

theorem run_l1 (x t : List Bool) (v : Option Bool) :
    F^[x.length + 1] (some ⟨some .l1, v, st x t [] [] [] []⟩) =
      some ⟨some .l2, none, st [] (x.reverse ++ t) [] [] [] []⟩ := by
  induction x generalizing v t with
  | nil => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | cons b x ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .l1, v, st (b :: x) t [] [] [] []⟩) =
        some ⟨some .l1, some b, st x (b :: t) [] [] [] []⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip]
    rw [e, ih]; simp

theorem run_l2 (t o : List Bool) (a : ℕ) (v : Option Bool) :
    F^[t.length + 1] (some ⟨some .l2, v, st [] t (ones a) [] [] o⟩) =
      some ⟨some .l3, none, st [] [] (ones (a + t.length)) [true] [] (false :: (t.reverse ++ o))⟩ := by
  induction t generalizing v o a with
  | nil => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | cons b t ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .l2, v, st [] (b :: t) (ones a) [] [] o⟩) =
        some ⟨some .l2, some b, st [] t (ones (a + 1)) [] [] (b :: o)⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    rw [e, ih]; simp [show a + 1 + t.length = a + (t.length + 1) by omega]

theorem run_l4 (m : ℕ) (c : ℕ) (a o : List Bool) (v : Option Bool) :
    F^[m + 1] (some ⟨some .l4, v, st [] [] a (ones m) (ones c) o⟩) =
      some ⟨some .l5, none, st [] [] a [] (ones (c + 2 * m)) o⟩ := by
  induction m generalizing v c with
  | zero => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have e : F (some ⟨some .l4, v, st [] [] a (ones (m + 1)) (ones c) o⟩) =
        some ⟨some .l4, some true, st [] [] a (ones m) (ones (c + 2)) o⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    rw [e, ih, show c + 2 + 2 * m = c + 2 * (m + 1) by omega]

theorem run_l5 (m : ℕ) (b : ℕ) (a o : List Bool) (v : Option Bool) :
    F^[m + 1] (some ⟨some .l5, v, st [] [] a (ones b) (ones m) o⟩) =
      some ⟨some .l3, none, st [] [] a (ones (b + m)) [] o⟩ := by
  induction m generalizing v b with
  | zero => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have e : F (some ⟨some .l5, v, st [] [] a (ones b) (ones (m + 1)) o⟩) =
        some ⟨some .l5, some true, st [] [] a (ones (b + 1)) (ones m) o⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    rw [e, ih, show b + 1 + m = b + (m + 1) by omega]

theorem run_l6 (m : ℕ) (o : List Bool) (v : Option Bool) :
    F^[m + 1] (some ⟨some .l6, v, st [] [] [] (ones m) [] o⟩) =
      some ⟨none, none, st [] [] [] [] [] (ones m ++ o)⟩ := by
  induction m generalizing v o with
  | zero => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have e : F (some ⟨some .l6, v, st [] [] [] (ones (m + 1)) [] o⟩) =
        some ⟨some .l6, some true, st [] [] [] (ones m) [] (true :: o)⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    rw [e, ih]; simp [List.replicate_succ']

/-- The doubling loop: `k` rounds turn `m` marks into `2^k * m` marks. -/
theorem run_l3 (k : ℕ) : ∀ (m : ℕ) (v : Option Bool) (o : List Bool),
    ∃ s, s + 3 * m ≤ 3 * m * 2 ^ k + 3 * k + 1 ∧
      F^[s] (some ⟨some .l3, v, st [] [] (ones k) (ones m) [] o⟩) =
        some ⟨some .l6, none, st [] [] [] (ones (2 ^ k * m)) [] o⟩ := by
  induction k with
  | zero =>
    intro m v o
    exact ⟨1, by rw [pow_zero]; omega, by simp [TM2.step, stmt, TM2.stepAux, isS, flip]⟩
  | succ k ih =>
    intro m v o
    obtain ⟨s, hs, h⟩ := ih (2 * m) none o
    have e : F^[1] (some ⟨some .l3, v, st [] [] (ones (k + 1)) (ones m) [] o⟩) =
        some ⟨some .l4, some true, st [] [] (ones k) (ones m) [] o⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    have h4 := run_l4 m 0 (ones k) o (some true)
    have h5 := run_l5 (0 + 2 * m) 0 (ones k) o none
    simp only [Nat.zero_add] at h4 h5
    have := iter_chain (iter_chain (iter_chain e h4) h5) h
    refine ⟨_, ?_, this.trans (by rw [pow_succ, Nat.mul_assoc, Nat.mul_comm 2 m])⟩
    have h2 : 3 * (2 * m) * 2 ^ k = 3 * m * 2 ^ (k + 1) := by rw [pow_succ]; ring
    omega

end PadTM

/-- **The padding map is computable in time `4·2ⁿ + 5n + 4`.** -/
noncomputable def padComputable : TM2ComputableInTime strEnc strEnc padF where
  tm := PadTM.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time n := 4 * 2 ^ n + 5 * n + 4
  outputsFun x :=
    have hex : ∃ s ≤ 4 * 2 ^ x.length + 5 * x.length + 4,
        (flip bind (TM2.step PadTM.stmt))^[s] (some ⟨some .l1, none, PadTM.st x [] [] [] [] []⟩) =
          some ⟨none, none, PadTM.st [] [] [] [] [] (padF x)⟩ := by
      have h1 : (flip bind (TM2.step PadTM.stmt))^[x.length + 1]
          (some ⟨some .l1, none, PadTM.st x [] [] [] [] []⟩) =
          some ⟨some .l2, none, PadTM.st [] x.reverse [] [] [] []⟩ := by
        simpa using PadTM.run_l1 x [] none
      have h2 : (flip bind (TM2.step PadTM.stmt))^[x.length + 1]
          (some ⟨some .l2, none, PadTM.st [] x.reverse [] [] [] []⟩) =
          some ⟨some .l3, none, PadTM.st [] [] (PadTM.ones x.length) (PadTM.ones 1) [] (false :: x)⟩ := by
        simpa using PadTM.run_l2 x.reverse [] 0 none
      obtain ⟨s, hs, h3⟩ := PadTM.run_l3 x.length 1 none (false :: x)
      have h6 := PadTM.run_l6 (2 ^ x.length * 1) (false :: x) none
      have := iter_chain (iter_chain (iter_chain h1 h2) h3) h6
      refine ⟨_, ?_, this.trans (by simp [padF])⟩
      simp only [List.append_nil, List.length_reverse, Nat.mul_one] at hs ⊢
      omega
    { steps := Classical.choose hex
      evals_in_steps := by
        have := (Classical.choose_spec hex).2
        have ei : initList PadTM.tm (x : List Bool) =
            (⟨some .l1, none, PadTM.st x [] [] [] [] []⟩ : PadTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList PadTM.tm (padF x : List Bool) =
            (⟨none, none, PadTM.st [] [] [] [] [] (padF x)⟩ : PadTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact this
      steps_le_m := by
        have := (Classical.choose_spec hex).1
        simpa [strEnc] using this }

end PvnpReal
