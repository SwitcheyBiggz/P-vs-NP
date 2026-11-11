/-
  PvnpReal.Arith — unary arithmetic on Mathlib `FinTM2`s, toward evaluating polynomials in
  polynomial time.

  Bit strings encode pairs of unary numbers: `pairU n m = 1ⁿ 0 1ᵐ`.
  `hornerTM a` is a real 5-stack machine computing `(n, m) ↦ (n, n·m + a)` in time
  `O(|input|²)`. (On a string that is not of this form it still computes a fixed, specified
  function: `n` = leading ones, `m` = number of remaining symbols after the first zero.)
-/
import PvnpReal.Compose

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

namespace HornerTM

inductive HK | inp | N | M | T | out
  deriving DecidableEq

instance : Fintype HK := ⟨{.inp, .N, .M, .T, .out}, fun k => by cases k <;> simp⟩

inductive HL | readN | readM | outer | copy1 | copy2 | final
  deriving DecidableEq

instance : Fintype HL :=
  ⟨{.readN, .readM, .outer, .copy1, .copy2, .final}, fun k => by cases k <;> simp⟩

abbrev Γ : HK → Type := fun _ => Bool

abbrev St := TM2.Stmt Γ HL (Option Bool)

def isS : Option Bool → Bool := fun o => o.isSome
def isT : Option Bool → Bool
  | some true => true
  | _ => false

/-- Push `a` ones onto the output, then continue with `q`. -/
def pushN : ℕ → St → St
  | 0, q => q
  | a + 1, q => push HK.out (fun _ => true) (pushN a q)

def stmt (a : ℕ) : HL → St
  | .readN => pop HK.inp (fun _ o => o)
      (branch isT (push HK.N (fun _ => true) (goto fun _ => .readN)) (goto fun _ => .readM))
  | .readM => pop HK.inp (fun _ o => o)
      (branch isS (push HK.M (fun _ => true) (goto fun _ => .readM))
        (pushN a (goto fun _ => .outer)))
  | .outer => pop HK.M (fun _ o => o)
      (branch isS (goto fun _ => .copy1) (push HK.out (fun _ => false) (goto fun _ => .final)))
  | .copy1 => pop HK.N (fun _ o => o)
      (branch isS (push HK.T (fun _ => true) (push HK.out (fun _ => true) (goto fun _ => .copy1)))
        (goto fun _ => .copy2))
  | .copy2 => pop HK.T (fun _ o => o)
      (branch isS (push HK.N (fun _ => true) (goto fun _ => .copy2)) (goto fun _ => .outer))
  | .final => pop HK.N (fun _ o => o)
      (branch isS (push HK.out (fun _ => true) (goto fun _ => .final)) halt)

def tm (a : ℕ) : FinTM2 where
  K := HK
  k₀ := HK.inp
  k₁ := HK.out
  Γ := Γ
  Λ := HL
  main := .readN
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt a

/-- Stack builder. -/
def st (i n m t o : List Bool) : ∀ k : HK, List (Γ k)
  | .inp => i
  | .N => n
  | .M => m
  | .T => t
  | .out => o

@[simp] theorem upd_inp (i n m t o x : List Bool) :
    Function.update (st i n m t o) HK.inp x = st x n m t o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_N (i n m t o x : List Bool) :
    Function.update (st i n m t o) HK.N x = st i x m t o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_M (i n m t o x : List Bool) :
    Function.update (st i n m t o) HK.M x = st i n x t o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_T (i n m t o x : List Bool) :
    Function.update (st i n m t o) HK.T x = st i n m x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i n m t o x : List Bool) :
    Function.update (st i n m t o) HK.out x = st i n m t x := by
  funext k; cases k <;> rfl
@[simp] theorem st_inp (i n m t o : List Bool) : st i n m t o HK.inp = i := rfl
@[simp] theorem st_N (i n m t o : List Bool) : st i n m t o HK.N = n := rfl
@[simp] theorem st_M (i n m t o : List Bool) : st i n m t o HK.M = m := rfl
@[simp] theorem st_T (i n m t o : List Bool) : st i n m t o HK.T = t := rfl
@[simp] theorem st_out (i n m t o : List Bool) : st i n m t o HK.out = o := rfl

abbrev Cfg := TM2.Cfg Γ HL (Option Bool)

abbrev F (a : ℕ) : Option Cfg → Option Cfg := flip bind (TM2.step (stmt a))

theorem F_some (a : ℕ) (c : Cfg) : F a (some c) = TM2.step (stmt a) c := rfl

theorem stepAux_pushN (a : ℕ) (q : St) (v : Option Bool) (i n m t o : List Bool) :
    TM2.stepAux (pushN a q) v (st i n m t o) =
      TM2.stepAux q v (st i n m t (List.replicate a true ++ o)) := by
  induction a generalizing o with
  | zero => rfl
  | succ a ih =>
    simp only [pushN, TM2.stepAux, upd_out, st_out]
    rw [ih]; congr 2; simp [List.replicate_succ']

/-! ### Loops -/

theorem run_readN (a : ℕ) (l : List Bool) (v : Option Bool) (n m t o : List Bool) :
    ∃ v', (F a)^[(l.takeWhile id).length + 1] (some ⟨some .readN, v, st l n m t o⟩) =
      some ⟨some .readM, v',
        st (l.drop ((l.takeWhile id).length + 1)) (List.replicate (l.takeWhile id).length true ++ n)
          m t o⟩ := by
  induction l generalizing v n with
  | nil => exact ⟨none, by simp [F_some, TM2.step, stmt, TM2.stepAux, isT]⟩
  | cons b l ih =>
    cases b with
    | false => exact ⟨some false, by simp [F_some, TM2.step, stmt, TM2.stepAux, isT]⟩
    | true =>
      obtain ⟨v', hv⟩ := ih (some true) (true :: n)
      refine ⟨v', ?_⟩
      have e : (F a) (some ⟨some .readN, v, st (true :: l) n m t o⟩) =
          some ⟨some .readN, some true, st l (true :: n) m t o⟩ := by
        simp [F_some, TM2.step, stmt, TM2.stepAux, isT]
      simp only [List.takeWhile_cons, id, if_true, List.length_cons, List.drop_succ_cons]
      rw [Function.iterate_succ_apply, e, hv]
      simp [List.replicate_succ']

theorem run_readM (a : ℕ) (l : List Bool) (v : Option Bool) (n m t o : List Bool) :
    (F a)^[l.length + 1] (some ⟨some .readM, v, st l n m t o⟩) =
      some ⟨some .outer, none,
        st [] n (List.replicate l.length true ++ m) t (List.replicate a true ++ o)⟩ := by
  induction l generalizing v m with
  | nil =>
    simp [F_some, TM2.step, stmt, TM2.stepAux, isS, stepAux_pushN]
  | cons b l ih =>
    have e : (F a) (some ⟨some .readM, v, st (b :: l) n m t o⟩) =
        some ⟨some .readM, some b, st l n (true :: m) t o⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]
    simp [List.replicate_succ']

theorem run_copy1 (a k : ℕ) (v : Option Bool) (m t o : List Bool) :
    (F a)^[k + 1] (some ⟨some .copy1, v, st [] (List.replicate k true) m t o⟩) =
      some ⟨some .copy2, none,
        st [] [] m (List.replicate k true ++ t) (List.replicate k true ++ o)⟩ := by
  induction k generalizing v t o with
  | zero => simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
  | succ k ih =>
    have e : (F a) (some ⟨some .copy1, v, st [] (List.replicate (k + 1) true) m t o⟩) =
        some ⟨some .copy1, some true, st [] (List.replicate k true) m (true :: t) (true :: o)⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS, List.replicate_succ]
    rw [Function.iterate_succ_apply, e, ih]
    simp [List.replicate_succ']

theorem run_copy2 (a k : ℕ) (v : Option Bool) (n m o : List Bool) :
    (F a)^[k + 1] (some ⟨some .copy2, v, st [] n m (List.replicate k true) o⟩) =
      some ⟨some .outer, none, st [] (List.replicate k true ++ n) m [] o⟩ := by
  induction k generalizing v n with
  | zero => simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
  | succ k ih =>
    have e : (F a) (some ⟨some .copy2, v, st [] n m (List.replicate (k + 1) true) o⟩) =
        some ⟨some .copy2, some true, st [] (true :: n) m (List.replicate k true) o⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS, List.replicate_succ]
    rw [Function.iterate_succ_apply, e, ih]
    simp [List.replicate_succ']

theorem run_outer (a n m : ℕ) (v : Option Bool) (o : List Bool) :
    (F a)^[m * (2 * n + 3) + 1]
        (some ⟨some .outer, v, st [] (List.replicate n true) (List.replicate m true) [] o⟩) =
      some ⟨some .final, none,
        st [] (List.replicate n true) [] [] (false :: (List.replicate (n * m) true ++ o))⟩ := by
  induction m generalizing v o with
  | zero => simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
  | succ m ih =>
    have e : (F a) (some ⟨some .outer, v, st [] (List.replicate n true)
        (List.replicate (m + 1) true) [] o⟩) =
        some ⟨some .copy1, some true, st [] (List.replicate n true) (List.replicate m true) [] o⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS, List.replicate_succ]
    have h1 := run_copy1 a n (some true) (List.replicate m true) [] o
    have h2 := run_copy2 a n none [] (List.replicate m true) (List.replicate n true ++ o)
    have h3 := ih none (List.replicate n true ++ o)
    simp only [List.append_nil] at h1 h2
    rw [show (m + 1) * (2 * n + 3) + 1 = (m * (2 * n + 3) + 1) + ((n + 1) + ((n + 1) + 1)) by ring,
      Function.iterate_add_apply _ (m * (2 * n + 3) + 1) ((n + 1) + ((n + 1) + 1)),
      Function.iterate_add_apply _ (n + 1) ((n + 1) + 1), Function.iterate_add_apply _ (n + 1) 1,
      Function.iterate_one, e, h1, h2, h3]
    rw [Nat.mul_succ, List.replicate_add, List.append_assoc]

theorem run_final (a k : ℕ) (v : Option Bool) (o : List Bool) :
    (F a)^[k + 1] (some ⟨some .final, v, st [] (List.replicate k true) [] [] o⟩) =
      some ⟨none, none, st [] [] [] [] (List.replicate k true ++ o)⟩ := by
  induction k generalizing v o with
  | zero => simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
  | succ k ih =>
    have e : (F a) (some ⟨some .final, v, st [] (List.replicate (k + 1) true) [] [] o⟩) =
        some ⟨some .final, some true, st [] (List.replicate k true) [] [] (true :: o)⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS, List.replicate_succ]
    rw [Function.iterate_succ_apply, e, ih]
    simp [List.replicate_succ']


/-! ### The whole run -/

/-- Leading ones. -/
def hN (l : List Bool) : ℕ := (l.takeWhile id).length
/-- Number of symbols after the first zero. -/
def hM (l : List Bool) : ℕ := (l.drop (hN l + 1)).length

def steps (l : List Bool) : ℕ :=
  (hN l + 1) + ((hM l * (2 * hN l + 3) + 1) + ((hM l + 1) + (hN l + 1)))

theorem run (a : ℕ) (l : List Bool) :
    (F a)^[steps l] (some ⟨some .readN, none, st l [] [] [] []⟩) =
      some ⟨none, none, st [] [] [] []
        (List.replicate (hN l) true ++ false :: List.replicate (hN l * hM l + a) true)⟩ := by
  obtain ⟨v', h1⟩ := run_readN a l none [] [] [] []
  have h1' : (F a)^[hN l + 1] (some ⟨some .readN, none, st l [] [] [] []⟩) =
      some ⟨some .readM, v', st (l.drop (hN l + 1)) (List.replicate (hN l) true) [] [] []⟩ := by
    rw [List.append_nil] at h1; exact h1
  have h2 := run_readM a (l.drop (hN l + 1)) v' (List.replicate (hN l) true) [] [] []
  have h3 := run_outer a (hN l) (hM l) none (List.replicate a true)
  have h4 := run_final a (hN l) none (false :: (List.replicate (hN l * hM l) true ++
    List.replicate a true))
  simp only [List.append_nil] at h2
  unfold steps
  rw [Function.iterate_add_apply _ (hN l + 1), Function.iterate_add_apply _ (hM l * (2 * hN l + 3) + 1),
    Function.iterate_add_apply _ (hM l + 1), h1']
  erw [h2]
  rw [show (l.drop (hN l + 1)).length = hM l from rfl, h3, h4, List.replicate_add]
  try simp


theorem hN_le (l : List Bool) : hN l ≤ l.length := (List.takeWhile_prefix id).length_le
theorem hNM_le (l : List Bool) : hN l + hM l ≤ l.length := by
  have := hN_le l; unfold hM; rw [List.length_drop]; omega
theorem hM_le (l : List Bool) : hM l ≤ l.length := by have := hNM_le l; omega

theorem steps_le (l : List Bool) : steps l ≤ 2 * l.length ^ 2 + 4 * l.length + 4 := by
  have h1 := hN_le l
  have h2 := hM_le l
  have h3 : hM l * hN l ≤ l.length * l.length := Nat.mul_le_mul h2 h1
  have h4 := hNM_le l
  unfold steps
  nlinarith

theorem initList_eq (a : ℕ) (l : List Bool) :
    initList (tm a) l = (⟨some .readN, none, st l [] [] [] []⟩ : Cfg) := by
  simp only [initList]
  congr 1
  funext k; cases k <;> rfl

theorem haltList_eq (a : ℕ) (l : List Bool) :
    haltList (tm a) l = (⟨none, none, st [] [] [] [] l⟩ : Cfg) := by
  simp only [haltList]
  congr 1
  funext k; cases k <;> rfl

end HornerTM

/-- `(n, m) ↦ (n, n·m + a)` on unary pairs `1ⁿ 0 1ᵐ`, total on all bit strings. -/
def hornerF (a : ℕ) (l : List Bool) : List Bool :=
  List.replicate (HornerTM.hN l) true ++ false ::
    List.replicate (HornerTM.hN l * HornerTM.hM l + a) true

/-- **The Horner step is polynomial-time** (a real `FinTM2`, time `2n² + 4n + 4`). -/
noncomputable def hornerComputable (a : ℕ) :
    TM2ComputableInPolyTime strEnc strEnc (hornerF a) where
  tm := HornerTM.tm a
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X ^ 2 + 4 * Polynomial.X + 4
  outputsFun l :=
    { steps := HornerTM.steps l
      evals_in_steps := by
        have := HornerTM.run a l
        erw [List.map_id, List.map_id, HornerTM.initList_eq, Option.map_some,
          HornerTM.haltList_eq]
        exact this
      steps_le_m := by
        have := HornerTM.steps_le l
        simp only [strEnc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_ofNat]
        exact this }

end PvnpReal
