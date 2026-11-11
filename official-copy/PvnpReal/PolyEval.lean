/-
  PvnpReal.PolyEval — unary polynomial evaluation in polynomial time.

  `lenTM`: `x ↦ 1^{|x|} 0`; `sndTM`: `1ⁿ 0 1ᵐ ↦ 1ᵐ`; together with `hornerComputable` and
  `composeComputable` this gives `polyEvalComputable P : x ↦ 1^{P(|x|)}`.
-/
import PvnpReal.Arith
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

namespace SmallTM

inductive UK | inp | out
  deriving DecidableEq

instance : Fintype UK := ⟨{.inp, .out}, fun k => by cases k <;> simp⟩

inductive UL | l1 | l2
  deriving DecidableEq

instance : Fintype UL := ⟨{.l1, .l2}, fun k => by cases k <;> simp⟩

abbrev Γ : UK → Type := fun _ => Bool
abbrev St := TM2.Stmt Γ UL (Option Bool)
abbrev Cfg := TM2.Cfg Γ UL (Option Bool)

def st (i o : List Bool) : ∀ k : UK, List (Γ k)
  | .inp => i
  | .out => o

@[simp] theorem upd_inp (i o x : List Bool) : Function.update (st i o) UK.inp x = st x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i o x : List Bool) : Function.update (st i o) UK.out x = st i x := by
  funext k; cases k <;> rfl
@[simp] theorem st_inp (i o : List Bool) : st i o UK.inp = i := rfl
@[simp] theorem st_out (i o : List Bool) : st i o UK.out = o := rfl

def isS : Option Bool → Bool := fun o => o.isSome
def isT : Option Bool → Bool
  | some true => true
  | _ => false

def mk (m : UL → St) : FinTM2 where
  K := UK
  k₀ := UK.inp
  k₁ := UK.out
  Γ := Γ
  Λ := UL
  main := .l1
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := m

theorem initList_eq (m : UL → St) (l : List Bool) :
    initList (mk m) l = (⟨some .l1, none, st l []⟩ : Cfg) := by
  simp only [initList]; congr 1; funext k; cases k <;> rfl

theorem haltList_eq (m : UL → St) (l : List Bool) :
    haltList (mk m) l = (⟨none, none, st [] l⟩ : Cfg) := by
  simp only [haltList]; congr 1; funext k; cases k <;> rfl

/-! ### `lenTM`: `x ↦ 1^{|x|} 0` -/

def lenStmt : UL → St
  | .l1 => push UK.out (fun _ => false) (goto fun _ => .l2)
  | .l2 => pop UK.inp (fun _ o => o)
      (branch isS (push UK.out (fun _ => true) (goto fun _ => .l2)) halt)

abbrev FL : Option Cfg → Option Cfg := flip bind (TM2.step lenStmt)

theorem FL_some (c : Cfg) : FL (some c) = TM2.step lenStmt c := rfl

theorem len_loop (l : List Bool) (v : Option Bool) (o : List Bool) :
    FL^[l.length + 1] (some ⟨some .l2, v, st l o⟩) =
      some ⟨none, none, st [] (List.replicate l.length true ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [FL_some, TM2.step, lenStmt, TM2.stepAux, isS]
  | cons b l ih =>
    have e : FL (some ⟨some .l2, v, st (b :: l) o⟩) = some ⟨some .l2, some b, st l (true :: o)⟩ := by
      simp [FL_some, TM2.step, lenStmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]
    simp [List.replicate_succ']

def lenF (x : List Bool) : List Bool := List.replicate x.length true ++ [false]

noncomputable def lenComputable : TM2ComputableInPolyTime strEnc strEnc lenF where
  tm := mk lenStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun l :=
    { steps := (l.length + 1) + 1
      evals_in_steps := by
        have e : FL (some ⟨some .l1, none, st l []⟩) = some ⟨some .l2, none, st l [false]⟩ := by
          simp [FL_some, TM2.step, lenStmt, TM2.stepAux]
        have := len_loop l none [false]
        erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
        change FL^[l.length + 1] (FL (some ⟨some .l1, none, st l []⟩)) =
          some ⟨none, none, st [] (lenF l)⟩
        rw [e]; exact this
      steps_le_m := by simp [strEnc] }

/-! ### `sndTM`: `1ⁿ 0 1ᵐ ↦ 1ᵐ` -/

def sndStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o) (branch isT (goto fun _ => .l1) (goto fun _ => .l2))
  | .l2 => pop UK.inp (fun _ o => o)
      (branch isS (push UK.out (fun _ => true) (goto fun _ => .l2)) halt)

abbrev FS : Option Cfg → Option Cfg := flip bind (TM2.step sndStmt)

theorem FS_some (c : Cfg) : FS (some c) = TM2.step sndStmt c := rfl

theorem snd_skip (l : List Bool) (v : Option Bool) :
    ∃ v', FS^[(l.takeWhile id).length + 1] (some ⟨some .l1, v, st l []⟩) =
      some ⟨some .l2, v', st (l.drop ((l.takeWhile id).length + 1)) []⟩ := by
  induction l generalizing v with
  | nil => exact ⟨none, by simp [FS_some, TM2.step, sndStmt, TM2.stepAux, isT]⟩
  | cons b l ih =>
    cases b with
    | false => exact ⟨some false, by simp [FS_some, TM2.step, sndStmt, TM2.stepAux, isT]⟩
    | true =>
      obtain ⟨v', hv⟩ := ih (some true)
      refine ⟨v', ?_⟩
      have e : FS (some ⟨some .l1, v, st (true :: l) []⟩) = some ⟨some .l1, some true, st l []⟩ := by
        simp [FS_some, TM2.step, sndStmt, TM2.stepAux, isT]
      simp only [List.takeWhile_cons, id, if_true, List.length_cons, List.drop_succ_cons]
      rw [Function.iterate_succ_apply, e, hv]

theorem snd_copy (l : List Bool) (v : Option Bool) (o : List Bool) :
    FS^[l.length + 1] (some ⟨some .l2, v, st l o⟩) =
      some ⟨none, none, st [] (List.replicate l.length true ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [FS_some, TM2.step, sndStmt, TM2.stepAux, isS]
  | cons b l ih =>
    have e : FS (some ⟨some .l2, v, st (b :: l) o⟩) = some ⟨some .l2, some b, st l (true :: o)⟩ := by
      simp [FS_some, TM2.step, sndStmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]
    simp [List.replicate_succ']

def sndF (l : List Bool) : List Bool := List.replicate (HornerTM.hM l) true

noncomputable def sndComputable : TM2ComputableInPolyTime strEnc strEnc sndF where
  tm := mk sndStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun l :=
    { steps := (HornerTM.hM l + 1) + (HornerTM.hN l + 1)
      evals_in_steps := by
        obtain ⟨v', h1⟩ := snd_skip l none
        have h2 := snd_copy (l.drop (HornerTM.hN l + 1)) v' []
        erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
        change FS^[HornerTM.hM l + 1 + (HornerTM.hN l + 1)] (some ⟨some .l1, none, st l []⟩) =
          some ⟨none, none, st [] (sndF l)⟩
        rw [Function.iterate_add_apply]
        erw [h1]
        rw [List.append_nil] at h2
        exact h2
      steps_le_m := by
        have := HornerTM.hNM_le l
        simp [strEnc]; omega }

end SmallTM

/-! ### Polynomial evaluation -/

/-- Unary pair `1ⁿ 0 1ᵐ`. -/
def pairU (n m : ℕ) : List Bool := List.replicate n true ++ false :: List.replicate m true

theorem hN_pairU (n m : ℕ) : HornerTM.hN (pairU n m) = n := by
  unfold HornerTM.hN pairU
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem hM_pairU (n m : ℕ) : HornerTM.hM (pairU n m) = m := by
  unfold HornerTM.hM; rw [hN_pairU]; simp [pairU]; omega

theorem hornerF_pairU (a n m : ℕ) : hornerF a (pairU n m) = pairU n (n * m + a) := by
  rw [hornerF, hN_pairU, hM_pairU]; rfl

/-- Horner value: `hval n [c₀, c₁, …] = c₀ + n·(c₁ + n·(…))`. -/
def hval (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => n * hval n cs + c

/-- The pipeline `lenF`, then Horner steps (highest coefficient first). -/
def pipe : List ℕ → List Bool → List Bool
  | [] => SmallTM.lenF
  | c :: cs => hornerF c ∘ pipe cs

theorem pipe_eq (cs : List ℕ) (x : List Bool) : pipe cs x = pairU x.length (hval x.length cs) := by
  induction cs with
  | nil => simp [pipe, SmallTM.lenF, pairU, hval]
  | cons c cs ih => simp only [pipe, Function.comp, ih, hornerF_pairU, hval]

noncomputable def pipeComputable : ∀ cs : List ℕ, TM2ComputableInPolyTime strEnc strEnc (pipe cs)
  | [] => SmallTM.lenComputable
  | c :: cs => composeComputable (pipeComputable cs) (hornerComputable c)

theorem hval_range (n : ℕ) (f : ℕ → ℕ) (k : ℕ) :
    hval n ((List.range k).map f) = ∑ i ∈ Finset.range k, f i * n ^ i := by
  induction k generalizing f with
  | zero => simp [hval]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hval, ih, Finset.sum_range_succ',
      Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; simp only [Function.comp]; ring
    · simp

/-- Coefficient list of a polynomial (lowest degree first). -/
noncomputable def coeffs (P : Polynomial ℕ) : List ℕ := (List.range (P.natDegree + 1)).map P.coeff

theorem hval_coeffs (P : Polynomial ℕ) (n : ℕ) : hval n (coeffs P) = P.eval n := by
  rw [coeffs, hval_range, Polynomial.eval_eq_sum_range]

/-- Unary polynomial evaluation. -/
def polyU (P : Polynomial ℕ) (x : List Bool) : List Bool := List.replicate (P.eval x.length) true

theorem polyU_eq (P : Polynomial ℕ) : polyU P = SmallTM.sndF ∘ pipe (coeffs P) := by
  funext x
  simp only [Function.comp, pipe_eq, SmallTM.sndF, hM_pairU, hval_coeffs, polyU]

/-- **Unary polynomial evaluation is polynomial-time**: for every `P : Polynomial ℕ` there is a
real `FinTM2` mapping `x` to `1^{P(|x|)}` in polynomial time. -/
noncomputable def polyEvalComputable (P : Polynomial ℕ) :
    TM2ComputableInPolyTime strEnc strEnc (polyU P) := by
  rw [polyU_eq]
  exact composeComputable (pipeComputable (coeffs P)) SmallTM.sndComputable

end PvnpReal
