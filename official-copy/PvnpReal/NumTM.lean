/-
  PvnpReal.NumTM — number sequences `u(a₀) u(a₁) …` (`u(a) = 1ᵃ0`) and two primitive machines:
  lookup of the `i`-th number (`numAtComputable`) and truncated subtraction (`monusComputable`).
-/
import PvnpReal.IterTM

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

/-! ### Number sequences -/

theorem lpX_length_lt {l : List Bool} (h : l ≠ []) : (lpX l).length < l.length := by
  rcases l with _ | ⟨b, r⟩
  · exact absurd rfl h
  · cases b
    · rw [LoopTM.lpX_cons_false]; simp
    · rw [LoopTM.lpX_cons_true]
      have := LoopTM.lp_len r
      simp; omega

/-- Parse a bit string as a sequence of unary numbers (total). -/
def numsOf (l : List Bool) : List ℕ :=
  if h : l = [] then [] else lpN l :: numsOf (lpX l)
termination_by l.length
decreasing_by exact lpX_length_lt h

def encNums (l : List ℕ) : List Bool := l.flatMap (fun a => List.replicate a true ++ [false])

theorem numsOf_nil : numsOf [] = [] := by rw [numsOf]; simp

theorem numsOf_ne {l : List Bool} (h : l ≠ []) : numsOf l = lpN l :: numsOf (lpX l) := by
  rw [numsOf]; simp [h]

theorem numsOf_encNums (l : List ℕ) : numsOf (encNums l) = l := by
  induction l with
  | nil => simp [encNums, numsOf_nil]
  | cons a l ih =>
    have : encNums (a :: l) = List.replicate a true ++ false :: encNums l := by
      simp [encNums]
    rw [this, numsOf_ne (by simp), lpN_rep, lpX_rep, ih]

theorem getD_numsOf (i : ℕ) : ∀ w : List Bool, (numsOf w).getD i 0 = lpN (lpX^[i] w) := by
  induction i with
  | zero =>
    intro w
    by_cases h : w = []
    · subst h; simp [numsOf_nil, lpN]
    · rw [numsOf_ne h]; simp
  | succ i ih =>
    intro w
    by_cases h : w = []
    · subst h
      have : ∀ j, lpX^[j] ([] : List Bool) = [] := by
        intro j; induction j with
        | zero => rfl
        | succ j ihj => rw [Function.iterate_succ_apply]; simpa [lpX, lpN] using ihj
      rw [this]; simp [numsOf_nil, lpN]
    · rw [numsOf_ne h, Function.iterate_succ_apply, List.getD_cons_succ, ih]

theorem lpN_replicate (n : ℕ) : lpN (List.replicate n true) = n := by
  induction n with
  | zero => simp [lpN]
  | succ n ih => rw [List.replicate_succ, LoopTM.lpN_cons_true, ih]

theorem lpX_replicate (n : ℕ) : lpX (List.replicate n true) = [] := by
  induction n with
  | zero => simp [lpX, lpN]
  | succ n ih => rw [List.replicate_succ, LoopTM.lpX_cons_true, ih]

/-! ### Machine 1: the `i`-th number -/

namespace NumTM

open TM2.Stmt

inductive NK | inp | C | out
  deriving DecidableEq

instance : Fintype NK := ⟨{.inp, .C, .out}, fun k => by cases k <;> simp⟩

inductive NL | c | s | k | cp | clr
  deriving DecidableEq

instance : Fintype NL := ⟨{.c, .s, .k, .cp, .clr}, fun k => by cases k <;> simp⟩

abbrev Γ : NK → Type := fun _ => Bool
abbrev St := TM2.Stmt Γ NL (Option Bool)
abbrev Cfg := TM2.Cfg Γ NL (Option Bool)

def st (i c o : List Bool) : ∀ k : NK, List (Γ k)
  | .inp => i
  | .C => c
  | .out => o

@[simp] theorem st_inp (i c o) : st i c o .inp = i := rfl
@[simp] theorem st_C (i c o) : st i c o .C = c := rfl
@[simp] theorem st_out (i c o) : st i c o .out = o := rfl
@[simp] theorem upd_inp (i c o x) : Function.update (st i c o) .inp x = st x c o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_C (i c o x) : Function.update (st i c o) .C x = st i x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i c o x) : Function.update (st i c o) .out x = st i c x := by
  funext k; cases k <;> rfl

def isS : Option Bool → Bool := fun o => o.isSome
def isT : Option Bool → Bool
  | some true => true
  | _ => false

def stmt : NL → St
  | .c => pop .inp (fun _ o => o) (branch isT (push .C (fun _ => true) (goto fun _ => .c))
      (goto fun _ => .s))
  | .s => pop .C (fun _ o => o) (branch isS (goto fun _ => .k) (goto fun _ => .cp))
  | .k => pop .inp (fun _ o => o) (branch isT (goto fun _ => .k) (goto fun _ => .s))
  | .cp => pop .inp (fun _ o => o) (branch isT (push .out (fun _ => true) (goto fun _ => .cp))
      (goto fun _ => .clr))
  | .clr => pop .inp (fun _ o => o) (branch isS (goto fun _ => .clr) halt)

def tm : FinTM2 where
  K := NK
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := NL
  main := .c
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt

local notation "F" => flip bind (TM2.step stmt)

abbrev ones (n : ℕ) : List Bool := List.replicate n true

theorem run_c (l : List Bool) (v : Option Bool) (a : ℕ) :
    ∃ v', F^[lpN l + 1] (some ⟨some .c, v, st l (ones a) []⟩) =
      some ⟨some .s, v', st (lpX l) (ones (a + lpN l)) []⟩ := by
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
      have e : F (some ⟨some .c, v, st (true :: l) (ones a) []⟩) =
          some ⟨some .c, some true, st l (ones (a + 1)) []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, List.replicate_succ]
      rw [e, h, show a + 1 + lpN l = a + (lpN l + 1) by omega]

theorem run_k (l : List Bool) (v : Option Bool) (c : List Bool) :
    ∃ v', F^[lpN l + 1] (some ⟨some .k, v, st l c []⟩) = some ⟨some .s, v', st (lpX l) c []⟩ := by
  induction l generalizing v with
  | nil => exact ⟨none, by simp [TM2.step, stmt, TM2.stepAux, isT, flip, lpN, lpX]⟩
  | cons b l ih =>
    cases b
    · exact ⟨some false, by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, LoopTM.lpN_cons_false,
          LoopTM.lpX_cons_false]⟩
    · obtain ⟨v', h⟩ := ih (some true)
      refine ⟨v', ?_⟩
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply]
      have e : F (some ⟨some .k, v, st (true :: l) c []⟩) = some ⟨some .k, some true, st l c []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip]
      rw [e, h]

theorem run_s (j : ℕ) : ∀ (w : List Bool) (v : Option Bool),
    ∃ s ≤ 2 * j + w.length + 1, F^[s] (some ⟨some .s, v, st w (ones j) []⟩) =
      some ⟨some .cp, none, st (lpX^[j] w) [] []⟩ := by
  induction j with
  | zero => intro w v; exact ⟨1, by omega, by simp [TM2.step, stmt, TM2.stepAux, isS, flip]⟩
  | succ j ih =>
    intro w v
    have e1 : F^[1] (some ⟨some .s, v, st w (ones (j + 1)) []⟩) =
        some ⟨some .k, some true, st w (ones j) []⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    obtain ⟨v', e2⟩ := run_k w (some true) (ones j)
    obtain ⟨s, hs, e3⟩ := ih (lpX w) v'
    have := iter_chain (iter_chain e1 e2) e3
    refine ⟨_, ?_, this.trans (by rw [← Function.iterate_succ_apply])⟩
    have := LoopTM.lp_len w
    omega

theorem run_cp (l : List Bool) (v : Option Bool) (o : List Bool) :
    ∃ v', F^[lpN l + 1] (some ⟨some .cp, v, st l [] o⟩) =
      some ⟨some .clr, v', st (lpX l) [] (ones (lpN l) ++ o)⟩ := by
  induction l generalizing v o with
  | nil => exact ⟨none, by simp [TM2.step, stmt, TM2.stepAux, isT, flip, lpN, lpX]⟩
  | cons b l ih =>
    cases b
    · exact ⟨some false, by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, LoopTM.lpN_cons_false,
          LoopTM.lpX_cons_false]⟩
    · obtain ⟨v', h⟩ := ih (some true) (true :: o)
      refine ⟨v', ?_⟩
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply]
      have e : F (some ⟨some .cp, v, st (true :: l) [] o⟩) =
          some ⟨some .cp, some true, st l [] (true :: o)⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip]
      rw [e, h]; simp [List.replicate_succ']

theorem run_clr (l : List Bool) (v : Option Bool) (o : List Bool) :
    F^[l.length + 1] (some ⟨some .clr, v, st l [] o⟩) = some ⟨none, none, st [] [] o⟩ := by
  induction l generalizing v with
  | nil => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .clr, v, st (b :: l) [] o⟩) = some ⟨some .clr, some b, st l [] o⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip]
    rw [e, ih]

theorem lpX_iter_len (j : ℕ) : ∀ w : List Bool, (lpX^[j] w).length ≤ w.length := by
  induction j with
  | zero => intro w; rfl
  | succ j ih =>
    intro w; rw [Function.iterate_succ_apply]
    exact (ih _).trans (by have := LoopTM.lp_len w; omega)

end NumTM

/-- `numAt z = (numsOf (lpX z))[lpN z]` (0 if absent), in unary. -/
def numAt (z : List Bool) : List Bool := List.replicate ((numsOf (lpX z)).getD (lpN z) 0) true

noncomputable def numAtComputable : TM2ComputableInPolyTime strEnc strEnc numAt where
  tm := NumTM.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * Polynomial.X + 6
  outputsFun z :=
    have hex : ∃ s ≤ 6 * z.length + 6,
        (flip bind (TM2.step NumTM.stmt))^[s] (some ⟨some .c, none, NumTM.st z [] []⟩) =
          some ⟨none, none, NumTM.st [] [] (numAt z)⟩ := by
      obtain ⟨v1, h1⟩ := NumTM.run_c z none 0
      simp only [Nat.zero_add] at h1
      obtain ⟨s, hs, h2⟩ := NumTM.run_s (lpN z) (lpX z) v1
      obtain ⟨v3, h3⟩ := NumTM.run_cp (lpX^[lpN z] (lpX z)) none []
      have h4 := NumTM.run_clr (lpX (lpX^[lpN z] (lpX z))) v3
        (NumTM.ones (lpN (lpX^[lpN z] (lpX z))) ++ [])
      have := iter_chain (iter_chain (iter_chain h1 h2) h3) h4
      refine ⟨_, ?_, this.trans (by rw [numAt, getD_numsOf]; simp)⟩
      have a1 := LoopTM.lp_len z
      have a2 := NumTM.lpX_iter_len (lpN z) (lpX z)
      have a3 := LoopTM.lp_len (lpX^[lpN z] (lpX z))
      omega
    { steps := Classical.choose hex
      evals_in_steps := by
        have := (Classical.choose_spec hex).2
        have ei : initList NumTM.tm (z : List Bool) =
            (⟨some .c, none, NumTM.st z [] []⟩ : NumTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList NumTM.tm (numAt z : List Bool) =
            (⟨none, none, NumTM.st [] [] (numAt z)⟩ : NumTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact this
      steps_le_m := by
        have := (Classical.choose_spec hex).1
        simpa [strEnc] using this }

/-! ### Machine 2: truncated subtraction -/

namespace SubTM

open TM2.Stmt NumTM

inductive SL | c | d | clr | mv
  deriving DecidableEq

instance : Fintype SL := ⟨{.c, .d, .clr, .mv}, fun k => by cases k <;> simp⟩

abbrev St := TM2.Stmt NumTM.Γ SL (Option Bool)
abbrev Cfg := TM2.Cfg NumTM.Γ SL (Option Bool)

def stmt : SL → St
  | .c => pop .inp (fun _ o => o) (branch isT (push .C (fun _ => true) (goto fun _ => .c))
      (goto fun _ => .d))
  | .d => pop .inp (fun _ o => o) (branch isT (pop .C (fun s _ => s) (goto fun _ => .d))
      (goto fun _ => .clr))
  | .clr => pop .inp (fun _ o => o) (branch isS (goto fun _ => .clr) (goto fun _ => .mv))
  | .mv => pop .C (fun _ o => o) (branch isS (push .out (fun _ => true) (goto fun _ => .mv)) halt)

def tm : FinTM2 where
  K := NK
  k₀ := .inp
  k₁ := .out
  Γ := NumTM.Γ
  Λ := SL
  main := .c
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt

local notation "F" => flip bind (TM2.step stmt)

theorem run_c (l : List Bool) (v : Option Bool) (a : ℕ) :
    ∃ v', F^[lpN l + 1] (some ⟨some .c, v, st l (ones a) []⟩) =
      some ⟨some .d, v', st (lpX l) (ones (a + lpN l)) []⟩ := by
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
      have e : F (some ⟨some .c, v, st (true :: l) (ones a) []⟩) =
          some ⟨some .c, some true, st l (ones (a + 1)) []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, List.replicate_succ]
      rw [e, h, show a + 1 + lpN l = a + (lpN l + 1) by omega]

theorem run_d (l : List Bool) (v : Option Bool) (a : ℕ) :
    ∃ v', F^[lpN l + 1] (some ⟨some .d, v, st l (ones a) []⟩) =
      some ⟨some .clr, v', st (lpX l) (ones (a - lpN l)) []⟩ := by
  induction l generalizing v a with
  | nil => exact ⟨none, by simp [TM2.step, stmt, TM2.stepAux, isT, flip, lpN, lpX]⟩
  | cons b l ih =>
    cases b
    · exact ⟨some false, by
        simp [TM2.step, stmt, TM2.stepAux, isT, flip, LoopTM.lpN_cons_false,
          LoopTM.lpX_cons_false]⟩
    · obtain ⟨v', h⟩ := ih (some true) (a - 1)
      refine ⟨v', ?_⟩
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply]
      have e : F (some ⟨some .d, v, st (true :: l) (ones a) []⟩) =
          some ⟨some .d, some true, st l (ones (a - 1)) []⟩ := by
        rcases a with _ | a
        · simp [TM2.step, stmt, TM2.stepAux, isT, flip]
        · simp [TM2.step, stmt, TM2.stepAux, isT, flip, List.replicate_succ]
      rw [e, h, show a - 1 - lpN l = a - (lpN l + 1) by omega]

theorem run_clr (l : List Bool) (v : Option Bool) (c : List Bool) :
    F^[l.length + 1] (some ⟨some .clr, v, st l c []⟩) = some ⟨some .mv, none, st [] c []⟩ := by
  induction l generalizing v with
  | nil => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .clr, v, st (b :: l) c []⟩) = some ⟨some .clr, some b, st l c []⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip]
    rw [e, ih]

theorem run_mv (n : ℕ) (v : Option Bool) (o : List Bool) :
    F^[n + 1] (some ⟨some .mv, v, st [] (ones n) o⟩) = some ⟨none, none, st [] [] (ones n ++ o)⟩ := by
  induction n generalizing v o with
  | zero => simp [TM2.step, stmt, TM2.stepAux, isS, flip]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have e : F (some ⟨some .mv, v, st [] (ones (n + 1)) o⟩) =
        some ⟨some .mv, some true, st [] (ones n) (true :: o)⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, isS, flip, List.replicate_succ]
    rw [e, ih]; simp [List.replicate_succ']

end SubTM

/-- `1ᵃ 0 1ᵇ 0 … ↦ 1^{a - b}`. -/
def monusF (z : List Bool) : List Bool := List.replicate (lpN z - lpN (lpX z)) true

noncomputable def monusComputable : TM2ComputableInPolyTime strEnc strEnc monusF where
  tm := SubTM.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 4
  outputsFun z :=
    have hex : ∃ s ≤ 4 * z.length + 4,
        (flip bind (TM2.step SubTM.stmt))^[s] (some ⟨some .c, none, NumTM.st z [] []⟩) =
          some ⟨none, none, NumTM.st [] [] (monusF z)⟩ := by
      obtain ⟨v1, h1⟩ := SubTM.run_c z none 0
      simp only [Nat.zero_add] at h1
      obtain ⟨v2, h2⟩ := SubTM.run_d (lpX z) v1 (lpN z)
      have h3 := SubTM.run_clr (lpX (lpX z)) v2 (NumTM.ones (lpN z - lpN (lpX z)))
      have h4 := SubTM.run_mv (lpN z - lpN (lpX z)) none []
      have := iter_chain (iter_chain (iter_chain h1 h2) h3) h4
      refine ⟨_, ?_, this.trans (by simp [monusF])⟩
      have a1 := LoopTM.lp_len z
      have a2 := LoopTM.lp_len (lpX z)
      omega
    { steps := Classical.choose hex
      evals_in_steps := by
        have := (Classical.choose_spec hex).2
        have ei : initList SubTM.tm (z : List Bool) =
            (⟨some .c, none, NumTM.st z [] []⟩ : SubTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList SubTM.tm (monusF z : List Bool) =
            (⟨none, none, NumTM.st [] [] (monusF z)⟩ : SubTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact this
      steps_le_m := by
        have := (Classical.choose_spec hex).1
        simpa [strEnc] using this }

/-! ### Closure lemmas -/

theorem PU.sub {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) : PU (fun x => u x - v x) :=
  ((PS.append hu (PS.cons false hv)).comp ⟨monusComputable⟩).congr (fun x => by
    simp [monusF, lpN_rep, lpX_rep, lpN_replicate])

theorem PU.getNum {u : List Bool → ℕ} {s : List Bool → List Bool} (hu : PU u) (hs : PS s) :
    PU (fun x => (numsOf (s x)).getD (u x) 0) :=
  ((PS.append hu (PS.cons false hs)).comp ⟨numAtComputable⟩).congr (fun x => by
    simp [numAt, lpN_rep, lpX_rep])

end PvnpReal
