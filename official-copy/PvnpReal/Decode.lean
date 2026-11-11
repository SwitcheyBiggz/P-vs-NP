/-
  PvnpReal.Decode — a decoder machine from a self-delimiting bit code to verifier inputs
  (`strEnc → pairEnc`), and printing the code with the polytime combinators.
-/
import PvnpReal.HalfTM

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

/-! ### The code -/

/-- Bit `c` is written `1 0` (false) or `1 1 0` (true). -/
def codeL (a : List Bool) : List Bool := a.flatMap (fun c => true :: (if c then [true, false] else [false]))

def codeP (a b : List Bool) : List Bool := codeL a ++ false :: codeL b

/-- What the decoder pushes, first component. -/
def pbP : List Bool → List Bool
  | [] => []
  | false :: r => pbP r
  | true :: true :: r => true :: pbP (r.drop 1)
  | true :: false :: r => false :: pbP r
  | [true] => []
termination_by l => l.length
decreasing_by all_goals (simp <;> omega)

def decP : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: r => ([], pbP r)
  | true :: true :: r => (true :: (decP (r.drop 1)).1, (decP (r.drop 1)).2)
  | true :: false :: r => (false :: (decP r).1, (decP r).2)
  | [true] => ([], [])
termination_by l => l.length
decreasing_by all_goals (simp <;> omega)

theorem pbP_codeL (b : List Bool) : pbP (codeL b) = b := by
  induction b with
  | nil => simp [codeL, pbP]
  | cons c b ih =>
    cases c
    · simp only [codeL, List.flatMap_cons, Bool.false_eq_true, if_false] at ih ⊢
      simp [pbP, ih]
    · simp only [codeL, List.flatMap_cons] at ih ⊢
      simp [pbP, ih]

theorem decP_codeP (a b : List Bool) : decP (codeP a b) = (a, b) := by
  induction a with
  | nil =>
    have : codeP [] b = false :: codeL b := by simp [codeP, codeL]
    rw [this, decP, pbP_codeL]
  | cons c a ih =>
    unfold codeP at ih ⊢
    cases c
    · simp only [codeL, List.flatMap_cons] at ih ⊢
      simp [decP, ih]
    · simp only [codeL, List.flatMap_cons] at ih ⊢
      simp [decP, ih]

theorem pbP_len (n : ℕ) : ∀ z : List Bool, z.length ≤ n → (pbP z).length ≤ z.length := by
  induction n with
  | zero => intro z hz; obtain rfl : z = [] := List.length_eq_zero_iff.1 (by omega); simp [pbP]
  | succ n ih =>
    intro z hz
    match z, hz with
    | [], _ => simp [pbP]
    | false :: r, hz => have := ih r (by simp at hz; omega); simp [pbP]; omega
    | [true], _ => simp [pbP]
    | true :: false :: r, hz => have := ih r (by simp at hz; omega); simp [pbP]; omega
    | true :: true :: r, hz =>
      have := ih (r.drop 1) (by simp at hz ⊢; omega); simp [pbP] at this ⊢; omega

theorem decP_len (n : ℕ) : ∀ z : List Bool, z.length ≤ n →
    (decP z).1.length + (decP z).2.length ≤ z.length := by
  induction n with
  | zero => intro z hz; obtain rfl : z = [] := List.length_eq_zero_iff.1 (by omega); simp [decP]
  | succ n ih =>
    intro z hz
    match z, hz with
    | [], _ => simp [decP]
    | false :: r, hz => have := pbP_len r.length r le_rfl; simp [decP]; omega
    | [true], _ => simp [decP]
    | true :: false :: r, hz => have := ih r (by simp at hz; omega); simp [decP]; omega
    | true :: true :: r, hz =>
      have := ih (r.drop 1) (by simp at hz ⊢; omega); simp [decP] at this ⊢; omega

/-! ### The decoder machine -/

namespace DecTM

open TM2.Stmt

inductive DK | inp | sc | out
  deriving DecidableEq

instance : Fintype DK := ⟨{.inp, .sc, .out}, fun k => by cases k <;> simp⟩

inductive DL | a1 | a2 | a3 | b1 | b2 | b3 | mv
  deriving DecidableEq

instance : Fintype DL := ⟨{.a1, .a2, .a3, .b1, .b2, .b3, .mv}, fun k => by cases k <;> simp⟩

abbrev Γ : DK → Type
  | .inp => Bool
  | _ => Option Bool

abbrev σ := Option (Option Bool)
abbrev St := TM2.Stmt Γ DL σ
abbrev Cfg := TM2.Cfg Γ DL σ

def st (i : List Bool) (s o : List (Option Bool)) : ∀ k : DK, List (Γ k)
  | .inp => i
  | .sc => s
  | .out => o

@[simp] theorem upd_inp (i s o x) : Function.update (st i s o) .inp x = st x s o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_sc (i s o x) : Function.update (st i s o) .sc x = st i x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i s o x) : Function.update (st i s o) .out x = st i s x := by
  funext k; cases k <;> rfl
@[simp] theorem st_inp (i s o) : st i s o .inp = i := rfl
@[simp] theorem st_sc (i s o) : st i s o .sc = s := rfl
@[simp] theorem st_out (i s o) : st i s o .out = o := rfl

def gB : σ → Bool
  | some (some b) => b
  | _ => false

def stmt : DL → St
  | .a1 => pop .inp (fun _ o => o.map some) (branch (fun s => s.isSome)
      (branch gB (goto fun _ => .a2) (push .sc (fun _ => none) (goto fun _ => .b1)))
      (push .sc (fun _ => none) (goto fun _ => .mv)))
  | .a2 => pop .inp (fun _ o => o.map some) (branch (fun s => s.isSome)
      (branch gB (push .sc (fun _ => some true) (goto fun _ => .a3))
        (push .sc (fun _ => some false) (goto fun _ => .a1)))
      (push .sc (fun _ => none) (goto fun _ => .mv)))
  | .a3 => pop .inp (fun _ o => o.map some) (goto fun _ => .a1)
  | .b1 => pop .inp (fun _ o => o.map some) (branch (fun s => s.isSome)
      (branch gB (goto fun _ => .b2) (goto fun _ => .b1)) (goto fun _ => .mv))
  | .b2 => pop .inp (fun _ o => o.map some) (branch (fun s => s.isSome)
      (branch gB (push .sc (fun _ => some true) (goto fun _ => .b3))
        (push .sc (fun _ => some false) (goto fun _ => .b1)))
      (goto fun _ => .mv))
  | .b3 => pop .inp (fun _ o => o.map some) (goto fun _ => .b1)
  | .mv => pop .sc (fun _ o => o) (branch (fun s => s.isSome)
      (push .out (fun s => s.getD none) (goto fun _ => .mv)) halt)

def tm : FinTM2 where
  K := DK
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := DL
  main := .a1
  σ := σ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt

local notation "F" => flip bind (TM2.step stmt)

theorem run_mv (l o : List (Option Bool)) (v : σ) :
    F^[l.length + 1] (some ⟨some .mv, v, st [] l o⟩) = some ⟨none, none, st [] [] (l.reverse ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [TM2.step, stmt, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .mv, v, st [] (b :: l) o⟩) = some ⟨some .mv, some b, st [] l (b :: o)⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, flip]
    rw [e, ih]; simp

theorem run_b (n : ℕ) : ∀ (z : List Bool), z.length ≤ n → ∀ (v : σ) (s : List (Option Bool)),
    (∃ k ≤ z.length + 2, F^[k] (some ⟨some .b1, v, st z s []⟩) =
      some ⟨some .mv, none, st [] (((pbP z).map some).reverse ++ s) []⟩) := by
  induction n with
  | zero =>
    intro z hz v s
    obtain rfl : z = [] := List.length_eq_zero_iff.1 (by omega)
    exact ⟨1, by simp, by simp [TM2.step, stmt, TM2.stepAux, flip, pbP]⟩
  | succ n ih =>
    intro z hz v s
    rcases z with _ | ⟨b, r⟩
    · exact ⟨1, by simp, by simp [TM2.step, stmt, TM2.stepAux, flip, pbP]⟩
    rcases b
    · obtain ⟨k, hk, h⟩ := ih r (by simp at hz; omega) (some (some false)) s
      refine ⟨k + 1, by simp; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      have e : F (some ⟨some .b1, v, st (false :: r) s []⟩) =
          some ⟨some .b1, some (some false), st r s []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, flip, gB]
      rw [e, h, pbP]
    rcases r with _ | ⟨c, r⟩
    · refine ⟨2, by simp, ?_⟩
      simp [TM2.step, stmt, TM2.stepAux, flip, gB, pbP]
    rcases c
    · obtain ⟨k, hk, h⟩ := ih r (by simp at hz; omega) (some (some false)) (some false :: s)
      refine ⟨k + 2, by simp; omega, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have e : F (F (some ⟨some .b1, v, st (true :: false :: r) s []⟩)) =
          some ⟨some .b1, some (some false), st r (some false :: s) []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, flip, gB]
      rw [e, h, pbP]; simp
    · rcases r with _ | ⟨d, r⟩
      · refine ⟨4, by simp, ?_⟩
        simp [TM2.step, stmt, TM2.stepAux, flip, gB, pbP]
      · obtain ⟨k, hk, h⟩ := ih r (by simp at hz; omega) (some (some d)) (some true :: s)
        refine ⟨k + 3, by simp; omega, ?_⟩
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
        have e : F (F (F (some ⟨some .b1, v, st (true :: true :: d :: r) s []⟩))) =
            some ⟨some .b1, some (some d), st r (some true :: s) []⟩ := by
          simp [TM2.step, stmt, TM2.stepAux, flip, gB]
        rw [e, h, pbP]; simp

theorem run_a (n : ℕ) : ∀ (z : List Bool), z.length ≤ n → ∀ (v : σ) (s : List (Option Bool)),
    (∃ k ≤ z.length + 3, F^[k] (some ⟨some .a1, v, st z s []⟩) =
      some ⟨some .mv, none, st [] ((pairEnc (decP z)).reverse ++ s) []⟩) := by
  induction n with
  | zero =>
    intro z hz v s
    obtain rfl : z = [] := List.length_eq_zero_iff.1 (by omega)
    exact ⟨1, by simp, by simp [TM2.step, stmt, TM2.stepAux, flip, decP, pairEnc]⟩
  | succ n ih =>
    intro z hz v s
    rcases z with _ | ⟨b, r⟩
    · exact ⟨1, by simp, by simp [TM2.step, stmt, TM2.stepAux, flip, decP, pairEnc]⟩
    rcases b
    · obtain ⟨k, hk, h⟩ := run_b r.length r le_rfl (some (some false)) (none :: s)
      refine ⟨k + 1, by simp; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      have e : F (some ⟨some .a1, v, st (false :: r) s []⟩) =
          some ⟨some .b1, some (some false), st r (none :: s) []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, flip, gB]
      rw [e, h, decP]; simp [pairEnc]
    rcases r with _ | ⟨c, r⟩
    · refine ⟨2, by simp, ?_⟩
      simp [TM2.step, stmt, TM2.stepAux, flip, gB, decP, pairEnc]
    rcases c
    · obtain ⟨k, hk, h⟩ := ih r (by simp at hz; omega) (some (some false)) (some false :: s)
      refine ⟨k + 2, by simp; omega, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have e : F (F (some ⟨some .a1, v, st (true :: false :: r) s []⟩)) =
          some ⟨some .a1, some (some false), st r (some false :: s) []⟩ := by
        simp [TM2.step, stmt, TM2.stepAux, flip, gB]
      rw [e, h, decP]; simp [pairEnc]
    · rcases r with _ | ⟨d, r⟩
      · refine ⟨4, by simp, ?_⟩
        simp [TM2.step, stmt, TM2.stepAux, flip, gB, decP, pairEnc]
      · obtain ⟨k, hk, h⟩ := ih r (by simp at hz; omega) (some (some d)) (some true :: s)
        refine ⟨k + 3, by simp; omega, ?_⟩
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
        have e : F (F (F (some ⟨some .a1, v, st (true :: true :: d :: r) s []⟩))) =
            some ⟨some .a1, some (some d), st r (some true :: s) []⟩ := by
          simp [TM2.step, stmt, TM2.stepAux, flip, gB]
        rw [e, h, decP]; simp [pairEnc]

end DecTM

/-- **The decoder**: `strEnc → pairEnc`, computing `decP` (so `codeP a b ↦ a # b`). -/
noncomputable def decComputable : TM2ComputableInPolyTime strEnc pairEnc decP where
  tm := DecTM.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 7
  outputsFun z :=
    have hex : ∃ s ≤ 2 * z.length + 7,
        (flip bind (TM2.step DecTM.stmt))^[s] (some ⟨some .a1, none, DecTM.st z [] []⟩) =
          some ⟨none, none, DecTM.st [] [] (pairEnc (decP z))⟩ := by
      obtain ⟨k, hk, h1⟩ := DecTM.run_a z.length z le_rfl none []
      have h2 := DecTM.run_mv ((pairEnc (decP z)).reverse ++ []) [] none
      have := iter_chain h1 h2
      have hl : (pairEnc (decP z)).length ≤ z.length + 1 := by
        have := decP_len z.length z le_rfl
        simp [pairEnc]; omega
      refine ⟨_, ?_, this.trans (by simp)⟩
      simp; omega
    { steps := Classical.choose hex
      evals_in_steps := by
        have := (Classical.choose_spec hex).2
        have ei : initList DecTM.tm (z : List Bool) =
            (⟨some .a1, none, DecTM.st z [] []⟩ : DecTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList DecTM.tm (pairEnc (decP z)) =
            (⟨none, none, DecTM.st [] [] (pairEnc (decP z))⟩ : DecTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact this
      steps_le_m := by
        have := (Classical.choose_spec hex).1
        simpa [strEnc] using this }

end PvnpReal
