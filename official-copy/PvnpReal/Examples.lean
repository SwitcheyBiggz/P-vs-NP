/-
  PvnpReal.Examples — concrete Turing machines, run step by step, showing that the
  classes P and NP defined in `PvnpReal.Complexity` are not vacuous.

  `constMachine α b` is a real two-stack Mathlib `FinTM2`: it pops its whole input
  (over alphabet `α`) one symbol per step, then writes `b` on the output stack and halts.
  On input of length `n` it halts in exactly `n + 1` steps.
-/
import PvnpReal.Complexity

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

/-- Stack alphabets: stack `false` is the input stack (alphabet `α`),
stack `true` is the output stack (alphabet `Bool`). -/
abbrev cmΓ (α : Type) : Bool → Type := fun k => cond k Bool α

/-- The single instruction of the machine:
pop one input symbol into the state; if something was popped loop, otherwise
write `b` to the output stack and halt. -/
def cmStmt (α : Type) (b : Bool) : TM2.Stmt (cmΓ α) Unit (Option α) :=
  pop false (fun _ o => o)
    (branch (fun s => s.isSome) (goto fun _ => ())
      (push true (fun _ => b) halt))

def constMachine (α : Type) [Fintype α] (b : Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := cmΓ α
  Λ := Unit
  main := ()
  σ := Option α
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype α)
  m := fun _ => cmStmt α b

/-- Initial stacks: input `l`, output empty. -/
def inStk {α : Type} (l : List α) : ∀ k, List (cmΓ α k)
  | false => l
  | true => []

/-- Final stacks: input empty, output `[b]`. -/
def outStk (α : Type) (b : Bool) : ∀ k, List (cmΓ α k)
  | false => []
  | true => [b]

theorem cm_step_some (α : Type) (b : Bool) (a : α) (l : List α) (v : Option α)
    (S : ∀ k, List (cmΓ α k)) (h0 : S false = a :: l) :
    TM2.step (fun _ : Unit => cmStmt α b) ⟨some (), v, S⟩ =
      some ⟨some (), some a, Function.update S false l⟩ := by
  simp only [TM2.step, cmStmt, TM2.stepAux]
  rw [h0]
  rfl

theorem cm_step_none (α : Type) (b : Bool) (v : Option α)
    (S : ∀ k, List (cmΓ α k)) (h0 : S false = []) (h1 : S true = []) :
    TM2.step (fun _ : Unit => cmStmt α b) ⟨some (), v, S⟩ =
      some ⟨none, none, outStk α b⟩ := by
  simp only [TM2.step, cmStmt, TM2.stepAux]
  rw [h0]
  simp only [List.head?_nil, Option.isSome_none, List.tail_nil, Bool.cond_false]
  congr 2
  funext k
  cases k
  · simp [Function.update, h0, outStk]
  · simp [Function.update, h1, outStk]

/-- Running the machine on any configuration with input stack `l` and empty output stack:
after `l.length + 1` steps it halts with output `[b]` and an empty input stack. -/
theorem constMachine_run (α : Type) (b : Bool) (l : List α) (v : Option α)
    (S : ∀ k, List (cmΓ α k)) (h0 : S false = l) (h1 : S true = []) :
    (flip bind (TM2.step (fun _ : Unit => cmStmt α b)))^[l.length + 1]
        (some ⟨some (), v, S⟩) = some ⟨none, none, outStk α b⟩ := by
  induction l generalizing v S with
  | nil =>
    simp only [List.length_nil, zero_add, Function.iterate_one]
    exact cm_step_none α b v S h0 h1
  | cons a l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step (fun _ : Unit => cmStmt α b)) (some ⟨some (), v, S⟩) =
        some ⟨some (), some a, Function.update S false l⟩ :=
      cm_step_some α b a l v S h0
    rw [hstep]
    exact ih _ _ (by simp) (by simp [Function.update, h1])

theorem haltList_constMachine (α : Type) [Fintype α] (b : Bool) :
    haltList (constMachine α b) (List.map (Equiv.refl Bool).invFun (encodeBool b)) =
      ⟨none, none, outStk α b⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

theorem initList_constMachine (α : Type) [Fintype α] (b : Bool) (l : List α) :
    initList (constMachine α b) (List.map (Equiv.refl α).invFun l) =
      ⟨some (), none, inStk l⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k
  · exact List.map_id l
  · rfl

/-- The constant function `fun _ => b` on inputs encoded by `e` is computable in
polynomial time (time polynomial `X + 1`). -/
noncomputable def constComputable {β α : Type} [Fintype α] (e : β → List α) (b : Bool) :
    TM2ComputableInPolyTime e encodeBool (fun _ => b) where
  tm := constMachine α b
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a :=
    { steps := (e a).length + 1
      evals_in_steps := by
        have := constMachine_run α b (e a) none (inStk (e a)) rfl rfl
        erw [initList_constMachine α b (e a), Option.map_some, haltList_constMachine α b]
        exact this
      steps_le_m := by simp }

/-- The language of all strings is in P (decided by a real machine). -/
theorem univ_in_P : InP (fun _ => True) :=
  ⟨fun _ => true, ⟨constComputable strEnc true⟩, fun _ => by simp⟩

/-- The empty language is in P. -/
theorem empty_in_P : InP (fun _ => False) :=
  ⟨fun _ => false, ⟨constComputable strEnc false⟩, fun _ => by simp⟩

/-- The language of all strings is in NP (verifier reads `x # w` and accepts). -/
theorem univ_in_NP : InNP (fun _ => True) :=
  ⟨fun _ => true, 0, ⟨constComputable pairEnc true⟩,
    fun _ => by simp⟩

/-- The empty language is in NP. -/
theorem empty_in_NP : InNP (fun _ => False) :=
  ⟨fun _ => false, 0, ⟨constComputable pairEnc false⟩, fun _ => by simp⟩

/-- The two constant machines really compute different things, so InP is not a
"one machine fits all" definition like v76's. -/
theorem constMachines_differ : (fun _ : List Bool => true) ≠ (fun _ => false) := by
  intro h; simpa using congrFun h []

end PvnpReal
