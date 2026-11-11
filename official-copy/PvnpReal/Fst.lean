/-
  PvnpReal.Fst — finite-state transducers (Mealy machines with a final output) are polynomial-time:
  a `FinTM2` that reads the input once, pushing `(δ q b).2` per symbol and `fin q` at the end, then
  reverses. `fstComputable : PS (fstOut δ fin q₀)`.
-/
import PvnpReal.EncTM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

/-- Output of the transducer from state `q` on input `l`. -/
def fstOut {Q : Type} (δ : Q → Bool → Q × List Bool) (fin : Q → List Bool) : Q → List Bool → List Bool
  | q, [] => fin q
  | q, b :: r => (δ q b).2 ++ fstOut δ fin (δ q b).1 r

namespace FstTM

open TM2.Stmt EncTM

variable {Q : Type} [Fintype Q] [DecidableEq Q] [Inhabited Q]

abbrev Γf : EK → Type
  | _ => Bool

abbrev σf := Option (Option Bool)
abbrev Stf (Q : Type) := TM2.Stmt Γf (Option Q) σf

def stf (i s o : List Bool) : ∀ k : EK, List (Γf k)
  | .inp => i
  | .sc => s
  | .out => o

@[simp] theorem upd_inp (i s o x) : Function.update (stf i s o) .inp x = stf x s o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_sc (i s o x) : Function.update (stf i s o) .sc x = stf i x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i s o x) : Function.update (stf i s o) .out x = stf i s x := by
  funext k; cases k <;> rfl
@[simp] theorem st_inp (i s o) : stf i s o .inp = i := rfl
@[simp] theorem st_sc (i s o) : stf i s o .sc = s := rfl
@[simp] theorem st_out (i s o) : stf i s o .out = o := rfl

def pushF : List Bool → Stf Q → Stf Q
  | [], k => k
  | b :: l, k => push .sc (fun _ => b) (pushF l k)

theorem stepAux_pushF (l : List Bool) (k : Stf Q) (v : σf) (i s o : List Bool) :
    TM2.stepAux (pushF l k) v (stf i s o) = TM2.stepAux k v (stf i (l.reverse ++ s) o) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp [pushF, TM2.stepAux, ih]

variable (δ : Q → Bool → Q × List Bool) (fin : Q → List Bool)

def stmt : Option Q → Stf Q
  | some q => pop .inp (fun _ o => o.map some) (branch (fun s => s.isSome)
      (branch gB (pushF (δ q true).2 (goto fun _ => some (δ q true).1))
        (pushF (δ q false).2 (goto fun _ => some (δ q false).1)))
      (pushF (fin q) (goto fun _ => none)))
  | none => pop .sc (fun _ o => o.map some) (branch (fun s => s.isSome)
      (push .out (fun s => gB s) (goto fun _ => none)) halt)

def tm (q₀ : Q) : FinTM2 where
  K := EK
  k₀ := .inp
  k₁ := .out
  Γ := Γf
  Λ := Option Q
  main := some q₀
  σ := σf
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt δ fin

local notation "F" => flip bind (TM2.step (stmt δ fin))

theorem run_mv (l o : List Bool) (v : σf) :
    F^[l.length + 1] (some ⟨some none, v, stf [] l o⟩) = some ⟨none, none, stf [] [] (l.reverse ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [TM2.step, stmt, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some none, v, stf [] (b :: l) o⟩) =
        some ⟨some none, some (some b), stf [] l (b :: o)⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, flip, gB]
    rw [e, ih]; simp

theorem run_in (x : List Bool) (q : Q) (s : List Bool) (v : σf) :
    F^[x.length + 1] (some ⟨some (some q), v, stf x s []⟩) =
      some ⟨some none, none, stf [] ((fstOut δ fin q x).reverse ++ s) []⟩ := by
  induction x generalizing q s v with
  | nil => simp [TM2.step, stmt, TM2.stepAux, flip, stepAux_pushF, fstOut]
  | cons b x ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some (some q), v, stf (b :: x) s []⟩) =
        some ⟨some (some (δ q b).1), some (some b), stf x ((δ q b).2.reverse ++ s) []⟩ := by
      cases b <;> simp [TM2.step, stmt, TM2.stepAux, flip, gB, stepAux_pushF]
    rw [e, ih]; simp [fstOut]

theorem fstOut_len (C : ℕ) (hδ : ∀ q b, (δ q b).2.length ≤ C) (hf : ∀ q, (fin q).length ≤ C) :
    ∀ (x : List Bool) (q : Q), (fstOut δ fin q x).length ≤ C * (x.length + 1) := by
  intro x
  induction x with
  | nil => intro q; simpa [fstOut] using hf q
  | cons b x ih =>
    intro q
    have := ih (δ q b).1; have := hδ q b
    simp only [fstOut, List.length_append, List.length_cons]; nlinarith

end FstTM

/-- **Finite-state transducers are polynomial-time.** -/
theorem fstComputable {Q : Type} [Fintype Q] [DecidableEq Q] [Inhabited Q]
    (δ : Q → Bool → Q × List Bool) (fin : Q → List Bool) (q₀ : Q) :
    PS (fstOut δ fin q₀) := by
  classical
  obtain ⟨C, hδ, hf⟩ : ∃ C, (∀ q b, (δ q b).2.length ≤ C) ∧ ∀ q, (fin q).length ≤ C := by
    refine ⟨(Finset.univ.sup fun p : Q × Bool => (δ p.1 p.2).2.length) +
      Finset.univ.sup fun q => (fin q).length, fun q b => ?_, fun q => ?_⟩
    · have := Finset.le_sup (f := fun p : Q × Bool => (δ p.1 p.2).2.length) (Finset.mem_univ (q, b))
      exact le_trans this (Nat.le_add_right _ _)
    · have := Finset.le_sup (f := fun q : Q => (fin q).length) (Finset.mem_univ q)
      exact le_trans this (Nat.le_add_left _ _)
  exact ⟨{
    tm := FstTM.tm δ fin q₀
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C (C + 1) * Polynomial.X + Polynomial.C (C + 3)
    outputsFun := fun x =>
      { steps := x.length + 1 + ((fstOut δ fin q₀ x).length + 1)
        evals_in_steps := by
          have h1 := FstTM.run_in δ fin x q₀ [] none
          have h2 := FstTM.run_mv δ fin ((fstOut δ fin q₀ x).reverse ++ []) [] none
          have e := iter_chain h1 h2
          simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at e
          have ei : initList (FstTM.tm δ fin q₀) x =
              (⟨some (some q₀), none, FstTM.stf x [] []⟩ : TM2.Cfg FstTM.Γf (Option Q) FstTM.σf) := by
            simp only [initList]; congr 1; funext k; cases k <;> rfl
          have eh : haltList (FstTM.tm δ fin q₀) (fstOut δ fin q₀ x) =
              (⟨none, none, FstTM.stf [] [] (fstOut δ fin q₀ x)⟩ : TM2.Cfg FstTM.Γf (Option Q) FstTM.σf) := by
            simp only [haltList]; congr 1; funext k; cases k <;> rfl
          erw [List.map_id, List.map_id, Option.map_some, ei, eh]
          first | exact e | (rw [Nat.add_comm]; exact e)
        steps_le_m := by
          have := FstTM.fstOut_len δ fin C hδ hf x q₀
          simp only [strEnc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
            Polynomial.eval_C]
          nlinarith } }⟩

end PvnpReal
