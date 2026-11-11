/-
  PvnpReal.OracleP — sanity check for the oracle model: **`P ⊆ P^A` for every oracle `A`**.
  A Mathlib `FinTM2` decider becomes an `NProg` (`Sim.prog`), embedded as an oracle program
  with no queries (`emb0`); its runs are oracle-independent and equal to the `nrunFor` runs.
-/
import PvnpReal.OracleEq

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Classical

namespace OSim

/-- Embed an `NProg` tree as an oracle tree with no queries. -/
def emb0 : NStmt → OStmt
  | .push k f q => .push k f (emb0 q)
  | .peek k f q => .peek k f (emb0 q)
  | .pop k f q => .pop k f (emb0 q)
  | .load f q => .load f (emb0 q)
  | .branch f q₁ q₂ => .branch f (emb0 q₁) (emb0 q₂)
  | .goto f => .goto f
  | .halt => .halt

theorem emb0_aux (A : List Bool → Prop) (q : NStmt) : ∀ v S, oAux A (emb0 q) v S = nAux q v S := by
  induction q with
  | push k f q ih => intro v S; simp only [emb0, oAux, nAux]; exact ih _ _
  | peek k f q ih => intro v S; simp only [emb0, oAux, nAux]; exact ih _ _
  | pop k f q ih => intro v S; simp only [emb0, oAux, nAux]; exact ih _ _
  | load f q ih => intro v S; simp only [emb0, oAux, nAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [emb0, oAux, nAux]
    rcases Bool.eq_false_or_eq_true (f.getD v false) with hb | hb
    · simp only [hb, cond_true]; exact ih₁ _ _
    · simp only [hb, cond_false]; exact ih₂ _ _
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

/-- The query-free oracle program of an `NProg`. -/
def ofN (p : NProg) : OProg :=
  ⟨p.k0, p.k0, p.k1, p.main, p.init, p.inT, p.outT, p.m.map emb0⟩

theorem orun_ofN (A : List Bool → Prop) (p : NProg) :
    ∀ t c, orunFor A (ofN p) t c = nrunFor p t c := by
  intro t
  induction t with
  | zero => intro c; rfl
  | succ t ih =>
    rintro ⟨l, v, S⟩
    cases l with
    | none => rfl
    | some l =>
      simp only [orunFor, nrunFor]
      rw [show (ofN p).m.getD l .halt = emb0 (p.m.getD l .halt) from
        List.getD_map emb0 (l := p.m) (d := .halt), emb0_aux]
      exact ih _

theorem OInit_ofN (p : NProg) (x : List Bool) : OInit (ofN p) x [] = NInit p x := by
  simp only [OInit, NInit, ofN]
  congr 1
  funext j
  by_cases hj : j = p.k0 <;> simp [hj]

end OSim

open OSim

/-- **`P ⊆ P^A` for every oracle `A`.** -/
theorem P_sub_PO (A L : Language) (hL : InP L) : InPO A L := by
  obtain ⟨f, ⟨h⟩, hf⟩ := hL
  let p := Sim.prog h.tm h.inputAlphabet h.outputAlphabet
  refine ⟨ofN p, h.time, fun x => ?_⟩
  have hr := runFor_computable h.toTM2ComputableInTime x
  obtain ⟨i1, i2⟩ := Sim.init_enc h.tm h.inputAlphabet h.outputAlphabet x
  obtain ⟨s1, s2⟩ := Sim.simulate h.tm h.inputAlphabet h.outputAlphabet _ _ _ i2 hr
  rw [i1] at s1
  refine ⟨_, by rw [OInit_ofN, orun_ofN]; exact s1, ?_⟩
  rw [hf x]
  have hb := Sim.halt_out h.tm h.inputAlphabet h.outputAlphabet (f x) s2
  unfold OAccepts
  rw [show (ofN p).ka = p.k1 from rfl, show (ofN p).accT = p.outT from rfl]
  have hb' : ((Sim.encCfg h.tm (haltList h.toTM2ComputableInTime.tm
      (List.map h.toTM2ComputableInTime.outputAlphabet.invFun (encodeBool (f x))))).stk p.k1).head?.map
      (fun s => p.outT.getD s false) = some (f x) := hb
  rw [hb']
  simp

end PvnpReal
