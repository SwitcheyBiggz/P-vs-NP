/-
  PvnpReal.NormalForm — a concrete, encodable machine model `NProg` (stacks, symbols, states and
  labels are natural numbers; all functions are finite tables), its clocked semantics `nrunFor`,
  and a **step-for-step simulation of every `FinTM2`** by an `NProg` (`simulate`).

  This gives a concrete interpreter `U` (code ↦ `NProg` via Mathlib's derived `Encodable`,
  then clocked run) and the theorem `reproduces_U : Reproduces U`: every polynomial-time decider
  is reproduced by `U` on arbitrarily long self-codes. With `Hierarchy.lean` this reduces
  P ≠ EXP to the single statement `InEXP (diagLang U)` (a universal machine), not proven here.
-/
import PvnpReal.Hierarchy
import Mathlib.Tactic.DeriveEncodable

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### The normal-form machine model -/

inductive NStmt
  | push (k : ℕ) (f : List ℕ) (q : NStmt)
  | peek (k : ℕ) (f : List (List ℕ)) (q : NStmt)
  | pop (k : ℕ) (f : List (List ℕ)) (q : NStmt)
  | load (f : List ℕ) (q : NStmt)
  | branch (f : List Bool) (q₁ q₂ : NStmt)
  | goto (f : List ℕ)
  | halt
  deriving Encodable

structure NProg where
  k0 : ℕ
  k1 : ℕ
  main : ℕ
  init : ℕ
  inT : List ℕ
  outT : List Bool
  m : List NStmt
  deriving Encodable

instance : Inhabited NProg := ⟨⟨0, 0, 0, 0, [], [], []⟩⟩

structure NCfg where
  l : Option ℕ
  var : ℕ
  stk : ℕ → List ℕ

def oc : Option ℕ → ℕ
  | none => 0
  | some a => a + 1

def nAux : NStmt → ℕ → (ℕ → List ℕ) → NCfg
  | .push k f q, v, S => nAux q v (Function.update S k (f.getD v 0 :: S k))
  | .peek k f q, v, S => nAux q ((f.getD v []).getD (oc (S k).head?) 0) S
  | .pop k f q, v, S => nAux q ((f.getD v []).getD (oc (S k).head?) 0)
      (Function.update S k (S k).tail)
  | .load f q, v, S => nAux q (f.getD v 0) S
  | .branch f q₁ q₂, v, S => cond (f.getD v false) (nAux q₁ v S) (nAux q₂ v S)
  | .goto f, v, S => ⟨some (f.getD v 0), v, S⟩
  | .halt, v, S => ⟨none, v, S⟩

/-- Clocked run of an `NProg` (first halting configuration within `t` steps). -/
def nrunFor (p : NProg) : ℕ → NCfg → Option NCfg
  | 0, c => if c.l = none then some c else none
  | t + 1, c => match c.l with
    | none => some c
    | some l => nrunFor p t (nAux (p.m.getD l .halt) c.var c.stk)

def NInit (p : NProg) (x : List Bool) : NCfg :=
  ⟨some p.main, p.init, fun j => if j = p.k0 then x.map (fun b => p.inT.getD (if b then 1 else 0) 0)
    else []⟩

/-- **The concrete interpreter**: `x = 1ᵃ 0 1ᴺ 0…` names program `decode N`; run it on `y`
for `t` steps and read the top of its output stack. -/
noncomputable def U (x y : List Bool) (t : ℕ) : Option Bool :=
  let p := (Encodable.decode (α := NProg) (lpN (lpX x))).getD default
  match nrunFor p t (NInit p y) with
  | some c => (c.stk p.k1).head?.map (fun s => p.outT.getD s false)
  | none => none

/-! ### Simulating an arbitrary `FinTM2` -/

def stPushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → List (Σ k, σ → Γ k)
  | .push k f q => ⟨k, f⟩ :: stPushes q
  | .peek _ _ q => stPushes q
  | .pop _ _ q => stPushes q
  | .load _ q => stPushes q
  | .branch _ q₁ q₂ => stPushes q₁ ++ stPushes q₂
  | .goto _ => []
  | .halt => []

theorem ofFn_getD {α : Type*} {n : ℕ} (g : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn g).getD i d = g i := by
  simp [List.getD_eq_getElem?_getD]

theorem range_map_getD {α : Type*} (n : ℕ) (g : ℕ → α) {j : ℕ} (hj : j < n) (d : α) :
    ((List.range n).map g).getD j d = g j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem sig_cast {K : Type} {Γ : K → Type} {k : K} {a : Γ k} {s : Σ k, Γ k} (h : s = ⟨k, a⟩)
    (hk : s.1 = k) : hk ▸ s.2 = a := by
  subst h; rfl

namespace Sim

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

open Classical

variable (tm : FinTM2)

noncomputable def eK : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin _
noncomputable def eΛ : tm.Λ ≃ Fin (Fintype.card tm.Λ) := Fintype.equivFin _
noncomputable def eσ : tm.σ ≃ Fin (Fintype.card tm.σ) := Fintype.equivFin _

noncomputable def allPush : List (Σ k, tm.σ → tm.Γ k) :=
  (Finset.univ : Finset tm.Λ).toList.flatMap (fun l => stPushes (tm.m l))

noncomputable def vals : List (Σ k, tm.Γ k) :=
  (allPush tm).flatMap (fun p => (Finset.univ : Finset tm.σ).toList.map (fun v => ⟨p.1, p.2 v⟩)) ++
    (Finset.univ : Finset (tm.Γ tm.k₀)).toList.map (fun b => ⟨tm.k₀, b⟩)

noncomputable def code (s : Σ k, tm.Γ k) : ℕ := (vals tm).idxOf s

noncomputable def dec (k : tm.K) : ℕ → Option (tm.Γ k)
  | 0 => none
  | i + 1 => if hi : i < (vals tm).length then
      if hk : ((vals tm)[i]).1 = k then some (hk ▸ ((vals tm)[i]).2) else none else none

theorem code_lt {s : Σ k, tm.Γ k} (hs : s ∈ vals tm) : code tm s < (vals tm).length :=
  List.idxOf_lt_length_of_mem hs

theorem dec_code {k : tm.K} {a : tm.Γ k} (hs : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ vals tm) :
    dec tm k (code tm ⟨k, a⟩ + 1) = some a := by
  have hi := code_lt tm hs
  have hg : (vals tm)[code tm ⟨k, a⟩] = ⟨k, a⟩ := List.getElem_idxOf hi
  have hk : ((vals tm)[code tm ⟨k, a⟩]).1 = k := by rw [hg]
  simp only [dec, dif_pos hi, dif_pos hk]
  exact congrArg some (sig_cast hg hk)

noncomputable def tr : TM2.Stmt tm.Γ tm.Λ tm.σ → NStmt
  | .push k f q => .push (eK tm k) (List.ofFn fun i => code tm ⟨k, f ((eσ tm).symm i)⟩) (tr q)
  | .peek k f q => .peek (eK tm k) (List.ofFn fun i => (List.range ((vals tm).length + 1)).map
      fun j => ((eσ tm) (f ((eσ tm).symm i) (dec tm k j)) : ℕ)) (tr q)
  | .pop k f q => .pop (eK tm k) (List.ofFn fun i => (List.range ((vals tm).length + 1)).map
      fun j => ((eσ tm) (f ((eσ tm).symm i) (dec tm k j)) : ℕ)) (tr q)
  | .load a q => .load (List.ofFn fun i => ((eσ tm) (a ((eσ tm).symm i)) : ℕ)) (tr q)
  | .branch f q₁ q₂ => .branch (List.ofFn fun i => f ((eσ tm).symm i)) (tr q₁) (tr q₂)
  | .goto f => .goto (List.ofFn fun i => ((eΛ tm) (f ((eσ tm).symm i)) : ℕ))
  | .halt => .halt

noncomputable def encS (S : ∀ k, List (tm.Γ k)) (j : ℕ) : List ℕ :=
  if h : j < Fintype.card tm.K then (S ((eK tm).symm ⟨j, h⟩)).map (fun a => code tm ⟨_, a⟩) else []

noncomputable def encCfg (c : TM2.Cfg tm.Γ tm.Λ tm.σ) : NCfg :=
  ⟨c.l.map (fun l => ((eΛ tm) l : ℕ)), ((eσ tm) c.var : ℕ), encS tm c.stk⟩

def Inv (S : ∀ k, List (tm.Γ k)) : Prop := ∀ k, ∀ a ∈ S k, (⟨k, a⟩ : Σ k, tm.Γ k) ∈ vals tm

theorem encS_eK (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    encS tm S (eK tm k) = (S k).map (fun a => code tm ⟨k, a⟩) := by
  have hl : ((eK tm k : Fin _) : ℕ) < Fintype.card tm.K := (eK tm k).2
  simp only [encS, dif_pos hl]
  have : (eK tm).symm ⟨(eK tm k : ℕ), hl⟩ = k := by simp
  generalize (eK tm).symm ⟨(eK tm k : ℕ), hl⟩ = k' at this
  subst this; rfl

theorem encS_update (S : ∀ k, List (tm.Γ k)) (k : tm.K) (l : List (tm.Γ k)) :
    encS tm (Function.update S k l) =
      Function.update (encS tm S) (eK tm k) (l.map (fun a => code tm ⟨k, a⟩)) := by
  funext j
  by_cases hj : j = (eK tm k : ℕ)
  · subst hj; rw [Function.update_self, encS_eK, Function.update_self]
  · rw [Function.update_of_ne hj]
    unfold encS
    split
    · next h =>
      have hne : (eK tm).symm ⟨j, h⟩ ≠ k := by
        intro e; apply hj; rw [← e]; simp
      rw [Function.update_of_ne hne]
    · rfl

theorem mem_vals_push {k : tm.K} {f : tm.σ → tm.Γ k} (h : (⟨k, f⟩ : Σ k, tm.σ → tm.Γ k) ∈ allPush tm)
    (v : tm.σ) : (⟨k, f v⟩ : Σ k, tm.Γ k) ∈ vals tm := by
  unfold vals
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨_, h, ?_⟩)
  exact List.mem_map.2 ⟨v, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩

theorem head_enc (S : ∀ k, List (tm.Γ k)) (hS : Inv tm S) (k : tm.K) :
    oc (encS tm S (eK tm k)).head? < (vals tm).length + 1 ∧
    dec tm k (oc (encS tm S (eK tm k)).head?) = (S k).head? := by
  rw [encS_eK]
  cases hk : S k with
  | nil => exact ⟨by simp [oc], by simp [oc, dec]⟩
  | cons a r =>
    have hm : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ vals tm := hS k a (by rw [hk]; simp)
    refine ⟨by simp [oc]; exact code_lt tm hm, ?_⟩
    simp only [List.map_cons, List.head?_cons, oc]
    exact dec_code tm hm

theorem sim (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : ∀ p ∈ stPushes q, p ∈ allPush tm)
    (v : tm.σ) (S : ∀ k, List (tm.Γ k)) (hS : Inv tm S) :
    nAux (tr tm q) ((eσ tm) v) (encS tm S) = encCfg tm (TM2.stepAux q v S) ∧
      Inv tm (TM2.stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
    have hk : (⟨k, f⟩ : Σ k, tm.σ → tm.Γ k) ∈ allPush tm := hq _ (by simp [stPushes])
    have hS' : Inv tm (Function.update S k (f v :: S k)) := by
      intro k' a ha
      by_cases e : k' = k
      · subst e
        rw [Function.update_self] at ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact mem_vals_push tm hk v
        · exact hS _ a ha
      · rw [Function.update_of_ne e] at ha; exact hS _ a ha
    have := ih (fun p hp => hq p (by simp [stPushes, hp])) v _ hS'
    simp only [tr, nAux, TM2.stepAux]
    rw [ofFn_getD, Equiv.symm_apply_apply, encS_eK, ← this.1, encS_update]
    exact ⟨by simp, this.2⟩
  | peek k f q ih =>
    obtain ⟨h1, h2⟩ := head_enc tm S hS k
    have := ih hq (f v (S k).head?) S hS
    simp only [tr, nAux, TM2.stepAux]
    rw [ofFn_getD, Equiv.symm_apply_apply, range_map_getD _ _ h1, h2]
    exact this
  | pop k f q ih =>
    obtain ⟨h1, h2⟩ := head_enc tm S hS k
    have hS' : Inv tm (Function.update S k (S k).tail) := by
      intro k' a ha
      by_cases e : k' = k
      · subst e
        rw [Function.update_self] at ha
        exact hS _ a (List.mem_of_mem_tail ha)
      · rw [Function.update_of_ne e] at ha; exact hS _ a ha
    have := ih hq (f v (S k).head?) _ hS'
    simp only [tr, nAux, TM2.stepAux]
    rw [ofFn_getD, Equiv.symm_apply_apply, range_map_getD _ _ h1, h2, ← this.1, encS_update,
      encS_eK]
    exact ⟨by simp [List.map_tail], this.2⟩
  | load a q ih =>
    have := ih hq (a v) S hS
    simp only [tr, nAux, TM2.stepAux]
    rw [ofFn_getD, Equiv.symm_apply_apply]
    exact this
  | branch f q₁ q₂ ih₁ ih₂ =>
    have a1 := ih₁ (fun p hp => hq p (by simp [stPushes, hp])) v S hS
    have a2 := ih₂ (fun p hp => hq p (by simp [stPushes, hp])) v S hS
    simp only [tr, nAux, TM2.stepAux]
    rw [ofFn_getD, Equiv.symm_apply_apply]
    cases f v <;> simpa using ‹_›
  | goto f =>
    simp only [tr, nAux, TM2.stepAux]
    rw [ofFn_getD, Equiv.symm_apply_apply]
    exact ⟨rfl, hS⟩
  | halt => exact ⟨rfl, hS⟩

/-- The `NProg` simulating `tm` (with given input/output alphabet identifications). -/
noncomputable def prog (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) : NProg where
  k0 := eK tm tm.k₀
  k1 := eK tm tm.k₁
  main := eΛ tm tm.main
  init := eσ tm tm.initialState
  inT := [code tm ⟨tm.k₀, ia.symm false⟩, code tm ⟨tm.k₀, ia.symm true⟩]
  outT := (List.range (vals tm).length).map (fun i => ((dec tm tm.k₁ (i + 1)).map oa).getD false)
  m := List.ofFn fun i => tr tm (tm.m ((eΛ tm).symm i))

theorem pushes_main (l : tm.Λ) : ∀ p ∈ stPushes (tm.m l), p ∈ allPush tm := fun p hp =>
  List.mem_flatMap.2 ⟨l, Finset.mem_toList.2 (Finset.mem_univ _), hp⟩

/-- **Simulation**: clocked runs of `tm` are mirrored exactly by the clocked runs of `prog`. -/
theorem simulate (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (t : ℕ) :
    ∀ (c h : TM2.Cfg tm.Γ tm.Λ tm.σ), Inv tm c.stk → runFor tm.m t c = some h →
      nrunFor (prog tm ia oa) t (encCfg tm c) = some (encCfg tm h) ∧ Inv tm h.stk := by
  induction t with
  | zero =>
    rintro ⟨cl, v, S⟩ h hc e
    cases cl with
    | none => simp [runFor] at e; subst e; exact ⟨by simp [nrunFor, encCfg], hc⟩
    | some l => simp [runFor] at e
  | succ t ih =>
    rintro ⟨cl, v, S⟩ h hc e
    cases cl with
    | none => simp [runFor] at e; subst e; exact ⟨by simp [nrunFor, encCfg], hc⟩
    | some l =>
      simp only [runFor, TM2.step, Option.bind_some] at e
      obtain ⟨s1, s2⟩ := sim tm (tm.m l) (pushes_main tm l) v S hc
      obtain ⟨r1, r2⟩ := ih _ h s2 e
      refine ⟨?_, r2⟩
      simp only [encCfg, Option.map_some, nrunFor]
      have hm : (prog tm ia oa).m.getD ((eΛ tm) l : ℕ) .halt = tr tm (tm.m l) := by
        simp only [prog]; rw [ofFn_getD, Equiv.symm_apply_apply]
      rw [hm]
      have := s1; simp only [encCfg] at this ⊢
      rw [this]; exact r1

theorem init_enc (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (x : List Bool) :
    encCfg tm (initList tm (x.map ia.invFun)) = NInit (prog tm ia oa) x ∧
      Inv tm (initList tm (x.map ia.invFun)).stk := by
  have hstk : ∀ k, (initList tm (x.map ia.invFun)).stk k =
      if h : k = tm.k₀ then h ▸ x.map ia.invFun else [] := by
    intro k; simp only [initList]; split
    · next h => subst h; rfl
    · rfl
  constructor
  · unfold encCfg NInit
    congr 1
    funext j
    by_cases hj : j = (eK tm tm.k₀ : ℕ)
    · subst hj
      rw [if_pos (show ((eK tm tm.k₀ : ℕ)) = (prog tm ia oa).k0 from rfl), encS_eK, hstk,
        dif_pos rfl]
      simp only [List.map_map]
      congr 1; funext b; cases b <;> rfl
    · rw [if_neg (show ¬ j = (prog tm ia oa).k0 from hj)]
      unfold encS
      split
      · next h =>
        have hne : (eK tm).symm ⟨j, h⟩ ≠ tm.k₀ := by
          intro e; apply hj; rw [← e]; simp
        rw [hstk, dif_neg hne]; rfl
      · rfl
  · intro k a ha
    rw [hstk] at ha
    split at ha
    · next h =>
      subst h
      unfold vals
      exact List.mem_append_right _ (List.mem_map.2 ⟨a, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩)
    · simp at ha

theorem halt_out (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (b : Bool)
    (hI : Inv tm (haltList tm [oa.invFun b]).stk) :
    ((encCfg tm (haltList tm [oa.invFun b])).stk (prog tm ia oa).k1).head?.map
      (fun s => (prog tm ia oa).outT.getD s false) = some b := by
  have hk : (haltList tm [oa.invFun b]).stk tm.k₁ = [oa.invFun b] := by
    unfold haltList; dsimp only; rw [dif_pos rfl]; rfl
  have hm : (⟨tm.k₁, oa.invFun b⟩ : Σ k, tm.Γ k) ∈ vals tm := hI _ _ (by rw [hk]; simp)
  simp only [encCfg, prog]
  rw [encS_eK, hk]
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.map_some]
  rw [range_map_getD _ _ (code_lt tm hm), dec_code tm hm]
  simp

end Sim

/-- **`U` reproduces every polynomial-time decider** (on the self-codes `1ᵃ 0 1^{code} 0`). -/
theorem reproduces_U : Reproduces U := by
  intro f ⟨h⟩
  refine ⟨h.time, fun n0 => ?_⟩
  let p := Sim.prog h.tm h.inputAlphabet h.outputAlphabet
  let x : List Bool := List.replicate n0 true ++ false ::
    (List.replicate (Encodable.encode p) true ++ [false])
  refine ⟨x, by simp [x], fun t ht => ?_⟩
  have hp : (Encodable.decode (α := NProg) (lpN (lpX x))).getD default = p := by
    simp only [x, lpX_rep, lpN_rep, Encodable.encodek, Option.getD_some]
  have hr := runFor_computable h.toTM2ComputableInTime x
  have hr' := runFor_mono h.tm.m (show h.toTM2ComputableInTime.time (strEnc x).length ≤ t from ht) hr
  obtain ⟨i1, i2⟩ := Sim.init_enc h.tm h.inputAlphabet h.outputAlphabet x
  obtain ⟨s1, s2⟩ := Sim.simulate h.tm h.inputAlphabet h.outputAlphabet t _ _ i2 hr'
  have s1' : nrunFor p t (NInit p x) = some (Sim.encCfg h.tm
      (haltList h.tm [h.outputAlphabet.invFun (f x)])) := by
    rw [← i1]; exact s1
  unfold U
  simp only [hp]
  rw [s1']
  exact Sim.halt_out h.tm h.inputAlphabet h.outputAlphabet (f x) s2

/-- **P ≠ EXP is reduced to one concrete statement**: the exponentially clocked diagonal of the
concrete interpreter `U` is in EXP. (Not proven: it needs a universal `FinTM2` for `NProg`.) -/
theorem P_ne_EXP_of_diagU_in_EXP (hE : InEXP (diagLang U)) : P_ne_EXP :=
  P_ne_EXP_of_universal reproduces_U hE

end PvnpReal
