/-
  PvnpReal.CookLevinTab — instantiating the tableau (`Tableau.lean`) for an NP verifier given as a
  Mathlib `FinTM2`: step and space bounds, a finite value list covering the run, and the link
  between halt-and-stay runs and Mathlib's `EvalsToInTime`.
-/
import PvnpReal.Tableau
import PvnpReal.Compose

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

section Run

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (m : Λ → Stmt Γ Λ σ)

/-- A halting run reached by Mathlib's `flip bind step` iteration is also reached, and then kept,
by the halt-and-stay iteration. -/
theorem stepStay_of_evals (n : ℕ) (c h : Cfg Γ Λ σ) (hh : h.l = none)
    (hrun : (flip bind (TM2.step m))^[n] (some c) = some h) :
    ∀ N, n ≤ N → (stepStay m)^[N] c = h := by
  induction n generalizing c with
  | zero =>
    simp only [Function.iterate_zero, id, Option.some.injEq] at hrun
    subst hrun
    intro N _
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply']
      rw [ih (Nat.zero_le _)]
      obtain ⟨l, v, S⟩ := c; simp only at hh; subst hh; rfl
  | succ n ih =>
    intro N hN
    rw [Function.iterate_succ_apply] at hrun
    rcases hcs : TM2.step m c with _ | c'
    · change (flip bind (TM2.step m))^[n] (TM2.step m c) = some h at hrun
      rw [hcs, flip_bind_iterate_none] at hrun; cases hrun
    · change (flip bind (TM2.step m))^[n] (TM2.step m c) = some h at hrun
      rw [hcs] at hrun
      obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      have : stepStay m c = c' := by simp [stepStay, hcs]
      rw [this]
      exact ih c' hrun N (by omega)

/-- Symbols a statement can push. -/
def pushSyms (vs : List σ) : Stmt Γ Λ σ → List (Sig Γ)
  | Stmt.push k f q => vs.map (fun v => ⟨k, f v⟩) ++ pushSyms vs q
  | Stmt.peek _ _ q => pushSyms vs q
  | Stmt.pop _ _ q => pushSyms vs q
  | Stmt.load _ q => pushSyms vs q
  | Stmt.branch _ q₁ q₂ => pushSyms vs q₁ ++ pushSyms vs q₂
  | Stmt.goto _ => []
  | Stmt.halt => []

/-- All stack symbols lie in `L`. -/
def SymsIn (L : List (Sig Γ)) (S : ∀ k, List (Γ k)) : Prop := ∀ k, ∀ g ∈ S k, (⟨k, g⟩ : Sig Γ) ∈ L

theorem stepAux_syms (vs : List σ) (hvs : ∀ v, v ∈ vs) (L : List (Sig Γ)) (q : Stmt Γ Λ σ)
    (hq : ∀ x ∈ pushSyms vs q, x ∈ L) (v : σ) (S : ∀ k, List (Γ k)) (hS : SymsIn L S) :
    SymsIn L (stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [pushSyms, List.mem_append, List.mem_map] at hq
    simp only [stepAux]
    refine ih (fun x hx => hq x (Or.inr hx)) _ _ (fun k' g hg => ?_)
    by_cases hk : k' = k
    · subst hk
      simp only [Function.update_self, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hq _ (Or.inl ⟨v, hvs v, rfl⟩)
      · exact hS k' g hg
    · rw [Function.update_of_ne hk] at hg; exact hS k' g hg
  | peek k f q ih => exact ih hq _ _ hS
  | pop k f q ih =>
    simp only [stepAux]
    refine ih hq _ _ (fun k' g hg => ?_)
    by_cases hk : k' = k
    · subst hk
      simp only [Function.update_self] at hg
      exact hS k' g (List.mem_of_mem_tail hg)
    · rw [Function.update_of_ne hk] at hg; exact hS k' g hg
  | load a q ih => exact ih hq _ _ hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [pushSyms, List.mem_append] at hq
    simp only [stepAux]
    cases f v
    · exact ih₂ (fun x hx => hq x (Or.inr hx)) _ _ hS
    · exact ih₁ (fun x hx => hq x (Or.inl hx)) _ _ hS
  | goto f => exact hS
  | halt => exact hS

theorem stepStay_syms (vs : List σ) (hvs : ∀ v, v ∈ vs) (L : List (Sig Γ))
    (hm : ∀ lab, ∀ x ∈ pushSyms vs (m lab), x ∈ L) (c : Cfg Γ Λ σ) (hc : SymsIn L c.stk) :
    SymsIn L (stepStay m c).stk := by
  obtain ⟨_ | lab, v, S⟩ := c
  · exact hc
  · exact stepAux_syms vs hvs L (m lab) (hm lab) v S hc

theorem stepStay_len (c : Cfg Γ Λ σ) (B P : ℕ) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hc : ∀ k, (c.stk k).length ≤ B) : ∀ k, ((stepStay m c).stk k).length ≤ B + P := by
  obtain ⟨_ | lab, v, S⟩ := c
  · intro k; have := hc k; simp only [stepStay, TM2.step, Option.getD_none] at *; omega
  · intro k
    have := stepAux_len (m lab) v S B hc k
    have := hP lab
    simp only [stepStay, TM2.step, Option.getD_some]
    omega

theorem iterate_stepStay_len (c : Cfg Γ Λ σ) (B P : ℕ) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hc : ∀ k, (c.stk k).length ≤ B) (t : ℕ) :
    ∀ k, (((stepStay m)^[t] c).stk k).length ≤ B + P * t := by
  induction t with
  | zero => simpa using hc
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    intro k
    have := stepStay_len m _ (B + P * t) P hP ih k
    rw [Nat.mul_succ]; omega


/-! ### A value list covering every run -/

/-- All lists of length `≤ d` with entries from `L`. -/
def upTo {α : Type*} (L : List α) (d : ℕ) : List (List α) :=
  (List.range (d + 1)).flatMap (tuples L)

theorem mem_upTo {α : Type*} (L : List α) (d : ℕ) (l : List α) :
    l ∈ upTo L d ↔ l.length ≤ d ∧ ∀ x ∈ l, x ∈ L := by
  simp only [upTo, List.mem_flatMap, List.mem_range, mem_tuples]
  constructor
  · rintro ⟨r, hr, rfl, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨h1, h2⟩; exact ⟨l.length, by omega, rfl, h2⟩

variable [Fintype K] [Fintype Λ] [Fintype σ]

/-- The finite set of tableau values: summaries with lengths `≤ S` and windows over `L`, the
symbols of `L`, and a default value `u0`. -/
noncomputable def tabValues (d S : ℕ) (L : List (Sig Γ)) (u0 : TVal Γ Λ σ) : List (TVal Γ Λ σ) :=
  (((Finset.univ : Finset (Option Λ)) ×ˢ (Finset.univ : Finset σ) ×ˢ
      Fintype.piFinset (fun _ : K => Finset.range (S + 1)) ×ˢ
      Fintype.piFinset (fun _ : K => (upTo L d).toFinset)).image
      (fun p => (Sum.inl ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : TVal Γ Λ σ)) ∪
    (L.map Sum.inr).toFinset ∪ {u0}).toList

theorem u0_mem_tabValues (d S : ℕ) (L : List (Sig Γ)) (u0 : TVal Γ Λ σ) :
    u0 ∈ tabValues d S L u0 := by
  simp [tabValues]

theorem tabValues_cover (d S : ℕ) (L : List (Sig Γ)) (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ)
    (hL : SymsIn L c.stk) (hS : ∀ k, (c.stk k).length ≤ S) :
    (Sum.inl (summOf d c) : TVal Γ Λ σ) ∈ tabValues d S L u0 ∧
      ∀ k (i : ℕ) g, (c.stk k).reverse[i]? = some g →
        (Sum.inr ⟨k, g⟩ : TVal Γ Λ σ) ∈ tabValues d S L u0 := by
  constructor
  · simp only [tabValues, Finset.mem_toList, Finset.mem_union, Finset.mem_image]
    refine Or.inl (Or.inl ⟨(c.l, c.var, fun k => (c.stk k).length,
      fun k => toSig k ((c.stk k).take d)), ?_, rfl⟩)
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_range, List.mem_toFinset, mem_upTo]
    refine ⟨fun k => by have := hS k; omega, fun k => ⟨by simp [toSig], fun x hx => ?_⟩⟩
    simp only [toSig, List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hL k g (List.mem_of_mem_take hg)
  · intro k i g hg
    simp only [tabValues, Finset.mem_toList, Finset.mem_union, List.mem_toFinset, List.mem_map]
    refine Or.inl (Or.inr ⟨⟨k, g⟩, hL k g ?_, rfl⟩)
    exact List.mem_reverse.1 (List.mem_of_getElem? hg)

end Run


/-! ### The tableau for an NP verifier -/

section Verifier

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {V : List Bool × List Bool → Bool} (q : Polynomial ℕ)
  (h : TM2ComputableInPolyTime pairEnc encodeBool V)

/-- Window depth: the largest `sdepth` in the program. -/
noncomputable def clD (M : FinTM2) : ℕ := Finset.univ.sup (fun l => sdepth (M.m l))

noncomputable def clKs (M : FinTM2) : List M.K := Finset.univ.toList

/-- Every stack symbol a run can ever see. -/
noncomputable def clL (M : FinTM2) : List (Sig M.Γ) :=
  (Finset.univ : Finset (M.Γ M.k₀)).toList.map (fun g => ⟨M.k₀, g⟩) ++
    (Finset.univ : Finset M.Λ).toList.flatMap
      (fun l => pushSyms (Finset.univ : Finset M.σ).toList (M.m l))

/-- `|x| + 1 + q(|x|)`: the longest verifier input. -/
def clN (x : List Bool) : ℕ := x.length + 1 + q.eval x.length

noncomputable def clT (x : List Bool) : ℕ := h.time.eval (clN q x)

noncomputable def clS (x : List Bool) : ℕ := clN q x + pushTotal h.tm * clT q h x

noncomputable def clPre (x : List Bool) : List (h.tm.Γ h.tm.k₀) :=
  (x.map some ++ [none]).map h.inputAlphabet.invFun

def clAllowed (g : h.tm.Γ h.tm.k₀) : Prop := (h.inputAlphabet g).isSome = true

noncomputable def clAcc : TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ := haltList h.tm ((encodeBool true).map h.outputAlphabet.invFun)

noncomputable def clU0 : TVal h.tm.Γ h.tm.Λ h.tm.σ :=
  Sum.inl (⟨none, h.tm.initialState, fun _ => 0, fun _ => []⟩ : Summ h.tm.Γ h.tm.Λ h.tm.σ)

/-- **The Cook–Levin formula for input `x`.** -/
noncomputable def clCNF (x : List Bool) : CNF :=
  tabCNF h.tm.m (clD h.tm) (clKs h.tm) (clS q h x) h.tm.main h.tm.initialState h.tm.k₀
    (clPre h x) (clAllowed h) (q.eval x.length) (clT q h x) (clAcc h)
    (tabValues (clD h.tm) (clS q h x) (clL h.tm) (clU0 h))

theorem initList_eq_initCfg (M : FinTM2) (l : List (M.Γ M.k₀)) :
    @Eq (TM2.Cfg M.Γ M.Λ M.σ) (initList M l) (initCfg M.main M.initialState M.k₀ l) := by
  show initList M l = (⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ l⟩ :
    TM2.Cfg M.Γ M.Λ M.σ)
  rw [← initList_stk]; rfl

theorem pairEnc_map (x w : List Bool) :
    (pairEnc (x, w)).map h.inputAlphabet.invFun =
      clPre h x ++ w.map (h.inputAlphabet.invFun ∘ some) := by
  simp [pairEnc, clPre, List.map_append]

/-- The halt-and-stay run of the verifier on `x # w` ends, after `clT` steps, in the halting
configuration that outputs `V (x, w)`. -/
theorem verifier_stay (x w : List Bool) (hw : w.length ≤ q.eval x.length) :
    (stepStay h.tm.m)^[clT q h x]
        (initCfg h.tm.main h.tm.initialState h.tm.k₀
          (clPre h x ++ w.map (h.inputAlphabet.invFun ∘ some))) =
      haltList h.tm ((encodeBool (V (x, w))).map h.outputAlphabet.invFun) := by
  obtain ⟨⟨n, hev⟩, hle⟩ := h.outputsFun (x, w)
  rw [pairEnc_map, initList_eq_initCfg] at hev
  refine stepStay_of_evals h.tm.m n _ _ rfl hev _ (le_trans hle ?_)
  apply poly_eval_mono
  simp [pairEnc, clN]; omega

theorem haltList_true_iff (b : Bool) :
    @Eq (TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ) (haltList h.tm ((encodeBool b).map h.outputAlphabet.invFun))
      (clAcc h) ↔ b = true := by
  constructor
  · intro e
    have := congrArg (fun c : TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ => (c.stk h.tm.k₁).head?) e
    simp only [clAcc, haltList_stk, Function.update_self] at this
    have h2 : h.outputAlphabet.invFun b = h.outputAlphabet.invFun true := by
      simpa [encodeBool] using this
    exact h.outputAlphabet.symm.injective h2
  · rintro rfl; rfl

theorem clD_spec (lab : h.tm.Λ) : sdepth (h.tm.m lab) ≤ clD h.tm :=
  Finset.le_sup (f := fun l => sdepth (h.tm.m l)) (Finset.mem_univ lab)

theorem clKs_spec (k : h.tm.K) : k ∈ clKs h.tm := by simp [clKs]

theorem init_len (x : List Bool) (ws : List (h.tm.Γ h.tm.k₀)) (hw : ws.length ≤ q.eval x.length) :
    ∀ k, ((initCfg h.tm.main h.tm.initialState h.tm.k₀ (clPre h x ++ ws)).stk k).length ≤
      clN q x := by
  intro k
  by_cases hk : k = h.tm.k₀
  · subst hk; simp [initCfg, clPre, clN]; omega
  · simp [initCfg, hk]

theorem init_syms (x : List Bool) (ws : List (h.tm.Γ h.tm.k₀)) :
    SymsIn (clL h.tm) (initCfg h.tm.main h.tm.initialState h.tm.k₀ (clPre h x ++ ws)).stk := by
  intro k g hg
  by_cases hk : k = h.tm.k₀
  · subst hk
    simp [clL]
  · simp [initCfg, hk] at hg

theorem run_syms (c : TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ) (hc : SymsIn (clL h.tm) c.stk) (t : ℕ) :
    SymsIn (clL h.tm) ((stepStay h.tm.m)^[t] c).stk := by
  induction t with
  | zero => exact hc
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    refine stepStay_syms h.tm.m _ (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) _ (fun lab x hx => ?_) _ ih
    simp only [clL, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨lab, by simp, hx⟩

/-- **The Cook–Levin formula is correct**: `x` has a witness accepted by the verifier iff the
formula `clCNF q h x` is satisfiable. -/
theorem clCNF_correct (x : List Bool) :
    (∃ w : List Bool, w.length ≤ q.eval x.length ∧ V (x, w) = true) ↔ SAT (clCNF q h x) := by
  unfold clCNF
  have hlen : ∀ ws : List (h.tm.Γ h.tm.k₀), ws.length ≤ q.eval x.length →
      ∀ t ≤ clT q h x, ∀ k, (((stepStay h.tm.m)^[t]
        (initCfg h.tm.main h.tm.initialState h.tm.k₀ (clPre h x ++ ws))).stk k).length ≤
          clS q h x := by
    intro ws hw t ht k
    have := iterate_stepStay_len h.tm.m _ (clN q x) (pushTotal h.tm)
      (pushes_le_total h.tm) (init_len q h x ws hw) t k
    have := Nat.mul_le_mul_left (pushTotal h.tm) ht
    unfold clS; omega
  rw [tabCNF_correct h.tm.m (clD h.tm) (clKs h.tm) (clS q h x) h.tm.main h.tm.initialState
    h.tm.k₀ (clPre h x) (clAllowed h) (q.eval x.length) (clT q h x) (clAcc h)
    (clD_spec h) (clKs_spec h) _ (clU0 h) (u0_mem_tabValues _ _ _ _)
    (fun ws hw _ => hlen ws hw)
    (fun ws hw _ t ht => tabValues_cover _ _ _ _ _ (run_syms h _ (init_syms h x ws) t)
      (hlen ws hw t ht))]
  constructor
  · rintro ⟨w, hw, hV⟩
    refine ⟨w.map (h.inputAlphabet.invFun ∘ some), by simpa using hw, fun g hg => ?_, ?_⟩
    · simp only [List.mem_map, Function.comp] at hg
      obtain ⟨b, -, rfl⟩ := hg
      simp [clAllowed]
    · rw [verifier_stay q h x w hw, haltList_true_iff]; exact hV
  · rintro ⟨ws, hw, hal, hrun⟩
    let w := ws.map (fun g => (h.inputAlphabet g).getD false)
    have hws : w.map (h.inputAlphabet.invFun ∘ some) = ws := by
      simp only [w, List.map_map]
      conv_rhs => rw [← List.map_id ws]
      apply List.map_congr_left
      intro g hg
      have := hal g hg
      simp only [clAllowed, Option.isSome_iff_exists] at this
      obtain ⟨b, hb⟩ := this
      simp only [Function.comp, hb, Option.getD_some, id]
      rw [← hb]; exact h.inputAlphabet.left_inv g
    refine ⟨w, by simpa [w] using hw, ?_⟩
    rw [← haltList_true_iff h, ← verifier_stay q h x w (by simpa [w] using hw), hws]
    exact hrun


/-- The Cook–Levin map on bit strings: `x ↦` the encoding of the tableau formula. -/
noncomputable def clMap (x : List Bool) : List Bool := encodeCNF (clCNF q h x)

theorem clMap_correct (x : List Bool) :
    (∃ w : List Bool, w.length ≤ q.eval x.length ∧ V (x, w) = true) ↔ SATLang (clMap q h x) := by
  rw [clCNF_correct q h x, clMap, SATLang_encode_iff]

end Verifier

/-- **Cook–Levin, reduced to one computability fact.** If, for every polynomial-time verifier,
the explicit tableau map `clMap` is computable by a polynomial-time `FinTM2`, then SAT is
NP-complete. Everything else (SAT ∈ NP, correctness of the tableau formula, the CSP → CNF
encoding, locality of TM2 steps) is proven above. The hypothesis is NOT proven here. -/
theorem cookLevin_of_clMap_polytime
    (H : ∀ (V : List Bool × List Bool → Bool) (q : Polynomial ℕ)
      (h : TM2ComputableInPolyTime pairEnc encodeBool V),
      Nonempty (TM2ComputableInPolyTime strEnc strEnc (clMap q h))) :
    CookLevinStatement := by
  refine ⟨SAT_in_NP, fun L hL => ?_⟩
  obtain ⟨V, q, ⟨h⟩, hV⟩ := hL
  exact ⟨clMap q h, H V q h, fun x => (hV x).trans (clMap_correct q h x)⟩

end PvnpReal
