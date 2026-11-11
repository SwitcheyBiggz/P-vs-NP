/-
  PvnpReal.Reproduce2 — **`Reproduces U2`** and the unconditional **`P_ne_EXP`**.

  Every polynomial-time decider `f` is given (via `NormalForm.Sim.prog`) as an `NProg`, compiled
  (`FlatComp`) into a flat program `Pc`, and the self-codes `x = 1ⁿ 0 enc(Pc)` make the flat
  interpreter `U2 x x t` output `f x` for all `t ≥ D·time(|x|) + 1`.
-/
import PvnpReal.FlatInit

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

namespace Flat

namespace Prm

variable (P : Prm)

theorem Pc_getD5 : P.Pc.getD 5 0 = P.start := rfl
theorem Pc_getD0 : P.Pc.getD 0 0 = P.nK := rfl
theorem Pc_getD2 : P.Pc.getD 2 0 = P.p.k0 := rfl
theorem Pc_getD3 : P.Pc.getD 3 0 = P.p.inT.getD 0 0 := rfl
theorem Pc_getD4 : P.Pc.getD 4 0 = P.p.inT.getD 1 0 := rfl

theorem S0_eq (x : List Bool) : S0 P.Pc x = (NInit P.p x).stk := by
  funext k
  change (if k = P.p.k0 then x.map (fun b => if b then P.p.inT.getD 1 0 else P.p.inT.getD 0 0)
    else []) = (if k = P.p.k0 then x.map (fun b => P.p.inT.getD (if b then 1 else 0) 0) else [])
  by_cases hk : k = P.p.k0
  · rw [if_pos hk, if_pos hk]; congr 1; funext b; cases b <;> rfl
  · rw [if_neg hk, if_neg hk]

/-- **The flat interpreter reproduces a compiled `NProg` run.** -/
theorem reproduce (hN : ∀ q ∈ P.nodes, P.NWF q) (hk0 : P.p.k0 < P.nK) (hk1 : P.p.k1 < P.nK)
    (hinit : P.p.init < P.V) (hin : ∀ b : Bool, P.p.inT.getD (if b then 1 else 0) 0 < P.B)
    (x y : List Bool) (hx : numsOf (lpX x) = P.Pc)
    (T : ℕ) (h : NCfg) (hr : nrunFor P.p T (NInit P.p y) = some h) (b : Bool)
    (hb : (h.stk P.p.k1).head?.map (fun s => P.p.outT.getD s false) = some b) :
    ∀ t, P.D * T + 1 ≤ t → P.Pc.length ≤ y.length + t → U2 x y t = some b := by
  intro t ht hPc
  have hS0 : SGood P.B (NInit P.p y).stk := by
    intro k a ha
    simp only [NInit] at ha
    split at ha
    · obtain ⟨c, _, rfl⟩ := List.mem_map.1 ha; exact hin c
    · simp at ha
  obtain ⟨n, hn, e, hl, hS⟩ := P.macroSim hN T _ h hinit hS0 hr
  obtain ⟨hl', v, S⟩ := h
  simp only at hl; subst hl
  have e' : (mstep P.Pc)^[n] ⟨P.start, (NInit P.p y).stk⟩ = ⟨P.CHK, S⟩ := e
  obtain ⟨s, hs, hsb⟩ : ∃ s, (S P.p.k1).head? = some s ∧ P.p.outT.getD s false = b := by
    cases hh : (S P.p.k1).head? with
    | none => simp [hh] at hb
    | some s => simp [hh] at hb; exact ⟨s, rfl, hb⟩
  have hc := P.chk_step S hS
  rw [hs] at hc
  simp only [oc, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, Nat.add_sub_cancel, true_and,
    hsb] at hc
  -- the final configuration
  have hfix : mstep P.Pc ⟨if b = true then P.CHK + 1 else P.CHK + 2, S⟩ =
      ⟨if b = true then P.CHK + 1 else P.CHK + 2, S⟩ := by
    cases b
    · exact P.rej_fix S
    · exact P.acc_fix S
  have hreach : (mstep P.Pc)^[t] ⟨P.start, (NInit P.p y).stk⟩ =
      ⟨if b = true then P.CHK + 1 else P.CHK + 2, S⟩ := by
    have : t = (t - (n + 1)) + 1 + n := by omega
    rw [this, Function.iterate_add_apply, e', Function.iterate_succ_apply, hc]
    exact Function.iterate_fixed hfix _
  -- layout
  have hR := rep_iter (P.stk_ok hN hk1) t _ _ (rep_init P.Pc y t hPc (by rw [Pc_getD0, Pc_getD2]; exact hk0))
    (fun k _ => by
      show (S0 P.Pc y k).length + t ≤ y.length + t + 1
      unfold S0; split <;> simp <;> omega)
  rw [Pc_getD5, S0_eq P y, hreach] at hR
  have htag := rep_tag hR
  unfold U2
  rw [srcL_eq, hx, htag]
  cases b
  · simp [P.tag_rej]
  · simp [P.tag_acc]

end Prm

end Flat

open Flat

namespace Sim

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

open Classical

variable (tm : FinTM2)

theorem getD_lt1 {B : ℕ} {l : List ℕ} (h : ∀ a ∈ l, a < B) (h0 : 0 < B) (v : ℕ) : l.getD v 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : l[v]? with
  | none => exact h0
  | some a => exact h a (List.mem_of_getElem? hv)

theorem getD_lt2 {B : ℕ} {L : List (List ℕ)} (h : ∀ l ∈ L, ∀ a ∈ l, a < B) (h0 : 0 < B) (v o : ℕ) :
    (L.getD v []).getD o 0 < B := by
  rw [List.getD_eq_getElem?_getD (l := L)]
  cases hv : L[v]? with
  | none => exact h0
  | some l => exact getD_lt1 (h l (List.mem_of_getElem? hv)) h0 o

noncomputable def prm (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) : Prm :=
  ⟨prog tm ia oa, Fintype.card tm.σ, (vals tm).length + 1, Fintype.card tm.K⟩

theorem card_σ_pos : 0 < Fintype.card tm.σ := Fintype.card_pos_iff.2 ⟨tm.initialState⟩

theorem code_le (s : Σ k, tm.Γ k) : code tm s < (vals tm).length + 1 := by
  have := List.idxOf_le_length (a := s) (l := vals tm)
  unfold code; omega

theorem nwf_tr (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (s : TM2.Stmt tm.Γ tm.Λ tm.σ) :
    ∀ q ∈ subs (tr tm s), (prm tm ia oa).NWF q := by
  induction s with
  | push k f q ih =>
    intro q' hq'
    simp only [tr, subs, List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · refine ⟨(eK tm k).2, fun v => getD_lt1 ?_ (by simp [prm]) v⟩
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact code_le tm _
    · exact ih q' hq'
  | peek k f q ih =>
    intro q' hq'
    simp only [tr, subs, List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · refine ⟨(eK tm k).2, fun v o => getD_lt2 ?_ (card_σ_pos tm) v o⟩
      intro l hl a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha
      exact Fin.isLt _
    · exact ih q' hq'
  | pop k f q ih =>
    intro q' hq'
    simp only [tr, subs, List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · refine ⟨(eK tm k).2, fun v o => getD_lt2 ?_ (card_σ_pos tm) v o⟩
      intro l hl a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha
      exact Fin.isLt _
    · exact ih q' hq'
  | load a q ih =>
    intro q' hq'
    simp only [tr, subs, List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · refine fun v => getD_lt1 ?_ (card_σ_pos tm) v
      intro b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hb
      exact Fin.isLt _
    · exact ih q' hq'
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro q' hq'
    simp only [tr, subs, List.mem_cons, List.mem_append] at hq'
    rcases hq' with rfl | hq' | hq'
    · trivial
    · exact ih₁ q' hq'
    · exact ih₂ q' hq'
  | goto f =>
    intro q' hq'
    simp only [tr, subs, List.mem_singleton] at hq'
    subst hq'; trivial
  | halt =>
    intro q' hq'
    simp only [tr, subs, List.mem_singleton] at hq'
    subst hq'; trivial

theorem nwf_nodes (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) :
    ∀ q ∈ (prm tm ia oa).nodes, (prm tm ia oa).NWF q := by
  intro q hq
  simp only [Prm.nodes, List.mem_append, List.mem_flatMap, List.mem_singleton] at hq
  rcases hq with ⟨s, hs, hq⟩ | rfl
  · simp only [prm, prog] at hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hs
    exact nwf_tr tm ia oa _ q hq
  · trivial

end Sim

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

/-- **`U2` reproduces every polynomial-time decider.** -/
theorem reproduces_U2 : Reproduces U2 := by
  intro f ⟨h⟩
  let P := Sim.prm h.tm h.inputAlphabet h.outputAlphabet
  refine ⟨Polynomial.C P.D * h.time + 1, fun n0 => ?_⟩
  let x : List Bool := List.replicate n0 true ++ false :: encNums P.Pc
  have hx : numsOf (lpX x) = P.Pc := by simp only [x, lpX_rep, numsOf_encNums]
  have hPc : P.Pc.length ≤ x.length := by
    have := encNums_length_ge P.Pc
    simp only [x, List.length_append, List.length_replicate, List.length_cons]; omega
  refine ⟨x, by simp [x], fun t ht => ?_⟩
  have hr := runFor_computable h.toTM2ComputableInTime x
  obtain ⟨i1, i2⟩ := Sim.init_enc h.tm h.inputAlphabet h.outputAlphabet x
  obtain ⟨s1, s2⟩ := Sim.simulate h.tm h.inputAlphabet h.outputAlphabet _ _ _ i2 hr
  rw [i1] at s1
  have hb := Sim.halt_out h.tm h.inputAlphabet h.outputAlphabet (f x) s2
  have hcard : ∀ (k : h.tm.K), (Sim.eK h.tm k : ℕ) < Fintype.card h.tm.K := fun k => (Sim.eK h.tm k).2
  refine Prm.reproduce P (Sim.nwf_nodes _ _ _) (hcard _) (hcard _) (Sim.eσ h.tm h.tm.initialState).2
    ?_ x x hx _ _ s1 (f x) hb t ?_ (by omega)
  · intro b
    cases b <;> exact Sim.code_le _ _
  · have : (Polynomial.C P.D * h.time + 1).eval x.length = P.D * h.time.eval x.length + 1 := by simp
    rw [this] at ht
    exact ht

/-- **P ≠ EXP, unconditionally.** -/
theorem p_ne_exp : P_ne_EXP := P_ne_EXP_of_universal reproduces_U2 diagU2_in_EXP

end PvnpReal
