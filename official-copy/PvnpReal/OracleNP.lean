/-
  PvnpReal.OracleNP — **`NP ⊆ NP^A` for every oracle `A`**.

  A Mathlib verifier `V` (input `pairEnc (x, w)`, witness `|w| ≤ q`) becomes an oracle program
  with no queries: a hand-written prefix (verified loop lemmas `skip_run`, `mv_run`) turns the
  separate input stack `x` and witness stack `w` (exact length `q + 1`) into `pairEnc (x, lpX w)`
  on the input stack of `V`'s normal form, then runs it (`osim0`). Since every `w` of length
  `q + 1` has `|lpX w| ≤ q`, and `w' ↦ 1^{q-|w'|} 0 w'` is a right inverse, the witness sets match.
-/
import PvnpReal.OracleP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Classical

namespace ONP

def R3 : List (List ℕ) := List.replicate 3 [0, 1, 2]
def rep3 (n : ℕ) : List ℕ := List.replicate 3 n
def bsym (b : Bool) : ℕ := if b then 1 else 0

/-- Skip `1*0` on stack `s` (computes `lpX`), then go to `next`. -/
def skS (s self next : ℕ) : OStmt :=
  .pop s R3 (.branch [false, false, true] (.goto (rep3 self)) (.goto (rep3 next)))

/-- Move stack `s` onto `d`, writing bit `b` as `a0`/`a1`, then go to `next`. -/
def mvS (s d a0 a1 self next : ℕ) : OStmt :=
  .pop s R3 (.branch [true, false, false] (.goto (rep3 next)) (.push d [0, a0, a1] (.goto (rep3 self))))

def pnS (d c next : ℕ) : OStmt := .push d [c, c, c] (.goto (rep3 next))

def fnS (i0 mainS : ℕ) : OStmt := .load [i0, i0, i0] (.goto (List.replicate (i0 + 1) mainS))

theorem R3_get {v : ℕ} (hv : v < 3) (o : ℕ) (ho : o < 3) : (R3.getD v []).getD o 0 = o := by
  rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;>
    rcases (by omega : o = 0 ∨ o = 1 ∨ o = 2) with rfl | rfl | rfl <;> rfl

theorem rep3_get {v : ℕ} (hv : v < 3) (n : ℕ) : (rep3 n).getD v 0 = n := by
  rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;> rfl

theorem c3_get {v : ℕ} (hv : v < 3) (c : ℕ) : ([c, c, c] : List ℕ).getD v 0 = c := by
  rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;> rfl

theorem oc_bsym (b : Bool) : oc (some (bsym b)) = if b then 2 else 1 := by cases b <;> rfl
theorem oc_none' : oc none = 0 := rfl

variable {A : List Bool → Prop} {P : OProg}

theorem orun_step (t l v : ℕ) (S : ℕ → List ℕ) :
    orunFor A P (t + 1) ⟨some l, v, S⟩ = orunFor A P t (oAux A (P.m.getD l .halt) v S) := rfl

theorem skip_run {s self next : ℕ} (hm : P.m.getD self .halt = skS s self next) :
    ∀ (w : List Bool) (v : ℕ) (S : ℕ → List ℕ), v < 3 → S s = w.map bsym →
      ∃ k ≤ w.length + 1, ∃ v' < 3, ∀ t, orunFor A P (t + k) ⟨some self, v, S⟩ =
        orunFor A P t ⟨some next, v', Function.update S s ((lpX w).map bsym)⟩ := by
  intro w
  induction w with
  | nil =>
    intro v S hv hS
    refine ⟨1, le_refl _, 0, by omega, fun t => ?_⟩
    rw [orun_step, hm]
    simp only [skS, oAux, hS, List.map_nil, List.head?_nil, oc_none', R3_get hv 0 (by omega),
      List.tail_nil, List.getD_cons_zero, cond_false, rep3_get (show 0 < 3 by omega)]
    rfl
  | cons b w ih =>
    intro v S hv hS
    cases b
    · refine ⟨1, by simp, 1, by omega, fun t => ?_⟩
      rw [orun_step, hm]
      simp only [skS, oAux, hS, List.map_cons, List.head?_cons, oc_bsym, Bool.false_eq_true,
        if_false, R3_get hv 1 (by omega), List.tail_cons, List.getD_cons_succ, List.getD_cons_zero,
        cond_false, rep3_get (show 1 < 3 by omega), LoopTM.lpX_cons_false]
    · have hS' : (Function.update S s (w.map bsym)) s = w.map bsym := Function.update_self _ _ _
      obtain ⟨k, hk, v', hv', e⟩ := ih 2 _ (by omega) hS'
      refine ⟨k + 1, by simp; omega, v', hv', fun t => ?_⟩
      rw [← Nat.add_assoc, orun_step, hm]
      simp only [skS, oAux, hS, List.map_cons, List.head?_cons, oc_bsym, if_true,
        R3_get hv 2 (by omega), List.tail_cons, List.getD_cons_succ, List.getD_cons_zero, cond_true,
        rep3_get (show 2 < 3 by omega)]
      rw [e, LoopTM.lpX_cons_true, Function.update_idem]

theorem mv_run {s d a0 a1 self next : ℕ} (hsd : s ≠ d) (hm : P.m.getD self .halt = mvS s d a0 a1 self next) :
    ∀ (l : List Bool) (v : ℕ) (S : ℕ → List ℕ), v < 3 → S s = l.map bsym →
      ∀ t, orunFor A P (t + (l.length + 1)) ⟨some self, v, S⟩ =
        orunFor A P t ⟨some next, 0, Function.update (Function.update S s []) d
          (l.reverse.map (fun b => if b then a1 else a0) ++ S d)⟩ := by
  intro l
  induction l with
  | nil =>
    intro v S hv hS t
    rw [List.length_nil, orun_step, hm]
    simp only [mvS, oAux, hS, List.map_nil, List.head?_nil, oc_none', R3_get hv 0 (by omega),
      List.tail_nil, List.getD_cons_zero, cond_true, rep3_get (show 0 < 3 by omega),
      List.reverse_nil, List.nil_append]
    congr 2
    funext j
    by_cases hj : j = d
    · subst hj; rw [Function.update_self, Function.update_of_ne (Ne.symm hsd)]
    · rw [Function.update_of_ne hj]
  | cons b l ih =>
    intro v S hv hS t
    have hv' : (if b then 2 else 1) < 3 := by split <;> omega
    let S1 := Function.update (Function.update S s (l.map bsym)) d
      ((if b then a1 else a0) :: S d)
    have hS1 : S1 s = l.map bsym := by
      simp only [S1]; rw [Function.update_of_ne hsd, Function.update_self]
    have e := ih (if b then 2 else 1) S1 hv' hS1 t
    rw [show t + ((b :: l).length + 1) = (t + (l.length + 1)) + 1 by simp; omega, orun_step, hm]
    have hstep : oAux A (mvS s d a0 a1 self next) v S = ⟨some self, if b then 2 else 1, S1⟩ := by
      cases b
      · simp only [mvS, oAux, hS, List.map_cons, List.head?_cons, oc_bsym, Bool.false_eq_true,
          if_false, R3_get hv 1 (by omega), List.tail_cons, List.getD_cons_succ,
          List.getD_cons_zero, cond_false, rep3_get (show 1 < 3 by omega), S1,
          Function.update_of_ne (Ne.symm hsd)]
      · simp only [mvS, oAux, hS, List.map_cons, List.head?_cons, oc_bsym, if_true,
          R3_get hv 2 (by omega), List.tail_cons, List.getD_cons_succ,
          List.getD_cons_zero, cond_false, rep3_get (show 2 < 3 by omega), S1,
          Function.update_of_ne (Ne.symm hsd)]
    rw [hstep, e]
    congr 2
    funext j
    simp only [S1, Function.update_apply]
    by_cases hj : j = d
    · subst hj; simp [Ne.symm hsd]
    · by_cases hs : j = s <;> simp [hj, hs]

theorem pn_run {d c next self : ℕ} (hm : P.m.getD self .halt = pnS d c next) (v : ℕ) (hv : v < 3)
    (S : ℕ → List ℕ) (t : ℕ) :
    orunFor A P (t + 1) ⟨some self, v, S⟩ =
      orunFor A P t ⟨some next, v, Function.update S d (c :: S d)⟩ := by
  rw [orun_step, hm]
  simp only [pnS, oAux, c3_get hv, rep3_get hv]

theorem fn_run {i0 mainS self : ℕ} (hm : P.m.getD self .halt = fnS i0 mainS) (v : ℕ) (hv : v < 3)
    (S : ℕ → List ℕ) (t : ℕ) :
    orunFor A P (t + 1) ⟨some self, v, S⟩ = orunFor A P t ⟨some mainS, i0, S⟩ := by
  rw [orun_step, hm]
  simp only [fnS, oAux, c3_get hv]
  simp [List.getD_eq_getElem?_getD]


/-! ### The verifier's oracle program -/

section Verifier

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

open Sim

variable (tm : FinTM2) (ia : tm.Γ tm.k₀ ≃ Option Bool) (oa : tm.Γ tm.k₁ ≃ Bool)

noncomputable def KX : ℕ := Fintype.card tm.K
noncomputable def MM : ℕ := Fintype.card tm.Λ
noncomputable def K0 : ℕ := eK tm tm.k₀
noncomputable def cc (o : Option Bool) : ℕ := code tm ⟨tm.k₀, ia.symm o⟩

noncomputable def m0 : List NStmt := List.ofFn fun i => tr tm (tm.m ((eΛ tm).symm i))

noncomputable def suf : List OStmt :=
  [skS (KX tm + 1) (MM tm + 0) (MM tm + 1),
   mvS (KX tm + 1) (KX tm + 2) 0 1 (MM tm + 1) (MM tm + 2),
   mvS (KX tm + 2) (K0 tm) (cc tm ia (some false)) (cc tm ia (some true)) (MM tm + 2) (MM tm + 3),
   pnS (K0 tm) (cc tm ia none) (MM tm + 4),
   mvS (KX tm) (KX tm + 2) 0 1 (MM tm + 4) (MM tm + 5),
   mvS (KX tm + 2) (K0 tm) (cc tm ia (some false)) (cc tm ia (some true)) (MM tm + 5) (MM tm + 6),
   fnS (eσ tm tm.initialState) (eΛ tm tm.main)]

/-- The query-free oracle program: merge `x` and `lpX w` into `pairEnc`, then run `V`. -/
noncomputable def nvP : OProg where
  k0 := KX tm
  kw := KX tm + 1
  ka := eK tm tm.k₁
  main := MM tm
  init := 0
  inT := [0, 1]
  accT := (List.range (vals tm).length).map (fun i => ((Sim.dec tm tm.k₁ (i + 1)).map oa).getD false)
  m := (m0 tm).map OSim.emb0 ++ suf tm ia

theorem m_suf (i : ℕ) : (nvP tm ia oa).m.getD (MM tm + i) .halt = (suf tm ia).getD i .halt := by
  have hl : ((m0 tm).map OSim.emb0).length = MM tm := by simp [m0, MM]
  simp only [nvP, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left]

theorem m_pre (l : tm.Λ) : (nvP tm ia oa).m.getD (eΛ tm l : ℕ) .halt = OSim.emb0 (tr tm (tm.m l)) := by
  have hl : (eΛ tm l : ℕ) < ((m0 tm).map OSim.emb0).length := by simp [m0]
  simp only [nvP, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hl]
  simp [m0]

/-- **Simulation** of `tm` by the oracle program (oracle-independent). -/
theorem osim0 (A : List Bool → Prop) (t : ℕ) :
    ∀ (c h : TM2.Cfg tm.Γ tm.Λ tm.σ), Inv tm c.stk → runFor tm.m t c = some h →
      orunFor A (nvP tm ia oa) t (encCfg tm c) = some (encCfg tm h) ∧ Inv tm h.stk := by
  induction t with
  | zero =>
    rintro ⟨cl, v, S⟩ h hc e
    cases cl with
    | none => simp [runFor] at e; subst e; exact ⟨by simp [orunFor, encCfg], hc⟩
    | some l => simp [runFor] at e
  | succ t ih =>
    rintro ⟨cl, v, S⟩ h hc e
    cases cl with
    | none => simp [runFor] at e; subst e; exact ⟨by simp [orunFor, encCfg], hc⟩
    | some l =>
      simp only [runFor, TM2.step, Option.bind_some] at e
      obtain ⟨s1, s2⟩ := sim tm (tm.m l) (pushes_main tm l) v S hc
      obtain ⟨r1, r2⟩ := ih _ h s2 e
      refine ⟨?_, r2⟩
      simp only [encCfg, Option.map_some, orunFor]
      rw [m_pre, OSim.emb0_aux]
      have := s1; simp only [encCfg] at this ⊢
      rw [this]; exact r1

theorem initList_stk (l : List (tm.Γ tm.k₀)) (k : tm.K) :
    (initList tm l).stk k = if h : k = tm.k₀ then h ▸ l else [] := by
  simp only [initList]; split
  · next h => subst h; rfl
  · rfl

theorem init_inv (l : List (tm.Γ tm.k₀)) : Inv tm (initList tm l).stk := by
  intro k a ha
  rw [initList_stk] at ha
  split at ha
  · next h =>
    subst h
    unfold vals
    exact List.mem_append_right _ (List.mem_map.2 ⟨a, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩)
  · simp at ha

theorem encS_init (l : List (tm.Γ tm.k₀)) (j : ℕ) :
    encS tm (initList tm l).stk j = if j = K0 tm then l.map (fun a => code tm ⟨tm.k₀, a⟩) else [] := by
  by_cases hj : j = K0 tm
  · subst hj; rw [if_pos rfl, K0, encS_eK, initList_stk, dif_pos rfl]
  · rw [if_neg hj]
    unfold encS
    split
    · next h =>
      have hne : (eK tm).symm ⟨j, h⟩ ≠ tm.k₀ := by
        intro e; apply hj; rw [K0, ← e]; simp
      rw [initList_stk, dif_neg hne]; rfl
    · rfl

theorem halt_out' (b : Bool) (hI : Inv tm (haltList tm [oa.invFun b]).stk) :
    ((encCfg tm (haltList tm [oa.invFun b])).stk (nvP tm ia oa).ka).head?.map
      (fun s => (nvP tm ia oa).accT.getD s false) = some b := by
  have hk : (haltList tm [oa.invFun b]).stk tm.k₁ = [oa.invFun b] := by
    unfold haltList; dsimp only; rw [dif_pos rfl]; rfl
  have hm : (⟨tm.k₁, oa.invFun b⟩ : Σ k, tm.Γ k) ∈ vals tm := hI _ _ (by rw [hk]; simp)
  simp only [encCfg, nvP]
  rw [encS_eK, hk]
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.map_some]
  rw [range_map_getD _ _ (code_lt tm hm), dec_code tm hm]
  simp

theorem K0_lt : K0 tm < KX tm := (eK tm tm.k₀).2

theorem bsym_eq : (fun b : Bool => ([0, 1] : List ℕ).getD (if b then 1 else 0) 0) = bsym := by
  funext b; cases b <;> rfl

theorem bsym_eq' : (fun b : Bool => if b then (1 : ℕ) else 0) = bsym := rfl

theorem cc_eq (l : List Bool) :
    l.map (fun b => if b then cc tm ia (some true) else cc tm ia (some false)) =
      l.map (fun b => cc tm ia (some b)) := by
  congr 1; funext b; cases b <;> rfl

/-- **The merge prefix**: from `OInit` it reaches exactly the encoded initial configuration of
`tm` on `pairEnc (x, lpX w)`. -/
theorem prefix_run (A : List Bool → Prop) (x w : List Bool) :
    ∃ k ≤ w.length + 2 * (lpX w).length + 2 * x.length + 7, ∀ t,
      orunFor A (nvP tm ia oa) (t + k) (OInit (nvP tm ia oa) x w) =
        orunFor A (nvP tm ia oa) t
          (encCfg tm (initList tm ((pairEnc (x, lpX w)).map ia.invFun))) := by
  set P := nvP tm ia oa with hP
  set w' := lpX w with hw'
  have h0 := K0_lt tm
  have hX0 : KX tm ≠ K0 tm := by omega
  have hW0 : KX tm + 1 ≠ K0 tm := by omega
  have hT0 : KX tm + 2 ≠ K0 tm := by omega
  let S0 : ℕ → List ℕ := fun j => if j = KX tm then x.map bsym else if j = KX tm + 1 then w.map bsym else []
  have hI : OInit P x w = ⟨some (MM tm + 0), 0, S0⟩ := by
    simp only [OInit, hP, nvP, bsym_eq, S0]; rfl
  -- phase 1: skip
  obtain ⟨k1, hk1, v1, hv1, e1⟩ := skip_run (A := A) (P := P) (s := KX tm + 1) (self := MM tm + 0)
    (next := MM tm + 1) (by rw [hP, m_suf]; rfl) w 0 S0 (by omega) (by simp [S0])
  let S1 := Function.update S0 (KX tm + 1) (w'.map bsym)
  -- phase 2: W → T
  have e2 := mv_run (A := A) (P := P) (s := KX tm + 1) (d := KX tm + 2) (a0 := 0) (a1 := 1)
    (self := MM tm + 1) (next := MM tm + 2) (by omega) (by rw [hP, m_suf]; rfl) w' v1 S1 hv1
    (by simp [S1])
  let S2 := Function.update (Function.update S1 (KX tm + 1) []) (KX tm + 2)
    (w'.reverse.map (fun b => if b then 1 else 0) ++ S1 (KX tm + 2))
  have e3 := mv_run (A := A) (P := P) (s := KX tm + 2) (d := K0 tm) (a0 := cc tm ia (some false))
    (a1 := cc tm ia (some true)) (self := MM tm + 2) (next := MM tm + 3) hT0
    (by rw [hP, m_suf]; rfl) w'.reverse 0 S2 (by omega)
    (by simp [S2, S1, S0, Function.update_apply, bsym_eq'])
  let S3 := Function.update (Function.update S2 (KX tm + 2) []) (K0 tm)
    (w'.reverse.reverse.map (fun b => if b then cc tm ia (some true) else cc tm ia (some false)) ++
      S2 (K0 tm))
  have e4 := pn_run (A := A) (P := P) (d := K0 tm) (c := cc tm ia none) (next := MM tm + 4)
    (self := MM tm + 3) (by rw [hP, m_suf]; rfl) 0 (by omega) S3
  let S4 := Function.update S3 (K0 tm) (cc tm ia none :: S3 (K0 tm))
  have e5 := mv_run (A := A) (P := P) (s := KX tm) (d := KX tm + 2) (a0 := 0) (a1 := 1)
    (self := MM tm + 4) (next := MM tm + 5) (by omega) (by rw [hP, m_suf]; rfl) x 0 S4 (by omega)
    (by simp [S4, S3, S2, S1, S0, Function.update_apply, Ne.symm hX0, hX0])
  let S5 := Function.update (Function.update S4 (KX tm) []) (KX tm + 2)
    (x.reverse.map (fun b => if b then 1 else 0) ++ S4 (KX tm + 2))
  have e6 := mv_run (A := A) (P := P) (s := KX tm + 2) (d := K0 tm) (a0 := cc tm ia (some false))
    (a1 := cc tm ia (some true)) (self := MM tm + 5) (next := MM tm + 6) hT0
    (by rw [hP, m_suf]; rfl) x.reverse 0 S5 (by omega)
    (by simp [S5, S4, S3, Function.update_apply, bsym_eq', Ne.symm hT0, hT0])
  let S6 := Function.update (Function.update S5 (KX tm + 2) []) (K0 tm)
    (x.reverse.reverse.map (fun b => if b then cc tm ia (some true) else cc tm ia (some false)) ++
      S5 (K0 tm))
  have e7 := fn_run (A := A) (P := P) (i0 := eσ tm tm.initialState) (mainS := eΛ tm tm.main)
    (self := MM tm + 6) (by rw [hP, m_suf]; rfl) 0 (by omega) S6
  have hfin : (⟨some (eΛ tm tm.main : ℕ), (eσ tm tm.initialState : ℕ), S6⟩ : NCfg) =
      encCfg tm (initList tm ((pairEnc (x, w')).map ia.invFun)) := by
    simp only [encCfg]
    congr 1
    funext j
    rw [encS_init]
    by_cases hj : j = K0 tm
    · subst hj
      simp only [S6, S5, S4, S3, S2, Function.update_self, if_pos rfl, List.reverse_reverse, cc_eq,
        Function.update_of_ne (Ne.symm hT0), Function.update_of_ne (Ne.symm hX0)]
      simp [S1, S0, Function.update_apply, pairEnc, List.map_map, Ne.symm hX0, Ne.symm hW0,
        Ne.symm hT0, cc]
      rfl
    · rw [if_neg hj]
      simp only [S6, S5, S4, S3, S2, S1, S0, Function.update_apply, hj, if_false]
      by_cases a : j = KX tm + 2
      · simp [a]
      · by_cases b : j = KX tm
        · simp [a, b]
        · by_cases c : j = KX tm + 1
          · simp [a, b, c]
          · simp [a, b, c]
  refine ⟨1 + (x.reverse.length + 1) + (x.length + 1) + 1 + (w'.reverse.length + 1) +
    (w'.length + 1) + k1, by simp only [List.length_reverse]; omega, fun t => ?_⟩
  rw [show t + (1 + (x.reverse.length + 1) + (x.length + 1) + 1 + (w'.reverse.length + 1) +
    (w'.length + 1) + k1) = t + 1 + (x.reverse.length + 1) + (x.length + 1) + 1 +
    (w'.reverse.length + 1) + (w'.length + 1) + k1 by omega, hI]
  exact (e1 _).trans ((e2 _).trans ((e3 _).trans ((e4 _).trans ((e5 _).trans ((e6 _).trans
    ((e7 _).trans (congrArg _ hfin)))))))

end Verifier

end ONP

open ONP

/-- **`NP ⊆ NP^A` for every oracle `A`.** -/
theorem NP_sub_NPO (A L : Language) (hL : InNP L) : InNPO A L := by
  obtain ⟨V, q, ⟨h⟩, hV⟩ := hL
  let P := nvP h.tm h.inputAlphabet h.outputAlphabet
  let Tp : Polynomial ℕ := Polynomial.C 3 * (q + Polynomial.C 2) + Polynomial.C 2 * Polynomial.X +
    Polynomial.C 6 + h.time.comp (Polynomial.X + Polynomial.C 1 + q)
  refine ⟨P, Tp, q + Polynomial.C 1, fun x => ?_⟩
  have key : ∀ w : List Bool, w.length = q.eval x.length + 1 →
      orunFor A P (Tp.eval x.length) (OInit P x w) =
        some (Sim.encCfg h.tm (haltList h.tm [h.outputAlphabet.invFun (V (x, lpX w))])) ∧
      Sim.Inv h.tm (haltList h.tm [h.outputAlphabet.invFun (V (x, lpX w))]).stk ∧
      (lpX w).length ≤ q.eval x.length := by
    intro w hw
    have hne : w ≠ [] := by intro e; rw [e] at hw; simp at hw
    have hl := lpX_length_lt hne
    have hr : runFor h.tm.m (h.time.eval (pairEnc (x, lpX w)).length)
        (initList h.tm ((pairEnc (x, lpX w)).map h.inputAlphabet.invFun)) =
        some (haltList h.tm [h.outputAlphabet.invFun (V (x, lpX w))]) :=
      runFor_computable h.toTM2ComputableInTime (x, lpX w)
    obtain ⟨k, hk, e⟩ := prefix_run h.tm h.inputAlphabet h.outputAlphabet A x w
    obtain ⟨s1, s2⟩ := osim0 h.tm h.inputAlphabet h.outputAlphabet A _ _ _
      (init_inv h.tm _) hr
    refine ⟨orun_mono ?_ ((e _).trans s1), s2, by omega⟩
    have hp : (pairEnc (x, lpX w)).length = x.length + 1 + (lpX w).length := by
      simp [pairEnc]; omega
    have hm := poly_eval_mono h.time (show (pairEnc (x, lpX w)).length ≤
      x.length + 1 + q.eval x.length by omega)
    simp only [Tp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_comp]
    omega
  have hQ : (q + Polynomial.C 1).eval x.length = q.eval x.length + 1 := by simp
  refine ⟨fun w hw => ⟨_, (key w (hQ ▸ hw)).1⟩, ?_⟩
  rw [hV x]
  constructor
  · rintro ⟨w', hw', hv⟩
    let w := List.replicate (q.eval x.length - w'.length) true ++ false :: w'
    have hlw : lpX w = w' := lpX_rep _ _
    have hwl : w.length = q.eval x.length + 1 := by simp [w]; omega
    obtain ⟨k1, k2, -⟩ := key w hwl
    refine ⟨w, _, hQ ▸ hwl, k1, ?_⟩
    unfold OAccepts
    rw [halt_out' h.tm h.inputAlphabet h.outputAlphabet _ k2, hlw, hv]
  · rintro ⟨w, c, hw, hc, hacc⟩
    obtain ⟨k1, k2, k3⟩ := key w (hQ ▸ hw)
    rw [k1] at hc
    cases (Option.some.inj hc)
    unfold OAccepts at hacc
    rw [halt_out' h.tm h.inputAlphabet h.outputAlphabet _ k2] at hacc
    exact ⟨lpX w, k3, Option.some.inj hacc⟩

end PvnpReal
