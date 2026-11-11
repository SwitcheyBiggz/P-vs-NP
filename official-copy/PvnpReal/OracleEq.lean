/-
  PvnpReal.OracleEq — **Baker–Gill–Solovay, part 1**: an oracle `A` with `P^A = NP^A`.

  * `PO_of_reduction`: if `L x ↔ A (g x)` for a polynomial-time `g` (a Mathlib `FinTM2`),
    then `L ∈ P^A` — the oracle program is `Sim.prog` of `g`'s machine with every `halt`
    replaced by "query the output stack, push the answer, halt" (`emb`, `osim`).
  * `Aself`: a self-referential oracle, defined by well-founded recursion on length:
    `z = 1ᴺ 0 1ᶜ 0 1ᵀ 0 1^Q 0 x ∈ Aself` iff the oracle program with code `c` accepts `(x, w)`
    for some `|w| = Q` within `T` steps, using `Aself` restricted to strings shorter than `z`.
    Choosing the padding `N ≥ |x| + Q + cP·T` (all queries are shorter than `z`,
    `orunQ_bound`) makes the restriction invisible (`orun_congr`), so every `NP^Aself`
    language reduces to `Aself` in polynomial time.
  (The classical proof uses a PSPACE-complete oracle; this self-referential padded oracle is a
  standard alternative and is cheaper to verify.)
-/
import PvnpReal.OracleSep

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Classical

namespace OSim

/-- Final statement: query stack `ka`, push the answer (`1`/`0`) on it, halt. -/
def finS (ka : ℕ) (qT : List Bool) : OStmt :=
  .query ka qT (.load [] (.push ka [1] .halt)) (.load [] (.push ka [0] .halt))

/-- Embed an `NProg` tree, replacing `halt` by `finS`. -/
def emb (ka : ℕ) (qT : List Bool) : NStmt → OStmt
  | .push k f q => .push k f (emb ka qT q)
  | .peek k f q => .peek k f (emb ka qT q)
  | .pop k f q => .pop k f (emb ka qT q)
  | .load f q => .load f (emb ka qT q)
  | .branch f q₁ q₂ => .branch f (emb ka qT q₁) (emb ka qT q₂)
  | .goto f => .goto f
  | .halt => finS ka qT

noncomputable def finC (A : List Bool → Prop) (ka : ℕ) (qT : List Bool) (r : NCfg) : NCfg :=
  ⟨none, 0, Function.update r.stk ka ((if A (qstr qT (r.stk ka)) then 1 else 0) :: r.stk ka)⟩

theorem emb_aux (A : List Bool → Prop) (ka : ℕ) (qT : List Bool) (q : NStmt) :
    ∀ v S, oAux A (emb ka qT q) v S =
      if (nAux q v S).l = none then finC A ka qT (nAux q v S) else nAux q v S := by
  induction q with
  | push k f q ih => intro v S; simp only [emb, oAux, nAux]; exact ih _ _
  | peek k f q ih => intro v S; simp only [emb, oAux, nAux]; exact ih _ _
  | pop k f q ih => intro v S; simp only [emb, oAux, nAux]; exact ih _ _
  | load f q ih => intro v S; simp only [emb, oAux, nAux]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [emb, oAux, nAux]
    rcases Bool.eq_false_or_eq_true (f.getD v false) with hb | hb
    · simp only [hb, cond_true]; exact ih₁ _ _
    · simp only [hb, cond_false]; exact ih₂ _ _
  | goto f => intro v S; simp [emb, oAux, nAux]
  | halt =>
    intro v S
    simp only [emb, finS, oAux, nAux, if_true, finC]
    split <;> simp_all

theorem orun_halted {A : List Bool → Prop} {p : OProg} {c : NCfg} (hl : c.l = none) (t : ℕ) :
    orunFor A p t c = some c := by
  obtain ⟨l, v, S⟩ := c
  simp only at hl; subst hl
  cases t <;> simp [orunFor]

end OSim

open OSim

namespace Sim

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (tm : FinTM2)

/-- The oracle program: `Sim.prog` with every `halt` replaced by the final query. -/
noncomputable def oprog (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) : OProg :=
  let p0 := prog tm ia oa
  ⟨p0.k0, p0.k0, p0.k1, p0.main, p0.init, p0.inT, [false, true], p0.m.map (emb p0.k1 p0.outT)⟩

theorem osim (A : List Bool → Prop) (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (t : ℕ) :
    ∀ (c h : TM2.Cfg tm.Γ tm.Λ tm.σ), Inv tm c.stk → c.l ≠ none → runFor tm.m t c = some h →
      orunFor A (oprog tm ia oa) t (encCfg tm c) =
        some (finC A (prog tm ia oa).k1 (prog tm ia oa).outT (encCfg tm h)) ∧ Inv tm h.stk := by
  induction t with
  | zero =>
    rintro ⟨cl, v, S⟩ h _ hl e
    cases cl with
    | none => exact absurd rfl hl
    | some l => simp [runFor] at e
  | succ t ih =>
    rintro ⟨cl, v, S⟩ h hc hl e
    cases cl with
    | none => exact absurd rfl hl
    | some l =>
      simp only [runFor, TM2.step, Option.bind_some] at e
      obtain ⟨s1, s2⟩ := sim tm (tm.m l) (pushes_main tm l) v S hc
      have hm : (oprog tm ia oa).m.getD ((eΛ tm) l : ℕ) .halt =
          emb (prog tm ia oa).k1 (prog tm ia oa).outT (tr tm (tm.m l)) := by
        simp only [oprog, prog]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_ofFn]
        simp
      simp only [encCfg, Option.map_some, orunFor]
      rw [hm, emb_aux]
      have s1' : nAux (tr tm (tm.m l)) ((eσ tm) v) (encS tm S) =
          encCfg tm (TM2.stepAux (tm.m l) v S) := s1
      rw [s1']
      set c' := TM2.stepAux (tm.m l) v S
      by_cases hc' : c'.l = none
      · have : (encCfg tm c').l = none := by simp [encCfg, hc']
        rw [if_pos this]
        have hh : h = c' := by
          have : runFor tm.m t c' = some c' := by
            obtain ⟨l', v', S'⟩ := c'
            simp only at hc'; subst hc'
            cases t <;> simp [runFor]
          rw [this] at e; exact (Option.some.inj e).symm
        subst hh
        refine ⟨orun_halted (by simp [finC]) _, s2⟩
      · have : (encCfg tm c').l ≠ none := by
          intro e'; apply hc'; simpa [encCfg] using e'
        rw [if_neg this]
        exact ih _ _ s2 hc' e

theorem oinit_eq (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (x : List Bool) :
    OInit (oprog tm ia oa) x [] = NInit (prog tm ia oa) x := by
  simp only [OInit, NInit, oprog]
  congr 1
  funext j
  by_cases hj : j = (prog tm ia oa).k0 <;> simp [hj]

theorem query_out (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (y : List Bool)
    (hI : Inv tm (haltList tm (y.map oa.invFun)).stk) :
    qstr (prog tm ia oa).outT ((encCfg tm (haltList tm (y.map oa.invFun))).stk (prog tm ia oa).k1) = y := by
  have hk : (haltList tm (y.map oa.invFun)).stk tm.k₁ = y.map oa.invFun := by
    unfold haltList; dsimp only; rw [dif_pos rfl]; rfl
  simp only [encCfg]
  rw [show (prog tm ia oa).k1 = (eK tm tm.k₁ : ℕ) from rfl, encS_eK, hk, qstr, List.map_map,
    List.map_map]
  conv_rhs => rw [← List.map_id y]
  apply List.map_congr_left
  intro b hb
  have hm : (⟨tm.k₁, oa.invFun b⟩ : Σ k, tm.Γ k) ∈ vals tm :=
    hI _ _ (by rw [hk]; exact List.mem_map_of_mem hb)
  simp only [Function.comp, prog]
  rw [range_map_getD _ _ (code_lt tm hm), dec_code tm hm]
  simp

end Sim

/-- **`P^A` contains every language polytime-reducible to `A`.** -/
theorem PO_of_reduction (A : Language) {g : List Bool → List Bool} (hg : PS g) (L : Language)
    (hL : ∀ x, L x ↔ A (g x)) : InPO A L := by
  obtain ⟨h⟩ := hg
  refine ⟨Sim.oprog h.tm h.inputAlphabet h.outputAlphabet, h.time, fun x => ?_⟩
  have hr := runFor_computable h.toTM2ComputableInTime x
  obtain ⟨i1, i2⟩ := Sim.init_enc h.tm h.inputAlphabet h.outputAlphabet x
  have hl : (initList h.tm (List.map h.inputAlphabet.invFun (strEnc x))).l ≠ none := by
    simp [initList]
  obtain ⟨s1, s2⟩ := Sim.osim h.tm A h.inputAlphabet h.outputAlphabet _ _ _ i2 hl hr
  rw [i1, ← Sim.oinit_eq] at s1
  refine ⟨_, s1, ?_⟩
  rw [hL x]
  have hq : qstr (Sim.prog h.tm h.inputAlphabet h.outputAlphabet).outT
      ((Sim.encCfg h.tm (haltList h.toTM2ComputableInTime.tm
        (List.map h.toTM2ComputableInTime.outputAlphabet.invFun (strEnc (g x))))).stk
        (Sim.prog h.tm h.inputAlphabet h.outputAlphabet).k1) = g x :=
    Sim.query_out h.tm h.inputAlphabet h.outputAlphabet (g x) s2
  simp only [OAccepts, finC]
  rw [show (Sim.oprog h.tm h.inputAlphabet h.outputAlphabet).ka =
    (Sim.prog h.tm h.inputAlphabet h.outputAlphabet).k1 from rfl, Function.update_self, hq]
  simp only [List.head?_cons, Option.map_some, Option.some.injEq]
  split <;> simp_all [Sim.oprog]

/-! ### The self-referential oracle -/

/-- Parsing `z = 1ᴺ 0 1ᶜ 0 1ᵀ 0 1^Q 0 x`. -/
def zC (z : List Bool) : ℕ := lpN (lpX z)
def zT (z : List Bool) : ℕ := lpN (lpX (lpX z))
def zQ (z : List Bool) : ℕ := lpN (lpX (lpX (lpX z)))
def zX (z : List Bool) : List Bool := lpX (lpX (lpX (lpX z)))

/-- **The oracle `A` with `P^A = NP^A`.** -/
noncomputable def Aself (z : List Bool) : Prop :=
  ∃ p : OProg, Encodable.decode (zC z) = some p ∧ ∃ w : List Bool, w.length = zQ z ∧ ∃ h,
    orunFor (fun s => if _ : s.length < z.length then Aself s else False) p (zT z)
      (OInit p (zX z) w) = some h ∧ OAccepts p h
termination_by z.length

theorem Aself_eq (z : List Bool) : Aself z ↔
    ∃ p : OProg, Encodable.decode (zC z) = some p ∧ ∃ w : List Bool, w.length = zQ z ∧ ∃ h,
      orunFor (fun s => if _ : s.length < z.length then Aself s else False) p (zT z)
        (OInit p (zX z) w) = some h ∧ OAccepts p h := by
  rw [Aself]

/-- The query string for `x` (program `p`, time `T`, witness length `Q`). -/
def zOf (p : OProg) (T Q : Polynomial ℕ) (x : List Bool) : List Bool :=
  List.replicate (x.length + Q.eval x.length + p.cP * T.eval x.length) true ++ false ::
    (List.replicate (Encodable.encode p) true ++ false ::
      (List.replicate (T.eval x.length) true ++ false ::
        (List.replicate (Q.eval x.length) true ++ false :: x)))

theorem zOf_PS (p : OProg) (T Q : Polynomial ℕ) : PS (zOf p T Q) := by
  have h1 := PU.poly (Polynomial.X + Q + Polynomial.C p.cP * T)
  have h2 := PU.const (Encodable.encode p)
  have h3 := PU.poly T
  have h4 := PU.poly Q
  refine (PS.append h1 (PS.cons false (PS.append h2 (PS.cons false (PS.append h3
    (PS.cons false (PS.append h4 (PS.cons false PS.id)))))))).congr (fun x => ?_)
  simp [zOf]

/-- **`NP^Aself ⊆ P^Aself`.** -/
theorem NPO_sub_PO (L : Language) (hL : InNPO Aself L) : InPO Aself L := by
  obtain ⟨p, T, Q, hp⟩ := hL
  refine PO_of_reduction Aself (zOf_PS p T Q) L (fun x => ?_)
  set z := zOf p T Q x
  have hC : zC z = Encodable.encode p := by simp [z, zC, zOf, lpX_rep, lpN_rep]
  have hT : zT z = T.eval x.length := by simp [z, zT, zOf, lpX_rep, lpN_rep]
  have hQ : zQ z = Q.eval x.length := by simp [z, zQ, zOf, lpX_rep, lpN_rep]
  have hX : zX z = x := by simp [z, zX, zOf, lpX_rep]
  have hz : x.length + Q.eval x.length + p.cP * T.eval x.length < z.length := by
    simp [z, zOf]
  -- the restricted oracle gives the same runs
  have hrun : ∀ w : List Bool, w.length = Q.eval x.length →
      orunFor (fun s => if _ : s.length < z.length then Aself s else False) p (T.eval x.length)
        (OInit p x w) = orunFor Aself p (T.eval x.length) (OInit p x w) := by
    intro w hw
    apply orun_congr
    intro s hs
    have := orunQ_bound _ p _ _ _ (OInit_bound p x w) s hs
    rw [dif_pos (by omega)]
  rw [(hp x).2, Aself_eq, hC, hT, hQ, hX]
  simp only [Encodable.encodek, Option.some.injEq, exists_eq_left']
  constructor
  · rintro ⟨w, h, hw, e, ha⟩; exact ⟨w, hw, h, by rw [hrun w hw]; exact e, ha⟩
  · rintro ⟨w, hw, h, e, ha⟩; exact ⟨w, h, hw, by rw [← hrun w hw]; exact e, ha⟩

/-- **Baker–Gill–Solovay (1): there is an oracle `A` with `P^A = NP^A`.** -/
theorem exists_oracle_P_eq_NP : ∃ A : Language, ∀ L, InPO A L ↔ InNPO A L :=
  ⟨Aself, fun L => ⟨InPO.toNPO, NPO_sub_PO L⟩⟩

/-- **Baker–Gill–Solovay.** Both relativized outcomes occur.

Meta-remark (documentation only, not a theorem): every argument that goes through unchanged when
all machines get the same oracle ("relativizes") would prove the same answer for `P^O` vs `NP^O`
for every oracle `O`; since both answers occur, no relativizing argument settles P vs NP. This
file does not formalize "relativizing proof", and P vs NP itself is untouched. -/
theorem baker_gill_solovay :
    (∃ A : Language, ∀ L, InPO A L ↔ InNPO A L) ∧ (∃ B : Language, ∃ L, InNPO B L ∧ ¬ InPO B L) :=
  ⟨exists_oracle_P_eq_NP, exists_oracle_P_ne_NP⟩

end PvnpReal
