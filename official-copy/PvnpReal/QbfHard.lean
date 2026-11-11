/-
  PvnpReal.QbfHard — **TQBF is PSPACE-hard**, hence PSPACE-complete, and `P = PSPACE ↔ TQBF ∈ P`.

  For `L ∈ PSPACE` decided by `h` in space `p(n)`:
  * the verifier wrapper `verifierTM` (from `PSubsetNP.lean`) reads `x #` and then runs `h`; its
    halt-and-stay run stays within space `|x| + 1 + P·(2|x|+3) + p(|x|)` forever and has halted by
    step `2^{k(x)}`, `k(x) = A + B·p(|x|) + |x| + 3` (configuration counting, `steps_le_card`);
  * the Cook–Levin tableau `tab2CS` of that run with `T = 2^{k(x)}` rows is satisfiable iff `x ∈ L`
    (`tab2_sound`, `tab2_complete`);
  * by `QbfTab` it is satisfiable iff a chain of `2^{k(x)}` row blocks exists, and by `QbfSav` iff
    the Savitch QBF `redQ x` is true;
  * `redQ` is computed by a polynomial-time `FinTM2` (`PS.redQ`).
-/
import PvnpReal.QbfTab
import PvnpReal.PSubsetNP

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

/-! ### Runs: flip-bind vs halt-and-stay -/

section Runs

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (m : Λ → Stmt Γ Λ σ)

theorem stay_of_flip : ∀ (i : ℕ) (c c' : Cfg Γ Λ σ),
    (flip bind (TM2.step m))^[i] (some c) = some c' → (stepStay m)^[i] c = c' := by
  intro i
  induction i with
  | zero => intro c c' h; simpa using h
  | succ i ih =>
    intro c c' h
    rw [Function.iterate_succ_apply] at h
    rw [Function.iterate_succ_apply]
    change (flip bind (TM2.step m))^[i] (TM2.step m c) = some c' at h
    rcases hs : TM2.step m c with _ | c1
    · rw [hs, flip_bind_iterate_none] at h; cases h
    · rw [hs] at h
      have : stepStay m c = c1 := by unfold stepStay; rw [hs]; rfl
      rw [this]; exact ih c1 c' h

theorem flip_some_of_le {α : Type} (F : α → Option α) (N : ℕ) (c c' : α)
    (h : (flip bind F)^[N] (some c) = some c') (t : ℕ) (ht : t ≤ N) :
    ∃ c'', (flip bind F)^[t] (some c) = some c'' := by
  rcases e : (flip bind F)^[t] (some c) with _ | c''
  · rw [show N = (N - t) + t by omega, Function.iterate_add_apply, e, flip_bind_iterate_none] at h
    cases h
  · exact ⟨c'', rfl⟩

end Runs

/-! ### The verifier wrapper on `x #` -/

section Mach

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool)

theorem stepStay_lift (c : TM2.Cfg M.Γ M.Λ M.σ) :
    stepStay (Vm M e) (liftCfg M c) = liftCfg M (stepStay M.m c) := by
  unfold stepStay; erw [step_lift M e c]; cases TM2.step M.m c <;> rfl

theorem iterate_stepStay_lift : ∀ (t : ℕ) (c : TM2.Cfg M.Γ M.Λ M.σ),
    (stepStay (Vm M e))^[t] (liftCfg M c) = liftCfg M ((stepStay M.m)^[t] c) := by
  intro t
  induction t with
  | zero => intro c; rfl
  | succ t ih => intro c; rw [Function.iterate_succ_apply, stepStay_lift]; exact ih _

theorem lift_len (c : TM2.Cfg M.Γ M.Λ M.σ) (B : ℕ) (h : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, ((liftCfg M c).stk k).length ≤ B := by
  intro k
  rcases k with _ | _ | k
  · simp [liftCfg, mkStk]
  · simp [liftCfg, mkStk]
  · exact h k

theorem verifier_pre (x : List Bool) :
    (flip bind (TM2.step (Vm M e)))^[(x.length + 1) + (1 + (x.length + 1))]
        (some ⟨some (Sum.inr Phase.A), (M.initialState, none),
          mkStk M (x.map some ++ [none]) [] (fun _ => [])⟩) =
      some (liftCfg M (initList M (x.map e.symm))) := by
  have hA := runA M e x (M.initialState, none) [] [] (fun _ => [])
  have hB := runB M e [] (M.initialState, some none) (x.reverse ++ []) (fun _ => [])
  have hC := runC M e (x.reverse ++ []) (M.initialState, none) (fun _ => [])
  simp only [List.append_nil, List.length_reverse, List.length_nil] at hA hB hC
  rw [Function.iterate_add_apply (m := x.length + 1), Function.iterate_add_apply (m := 1)]
  rw [hA, hB, hC]
  rw [List.reverse_reverse, start_eq]

theorem initCfg_verifier (l : List (Option Bool)) :
    @Eq (TM2.Cfg (VΓ M) (VΛ M) (Vσ M))
      (initCfg (verifierTM M e).main (verifierTM M e).initialState (verifierTM M e).k₀ l)
      ⟨some (Sum.inr Phase.A), (M.initialState, none), mkStk M l [] (fun _ => [])⟩ := by
  simp only [initCfg]
  congr 1
  funext j
  rcases j with _ | _ | j
  · rfl
  · rfl
  · rfl

/-- Every configuration of a FinTM2 run uses only symbols from `clL`. -/
theorem run_syms' (c : TM2.Cfg M.Γ M.Λ M.σ) (hc : SymsIn (clL M) c.stk) (t : ℕ) :
    SymsIn (clL M) ((stepStay M.m)^[t] c).stk := by
  induction t with
  | zero => exact hc
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    refine stepStay_syms M.m _ (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) _
      (fun lab x hx => ?_) _ ih
    simp only [clL, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨lab, by simp, hx⟩

end Mach

/-! ### Shifted constraint clauses -/

section Shift

variable {D : Type*} [DecidableEq D]

theorem hotVar_shift (U : List D) (v s : ℕ) (d : D) :
    hotVar U (v + s) d = hotVar U v d + s * U.length := by
  unfold hotVar; ring

theorem conClauses_shC (U : List D) (c : Constraint D) (s : ℕ) (a : ℕ → Bool) :
    evalCNF (conClauses U (shC s c)) a = evalCNF (conClauses U c) (fun v => a (v + s * U.length)) := by
  simp only [conClauses, shC, forbidClause, List.length_map, evalCNF, evalClause, List.all_map,
    List.any_map, List.zip_map_left, Function.comp_def, evalLiteral, hotVar_shift, Prod.map,
    id]

theorem alo_shift (U : List D) (v s : ℕ) (a : ℕ → Bool) :
    evalClause (aloClause U (v + s)) a = evalClause (aloClause U v) (fun w => a (w + s * U.length)) := by
  simp only [aloClause, evalClause, List.any_map, Function.comp_def, evalLiteral, hotVar_shift]

theorem HC_shift (U : List D) (cs : List (Constraint D)) (s : ℕ) (a : ℕ → Bool) :
    evalCNF (HC U (cs.map (shC s))) a = true ↔
      evalCNF (HC U cs) (fun v => a (v + s * U.length)) = true := by
  rw [HC_iff, HC_iff, List.forall_mem_map]
  simp only [conClauses_shC]

theorem rdF_two (a : ℕ → Bool) (p n : ℕ) : rdF a p n ++ rdF a (p + n) n = rdF a p (2 * n) := by
  unfold rdF
  rw [two_mul, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp_def, Nat.add_assoc]

end Shift

/-! ### Row blocks at any row -/

section TabT

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [DecidableEq (V2 Γ Λ σ)]
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (S : ℕ) (U : List (V2 Γ Λ σ))

/-- Rows `t`, `t+1` and the transition between them. -/
noncomputable def tabBt (t : ℕ) : CNF :=
  AL U (sv2 Ks S t) (2 * W2 Ks S) ++
    HC U (csRow d Ks S t ++ csRow d Ks S (t + 1) ++ csTrans m d P Ks S t)

theorem tabBt_shift (t : ℕ) (a : ℕ → Bool) :
    evalCNF (tabBt m d P Ks S U t) a = true ↔
      evalCNF (tabB0 m d P Ks S U) (fun v => a (v + t * W2 Ks S * U.length)) = true := by
  unfold tabBt tabB0
  rw [evalCNF_app, evalCNF_app, Bool.and_eq_true, Bool.and_eq_true]
  have r0 := csRow_shift (Γ := Γ) (Λ := Λ) (σ := σ) d Ks S 0 t
  have r1 := csRow_shift (Γ := Γ) (Λ := Λ) (σ := σ) d Ks S 1 t
  have r2 := csTrans_shift m d P Ks S 0 t
  rw [Nat.zero_add] at r0 r2
  rw [Nat.add_comm 1 t] at r1
  rw [r0, r1, r2, ← List.map_append, ← List.map_append, HC_shift]
  apply and_congr_left'
  rw [AL_iff, AL_iff]
  apply forall_congr'; intro i; apply imp_congr_right; intro _
  rw [show sv2 Ks S t + i = (sv2 Ks S 0 + i) + t * W2 Ks S by unfold sv2; ring, alo_shift]

theorem tabBt_iff (hS2 : 2 * d + P + 1 ≤ S) (t : ℕ) (a : ℕ → Bool) :
    evalCNF (tabBt m d P Ks S U t) a = true ↔
      tabR m d P Ks S U (rdF a (2 * U.length + t * (W2 Ks S * U.length)) (W2 Ks S * U.length))
        (rdF a (2 * U.length + t * (W2 Ks S * U.length) + W2 Ks S * U.length)
          (W2 Ks S * U.length)) := by
  rw [tabBt_shift, tabR, List.append_assoc, rdF_two]
  rw [evalCNF_congr _ _ (asg (List.replicate (2 * U.length) false ++
    rdF a (2 * U.length + t * (W2 Ks S * U.length)) (2 * (W2 Ks S * U.length))))]
  intro cl hcl l hl
  obtain ⟨h1, h2⟩ := tabB0_vars m d P Ks S U hS2 cl hcl l hl
  obtain ⟨i, hi⟩ : ∃ i, l.var = 2 * U.length + i := ⟨l.var - 2 * U.length, by omega⟩
  rw [hi]
  have e : (List.replicate (2 * U.length) false).length = 2 * U.length := by simp
  have hh := asg_append_right (List.replicate (2 * U.length) false)
    (rdF a (2 * U.length + t * (W2 Ks S * U.length)) (2 * (W2 Ks S * U.length))) i
  rw [e] at hh
  rw [hh]
  unfold asg
  rw [rdF_getD _ _ _ _ (by omega)]
  congr 1
  rw [Nat.mul_assoc]; ring

end TabT

/-! ### The reduction for a PSPACE decider -/

open scoped Classical

section Hard

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {f : List Bool → Bool} (h : TM2ComputableInTime strEnc encodeBool f) (p : Polynomial ℕ)

/-- The machine whose run is tabulated: read `x #`, then run the decider. -/
noncomputable abbrev hV : FinTM2 := verifierTM h.tm h.inputAlphabet

noncomputable def hsb (b : Bool) : (hV h).Γ (hV h).k₀ := (some b : Option Bool)
noncomputable def hsep : (hV h).Γ (hV h).k₀ := (none : Option Bool)
noncomputable def hacc : (hV h).Γ (hV h).k₁ := h.outputAlphabet.invFun true

/-- Preprocessing steps of the wrapper on `x #`. -/
def htp (x : List Bool) : ℕ := x.length + 1 + (1 + (x.length + 1))

/-- A bound on every stack, at every time, of the halt-and-stay run. -/
noncomputable def hB0 (x : List Bool) : ℕ :=
  x.length + 1 + pushTotal (hV h) * htp x + p.eval x.length

/-- Row depth of the tableau. -/
noncomputable def hS (x : List Bool) : ℕ :=
  hB0 h p x + 2 * clD (hV h) + pushTotal (hV h) + x.length + 3

noncomputable def hA : ℕ := (Nat.card h.tm.Λ + 1) * Nat.card h.tm.σ
noncomputable def hBb : ℕ := (Nat.card (symSet h.tm) + 2) ^ Nat.card h.tm.K

/-- Number of Savitch levels: the run has halted by step `2 ^ hk x`. -/
noncomputable def hk (x : List Bool) : ℕ := hA h + hBb h * p.eval x.length + x.length + 3

noncomputable def hc0 (x : List Bool) : TM2.Cfg (hV h).Γ (hV h).Λ (hV h).σ :=
  initCfg (hV h).main (hV h).initialState (hV h).k₀
    (x.map (hsb h) ++ hsep h :: ([] : List Bool).map (hsb h))

theorem hc0_eq (x : List Bool) : hc0 h x = ⟨some (Sum.inr Phase.A), (h.tm.initialState, none),
    mkStk h.tm (x.map some ++ [none]) [] (fun _ => [])⟩ :=
  initCfg_verifier h.tm h.inputAlphabet _

theorem h_evals (x : List Bool) :
    (flip bind (TM2.step h.tm.m))^[(h.outputsFun x).steps]
        (some (initList h.tm (x.map h.inputAlphabet.symm))) =
      some (haltList h.tm ((encodeBool (f x)).map h.outputAlphabet.invFun)) :=
  (h.outputsFun x).evals_in_steps

theorem h_pre (x : List Bool) :
    (stepStay (hV h).m)^[htp x] (hc0 h x) =
      liftCfg h.tm (initList h.tm (x.map h.inputAlphabet.symm)) := by
  rw [hc0_eq]
  exact stay_of_flip _ _ _ _ (verifier_pre h.tm h.inputAlphabet x)

theorem h_after (x : List Bool) (t : ℕ) :
    (stepStay (hV h).m)^[htp x + t] (hc0 h x) =
      liftCfg h.tm ((stepStay h.tm.m)^[t] (initList h.tm (x.map h.inputAlphabet.symm))) := by
  rw [Nat.add_comm, Function.iterate_add_apply, h_pre]
  exact iterate_stepStay_lift h.tm h.inputAlphabet t _

theorem h_final (x : List Bool) (N : ℕ) (hN : (h.outputsFun x).steps + htp x ≤ N) :
    (stepStay (hV h).m)^[N] (hc0 h x) =
      haltList (hV h) ((encodeBool (f x)).map h.outputAlphabet.invFun) := by
  have hrun := verifier_run h.tm h.inputAlphabet x [] _ _ (h_evals h x)
  rw [hc0_eq]
  refine Eq.trans (stepStay_of_evals (Vm h.tm h.inputAlphabet) _ _ _ rfl hrun N ?_)
    (haltList_verifier _ _ _).symm
  simp only [htp, List.length_nil] at hN ⊢
  omega

theorem h_acc (x : List Bool) (N : ℕ) (hN : (h.outputsFun x).steps + htp x ≤ N) :
    cellOf ((stepStay (hV h).m)^[N] (hc0 h x)) (hV h).k₁ 0 = some ⟨(hV h).k₁, hacc h⟩ ↔
      f x = true := by
  rw [h_final h x N hN]
  simp [cellOf, haltList_stk, encodeBool, hacc]
  constructor
  · intro e
    obtain ⟨a, ha, e2⟩ := e
    have ha' : h.outputAlphabet.symm (f x) = a := Option.some.inj ha
    subst ha'
    have e3 := eq_of_heq (Sigma.mk.inj_iff.1 e2).2
    exact h.outputAlphabet.symm.injective e3
  · intro e; rw [e]; exact ⟨_, rfl, rfl⟩

theorem h_init_len (x : List Bool) : ∀ k, ((hc0 h x).stk k).length ≤ x.length + 1 := by
  intro k
  by_cases hk : k = (hV h).k₀
  · subst hk; simp [hc0, initCfg]
  · simp [hc0, initCfg, hk]

theorem h_len (hsp : SpaceBounded h (fun n => p.eval n)) (x : List Bool) (t : ℕ) (k) :
    (((stepStay (hV h).m)^[t] (hc0 h x)).stk k).length ≤ hB0 h p x := by
  by_cases ht : t ≤ htp x
  · have := iterate_stepStay_len (hV h).m (hc0 h x) (x.length + 1) (pushTotal (hV h))
      (pushes_le_total (hV h)) (h_init_len h x) t k
    have := Nat.mul_le_mul_left (pushTotal (hV h)) ht
    unfold hB0; omega
  · obtain ⟨t', rfl⟩ : ∃ t', t = htp x + t' := ⟨t - htp x, by omega⟩
    rw [h_after]
    refine lift_len h.tm _ _ (fun k' => ?_) k
    have hM := h_evals h x
    suffices hb : (((stepStay h.tm.m)^[t'] (initList h.tm (x.map h.inputAlphabet.symm))).stk
        k').length ≤ p.eval x.length by unfold hB0; omega
    by_cases hle : t' ≤ (h.outputsFun x).steps
    · obtain ⟨c'', hc''⟩ := flip_some_of_le _ _ _ _ hM t' hle
      rw [stay_of_flip _ _ _ _ hc'']
      exact hsp x t' c'' hle hc'' k'
    · rw [stepStay_of_evals _ _ _ _ rfl hM t' (by omega)]
      exact hsp x _ _ le_rfl hM k'

theorem h_steps (hsp : SpaceBounded h (fun n => p.eval n)) (x : List Bool) :
    (h.outputsFun x).steps + htp x ≤ 2 ^ hk h p x := by
  have hs := steps_le_card h _ hsp x
  have a1 : hA h ≤ 2 ^ hA h := (Nat.lt_two_pow_self).le
  have a2 : hBb h ^ p.eval x.length ≤ 2 ^ (hBb h * p.eval x.length) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have a3 : (h.outputsFun x).steps ≤ 2 ^ (hA h + hBb h * p.eval x.length) := by
    rw [pow_add]
    exact hs.trans (Nat.mul_le_mul a1 a2)
  have a4 : htp x ≤ 2 ^ (x.length + 2) := by
    have := (Nat.lt_two_pow_self (n := x.length))
    rw [pow_add]; unfold htp; omega
  have a5 : 2 ^ (hA h + hBb h * p.eval x.length) ≤
      2 ^ (hA h + hBb h * p.eval x.length + (x.length + 2)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have a6 : 2 ^ (x.length + 2) ≤ 2 ^ (hA h + hBb h * p.eval x.length + (x.length + 2)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : hk h p x = hA h + hBb h * p.eval x.length + (x.length + 2) + 1 := by unfold hk; omega
  rw [this, pow_succ]
  omega

theorem hV_d (lab : (hV h).Λ) : sdepth ((hV h).m lab) ≤ clD (hV h) :=
  Finset.le_sup (f := fun l => sdepth ((hV h).m l)) (Finset.mem_univ lab)

theorem hV_Ks (k : (hV h).K) : k ∈ clKs (hV h) := by simp [clKs]

theorem h_S1 (x : List Bool) : x.length + 2 + 0 ≤ hS h p x := by unfold hS; omega
theorem h_S2 (x : List Bool) : 2 * clD (hV h) + pushTotal (hV h) + 1 ≤ hS h p x := by
  unfold hS; omega

noncomputable def hU : List (V2 (hV h).Γ (hV h).Λ (hV h).σ) := tab2Values (clD (hV h)) (clL (hV h))

theorem hU_ne : hU h ≠ [] := tab2Values_ne _ _

/-- The tableau constraints for input `x`. -/
noncomputable def hCS (x : List Bool) :=
  tab2CS (hV h).m (clD (hV h)) (pushTotal (hV h)) (clKs (hV h)) (hS h p x) (2 ^ hk h p x)
    (hV h).k₀ (hV h).k₁ (hV h).main (hV h).initialState (hsb h) (hsep h) 0 (hacc h) x

theorem hCS_iff (hsp : SpaceBounded h (fun n => p.eval n)) (x : List Bool) :
    CSPSat (hU h) (hCS h p x) ↔ f x = true := by
  have hlen : ∀ w : List Bool, w.length ≤ 0 → ∀ t ≤ 2 ^ hk h p x, ∀ k,
      (((stepStay (hV h).m)^[t] (initCfg (hV h).main (hV h).initialState (hV h).k₀
        (x.map (hsb h) ++ hsep h :: w.map (hsb h)))).stk k).length ≤
          hS h p x - (clD (hV h) + 1) := by
    intro w hw t _ k
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)]
    have := h_len h p hsp x t k
    unfold hc0 at this
    unfold hS; omega
  constructor
  · intro hsat
    obtain ⟨w, hw, hacc'⟩ := tab2_sound (hd := hV_d h) (hP := pushes_le_total (hV h))
      (hKs := hV_Ks h) _ (tab2Values_win _ _) (h_S1 h p x) (h_S2 h p x) hlen hsat
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)] at hacc'
    exact (h_acc h x _ (h_steps h p hsp x)).1 hacc'
  · intro hf
    have hsb' : ∀ b, (⟨(hV h).k₀, hsb h b⟩ : Sig (hV h).Γ) ∈ clL (hV h) := fun b => by
      simp [clL]
    have hsyms : SymsIn (clL (hV h)) (hc0 h x).stk := by
      intro k g hg
      by_cases hk : k = (hV h).k₀
      · subst hk; simp [clL]
      · simp [hc0, initCfg, hk] at hg
    exact tab2_complete (hd := hV_d h) (hP := pushes_le_total (hV h)) (hKs := hV_Ks h)
      (h_S1 h p x) (h_S2 h p x) [] le_rfl (hlen [] le_rfl)
      ((h_acc h x _ (h_steps h p hsp x)).2 hf) _
      (assign2_mem _ _ _ _ _ _ hsb' _ (fun t => run_syms' (hV h) _ hsyms t))

/-! ### The Savitch QBF -/

/-- Hot bits per tableau row. -/
noncomputable def hn (x : List Bool) : ℕ := W2 (clKs (hV h)) (hS h p x) * (hU h).length

noncomputable def hTop (x : List Bool) : CNF :=
  tabTop (clKs (hV h)) (hS h p x) (hV h).k₀ (hV h).k₁ (hV h).main (hV h).initialState (hsb h)
    (hsep h) 0 (hacc h) x (hU h)

noncomputable def hBot (x : List Bool) : CNF :=
  tabBt (hV h).m (clD (hV h)) (pushTotal (hV h)) (clKs (hV h)) (hS h p x) (hU h) (4 * hk h p x)

/-- **The reduction**: the Savitch QBF for `x`. -/
noncomputable def redQBF (x : List Bool) : QBF :=
  ⟨List.replicate (2 * (hU h).length + 2 * hn h p x) false ++ lvlPre (hn h p x) (hk h p x),
    hTop h p x ++ (lvlCNF (hn h p x) (2 * (hU h).length) (hk h p x) ++ hBot h p x)⟩

noncomputable def redQ (x : List Bool) : List Bool := encodeQBF (redQBF h p x)

theorem redQ_correct (hsp : SpaceBounded h (fun n => p.eval n)) (x : List Bool) :
    f x = true ↔ TQBF (redQ h p x) := by
  have hUl : 0 < (hU h).length := List.length_pos_iff.2 (hU_ne h)
  have hW : 0 < W2 (clKs (hV h)) (hS h p x) := by unfold W2; omega
  have hn1 : 1 ≤ hn h p x := Nat.mul_pos hW hUl
  rw [redQ, TQBF_encode, ← hCS_iff h p hsp x]
  simp only [QBF.val, redQBF]
  have hTv : ∀ cl ∈ hTop h p x, ∀ l ∈ cl, l.var < 2 * (hU h).length + 2 * hn h p x := by
    unfold hTop hn
    exact tabTop_vars _ _ _ _ _ _ _ _ _ _ _ _ (hV_Ks h _) (hV_Ks h _) (h_S1 h p x)
  rw [sav_correct (tabR (hV h).m (clD (hV h)) (pushTotal (hV h)) (clKs (hV h)) (hS h p x) (hU h))
    (hn h p x) (2 * (hU h).length) (hk h p x) hn1 (hTop h p x) (hBot h p x) hTv
    (fun a => by
      rw [hBot, tabBt_iff _ _ _ _ _ _ (h_S2 h p x)]
      unfold hn
      rw [show 4 * hk h p x * (W2 (clKs (hV h)) (hS h p x) * (hU h).length) =
        4 * (W2 (clKs (hV h)) (hS h p x) * (hU h).length) * hk h p x by ring])]
  constructor
  · intro hc
    unfold hTop hn
    obtain ⟨g, hg, htop, hch⟩ := chain_of_tab _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hU_ne h) (hV_Ks h _)
      (hV_Ks h _) (h_S1 h p x) (h_S2 h p x) _ (Nat.one_le_two_pow) hc
    refine ⟨g, hg, htop, ?_⟩
    exact (sav_chain _ _ _ _ _ (rdF_length _ _ _) (rdF_length _ _ _)).2 hch
  · rintro ⟨g, -, htop, hsav⟩
    unfold hTop hn at *
    exact tab_of_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hU_ne h) (hV_Ks h _) (hV_Ks h _)
      (h_S1 h p x) (h_S2 h p x) _ (Nat.one_le_two_pow) g htop
      ((sav_chain _ _ _ _ _ (rdF_length _ _ _) (rdF_length _ _ _)).1 hsav)

end Hard

end PvnpReal
