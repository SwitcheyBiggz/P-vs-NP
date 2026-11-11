/-
  PvnpReal.NHard — Savitch: every NPSPACE language reduces to TQBF (correctness part).

  * Path shortening (`NTM.short`): if a space-bounded NTM accepts `x`, it accepts within fewer
    steps than there are configuration codes (`cfgCode`), by cutting out a repeated configuration
    and splicing the choice sequences; halted configurations stay, so it accepts at row `2^k`.
  * `nCS_iff`: the nondeterministic tableau with `2^k` rows is satisfiable iff `N` accepts `x`.
  * `redQN_correct`: `N` accepts `x` iff the Savitch QBF over row blocks of the nondeterministic
    tableau is true.
-/
import PvnpReal.QbfTabN

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

namespace NTM

variable (N : NTM)

theorem runC_add (bs : ℕ → Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) (i : ℕ) :
    ∀ r, N.runC bs c (i + r) = N.runC (fun s => bs (i + s)) (N.runC bs c i) r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    show N.nstep (bs (i + r)) (N.runC bs c (i + r)) = N.nstep (bs (i + r)) _
    rw [ih]

theorem runC_congr (bs bs' : ℕ → Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) :
    ∀ t, (∀ s < t, bs s = bs' s) → N.runC bs c t = N.runC bs' c t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    show N.nstep (bs t) (N.runC bs c t) = N.nstep (bs' t) (N.runC bs' c t)
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

theorem nstep_halted (b : Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) (h : c.l = none) :
    N.nstep b c = c := by
  unfold nstep relab
  rw [stepStay_halted _ _ h]
  rcases c with ⟨l, v, S⟩
  simp only at h; subst h
  cases b <;> rfl

theorem runC_halted (bs : ℕ → Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) (t : ℕ)
    (h : (N.runC bs c t).l = none) : ∀ r, N.runC bs c (t + r) = N.runC bs c t := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    show N.nstep (bs (t + r)) (N.runC bs c (t + r)) = _
    rw [ih, nstep_halted _ _ _ h]

theorem stepStay_good (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) (hc : GoodS (symSet N.tm) c.stk) :
    GoodS (symSet N.tm) (stepStay N.tm.m c).stk := by
  rcases c with ⟨_ | l, v, S⟩
  · exact hc
  · exact stepAux_good _ _ (fun x hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)) v S hc

theorem runC_good (bs : ℕ → Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ)
    (hc : GoodS (symSet N.tm) c.stk) : ∀ t, GoodS (symSet N.tm) (N.runC bs c t).stk := by
  intro t
  induction t with
  | zero => exact hc
  | succ t ih => exact N.stepStay_good _ ih

theorem init_good (x : List Bool) : GoodS (symSet N.tm) (N.init x).stk := by
  intro k a ha
  by_cases hk : k = N.tm.k₀
  · subst hk; exact Or.inr ⟨a, rfl⟩
  · simp [init, initCfg, hk] at ha

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- The type of configuration codes for space `S`. -/
abbrev Code (S : ℕ) := Option N.tm.Λ × N.tm.σ × (N.tm.K → Fin S → Option (Option (symSet N.tm)))

/-- **Path shortening.** An accepting run can be replaced by one accepting in fewer steps than
there are configuration codes. -/
theorem short {Sf : ℕ → ℕ} (hsp : N.SpaceBounded Sf) (x : List Bool) :
    ∀ t (bs : ℕ → Bool), N.Acc (N.run bs x t) →
      ∃ (bs' : ℕ → Bool) (t' : ℕ), t' < Nat.card (N.Code (Sf x.length)) ∧ N.Acc (N.run bs' x t') := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro bs hacc
  by_cases ht : t < Nat.card (N.Code (Sf x.length))
  · exact ⟨bs, t, ht, hacc⟩
  let g : Fin (t + 1) → N.Code (Sf x.length) := fun j => cfgCode N.tm (Sf x.length) (N.run bs x j.1)
  have hni : ¬ Function.Injective g := by
    intro hg
    have := Nat.card_le_card_of_injective g hg
    simp only [Nat.card_eq_fintype_card (α := Fin (t + 1)), Fintype.card_fin] at this
    omega
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i0, j0, he, hne⟩ := hni
  have key : ∀ i j : Fin (t + 1), i.1 < j.1 → g i = g j →
      ∃ (bs' : ℕ → Bool) (t' : ℕ), t' < Nat.card (N.Code (Sf x.length)) ∧ N.Acc (N.run bs' x t') := by
    intro i j hij hg
    have ec : N.run bs x i.1 = N.run bs x j.1 :=
      cfgCode_inj N.tm _ _ _ (N.runC_good bs _ (N.init_good x) _) (N.runC_good bs _ (N.init_good x) _)
        (fun k => hsp x bs _ k) (fun k => hsp x bs _ k) hg
    let bs' : ℕ → Bool := fun s => if s < i.1 then bs s else bs (s + (j.1 - i.1))
    have h1 : N.run bs' x i.1 = N.run bs x i.1 :=
      N.runC_congr bs' bs _ _ (fun s hs => by simp only [bs', if_pos hs])
    have h2 : ∀ r, N.run bs' x (i.1 + r) = N.run bs x (j.1 + r) := by
      intro r
      unfold run
      rw [N.runC_add bs' _ i.1 r, N.runC_add bs _ j.1 r]
      have h1' : N.runC bs' (N.init x) i.1 = N.runC bs (N.init x) j.1 := h1.trans ec
      rw [h1']
      congr 1
      funext s
      simp only [bs', if_neg (show ¬ (i.1 + s < i.1) by omega)]
      congr 1; omega
    obtain ⟨r, hr⟩ : ∃ r, t = j.1 + r := ⟨t - j.1, by have := j.2; omega⟩
    have hacc' : N.Acc (N.run bs' x (i.1 + r)) := by rw [h2, ← hr]; exact hacc
    exact ih (i.1 + r) (by omega) bs' hacc'
  rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · exact key i0 j0 h he
  · exact key j0 i0 h he.symm

/-- Constants of the configuration count. -/
noncomputable def cA : ℕ := (Nat.card N.tm.Λ + 1) * Nat.card N.tm.σ
noncomputable def cB : ℕ := (Nat.card (symSet N.tm) + 2) ^ Nat.card N.tm.K

theorem card_code_le (S : ℕ) : Nat.card (N.Code S) ≤ 2 ^ (N.cA + N.cB * S) := by
  have e : Nat.card (N.Code S) = N.cA * N.cB ^ S := by
    simp only [Code, Nat.card_prod, natCard_option, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin S), Fintype.card_fin, cA, cB]
    rw [← pow_mul, ← pow_mul, mul_comm S, mul_assoc]
  rw [e, pow_add]
  apply Nat.mul_le_mul
  · exact (Nat.lt_two_pow_self).le
  · rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _

/-- Acceptance at a fixed late time. -/
theorem accepts_iff_at {Sf : ℕ → ℕ} (hsp : N.SpaceBounded Sf) (x : List Bool) (T : ℕ)
    (hT : 2 ^ (N.cA + N.cB * Sf x.length) ≤ T) :
    N.Accepts x ↔ ∃ bs : ℕ → Bool, N.Acc (N.run bs x T) := by
  constructor
  · rintro ⟨bs, t, hacc⟩
    obtain ⟨bs', t', ht', hacc'⟩ := N.short hsp x t bs hacc
    refine ⟨bs', ?_⟩
    have hle : t' ≤ T := by have := N.card_code_le (Sf x.length); omega
    have e := N.runC_halted bs' (N.init x) t' hacc'.1 (T - t')
    rw [show t' + (T - t') = T by omega] at e
    unfold run; rw [e]; exact hacc'
  · rintro ⟨bs, hacc⟩; exact ⟨bs, T, hacc⟩

end NTM

/-! ### Row blocks at any row (nondeterministic) -/

section TabTN

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [DecidableEq (V2 Γ Λ σ)]
variable (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (d P : ℕ) (Ks : List K) (S : ℕ) (U : List (V2 Γ Λ σ))

/-- Rows `t`, `t+1` and the nondeterministic transition between them. -/
noncomputable def tabBtN (t : ℕ) : CNF :=
  AL U (sv2 Ks S t) (2 * W2 Ks S) ++
    HC U (csRow d Ks S t ++ csRow d Ks S (t + 1) ++ csTransN m alt d P Ks S t)

theorem tabBtN_shift (t : ℕ) (a : ℕ → Bool) :
    evalCNF (tabBtN m alt d P Ks S U t) a = true ↔
      evalCNF (tabB0N m alt d P Ks S U) (fun v => a (v + t * W2 Ks S * U.length)) = true := by
  unfold tabBtN tabB0N
  rw [evalCNF_app, evalCNF_app, Bool.and_eq_true, Bool.and_eq_true]
  have r0 := csRow_shift (Γ := Γ) (Λ := Λ) (σ := σ) d Ks S 0 t
  have r1 := csRow_shift (Γ := Γ) (Λ := Λ) (σ := σ) d Ks S 1 t
  have r2 := csTransN_shift m alt d P Ks S 0 t
  rw [Nat.zero_add] at r0 r2
  rw [Nat.add_comm 1 t] at r1
  rw [r0, r1, r2, ← List.map_append, ← List.map_append, HC_shift]
  apply and_congr_left'
  rw [AL_iff, AL_iff]
  apply forall_congr'; intro i; apply imp_congr_right; intro _
  rw [show sv2 Ks S t + i = (sv2 Ks S 0 + i) + t * W2 Ks S by unfold sv2; ring, alo_shift]

theorem tabBtN_iff (hS2 : 2 * d + P + 1 ≤ S) (t : ℕ) (a : ℕ → Bool) :
    evalCNF (tabBtN m alt d P Ks S U t) a = true ↔
      tabRN m alt d P Ks S U (rdF a (2 * U.length + t * (W2 Ks S * U.length)) (W2 Ks S * U.length))
        (rdF a (2 * U.length + t * (W2 Ks S * U.length) + W2 Ks S * U.length)
          (W2 Ks S * U.length)) := by
  rw [tabBtN_shift, tabRN, List.append_assoc, rdF_two]
  rw [evalCNF_congr _ _ (asg (List.replicate (2 * U.length) false ++
    rdF a (2 * U.length + t * (W2 Ks S * U.length)) (2 * (W2 Ks S * U.length))))]
  intro cl hcl l hl
  obtain ⟨h1, h2⟩ := tabB0N_vars m alt d P Ks S U hS2 cl hcl l hl
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

end TabTN

/-! ### The reduction for a space-bounded NTM -/

section NRed

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (N : NTM) (p : Polynomial ℕ)

/-- Row depth of the tableau. -/
noncomputable def nS (x : List Bool) : ℕ :=
  p.eval x.length + 2 * clD N.tm + pushTotal N.tm + x.length + 3

/-- Number of Savitch levels: accepting runs can be taken to have `2 ^ nk x` steps. -/
noncomputable def nk (x : List Bool) : ℕ := N.cA + N.cB * p.eval x.length

noncomputable def nU : List (V2 N.tm.Γ N.tm.Λ N.tm.σ) := tab2Values (clD N.tm) (clL N.tm)

theorem nU_ne : nU N ≠ [] := tab2Values_ne _ _

theorem N_d (lab : N.tm.Λ) : sdepth (N.tm.m lab) ≤ clD N.tm :=
  Finset.le_sup (f := fun l => sdepth (N.tm.m l)) (Finset.mem_univ lab)

theorem N_Ks (k : N.tm.K) : k ∈ clKs N.tm := by simp [clKs]

theorem n_S1 (x : List Bool) : x.length + 2 + 0 ≤ nS N p x := by unfold nS; omega
theorem n_S2 (x : List Bool) : 2 * clD N.tm + pushTotal N.tm + 1 ≤ nS N p x := by
  unfold nS; omega

/-- The nondeterministic tableau constraints for input `x`. -/
noncomputable def nCS (x : List Bool) :=
  tabNCS N.tm.m N.alt (clD N.tm) (pushTotal N.tm) (clKs N.tm) (nS N p x) (2 ^ nk N p x)
    N.tm.k₀ N.tm.k₁ N.tm.main N.tm.initialState N.sb N.sep 0 N.acc x

theorem run_symsN (bs : ℕ → Bool) (x : List Bool) :
    ∀ t, SymsIn (clL N.tm) (N.run bs x t).stk := by
  intro t
  induction t with
  | zero =>
    intro k g hg
    by_cases hk : k = N.tm.k₀
    · subst hk; simp [clL]
    · simp [NTM.run, NTM.runC, NTM.init, initCfg, hk] at hg
  | succ t ih =>
    show SymsIn (clL N.tm) (stepStay N.tm.m (N.run bs x t)).stk
    refine stepStay_syms N.tm.m _ (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) _
      (fun lab y hy => ?_) _ ih
    simp only [clL, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨lab, by simp, hy⟩

theorem nCS_iff (hsp : N.SpaceBounded (fun n => p.eval n)) (x : List Bool) :
    CSPSat (nU N) (nCS N p x) ↔ N.Accepts x := by
  have hrun : ∀ (bs : ℕ → Bool) t, runG N.tm.m N.alt bs (initCfg N.tm.main N.tm.initialState
      N.tm.k₀ (x.map N.sb ++ N.sep :: ([] : List Bool).map N.sb)) t = N.run bs x t :=
    fun bs t => (N.run_eq bs x t).symm
  have hlen : ∀ w : List Bool, w.length ≤ 0 → ∀ (bs : ℕ → Bool), ∀ t ≤ 2 ^ nk N p x, ∀ k,
      ((runG N.tm.m N.alt bs (initCfg N.tm.main N.tm.initialState N.tm.k₀
        (x.map N.sb ++ N.sep :: w.map N.sb)) t).stk k).length ≤ nS N p x - (clD N.tm + 1) := by
    intro w hw bs t _ k
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw), hrun]
    have := hsp x bs t k
    unfold nS; simp only at this; omega
  have hT : 2 ^ (N.cA + N.cB * (fun n => p.eval n) x.length) ≤ 2 ^ nk N p x := le_of_eq rfl
  constructor
  · intro hsat
    obtain ⟨w, hw, bs, hl, hc⟩ := tabN_sound (hd := N_d N) (hP := pushes_le_total N.tm)
      (hKs := N_Ks N) _ (tab2Values_win _ _) (n_S1 N p x) (n_S2 N p x) hlen hsat
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw), hrun] at hl hc
    exact (N.accepts_iff_at hsp x _ hT).2 ⟨bs, hl, hc⟩
  · intro hacc
    obtain ⟨bs, hl, hc⟩ := (N.accepts_iff_at hsp x _ hT).1 hacc
    have hsb' : ∀ b, (⟨N.tm.k₀, N.sb b⟩ : Sig N.tm.Γ) ∈ clL N.tm := fun b => by simp [clL]
    exact tabN_complete (hd := N_d N) (hP := pushes_le_total N.tm) (hKs := N_Ks N)
      (n_S1 N p x) (n_S2 N p x) [] le_rfl bs (hlen [] le_rfl bs) (by rw [hrun]; exact hl)
      (by rw [hrun]; exact hc) _
      (assign2_mem _ _ _ _ _ _ hsb' _ (fun t => by rw [hrun]; exact run_symsN N bs x t))

/-! ### The Savitch QBF -/

/-- Hot bits per tableau row. -/
noncomputable def nn (x : List Bool) : ℕ := W2 (clKs N.tm) (nS N p x) * (nU N).length

noncomputable def nTop (x : List Bool) : CNF :=
  tabTopN (clKs N.tm) (nS N p x) N.tm.k₀ N.tm.k₁ N.tm.main N.tm.initialState N.sb N.sep 0 N.acc x
    (nU N)

noncomputable def nBot (x : List Bool) : CNF :=
  tabBtN N.tm.m N.alt (clD N.tm) (pushTotal N.tm) (clKs N.tm) (nS N p x) (nU N) (4 * nk N p x)

/-- **The reduction**: the Savitch QBF for `x` (nondeterministic version). -/
noncomputable def redQBFN (x : List Bool) : QBF :=
  ⟨List.replicate (2 * (nU N).length + 2 * nn N p x) false ++ lvlPre (nn N p x) (nk N p x),
    nTop N p x ++ (lvlCNF (nn N p x) (2 * (nU N).length) (nk N p x) ++ nBot N p x)⟩

noncomputable def redQN (x : List Bool) : List Bool := encodeQBF (redQBFN N p x)

theorem redQN_correct (hsp : N.SpaceBounded (fun n => p.eval n)) (x : List Bool) :
    N.Accepts x ↔ TQBF (redQN N p x) := by
  have hUl : 0 < (nU N).length := List.length_pos_iff.2 (nU_ne N)
  have hW : 0 < W2 (clKs N.tm) (nS N p x) := by unfold W2; omega
  have hn1 : 1 ≤ nn N p x := Nat.mul_pos hW hUl
  rw [redQN, TQBF_encode, ← nCS_iff N p hsp x]
  simp only [QBF.val, redQBFN]
  have hTv : ∀ cl ∈ nTop N p x, ∀ l ∈ cl, l.var < 2 * (nU N).length + 2 * nn N p x := by
    unfold nTop nn
    exact tabTopN_vars _ _ _ _ _ _ _ _ _ _ _ _ (N_Ks N _) (N_Ks N _) (n_S1 N p x)
  rw [sav_correct (tabRN N.tm.m N.alt (clD N.tm) (pushTotal N.tm) (clKs N.tm) (nS N p x) (nU N))
    (nn N p x) (2 * (nU N).length) (nk N p x) hn1 (nTop N p x) (nBot N p x) hTv
    (fun a => by
      rw [nBot, tabBtN_iff _ _ _ _ _ _ _ (n_S2 N p x)]
      unfold nn
      rw [show 4 * nk N p x * (W2 (clKs N.tm) (nS N p x) * (nU N).length) =
        4 * (W2 (clKs N.tm) (nS N p x) * (nU N).length) * nk N p x by ring])]
  constructor
  · intro hc
    unfold nTop nn
    obtain ⟨g, hg, htop, hch⟩ := chain_of_tabN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nU_ne N)
      (N_Ks N _) (N_Ks N _) (n_S1 N p x) (n_S2 N p x) _ (Nat.one_le_two_pow) hc
    refine ⟨g, hg, htop, ?_⟩
    exact (sav_chain _ _ _ _ _ (rdF_length _ _ _) (rdF_length _ _ _)).2 hch
  · rintro ⟨g, -, htop, hsav⟩
    unfold nTop nn at *
    exact tab_of_chainN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (nU_ne N) (N_Ks N _) (N_Ks N _)
      (n_S1 N p x) (n_S2 N p x) _ (Nat.one_le_two_pow) g htop
      ((sav_chain _ _ _ _ _ (rdF_length _ _ _) (rdF_length _ _ _)).1 hsav)

end NRed

end PvnpReal
