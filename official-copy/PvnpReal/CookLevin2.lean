/-
  PvnpReal.CookLevin2 — the second tableau instantiated for an NP verifier, its correctness, the
  polynomial-time computability of its encoding, and the Cook–Levin theorem.
-/
import PvnpReal.Tab2Print
import PvnpReal.CookLevinTab
import PvnpReal.SatMachine

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

/-! ### All scope indices are below `N = 2 + (T+1)·W2` -/

section Scope

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (S T : ℕ) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool)

theorem sv2_lt {t : ℕ} (ht : t ≤ T) : sv2 Ks S t < 2 + (T + 1) * W2 Ks S := by
  have hW : 0 < W2 Ks S := by unfold W2; omega
  have : t * W2 Ks S < (T + 1) * W2 Ks S := Nat.mul_lt_mul_of_pos_right (by omega) hW
  unfold sv2; omega

theorem cv2_lt {t : ℕ} (ht : t ≤ T) {k : K} (hk : k ∈ Ks) {p : ℕ} (hp : p < S) :
    cv2 Ks S t k p < 2 + (T + 1) * W2 Ks S := by
  have hi := List.idxOf_lt_length_of_mem hk
  have hr : 1 + Ks.idxOf k * S + p < W2 Ks S := by
    unfold W2
    have : (Ks.idxOf k + 1) * S ≤ Ks.length * S := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul] at this; omega
  have : (t + 1) * W2 Ks S ≤ (T + 1) * W2 Ks S := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at this
  unfold cv2; omega

theorem tab2_scope_lt (hKs : ∀ k, k ∈ Ks) (hS1 : xs.length + 2 + Q ≤ S)
    (hS2 : 2 * d + P + 1 ≤ S) :
    ∀ c ∈ tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs, ∀ v ∈ c.scope,
      v < 2 + (T + 1) * W2 Ks S := by
  have hN : 2 ≤ 2 + (T + 1) * W2 Ks S := by omega
  intro c hc
  simp only [tab2CS, csZ, csInit, csRow, csTrans, csFinal, List.mem_append, List.mem_cons,
    List.mem_singleton, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_filter,
    List.not_mem_nil, or_false] at hc
  rcases hc with (((((rfl | rfl) | ((((((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) |
    ⟨j, hj, rfl⟩) | ⟨k, ⟨-, hk⟩, p, hp, rfl⟩))) | ⟨t, ht, k, -, (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)⟩) |
    ⟨t, ht, rfl | ⟨k, -, (⟨p, hp, rfl⟩ | ⟨j, hj, rfl⟩)⟩⟩) | rfl)
  all_goals intro v hv
  all_goals simp only [List.mem_cons, List.mem_singleton, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hv
  · omega
  · omega
  · subst hv; exact sv2_lt Ks S T (Nat.zero_le _)
  · rcases hv with rfl | rfl
    · exact cv2_lt Ks S T (Nat.zero_le _) (hKs _) (by omega)
    · have : NthTM.bit xs i ≤ 1 := by unfold NthTM.bit; split <;> omega
      omega
  · subst hv; exact cv2_lt Ks S T (Nat.zero_le _) (hKs _) (by omega)
  · rcases hv with rfl | rfl <;> exact cv2_lt Ks S T (Nat.zero_le _) (hKs _) (by omega)
  · subst hv; exact cv2_lt Ks S T (Nat.zero_le _) (hKs _) (by omega)
  · subst hv; exact cv2_lt Ks S T (Nat.zero_le _) (hKs _) hp
  · rcases hv with rfl | rfl
    · exact sv2_lt Ks S T (by omega)
    · exact cv2_lt Ks S T (by omega) (hKs _) (by omega)
  · subst hv; exact cv2_lt Ks S T (by omega) (hKs _) (by omega)
  · rcases hv with rfl | rfl
    · exact sv2_lt Ks S T (by omega)
    · exact sv2_lt Ks S T (by omega)
  · rcases hv with rfl | rfl | ⟨i, hi, rfl⟩
    · exact sv2_lt Ks S T (by omega)
    · exact cv2_lt Ks S T (by omega) (hKs _) (by omega)
    · exact cv2_lt Ks S T (by omega) (hKs _) (by omega)
  · rcases hv with rfl | rfl | ⟨i, hi, rfl⟩
    · exact sv2_lt Ks S T (by omega)
    · exact cv2_lt Ks S T (by omega) (hKs _) (by omega)
    · exact cv2_lt Ks S T (by omega) (hKs _) (by omega)
  · subst hv; exact cv2_lt Ks S T le_rfl (hKs _) (by omega)

end Scope

/-! ### A finite value list -/

section Values

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable [Fintype K] [Fintype Λ] [Fintype σ]

noncomputable def tab2Values (d : ℕ) (L : List (Sig Γ)) : List (V2 Γ Λ σ) :=
  (((Finset.univ : Finset (Option Λ)) ×ˢ (Finset.univ : Finset σ) ×ˢ
      Fintype.piFinset (fun _ : K => (upTo L d).toFinset)).image
      (fun p => (Sum.inl ⟨p.1, p.2.1, p.2.2⟩ : V2 Γ Λ σ)) ∪
    (L.map (fun g => (Sum.inr (some g) : V2 Γ Λ σ))).toFinset ∪ {Sum.inr none}).toList

theorem tab2Values_ne (d : ℕ) (L : List (Sig Γ)) : tab2Values (Λ := Λ) (σ := σ) d L ≠ [] := by
  intro h
  have : (Sum.inr none : V2 Γ Λ σ) ∈ tab2Values d L := by simp [tab2Values]
  rw [h] at this; simp at this

theorem tab2Values_win (d : ℕ) (L : List (Sig Γ)) :
    ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ tab2Values d L → ∀ k, (R.win k).length ≤ d := by
  intro R hR k
  simp only [tab2Values, Finset.mem_toList, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset, List.mem_map, Finset.mem_singleton, reduceCtorEq, or_false,
    Finset.mem_product, Fintype.mem_piFinset, mem_upTo, exists_false, and_false] at hR
  obtain ⟨⟨l, v, w⟩, ⟨-, -, hw⟩, he⟩ := hR
  cases he
  exact (hw k).1

theorem tab2Values_ctl (d : ℕ) (L : List (Sig Γ)) (c : Cfg Γ Λ σ) (hL : SymsIn L c.stk) :
    (Sum.inl (ctlOf d c) : V2 Γ Λ σ) ∈ tab2Values d L := by
  simp only [tab2Values, Finset.mem_toList, Finset.mem_union, Finset.mem_image]
  refine Or.inl (Or.inl ⟨(c.l, c.var, fun k => toSig k ((c.stk k).take d)), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    List.mem_toFinset, mem_upTo]
  refine fun k => ⟨by simp [toSig], fun x hx => ?_⟩
  simp only [toSig, List.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact hL k g (List.mem_of_mem_take hg)

theorem tab2Values_cell (d : ℕ) (L : List (Sig Γ)) (c : Cfg Γ Λ σ) (hL : SymsIn L c.stk)
    (k : K) (p : ℕ) : (Sum.inr (cellOf c k p) : V2 Γ Λ σ) ∈ tab2Values d L := by
  unfold cellOf
  rcases h : (c.stk k)[p]? with _ | g
  · simp [tab2Values]
  · have := hL k g (List.mem_of_getElem? h)
    simp only [tab2Values, Finset.mem_toList, Finset.mem_union, List.mem_toFinset, List.mem_map,
      Option.map_some]
    exact Or.inl (Or.inr ⟨_, this, rfl⟩)

theorem assign2_mem (d : ℕ) (L : List (Sig Γ)) (Ks : List K) (S : ℕ) (k₀ : K) (sb : Bool → Γ k₀)
    (hsb : ∀ b, (⟨k₀, sb b⟩ : Sig Γ) ∈ L) (run : ℕ → Cfg Γ Λ σ) (hrun : ∀ t, SymsIn L (run t).stk)
    (v : ℕ) : assign2 d Ks S k₀ sb run v ∈ tab2Values d L := by
  have hZ : ∀ b, (Sum.inr (some ⟨k₀, sb b⟩) : V2 Γ Λ σ) ∈ tab2Values d L := fun b => by
    simp only [tab2Values, Finset.mem_toList, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact Or.inl (Or.inr ⟨_, hsb b, rfl⟩)
  unfold assign2
  split_ifs
  · exact hZ false
  · exact hZ true
  · exact tab2Values_ctl d L _ (hrun _)
  · split
    · exact tab2Values_cell d L _ (hrun _) _ _
    · simp [tab2Values]

end Values

end PvnpReal

/-! ### The second tableau for an NP verifier -/

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

section Verifier2

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {V : List Bool × List Bool → Bool} (q : Polynomial ℕ)
  (h : TM2ComputableInPolyTime pairEnc encodeBool V)

noncomputable def c2sb (b : Bool) : h.tm.Γ h.tm.k₀ := h.inputAlphabet.invFun (some b)
noncomputable def c2sep : h.tm.Γ h.tm.k₀ := h.inputAlphabet.invFun none
noncomputable def c2acc : h.tm.Γ h.tm.k₁ := h.outputAlphabet.invFun true

/-- Rows are `S` cells deep: enough for every stack plus the bottom margin. -/
noncomputable def c2S (x : List Bool) : ℕ :=
  clN q x + pushTotal h.tm * clT q h x + 2 * clD h.tm + pushTotal h.tm + 2

noncomputable def c2N (x : List Bool) : ℕ := 2 + (clT q h x + 1) * W2 (clKs h.tm) (c2S q h x)

/-- **The second Cook–Levin formula for input `x`.** -/
noncomputable def cl2CNF (x : List Bool) : CNF :=
  cspCNF (tab2Values (clD h.tm) (clL h.tm)) (c2N q h x)
    (tab2CS h.tm.m (clD h.tm) (pushTotal h.tm) (clKs h.tm) (c2S q h x) (clT q h x) h.tm.k₀ h.tm.k₁
      h.tm.main h.tm.initialState (c2sb h) (c2sep h) (q.eval x.length) (c2acc h) x)

/-- The Cook–Levin map on bit strings, second version. -/
noncomputable def cl2Map (x : List Bool) : List Bool := encodeCNF (cl2CNF q h x)

theorem c2_init (x w : List Bool) :
    x.map (c2sb h) ++ c2sep h :: w.map (c2sb h) =
      clPre h x ++ w.map (h.inputAlphabet.invFun ∘ some) := by
  simp [clPre, c2sep]; rfl

theorem c2_acc_cell (b : Bool) :
    cellOf (haltList h.tm ((encodeBool b).map h.outputAlphabet.invFun)) h.tm.k₁ 0 =
      some ⟨h.tm.k₁, h.outputAlphabet.invFun b⟩ := by
  simp [cellOf, haltList_stk, encodeBool]

theorem c2_len (x w : List Bool) (hw : w.length ≤ q.eval x.length) :
    ∀ t ≤ clT q h x, ∀ k, (((stepStay h.tm.m)^[t] (initCfg h.tm.main h.tm.initialState h.tm.k₀
      (x.map (c2sb h) ++ c2sep h :: w.map (c2sb h)))).stk k).length ≤
        c2S q h x - (clD h.tm + 1) := by
  intro t ht k
  rw [c2_init]
  have := iterate_stepStay_len h.tm.m _ (clN q x) (pushTotal h.tm)
    (pushes_le_total h.tm)
    (init_len q h x (w.map (h.inputAlphabet.invFun ∘ some)) (by simpa using hw)) t k
  have := Nat.mul_le_mul_left (pushTotal h.tm) ht
  unfold c2S; omega

theorem c2_hS1 (x : List Bool) : x.length + 2 + q.eval x.length ≤ c2S q h x := by
  unfold c2S clN; omega

theorem c2_hS2 (x : List Bool) : 2 * clD h.tm + pushTotal h.tm + 1 ≤ c2S q h x := by
  unfold c2S; omega

/-- **Correctness of the second Cook–Levin formula.** -/
theorem cl2CNF_correct (x : List Bool) :
    (∃ w : List Bool, w.length ≤ q.eval x.length ∧ V (x, w) = true) ↔ SAT (cl2CNF q h x) := by
  unfold cl2CNF c2N
  rw [cspCNF_correct _ (tab2Values_ne _ _) _ _
    (tab2_scope_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (clKs_spec h) (c2_hS1 q h x) (c2_hS2 q h x))]
  have hsb : ∀ b, (⟨h.tm.k₀, c2sb h b⟩ : Sig h.tm.Γ) ∈ clL h.tm := fun b => by simp [clL]
  constructor
  · rintro ⟨w, hw, hV⟩
    refine tab2_complete (hd := clD_spec h) (hP := pushes_le_total h.tm) (hKs := clKs_spec h)
      (c2_hS1 q h x) (c2_hS2 q h x) w hw (c2_len q h x w hw) ?_ _
      (assign2_mem _ _ _ _ _ _ hsb _ (fun t => ?_))
    · rw [c2_init, verifier_stay q h x w hw, hV, c2_acc_cell]; rfl
    · rw [c2_init]
      exact run_syms h _ (init_syms h x _) t
  · intro hsat
    obtain ⟨w, hw, hacc⟩ := tab2_sound (hd := clD_spec h) (hP := pushes_le_total h.tm)
      (hKs := clKs_spec h) _ (tab2Values_win _ _) (c2_hS1 q h x) (c2_hS2 q h x)
      (fun w hw => c2_len q h x w hw) hsat
    refine ⟨w, hw, ?_⟩
    rw [c2_init, verifier_stay q h x w hw, c2_acc_cell] at hacc
    have e := eq_of_heq (Sigma.mk.inj_iff.1 (Option.some.inj hacc)).2
    exact h.outputAlphabet.symm.injective e

/-! ### The second Cook–Levin map is polynomial-time computable -/

theorem PU.clN : PU (fun x => clN q x) :=
  ((PU.lenX.add (PU.const 1)).add (PU.poly q)).congr (fun _ => rfl)

theorem PU.clT : PU (fun x => clT q h x) := (PU.polyOf h.time (PU.clN q)).congr (fun _ => rfl)

theorem PU.c2S : PU (fun x => c2S q h x) :=
  ((((PU.clN q).add ((PU.const _).mul (PU.clT q h))).add (PU.const _)).add (PU.const _)).add
    (PU.const _) |>.congr (fun _ => rfl)

/-- **Piece 5, discharged for the new formula**: `cl2Map` is computed by a polynomial-time
`FinTM2` (built from the proven combinators). -/
theorem cl2Map_PS : PS (cl2Map q h) := by
  have hR1 : PU (fun x => c2S q h x - (x.length + 1 + q.eval x.length)) :=
    ((((PU.const (pushTotal h.tm)).mul (PU.clT q h)).add (PU.const (2 * clD h.tm))).add
      (PU.const (pushTotal h.tm + 2))).congr (fun x => by unfold c2S clN; omega)
  have hR2 : PU (fun x => c2S q h x - (clD h.tm + pushTotal h.tm) - (clD h.tm + 1)) :=
    (((PU.clN q).add ((PU.const (pushTotal h.tm)).mul (PU.clT q h))).add (PU.const 1)).congr
      (fun x => by unfold c2S; omega)
  have hR3 : PU (fun x => c2S q h x - (clD h.tm + 1)) :=
    (((PU.clN q).add ((PU.const (pushTotal h.tm)).mul (PU.clT q h))).add
      (PU.const (clD h.tm + pushTotal h.tm + 1))).congr (fun x => by unfold c2S; omega)
  have hN : PU (fun x => c2N q h x) :=
    ((PU.const 2).add (((PU.clT q h).add (PU.const 1)).mul
      ((PU.const 1).add ((PU.const _).mul (PU.c2S q h))))).congr (fun _ => rfl)
  exact (tab2_encode_PS h.tm.m (clD h.tm) (pushTotal h.tm) (clKs h.tm) h.tm.k₀ h.tm.k₁ h.tm.main
    h.tm.initialState (c2sb h) (c2sep h) (c2acc h) (tab2Values (clD h.tm) (clL h.tm))
    (PU.c2S q h) (PU.clT q h) (PU.poly q) hN hR1 hR2 hR3).congr (fun _ => rfl)

theorem cl2Map_correct (x : List Bool) :
    (∃ w : List Bool, w.length ≤ q.eval x.length ∧ V (x, w) = true) ↔ SATLang (cl2Map q h x) := by
  rw [cl2CNF_correct q h x, cl2Map, SATLang_encode_iff]

end Verifier2

/-- **The Cook–Levin theorem** (for the definitions in `Complexity.lean`): SAT is NP-complete.
`SAT_in_NP` gives membership; every NP language reduces to SAT via `cl2Map`, which is proven
correct (`cl2Map_correct`) and computed by a polynomial-time `FinTM2` (`cl2Map_PS`). -/
theorem cookLevin : CookLevinStatement := by
  refine ⟨SAT_in_NP, fun L hL => ?_⟩
  obtain ⟨V, q, ⟨h⟩, hV⟩ := hL
  exact ⟨cl2Map q h, cl2Map_PS q h, fun x => (hV x).trans (cl2Map_correct q h x)⟩

theorem SAT_NPHard : NPHard SATLang := cookLevin_iff_NPHard.1 cookLevin

end PvnpReal
