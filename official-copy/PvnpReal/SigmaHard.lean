/-
  PvnpReal.SigmaHard — the Cook–Levin tableau with its witness prefix exposed as free variables.

  For a polynomial-time verifier `V` (on pairs) and an input `x`, the CNF `coreCNF x n` is the second
  Cook–Levin formula `cl2CNF x` (variables `< cM x`) preceded by *link clauses* tying the variables
  `cM x + i` (`i < n`) to the witness cells `i` of the initial row:
  `u_i → t_i`, `t_i → u_i`, `¬t_i ∨ ¬f_i`, and `¬e` for every non-bit value `e` of the cell, where
  `t_i`/`f_i` are the one-hot variables "cell `i` holds the bit `true`/`false`".

  `core_iff`: for `|p| = n ≤ q(|x|)`,
    `(∃ w, |p ++ w| ≤ q(|x|) ∧ V(x, p ++ w)) ↔ ∃ z, |z| = cM x ∧ coreCNF x n (z ++ p)`.
-/
import PvnpReal.SigmaTab
import PvnpReal.CookLevin2
import PvnpReal.QbfTab

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

theorem stk_get {α : Type*} (f : Bool → α) (sep : α) (x W : List Bool) (i : ℕ) :
    (x.map f ++ sep :: W.map f)[x.length + 1 + i]? = (W[i]?).map f := by
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp [show x.length + 1 + i - x.length = i + 1 by omega]

theorem asg_append_lo (z p : List Bool) {v : ℕ} (hv : v < z.length) :
    asg (z ++ p) v = asg z v := by
  simp [asg, List.getD_eq_getElem?_getD, List.getElem?_append_left hv]

theorem asg_append_hi (z p : List Bool) (i : ℕ) : asg (z ++ p) (z.length + i) = asg p i := by
  simp [asg, List.getD_eq_getElem?_getD, List.getElem?_append_right]

section Core

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {V : List Bool × List Bool → Bool} (q : Polynomial ℕ)
  (h : TM2ComputableInPolyTime pairEnc encodeBool V)

noncomputable def cU : List (V2 h.tm.Γ h.tm.Λ h.tm.σ) := tab2Values (clD h.tm) (clL h.tm)

/-- Number of tableau variables (one-hot), i.e. `cl2CNF x` uses variables `< cM x`. -/
noncomputable def cM (x : List Bool) : ℕ := c2N q h x * (cU h).length

noncomputable def cCell (x : List Bool) (i : ℕ) : ℕ :=
  cv2 (clKs h.tm) (c2S q h x) 0 h.tm.k₀ (x.length + 1 + i)

noncomputable def cSb (b : Bool) : V2 h.tm.Γ h.tm.Λ h.tm.σ := Sum.inr (some ⟨h.tm.k₀, c2sb h b⟩)

noncomputable def cBad : List (V2 h.tm.Γ h.tm.Λ h.tm.σ) :=
  (cU h).filter (fun e => decide (e ≠ cSb h true ∧ e ≠ cSb h false))

noncomputable def linkI (x : List Bool) (i : ℕ) : CNF :=
  [[⟨cM q h x + i, true⟩, ⟨hotVar (cU h) (cCell q h x i) (cSb h true), false⟩],
   [⟨cM q h x + i, false⟩, ⟨hotVar (cU h) (cCell q h x i) (cSb h true), true⟩],
   [⟨hotVar (cU h) (cCell q h x i) (cSb h true), true⟩,
    ⟨hotVar (cU h) (cCell q h x i) (cSb h false), true⟩]] ++
  (cBad h).map (fun e => [⟨hotVar (cU h) (cCell q h x i) e, true⟩])

noncomputable def linkCNF (x : List Bool) (n : ℕ) : CNF := (List.range n).flatMap (linkI q h x)

noncomputable def coreCNF (x : List Bool) (n : ℕ) : CNF := linkCNF q h x n ++ cl2CNF q h x

theorem cU_ne : cU h ≠ [] := tab2Values_ne _ _

theorem cSb_mem (b : Bool) : cSb h b ∈ cU h := by
  have hsb : (⟨h.tm.k₀, c2sb h b⟩ : Sig h.tm.Γ) ∈ clL h.tm := by simp [clL]
  simp only [cU, cSb, tab2Values, Finset.mem_toList, Finset.mem_union, List.mem_toFinset, List.mem_map]
  exact Or.inl (Or.inr ⟨_, hsb, rfl⟩)

theorem c2sb_inj : Function.Injective (c2sb h) := by
  intro a b e
  have := congrArg h.inputAlphabet e
  simpa [c2sb] using this

theorem cSb_inj {a b : Bool} (e : cSb h a = cSb h b) : a = b := by
  simp only [cSb, Sum.inr.injEq, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
  exact c2sb_inj h e

theorem cCell_lt (x : List Bool) {i : ℕ} (hi : i < q.eval x.length) : cCell q h x i < c2N q h x := by
  have hS := c2_hS1 q h x
  have hb := (cv2_bounds (Ks := clKs h.tm) (S := c2S q h x) 0 (clKs_spec h h.tm.k₀)
    (show x.length + 1 + i < c2S q h x by omega)).2
  simp only [Nat.zero_add] at hb
  have hW : sv2 (clKs h.tm) (c2S q h x) 1 ≤ c2N q h x := by
    unfold sv2 c2N
    have := Nat.mul_le_mul_right (W2 (clKs h.tm) (c2S q h x)) (show 1 ≤ clT q h x + 1 by omega)
    omega
  unfold cCell; omega

theorem hot_lt (x : List Bool) {v : ℕ} (hv : v < c2N q h x) {e : V2 h.tm.Γ h.tm.Λ h.tm.σ}
    (he : e ∈ cU h) : hotVar (cU h) v e < cM q h x := by
  have := (hotVar_bnd (cU h) v he).2
  have := Nat.mul_le_mul_right (cU h).length (show v + 1 ≤ c2N q h x by omega)
  unfold cM; rw [Nat.add_mul] at this; omega

theorem cl2_vars (x : List Bool) : ∀ cl ∈ cl2CNF q h x, ∀ l ∈ cl, ∃ v < c2N q h x, ∃ e ∈ cU h,
    l.var = hotVar (cU h) v e := by
  intro cl hcl l hl
  simp only [cl2CNF, cspCNF, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap] at hcl
  rcases hcl with ⟨v, hv, rfl⟩ | ⟨c, hc, hcl⟩
  · obtain ⟨e, he, hl⟩ := alo_vars _ v l hl
    exact ⟨v, hv, e, he, hl⟩
  · obtain ⟨v, hv, e, he, hl⟩ := conCl_vars _ c cl hcl l hl
    exact ⟨v, tab2_scope_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (clKs_spec h) (c2_hS1 q h x)
      (c2_hS2 q h x) c hc v hv, e, he, hl⟩

theorem hotB_hot (U : List (V2 h.tm.Γ h.tm.Λ h.tm.σ)) (a : ℕ → V2 h.tm.Γ h.tm.Λ h.tm.σ) (v : ℕ)
    {e : V2 h.tm.Γ h.tm.Λ h.tm.σ} (he : e ∈ U) (ha : a v ∈ U) :
    hotB U a (hotVar U v e) = decide (e = a v) := by
  simp only [hotB, hotVar_div U v he, hotVar_mod U v he]
  exact decide_eq_decide.2 (@List.idxOf_inj _ instBEqOfDecidableEq inferInstance _ _ _ he)

/-- **Tableau with exposed witness prefix.** -/
theorem core_iff (x p : List Bool) (hp : p.length ≤ q.eval x.length) :
    (∃ w : List Bool, (p ++ w).length ≤ q.eval x.length ∧ V (x, p ++ w) = true) ↔
      ∃ z : List Bool, z.length = cM q h x ∧
        evalCNF (coreCNF q h x p.length) (asg (z ++ p)) = true := by
  have hUne := cU_ne h
  have hS1 := c2_hS1 q h x
  have hS2 := c2_hS2 q h x
  constructor
  · -- completeness
    rintro ⟨w, hwQ, hV⟩
    set W := p ++ w with hW
    set run : ℕ → Cfg h.tm.Γ h.tm.Λ h.tm.σ := fun t => (stepStay h.tm.m)^[t]
      (initCfg h.tm.main h.tm.initialState h.tm.k₀ (x.map (c2sb h) ++ c2sep h :: W.map (c2sb h)))
      with hrun
    set a := assign2 (clD h.tm) (clKs h.tm) (c2S q h x) h.tm.k₀ (c2sb h) run with ha
    have hacc : cellOf ((stepStay h.tm.m)^[clT q h x] (initCfg h.tm.main h.tm.initialState h.tm.k₀
        (x.map (c2sb h) ++ c2sep h :: W.map (c2sb h)))) h.tm.k₁ 0 = some ⟨h.tm.k₁, c2acc h⟩ := by
      rw [c2_init, verifier_stay q h x W hwQ, hV, c2_acc_cell]; rfl
    have hc := tab2_complete_at (hd := clD_spec h) (hP := pushes_le_total h.tm)
      (hKs := clKs_spec h) hS1 hS2 W hwQ (c2_len q h x W hwQ) hacc
    have hsb : ∀ b, (⟨h.tm.k₀, c2sb h b⟩ : Sig h.tm.Γ) ∈ clL h.tm := fun b => by simp [clL]
    have hU : ∀ v, a v ∈ cU h := assign2_mem _ _ _ _ _ _ hsb _ (fun t => by
      simp only [hrun]; rw [c2_init]; exact run_syms h _ (init_syms h x _) t)
    refine ⟨(List.range (cM q h x)).map (hotB (cU h) a), by simp, ?_⟩
    have hlo : ∀ v < cM q h x, asg ((List.range (cM q h x)).map (hotB (cU h) a) ++ p) v =
        hotB (cU h) a v := by
      intro v hv
      rw [asg_append_lo _ _ (by simpa using hv)]
      simp [asg, List.getD_eq_getElem?_getD, hv]
    have hhi : ∀ i, asg ((List.range (cM q h x)).map (hotB (cU h) a) ++ p) (cM q h x + i) =
        asg p i := by
      intro i
      have := asg_append_hi ((List.range (cM q h x)).map (hotB (cU h) a)) p i
      simpa using this
    have hcellv : ∀ i < p.length, a (cCell q h x i) = cSb h (asg p i) := by
      intro i hi
      unfold cCell
      rw [ha, assign2_cv run 0 (clKs_spec h h.tm.k₀) (show x.length + 1 + i < c2S q h x by omega)]
      simp only [hrun, Function.iterate_zero, id, cellOf, initCfg, cSb, asg, Function.update_self,
        stk_get, hW, List.getElem?_append_left hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi]
      simp
    rw [coreCNF, evalCNF, List.all_append, Bool.and_eq_true]
    refine And.symm ⟨?_, ?_⟩
    · -- the tableau part
      have hsat : evalCNF (cl2CNF q h x) (hotB (cU h) a) = true := by
        rw [evalCNF_iff]
        intro cl hcl
        simp only [cl2CNF, cspCNF, List.mem_append, List.mem_map, List.mem_range,
          List.mem_flatMap] at hcl
        rcases hcl with ⟨v, -, rfl⟩ | ⟨c, hc', hcl⟩
        · have := alo_hot (cU h) a v (hU v)
          simpa [evalClause, cU] using this
        · have := con_hot (cU h) a c (fun v _ => hU v) (hc c hc')
          rw [evalCNF_iff] at this
          exact this cl hcl
      rw [evalCNF, List.all_eq_true] at hsat
      rw [List.all_eq_true]
      intro cl hcl
      rw [evalClause_congr cl _ (hotB (cU h) a) (fun l hl => ?_)]
      · exact hsat cl hcl
      obtain ⟨v, hv, e, he, hl'⟩ := cl2_vars q h x cl hcl l hl
      rw [hl']
      exact hlo _ (hot_lt q h x hv he)
    · -- the links
      rw [List.all_eq_true]
      intro cl hcl
      simp only [linkCNF, List.mem_flatMap, List.mem_range] at hcl
      obtain ⟨i, hi, hcl⟩ := hcl
      have hcl' := cCell_lt q h x (show i < q.eval x.length by omega)
      have ht := hot_lt q h x hcl' (cSb_mem h true)
      have hf := hot_lt q h x hcl' (cSb_mem h false)
      have hbt : asg ((List.range (cM q h x)).map (hotB (cU h) a) ++ p)
          (hotVar (cU h) (cCell q h x i) (cSb h true)) = asg p i := by
        rw [hlo _ ht, hotB_hot h (cU h) a _ (cSb_mem h true) (hU _), hcellv i hi]
        cases asg p i <;> simp <;> (intro e; exact absurd (cSb_inj h e) (by simp))
      have hbf : asg ((List.range (cM q h x)).map (hotB (cU h) a) ++ p)
          (hotVar (cU h) (cCell q h x i) (cSb h false)) = !asg p i := by
        rw [hlo _ hf, hotB_hot h (cU h) a _ (cSb_mem h false) (hU _), hcellv i hi]
        cases asg p i <;> simp <;> (intro e; exact absurd (cSb_inj h e) (by simp))
      simp only [linkI, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false, List.mem_map] at hcl
      rcases hcl with (rfl | rfl | rfl) | ⟨e, he, rfl⟩
      · simp only [evalClause, List.any_cons, List.any_nil, evalLiteral, hhi, hbt]; cases asg p i <;> rfl
      · simp only [evalClause, List.any_cons, List.any_nil, evalLiteral, hhi, hbt]; cases asg p i <;> rfl
      · simp only [evalClause, List.any_cons, List.any_nil, evalLiteral, hbt, hbf]
        cases asg p i <;> rfl
      · simp only [cBad, List.mem_filter, decide_eq_true_eq] at he
        simp only [evalClause, List.any_cons, List.any_nil, evalLiteral, if_true, Bool.or_false]
        rw [hlo _ (hot_lt q h x hcl' he.1), hotB_hot h (cU h) a _ he.1 (hU _), hcellv i hi]
        cases hb : asg p i
        · simp [he.2.2]
        · simp [he.2.1]
  · -- soundness
    rintro ⟨z, hz, hev⟩
    set b := asg (z ++ p) with hb
    rw [coreCNF, evalCNF, List.all_append, Bool.and_eq_true] at hev
    obtain ⟨hev2, hev1⟩ := hev
    have hall : ∀ cl ∈ cl2CNF q h x, evalClause cl b = true := List.all_eq_true.1 hev1
    have hlk : ∀ cl ∈ linkCNF q h x p.length, evalClause cl b = true := List.all_eq_true.1 hev2
    have halo : ∀ v < c2N q h x, evalClause (aloClause (cU h) v) b = true := fun v hv =>
      hall _ (by simp only [cl2CNF, cspCNF, List.mem_append, List.mem_map, List.mem_range]
                 exact Or.inl ⟨v, hv, rfl⟩)
    set a := decB (cU h) (cU_ne h) b with ha
    have hU : ∀ v, a v ∈ cU h := decB_mem _ _ _
    have hc : ∀ c ∈ tab2CS h.tm.m (clD h.tm) (pushTotal h.tm) (clKs h.tm) (c2S q h x) (clT q h x)
        h.tm.k₀ h.tm.k₁ h.tm.main h.tm.initialState (c2sb h) (c2sep h) (q.eval x.length) (c2acc h) x,
        c.rel (c.scope.map a) = true := by
      intro c hc
      refine con_of _ _ b c ?_ (fun v hv => halo v (tab2_scope_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (clKs_spec h) hS1 hS2 c hc v hv))
      rw [evalCNF, List.all_eq_true]
      intro cl hcl
      exact hall cl (by
        simp only [cl2CNF, cspCNF, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨c, hc, hcl⟩)
    obtain ⟨w, hwQ, h0⟩ := rep2_init (clKs_spec h) (cU h) (tab2Values_win _ _) a hU hc hS1
      (by omega)
    -- the linked cells
    have hcell : ∀ i < p.length, a (cCell q h x i) = cSb h (asg p i) := by
      intro i hi
      have hcl' := cCell_lt q h x (show i < q.eval x.length by omega)
      have hmk := decB_hot (cU h) (cU_ne h) b _ (halo _ hcl')
      rw [← ha] at hmk
      have hL : ∀ cl ∈ linkI q h x i, evalClause cl b = true := fun cl hcl =>
        hlk cl (by simp only [linkCNF, List.mem_flatMap, List.mem_range]; exact ⟨i, hi, hcl⟩)
      have hu : b (cM q h x + i) = asg p i := by rw [hb, ← hz, asg_append_hi]
      have c1 := hL [⟨cM q h x + i, true⟩, ⟨hotVar (cU h) (cCell q h x i) (cSb h true), false⟩]
        (by simp [linkI])
      have c2 := hL [⟨cM q h x + i, false⟩, ⟨hotVar (cU h) (cCell q h x i) (cSb h true), true⟩]
        (by simp [linkI])
      have c3 := hL [⟨hotVar (cU h) (cCell q h x i) (cSb h true), true⟩,
        ⟨hotVar (cU h) (cCell q h x i) (cSb h false), true⟩] (by simp [linkI])
      simp only [evalClause, List.any_cons, List.any_nil, evalLiteral, if_true, Bool.false_eq_true,
        if_false, Bool.or_false, hu] at c1 c2 c3
      have hgood : a (cCell q h x i) = cSb h true ∨ a (cCell q h x i) = cSb h false := by
        by_contra hn
        push_neg at hn
        have := hL [⟨hotVar (cU h) (cCell q h x i) (a (cCell q h x i)), true⟩] (by
          simp only [linkI, List.mem_append, List.mem_map]
          right; refine ⟨_, ?_, rfl⟩
          simp only [cBad, List.mem_filter, decide_eq_true_eq]
          exact ⟨hU _, hn⟩)
        simp [evalClause, evalLiteral, hmk] at this
      cases hpi : asg p i
      · rw [hpi] at c2
        rcases hgood with e | e
        · rw [e] at hmk; simp at c2; rw [hmk] at c2; simp at c2
        · exact e
      · rw [hpi] at c1
        rcases hgood with e | e
        · exact e
        · rw [e] at hmk; simp at c1; rw [hmk, c1] at c3; simp at c3
    have hwp : ∀ i < p.length, w[i]? = some (asg p i) := by
      intro i hi
      have e := h0.2 h.tm.k₀ (x.length + 1 + i) (by omega)
      rw [show cv2 (clKs h.tm) (c2S q h x) 0 h.tm.k₀ (x.length + 1 + i) = cCell q h x i from rfl,
        hcell i hi] at e
      simp only [cSb, cellOf, initCfg, Function.update_self, Sum.inr.injEq, stk_get] at e
      rcases hw : w[i]? with _ | c
      · rw [hw] at e; simp at e
      · rw [hw] at e
        simp only [Option.map_some, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
        rw [c2sb_inj h e.symm]
    have hlen : p.length ≤ w.length := by
      by_contra hl
      have := hwp w.length (by omega)
      simp at this
    have hweq : w = p ++ w.drop p.length := by
      apply List.ext_getElem?
      intro i
      rcases Nat.lt_or_ge i p.length with hi | hi
      · rw [hwp i hi, List.getElem?_append_left hi]
        simp [asg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      · rw [List.getElem?_append_right hi, List.getElem?_drop]
        congr 1; omega
    have hacc := tab2_accept_of (hd := clD_spec h) (hP := pushes_le_total h.tm) (hKs := clKs_spec h)
      (cU h) (tab2Values_win _ _) a hU hc hS2 w (c2_len q h x w hwQ) h0
    rw [c2_init, verifier_stay q h x w hwQ, c2_acc_cell] at hacc
    have e := eq_of_heq (Sigma.mk.inj_iff.1 (Option.some.inj hacc)).2
    have hV := h.outputAlphabet.symm.injective e
    refine ⟨w.drop p.length, ?_, ?_⟩
    · rw [← hweq]; exact hwQ
    · rw [← hweq]; exact hV

end Core

end PvnpReal
