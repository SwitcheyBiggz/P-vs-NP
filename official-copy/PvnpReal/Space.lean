/-
  PvnpReal.Space — deterministic **space** for Mathlib `FinTM2` deciders.

  Space measure: `SpaceBounded h S` says that in every configuration of the run of `h` on `x`
  (up to and including the halting step), **every stack has length ≤ S(|x|)**. The input stack is
  included (there is no separate read-only input tape), so `S(n) ≥ n` for every machine; sublinear
  space is not modelled.

  * `time_to_space`: a machine running in time `T` uses space `n + C·T(n)` (`C = pushTotal`).
  * `steps_le_card`: a halting run with space `S` has at most `A·B^{S}` steps (configuration counting;
    stack symbols range over the finite set of input symbols and symbols pushed by the program).
  * **`dtime_sub_dspace`**, **`dspace_sub_dtime`**, **`P_subset_PSPACE`**, **`PSPACE_subset_EXP`**.
  * **`space_hierarchy`**: for one universal exponent `k`, every `t` with suitable padding machine gives
    `diagT t ∈ DSPACE(K(t+n+1)^{k a})` but `∉ DSPACE(S)` whenever `A·B^{S(n)} = o(t(n))` for all `A, B`.
    (This is an exponential-gap space hierarchy, obtained via time; the textbook `DSPACE(s) ⊊ DSPACE(S)`
    for `s = o(S)` needs a space-efficient universal machine, NOT built here.)
-/
import PvnpReal.TimeHierarchy2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

/-! ### Symbols that can ever appear on the stacks -/

section Sym

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Symbols pushed by a statement. -/
def pushVals : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ pushVals q
  | .peek _ _ q => pushVals q
  | .pop _ _ q => pushVals q
  | .load _ q => pushVals q
  | .branch _ q₁ q₂ => pushVals q₁ ∪ pushVals q₂
  | .goto _ => ∅
  | .halt => ∅

theorem pushVals_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (pushVals q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

def GoodS (Sy : Set (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k, ∀ a ∈ S k, (⟨k, a⟩ : Σ k, Γ k) ∈ Sy

theorem stepAux_good [DecidableEq K] (Sy : Set (Σ k, Γ k)) (q : TM2.Stmt Γ Λ σ)
    (hq : pushVals q ⊆ Sy) (v : σ) (S : ∀ k, List (Γ k)) (hS : GoodS Sy S) :
    GoodS Sy (TM2.stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [TM2.stepAux]
    apply ih (fun x hx => hq (Or.inr hx))
    intro j a ha
    by_cases h : j = k
    · subst h
      rw [Function.update_self] at ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hq (Or.inl ⟨v, rfl⟩)
      · exact hS j a ha
    · rw [Function.update_of_ne h] at ha; exact hS j a ha
  | peek k f q ih => simp only [TM2.stepAux]; exact ih hq _ _ hS
  | pop k f q ih =>
    simp only [TM2.stepAux]
    apply ih hq
    intro j a ha
    by_cases h : j = k
    · subst h
      rw [Function.update_self] at ha
      exact hS j a (List.mem_of_mem_tail ha)
    · rw [Function.update_of_ne h] at ha; exact hS j a ha
  | load a q ih => simp only [TM2.stepAux]; exact ih hq _ _ hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ (fun x hx => hq (Or.inr hx)) _ _ hS
    · exact ih₁ (fun x hx => hq (Or.inl hx)) _ _ hS
  | goto f => exact hS
  | halt => exact hS

end Sym

/-- All stack symbols a machine can ever hold. -/
def symSet (tm : FinTM2) : Set (Σ k, tm.Γ k) :=
  (⋃ l, pushVals (tm.m l)) ∪ Set.range (fun a : tm.Γ tm.k₀ => (⟨tm.k₀, a⟩ : Σ k, tm.Γ k))

theorem symSet_finite (tm : FinTM2) : (symSet tm).Finite :=
  (Set.finite_iUnion (fun l => pushVals_finite (tm.m l))).union (Set.finite_range _)

instance (tm : FinTM2) : Finite (symSet tm) := (symSet_finite tm).to_subtype

theorem step_good (tm : FinTM2) (c d : tm.Cfg) (hc : GoodS (symSet tm) c.stk)
    (h : tm.step c = some d) : GoodS (symSet tm) d.stk := by
  rcases c with ⟨_ | l, v, S⟩
  · cases h
  · change some (TM2.stepAux (tm.m l) v S) = some d at h
    cases h
    exact stepAux_good _ _ (fun x hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)) v S hc

theorem iter_good (tm : FinTM2) (i : ℕ) : ∀ (c d : tm.Cfg), GoodS (symSet tm) c.stk →
    (flip bind tm.step)^[i] (some c) = some d → GoodS (symSet tm) d.stk := by
  induction i with
  | zero => intro c d hc h; simp at h; subst h; exact hc
  | succ i ih =>
    intro c d hc h
    rw [Function.iterate_succ_apply] at h
    change (flip bind tm.step)^[i] (tm.step c) = some d at h
    rcases hs : tm.step c with _ | c'
    · rw [hs, flip_bind_iterate_none] at h; cases h
    · rw [hs] at h; exact ih c' d (step_good tm c c' hc hs) h

theorem init_good (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    GoodS (symSet tm) (initList tm l).stk := by
  intro k a _
  by_cases hk : k = tm.k₀
  · subst hk; exact Or.inr ⟨a, rfl⟩
  · simp only [initList, dif_neg hk] at *
    simp_all

/-! ### Configuration counting -/

section Count

open Classical

variable (tm : FinTM2)

noncomputable def symCode (k : tm.K) (a : tm.Γ k) : Option (symSet tm) :=
  if h : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ symSet tm then some ⟨_, h⟩ else none

noncomputable def cfgCode (S : ℕ) (c : tm.Cfg) :
    Option tm.Λ × tm.σ × (tm.K → Fin S → Option (Option (symSet tm))) :=
  (c.l, c.var, fun k i => (c.stk k)[i.1]?.map (symCode tm k))

theorem symCode_inj {k : tm.K} {a b : tm.Γ k} (ha : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ symSet tm)
    (hb : (⟨k, b⟩ : Σ k, tm.Γ k) ∈ symSet tm) (h : symCode tm k a = symCode tm k b) : a = b := by
  unfold symCode at h
  rw [dif_pos ha, dif_pos hb] at h
  simp only [Option.some.injEq, Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact h

theorem cfgCode_inj (S : ℕ) (c d : tm.Cfg) (hc : GoodS (symSet tm) c.stk)
    (hd : GoodS (symSet tm) d.stk) (hcS : ∀ k, (c.stk k).length ≤ S)
    (hdS : ∀ k, (d.stk k).length ≤ S) (h : cfgCode tm S c = cfgCode tm S d) : c = d := by
  rcases c with ⟨l, v, A⟩
  rcases d with ⟨l', v', B⟩
  simp only [cfgCode, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, h3⟩ := h
  congr
  funext k
  apply List.ext_getElem?
  intro n
  by_cases hn : n < S
  · have e := congrFun (congrFun h3 k) ⟨n, hn⟩
    simp only at e
    rcases ha : (A k)[n]? with _ | a <;> rcases hb : (B k)[n]? with _ | b <;>
      simp only [ha, hb, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at e ⊢
    have ma : a ∈ A k := List.mem_of_getElem? ha
    have mb : b ∈ B k := List.mem_of_getElem? hb
    exact symCode_inj tm (hc k a ma) (hd k b mb) e
  · have h1 := hcS k
    have h2 := hdS k
    simp only at h1 h2
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end Count

theorem natCard_option {α : Type} [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]

/-- No configuration repeats before halting. -/
theorem run_no_repeat {α : Type} (f : α → Option α) (a : Option α) (N : ℕ)
    (hN : (flip bind f)^[N + 1] a = none) (hs : ∀ m ≤ N, (flip bind f)^[m] a ≠ none)
    {i j : ℕ} (hij : i < j) (hj : j ≤ N) (h : (flip bind f)^[i] a = (flip bind f)^[j] a) : False := by
  set F := flip bind f
  have per : ∀ r m, F^[m + r * (j - i) + i] a = F^[m + i] a := by
    intro r
    induction r with
    | zero => intro m; simp
    | succ r ih =>
      intro m
      have e1 : m + (r + 1) * (j - i) + i = (m + r * (j - i)) + j := by
        rw [Nat.add_mul]; omega
      rw [e1, Function.iterate_add_apply, ← h, ← Function.iterate_add_apply, ih]
  have hd : 0 < j - i := by omega
  have e := per ((N + 1 - i) / (j - i)) ((N + 1 - i) % (j - i))
  have e2 : (N + 1 - i) % (j - i) + (N + 1 - i) / (j - i) * (j - i) + i = N + 1 := by
    have := Nat.mod_add_div (N + 1 - i) (j - i)
    rw [mul_comm] at this; omega
  rw [e2, hN] at e
  have hm : (N + 1 - i) % (j - i) < j - i := Nat.mod_lt _ hd
  exact hs _ (by omega) e.symm

/-- `L ∈ DSPACE(S)` machinery: every stack stays within `S(|x|)` during the run. -/
def SpaceBounded {f : List Bool → Bool} (h : TM2ComputableInTime strEnc encodeBool f)
    (S : ℕ → ℕ) : Prop :=
  ∀ x i (c : h.tm.Cfg), i ≤ (h.outputsFun x).steps →
    (flip bind h.tm.step)^[i] (some (initList h.tm (List.map h.inputAlphabet.invFun (strEnc x)))) =
      some c → ∀ k, (c.stk k).length ≤ S x.length

def InDSPACE (S : ℕ → ℕ) (L : Language) : Prop :=
  ∃ (f : List Bool → Bool) (h : TM2ComputableInTime strEnc encodeBool f),
    SpaceBounded h S ∧ ∀ x, L x ↔ f x = true

def InPSPACE (L : Language) : Prop := ∃ p : Polynomial ℕ, InDSPACE (fun n => p.eval n) L

theorem InDSPACE.mono {S S' : ℕ → ℕ} {L : Language} (h : InDSPACE S L) (hS : ∀ n, S n ≤ S' n) :
    InDSPACE S' L := by
  obtain ⟨f, h, hb, hL⟩ := h
  exact ⟨f, h, fun x i c hi hc k => (hb x i c hi hc k).trans (hS _), hL⟩

/-- **Time bounds space**: time `T` ⇒ space `n + C·T(n)`. -/
theorem time_to_space {f : List Bool → Bool} (h : TM2ComputableInTime strEnc encodeBool f) :
    SpaceBounded h (fun n => n + pushTotal h.tm * h.time n) := by
  intro x i c hi hc k
  have hl := iterate_len h.tm i _ c hc (List.map h.inputAlphabet.invFun (strEnc x)).length (by
    intro k
    simp only [initList]
    split
    · next hk => subst hk; simp
    · simp) k
  have hs := (h.outputsFun x).steps_le_m
  have : pushTotal h.tm * i ≤ pushTotal h.tm * h.time x.length :=
    Nat.mul_le_mul_left _ (hi.trans hs)
  simp only [List.length_map, strEnc] at hl ⊢
  omega

theorem dtime_sub_dspace {T : ℕ → ℕ} {L : Language} (hL : InDTIME T L) :
    ∃ C, InDSPACE (fun n => n + C * T n) L := by
  obtain ⟨f, h, hb, hf⟩ := hL
  exact ⟨pushTotal h.tm, f, h, fun x i c hi hc k =>
    (time_to_space h x i c hi hc k).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hb _)) _), hf⟩

/-- **Configuration counting**: a run with space `S` has at most `A·B^{S}` steps. -/
theorem steps_le_card {f : List Bool → Bool} (h : TM2ComputableInTime strEnc encodeBool f)
    (S : ℕ → ℕ) (hS : SpaceBounded h S) (x : List Bool) :
    (h.outputsFun x).steps ≤ (Nat.card h.tm.Λ + 1) * Nat.card h.tm.σ *
      ((Nat.card (symSet h.tm) + 2) ^ Nat.card h.tm.K) ^ S x.length := by
  set tm := h.tm
  set N := (h.outputsFun x).steps
  set c0 := initList tm (List.map h.inputAlphabet.invFun (strEnc x))
  set F := flip bind tm.step
  have hev : F^[N] (some c0) = some (haltList tm _) := (h.outputsFun x).evals_in_steps
  have hN : F^[N + 1] (some c0) = none := by
    rw [Function.iterate_succ_apply', hev]; rfl
  have hs : ∀ m ≤ N, F^[m] (some c0) ≠ none := by
    intro m hm e
    have : F^[N] (some c0) = none := by
      rw [show N = (N - m) + m by omega, Function.iterate_add_apply, e, flip_bind_iterate_none]
    rw [hev] at this; cases this
  let g : Fin (N + 1) → Option (Option tm.Λ × tm.σ × (tm.K → Fin (S x.length) →
      Option (Option (symSet tm)))) := fun j => (F^[j.1] (some c0)).map (cfgCode tm (S x.length))
  have hg : Function.Injective g := by
    intro i j e
    rcases hi : F^[i.1] (some c0) with _ | ci
    · exact absurd hi (hs i (by omega))
    rcases hj : F^[j.1] (some c0) with _ | cj
    · exact absurd hj (hs j (by omega))
    simp only [g, hi, hj, Option.map_some, Option.some.injEq] at e
    have gi := iter_good tm i.1 c0 ci (init_good tm _) hi
    have gj := iter_good tm j.1 c0 cj (init_good tm _) hj
    have ecd := cfgCode_inj tm _ ci cj gi gj (hS x i ci (by omega) hi) (hS x j cj (by omega) hj) e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h' => hne (Fin.ext h')) with hl | hl
    · exact run_no_repeat tm.step (some c0) N hN hs hl (by omega) (by rw [hi, hj, ecd])
    · exact run_no_repeat tm.step (some c0) N hN hs hl (by omega) (by rw [hi, hj, ecd])
  have hc := Nat.card_le_card_of_injective g hg
  simp only [Nat.card_eq_fintype_card (α := Fin (N + 1)), Fintype.card_fin, natCard_option,
    Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (S x.length))] at hc
  have e : ((Nat.card (symSet tm) + 1 + 1) ^ S x.length) ^ Nat.card tm.K =
      ((Nat.card (symSet tm) + 2) ^ Nat.card tm.K) ^ S x.length := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e] at hc
  rw [mul_assoc]
  exact Nat.le_of_succ_le_succ hc

/-- **Space bounds time**: `DSPACE(S) ⊆ DTIME(A·B^{S})` (constants depending on the machine). -/
theorem dspace_sub_dtime {S : ℕ → ℕ} {L : Language} (hL : InDSPACE S L) :
    ∃ A B, InDTIME (fun n => A * B ^ S n) L := by
  obtain ⟨f, h, hb, hf⟩ := hL
  let A := (Nat.card h.tm.Λ + 1) * Nat.card h.tm.σ
  let B := (Nat.card (symSet h.tm) + 2) ^ Nat.card h.tm.K
  let h' : TM2ComputableInTime strEnc encodeBool f :=
    { tm := h.tm
      inputAlphabet := h.inputAlphabet
      outputAlphabet := h.outputAlphabet
      time := fun n => A * B ^ S n
      outputsFun := fun x =>
        { steps := (h.outputsFun x).steps
          evals_in_steps := (h.outputsFun x).evals_in_steps
          steps_le_m := by
            exact steps_le_card h S hb x } }
  exact ⟨A, B, f, h', fun n => le_rfl, hf⟩

/-- **P ⊆ PSPACE.** -/
theorem P_subset_PSPACE (L : Language) (hL : InP L) : InPSPACE L := by
  obtain ⟨f, ⟨hf⟩, hfL⟩ := hL
  obtain ⟨C, hC⟩ := dtime_sub_dspace (T := fun n => hf.time.eval n)
    ⟨f, hf.toTM2ComputableInTime, fun n => le_rfl, hfL⟩
  exact ⟨Polynomial.X + Polynomial.C C * hf.time, hC.mono (fun n => by simp)⟩

/-- **PSPACE ⊆ EXP.** -/
theorem PSPACE_subset_EXP (L : Language) (hL : InPSPACE L) : InEXP L := by
  obtain ⟨p, hp⟩ := hL
  obtain ⟨A, B, f, h, hb, hf⟩ := dspace_sub_dtime hp
  refine ⟨f, Polynomial.C A + Polynomial.C B * p, ⟨h, fun n => (hb n).trans ?_⟩, hf⟩
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul]
  rw [pow_add, pow_mul]
  exact Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _)

/-- Lower bound: `diagT t ∉ DSPACE(S)` when `A·B^{S} = o(t)` for all `A, B`. -/
theorem diagT_not_in_DSPACE (t S : ℕ → ℕ)
    (hS : ∀ A B D : ℕ, ∃ N, ∀ n ≥ N, D * (A * B ^ S n) + 1 ≤ t n) : ¬ InDSPACE S (diagT t) := by
  intro h
  obtain ⟨A, B, hT⟩ := dspace_sub_dtime h
  exact diagT_not_in_DTIME t _ (fun D => hS A B D) hT

/-- **Space hierarchy (exponential gap, via time)**, with one universal exponent `k`. -/
theorem space_hierarchy : ∃ k : ℕ, 1 ≤ k ∧ ∀ (t : ℕ → ℕ)
    (hp : TM2ComputableInTime strEnc strEnc (padWith t)) (A a : ℕ), 1 ≤ a →
    (∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) →
    ∃ K, InDSPACE (fun n => K * (t n + n + 1) ^ (k * a)) (diagT t) ∧
      ∀ S : ℕ → ℕ, (∀ A B D : ℕ, ∃ N, ∀ n ≥ N, D * (A * B ^ S n) + 1 ≤ t n) →
        ¬ InDSPACE S (diagT t) := by
  obtain ⟨k, hk, hT⟩ := time_hierarchy_pow
  refine ⟨k, hk, fun t hp A a ha hA => ?_⟩
  obtain ⟨K, hK, -⟩ := hT t hp A a ha hA
  obtain ⟨C, hC⟩ := dtime_sub_dspace hK
  refine ⟨C * K + 1, hC.mono (fun n => ?_), fun S hS => diagT_not_in_DSPACE t S hS⟩
  have hm : 1 ≤ t n + n + 1 := by omega
  have h1 : t n + n + 1 ≤ (t n + n + 1) ^ (k * a) := by
    calc t n + n + 1 = (t n + n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hm (Nat.one_le_iff_ne_zero.2 (by positivity))
  generalize (t n + n + 1) ^ (k * a) = Q at h1
  have e : (C * K + 1) * Q = C * (K * Q) + Q := by ring
  omega

end PvnpReal
