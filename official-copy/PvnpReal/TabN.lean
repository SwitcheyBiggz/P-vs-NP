/-
  PvnpReal.TabN — the tableau of a nondeterministic run.

  The control constraint between rows `t` and `t+1` is relaxed to `transCPN`: the next label is
  either the label reached by the step or its `alt`-relabelling (the choice of an `NTM`); all cell
  constraints are those of the deterministic tableau (`(csTrans m …).tail`), since relabelling does
  not touch the stacks. The final row must be halted with the accepting symbol (`csFinalH`).
  `tabN_sound`: a solution yields a choice sequence whose run accepts at row `T`;
  `tabN_complete`: an accepting run yields a solution.
-/
import PvnpReal.NSpace

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

open scoped Classical

section TabN

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Relabel the next instruction with `alt` when `b = true`. -/
def relabC (alt : Λ → Λ) (b : Bool) (c : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  ⟨if b then c.l.map alt else c.l, c.var, c.stk⟩

/-- Nondeterministic run with choice sequence `bs`. -/
def runG (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (bs : ℕ → Bool) (c : Cfg Γ Λ σ) : ℕ → Cfg Γ Λ σ
  | 0 => c
  | t + 1 => relabC alt (bs t) (stepStay m (runG m alt bs c t))

theorem runG_congr (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (bs bs' : ℕ → Bool) (c : Cfg Γ Λ σ) :
    ∀ t, (∀ s < t, bs s = bs' s) → runG m alt bs c t = runG m alt bs' c t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    simp only [runG]
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

theorem NTM.run_eq (N : NTM) (bs : ℕ → Bool) (x : List Bool) :
    ∀ t, N.run bs x t = runG N.tm.m N.alt bs (N.init x) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show N.nstep (bs t) (N.run bs x t) = _
    rw [ih]; rfl

variable (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (d P : ℕ)

/-- The relaxed control relation. -/
def transCPN (R R' : Ctl Γ Λ σ) : Prop :=
  ∃ (R'' : Ctl Γ Λ σ) (b : Bool), transCP m R R'' ∧ R'.var = R''.var ∧
    R'.l = (if b then R''.l.map alt else R''.l)

theorem transCPN_iff (hd : ∀ lab, sdepth (m lab) ≤ d) (c : Cfg Γ Λ σ) (R' : Ctl Γ Λ σ) :
    transCPN m alt (ctlOf d c) R' ↔
      ∃ b, R'.l = (relabC alt b (stepStay m c)).l ∧ R'.var = (relabC alt b (stepStay m c)).var := by
  constructor
  · rintro ⟨R'', b, h1, h2, h3⟩
    rw [transCP_iff m d hd] at h1
    refine ⟨b, ?_, ?_⟩
    · rw [h3, h1.1]; rfl
    · rw [h2, h1.2]; rfl
  · rintro ⟨b, h1, h2⟩
    refine ⟨⟨(stepStay m c).l, (stepStay m c).var, R'.win⟩, b, ?_, h2, h1⟩
    rw [transCP_iff m d hd]
    exact ⟨rfl, rfl⟩

variable (Ks : List K) (S T : ℕ) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool)

/-- Between rows `t` and `t + 1`, nondeterministically. -/
noncomputable def csTransN (t : ℕ) : List (Constraint (V2 Γ Λ σ)) :=
  ⟨[sv2 Ks S t, sv2 Ks S (t + 1)], ctlRel2 (transCPN m alt)⟩ :: (csTrans m d P Ks S t).tail

/-- Final row: accepting symbol on the output stack, and halted. -/
noncomputable def csFinalH : List (Constraint (V2 Γ Λ σ)) :=
  csFinal Ks S T k₁ gacc ++ [⟨[sv2 Ks S T], ctlRel1 (fun R => R.l = none)⟩]

/-- **The nondeterministic tableau.** -/
noncomputable def tabNCS : List (Constraint (V2 Γ Λ σ)) :=
  csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs ++ (List.range (T + 1)).flatMap (csRow d Ks S) ++
    (List.range T).flatMap (csTransN m alt d P Ks S) ++ csFinalH Ks S T k₁ gacc

/-! ### Membership -/

section Mem
variable {m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs}
variable (hKs : ∀ k, k ∈ Ks)

local notation "CSN" => tabNCS m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs

theorem mN_pre {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs) :
    c ∈ CSN :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

theorem mN_row {t : ℕ} (ht : t ≤ T) {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csRow d Ks S t) : c ∈ CSN :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨t, List.mem_range.2 (by omega), h⟩)))

theorem mN_trans {t : ℕ} (ht : t < T) {c : Constraint (V2 Γ Λ σ)}
    (h : c ∈ csTransN m alt d P Ks S t) : c ∈ CSN :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, h⟩))

theorem mN_tail {t : ℕ} (ht : t < T) {c : Constraint (V2 Γ Λ σ)}
    (h : c ∈ (csTrans m d P Ks S t).tail) : c ∈ CSN :=
  mN_trans ht (List.mem_cons_of_mem _ h)

theorem mN_tctl {t : ℕ} (ht : t < T) :
    (⟨[sv2 Ks S t, sv2 Ks S (t + 1)], ctlRel2 (transCPN m alt)⟩ : Constraint (V2 Γ Λ σ)) ∈ CSN :=
  mN_trans ht (List.mem_cons_self ..)

include hKs in
theorem mN_link {t : ℕ} (ht : t ≤ T) (k : K) {i : ℕ} (hi : i < d) :
    (⟨[sv2 Ks S t, cv2 Ks S t k i], linkRel k i⟩ : Constraint (V2 Γ Λ σ)) ∈ CSN :=
  mN_row ht (List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_left _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)⟩)

include hKs in
theorem mN_blankEnd {t : ℕ} (ht : t ≤ T) (k : K) {j : ℕ} (hj : j < d + 1) :
    (⟨[cv2 Ks S t k (S - (d + 1) + j)], cellRel1 (· = none)⟩ : Constraint (V2 Γ Λ σ)) ∈ CSN :=
  mN_row ht (List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_right _
    (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)⟩)

include hKs in
theorem mN_small {t : ℕ} (ht : t < T) (k : K) {p : ℕ} (hp : p < d + P) :
    (⟨sv2 Ks S t :: cv2 Ks S (t + 1) k p :: (List.range (p + d + 1)).map (fun i => cv2 Ks S t k i),
      tcRel m d k p p⟩ : Constraint (V2 Γ Λ σ)) ∈ CSN :=
  mN_tail ht (by
    simp only [csTrans, List.tail_cons]
    exact List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_left _
      (List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩)⟩)

include hKs in
theorem mN_deep {t : ℕ} (ht : t < T) (k : K) {j : ℕ} (hj : j < S - (d + P) - (d + 1)) :
    (⟨sv2 Ks S t :: cv2 Ks S (t + 1) k (d + P + j) ::
        (List.range (P + d + 1)).map (fun i => cv2 Ks S t k (d + j + i)),
      tcRel m d k P (d + P)⟩ : Constraint (V2 Γ Λ σ)) ∈ CSN :=
  mN_tail ht (by
    simp only [csTrans, List.tail_cons]
    exact List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_right _
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)⟩)

theorem mN_final : (⟨[cv2 Ks S T k₁ 0], cellRel1 (· = some ⟨k₁, gacc⟩)⟩ :
    Constraint (V2 Γ Λ σ)) ∈ CSN :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton_self _))

theorem mN_halt : (⟨[sv2 Ks S T], ctlRel1 (fun R => R.l = none)⟩ :
    Constraint (V2 Γ Λ σ)) ∈ CSN :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _))

end Mem

/-! ### Soundness -/

variable {m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs}

local notation "CSN" => tabNCS m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs

theorem ctl_of_linksN (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (a : ℕ → V2 Γ Λ σ) (hU : ∀ v, a v ∈ U) (hc : ∀ c ∈ CSN, c.rel (c.scope.map a) = true)
    {t : ℕ} (ht : t ≤ T) (c : Cfg Γ Λ σ) (R : Ctl Γ Λ σ)
    (hR : a (sv2 Ks S t) = Sum.inl R) (hl : R.l = c.l) (hv : R.var = c.var)
    (hcells : ∀ k, ∀ p < S, a (cv2 Ks S t k p) = Sum.inr (cellOf c k p)) (hdS : d ≤ S) :
    R = ctlOf d c := by
  refine ctl_eq_of d R c hl hv (hUd R (hR ▸ hU _)) (fun k i hi => ?_)
  have h := hc _ (mN_link (m := m) (alt := alt) (P := P) (k₀ := k₀) (k₁ := k₁) (main := main)
    (v₀ := v₀) (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs) hKs ht k hi)
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨R', c', h1, h2, h3⟩ := linkRel_true h
  rw [hR] at h1; cases h1
  rw [hcells k i (by omega)] at h2; cases h2
  exact h3

theorem repN_step (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (a : ℕ → V2 Γ Λ σ) (hU : ∀ v, a v ∈ U) (hc : ∀ c ∈ CSN, c.rel (c.scope.map a) = true)
    (hS2 : 2 * d + P + 1 ≤ S) {t : ℕ} (ht : t < T) (c : Cfg Γ Λ σ) (hrep : Rep2 d Ks S a t c)
    (hlen : ∀ k, ((stepStay m c).stk k).length ≤ S - (d + 1)) :
    ∃ b, Rep2 d Ks S a (t + 1) (relabC alt b (stepStay m c)) := by
  have hcells : ∀ k, ∀ p < S, a (cv2 Ks S (t + 1) k p) = Sum.inr (cellOf (stepStay m c) k p) := by
    intro k p hp
    by_cases h1 : p < d + P
    · have h := hc _ (mN_small (alt := alt) (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs)
        (k₁ := k₁) (main := main) (v₀ := v₀) hKs ht k h1)
      simp only [List.map_cons, List.map_map] at h
      rw [hrep.1] at h
      obtain ⟨new, hnew, htc⟩ := tcRel_true m d h
      have eo : List.map (a ∘ fun i => cv2 Ks S t k i) (List.range (p + d + 1)) =
          (List.range (p + d + 1)).map (fun i => Sum.inr (cellOf c k (p - p + i))) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        simp only [Function.comp, Nat.sub_self, Nat.zero_add]
        exact hrep.2 k i (by omega)
      rw [eo] at htc
      rw [hnew, (tcP_iff m d P hd hP c k p p p le_rfl (Or.inl ⟨rfl, rfl⟩) new).1 htc]
    · by_cases h2 : p < S - (d + 1)
      · obtain ⟨j, rfl⟩ : ∃ j, p = d + P + j := ⟨p - (d + P), by omega⟩
        have h := hc _ (mN_deep (alt := alt) (sb := sb) (sep := sep) (Q := Q) (gacc := gacc)
          (xs := xs) (k₁ := k₁) (main := main) (v₀ := v₀) hKs ht k (j := j) (by omega))
        simp only [List.map_cons, List.map_map] at h
        rw [hrep.1] at h
        obtain ⟨new, hnew, htc⟩ := tcRel_true m d h
        have eo : List.map (a ∘ fun i => cv2 Ks S t k (d + j + i)) (List.range (P + d + 1)) =
            (List.range (P + d + 1)).map (fun i => Sum.inr (cellOf c k (d + P + j - P + i))) := by
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          simp only [Function.comp]
          rw [show d + P + j - P + i = d + j + i by omega]
          exact hrep.2 k _ (by omega)
        rw [eo] at htc
        rw [hnew, (tcP_iff m d P hd hP c k (d + P + j) P (d + P) (by omega)
          (Or.inr ⟨rfl, by omega, rfl⟩) new).1 htc]
      · obtain ⟨j, rfl⟩ : ∃ j, p = S - (d + 1) + j := ⟨p - (S - (d + 1)), by omega⟩
        have h := hc _ (mN_blankEnd (m := m) (alt := alt) (P := P) (sb := sb) (sep := sep) (Q := Q)
          (gacc := gacc) (xs := xs) (k₁ := k₁) (main := main) (v₀ := v₀) hKs (t := t + 1)
          (by omega) k (j := j) (by omega))
        simp only [List.map_cons, List.map_nil] at h
        obtain ⟨c', h1, h2⟩ := cellRel1_true h
        rw [h1, h2]
        simp only [cellOf]
        rw [List.getElem?_eq_none (by have := hlen k; omega)]
        rfl
  have h := hc _ (mN_tctl (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs) (k₁ := k₁)
    (main := main) (v₀ := v₀) (Ks := Ks) (S := S) (m := m) (alt := alt) (d := d) (P := P) ht)
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨R, R', h1, h2, h3⟩ := ctlRel2_true h
  rw [hrep.1] at h1; cases h1
  rw [transCPN_iff m alt d hd] at h3
  obtain ⟨b, hb1, hb2⟩ := h3
  refine ⟨b, ?_, hcells⟩
  rw [h2, ctl_of_linksN hKs U hUd a hU hc (t := t + 1) (by omega) _ R' h2 hb1 hb2 hcells (by omega)]

theorem repN_init (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (a : ℕ → V2 Γ Λ σ) (hU : ∀ v, a v ∈ U) (hc : ∀ c ∈ CSN, c.rel (c.scope.map a) = true)
    (hS1 : xs.length + 2 + Q ≤ S) (hdS : d ≤ S) :
    ∃ w : List Bool, w.length ≤ Q ∧
      Rep2 d Ks S a 0 (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) := by
  -- the first input cell holds some symbol `g`
  have hpre : ∀ c ∈ csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs, c.rel (c.scope.map a) = true :=
    fun c h => hc c (mN_pre h)
  obtain ⟨g, hg⟩ : ∃ g : Γ k₀, a (cv2 Ks S 0 k₀ 0) = Sum.inr (some ⟨k₀, g⟩) := by
    cases hx : xs with
    | nil =>
      have h := hpre ⟨[cv2 Ks S 0 k₀ xs.length], cellRel1 (· = some ⟨k₀, sep⟩)⟩
        (List.mem_append_right _ (by simp [csInit]))
      simp only [List.map_cons, List.map_nil, hx, List.length_nil] at h
      obtain ⟨c, e1, e2⟩ := cellRel1_true h
      exact ⟨sep, by rw [e1, e2]⟩
    | cons b xs' =>
      have h := hpre ⟨[cv2 Ks S 0 k₀ 0, NthTM.bit xs 0], cellRel2 (· = ·)⟩
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
            (List.mem_map.2 ⟨0, List.mem_range.2 (by simp [hx]), rfl⟩)))))))
      simp only [List.map_cons, List.map_nil] at h
      obtain ⟨c, c', e1, e2, e3⟩ := cellRel2_true h
      cases b
      · have hz := hpre ⟨[0], cellRel1 (· = some ⟨k₀, sb false⟩)⟩
          (List.mem_append_left _ (by simp [csZ]))
        simp only [List.map_cons, List.map_nil] at hz
        obtain ⟨z, f1, f2⟩ := cellRel1_true hz
        have hb : NthTM.bit xs 0 = 0 := by simp [hx, NthTM.bit]
        rw [hb, f1] at e2; cases e2
        exact ⟨sb false, by rw [e1, e3, f2]⟩
      · have hz := hpre ⟨[1], cellRel1 (· = some ⟨k₀, sb true⟩)⟩
          (List.mem_append_left _ (by simp [csZ]))
        simp only [List.map_cons, List.map_nil] at hz
        obtain ⟨z, f1, f2⟩ := cellRel1_true hz
        have hb : NthTM.bit xs 0 = 1 := by simp [hx, NthTM.bit]
        rw [hb, f1] at e2; cases e2
        exact ⟨sb true, by rw [e1, e3, f2]⟩
  have hc' : ∀ c ∈ tab2CS m d P Ks S 0 k₀ k₀ main v₀ sb sep Q g xs,
      c.rel (c.scope.map a) = true := by
    intro c hcm
    simp only [tab2CS, List.mem_append] at hcm
    rcases hcm with (((h | h) | h) | h) | h
    · exact hpre c (List.mem_append_left _ h)
    · exact hpre c (List.mem_append_right _ h)
    · obtain ⟨t, ht, h⟩ := List.mem_flatMap.1 h
      rw [List.mem_range] at ht
      exact hc c (mN_row (T := T) (Nat.zero_le _ |>.trans' (by omega)) h)
    · simp at h
    · simp only [csFinal, List.mem_singleton] at h
      subst h
      simp only [List.map_cons, List.map_nil, hg, cellRel1, decide_true]
  exact rep2_init (m := m) (P := P) (T := 0) (k₁ := k₀) (gacc := g) hKs U hUd a hU hc' hS1 hdS

/-- **Soundness of the nondeterministic tableau.** -/
theorem tabN_sound (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S)
    (hlen : ∀ w : List Bool, w.length ≤ Q → ∀ (bs : ℕ → Bool), ∀ t ≤ T, ∀ k,
      ((runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) t).stk k).length ≤
        S - (d + 1))
    (hsat : CSPSat U CSN) :
    ∃ w : List Bool, w.length ≤ Q ∧ ∃ bs : ℕ → Bool,
      (runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) T).l = none ∧
      cellOf (runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) T) k₁ 0 =
        some ⟨k₁, gacc⟩ := by
  obtain ⟨a, hU, hc⟩ := hsat
  obtain ⟨w, hwl, h0⟩ := repN_init hKs U hUd a hU hc hS1 (by omega)
  refine ⟨w, hwl, ?_⟩
  set c0 := initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)
  have hrep : ∀ t ≤ T, ∃ bs : ℕ → Bool, Rep2 d Ks S a t (runG m alt bs c0 t) := by
    intro t ht
    induction t with
    | zero => exact ⟨fun _ => false, h0⟩
    | succ t ih =>
      obtain ⟨bs, hbs⟩ := ih (by omega)
      obtain ⟨b, hb⟩ := repN_step hd hP hKs U hUd a hU hc hS2 (by omega) _ hbs
        (fun k => hlen w hwl bs (t + 1) ht k)
      refine ⟨Function.update bs t b, ?_⟩
      have e : runG m alt (Function.update bs t b) c0 t = runG m alt bs c0 t :=
        runG_congr m alt _ _ c0 t (fun s hs => Function.update_of_ne (by omega) _ _)
      show Rep2 d Ks S a (t + 1) (relabC alt (Function.update bs t b t)
        (stepStay m (runG m alt (Function.update bs t b) c0 t)))
      rw [Function.update_self, e]
      exact hb
  obtain ⟨bs, hT⟩ := hrep T le_rfl
  refine ⟨bs, ?_, ?_⟩
  · have h := hc _ (mN_halt (m := m) (alt := alt) (d := d) (P := P) (T := T) (k₀ := k₀)
      (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs) (Q := Q) (main := main)
      (v₀ := v₀) (k₁ := k₁))
    simp only [List.map_cons, List.map_nil] at h
    obtain ⟨R, e1, e2⟩ := ctlRel1_true h
    rw [hT.1] at e1; cases e1
    exact e2
  · have h := hc _ (mN_final (m := m) (alt := alt) (d := d) (P := P) (T := T) (k₀ := k₀)
      (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs) (Q := Q) (main := main)
      (v₀ := v₀) (k₁ := k₁))
    simp only [List.map_cons, List.map_nil] at h
    obtain ⟨c, e1, e2⟩ := cellRel1_true h
    rw [hT.2 k₁ 0 (by omega)] at e1
    cases e1
    exact e2

/-- **Completeness of the nondeterministic tableau.** -/
theorem tabN_complete (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S)
    (w : List Bool) (hw : w.length ≤ Q) (bs : ℕ → Bool)
    (hlen : ∀ t ≤ T, ∀ k,
      ((runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) t).stk k).length ≤
        S - (d + 1))
    (hhalt : (runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) T).l = none)
    (hacc : cellOf (runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) T) k₁ 0 =
        some ⟨k₁, gacc⟩)
    (U : List (V2 Γ Λ σ))
    (hU : ∀ v, assign2 d Ks S k₀ sb
      (fun t => runG m alt bs (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) t) v ∈ U) :
    CSPSat U CSN := by
  set c0 := initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb) with hc0
  set run : ℕ → Cfg Γ Λ σ := fun t => runG m alt bs c0 t with hrun
  refine ⟨assign2 d Ks S k₀ sb run, hU, ?_⟩
  have hst : c0.stk k₀ = xs.map sb ++ sep :: w.map sb := by simp [hc0, initCfg]
  have hst' : ∀ k, k ≠ k₀ → c0.stk k = [] := fun k hk => by simp [hc0, initCfg, hk]
  have hrun0 : run 0 = c0 := rfl
  have hrunS : ∀ t, run (t + 1) = relabC alt (bs t) (stepStay m (run t)) := fun t => rfl
  have a0 : assign2 d Ks S k₀ sb run 0 = Sum.inr (some ⟨k₀, sb false⟩) := by simp [assign2]
  have a1 : assign2 d Ks S k₀ sb run 1 = Sum.inr (some ⟨k₀, sb true⟩) := by simp [assign2]
  intro c hc
  simp only [tabNCS, csZ, csInit, csRow, csTransN, csTrans, List.tail_cons, csFinalH, csFinal,
    List.mem_append, List.mem_cons,
    List.mem_singleton, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_filter,
    List.not_mem_nil, or_false] at hc
  rcases hc with (((((rfl | rfl) | ((((((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) |
    ⟨j, hj, rfl⟩) | ⟨k, ⟨-, hk⟩, p, hp, rfl⟩))) | ⟨t, ht, k, -, (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)⟩) |
    ⟨t, ht, rfl | ⟨k, -, (⟨p, hp, rfl⟩ | ⟨j, hj, rfl⟩)⟩⟩) | rfl | rfl)
  · simp [cellRel1, a0]
  · simp [cellRel1, a1]
  · simp only [List.map_cons, List.map_nil, assign2_sv, ctlRel1, ctlOf, hrun0]
    simp [hc0, initCfg]
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show i < S by omega)]
    have hb : NthTM.bit xs i = if xs[i] then 1 else 0 := by
      simp [NthTM.bit, List.getElem?_eq_getElem hi]
    rw [hb]
    cases hx : xs[i]
    · simp only [if_neg (show ¬(false = true) by simp), a0, cellRel2, hrun0, cellOf, hst,
        List.getElem?_append_left (show i < (xs.map sb).length by simpa),
        List.getElem?_map, List.getElem?_eq_getElem hi, hx]
      simp [a0, a1]
    · simp only [if_pos rfl, a1, cellRel2, hrun0, cellOf, hst,
        List.getElem?_append_left (show i < (xs.map sb).length by simpa),
        List.getElem?_map, List.getElem?_eq_getElem hi, hx]
      simp [a0, a1]
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show xs.length < S by omega),
      cellRel1, hrun0, cellOf, hst, List.getElem?_append_right (show (xs.map sb).length ≤ xs.length
        by simp)]
    simp
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show xs.length + 1 + j < S by omega),
      assign2_cv run 0 (hKs k₀) (show xs.length + 2 + j < S by omega), cellRel2, hrun0, cellOf, hst,
      List.getElem?_append_right (show (xs.map sb).length ≤ xs.length + 1 + j by simp; omega),
      List.getElem?_append_right (show (xs.map sb).length ≤ xs.length + 2 + j by simp; omega),
      List.length_map, show xs.length + 1 + j - xs.length = j + 1 by omega,
      show xs.length + 2 + j - xs.length = j + 1 + 1 by omega, List.getElem?_cons_succ,
      decide_eq_true_eq]
    unfold witP
    constructor
    · rcases h : (w.map sb)[j]? with _ | g
      · simp
      · right
        simp only [List.getElem?_map] at h
        obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨b, rfl⟩
    · intro h
      simp only [Option.map_eq_none_iff, List.getElem?_eq_none_iff, List.length_map] at h ⊢
      omega
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show xs.length + 1 + Q + j < S by omega),
      cellRel1, hrun0, cellOf, hst, decide_eq_true_eq, Option.map_eq_none_iff, List.getElem?_eq_none_iff]
    simp; omega
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k) hp, cellRel1, hrun0, cellOf,
      hst' k (of_decide_eq_true hk)]
    simp
  · simp only [List.map_cons, List.map_nil, assign2_sv, assign2_cv run t (hKs k) (show i < S by omega),
      linkRel, win_link _ k hi]
    simp
  · simp only [List.map_cons, List.map_nil,
      assign2_cv run t (hKs k) (show S - (d + 1) + j < S by omega), cellRel1, cellOf,
      decide_eq_true_eq, Option.map_eq_none_iff, List.getElem?_eq_none_iff]
    exact le_trans (hlen t (by omega) k) (by omega)
  · simp only [List.map_cons, List.map_nil, assign2_sv, ctlRel2, decide_eq_true_eq,
      transCPN_iff m alt d hd]
    exact ⟨bs t, rfl, rfl⟩
  · simp only [List.map_cons, List.map_map, assign2_sv, assign2_cv run (t + 1) (hKs k)
      (show p < S by omega)]
    have eo : List.map (assign2 d Ks S k₀ sb run ∘ fun i => cv2 Ks S t k i) (List.range (p + d + 1)) =
        (List.range (p + d + 1)).map (fun i => Sum.inr (cellOf (run t) k (p - p + i))) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [Function.comp, Nat.sub_self, Nat.zero_add]
      exact assign2_cv run t (hKs k) (by omega)
    rw [eo]
    simp only [tcRel, decide_eq_true_eq]
    rw [tcP_iff m d P hd hP _ k p p p le_rfl (Or.inl ⟨rfl, rfl⟩)]; rfl
  · simp only [List.map_cons, List.map_map, assign2_sv, assign2_cv run (t + 1) (hKs k)
      (show d + P + j < S by omega)]
    have eo : List.map (assign2 d Ks S k₀ sb run ∘ fun i => cv2 Ks S t k (d + j + i))
        (List.range (P + d + 1)) =
        (List.range (P + d + 1)).map (fun i => Sum.inr (cellOf (run t) k (d + P + j - P + i))) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [Function.comp]
      rw [show d + P + j - P + i = d + j + i by omega]
      exact assign2_cv run t (hKs k) (by omega)
    rw [eo]
    simp only [tcRel, decide_eq_true_eq]
    rw [tcP_iff m d P hd hP _ k (d + P + j) P (d + P) (by omega) (Or.inr ⟨rfl, by omega, rfl⟩)]
    rfl
  · simp only [List.map_cons, List.map_nil, assign2_cv run T (hKs k₁) (show 0 < S by omega),
      cellRel1, decide_eq_true_eq]
    exact hacc
  · simp only [List.map_cons, List.map_nil, assign2_sv, ctlRel1, decide_eq_true_eq, ctlOf]
    exact hhalt

end TabN

end PvnpReal
