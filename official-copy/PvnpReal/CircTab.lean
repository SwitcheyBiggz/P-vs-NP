/-
  PvnpReal.CircTab — the `Tab2` run of a `FinTM2`, row by row, as a one-hot straight-line program:
  every cell of row `t+1` is a function of the control value and a window of row `t`
  (`tcP_iff`), every control value of row `t+1` of the previous control value and the top cells
  of row `t+1` (`transCP_iff`). Hence (`hasCircuit_tab`) any property of a cell of row `T` is
  computed by a circuit of size polynomial in `T` and the row width `S`.
-/
import PvnpReal.CircOneHot
import PvnpReal.CookLevin2

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

open scoped Classical

section CircTab

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-! ### Layout -/

def Wc (Ks : List K) (S : ℕ) : ℕ := Ks.length * S + 1
def ci (Ks : List K) (S t a p : ℕ) : ℕ := t * Wc Ks S + a * S + p
def cc (Ks : List K) (S t : ℕ) : ℕ := t * Wc Ks S + Ks.length * S

def rpOf (d P p : ℕ) : ℕ := if p < d + P then p else P
def pcOf (d P p : ℕ) : ℕ := if p < d + P then p else d + P
def cntOf (d P S p : ℕ) : ℕ := min (rpOf d P p + d + 1) (S - (p - rpOf d P p))

/-! ### Node functions -/

noncomputable def cellF (m : Λ → Stmt Γ Λ σ) (d : ℕ) (k : K) (rp pcap : ℕ) (R : Ctl Γ Λ σ)
    (olds : List (V2 Γ Λ σ)) : V2 Γ Λ σ :=
  if h : ∃ new, tcP m d k rp pcap R new olds then Sum.inr (Classical.choose h) else Sum.inr none

def cellOpt : V2 Γ Λ σ → Option (Sig Γ)
  | Sum.inr c => c
  | Sum.inl _ => none

def winOf (d : ℕ) (Ks : List K) (cells : List (V2 Γ Λ σ)) (k : K) : List (Sig Γ) :=
  (List.range d).filterMap (fun i => cellOpt (cells.getD (Ks.idxOf k * d + i) (Sum.inr none)))

def transLV (m : Λ → Stmt Γ Λ σ) (R : Ctl Γ Λ σ) : Option Λ × σ :=
  match R.l with
  | none => (R.l, R.var)
  | some lab => ((winRun m R lab).l, (winRun m R lab).var)

noncomputable def cellFn (m : Λ → Stmt Γ Λ σ) (d P S : ℕ) (Ks : List K) (a p : ℕ)
    (vs : List (V2 Γ Λ σ)) : V2 Γ Λ σ :=
  match vs, Ks[a]? with
  | Sum.inl R :: olds, some k => cellF m d k (rpOf d P p) (pcOf d P p) R
      (olds ++ List.replicate (rpOf d P p + d + 1 - cntOf d P S p) (Sum.inr none))
  | _, _ => Sum.inr none

def ctlFn (m : Λ → Stmt Γ Λ σ) (d : ℕ) (Ks : List K) (vs : List (V2 Γ Λ σ)) : V2 Γ Λ σ :=
  match vs with
  | Sum.inl R :: cells => Sum.inl ⟨(transLV m R).1, (transLV m R).2, winOf d Ks cells⟩
  | _ => Sum.inr none

def ctl0Fn (d : ℕ) (Ks : List K) (l0 : Option Λ) (v0 : σ) (vs : List (V2 Γ Λ σ)) : V2 Γ Λ σ :=
  Sum.inl ⟨l0, v0, winOf d Ks vs⟩

def cellDeps (d : ℕ) (Ks : List K) (S t : ℕ) : List ℕ :=
  (List.range Ks.length).flatMap (fun a => (List.range d).map (fun i => ci Ks S t a i))

noncomputable def cellNode (m : Λ → Stmt Γ Λ σ) (d P S : ℕ) (Ks : List K)
    (init0 : ℕ → ℕ → ANode (V2 Γ Λ σ)) : ℕ → ℕ → ℕ → ANode (V2 Γ Λ σ)
  | 0, a, p => init0 a p
  | t + 1, a, p => .fn (cc Ks S t :: (List.range (cntOf d P S p)).map
      (fun i => ci Ks S t a (p - rpOf d P p + i))) (cellFn m d P S Ks a p)

def ctlNode (m : Λ → Stmt Γ Λ σ) (d : ℕ) (Ks : List K) (S : ℕ) (l0 : Option Λ) (v0 : σ) :
    ℕ → ANode (V2 Γ Λ σ)
  | 0 => .fn (cellDeps d Ks S 0) (ctl0Fn d Ks l0 v0)
  | t + 1 => .fn (cc Ks S t :: cellDeps d Ks S (t + 1)) (ctlFn m d Ks)

noncomputable def tabNode (m : Λ → Stmt Γ Λ σ) (d P S : ℕ) (Ks : List K)
    (init0 : ℕ → ℕ → ANode (V2 Γ Λ σ)) (l0 : Option Λ) (v0 : σ) (j : ℕ) : ANode (V2 Γ Λ σ) :=
  if j % Wc Ks S < Ks.length * S then
    cellNode m d P S Ks init0 (j / Wc Ks S) (j % Wc Ks S / S) (j % Wc Ks S % S)
  else ctlNode m d Ks S l0 v0 (j / Wc Ks S)

/-- Intended values: the cells and controls of the run. -/
def tabVal (d S : ℕ) (Ks : List K) (run : ℕ → Cfg Γ Λ σ) (j : ℕ) : V2 Γ Λ σ :=
  if j % Wc Ks S < Ks.length * S then
    match Ks[j % Wc Ks S / S]? with
    | some k => Sum.inr (cellOf (run (j / Wc Ks S)) k (j % Wc Ks S % S))
    | none => Sum.inr none
  else Sum.inl (ctlOf d (run (j / Wc Ks S)))

/-! ### Index arithmetic -/

theorem ci_dec (Ks : List K) (S t a p : ℕ) (ha : a < Ks.length) (hp : p < S) :
    ci Ks S t a p / Wc Ks S = t ∧ ci Ks S t a p % Wc Ks S = a * S + p ∧
      a * S + p < Ks.length * S ∧ (a * S + p) / S = a ∧ (a * S + p) % S = p := by
  have h1 : a * S + p < Ks.length * S := by
    have : (a + 1) * S ≤ Ks.length * S := Nat.mul_le_mul_right _ ha
    simp only [Nat.add_mul, Nat.one_mul] at this; omega
  have hW : a * S + p < Wc Ks S := by unfold Wc; omega
  have hS : 0 < S := by omega
  unfold ci
  refine ⟨?_, ?_, h1, ?_, ?_⟩
  · rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_div (by unfold Wc; omega), Nat.div_eq_of_lt hW,
      Nat.add_zero]
  · rw [Nat.add_assoc, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hW]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hp, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]

theorem cc_dec (Ks : List K) (S t : ℕ) :
    cc Ks S t / Wc Ks S = t ∧ cc Ks S t % Wc Ks S = Ks.length * S := by
  have hW : Ks.length * S < Wc Ks S := by unfold Wc; omega
  unfold cc
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div (by unfold Wc; omega), Nat.div_eq_of_lt hW, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hW]

theorem ci_lt_cc (Ks : List K) (S t a p : ℕ) (ha : a < Ks.length) (hp : p < S) :
    ci Ks S t a p < cc Ks S t := by
  have := (ci_dec Ks S t a p ha hp).2.2.1
  unfold ci cc; omega

theorem cc_lt_ci (Ks : List K) (S t a p : ℕ) : cc Ks S t < ci Ks S (t + 1) a p := by
  unfold cc ci Wc; rw [Nat.add_mul]; omega

theorem ci_mono (Ks : List K) (S t a p a' p' : ℕ) (ha : a < Ks.length) (hp : p < S) :
    ci Ks S t a p < ci Ks S (t + 1) a' p' :=
  (ci_lt_cc Ks S t a p ha hp).trans_le (Nat.le_of_lt (cc_lt_ci Ks S t a' p'))

theorem ci_lt_N (Ks : List K) (S t a p T : ℕ) (ht : t ≤ T) (ha : a < Ks.length) (hp : p < S) :
    ci Ks S t a p < (T + 1) * Wc Ks S := by
  have := ci_lt_cc Ks S t a p ha hp
  have : cc Ks S t < (t + 1) * Wc Ks S := by unfold cc Wc; rw [Nat.add_mul]; omega
  have : (t + 1) * Wc Ks S ≤ (T + 1) * Wc Ks S := Nat.mul_le_mul_right _ (by omega)
  omega

theorem cc_lt_N (Ks : List K) (S t T : ℕ) (ht : t ≤ T) : cc Ks S t < (T + 1) * Wc Ks S := by
  have : cc Ks S t < (t + 1) * Wc Ks S := by unfold cc Wc; rw [Nat.add_mul]; omega
  have : (t + 1) * Wc Ks S ≤ (T + 1) * Wc Ks S := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Every index below `N` is a cell index or a control index. -/
theorem idx_cases (Ks : List K) (S T j : ℕ) (hj : j < (T + 1) * Wc Ks S) :
    (∃ t a p, t ≤ T ∧ a < Ks.length ∧ p < S ∧ j = ci Ks S t a p) ∨ (∃ t, t ≤ T ∧ j = cc Ks S t) := by
  have hW : 0 < Wc Ks S := by unfold Wc; omega
  have ht : j / Wc Ks S ≤ T := by
    have := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hj); omega
  have hr : j % Wc Ks S < Wc Ks S := Nat.mod_lt _ hW
  have hjd : j = j / Wc Ks S * Wc Ks S + j % Wc Ks S := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod j _).symm
  by_cases hc : j % Wc Ks S < Ks.length * S
  · left
    have hS : 0 < S := by
      rcases Nat.eq_zero_or_pos S with h | h
      · simp [h] at hc
      · exact h
    refine ⟨j / Wc Ks S, j % Wc Ks S / S, j % Wc Ks S % S, ht,
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]), Nat.mod_lt _ hS, ?_⟩
    unfold ci
    have := Nat.div_add_mod (j % Wc Ks S) S
    rw [Nat.mul_comm S] at this
    omega
  · right
    refine ⟨j / Wc Ks S, ht, ?_⟩
    unfold cc
    unfold Wc at hr hc hjd ⊢; omega

/-! ### List lemmas -/

theorem filterMap_range_getElem? {β γ : Type*} (l : List β) (g : β → γ) :
    ∀ d, (List.range d).filterMap (fun i => l[i]?.map g) = (l.take d).map g
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.filterMap_append, filterMap_range_getElem? l g d, List.take_succ,
      List.map_append]
    rcases h : l[d]? with _ | b <;> simp [h]

theorem getD_blocks {β : Type*} (z : β) (D : ℕ) (g : ℕ → ℕ → β) :
    ∀ A a i, a < A → i < D →
      ((List.range A).flatMap (fun a => (List.range D).map (g a))).getD (a * D + i) z = g a i
  | 0, a, i, ha, _ => by omega
  | A + 1, a, i, ha, hi => by
    have hl : ((List.range A).flatMap (fun a => (List.range D).map (g a))).length = A * D := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases haA : a < A
    · have : a * D + i < A * D := by
        have : (a + 1) * D ≤ A * D := Nat.mul_le_mul_right _ haA
        simp only [Nat.add_mul, Nat.one_mul] at this; omega
      rw [List.getD_append _ _ _ _ (by rw [hl]; exact this)]
      exact getD_blocks z D g A a i haA hi
    · have hae : a = A := by omega
      subst hae
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
      simp [List.getD_eq_getElem?_getD, hi]

theorem transCP_transLV (m : Λ → Stmt Γ Λ σ) (R : Ctl Γ Λ σ) (w : K → List (Sig Γ)) :
    transCP m R ⟨(transLV m R).1, (transLV m R).2, w⟩ := by
  unfold transCP transLV
  split <;> simp_all

theorem cellOf_ge (c : Cfg Γ Λ σ) (k : K) {q : ℕ} (hq : (c.stk k).length ≤ q) :
    cellOf c k q = none := by
  simp [cellOf, List.getElem?_eq_none hq]

/-! ### Values -/

theorem tabVal_ci (d S : ℕ) (Ks : List K) (run : ℕ → Cfg Γ Λ σ) (t a p : ℕ) (ha : a < Ks.length)
    (hp : p < S) : tabVal d S Ks run (ci Ks S t a p) = Sum.inr (cellOf (run t) Ks[a] p) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ci_dec Ks S t a p ha hp
  unfold tabVal
  rw [h2, if_pos h3, h4, h5, h1, List.getElem?_eq_getElem ha]

theorem tabVal_cc (d S : ℕ) (Ks : List K) (run : ℕ → Cfg Γ Λ σ) (t : ℕ) :
    tabVal d S Ks run (cc Ks S t) = Sum.inl (ctlOf d (run t)) := by
  obtain ⟨h1, h2⟩ := cc_dec Ks S t
  unfold tabVal
  rw [h2, if_neg (lt_irrefl _), h1]

theorem tabNode_ci (m : Λ → Stmt Γ Λ σ) (d P S : ℕ) (Ks : List K) init0 l0 v0 (t a p : ℕ)
    (ha : a < Ks.length) (hp : p < S) :
    tabNode m d P S Ks init0 l0 v0 (ci Ks S t a p) = cellNode m d P S Ks init0 t a p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ci_dec Ks S t a p ha hp
  unfold tabNode
  rw [h2, if_pos h3, h4, h5, h1]

theorem tabNode_cc (m : Λ → Stmt Γ Λ σ) (d P S : ℕ) (Ks : List K) init0 l0 v0 (t : ℕ) :
    tabNode m d P S Ks init0 l0 v0 (cc Ks S t) = ctlNode m d Ks S l0 v0 t := by
  obtain ⟨h1, h2⟩ := cc_dec Ks S t
  unfold tabNode
  rw [h2, if_neg (lt_irrefl _), h1]

theorem cellF_eq (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (hd : ∀ lab, sdepth (m lab) ≤ d)
    (hP : ∀ lab, pushes (m lab) ≤ P) (c : Cfg Γ Λ σ) (k : K) (p rp pcap : ℕ) (hrp : rp ≤ p)
    (hcase : (pcap = p ∧ rp = p) ∨ (pcap = d + P ∧ d + P ≤ p ∧ rp = P)) :
    cellF m d k rp pcap (ctlOf d c)
      ((List.range (rp + d + 1)).map (fun i => Sum.inr (cellOf c k (p - rp + i)))) =
      Sum.inr (cellOf (stepStay m c) k p) := by
  have hiff := tcP_iff (m := m) (d := d) (P := P) hd hP c k p rp pcap hrp hcase
  have hex : ∃ new, tcP m d k rp pcap (ctlOf d c) new
      ((List.range (rp + d + 1)).map (fun i => Sum.inr (cellOf c k (p - rp + i)))) :=
    ⟨_, (hiff _).2 rfl⟩
  unfold cellF
  rw [dif_pos hex, (hiff _).1 (Classical.choose_spec hex)]

theorem map_cellDeps (d : ℕ) (Ks : List K) (S t : ℕ) {β : Type*} (f : ℕ → β) :
    (cellDeps d Ks S t).map f =
      (List.range Ks.length).flatMap (fun a => (List.range d).map (fun i => f (ci Ks S t a i))) := by
  simp [cellDeps, List.map_flatMap, Function.comp_def]

theorem winOf_run (d S : ℕ) (Ks : List K) (hKs : ∀ k, k ∈ Ks) (hdS : d ≤ S) (run : ℕ → Cfg Γ Λ σ)
    (t : ℕ) (k : K) :
    winOf d Ks ((cellDeps d Ks S t).map (tabVal d S Ks run)) k = toSig k (((run t).stk k).take d) := by
  rw [map_cellDeps]
  unfold winOf
  have hk := List.idxOf_lt_length_of_mem (hKs k)
  rw [List.filterMap_congr (g := fun i => ((run t).stk k)[i]?.map (fun g => (⟨k, g⟩ : Sig Γ))),
    filterMap_range_getElem?]
  · rfl
  · intro i hi
    rw [List.mem_range] at hi
    rw [getD_blocks (Sum.inr none) d (fun a i => tabVal d S Ks run (ci Ks S t a i)) Ks.length
      (Ks.idxOf k) i hk hi]
    rw [tabVal_ci d S Ks run t _ i hk (by omega), List.getElem_idxOf]
    rfl

theorem cellStep_val (m : Λ → Stmt Γ Λ σ) (d P S : ℕ) (Ks : List K) (hd : ∀ lab, sdepth (m lab) ≤ d)
    (hP : ∀ lab, pushes (m lab) ≤ P) (run : ℕ → Cfg Γ Λ σ)
    (hrun : ∀ t, run (t + 1) = stepStay m (run t)) (t : ℕ)
    (hlen : ∀ k, ((run t).stk k).length ≤ S) (a p : ℕ) (ha : a < Ks.length) (hp : p < S) :
    cellFn m d P S Ks a p ((cc Ks S t :: (List.range (cntOf d P S p)).map
      (fun i => ci Ks S t a (p - rpOf d P p + i))).map (tabVal d S Ks run)) =
      tabVal d S Ks run (ci Ks S (t + 1) a p) := by
  set rp := rpOf d P p with hrpd
  set cnt := cntOf d P S p with hcnt
  have hrp : rp ≤ p := by rw [hrpd, rpOf]; split_ifs <;> omega
  have hcase : (pcOf d P p = p ∧ rp = p) ∨ (pcOf d P p = d + P ∧ d + P ≤ p ∧ rp = P) := by
    rw [hrpd, rpOf, pcOf]; split_ifs with h
    · left; simp
    · right; simp; omega
  have hcntle : cnt ≤ rp + d + 1 ∧ cnt ≤ S - (p - rp) := by
    rw [hcnt, cntOf, ← hrpd]; omega
  have hmin : cnt = min (rp + d + 1) (S - (p - rp)) := by rw [hcnt, cntOf, ← hrpd]
  rw [tabVal_ci d S Ks run (t + 1) a p ha hp, hrun t]
  simp only [List.map_cons, List.map_map]
  rw [tabVal_cc]
  have holds : (List.range cnt).map ((tabVal d S Ks run) ∘ (fun i => ci Ks S t a (p - rp + i))) ++
      List.replicate (rp + d + 1 - cnt) (Sum.inr none) =
      (List.range (rp + d + 1)).map (fun i => Sum.inr (cellOf (run t) Ks[a] (p - rp + i))) := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.length_append, List.length_map, List.length_range, List.length_replicate] at h1
    by_cases hi : i < cnt
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_range, Function.comp]
      rw [tabVal_ci d S Ks run t a _ ha (by omega)]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp only [List.getElem_replicate, List.getElem_map, List.getElem_range]
      rw [cellOf_ge _ _ (by have := hlen Ks[a]; omega)]
  unfold cellFn
  rw [List.getElem?_eq_getElem ha]
  simp only
  rw [holds, cellF_eq m d P hd hP (run t) Ks[a] p rp (pcOf d P p) hrp hcase]

theorem ctlStep_val (m : Λ → Stmt Γ Λ σ) (d S : ℕ) (Ks : List K) (hd : ∀ lab, sdepth (m lab) ≤ d)
    (hKs : ∀ k, k ∈ Ks) (hdS : d ≤ S) (run : ℕ → Cfg Γ Λ σ)
    (hrun : ∀ t, run (t + 1) = stepStay m (run t)) (t : ℕ) :
    ctlFn m d Ks ((cc Ks S t :: cellDeps d Ks S (t + 1)).map (tabVal d S Ks run)) =
      tabVal d S Ks run (cc Ks S (t + 1)) := by
  rw [List.map_cons, tabVal_cc, tabVal_cc]
  unfold ctlFn
  simp only
  have h := (transCP_iff (m := m) (d := d) hd (run t) _).1
    (transCP_transLV m (ctlOf d (run t)) (winOf d Ks ((cellDeps d Ks S (t + 1)).map (tabVal d S Ks run))))
  simp only at h
  rw [← hrun] at h
  congr 1
  rw [ctlOf]
  congr 1
  · exact h.1
  · exact h.2
  · funext k; exact winOf_run d S Ks hKs hdS run (t + 1) k

theorem ctl0_val (d S : ℕ) (Ks : List K) (hKs : ∀ k, k ∈ Ks) (hdS : d ≤ S) (run : ℕ → Cfg Γ Λ σ)
    (l0 : Option Λ) (v0 : σ) (hl0 : (run 0).l = l0) (hv0 : (run 0).var = v0) :
    ctl0Fn d Ks l0 v0 ((cellDeps d Ks S 0).map (tabVal d S Ks run)) = tabVal d S Ks run (cc Ks S 0) := by
  rw [tabVal_cc]
  unfold ctl0Fn
  rw [ctlOf, hl0, hv0]
  congr 2
  funext k; exact winOf_run d S Ks hKs hdS run 0 k

/-! ### The tableau circuit -/

/-- **Runs of a `FinTM2` are computed by polynomial-size circuits.** For a family of runs
`run x` (input `x : Fin n → Bool`) whose row-0 cells are constants or single input bits, every
property of a cell of row `T` has a circuit with at most
`2 + ((T+1)·(|Ks|·S+1)·|U| + 1) · 4 · 2^(c·|U|)` gates, where `U = tab2Values d L` and
`c = 2d + P + 2 + |Ks|·d` depend only on the machine. -/
theorem hasCircuit_tab [Fintype K] [Fintype Λ] [Fintype σ]
    (m : Λ → Stmt Γ Λ σ) (d P S T n : ℕ) (Ks : List K)
    (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (hdS : d ≤ S) (L : List (Sig Γ))
    (init0 : ℕ → ℕ → ANode (V2 Γ Λ σ)) (l0 : Option Λ) (v0 : σ)
    (run : (Fin n → Bool) → ℕ → Cfg Γ Λ σ)
    (hrun : ∀ x t, run x (t + 1) = stepStay m (run x t))
    (hlen : ∀ x, ∀ t ≤ T, ∀ k, ((run x t).stk k).length ≤ S)
    (hsyms : ∀ x t, SymsIn L (run x t).stk)
    (hl0 : ∀ x, (run x 0).l = l0) (hv0 : ∀ x, (run x 0).var = v0)
    (hinit : ∀ a (ha : a < Ks.length), ∀ p < S,
      (∃ i f, i < n ∧ init0 a p = .inp i f ∧
        ∀ x, Sum.inr (cellOf (run x 0) Ks[a] p) = f ((List.ofFn x).getD i false)) ∨
      (∃ F, init0 a p = .fn [] F ∧ ∀ x, Sum.inr (cellOf (run x 0) Ks[a] p) = F []))
    (kout : K) (pout : ℕ) (hpout : pout < S) (Pr : Option (Sig Γ) → Prop) :
    HasCircuit n (2 + ((T + 1) * Wc Ks S * (tab2Values (Λ := Λ) (σ := σ) d L).length + 1) *
        (4 * 2 ^ ((2 * d + P + 2 + Ks.length * d) * (tab2Values (Λ := Λ) (σ := σ) d L).length)))
      (fun x => decide (Pr (cellOf (run x T) kout pout))) := by
  set U := tab2Values (Λ := Λ) (σ := σ) d L with hUd
  set N := (T + 1) * Wc Ks S with hN
  set as := (List.range N).map (tabNode m d P S Ks init0 l0 v0) with has
  have hasl : as.length = N := by simp [has]
  have hget : ∀ j (hj : j < as.length), as[j] = tabNode m d P S Ks init0 l0 v0 j := by
    intro j hj; simp [has]
  set c := 2 * d + P + 2 + Ks.length * d with hc
  have hcdl : ∀ t, (cellDeps d Ks S t).length = Ks.length * d := by
    intro t; simp [cellDeps, List.length_flatMap, List.sum_replicate]
  have hcdlt : ∀ t, ∀ v ∈ cellDeps d Ks S t, v < cc Ks S t := by
    intro t v hv
    simp only [cellDeps, List.mem_flatMap, List.mem_map, List.mem_range] at hv
    obtain ⟨a, ha, i, hi, rfl⟩ := hv
    exact ci_lt_cc Ks S t a i ha (by omega)
  have hccs : ∀ t, cc Ks S t < cc Ks S (t + 1) := by intro t; unfold cc Wc; rw [Nat.add_mul]; omega
  have hrpp : ∀ p, rpOf d P p ≤ p ∧ rpOf d P p + d + 1 ≤ 2 * d + P + 1 := by
    intro p; unfold rpOf; split_ifs <;> omega
  have hinp : ∀ j (hj : j < as.length) i f, as[j] = .inp i f → i < n := by
    intro j hj i f h
    rw [hget] at h; rw [hasl] at hj
    rcases idx_cases Ks S T j hj with ⟨t, a, p, ht, ha, hp, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [tabNode_ci _ _ _ _ _ _ _ _ _ _ _ ha hp] at h
      cases t with
      | zero =>
        simp only [cellNode] at h
        rcases hinit a ha p hp with ⟨i', f', hi', he, -⟩ | ⟨F, he, -⟩
        · rw [he, ANode.inp.injEq] at h; rw [← h.1]; exact hi'
        · rw [he] at h; cases h
      | succ t => simp [cellNode] at h
    · rw [tabNode_cc] at h; cases t <;> simp [ctlNode] at h
  have hfn : ∀ j (hj : j < as.length) ds F, as[j] = .fn ds F → (∀ e ∈ ds, e < j) ∧ ds.length ≤ c := by
    intro j hj ds F h
    rw [hget] at h; rw [hasl] at hj
    rcases idx_cases Ks S T j hj with ⟨t, a, p, ht, ha, hp, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [tabNode_ci _ _ _ _ _ _ _ _ _ _ _ ha hp] at h
      cases t with
      | zero =>
        simp only [cellNode] at h
        rcases hinit a ha p hp with ⟨i', f', -, he, -⟩ | ⟨F', he, -⟩
        · rw [he] at h; cases h
        · rw [he, ANode.fn.injEq] at h; rw [← h.1]; simp
      | succ t =>
        simp only [cellNode, ANode.fn.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hcnt : cntOf d P S p ≤ rpOf d P p + d + 1 ∧ cntOf d P S p ≤ S - (p - rpOf d P p) := by
          unfold cntOf; omega
        have := hrpp p
        refine ⟨?_, by simp; omega⟩
        intro e he
        simp only [List.mem_cons, List.mem_map, List.mem_range] at he
        rcases he with rfl | ⟨i, hi, rfl⟩
        · exact cc_lt_ci Ks S t a p
        · exact ci_mono Ks S t a _ a p ha (by omega)
    · rw [tabNode_cc] at h
      cases t with
      | zero =>
        simp only [ctlNode, ANode.fn.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hcdlt 0, by rw [hcdl]; omega⟩
      | succ t =>
        simp only [ctlNode, ANode.fn.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨?_, by simp [hcdl]; omega⟩
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hccs t
        · exact hcdlt _ e he
  have hU : ∀ x, ∀ j < as.length, tabVal d S Ks (run x) j ∈ U := by
    intro x j hj
    rw [hasl] at hj
    rcases idx_cases Ks S T j hj with ⟨t, a, p, ht, ha, hp, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [tabVal_ci d S Ks _ t a p ha hp]
      exact tab2Values_cell d L _ (hsyms x t) _ _
    · rw [tabVal_cc]
      exact tab2Values_ctl d L _ (hsyms x t)
  have hvi : ∀ x j (hj : j < as.length) i f, as[j] = .inp i f →
      tabVal d S Ks (run x) j = f ((List.ofFn x).getD i false) := by
    intro x j hj i f h
    rw [hget] at h; rw [hasl] at hj
    rcases idx_cases Ks S T j hj with ⟨t, a, p, ht, ha, hp, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [tabNode_ci _ _ _ _ _ _ _ _ _ _ _ ha hp] at h
      cases t with
      | zero =>
        simp only [cellNode] at h
        rcases hinit a ha p hp with ⟨i', f', -, he, hv⟩ | ⟨F, he, -⟩
        · rw [he, ANode.inp.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [tabVal_ci d S Ks _ 0 a p ha hp, hv x]
        · rw [he] at h; cases h
      | succ t => simp [cellNode] at h
    · rw [tabNode_cc] at h; cases t <;> simp [ctlNode] at h
  have hvf : ∀ x j (hj : j < as.length) ds F, as[j] = .fn ds F →
      tabVal d S Ks (run x) j = F (ds.map (tabVal d S Ks (run x))) := by
    intro x j hj ds F h
    rw [hget] at h; rw [hasl] at hj
    rcases idx_cases Ks S T j hj with ⟨t, a, p, ht, ha, hp, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [tabNode_ci _ _ _ _ _ _ _ _ _ _ _ ha hp] at h
      cases t with
      | zero =>
        simp only [cellNode] at h
        rcases hinit a ha p hp with ⟨i', f', -, he, -⟩ | ⟨F', he, hv⟩
        · rw [he] at h; cases h
        · rw [he, ANode.fn.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [tabVal_ci d S Ks _ 0 a p ha hp, hv x, List.map_nil]
      | succ t =>
        simp only [cellNode, ANode.fn.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (cellStep_val m d P S Ks hd hP (run x) (hrun x) t (hlen x t (by omega)) a p ha hp).symm
    · rw [tabNode_cc] at h
      cases t with
      | zero =>
        simp only [ctlNode, ANode.fn.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (ctl0_val d S Ks hKs hdS (run x) l0 v0 (hl0 x) (hv0 x)).symm
      | succ t =>
        simp only [ctlNode, ANode.fn.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (ctlStep_val m d S Ks hd hKs hdS (run x) (hrun x) t).symm
  have hk := List.idxOf_lt_length_of_mem (hKs kout)
  have ho : ci Ks S T (Ks.idxOf kout) pout < as.length := by
    rw [hasl]; exact ci_lt_N Ks S T _ pout T le_rfl hk hpout
  have hC := hasCircuit_aprog U (Sum.inr none) n c as (by omega) hinp hfn
    (fun x => tabVal d S Ks (run x)) hU hvi hvf _ ho (fun v => Pr (cellOpt v))
  rw [hasl] at hC
  have hf : (fun x => decide (Pr (cellOpt (tabVal d S Ks (run x) (ci Ks S T (Ks.idxOf kout) pout))))) =
      (fun x => decide (Pr (cellOf (run x T) kout pout))) := by
    funext x
    rw [tabVal_ci d S Ks _ T _ pout hk hpout, List.getElem_idxOf]
    rfl
  rw [hf] at hC
  exact hC

end CircTab

end PvnpReal
