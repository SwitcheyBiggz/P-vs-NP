/-
  PvnpReal.Tableau — the Cook–Levin tableau for a TM2 machine, stated as a finite-domain CSP
  (`PvnpReal.CSP`) with constraints of arity ≤ 3.

  Row `t` of the tableau holds
  * a *summary* variable: label, state, the length of each stack, and the top `d` cells of each
    stack (the window);
  * cell variables `(t, k, i)` for `i < S`: cell `i` of stack `k`, counted from the BOTTOM.
  Counting from the bottom makes a step local: cells below the window never move.
  `stepAux_window` (in `Locality.lean`) says the step depends only on the windows.
-/
import PvnpReal.Locality
import PvnpReal.CSP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2

open scoped Classical

section Tab

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Stack symbols tagged with their stack. -/
abbrev Sig (Γ : K → Type) := Σ k, Γ k

def toSig (k : K) (l : List (Γ k)) : List (Sig Γ) := l.map (fun g => ⟨k, g⟩)

def sig1 (k : K) (p : Sig Γ) : Option (Γ k) := if h : p.1 = k then some (h ▸ p.2) else none

def ofSig (k : K) (l : List (Sig Γ)) : List (Γ k) := l.filterMap (sig1 k)

theorem sig1_mk (k : K) (g : Γ k) : sig1 k (⟨k, g⟩ : Sig Γ) = some g := by simp [sig1]

theorem ofSig_toSig (k : K) (l : List (Γ k)) : ofSig k (toSig k l) = l := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [ofSig, toSig, sig1_mk] at ih ⊢; try exact ih

/-- The summary of a tableau row. -/
structure Summ (Γ : K → Type) (Λ σ : Type) where
  l : Option Λ
  var : σ
  len : K → ℕ
  win : K → List (Sig Γ)

/-- Values of tableau variables. -/
abbrev TVal (Γ : K → Type) (Λ σ : Type) := Summ Γ Λ σ ⊕ Sig Γ

variable (m : Λ → Stmt Γ Λ σ) (d : ℕ)

def summOf (c : Cfg Γ Λ σ) : Summ Γ Λ σ :=
  ⟨c.l, c.var, fun k => (c.stk k).length, fun k => toSig k ((c.stk k).take d)⟩

/-- Step, staying put once halted. -/
def stepStay (c : Cfg Γ Λ σ) : Cfg Γ Λ σ := (TM2.step m c).getD c

/-- The step computed from a summary's windows. -/
def winStep (s : Summ Γ Λ σ) (lab : Λ) : Cfg Γ Λ σ :=
  stepAux (m lab) s.var (fun k => ofSig k (s.win k))

/-! ### Relations -/

def rowSummP (S : ℕ) (s : Summ Γ Λ σ) : Prop :=
  ∀ k, s.len k ≤ S ∧ (s.win k).length = min (s.len k) d

def linkP (k : K) (i : ℕ) (s : Summ Γ Λ σ) (x : TVal Γ Λ σ) : Prop :=
  i < s.len k → ∃ g : Γ k, x = Sum.inr ⟨k, g⟩ ∧
    (s.len k - 1 - i < d → (s.win k)[s.len k - 1 - i]? = some ⟨k, g⟩)

def transSummP (s s' : Summ Γ Λ σ) : Prop :=
  match s.l with
  | none => s' = s
  | some lab => s'.l = (winStep m s lab).l ∧ s'.var = (winStep m s lab).var ∧
      ∀ k, s'.len k = (s.len k - d) + ((winStep m s lab).stk k).length

def transCellP (k : K) (i : ℕ) (s : Summ Γ Λ σ) (x x' : TVal Γ Λ σ) : Prop :=
  match s.l with
  | none => i < s.len k → x' = x
  | some lab => (i < s.len k - d → x' = x) ∧
      (∀ g, ((winStep m s lab).stk k).reverse[i - (s.len k - d)]? = some g →
        s.len k - d ≤ i → x' = Sum.inr ⟨k, g⟩)

/-- Initial row: label `main`, state `v₀`, only stack `k₀` non-empty, holding `pre ++ ws`
with `|ws| ≤ Q` and every symbol of `ws` allowed. -/
def initSummP (main : Λ) (v₀ : σ) (k₀ : K) (pre : List (Γ k₀)) (Q : ℕ) (s : Summ Γ Λ σ) : Prop :=
  s.l = some main ∧ s.var = v₀ ∧ (∀ k, k ≠ k₀ → s.len k = 0) ∧
    pre.length ≤ s.len k₀ ∧ s.len k₀ ≤ pre.length + Q

def initCellP (k₀ : K) (pre : List (Γ k₀)) (allowed : Γ k₀ → Prop) (i : ℕ) (s : Summ Γ Λ σ)
    (x : TVal Γ Λ σ) : Prop :=
  (i < s.len k₀ - pre.length → ∃ g, allowed g ∧ x = Sum.inr ⟨k₀, g⟩) ∧
  (∀ g, pre.reverse[i - (s.len k₀ - pre.length)]? = some g → s.len k₀ - pre.length ≤ i →
      x = Sum.inr ⟨k₀, g⟩)

def finalCellP (cacc : Cfg Γ Λ σ) (k : K) (i : ℕ) (x : TVal Γ Λ σ) : Prop :=
  ∀ g, (cacc.stk k).reverse[i]? = some g → x = Sum.inr ⟨k, g⟩

/-! ### Relations on value lists (for the CSP) -/

noncomputable def rel1 (P : Summ Γ Λ σ → Prop) : List (TVal Γ Λ σ) → Bool
  | [Sum.inl s] => decide (P s)
  | _ => false

noncomputable def rel2 (P : Summ Γ Λ σ → TVal Γ Λ σ → Prop) : List (TVal Γ Λ σ) → Bool
  | [Sum.inl s, x] => decide (P s x)
  | _ => false

noncomputable def rel2s (P : Summ Γ Λ σ → Summ Γ Λ σ → Prop) : List (TVal Γ Λ σ) → Bool
  | [Sum.inl s, Sum.inl s'] => decide (P s s')
  | _ => false

noncomputable def rel3 (P : Summ Γ Λ σ → TVal Γ Λ σ → TVal Γ Λ σ → Prop) :
    List (TVal Γ Λ σ) → Bool
  | [Sum.inl s, x, x'] => decide (P s x x')
  | _ => false

noncomputable def relC (P : TVal Γ Λ σ → Prop) : List (TVal Γ Λ σ) → Bool
  | [x] => decide (P x)
  | _ => false

/-! ### Variable layout -/

variable (Ks : List K) (S : ℕ)

def rowW : ℕ := 1 + Ks.length * S
def sv (t : ℕ) : ℕ := t * rowW Ks S
def cv (t : ℕ) (k : K) (i : ℕ) : ℕ := t * rowW Ks S + 1 + Ks.idxOf k * S + i

variable (main : Λ) (v₀ : σ) (k₀ : K) (pre : List (Γ k₀)) (allowed : Γ k₀ → Prop) (Q T : ℕ)
  (cacc : Cfg Γ Λ σ)

/-- All tableau constraints. -/
noncomputable def tabCS : List (Constraint (TVal Γ Λ σ)) :=
  [⟨[sv Ks S 0], rel1 (initSummP main v₀ k₀ pre Q)⟩] ++
  (List.range S).map (fun i =>
    ⟨[sv Ks S 0, cv Ks S 0 k₀ i], rel2 (initCellP k₀ pre allowed i)⟩) ++
  (List.range (T + 1)).flatMap (fun t =>
    ⟨[sv Ks S t], rel1 (rowSummP d S)⟩ ::
    Ks.flatMap (fun k => (List.range S).map (fun i =>
      ⟨[sv Ks S t, cv Ks S t k i], rel2 (linkP d k i)⟩))) ++
  (List.range T).flatMap (fun t =>
    ⟨[sv Ks S t, sv Ks S (t + 1)], rel2s (transSummP m d)⟩ ::
    Ks.flatMap (fun k => (List.range S).map (fun i =>
      ⟨[sv Ks S t, cv Ks S t k i, cv Ks S (t + 1) k i], rel3 (transCellP m d k i)⟩))) ++
  [⟨[sv Ks S T], rel1 (fun s => s = summOf d cacc)⟩] ++
  Ks.flatMap (fun k => (List.range S).map (fun i =>
    ⟨[cv Ks S T k i], relC (finalCellP cacc k i)⟩))


/-! ### Soundness: a solution of the CSP describes a real run -/

/-- Row `t` of the assignment `a` represents configuration `c`. -/
def Rep (a : ℕ → TVal Γ Λ σ) (t : ℕ) (c : Cfg Γ Λ σ) : Prop :=
  a (sv Ks S t) = Sum.inl (summOf d c) ∧
    ∀ k i g, (c.stk k).reverse[i]? = some g → a (cv Ks S t k i) = Sum.inr ⟨k, g⟩

theorem sig_eq {k : K} {g g' : Γ k} (h : (⟨k, g⟩ : Sig Γ) = ⟨k, g'⟩) : g = g' := by
  rw [Sigma.mk.inj_iff] at h; exact eq_of_heq h.2

theorem inr_sig_eq {k : K} {g g' : Γ k} (h : (Sum.inr ⟨k, g⟩ : TVal Γ Λ σ) = Sum.inr ⟨k, g'⟩) :
    g = g' := sig_eq (Sum.inr.inj h)

theorem rev_get {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l.reverse[l.length - 1 - j]? = l[j]? := by
  rw [List.getElem?_reverse (by omega)]; congr 1; omega

/-- A row whose summary and cells are consistent represents the configuration read off it. -/
theorem rep_of (a : ℕ → TVal Γ Λ σ) (t : ℕ) (s : Summ Γ Λ σ) (c : Cfg Γ Λ σ)
    (hKs : ∀ k, k ∈ Ks) (hs : a (sv Ks S t) = Sum.inl s) (hrow : rowSummP d S s)
    (hlink : ∀ k, ∀ i < S, linkP d k i s (a (cv Ks S t k i)))
    (hl : c.l = s.l) (hv : c.var = s.var) (hlen : ∀ k, (c.stk k).length = s.len k)
    (hcell : ∀ k i g, (c.stk k).reverse[i]? = some g → a (cv Ks S t k i) = Sum.inr ⟨k, g⟩) :
    Rep d Ks S a t c := by
  refine ⟨?_, hcell⟩
  rw [hs]
  congr 1
  obtain ⟨sl, sv', slen, swin⟩ := s
  simp only [summOf] at hl hv hlen ⊢
  subst hl hv
  have hlen' : slen = fun k => (c.stk k).length := funext fun k => (hlen k).symm
  subst hlen'
  congr 1
  funext k
  apply List.ext_getElem?
  intro j
  obtain ⟨hLS, hwl⟩ := hrow k
  simp only at hLS hwl
  by_cases hj : j < min (c.stk k).length d
  · have hjL : j < (c.stk k).length := lt_of_lt_of_le hj (min_le_left _ _)
    have hjd : j < d := lt_of_lt_of_le hj (min_le_right _ _)
    obtain ⟨g, hx, hw⟩ := hlink k ((c.stk k).length - 1 - j) (by omega) (by simp only; omega)
    simp only at hw
    have e1 : (c.stk k).length - 1 - ((c.stk k).length - 1 - j) = j := by omega
    rw [e1] at hw
    rw [hw (by omega), toSig, List.getElem?_map, List.getElem?_take, if_pos hjd]
    simp only [Option.map]
    obtain ⟨g0, hg0⟩ : ∃ g0, (c.stk k)[j]? = some g0 :=
      ⟨(c.stk k)[j], List.getElem?_eq_getElem hjL⟩
    rw [hg0]
    have := hcell k ((c.stk k).length - 1 - j) g0 (by rw [rev_get _ _ hjL, hg0])
    rw [this] at hx
    rw [inr_sig_eq hx]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    simp only [toSig, List.length_map, List.length_take]; omega


theorem rel1_true {P : Summ Γ Λ σ → Prop} {x : TVal Γ Λ σ} :
    rel1 P [x] = true ↔ ∃ s, x = Sum.inl s ∧ P s := by
  cases x <;> simp [rel1]

theorem rel2_true {P : Summ Γ Λ σ → TVal Γ Λ σ → Prop} {x y : TVal Γ Λ σ} :
    rel2 P [x, y] = true ↔ ∃ s, x = Sum.inl s ∧ P s y := by
  cases x <;> simp [rel2]

theorem rel2s_true {P : Summ Γ Λ σ → Summ Γ Λ σ → Prop} {x y : TVal Γ Λ σ} :
    rel2s P [x, y] = true ↔ ∃ s s', x = Sum.inl s ∧ y = Sum.inl s' ∧ P s s' := by
  cases x <;> cases y <;> simp [rel2s]

theorem rel3_true {P : Summ Γ Λ σ → TVal Γ Λ σ → TVal Γ Λ σ → Prop} {x y z : TVal Γ Λ σ} :
    rel3 P [x, y, z] = true ↔ ∃ s, x = Sum.inl s ∧ P s y z := by
  cases x <;> simp [rel3]

theorem relC_true {P : TVal Γ Λ σ → Prop} {x : TVal Γ Λ σ} : relC P [x] = true ↔ P x := by
  simp [relC]

@[simp] theorem summOf_l (c : Cfg Γ Λ σ) : (summOf d c).l = c.l := rfl
@[simp] theorem summOf_len (c : Cfg Γ Λ σ) (k : K) : (summOf d c).len k = (c.stk k).length := rfl

theorem winStep_summOf (c : Cfg Γ Λ σ) (lab : Λ) :
    winStep m (summOf d c) lab = stepAux (m lab) c.var (fun k => (c.stk k).take d) := by
  simp only [winStep, summOf, ofSig_toSig]

theorem rev_take_drop {α : Type*} (l : List α) (d i : ℕ) (g : α)
    (h : (l.drop d).reverse[i]? = some g) : l.reverse[i]? = some g := by
  have hi : i < (l.drop d).reverse.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  conv_lhs => rw [← List.take_append_drop d l]
  rw [List.reverse_append, List.getElem?_append_left hi, h]

/-- **One tableau step.** If row `t` represents `c` and the transition constraints between
rows `t` and `t+1` hold, then row `t+1` represents the next configuration. -/
theorem rep_step (hd : ∀ lab, sdepth (m lab) ≤ d) (a : ℕ → TVal Γ Λ σ) (t : ℕ)
    (c : Cfg Γ Λ σ) (hKs : ∀ k, k ∈ Ks) (hrep : Rep d Ks S a t c)
    (hts : rel2s (transSummP m d) [a (sv Ks S t), a (sv Ks S (t + 1))] = true)
    (htc : ∀ k, ∀ i < S,
      rel3 (transCellP m d k i) [a (sv Ks S t), a (cv Ks S t k i), a (cv Ks S (t + 1) k i)] = true)
    (hrow' : rel1 (rowSummP d S) [a (sv Ks S (t + 1))] = true)
    (hlink' : ∀ k, ∀ i < S, rel2 (linkP d k i) [a (sv Ks S (t + 1)), a (cv Ks S (t + 1) k i)] = true) :
    Rep d Ks S a (t + 1) (stepStay m c) := by
  obtain ⟨s', hs', hrow⟩ := rel1_true.1 hrow'
  obtain ⟨s0, s1, h0, h1, hP⟩ := rel2s_true.1 hts
  rw [hrep.1] at h0; cases h0
  rw [hs'] at h1; cases h1
  have hlink : ∀ k, ∀ i < S, linkP d k i s' (a (cv Ks S (t + 1) k i)) := by
    intro k i hi
    obtain ⟨s2, h2, hP2⟩ := rel2_true.1 (hlink' k i hi)
    rw [hs'] at h2; cases h2; exact hP2
  have hcellP : ∀ k, ∀ i < S, transCellP m d k i (summOf d c) (a (cv Ks S t k i))
      (a (cv Ks S (t + 1) k i)) := by
    intro k i hi
    obtain ⟨s2, h2, hP2⟩ := rel3_true.1 (htc k i hi)
    rw [hrep.1] at h2; cases h2; exact hP2
  rcases hcl : c.l with _ | lab
  · -- halted: nothing changes
    have hstay : stepStay m c = c := by
      obtain ⟨l, v, S'⟩ := c; simp only at hcl; subst hcl; rfl
    rw [hstay]
    simp only [transSummP, summOf_l, hcl] at hP
    refine ⟨by rw [hs', hP], fun k i g hg => ?_⟩
    have hi : i < (c.stk k).length := by
      by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hg; cases hg
    have hiS : i < S := lt_of_lt_of_le hi (by have := (hrow k).1; rw [hP] at this; exact this)
    have := hcellP k i hiS
    simp only [transCellP, summOf_l, summOf_len, hcl] at this
    rw [this hi]; exact hrep.2 k i g hg
  · -- running: use locality
    have hstay : stepStay m c = stepAux (m lab) c.var c.stk := by
      obtain ⟨l, v, S'⟩ := c; simp only at hcl; subst hcl; rfl
    rw [hstay]
    obtain ⟨wl, wv, ws⟩ := stepAux_window (m lab) c.var c.stk d (hd lab)
    have hP' := hP
    simp only [transSummP, summOf_l, summOf_len, hcl] at hP'
    rw [winStep_summOf] at hP'
    obtain ⟨hPl, hPv, hPlen⟩ := hP'
    have hlen : ∀ k, ((stepAux (m lab) c.var c.stk).stk k).length = s'.len k := by
      intro k; rw [ws k, hPlen k, List.length_append, List.length_drop]; omega
    refine rep_of d Ks S a (t + 1) s' _ hKs hs' hrow hlink (by rw [wl, hPl]) (by rw [wv, hPv])
      hlen (fun k i g hg => ?_)
    have hi : i < s'.len k := by
      rw [← hlen k]
      by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hg; cases hg
    have hiS : i < S := lt_of_lt_of_le hi (hrow k).1
    have hc := hcellP k i hiS
    simp only [transCellP, summOf_l, summOf_len, hcl] at hc
    rw [winStep_summOf] at hc
    obtain ⟨hc1, hc2⟩ := hc
    rw [ws k, List.reverse_append] at hg
    by_cases hB : i < (c.stk k).length - d
    · rw [hc1 hB]
      rw [List.getElem?_append_left (by simp; omega)] at hg
      exact hrep.2 k i g (rev_take_drop _ d i g hg)
    · rw [List.getElem?_append_right (by simp; omega)] at hg
      simp only [List.length_reverse, List.length_drop] at hg
      exact hc2 g hg (by omega)


/-- The initial configuration with input stack `st`. -/
def initCfg (main : Λ) (v₀ : σ) (k₀ : K) (st : List (Γ k₀)) : Cfg Γ Λ σ :=
  ⟨some main, v₀, Function.update (fun _ => []) k₀ st⟩

theorem rep_init (a : ℕ → TVal Γ Λ σ) (hKs : ∀ k, k ∈ Ks)
    (hs0 : rel1 (initSummP main v₀ k₀ pre Q) [a (sv Ks S 0)] = true)
    (hc0 : ∀ i < S, rel2 (initCellP k₀ pre allowed i) [a (sv Ks S 0), a (cv Ks S 0 k₀ i)] = true)
    (hrow : rel1 (rowSummP d S) [a (sv Ks S 0)] = true)
    (hlink : ∀ k, ∀ i < S, rel2 (linkP d k i) [a (sv Ks S 0), a (cv Ks S 0 k i)] = true) :
    ∃ ws : List (Γ k₀), ws.length ≤ Q ∧ (∀ g ∈ ws, allowed g) ∧
      Rep d Ks S a 0 (initCfg main v₀ k₀ (pre ++ ws)) := by
  obtain ⟨s, hs, hrowP⟩ := rel1_true.1 hrow
  obtain ⟨s1, h1, ⟨hl, hv, hk, hpre, hQ⟩⟩ := rel1_true.1 hs0
  rw [hs] at h1; cases h1
  have hlinkP : ∀ k, ∀ i < S, linkP d k i s (a (cv Ks S 0 k i)) := by
    intro k i hi
    obtain ⟨s2, h2, hP2⟩ := rel2_true.1 (hlink k i hi)
    rw [hs] at h2; cases h2; exact hP2
  have hcP : ∀ i < S, initCellP k₀ pre allowed i s (a (cv Ks S 0 k₀ i)) := by
    intro i hi
    obtain ⟨s2, h2, hP2⟩ := rel2_true.1 (hc0 i hi)
    rw [hs] at h2; cases h2; exact hP2
  have hLS : s.len k₀ ≤ S := (hrowP k₀).1
  set n := s.len k₀ - pre.length with hn
  have hex : ∀ i : Fin n, ∃ g, allowed g ∧ a (cv Ks S 0 k₀ i) = Sum.inr ⟨k₀, g⟩ :=
    fun i => (hcP i (by omega)).1 i.2
  let f : Fin n → Γ k₀ := fun i => (hex i).choose
  refine ⟨(List.ofFn f).reverse, by simp; omega, fun g hg => ?_, ?_⟩
  · rw [List.mem_reverse, List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact (hex i).choose_spec.1
  have hstk : ∀ k, (initCfg main v₀ k₀ (pre ++ (List.ofFn f).reverse)).stk k =
      if h : k = k₀ then h ▸ (pre ++ (List.ofFn f).reverse) else [] := by
    intro k
    by_cases h : k = k₀
    · subst h; simp [initCfg]
    · simp [initCfg, h]
  refine rep_of d Ks S a 0 s _ hKs hs hrowP hlinkP (by rw [hl]; rfl) (by rw [hv]; rfl) ?_ ?_
  · intro k
    rw [hstk k]
    by_cases h : k = k₀
    · subst h; simp; omega
    · simp [h, hk k h]
  · intro k i g hg
    rw [hstk k] at hg
    by_cases h : k = k₀
    · subst h
      simp only [dite_true, List.reverse_append, List.reverse_reverse] at hg
      by_cases hi : i < n
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_ofFn, dif_pos hi] at hg
        cases hg
        exact (hex ⟨i, hi⟩).choose_spec.2
      · rw [List.getElem?_append_right (by simp; omega), List.length_ofFn] at hg
        have hi' : i < S := by
          have : i - n < pre.length := by
            by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hg; cases hg
          omega
        exact (hcP i hi').2 g hg (by omega)
    · simp [h] at hg

/-- The last row pins down the configuration. -/
theorem rep_final (a : ℕ → TVal Γ Λ σ) (c : Cfg Γ Λ σ) (hrep : Rep d Ks S a T c)
    (hrow : rel1 (rowSummP d S) [a (sv Ks S T)] = true)
    (hf : rel1 (fun s => s = summOf d cacc) [a (sv Ks S T)] = true)
    (hfc : ∀ k, ∀ i < S, relC (finalCellP cacc k i) [a (cv Ks S T k i)] = true) :
    c = cacc := by
  obtain ⟨s, hs, hrowP⟩ := rel1_true.1 hrow
  obtain ⟨s1, h1, rfl⟩ := rel1_true.1 hf
  rw [hs] at h1; cases h1
  have he := hrep.1
  rw [hs] at he
  have he' := (Sum.inl.inj he).symm
  have hl : c.l = cacc.l := by rw [← summOf_l d c, he', summOf_l]
  have hv : c.var = cacc.var := congrArg Summ.var he'
  have hlen : ∀ k, (c.stk k).length = (cacc.stk k).length := fun k => by
    rw [← summOf_len d c, he', summOf_len]
  have hst : ∀ k, c.stk k = cacc.stk k := by
    intro k
    rw [← List.reverse_inj]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < (c.stk k).length
    · have hiS : i < S := lt_of_lt_of_le hi (by
        have := (hrowP k).1; rw [summOf_len] at this; rw [hlen k]; exact this)
      obtain ⟨g, hg⟩ : ∃ g, (c.stk k).reverse[i]? = some g :=
        ⟨_, List.getElem?_eq_getElem (by simpa using hi)⟩
      obtain ⟨g', hg'⟩ : ∃ g', (cacc.stk k).reverse[i]? = some g' :=
        ⟨_, List.getElem?_eq_getElem (by simp; rw [← hlen k]; exact hi)⟩
      have e1 := hrep.2 k i g hg
      have e2 := relC_true.1 (hfc k i hiS) g' hg'
      rw [e1] at e2
      rw [hg, hg', inr_sig_eq e2]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; rw [← hlen k]; omega)]
  obtain ⟨l, v, st⟩ := c
  obtain ⟨l', v', st'⟩ := cacc
  simp only at hl hv hst
  subst hl hv
  congr
  funext k; exact hst k


/-- **Soundness of the tableau.** Any solution of the tableau CSP comes from an allowed input
whose (halt-and-stay) run reaches `cacc` after `T` steps. -/
theorem tab_sound (hd : ∀ lab, sdepth (m lab) ≤ d) (hKs : ∀ k, k ∈ Ks) (U : List (TVal Γ Λ σ))
    (h : CSPSat U (tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc)) :
    ∃ ws : List (Γ k₀), ws.length ≤ Q ∧ (∀ g ∈ ws, allowed g) ∧
      (stepStay m)^[T] (initCfg main v₀ k₀ (pre ++ ws)) = cacc := by
  obtain ⟨a, -, ha⟩ := h
  have H : ∀ c, c ∈ tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc →
      c.rel (c.scope.map a) = true := ha
  simp only [tabCS, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.mem_flatMap, forall_eq_or_imp, List.nil_append] at H
  obtain ⟨hs0, H⟩ := H
  have hc0 : ∀ i < S, rel2 (initCellP k₀ pre allowed i) [a (sv Ks S 0), a (cv Ks S 0 k₀ i)] = true :=
    fun i hi => H _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))))
  have hrow : ∀ t ≤ T, rel1 (rowSummP d S) [a (sv Ks S t)] = true :=
    fun t ht => H _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨t, by omega, Or.inl rfl⟩))))
  have hlink : ∀ t ≤ T, ∀ k, ∀ i < S,
      rel2 (linkP d k i) [a (sv Ks S t), a (cv Ks S t k i)] = true :=
    fun t ht k i hi => H _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨t, by omega,
      Or.inr ⟨k, hKs k, i, hi, rfl⟩⟩))))
  have hts : ∀ t < T, rel2s (transSummP m d) [a (sv Ks S t), a (sv Ks S (t + 1))] = true :=
    fun t ht => H _ (Or.inl (Or.inl (Or.inr ⟨t, ht, Or.inl rfl⟩)))
  have htc : ∀ t < T, ∀ k, ∀ i < S, rel3 (transCellP m d k i)
      [a (sv Ks S t), a (cv Ks S t k i), a (cv Ks S (t + 1) k i)] = true :=
    fun t ht k i hi => H _ (Or.inl (Or.inl (Or.inr ⟨t, ht, Or.inr ⟨k, hKs k, i, hi, rfl⟩⟩)))
  have hf : rel1 (fun s => s = summOf d cacc) [a (sv Ks S T)] = true := H _ (Or.inl (Or.inr (Or.inl rfl)))
  have hfc : ∀ k, ∀ i < S, relC (finalCellP cacc k i) [a (cv Ks S T k i)] = true :=
    fun k i hi => H _ (Or.inr ⟨k, hKs k, i, hi, rfl⟩)
  obtain ⟨ws, hwl, hwa, hrep0⟩ := rep_init d Ks S main v₀ k₀ pre allowed Q a hKs hs0 hc0
    (hrow 0 (Nat.zero_le _)) (hlink 0 (Nat.zero_le _))
  refine ⟨ws, hwl, hwa, ?_⟩
  have hall : ∀ t ≤ T, Rep d Ks S a t ((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws))) := by
    intro t ht
    induction t with
    | zero => exact hrep0
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact rep_step m d Ks S hd a t _ hKs (ih (by omega)) (hts t (by omega)) (htc t (by omega))
        (hrow (t + 1) ht) (hlink (t + 1) ht)
  exact rep_final d Ks S T cacc a _ (hall T le_rfl) (hrow T le_rfl) hf hfc


/-! ### Completeness: a real run gives a solution -/

theorem sv_div (t : ℕ) : sv Ks S t / rowW Ks S = t := by
  unfold sv rowW; rw [Nat.mul_div_cancel _ (by omega)]

theorem sv_mod (t : ℕ) : sv Ks S t % rowW Ks S = 0 := by
  unfold sv; exact Nat.mul_mod_left _ _

theorem cv_lt {k : K} (hk : k ∈ Ks) {i : ℕ} (hi : i < S) :
    1 + Ks.idxOf k * S + i < rowW Ks S := by
  have h1 := List.idxOf_lt_length_of_mem hk
  have : (Ks.idxOf k + 1) * S ≤ Ks.length * S := Nat.mul_le_mul_right _ h1
  unfold rowW; rw [Nat.add_mul] at this; omega

theorem cv_div (t : ℕ) {k : K} (hk : k ∈ Ks) {i : ℕ} (hi : i < S) :
    cv Ks S t k i / rowW Ks S = t := by
  have := cv_lt Ks S hk hi
  unfold cv
  rw [show t * rowW Ks S + 1 + Ks.idxOf k * S + i = (1 + Ks.idxOf k * S + i) + rowW Ks S * t by
    rw [Nat.mul_comm]; omega, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt this,
    Nat.zero_add]

theorem cv_mod (t : ℕ) {k : K} (hk : k ∈ Ks) {i : ℕ} (hi : i < S) :
    cv Ks S t k i % rowW Ks S = 1 + Ks.idxOf k * S + i := by
  have := cv_lt Ks S hk hi
  unfold cv
  rw [show t * rowW Ks S + 1 + Ks.idxOf k * S + i = (1 + Ks.idxOf k * S + i) + rowW Ks S * t by
    rw [Nat.mul_comm]; omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]

/-- Cell `i` (from the bottom) of stack `k` as a tableau value (`u0` above the top). -/
def cellVal (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ) (k : K) (i : ℕ) : TVal Γ Λ σ :=
  match (c.stk k).reverse[i]? with
  | some g => Sum.inr ⟨k, g⟩
  | none => u0

/-- The canonical assignment built from a run. -/
def runAssign (u0 : TVal Γ Λ σ) (c0 : Cfg Γ Λ σ) (v : ℕ) : TVal Γ Λ σ :=
  if T < v / rowW Ks S then u0
  else if v % rowW Ks S = 0 then Sum.inl (summOf d ((stepStay m)^[v / rowW Ks S] c0))
  else match Ks[(v % rowW Ks S - 1) / S]? with
    | some k => cellVal u0 ((stepStay m)^[v / rowW Ks S] c0) k ((v % rowW Ks S - 1) % S)
    | none => u0

theorem runAssign_sv (u0 : TVal Γ Λ σ) (c0 : Cfg Γ Λ σ) {t : ℕ} (ht : t ≤ T) :
    runAssign m d Ks S T u0 c0 (sv Ks S t) = Sum.inl (summOf d ((stepStay m)^[t] c0)) := by
  unfold runAssign
  rw [sv_div, sv_mod, if_neg (by omega), if_pos rfl]

theorem runAssign_cv (u0 : TVal Γ Λ σ) (c0 : Cfg Γ Λ σ) {t : ℕ} (ht : t ≤ T) {k : K}
    (hk : k ∈ Ks) {i : ℕ} (hi : i < S) :
    runAssign m d Ks S T u0 c0 (cv Ks S t k i) = cellVal u0 ((stepStay m)^[t] c0) k i := by
  unfold runAssign
  rw [cv_div Ks S t hk hi, cv_mod Ks S t hk hi, if_neg (by omega), if_neg (by omega)]
  have e1 : (1 + Ks.idxOf k * S + i - 1) / S = Ks.idxOf k := by
    rw [show 1 + Ks.idxOf k * S + i - 1 = i + S * Ks.idxOf k by rw [Nat.mul_comm]; omega,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have e2 : (1 + Ks.idxOf k * S + i - 1) % S = i := by
    rw [show 1 + Ks.idxOf k * S + i - 1 = i + S * Ks.idxOf k by rw [Nat.mul_comm]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  rw [e1, e2, List.getElem?_idxOf hk]

theorem cellVal_of_get (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ) (k : K) (i : ℕ) (g : Γ k)
    (h : (c.stk k).reverse[i]? = some g) : cellVal u0 c k i = Sum.inr ⟨k, g⟩ := by
  unfold cellVal; rw [h]

theorem cellVal_eq_of_lt (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ) (k : K) (i : ℕ)
    (h : i < (c.stk k).length) : ∃ g, (c.stk k).reverse[i]? = some g ∧
      cellVal u0 c k i = Sum.inr ⟨k, g⟩ :=
  ⟨_, List.getElem?_eq_getElem (by simpa using h),
    cellVal_of_get u0 c k i _ (List.getElem?_eq_getElem (by simpa using h))⟩


theorem rowSumm_of (c : Cfg Γ Λ σ) (h : ∀ k, (c.stk k).length ≤ S) : rowSummP d S (summOf d c) :=
  fun k => ⟨h k, by simp [summOf, toSig, Nat.min_comm]⟩

theorem link_of (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ) (k : K) (i : ℕ) :
    linkP d k i (summOf d c) (cellVal u0 c k i) := by
  intro hi
  simp only [summOf_len] at hi
  obtain ⟨g, hg, he⟩ := cellVal_eq_of_lt u0 c k i hi
  refine ⟨g, he, fun hd' => ?_⟩
  simp only [summOf_len] at hd'
  simp only [summOf, toSig, List.getElem?_map, List.getElem?_take]
  rw [List.getElem?_reverse (by simpa using hi)] at hg
  rw [hg]; simp [hd']

theorem transSumm_of (hd : ∀ lab, sdepth (m lab) ≤ d) (c : Cfg Γ Λ σ) :
    transSummP m d (summOf d c) (summOf d (stepStay m c)) := by
  rcases hcl : c.l with _ | lab
  · have hstay : stepStay m c = c := by
      obtain ⟨l, v, S'⟩ := c; simp only at hcl; subst hcl; rfl
    simp only [transSummP, summOf_l, hcl, hstay]
  · have hstay : stepStay m c = stepAux (m lab) c.var c.stk := by
      obtain ⟨l, v, S'⟩ := c; simp only at hcl; subst hcl; rfl
    obtain ⟨wl, wv, ws⟩ := stepAux_window (m lab) c.var c.stk d (hd lab)
    simp only [transSummP, summOf_l, summOf_len, hcl, winStep_summOf, hstay]
    refine ⟨wl, wv, fun k => ?_⟩
    try simp only [summOf]
    rw [ws k, List.length_append, List.length_drop]; omega

theorem transCell_of (hd : ∀ lab, sdepth (m lab) ≤ d) (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ)
    (k : K) (i : ℕ) :
    transCellP m d k i (summOf d c) (cellVal u0 c k i) (cellVal u0 (stepStay m c) k i) := by
  rcases hcl : c.l with _ | lab
  · have hstay : stepStay m c = c := by
      obtain ⟨l, v, S'⟩ := c; simp only at hcl; subst hcl; rfl
    simp only [transCellP, summOf_l, hcl, hstay]
    exact fun _ => trivial
  · have hstay : stepStay m c = stepAux (m lab) c.var c.stk := by
      obtain ⟨l, v, S'⟩ := c; simp only at hcl; subst hcl; rfl
    obtain ⟨wl, wv, ws⟩ := stepAux_window (m lab) c.var c.stk d (hd lab)
    simp only [transCellP, summOf_l, summOf_len, hcl, winStep_summOf, hstay]
    refine ⟨fun hB => ?_, fun g hg hB => ?_⟩
    · obtain ⟨g, hg, he⟩ := cellVal_eq_of_lt u0 c k i (by omega)
      rw [he]
      apply cellVal_of_get
      rw [ws k, List.reverse_append, List.getElem?_append_left (by simp; omega)]
      rw [← hg]
      conv_rhs => rw [← List.take_append_drop d (c.stk k)]
      rw [List.reverse_append, List.getElem?_append_left (by simp; omega)]
    · apply cellVal_of_get
      rw [ws k, List.reverse_append, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_reverse, List.length_drop]
      exact hg

theorem init_of (ws : List (Γ k₀)) (hwl : ws.length ≤ Q) :
    initSummP main v₀ k₀ pre Q (summOf d (initCfg main v₀ k₀ (pre ++ ws))) := by
  refine ⟨rfl, rfl, fun k hk => ?_, ?_, ?_⟩
  · simp [summOf, initCfg, hk]
  · simp [summOf, initCfg]
  · simp [summOf, initCfg]; omega

theorem initCell_of (u0 : TVal Γ Λ σ) (ws : List (Γ k₀)) (hwa : ∀ g ∈ ws, allowed g) (i : ℕ) :
    initCellP k₀ pre allowed i (summOf d (initCfg main v₀ k₀ (pre ++ ws)))
      (cellVal u0 (initCfg main v₀ k₀ (pre ++ ws)) k₀ i) := by
  have hst : (initCfg main v₀ k₀ (pre ++ ws)).stk k₀ = pre ++ ws := by simp [initCfg]
  simp only [initCellP, summOf_len, hst, List.length_append, Nat.add_sub_cancel_left]
  refine ⟨fun hi => ?_, fun g hg hi => ?_⟩
  · have hg : (pre ++ ws).reverse[i]? = some (ws.reverse[i]'(by simpa using hi)) := by
      rw [List.reverse_append, List.getElem?_append_left (by simpa using hi)]
      exact List.getElem?_eq_getElem _
    have hi' : i < ws.reverse.length := by simpa using hi
    refine ⟨_, hwa _ (List.mem_reverse.1 (List.getElem_mem hi')), ?_⟩
    apply cellVal_of_get; rw [hst]; exact hg
  · apply cellVal_of_get; rw [hst, List.reverse_append, List.getElem?_append_right (by simpa using hi)]
    simpa using hg

theorem finalCell_of (u0 : TVal Γ Λ σ) (c : Cfg Γ Λ σ) (k : K) (i : ℕ) :
    finalCellP c k i (cellVal u0 c k i) := fun g hg => cellVal_of_get u0 c k i g hg

/-- **Completeness of the tableau.** An allowed witness whose run reaches `cacc` within the
space bound `S` gives a CSP solution, provided `U` contains every value used. -/
theorem tab_complete (hd : ∀ lab, sdepth (m lab) ≤ d) (hKs : ∀ k, k ∈ Ks)
    (U : List (TVal Γ Λ σ)) (u0 : TVal Γ Λ σ) (hu0 : u0 ∈ U)
    (ws : List (Γ k₀)) (hwl : ws.length ≤ Q) (hwa : ∀ g ∈ ws, allowed g)
    (hrun : (stepStay m)^[T] (initCfg main v₀ k₀ (pre ++ ws)) = cacc)
    (hS : ∀ t ≤ T, ∀ k, (((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws))).stk k).length ≤ S)
    (hU : ∀ t ≤ T, (Sum.inl (summOf d ((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws)))) :
      TVal Γ Λ σ) ∈ U ∧ ∀ k (i : ℕ) g, (((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws))).stk k).reverse[i]? = some g →
        (Sum.inr ⟨k, g⟩ : TVal Γ Λ σ) ∈ U) :
    CSPSat U (tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc) := by
  set c0 := initCfg main v₀ k₀ (pre ++ ws) with hc0
  let a := runAssign m d Ks S T u0 c0
  have aS : ∀ t ≤ T, a (sv Ks S t) = Sum.inl (summOf d ((stepStay m)^[t] c0)) :=
    fun t ht => runAssign_sv m d Ks S T u0 c0 ht
  have aC : ∀ t ≤ T, ∀ k, ∀ i < S, a (cv Ks S t k i) = cellVal u0 ((stepStay m)^[t] c0) k i :=
    fun t ht k i hi => runAssign_cv m d Ks S T u0 c0 ht (hKs k) hi
  refine ⟨a, fun v => ?_, fun c hc => ?_⟩
  · simp only [a, runAssign]
    split_ifs with h1 h2
    · exact hu0
    · exact (hU _ (by omega)).1
    · split
      · next k _ =>
        unfold cellVal
        split
        · next g hg => exact (hU (v / rowW Ks S) (by omega)).2 k _ g hg
        · exact hu0
      · exact hu0
  simp only [tabCS, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | ((((⟨i, hi, rfl⟩ | ⟨t, ht, rfl | ⟨k, -, i, hi, rfl⟩⟩) |
    ⟨t, ht, rfl | ⟨k, -, i, hi, rfl⟩⟩) | rfl) | ⟨k, -, i, hi, rfl⟩)
  · simp only [List.map_cons, List.map_nil]
    rw [aS 0 (Nat.zero_le _)]
    exact rel1_true.2 ⟨_, rfl, init_of d main v₀ k₀ pre Q ws hwl⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aS 0 (Nat.zero_le _), aC 0 (Nat.zero_le _) k₀ i hi]
    exact rel2_true.2 ⟨_, rfl, initCell_of d main v₀ k₀ pre allowed u0 ws hwa i⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aS t (by omega)]
    exact rel1_true.2 ⟨_, rfl, rowSumm_of d S _ (hS t (by omega))⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aS t (by omega), aC t (by omega) k i hi]
    exact rel2_true.2 ⟨_, rfl, link_of d u0 _ k i⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aS t (by omega), aS (t + 1) (by omega), Function.iterate_succ_apply']
    exact rel2s_true.2 ⟨_, _, rfl, rfl, transSumm_of m d hd _⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aS t (by omega), aC t (by omega) k i hi, aC (t + 1) (by omega) k i hi,
      Function.iterate_succ_apply']
    exact rel3_true.2 ⟨_, rfl, transCell_of m d hd u0 _ k i⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aS T le_rfl, hrun]
    exact rel1_true.2 ⟨_, rfl, rfl⟩
  · simp only [List.map_cons, List.map_nil]
    rw [aC T le_rfl k i hi, hrun]
    exact relC_true.2 (finalCell_of u0 cacc k i)


/-! ### The tableau as a CNF formula -/

theorem tabCS_scope_lt (hKs : ∀ k, k ∈ Ks) :
    ∀ c ∈ tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc, ∀ v ∈ c.scope,
      v < (T + 1) * rowW Ks S := by
  have hR : 0 < rowW Ks S := by unfold rowW; omega
  have hsv : ∀ t ≤ T, sv Ks S t < (T + 1) * rowW Ks S := by
    intro t ht; unfold sv; exact Nat.mul_lt_mul_of_pos_right (by omega) hR
  have hcv : ∀ t ≤ T, ∀ k, ∀ i < S, cv Ks S t k i < (T + 1) * rowW Ks S := by
    intro t ht k i hi
    have := cv_lt Ks S (hKs k) hi
    have h2 : t * rowW Ks S + rowW Ks S ≤ (T + 1) * rowW Ks S := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ ht) _
    unfold cv; omega
  intro c hc v hv
  simp only [tabCS, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | ((((⟨i, hi, rfl⟩ | ⟨t, ht, rfl | ⟨k, -, i, hi, rfl⟩⟩) |
    ⟨t, ht, rfl | ⟨k, -, i, hi, rfl⟩⟩) | rfl) | ⟨k, -, i, hi, rfl⟩) <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
    rcases hv with rfl | rfl | rfl <;>
    first
    | exact hsv _ (by omega)
    | exact hcv _ (by omega) _ _ hi

/-- The tableau CNF. -/
noncomputable def tabCNF (U : List (TVal Γ Λ σ)) : CNF :=
  cspCNF U ((T + 1) * rowW Ks S) (tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc)

/-- **Correctness of the Cook–Levin tableau** (for a TM2 machine, a fixed number of steps `T`, a
space bound `S`, and a value list `U` that covers every value the run uses):
the tableau CNF is satisfiable iff some allowed witness `ws` with `|ws| ≤ Q` makes the machine,
started on `pre ++ ws`, reach `cacc` after `T` (halt-and-stay) steps. -/
theorem tabCNF_correct (hd : ∀ lab, sdepth (m lab) ≤ d) (hKs : ∀ k, k ∈ Ks)
    (U : List (TVal Γ Λ σ)) (u0 : TVal Γ Λ σ) (hu0 : u0 ∈ U)
    (hS : ∀ ws : List (Γ k₀), ws.length ≤ Q → (∀ g ∈ ws, allowed g) →
      ∀ t ≤ T, ∀ k, (((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws))).stk k).length ≤ S)
    (hU : ∀ ws : List (Γ k₀), ws.length ≤ Q → (∀ g ∈ ws, allowed g) →
      ∀ t ≤ T, (Sum.inl (summOf d ((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws)))) :
        TVal Γ Λ σ) ∈ U ∧ ∀ k (i : ℕ) g,
        (((stepStay m)^[t] (initCfg main v₀ k₀ (pre ++ ws))).stk k).reverse[i]? = some g →
          (Sum.inr ⟨k, g⟩ : TVal Γ Λ σ) ∈ U) :
    SAT (tabCNF m d Ks S main v₀ k₀ pre allowed Q T cacc U) ↔
      ∃ ws : List (Γ k₀), ws.length ≤ Q ∧ (∀ g ∈ ws, allowed g) ∧
        (stepStay m)^[T] (initCfg main v₀ k₀ (pre ++ ws)) = cacc := by
  unfold tabCNF
  rw [cspCNF_correct U (List.ne_nil_of_mem hu0) _ _ (tabCS_scope_lt m d Ks S main v₀ k₀ pre allowed Q T cacc hKs)]
  constructor
  · exact tab_sound m d Ks S main v₀ k₀ pre allowed Q T cacc hd hKs U
  · rintro ⟨ws, hwl, hwa, hrun⟩
    exact tab_complete m d Ks S main v₀ k₀ pre allowed Q T cacc hd hKs U u0 hu0 ws hwl hwa hrun
      (hS ws hwl hwa) (hU ws hwl hwa)

end Tab

end PvnpReal
