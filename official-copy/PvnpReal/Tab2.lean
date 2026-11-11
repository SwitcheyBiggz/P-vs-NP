/-
  PvnpReal.Tab2 — a second Cook–Levin tableau, designed so that its CNF is easy to *print*.

  All CSP variables range over one fixed finite list of values, which does not depend on the input:
  * a control variable per row: label, state, and the top `d` cells of each stack;
  * cell variables `(t, k, p)`: cell `p` of stack `k`, counted from the TOP (`none` = blank).
  A step replaces the top of each stack by a new prefix of length `≤ d + P`, so a cell `p` of
  the next row is a function of the control value and the old cells `p - P … p + d`.
  Every relation is position-independent within its family. The input bits enter only through
  the *scope* of the bit constraints (two fixed variables `0`, `1` hold the two input symbols),
  so the forbidden-tuple lists of all constraints are constants of the machine.
-/
import PvnpReal.CookLevinTab
import PvnpReal.Unary

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

open scoped Classical

section Tab2

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

structure Ctl (Γ : K → Type) (Λ σ : Type) where
  l : Option Λ
  var : σ
  win : K → List (Sig Γ)

abbrev V2 (Γ : K → Type) (Λ σ : Type) := Ctl Γ Λ σ ⊕ Option (Sig Γ)

variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ)

def ctlOf (c : Cfg Γ Λ σ) : Ctl Γ Λ σ :=
  ⟨c.l, c.var, fun k => toSig k ((c.stk k).take d)⟩

def cellOf (c : Cfg Γ Λ σ) (k : K) (p : ℕ) : Option (Sig Γ) :=
  ((c.stk k)[p]?).map (fun g => ⟨k, g⟩)

def winRun (R : Ctl Γ Λ σ) (lab : Λ) : Cfg Γ Λ σ :=
  stepAux (m lab) R.var (fun k => ofSig k (R.win k))

/-! ### Relations -/

noncomputable def ctlRel1 (Pr : Ctl Γ Λ σ → Prop) : List (V2 Γ Λ σ) → Bool
  | [Sum.inl R] => decide (Pr R)
  | _ => false

noncomputable def cellRel1 (Pr : Option (Sig Γ) → Prop) : List (V2 Γ Λ σ) → Bool
  | [Sum.inr c] => decide (Pr c)
  | _ => false

noncomputable def cellRel2 (Pr : Option (Sig Γ) → Option (Sig Γ) → Prop) :
    List (V2 Γ Λ σ) → Bool
  | [Sum.inr c, Sum.inr c'] => decide (Pr c c')
  | _ => false

noncomputable def linkRel (k : K) (i : ℕ) : List (V2 Γ Λ σ) → Bool
  | [Sum.inl R, Sum.inr c] => decide ((R.win k)[i]? = c)
  | _ => false

noncomputable def ctlRel2 (Pr : Ctl Γ Λ σ → Ctl Γ Λ σ → Prop) : List (V2 Γ Λ σ) → Bool
  | [Sum.inl R, Sum.inl R'] => decide (Pr R R')
  | _ => false

def getC (olds : List (V2 Γ Λ σ)) (j : ℕ) : Option (Option (Sig Γ)) :=
  match olds[j]? with
  | some (Sum.inr c) => some c
  | _ => none

def transCP (R R' : Ctl Γ Λ σ) : Prop :=
  match R.l with
  | none => R'.l = R.l ∧ R'.var = R.var
  | some lab => R'.l = (winRun m R lab).l ∧ R'.var = (winRun m R lab).var

def tcP (k : K) (rp pcap : ℕ) (R : Ctl Γ Λ σ) (new : Option (Sig Γ)) (olds : List (V2 Γ Λ σ)) :
    Prop :=
  match R.l with
  | none => getC olds rp = some new
  | some lab =>
    if pcap < ((winRun m R lab).stk k).length then
      new = (((winRun m R lab).stk k)[pcap]?).map (fun g => ⟨k, g⟩)
    else getC olds (rp + d - ((winRun m R lab).stk k).length) = some new

noncomputable def tcRel (k : K) (rp pcap : ℕ) : List (V2 Γ Λ σ) → Bool
  | Sum.inl R :: Sum.inr new :: olds => decide (tcP m d k rp pcap R new olds)
  | _ => false

def witP {k₀ : K} (sb : Bool → Γ k₀) (c c' : Option (Sig Γ)) : Prop :=
  (c = none ∨ ∃ b, c = some ⟨k₀, sb b⟩) ∧ (c = none → c' = none)

/-! ### Specifications on real configurations -/

theorem winRun_ctlOf (c : Cfg Γ Λ σ) (lab : Λ) :
    winRun m (ctlOf d c) lab = stepAux (m lab) c.var (fun k => (c.stk k).take d) := by
  simp only [winRun, ctlOf, ofSig_toSig]

theorem stepStay_none (c : Cfg Γ Λ σ) (h : c.l = none) : stepStay m c = c := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · simp at h

theorem stepStay_some (c : Cfg Γ Λ σ) (lab : Λ) (h : c.l = some lab) :
    stepStay m c = stepAux (m lab) c.var c.stk := by
  rcases c with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; rfl

theorem transCP_iff (hd : ∀ lab, sdepth (m lab) ≤ d) (c : Cfg Γ Λ σ) (R' : Ctl Γ Λ σ) :
    transCP m (ctlOf d c) R' ↔ R'.l = (stepStay m c).l ∧ R'.var = (stepStay m c).var := by
  unfold transCP
  cases hl : c.l with
  | none =>
    simp only [ctlOf, hl, stepStay_none m c hl]
  | some lab =>
    simp only [ctlOf, hl]
    have hw := stepAux_window (m lab) c.var c.stk d (hd lab)
    rw [stepStay_some m c lab hl, hw.1, hw.2.1]
    simp only [winRun, ofSig_toSig]

theorem getC_map (f : ℕ → Option (Sig Γ)) (len j : ℕ) (hj : j < len) :
    getC ((List.range len).map (fun i => (Sum.inr (f i) : V2 Γ Λ σ))) j = some (f j) := by
  simp [getC, List.getElem?_map, List.getElem?_range hj]

/-- **The cell transition relation is exact.** `olds` lists the old cells at positions
`p - rp, …, p - rp + rp + d`. Either `pcap = p` (a small position), or `p ≥ d + P`,
`pcap = d + P`, and `rp = P` (a deep position). -/
theorem tcP_iff (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (c : Cfg Γ Λ σ) (k : K) (p rp pcap : ℕ) (hrp : rp ≤ p)
    (hcase : (pcap = p ∧ rp = p) ∨ (pcap = d + P ∧ d + P ≤ p ∧ rp = P)) (new : Option (Sig Γ)) :
    tcP m d k rp pcap (ctlOf d c) new
      ((List.range (rp + d + 1)).map (fun i => Sum.inr (cellOf c k (p - rp + i)))) ↔
      new = cellOf (stepStay m c) k p := by
  unfold tcP
  cases hl : c.l with
  | none =>
    simp only [ctlOf, hl, stepStay_none m c hl]
    rw [getC_map _ _ _ (by omega), Option.some.injEq, Nat.sub_add_cancel hrp, eq_comm]
  | some lab =>
    simp only [ctlOf, hl]
    have hw := stepAux_window (m lab) c.var c.stk d (hd lab)
    simp only [winRun, ofSig_toSig]
    rw [stepStay_some m c lab hl]
    set W := (stepAux (m lab) c.var (fun k => (c.stk k).take d)).stk k with hW
    have hWl : W.length ≤ d + P := by
      have := stepAux_len (m lab) c.var (fun k => (c.stk k).take d) d
        (fun k => by simp) k
      have := hP lab
      rw [hW]; omega
    unfold cellOf
    rw [hw.2.2 k, ← hW]
    split_ifs with hp
    · have hpW : p < W.length := by omega
      rw [List.getElem?_append_left hpW]
      rcases hcase with ⟨h1, -⟩ | ⟨h1, h2, -⟩
      · subst h1; rfl
      · omega
    · have hpW : W.length ≤ p := by omega
      rw [getC_map _ _ _ (by omega), Option.some.injEq, List.getElem?_append_right hpW,
        List.getElem?_drop]
      have : p - rp + (rp + d - W.length) = d + (p - W.length) := by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> omega
      rw [this, eq_comm]

/-- Windows are determined by the cells. -/
theorem ctl_eq_of (R : Ctl Γ Λ σ) (c : Cfg Γ Λ σ) (hl : R.l = c.l) (hv : R.var = c.var)
    (hwl : ∀ k, (R.win k).length ≤ d) (hlink : ∀ k, ∀ i < d, (R.win k)[i]? = cellOf c k i) :
    R = ctlOf d c := by
  rcases R with ⟨l, v, w⟩
  simp only at hl hv hwl hlink
  subst hl; subst hv
  simp only [ctlOf, Ctl.mk.injEq, true_and]
  funext k
  apply List.ext_getElem?
  intro i
  by_cases hi : i < d
  · rw [hlink k i hi]
    simp [cellOf, toSig, List.getElem?_take, hi]
  · rw [List.getElem?_eq_none (by have := hwl k; omega)]
    simp [toSig, List.getElem?_take, hi]

/-! ### Layout and constraints -/

section Layout
variable (Ks : List K) (S T : ℕ)

def W2 : ℕ := 1 + Ks.length * S
def sv2 (t : ℕ) : ℕ := 2 + t * W2 Ks S
def cv2 (t : ℕ) (k : K) (p : ℕ) : ℕ := 2 + t * W2 Ks S + 1 + Ks.idxOf k * S + p

variable (k₀ k₁ : K) (main : Λ) (v₀ : σ) (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁)
  (xs : List Bool)

/-- The two fixed variables holding the two input symbols. -/
noncomputable def csZ : List (Constraint (V2 Γ Λ σ)) :=
  [⟨[0], cellRel1 (· = some ⟨k₀, sb false⟩)⟩, ⟨[1], cellRel1 (· = some ⟨k₀, sb true⟩)⟩]

/-- Row 0: control, input bits, separator, witness cells, blanks. -/
noncomputable def csInit : List (Constraint (V2 Γ Λ σ)) :=
  [⟨[sv2 Ks S 0], ctlRel1 (fun R => R.l = some main ∧ R.var = v₀)⟩] ++
  (List.range xs.length).map (fun i =>
    ⟨[cv2 Ks S 0 k₀ i, NthTM.bit xs i], cellRel2 (· = ·)⟩) ++
  [⟨[cv2 Ks S 0 k₀ xs.length], cellRel1 (· = some ⟨k₀, sep⟩)⟩] ++
  (List.range Q).map (fun j =>
    ⟨[cv2 Ks S 0 k₀ (xs.length + 1 + j), cv2 Ks S 0 k₀ (xs.length + 2 + j)], cellRel2 (witP sb)⟩) ++
  (List.range (S - (xs.length + 1 + Q))).map (fun j =>
    ⟨[cv2 Ks S 0 k₀ (xs.length + 1 + Q + j)], cellRel1 (· = none)⟩) ++
  (Ks.filter (· ≠ k₀)).flatMap (fun k => (List.range S).map (fun p =>
    ⟨[cv2 Ks S 0 k p], cellRel1 (· = none)⟩))

/-- Per row: window links and the blank bottom margin. -/
noncomputable def csRow (t : ℕ) : List (Constraint (V2 Γ Λ σ)) :=
  Ks.flatMap (fun k =>
    (List.range d).map (fun i => ⟨[sv2 Ks S t, cv2 Ks S t k i], linkRel k i⟩) ++
    (List.range (d + 1)).map (fun j => ⟨[cv2 Ks S t k (S - (d + 1) + j)], cellRel1 (· = none)⟩))

/-- Between rows `t` and `t + 1`. -/
noncomputable def csTrans (t : ℕ) : List (Constraint (V2 Γ Λ σ)) :=
  ⟨[sv2 Ks S t, sv2 Ks S (t + 1)], ctlRel2 (transCP m)⟩ ::
  Ks.flatMap (fun k =>
    (List.range (d + P)).map (fun p =>
      ⟨sv2 Ks S t :: cv2 Ks S (t + 1) k p :: (List.range (p + d + 1)).map (fun i => cv2 Ks S t k i),
        tcRel m d k p p⟩) ++
    (List.range (S - (d + P) - (d + 1))).map (fun j =>
      ⟨sv2 Ks S t :: cv2 Ks S (t + 1) k (d + P + j) ::
          (List.range (P + d + 1)).map (fun i => cv2 Ks S t k (d + j + i)),
        tcRel m d k P (d + P)⟩))

noncomputable def csFinal : List (Constraint (V2 Γ Λ σ)) :=
  [⟨[cv2 Ks S T k₁ 0], cellRel1 (· = some ⟨k₁, gacc⟩)⟩]

/-- **The second tableau.** -/
noncomputable def tab2CS : List (Constraint (V2 Γ Λ σ)) :=
  csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs ++ (List.range (T + 1)).flatMap (csRow d Ks S) ++
    (List.range T).flatMap (csTrans m d P Ks S) ++ csFinal Ks S T k₁ gacc

end Layout

end Tab2

end PvnpReal
