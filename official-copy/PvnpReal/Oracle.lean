/-
  PvnpReal.Oracle — **oracle machines** and the relativized classes `P^A`, `NP^A`.

  Model: `OProg`, the `NProg` normal form (finitely many ℕ-indexed stacks, finite tables,
  one statement tree per step) extended by one statement
  `query k qT q₁ q₂`: read stack `k` (top first) as a bit string via the table `qT`, ask the
  oracle `A`, continue with `q₁` if the answer is yes and `q₂` otherwise. Input `x` is on stack
  `k0`, a witness `w` (for NP) on stack `kw`; a halted machine accepts iff the top of stack `ka`
  decodes to `true` under `accT`. Time = number of statement trees executed (`orunFor`).

  * `InPO A L`  : some oracle program decides `L` with oracle `A` in polynomial time.
  * `InNPO A L` : some oracle program verifies `L` with oracle `A` in polynomial time with
    witnesses of length exactly `Q(|x|)` (the Arora–Barak form of NP).

  General lemmas: query traces (`oQ`, `orunQ`), **trace congruence** (runs only depend on the
  oracle's answers to the queried strings), trace length/count bounds, monotonicity in the clock,
  `P^A ⊆ NP^A`.
-/
import PvnpReal.Reproduce2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

inductive OStmt
  | push (k : ℕ) (f : List ℕ) (q : OStmt)
  | peek (k : ℕ) (f : List (List ℕ)) (q : OStmt)
  | pop (k : ℕ) (f : List (List ℕ)) (q : OStmt)
  | load (f : List ℕ) (q : OStmt)
  | branch (f : List Bool) (q₁ q₂ : OStmt)
  | query (k : ℕ) (qT : List Bool) (q₁ q₂ : OStmt)
  | goto (f : List ℕ)
  | halt
  deriving Encodable

structure OProg where
  k0 : ℕ
  kw : ℕ
  ka : ℕ
  main : ℕ
  init : ℕ
  inT : List ℕ
  accT : List Bool
  m : List OStmt
  deriving Encodable

/-- The bit string read from a stack by a query. -/
def qstr (qT : List Bool) (l : List ℕ) : List Bool := l.map (fun s => qT.getD s false)

open Classical in
/-- One step (one statement tree) with oracle `A`. -/
noncomputable def oAux (A : List Bool → Prop) : OStmt → ℕ → (ℕ → List ℕ) → NCfg
  | .push k f q, v, S => oAux A q v (Function.update S k (f.getD v 0 :: S k))
  | .peek k f q, v, S => oAux A q ((f.getD v []).getD (oc (S k).head?) 0) S
  | .pop k f q, v, S => oAux A q ((f.getD v []).getD (oc (S k).head?) 0)
      (Function.update S k (S k).tail)
  | .load f q, v, S => oAux A q (f.getD v 0) S
  | .branch f q₁ q₂, v, S => cond (f.getD v false) (oAux A q₁ v S) (oAux A q₂ v S)
  | .query k qT q₁ q₂, v, S => if A (qstr qT (S k)) then oAux A q₁ v S else oAux A q₂ v S
  | .goto f, v, S => ⟨some (f.getD v 0), v, S⟩
  | .halt, v, S => ⟨none, v, S⟩

/-- Clocked run with oracle `A` (first halting configuration within `t` steps). -/
noncomputable def orunFor (A : List Bool → Prop) (p : OProg) : ℕ → NCfg → Option NCfg
  | 0, c => if c.l = none then some c else none
  | t + 1, c => match c.l with
    | none => some c
    | some l => orunFor A p t (oAux A (p.m.getD l .halt) c.var c.stk)

def OInit (p : OProg) (x w : List Bool) : NCfg :=
  ⟨some p.main, p.init, fun j =>
    if j = p.k0 then x.map (fun b => p.inT.getD (if b then 1 else 0) 0)
    else if j = p.kw then w.map (fun b => p.inT.getD (if b then 1 else 0) 0) else []⟩

def OAccepts (p : OProg) (h : NCfg) : Prop :=
  (h.stk p.ka).head?.map (fun s => p.accT.getD s false) = some true

/-- **`L ∈ P^A`.** -/
def InPO (A L : Language) : Prop :=
  ∃ (p : OProg) (T : Polynomial ℕ), ∀ x, ∃ h,
    orunFor A p (T.eval x.length) (OInit p x []) = some h ∧ (L x ↔ OAccepts p h)

/-- **`L ∈ NP^A`** (witnesses of length exactly `Q(|x|)`). -/
def InNPO (A L : Language) : Prop :=
  ∃ (p : OProg) (T Q : Polynomial ℕ), ∀ x,
    (∀ w : List Bool, w.length = Q.eval x.length →
      ∃ h, orunFor A p (T.eval x.length) (OInit p x w) = some h) ∧
    (L x ↔ ∃ w h, w.length = Q.eval x.length ∧
      orunFor A p (T.eval x.length) (OInit p x w) = some h ∧ OAccepts p h)

/-- **`P^A ⊆ NP^A`.** -/
theorem InPO.toNPO {A L : Language} (h : InPO A L) : InNPO A L := by
  obtain ⟨p, T, hp⟩ := h
  refine ⟨p, T, 0, fun x => ⟨fun w hw => ?_, ?_⟩⟩
  · have : w = [] := List.length_eq_zero_iff.1 (by simpa using hw)
    subst this; obtain ⟨h, e, _⟩ := hp x; exact ⟨h, e⟩
  · obtain ⟨h, e, hL⟩ := hp x
    rw [hL]
    constructor
    · intro ha; exact ⟨[], h, by simp, e, ha⟩
    · rintro ⟨w, h', hw, e', ha⟩
      have : w = [] := List.length_eq_zero_iff.1 (by simpa using hw)
      subst this; rw [e] at e'; cases e'; exact ha

/-! ### Query traces -/

open Classical in
/-- Strings queried while executing one statement tree. -/
noncomputable def oQ (A : List Bool → Prop) : OStmt → ℕ → (ℕ → List ℕ) → List (List Bool)
  | .push k f q, v, S => oQ A q v (Function.update S k (f.getD v 0 :: S k))
  | .peek k f q, v, S => oQ A q ((f.getD v []).getD (oc (S k).head?) 0) S
  | .pop k f q, v, S => oQ A q ((f.getD v []).getD (oc (S k).head?) 0)
      (Function.update S k (S k).tail)
  | .load f q, v, S => oQ A q (f.getD v 0) S
  | .branch f q₁ q₂, v, S => cond (f.getD v false) (oQ A q₁ v S) (oQ A q₂ v S)
  | .query k qT q₁ q₂, v, S => qstr qT (S k) ::
      (if A (qstr qT (S k)) then oQ A q₁ v S else oQ A q₂ v S)
  | .goto _, _, _ => []
  | .halt, _, _ => []

/-- Strings queried during a clocked run. -/
noncomputable def orunQ (A : List Bool → Prop) (p : OProg) : ℕ → NCfg → List (List Bool)
  | 0, _ => []
  | t + 1, c => match c.l with
    | none => []
    | some l => oQ A (p.m.getD l .halt) c.var c.stk ++
        orunQ A p t (oAux A (p.m.getD l .halt) c.var c.stk)

/-- Number of push nodes / query nodes of a tree. -/
def npush : OStmt → ℕ
  | .push _ _ q => npush q + 1
  | .peek _ _ q => npush q
  | .pop _ _ q => npush q
  | .load _ q => npush q
  | .branch _ q₁ q₂ => npush q₁ + npush q₂
  | .query _ _ q₁ q₂ => npush q₁ + npush q₂
  | .goto _ => 0
  | .halt => 0

def nqry : OStmt → ℕ
  | .push _ _ q => nqry q
  | .peek _ _ q => nqry q
  | .pop _ _ q => nqry q
  | .load _ q => nqry q
  | .branch _ q₁ q₂ => nqry q₁ + nqry q₂
  | .query _ _ q₁ q₂ => nqry q₁ + nqry q₂ + 1
  | .goto _ => 0
  | .halt => 0

open Classical

theorem oAux_congr (A A' : List Bool → Prop) (q : OStmt) :
    ∀ v S, (∀ s ∈ oQ A q v S, (A s ↔ A' s)) → oAux A q v S = oAux A' q v S := by
  induction q with
  | push k f q ih => intro v S h; simp only [oAux, oQ] at h ⊢; exact ih _ _ h
  | peek k f q ih => intro v S h; simp only [oAux, oQ] at h ⊢; exact ih _ _ h
  | pop k f q ih => intro v S h; simp only [oAux, oQ] at h ⊢; exact ih _ _ h
  | load f q ih => intro v S h; simp only [oAux, oQ] at h ⊢; exact ih _ _ h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S h
    simp only [oAux, oQ] at h ⊢
    cases hb : f.getD v false
    · simp only [hb, cond_false] at h ⊢; exact ih₂ _ _ h
    · simp only [hb, cond_true] at h ⊢; exact ih₁ _ _ h
  | query k qT q₁ q₂ ih₁ ih₂ =>
    intro v S h
    simp only [oAux, oQ] at h ⊢
    have h0 := h _ List.mem_cons_self
    have hr : ∀ s ∈ (if A (qstr qT (S k)) then oQ A q₁ v S else oQ A q₂ v S), (A s ↔ A' s) :=
      fun s hs => h s (List.mem_cons_of_mem _ hs)
    by_cases ha : A (qstr qT (S k))
    · rw [if_pos ha] at hr; rw [if_pos ha, if_pos (h0.1 ha)]; exact ih₁ _ _ hr
    · rw [if_neg ha] at hr; rw [if_neg ha, if_neg (fun e => ha (h0.2 e))]; exact ih₂ _ _ hr
  | goto f => intro v S _; rfl
  | halt => intro v S _; rfl

/-- **Trace congruence**: a run only depends on the answers to the strings it queries. -/
theorem orun_congr (A A' : List Bool → Prop) (p : OProg) :
    ∀ t c, (∀ s ∈ orunQ A p t c, (A s ↔ A' s)) → orunFor A p t c = orunFor A' p t c := by
  intro t
  induction t with
  | zero => intro c _; rfl
  | succ t ih =>
    rintro ⟨l, v, S⟩ h
    cases l with
    | none => rfl
    | some l =>
      simp only [orunQ, orunFor] at h ⊢
      have e := oAux_congr A A' _ v S (fun s hs => h s (List.mem_append_left _ hs))
      rw [← e]
      exact ih _ (fun s hs => h s (List.mem_append_right _ hs))

theorem oQ_len (A : List Bool → Prop) (q : OStmt) :
    ∀ v S, (oQ A q v S).length ≤ nqry q := by
  induction q with
  | push k f q ih => intro v S; simp only [oQ, nqry]; exact ih _ _
  | peek k f q ih => intro v S; simp only [oQ, nqry]; exact ih _ _
  | pop k f q ih => intro v S; simp only [oQ, nqry]; exact ih _ _
  | load f q ih => intro v S; simp only [oQ, nqry]; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [oQ, nqry]
    cases hb : f.getD v false
    · have := ih₂ v S; simp only [cond_false]; omega
    · have := ih₁ v S; simp only [cond_true]; omega
  | query k qT q₁ q₂ ih₁ ih₂ =>
    intro v S; simp only [oQ, nqry, List.length_cons]
    split
    · have := ih₁ v S; omega
    · have := ih₂ v S; omega
  | goto f => intro v S; simp [oQ]
  | halt => intro v S; simp [oQ]

/-- Stack growth and query lengths inside one tree. -/
theorem oAux_bound (A : List Bool → Prop) (q : OStmt) :
    ∀ v S B, (∀ k, (S k).length ≤ B) →
      (∀ k, ((oAux A q v S).stk k).length ≤ B + npush q) ∧
      ∀ s ∈ oQ A q v S, s.length ≤ B + npush q := by
  induction q with
  | push k f q ih =>
    intro v S B hS
    have hS' : ∀ j, (Function.update S k (f.getD v 0 :: S k) j).length ≤ B + 1 := by
      intro j
      by_cases e : j = k
      · subst e; simp [hS j]
      · rw [Function.update_of_ne e]; have := hS j; omega
    obtain ⟨a, b⟩ := ih v _ _ hS'
    simp only [oAux, oQ, npush]
    exact ⟨fun j => by have := a j; omega, fun s hs => by have := b s hs; omega⟩
  | peek k f q ih =>
    intro v S B hS; simp only [oAux, oQ, npush]; exact ih _ _ _ hS
  | pop k f q ih =>
    intro v S B hS
    have hS' : ∀ j, (Function.update S k (S k).tail j).length ≤ B := by
      intro j
      by_cases e : j = k
      · subst e; simp; have := hS j; omega
      · rw [Function.update_of_ne e]; exact hS j
    simp only [oAux, oQ, npush]; exact ih _ _ _ hS'
  | load f q ih =>
    intro v S B hS; simp only [oAux, oQ, npush]; exact ih _ _ _ hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S B hS
    simp only [oAux, oQ, npush]
    cases hb : f.getD v false
    · obtain ⟨a, b⟩ := ih₂ v S B hS
      exact ⟨fun j => by have := a j; simp; omega, fun s hs => by have := b s hs; omega⟩
    · obtain ⟨a, b⟩ := ih₁ v S B hS
      exact ⟨fun j => by have := a j; simp; omega, fun s hs => by have := b s hs; omega⟩
  | query k qT q₁ q₂ ih₁ ih₂ =>
    intro v S B hS
    simp only [oAux, oQ, npush]
    obtain ⟨a1, b1⟩ := ih₁ v S B hS
    obtain ⟨a2, b2⟩ := ih₂ v S B hS
    refine ⟨fun j => ?_, fun s hs => ?_⟩
    · split
      · have := a1 j; omega
      · have := a2 j; omega
    · rcases List.mem_cons.1 hs with rfl | hs
      · simp [qstr]; have := hS k; omega
      · split at hs
        · have := b1 s hs; omega
        · have := b2 s hs; omega
  | goto f => intro v S B hS; exact ⟨fun j => by simpa [oAux, npush] using hS j, by simp [oQ]⟩
  | halt => intro v S B hS; exact ⟨fun j => by simpa [oAux, npush] using hS j, by simp [oQ]⟩

/-- Per-program constants: total pushes / queries over all trees. -/
def OProg.cP (p : OProg) : ℕ := (p.m.map npush).sum
def OProg.cQ (p : OProg) : ℕ := (p.m.map nqry).sum

theorem npush_le (p : OProg) (l : ℕ) : npush (p.m.getD l .halt) ≤ p.cP := by
  by_cases hl : l < p.m.length
  · rw [List.getD_eq_getElem _ _ hl]
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem hl))
  · rw [List.getD_eq_default _ _ (by omega)]; simp [npush]

theorem nqry_le (p : OProg) (l : ℕ) : nqry (p.m.getD l .halt) ≤ p.cQ := by
  by_cases hl : l < p.m.length
  · rw [List.getD_eq_getElem _ _ hl]
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem hl))
  · rw [List.getD_eq_default _ _ (by omega)]; simp [nqry]

/-- At most `cQ · t` queries in `t` steps. -/
theorem orunQ_len (A : List Bool → Prop) (p : OProg) :
    ∀ t c, (orunQ A p t c).length ≤ p.cQ * t := by
  intro t
  induction t with
  | zero => intro c; simp [orunQ]
  | succ t ih =>
    rintro ⟨l, v, S⟩
    cases l with
    | none => simp [orunQ]
    | some l =>
      simp only [orunQ, List.length_append]
      have := oQ_len A (p.m.getD l .halt) v S
      have := nqry_le p l
      have := ih (oAux A (p.m.getD l .halt) v S)
      rw [Nat.mul_succ]; omega

/-- Every string queried in `t` steps has length `≤ B + cP · t`. -/
theorem orunQ_bound (A : List Bool → Prop) (p : OProg) :
    ∀ t c B, (∀ k, (c.stk k).length ≤ B) → ∀ s ∈ orunQ A p t c, s.length ≤ B + p.cP * t := by
  intro t
  induction t with
  | zero => intro c B _ s hs; simp [orunQ] at hs
  | succ t ih =>
    rintro ⟨l, v, S⟩ B hS s hs
    cases l with
    | none => simp [orunQ] at hs
    | some l =>
      simp only [orunQ, List.mem_append] at hs
      obtain ⟨a, b⟩ := oAux_bound A (p.m.getD l .halt) v S B hS
      have hp := npush_le p l
      rcases hs with hs | hs
      · have := b s hs; rw [Nat.mul_succ]; nlinarith
      · have := ih _ (B + npush (p.m.getD l .halt)) a s hs
        rw [Nat.mul_succ]; omega

theorem orun_none_l {A : List Bool → Prop} {p : OProg} :
    ∀ {t c h}, orunFor A p t c = some h → h.l = none := by
  intro t
  induction t with
  | zero => intro c h e; simp only [orunFor] at e; split at e <;> simp_all
  | succ t ih =>
    rintro ⟨l, v, S⟩ h e
    cases l with
    | none => simp [orunFor] at e; rw [← e]
    | some l => simp only [orunFor] at e; exact ih e

/-- Monotonicity in the clock. -/
theorem orun_mono {A : List Bool → Prop} {p : OProg} :
    ∀ {t t' c h}, t ≤ t' → orunFor A p t c = some h → orunFor A p t' c = some h := by
  intro t
  induction t with
  | zero =>
    intro t' c h ht e
    simp only [orunFor] at e
    split at e
    · next hl =>
      cases e
      obtain ⟨l, v, S⟩ := c
      simp only at hl; subst hl
      cases t' <;> simp [orunFor]
    · simp at e
  | succ t ih =>
    intro t' c h ht e
    obtain ⟨t', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none => simpa [orunFor] using e
    | some l => simp only [orunFor] at e ⊢; exact ih (by omega) e

theorem OInit_bound (p : OProg) (x w : List Bool) :
    ∀ k, ((OInit p x w).stk k).length ≤ x.length + w.length := by
  intro k
  simp only [OInit]
  split
  · simp
  · split <;> simp

end PvnpReal
