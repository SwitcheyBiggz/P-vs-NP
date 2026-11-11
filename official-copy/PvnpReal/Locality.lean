/-
  PvnpReal.Locality — a TM2 step only looks at, and only changes, a bounded window at
  the top of each stack. This is the "locality" fact that the Cook–Levin tableau rests on.
-/
import Mathlib.Computability.TuringMachine.StackTuringMachine

namespace PvnpReal

open Turing TM2

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-- How deep into the stacks a statement can read: the number of `peek`/`pop` nodes on the
longest path. -/
def sdepth : Stmt Γ Λ σ → ℕ
  | Stmt.push _ _ q => sdepth q
  | Stmt.peek _ _ q => sdepth q + 1
  | Stmt.pop _ _ q => sdepth q + 1
  | Stmt.load _ q => sdepth q
  | Stmt.branch _ q₁ q₂ => max (sdepth q₁) (sdepth q₂)
  | Stmt.goto _ => 0
  | Stmt.halt => 0

/-- Two stack families agree on their top `m` cells. -/
def TopEq (m : ℕ) (S S' : ∀ k, List (Γ k)) : Prop := ∀ k, (S k).take m = (S' k).take m

theorem TopEq.mono {m n : ℕ} {S S' : ∀ k, List (Γ k)} (h : TopEq m S S') (hn : n ≤ m) :
    TopEq n S S' := by
  intro k
  have := congrArg (List.take n) (h k)
  rwa [List.take_take, List.take_take, Nat.min_eq_left hn] at this

theorem TopEq.head? {m : ℕ} {S S' : ∀ k, List (Γ k)} (h : TopEq (m + 1) S S') (k : K) :
    (S k).head? = (S' k).head? := by
  have := congrArg List.head? (h k)
  rwa [List.head?_take, List.head?_take] at this

theorem TopEq.update_cons {m : ℕ} {S S' : ∀ k, List (Γ k)} (h : TopEq m S S') (k : K)
    (a : Γ k) : TopEq m (Function.update S k (a :: S k)) (Function.update S' k (a :: S' k)) := by
  intro k'
  by_cases hk : k' = k
  · subst hk
    simp only [Function.update_self]
    cases m with
    | zero => simp
    | succ m =>
      rw [List.take_succ_cons, List.take_succ_cons, (h.mono (Nat.le_succ m)) k']
  · simp only [Function.update_of_ne hk]; exact h k'

theorem TopEq.update_tail {m : ℕ} {S S' : ∀ k, List (Γ k)} (h : TopEq (m + 1) S S') (k : K) :
    TopEq m (Function.update S k (S k).tail) (Function.update S' k (S' k).tail) := by
  intro k'
  by_cases hk : k' = k
  · subst hk
    simp only [Function.update_self]
    have := congrArg List.tail (h k')
    have e : ∀ {α : Type _} (l : List α), (l.take (m + 1)).tail = l.tail.take m := by
      intro α l; cases l <;> simp
    rwa [e, e] at this
  · simp only [Function.update_of_ne hk]; exact (h.mono (Nat.le_succ m)) k'

/-- The shape of a stack after a step: a new prefix on top of the old stack with `n ≤ d`
cells removed, where the prefix and `n` are the same for any two stack families that agree on
their top `d` cells. -/
def SameEffect (d : ℕ) (S S' T T' : ∀ k, List (Γ k)) : Prop :=
  ∀ k, ∃ (pre : List (Γ k)) (n : ℕ), n ≤ d ∧ T k = pre ++ (S k).drop n ∧
    T' k = pre ++ (S' k).drop n

/-- **Locality of `stepAux`.** If two stack families agree on their top `sdepth q` cells, then
running `q` yields the same label and state, and each stack changes in the same way: the same
cells are popped (at most `sdepth q`) and the same cells are pushed. -/
theorem stepAux_local (q : Stmt Γ Λ σ) (v : σ) (S S' : ∀ k, List (Γ k))
    (h : TopEq (sdepth q) S S') :
    (stepAux q v S).l = (stepAux q v S').l ∧ (stepAux q v S).var = (stepAux q v S').var ∧
      SameEffect (sdepth q) S S' (stepAux q v S).stk (stepAux q v S').stk := by
  induction q generalizing v S S' with
  | push k f q ih =>
    obtain ⟨h1, h2, h3⟩ := ih v _ _ (h.update_cons k (f v))
    refine ⟨h1, h2, fun k' => ?_⟩
    obtain ⟨pre, n, hn, e1, e2⟩ := h3 k'
    simp only [stepAux, sdepth] at e1 e2 ⊢
    rw [e1, e2]
    by_cases hk : k' = k
    · subst hk
      simp only [Function.update_self]
      cases n with
      | zero => exact ⟨pre ++ [f v], 0, Nat.zero_le _, by simp, by simp⟩
      | succ n =>
        exact ⟨pre, n, by omega, by simp, by simp⟩
    · simp only [Function.update_of_ne hk]
      exact ⟨pre, n, hn, rfl, rfl⟩
  | peek k f q ih =>
    have hh := h.head? k
    simp only [stepAux, sdepth] at h ⊢
    rw [hh]
    obtain ⟨h1, h2, h3⟩ := ih (f v ((S' k).head?)) _ _ (h.mono (Nat.le_succ _))
    refine ⟨h1, h2, fun k' => ?_⟩
    obtain ⟨pre, n, hn, e1, e2⟩ := h3 k'
    exact ⟨pre, n, by omega, e1, e2⟩
  | pop k f q ih =>
    have hh := h.head? k
    simp only [stepAux, sdepth] at h ⊢
    rw [hh]
    obtain ⟨h1, h2, h3⟩ := ih (f v ((S' k).head?)) _ _ (h.update_tail k)
    refine ⟨h1, h2, fun k' => ?_⟩
    obtain ⟨pre, n, hn, e1, e2⟩ := h3 k'
    rw [e1, e2]
    by_cases hk : k' = k
    · subst hk
      simp only [Function.update_self, List.drop_tail]
      exact ⟨pre, n + 1, by omega, rfl, rfl⟩
    · simp only [Function.update_of_ne hk]
      exact ⟨pre, n, by omega, rfl, rfl⟩
  | load a q ih =>
    simp only [stepAux, sdepth] at h ⊢
    exact ih _ _ _ h
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [stepAux, sdepth] at h ⊢
    cases f v
    · obtain ⟨h1, h2, h3⟩ := ih₂ v _ _ (h.mono (le_max_right _ _))
      refine ⟨h1, h2, fun k => ?_⟩
      obtain ⟨pre, n, hn, e1, e2⟩ := h3 k
      exact ⟨pre, n, le_trans hn (le_max_right _ _), e1, e2⟩
    · obtain ⟨h1, h2, h3⟩ := ih₁ v _ _ (h.mono (le_max_left _ _))
      refine ⟨h1, h2, fun k => ?_⟩
      obtain ⟨pre, n, hn, e1, e2⟩ := h3 k
      exact ⟨pre, n, le_trans hn (le_max_left _ _), e1, e2⟩
  | goto f =>
    exact ⟨rfl, rfl, fun k => ⟨[], 0, le_refl _, by simp, by simp⟩⟩
  | halt =>
    exact ⟨rfl, rfl, fun k => ⟨[], 0, le_refl _, by simp, by simp⟩⟩

end PvnpReal

namespace PvnpReal

open Turing TM2

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

theorem TopEq.take_self (d : ℕ) (S : ∀ k, List (Γ k)) : TopEq d S (fun k => (S k).take d) := by
  intro k; simp

/-- **Window form of locality.** Running `q` on the full stacks is the same as running it on
the top `d ≥ sdepth q` cells of each stack and then putting back the untouched part below. -/
theorem stepAux_window (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (d : ℕ)
    (hd : sdepth q ≤ d) :
    (stepAux q v S).l = (stepAux q v (fun k => (S k).take d)).l ∧
    (stepAux q v S).var = (stepAux q v (fun k => (S k).take d)).var ∧
    ∀ k, (stepAux q v S).stk k = (stepAux q v (fun k => (S k).take d)).stk k ++ (S k).drop d := by
  obtain ⟨h1, h2, h3⟩ := stepAux_local q v S _ ((TopEq.take_self d S).mono hd)
  refine ⟨h1, h2, fun k => ?_⟩
  obtain ⟨pre, n, hn, e1, e2⟩ := h3 k
  rw [e1, e2, List.append_assoc]
  congr 1
  have hnd : n ≤ d := le_trans hn hd
  by_cases hl : n ≤ (S k).length
  · conv_lhs => rw [← List.take_append_drop d (S k)]
    rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]
  · have h0 : (S k).drop n = [] := List.drop_eq_nil_of_le (by omega)
    have h0' : (S k).drop d = [] := List.drop_eq_nil_of_le (by omega)
    rw [h0, h0', List.drop_eq_nil_of_le (by rw [List.length_take]; omega)]
    rfl

end PvnpReal
