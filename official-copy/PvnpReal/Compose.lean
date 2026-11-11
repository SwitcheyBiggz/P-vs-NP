/-
  PvnpReal.Compose — composing two polynomial-time Mathlib Turing machines, hence
  transitivity of polynomial-time reductions.

  1. `outLen_bound`: a machine running `n` steps can only grow its stacks by `C·n`
     (`C` = total number of `push` instructions in the program). So polytime outputs are
     polynomially long.
  2. `composeTM`: run `M1`; when it halts, move its output (reversing it twice through a
     scratch stack) onto `M2`'s input stack; run `M2`.
-/
import PvnpReal.PSubsetNP
import PvnpReal.Reductions

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

/-! ## 1. Stack growth is bounded by the number of pushes -/

section Growth
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

theorem len_update_le (S : ∀ k, List (Γ k)) (k' : K) (x : List (Γ k')) (k : K)
    (B : ℕ) (hS : (S k).length ≤ B) (hx : x.length ≤ (S k').length + 1) :
    (Function.update S k' x k).length ≤ B + 1 := by
  by_cases h : k = k'
  · subst h; rw [Function.update_self]; omega
  · rw [Function.update_of_ne h]; omega

theorem stepAux_len (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (B : ℕ)
    (hS : ∀ k, (S k).length ≤ B) : ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B + pushes q := by
  induction q generalizing v S B with
  | push k' f q ih =>
    intro k
    have := ih v _ (B + 1) (fun j => len_update_le S k' (f v :: S k') j B (hS j)
      (by rw [List.length_cons]))
    simp only [TM2.stepAux, pushes]
    have := this k; omega
  | peek k' f q ih => exact ih _ _ _ hS
  | pop k' f q ih =>
    intro k
    have := ih (f v (S k').head?) (Function.update S k' (S k').tail) B (fun j => by
      by_cases h : j = k'
      · subst h; rw [Function.update_self]; simp; have := hS j; omega
      · rw [Function.update_of_ne h]; exact hS j) k
    simpa [TM2.stepAux, pushes] using this
  | load a q ih => exact ih _ _ _ hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro k
    simp only [TM2.stepAux, pushes]
    cases f v
    · have := ih₂ v S B hS k; simp only [Bool.cond_false]; omega
    · have := ih₁ v S B hS k; simp only [Bool.cond_true]; omega
  | goto f => intro k; have := hS k; simp only [TM2.stepAux, pushes]; omega
  | halt => intro k; have := hS k; simp only [TM2.stepAux, pushes]; omega

end Growth

/-- Total number of pushes in a machine's program. -/
noncomputable def pushTotal (tm : FinTM2) : ℕ :=
  @Finset.sum tm.Λ ℕ _ (@Finset.univ tm.Λ tm.ΛFin) (fun l => pushes (tm.m l))

theorem pushes_le_total (tm : FinTM2) (l : tm.Λ) : pushes (tm.m l) ≤ pushTotal tm := by
  letI := tm.ΛFin
  unfold pushTotal
  exact Finset.single_le_sum (f := fun l => pushes (tm.m l)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ l)

theorem iterate_len (tm : FinTM2) (n : ℕ) (c d : tm.Cfg)
    (h : (flip bind tm.step)^[n] (some c) = some d) (B : ℕ)
    (hB : ∀ k, (c.stk k).length ≤ B) : ∀ k, (d.stk k).length ≤ B + pushTotal tm * n := by
  induction n generalizing c B with
  | zero => simp at h; subst h; simpa using hB
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    rcases c with ⟨_ | l, v, S⟩
    · have : (flip bind tm.step)^[n] none = none := flip_bind_iterate_none _ n
      change (flip bind tm.step)^[n] none = some d at h
      rw [this] at h; cases h
    · change (flip bind tm.step)^[n] (some (TM2.stepAux (tm.m l) v S)) = some d at h
      have h1 := stepAux_len (tm.m l) v S B hB
      have h2 := ih _ h (B + pushes (tm.m l)) h1
      intro k
      have := h2 k
      have := pushes_le_total tm l
      have : pushTotal tm * (n + 1) = pushTotal tm * n + pushTotal tm := by ring
      omega

/-- **Output-length bound**: a polytime machine's output is at most
`|input| + C · time(|input|)` long. -/
theorem outLen_bound {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + pushTotal h.tm * h.time.eval (ea a).length := by
  have hx := h.outputsFun a
  have e := hx.evals_in_steps
  simp only [Option.map_some] at e
  have hl := iterate_len h.tm hx.steps _ _ e (ea a).length (by
    intro k
    simp only [initList]
    split
    · next hk => subst hk; simp
    · simp)
  have := hl h.tm.k₁
  simp only [haltList, dite_true, List.length_map] at this
  have hs := hx.steps_le_m
  have : pushTotal h.tm * hx.steps ≤ pushTotal h.tm * h.time.eval (ea a).length :=
    Nat.mul_le_mul_left _ hs
  simp only [eq_mpr_eq_cast, cast_eq, List.length_map] at *
  omega

/-! ## 2. The composition machine -/

section Comp
variable (M1 M2 : FinTM2) {C : Type} [Inhabited C] (e1 : M1.Γ M1.k₁ ≃ C) (e2 : M2.Γ M2.k₀ ≃ C)

/-- Stacks: `none` = scratch (alphabet of `M2`'s input), `some (inl k)` = `M1`'s, `some (inr k)` = `M2`'s. -/
abbrev CK := Option (M1.K ⊕ M2.K)

abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (.inl k) => M1.Γ k
  | some (.inr k) => M2.Γ k

/-- Labels: `M1`'s, `M2`'s, and two transfer phases (`false` = T1, `true` = T2). -/
abbrev CΛ := M1.Λ ⊕ (M2.Λ ⊕ Bool)
abbrev Cσ := M1.σ × M2.σ × Option (M2.Γ M2.k₀)

/-- `M1`'s instructions; `halt` becomes "go to the transfer phase". -/
def lift1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => push (some (.inl k)) (fun s => f s.1) (lift1 q)
  | .peek k f q => peek (some (.inl k)) (fun s o => (f s.1 o, s.2)) (lift1 q)
  | .pop k f q => pop (some (.inl k)) (fun s o => (f s.1 o, s.2)) (lift1 q)
  | .load a q => load (fun s => (a s.1, s.2)) (lift1 q)
  | .branch f q₁ q₂ => branch (fun s => f s.1) (lift1 q₁) (lift1 q₂)
  | .goto f => goto (fun s => .inl (f s.1))
  | .halt => goto (fun _ => .inr (.inr false))

/-- `M2`'s instructions. -/
def lift2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => push (some (.inr k)) (fun s => f s.2.1) (lift2 q)
  | .peek k f q => peek (some (.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift2 q)
  | .pop k f q => pop (some (.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift2 q)
  | .load a q => load (fun s => (s.1, a s.2.1, s.2.2)) (lift2 q)
  | .branch f q₁ q₂ => branch (fun s => f s.2.1) (lift2 q₁) (lift2 q₂)
  | .goto f => goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => halt

def conv (b : M1.Γ M1.k₁) : M2.Γ M2.k₀ := e2.symm (e1 b)

/-- T1: move `M1`'s output onto the scratch stack (reversing it). -/
def sT1 : TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  pop (some (.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map (conv M1 M2 e1 e2)))
    (branch (fun s => s.2.2.isSome)
      (push none (fun s => s.2.2.getD (e2.symm default)) (goto fun _ => .inr (.inr false)))
      (goto fun _ => .inr (.inr true)))

/-- T2: move the scratch stack onto `M2`'s input stack (reversing it back), then start `M2`. -/
def sT2 : TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  pop none (fun s o => (s.1, s.2.1, o))
    (branch (fun s => s.2.2.isSome)
      (push (some (.inr M2.k₀)) (fun s => s.2.2.getD (e2.symm default))
        (goto fun _ => .inr (.inr true)))
      (goto fun _ => .inr (.inl M2.main)))

def Cm : CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .inl l => lift1 M1 M2 (M1.m l)
  | .inr (.inl l) => lift2 M1 M2 (M2.m l)
  | .inr (.inr false) => sT1 M1 M2 e1 e2
  | .inr (.inr true) => sT2 M1 M2 e2

def composeTM : FinTM2 where
  K := CK M1 M2
  kDecidableEq := inferInstance
  kFin := @instFintypeOption _ (@instFintypeSum _ _ M1.kFin M2.kFin)
  k₀ := some (.inl M1.k₀)
  k₁ := some (.inr M2.k₁)
  Γ := CΓ M1 M2
  Λ := CΛ M1 M2
  main := .inl M1.main
  ΛFin := @instFintypeSum _ _ M1.ΛFin (@instFintypeSum _ _ M2.ΛFin inferInstance)
  σ := Cσ M1 M2
  initialState := (M1.initialState, M2.initialState, none)
  σFin := @instFintypeProd _ _ M1.σFin
    (@instFintypeProd _ _ M2.σFin (@instFintypeOption _ M2.Γk₀Fin))
  Γk₀Fin := M1.Γk₀Fin
  m := Cm M1 M2 e1 e2

def cmk (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (sc : List (M2.Γ M2.k₀)) :
    ∀ k, List (CΓ M1 M2 k)
  | none => sc
  | some (.inl k) => S1 k
  | some (.inr k) => S2 k

theorem cupd_sc (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (sc sc' : List (M2.Γ M2.k₀)) :
    Function.update (cmk M1 M2 S1 S2 sc) none sc' = cmk M1 M2 S1 S2 sc' := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem cupd_1 (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (sc : List (M2.Γ M2.k₀))
    (k : M1.K) (x : List (M1.Γ k)) :
    Function.update (cmk M1 M2 S1 S2 sc) (some (.inl k)) x =
      cmk M1 M2 (Function.update S1 k x) S2 sc := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h; rw [Function.update_self]
      show x = Function.update S1 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S1 j = Function.update S1 k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem cupd_2 (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (sc : List (M2.Γ M2.k₀))
    (k : M2.K) (x : List (M2.Γ k)) :
    Function.update (cmk M1 M2 S1 S2 sc) (some (.inr k)) x =
      cmk M1 M2 S1 (Function.update S2 k x) sc := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h; rw [Function.update_self]
      show x = Function.update S2 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S2 j = Function.update S2 k x j
      rw [Function.update_of_ne h]

/-- `M1`'s configuration inside the composite (halted ↦ transfer phase T1). -/
def liftC1 (c : M1.Cfg) : TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (match c.l with | none => .inr (.inr false) | some l => .inl l),
    (c.var, M2.initialState, none), cmk M1 M2 c.stk (fun _ => []) []⟩

def liftC2 (c : M2.Cfg) : TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => .inr (.inl l)), (M1.initialState, c.var, none),
    cmk M1 M2 (fun _ => []) c.stk []⟩

theorem stepAux_lift1 (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ) (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (lift1 M1 M2 q) (v, M2.initialState, none) (cmk M1 M2 S (fun _ => []) []) =
      liftC1 M1 M2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (lift1 M1 M2 q) (v, M2.initialState, none)
      (Function.update (cmk M1 M2 S (fun _ => []) []) (some (.inl k)) (f v :: S k)) = _
    rw [cupd_1]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (lift1 M1 M2 q) (f v (S k).head?, M2.initialState, none)
      (Function.update (cmk M1 M2 S (fun _ => []) []) (some (.inl k)) (S k).tail) = _
    rw [cupd_1]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftC1 M1 M2 (cond (f v) _ _)
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem stepAux_lift2 (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ) (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (lift2 M1 M2 q) (M1.initialState, v, none) (cmk M1 M2 (fun _ => []) S []) =
      liftC2 M1 M2 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (lift2 M1 M2 q) (M1.initialState, v, none)
      (Function.update (cmk M1 M2 (fun _ => []) S []) (some (.inr k)) (f v :: S k)) = _
    rw [cupd_2]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (lift2 M1 M2 q) (M1.initialState, f v (S k).head?, none)
      (Function.update (cmk M1 M2 (fun _ => []) S []) (some (.inr k)) (S k).tail) = _
    rw [cupd_2]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftC2 M1 M2 (cond (f v) _ _)
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

/-- If `M1` runs from `c` to `d` in `n` steps, the composite runs from `liftC1 c` to
`liftC1 d` in `n` steps. -/
theorem iterate_lift1 (n : ℕ) (c d : M1.Cfg)
    (h : (flip bind (TM2.step M1.m))^[n] (some c) = some d) :
    (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[n] (some (liftC1 M1 M2 c)) =
      some (liftC1 M1 M2 d) := by
  induction n generalizing c with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind (TM2.step M1.m))^[n] none = some d at h
      rw [flip_bind_iterate_none] at h; cases h
    · change (flip bind (TM2.step M1.m))^[n] (some (TM2.stepAux (M1.m l) v S)) = some d at h
      change (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[n]
        (some (TM2.stepAux (lift1 M1 M2 (M1.m l)) (v, M2.initialState, none)
          (cmk M1 M2 S (fun _ => []) []))) = _
      rw [stepAux_lift1]
      exact ih _ h

theorem step_lift2 (c : M2.Cfg) :
    TM2.step (Cm M1 M2 e1 e2) (liftC2 M1 M2 c) = (TM2.step M2.m c).map (liftC2 M1 M2) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (lift2 M1 M2 (M2.m l)) (M1.initialState, v, none)
      (cmk M1 M2 (fun _ => []) S [])) = _
    rw [stepAux_lift2]; rfl

theorem iterate_lift2 (n : ℕ) (c : M2.Cfg) :
    (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[n] (some (liftC2 M1 M2 c)) =
      ((flip bind (TM2.step M2.m))^[n] (some c)).map (liftC2 M1 M2) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    show (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[n] (TM2.step (Cm M1 M2 e1 e2) (liftC2 M1 M2 c)) =
      ((flip bind (TM2.step M2.m))^[n] (TM2.step M2.m c)).map (liftC2 M1 M2)
    rw [step_lift2]
    cases h : TM2.step M2.m c with
    | none =>
      exact (flip_bind_iterate_none _ n).trans
        (congrArg (Option.map (liftC2 M1 M2)) (flip_bind_iterate_none _ n)).symm
    | some c' => exact ih c'

/-! ### The two transfer phases -/

theorem T1_cons (v1 : M1.σ) (v2 : M2.σ) (o : Option (M2.Γ M2.k₀)) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) (sc : List (M2.Γ M2.k₀)) (b : M1.Γ M1.k₁) (r : List (M1.Γ M1.k₁))
    (h0 : S1 M1.k₁ = b :: r) :
    TM2.step (Cm M1 M2 e1 e2) ⟨some (.inr (.inr false)), (v1, v2, o), cmk M1 M2 S1 S2 sc⟩ =
      some ⟨some (.inr (.inr false)), (v1, v2, some (conv M1 M2 e1 e2 b)),
        cmk M1 M2 (Function.update S1 M1.k₁ r) S2 (conv M1 M2 e1 e2 b :: sc)⟩ := by
  simp only [TM2.step, Cm, sT1, TM2.stepAux, cmk, h0, List.head?_cons, List.tail_cons,
    Option.map_some, Option.isSome_some, Bool.cond_true, Option.getD_some, cupd_1, cupd_sc]

theorem T1_nil (v1 : M1.σ) (v2 : M2.σ) (o : Option (M2.Γ M2.k₀)) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) (sc : List (M2.Γ M2.k₀)) (h0 : S1 M1.k₁ = []) :
    TM2.step (Cm M1 M2 e1 e2) ⟨some (.inr (.inr false)), (v1, v2, o), cmk M1 M2 S1 S2 sc⟩ =
      some ⟨some (.inr (.inr true)), (v1, v2, none),
        cmk M1 M2 (Function.update S1 M1.k₁ []) S2 sc⟩ := by
  simp only [TM2.step, Cm, sT1, TM2.stepAux, cmk, h0, List.head?_nil, List.tail_nil,
    Option.map_none, Option.isSome_none, Bool.cond_false, cupd_1]

theorem T2_cons (v1 : M1.σ) (v2 : M2.σ) (o : Option (M2.Γ M2.k₀)) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) (b : M2.Γ M2.k₀) (sc : List (M2.Γ M2.k₀)) :
    TM2.step (Cm M1 M2 e1 e2) ⟨some (.inr (.inr true)), (v1, v2, o), cmk M1 M2 S1 S2 (b :: sc)⟩ =
      some ⟨some (.inr (.inr true)), (v1, v2, some b),
        cmk M1 M2 S1 (Function.update S2 M2.k₀ (b :: S2 M2.k₀)) sc⟩ := by
  simp only [TM2.step, Cm, sT2, TM2.stepAux, cmk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some, cupd_2, cupd_sc]

theorem T2_nil (v1 : M1.σ) (v2 : M2.σ) (o : Option (M2.Γ M2.k₀)) (S1 : ∀ k, List (M1.Γ k))
    (S2 : ∀ k, List (M2.Γ k)) :
    TM2.step (Cm M1 M2 e1 e2) ⟨some (.inr (.inr true)), (v1, v2, o), cmk M1 M2 S1 S2 []⟩ =
      some ⟨some (.inr (.inl M2.main)), (v1, v2, none), cmk M1 M2 S1 S2 []⟩ := by
  simp only [TM2.step, Cm, sT2, TM2.stepAux, cmk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, cupd_sc]

theorem loopT1 (v1 : M1.σ) (v2 : M2.σ) (S2 : ∀ k, List (M2.Γ k)) (l : List (M1.Γ M1.k₁)) :
    ∀ (o : Option (M2.Γ M2.k₀)) (sc : List (M2.Γ M2.k₀)),
    (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[l.length + 1]
        (some ⟨some (.inr (.inr false)), (v1, v2, o),
          cmk M1 M2 (Function.update (fun _ => []) M1.k₁ l) S2 sc⟩) =
      some ⟨some (.inr (.inr true)), (v1, v2, none),
        cmk M1 M2 (fun _ => []) S2 ((l.map (conv M1 M2 e1 e2)).reverse ++ sc)⟩ := by
  induction l with
  | nil =>
    intro o sc
    simp only [List.length_nil, zero_add, Function.iterate_one, List.map_nil,
      List.reverse_nil, List.nil_append]
    rw [flip_bind_some, T1_nil M1 M2 e1 e2 _ _ _ _ _ _ (by simp)]
    simp
  | cons b l ih =>
    intro o sc
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some,
      T1_cons M1 M2 e1 e2 _ _ _ _ _ _ b l (by simp), Function.update_idem, ih]
    simp

theorem loopT2 (v1 : M1.σ) (v2 : M2.σ) (S1 : ∀ k, List (M1.Γ k)) (sc : List (M2.Γ M2.k₀)) :
    ∀ (o : Option (M2.Γ M2.k₀)) (m : List (M2.Γ M2.k₀)),
    (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[sc.length + 1]
        (some ⟨some (.inr (.inr true)), (v1, v2, o),
          cmk M1 M2 S1 (Function.update (fun _ => []) M2.k₀ m) sc⟩) =
      some ⟨some (.inr (.inl M2.main)), (v1, v2, none),
        cmk M1 M2 S1 (Function.update (fun _ => []) M2.k₀ (sc.reverse ++ m)) []⟩ := by
  induction sc with
  | nil =>
    intro o m
    simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
      List.nil_append]
    rw [flip_bind_some, T2_nil]
  | cons b sc ih =>
    intro o m
    rw [List.length_cons, Function.iterate_succ_apply, flip_bind_some, T2_cons,
      Function.update_self, Function.update_idem, ih]
    simp

theorem haltList_stk (tm : FinTM2) (l : List (tm.Γ tm.k₁)) :
    (haltList tm l).stk = Function.update (fun _ => []) tm.k₁ l := by
  funext j
  by_cases h : j = tm.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]

theorem initList_compose (l : List (M1.Γ M1.k₀)) :
    initList (composeTM M1 M2 e1 e2) l = liftC1 M1 M2 (initList M1 l) := by
  simp only [initList, liftC1]
  congr 1
  funext j
  rcases j with _ | j | j
  · rfl
  · by_cases h : j = M1.k₀
    · subst h; simp [composeTM, cmk]; rfl
    · simp [composeTM, cmk, h]
  · rfl

theorem haltList_compose (l : List (M2.Γ M2.k₁)) :
    haltList (composeTM M1 M2 e1 e2) l = liftC2 M1 M2 (haltList M2 l) := by
  simp only [haltList, liftC2]
  congr 1
  funext j
  rcases j with _ | j | j
  · rfl
  · rfl
  · by_cases h : j = M2.k₁
    · subst h; simp [composeTM, cmk]; rfl
    · simp [composeTM, cmk, h]

/-- The whole composite run: `M1` (n1 steps), T1, T2, then `M2` (n2 steps). -/
theorem compose_run (l1 : List (M1.Γ M1.k₀)) (out1 : List (M1.Γ M1.k₁))
    (out2 : List (M2.Γ M2.k₁)) (n1 n2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[n1] (some (initList M1 l1)) = some (haltList M1 out1))
    (h2 : (flip bind (TM2.step M2.m))^[n2]
      (some (initList M2 (out1.map (conv M1 M2 e1 e2)))) = some (haltList M2 out2)) :
    (flip bind (TM2.step (Cm M1 M2 e1 e2)))^[n2 + ((out1.length + 1) + ((out1.length + 1) + n1))]
        (some (liftC1 M1 M2 (initList M1 l1))) = some (liftC2 M1 M2 (haltList M2 out2)) := by
  have hA := iterate_lift1 M1 M2 e1 e2 n1 _ _ h1
  have eA : liftC1 M1 M2 (haltList M1 out1) =
      ⟨some (.inr (.inr false)), (M1.initialState, M2.initialState, none),
        cmk M1 M2 (Function.update (fun _ => []) M1.k₁ out1) (fun _ => []) []⟩ := by
    simp only [liftC1, haltList_stk]; rfl
  rw [eA] at hA
  have hB := loopT1 M1 M2 e1 e2 M1.initialState M2.initialState (fun _ => []) out1 none []
  rw [List.append_nil] at hB
  have hE : (fun _ => [] : ∀ k, List (M2.Γ k)) = Function.update (fun _ => []) M2.k₀ [] := by
    simp
  have hC := loopT2 M1 M2 e1 e2 M1.initialState M2.initialState (fun _ => [])
    (out1.map (conv M1 M2 e1 e2)).reverse none []
  rw [← hE, List.reverse_reverse, List.append_nil, List.length_reverse, List.length_map] at hC
  have eD : liftC2 M1 M2 (initList M2 (out1.map (conv M1 M2 e1 e2))) =
      ⟨some (.inr (.inl M2.main)), (M1.initialState, M2.initialState, none),
        cmk M1 M2 (fun _ => []) (Function.update (fun _ => []) M2.k₀
          (out1.map (conv M1 M2 e1 e2))) []⟩ := by
    simp only [liftC2, initList_stk]; rfl
  have hD := iterate_lift2 M1 M2 e1 e2 n2 (initList M2 (out1.map (conv M1 M2 e1 e2)))
  rw [h2, eD] at hD
  rw [Function.iterate_add_apply _ n2, Function.iterate_add_apply _ (out1.length + 1)
    ((out1.length + 1) + n1), Function.iterate_add_apply _ (out1.length + 1) n1,
    hA, hB, hC, hD]
  rfl

end Comp

theorem map_conv {M1 M2 : FinTM2} {C : Type} [Inhabited C] (e1 : M1.Γ M1.k₁ ≃ C)
    (e2 : M2.Γ M2.k₀ ≃ C) (l : List C) :
    (List.map e1.invFun l).map (conv M1 M2 e1 e2) = List.map e2.invFun l := by
  rw [List.map_map]
  congr 1
  funext b
  simp [conv, Equiv.apply_symm_apply]

/-- **Composition of polynomial-time functions** (on bit strings) is polynomial-time. -/
noncomputable def composeComputable {f g : List Bool → List Bool}
    (h1 : TM2ComputableInPolyTime strEnc strEnc f) (h2 : TM2ComputableInPolyTime strEnc strEnc g) :
    TM2ComputableInPolyTime strEnc strEnc (g ∘ f) where
  tm := composeTM h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet
  inputAlphabet := h1.inputAlphabet
  outputAlphabet := h2.outputAlphabet
  time := h1.time + 2 * (Polynomial.X + (pushTotal h1.tm : Polynomial ℕ) * h1.time) + 2 +
    h2.time.comp (Polynomial.X + (pushTotal h1.tm : Polynomial ℕ) * h1.time)
  outputsFun x := by
    let hx1 := h1.outputsFun x
    let hx2 := h2.outputsFun (f x)
    refine
      { steps := hx2.steps + (((List.map h1.outputAlphabet.invFun (strEnc (f x))).length + 1) +
          (((List.map h1.outputAlphabet.invFun (strEnc (f x))).length + 1) + hx1.steps))
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have e1 := hx1.evals_in_steps
      simp only [Option.map_some] at e1
      have e2 : (flip bind (TM2.step h2.tm.m))^[hx2.steps] (some (initList h2.tm
          ((List.map h1.outputAlphabet.invFun (strEnc (f x))).map
            (conv h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet)))) =
          some (haltList h2.tm (List.map h2.outputAlphabet.invFun (strEnc (g (f x))))) := by
        rw [map_conv]; exact hx2.evals_in_steps
      have := compose_run h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet _ _ _ _ _ e1 e2
      erw [initList_compose]
      exact this.trans (congrArg some (haltList_compose _ _ _ _ _).symm)
    · have hs1 := hx1.steps_le_m
      have hs2 := hx2.steps_le_m
      have hlen := outLen_bound h1 x
      have hmono := poly_eval_mono h2.time hlen
      simp only [strEnc, List.length_map] at *
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
      have hC : pushTotal h1.tm * hx1.steps ≤ pushTotal h1.tm * h1.time.eval x.length :=
        Nat.mul_le_mul_left _ hs1
      omega

/-- **Transitivity of polynomial-time reductions.** -/
theorem PolyReduces.trans {L L' L'' : Language} (h1 : PolyReduces L L')
    (h2 : PolyReduces L' L'') : PolyReduces L L'' := by
  obtain ⟨f, ⟨hf⟩, hL⟩ := h1
  obtain ⟨g, ⟨hg⟩, hL'⟩ := h2
  exact ⟨g ∘ f, ⟨composeComputable hf hg⟩, fun x => (hL x).trans (hL' (f x))⟩

/-- NP-hardness transfers along reductions. -/
theorem NPHard.of_reduces {L L' : Language} (h : NPHard L) (hr : PolyReduces L L') :
    NPHard L' := fun L'' hL'' => (h L'' hL'').trans hr

/-- So Cook–Levin follows from *any* NP-hard language reducing to SAT. -/
theorem cookLevin_of_reduces {L : Language} (h : NPHard L) (hr : PolyReduces L SATLang) :
    CookLevinStatement :=
  cookLevin_iff_NPHard.2 (h.of_reduces hr)

end PvnpReal
