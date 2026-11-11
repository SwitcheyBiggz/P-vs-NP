/-
  PvnpReal.FanOut — the fan-out combinator: if `f` and `g` are polynomial-time computable
  (bit strings to bit strings), so is `x ↦ f x ++ g x`.

  `fanTM M1 M2` copies its input onto both machines' input stacks, runs `M1`, then `M2` (each
  on its own stacks), and finally moves `M2`'s output and then `M1`'s output onto the output
  stack through a scratch stack.
-/
import PvnpReal.Compose

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

inductive FP | p0 | p1 | f1 | f2 | f3 | f4
  deriving DecidableEq

instance : Fintype FP := ⟨{.p0, .p1, .f1, .f2, .f3, .f4}, fun k => by cases k <;> simp⟩

section Fan

variable (M1 M2 : FinTM2) (e1i : M1.Γ M1.k₀ ≃ Bool) (e1o : M1.Γ M1.k₁ ≃ Bool)
  (e2i : M2.Γ M2.k₀ ≃ Bool) (e2o : M2.Γ M2.k₁ ≃ Bool)

/-- Stacks: `inl false` = scratch, `inl true` = output, then `M1`'s and `M2`'s stacks. -/
abbrev FK := Bool ⊕ (M1.K ⊕ M2.K)

abbrev FΓ : FK M1 M2 → Type
  | .inl _ => Bool
  | .inr (.inl k) => M1.Γ k
  | .inr (.inr k) => M2.Γ k

abbrev FΛ := M1.Λ ⊕ (M2.Λ ⊕ FP)
abbrev Fσ := M1.σ × M2.σ × Option Bool
abbrev FSt := TM2.Stmt (FΓ M1 M2) (FΛ M1 M2) (Fσ M1 M2)
abbrev FCfg := TM2.Cfg (FΓ M1 M2) (FΛ M1 M2) (Fσ M1 M2)

def liftA : TM2.Stmt M1.Γ M1.Λ M1.σ → FSt M1 M2
  | .push k f q => push (.inr (.inl k)) (fun s => f s.1) (liftA q)
  | .peek k f q => peek (.inr (.inl k)) (fun s o => (f s.1 o, s.2)) (liftA q)
  | .pop k f q => pop (.inr (.inl k)) (fun s o => (f s.1 o, s.2)) (liftA q)
  | .load a q => load (fun s => (a s.1, s.2)) (liftA q)
  | .branch f q₁ q₂ => branch (fun s => f s.1) (liftA q₁) (liftA q₂)
  | .goto f => goto (fun s => .inl (f s.1))
  | .halt => goto (fun _ => .inr (.inl M2.main))

def liftB : TM2.Stmt M2.Γ M2.Λ M2.σ → FSt M1 M2
  | .push k f q => push (.inr (.inr k)) (fun s => f s.2.1) (liftB q)
  | .peek k f q => peek (.inr (.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (liftB q)
  | .pop k f q => pop (.inr (.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (liftB q)
  | .load a q => load (fun s => (s.1, a s.2.1, s.2.2)) (liftB q)
  | .branch f q₁ q₂ => branch (fun s => f s.2.1) (liftB q₁) (liftB q₂)
  | .goto f => goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => goto (fun _ => .inr (.inr .f1))

/-- Move a stack onto another one (reversing it), converting symbols through `Bool`. -/
def moveStmt (a b : FK M1 M2) (ea : FΓ M1 M2 a → Bool) (eb : Bool → FΓ M1 M2 b) (self : FP)
    (fin : FSt M1 M2) : FSt M1 M2 :=
  pop a (fun s o => (s.1, s.2.1, o.map ea))
    (branch (fun s => s.2.2.isSome)
      (push b (fun s => eb (s.2.2.getD false)) (goto fun _ => .inr (.inr self))) fin)

def p1Stmt : FSt M1 M2 :=
  pop (.inl false) (fun s o => (s.1, s.2.1, o))
    (branch (fun s => s.2.2.isSome)
      (push (.inr (.inl M1.k₀)) (fun s => e1i.symm (s.2.2.getD false))
        (push (.inr (.inr M2.k₀)) (fun s => e2i.symm (s.2.2.getD false))
          (goto fun _ => .inr (.inr .p1))))
      (goto fun _ => .inl M1.main))

def Fm : FΛ M1 M2 → FSt M1 M2
  | .inl l => liftA M1 M2 (M1.m l)
  | .inr (.inl l) => liftB M1 M2 (M2.m l)
  | .inr (.inr .p0) => moveStmt M1 M2 (.inr (.inl M1.k₀)) (.inl false) e1i (fun b => b) .p0
      (goto fun _ => .inr (.inr .p1))
  | .inr (.inr .p1) => p1Stmt M1 M2 e1i e2i
  | .inr (.inr .f1) => moveStmt M1 M2 (.inr (.inr M2.k₁)) (.inl false) e2o (fun b => b) .f1
      (goto fun _ => .inr (.inr .f2))
  | .inr (.inr .f2) => moveStmt M1 M2 (.inl false) (.inl true) (fun b => b) (fun b => b) .f2
      (goto fun _ => .inr (.inr .f3))
  | .inr (.inr .f3) => moveStmt M1 M2 (.inr (.inl M1.k₁)) (.inl false) e1o (fun b => b) .f3
      (goto fun _ => .inr (.inr .f4))
  | .inr (.inr .f4) => moveStmt M1 M2 (.inl false) (.inl true) (fun b => b) (fun b => b) .f4 halt

def fanTM : FinTM2 where
  K := FK M1 M2
  kDecidableEq := inferInstance
  kFin := @instFintypeSum _ _ inferInstance (@instFintypeSum _ _ M1.kFin M2.kFin)
  k₀ := .inr (.inl M1.k₀)
  k₁ := .inl true
  Γ := FΓ M1 M2
  Λ := FΛ M1 M2
  main := .inr (.inr .p0)
  ΛFin := @instFintypeSum _ _ M1.ΛFin (@instFintypeSum _ _ M2.ΛFin inferInstance)
  σ := Fσ M1 M2
  initialState := (M1.initialState, M2.initialState, none)
  σFin := @instFintypeProd _ _ M1.σFin (@instFintypeProd _ _ M2.σFin inferInstance)
  Γk₀Fin := M1.Γk₀Fin
  m := Fm M1 M2 e1i e1o e2i e2o

abbrev FF : Option (FCfg M1 M2) → Option (FCfg M1 M2) :=
  flip bind (TM2.step (Fm M1 M2 e1i e1o e2i e2o))

/-! ### Stack builder -/

def fk (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t o : List Bool) :
    ∀ k : FK M1 M2, List (FΓ M1 M2 k)
  | .inl false => t
  | .inl true => o
  | .inr (.inl k) => S1 k
  | .inr (.inr k) => S2 k

theorem fupd_t (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t o x : List Bool) :
    Function.update (fk M1 M2 S1 S2 t o) (.inl false) x = fk M1 M2 S1 S2 x o := by
  funext j
  rcases j with (_ | _) | j | j
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fupd_o (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t o x : List Bool) :
    Function.update (fk M1 M2 S1 S2 t o) (.inl true) x = fk M1 M2 S1 S2 t x := by
  funext j
  rcases j with (_ | _) | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fupd_1 (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t o : List Bool)
    (k : M1.K) (x : List (M1.Γ k)) :
    Function.update (fk M1 M2 S1 S2 t o) (.inr (.inl k)) x =
      fk M1 M2 (Function.update S1 k x) S2 t o := by
  funext j
  rcases j with (_ | _) | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h; rw [Function.update_self]
      show x = Function.update S1 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S1 j = Function.update S1 k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fupd_2 (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t o : List Bool)
    (k : M2.K) (x : List (M2.Γ k)) :
    Function.update (fk M1 M2 S1 S2 t o) (.inr (.inr k)) x =
      fk M1 M2 S1 (Function.update S2 k x) t o := by
  funext j
  rcases j with (_ | _) | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h; rw [Function.update_self]
      show x = Function.update S2 j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S2 j = Function.update S2 k x j
      rw [Function.update_of_ne h]

/-! ### Moving a stack -/

theorem move_run (a b : FK M1 M2) (hab : a ≠ b) (ea : FΓ M1 M2 a → Bool)
    (eb : Bool → FΓ M1 M2 b) (self : FP) (fin : FSt M1 M2)
    (hm : Fm M1 M2 e1i e1o e2i e2o (.inr (.inr self)) = moveStmt M1 M2 a b ea eb self fin)
    (l : List (FΓ M1 M2 a)) :
    ∀ (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool) (S : ∀ k, List (FΓ M1 M2 k)), S a = l →
    (FF M1 M2 e1i e1o e2i e2o)^[l.length + 1] (some ⟨some (.inr (.inr self)), (v1, v2, o), S⟩) =
      some (TM2.stepAux fin (v1, v2, none)
        (Function.update (Function.update S a []) b ((l.map (eb ∘ ea)).reverse ++ S b))) := by
  induction l with
  | nil =>
    intro v1 v2 o S hS
    show some (TM2.stepAux (Fm M1 M2 e1i e1o e2i e2o (.inr (.inr self))) (v1, v2, o) S) = _
    rw [hm]
    simp only [moveStmt, TM2.stepAux, hS, List.head?_nil, List.tail_nil, Option.map_none,
      Option.isSome_none, Bool.cond_false, List.map_nil, List.reverse_nil, List.nil_append]
    congr 2
    funext k
    by_cases hk : k = b
    · subst hk; rw [Function.update_self, Function.update_of_ne (Ne.symm hab)]
    · rw [Function.update_of_ne hk]
  | cons x l ih =>
    intro v1 v2 o S hS
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : FF M1 M2 e1i e1o e2i e2o (some ⟨some (.inr (.inr self)), (v1, v2, o), S⟩) =
        some ⟨some (.inr (.inr self)), (v1, v2, some (ea x)),
          Function.update (Function.update S a l) b (eb (ea x) :: S b)⟩ := by
      show some (TM2.stepAux (Fm M1 M2 e1i e1o e2i e2o (.inr (.inr self))) (v1, v2, o) S) = _
      rw [hm]
      simp only [moveStmt, TM2.stepAux, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      congr 3
      rw [Function.update_of_ne (Ne.symm hab)]
    rw [e, ih v1 v2 _ _ (by rw [Function.update_of_ne hab, Function.update_self])]
    congr 2
    funext k
    by_cases hk : k = b
    · subst hk
      rw [Function.update_self, Function.update_self, Function.update_self]
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases ha : k = a
      · subst ha; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne hk,
          Function.update_of_ne ha]

/-! ### Phases -/

theorem nil_upd1 (k : M1.K) :
    (Function.update (fun _ => []) k [] : ∀ j, List (M1.Γ j)) = fun _ => [] := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem nil_upd2 (k : M2.K) :
    (Function.update (fun _ => []) k [] : ∀ j, List (M2.Γ j)) = fun _ => [] := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem phA (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool) :
    (FF M1 M2 e1i e1o e2i e2o)^[(S1 M1.k₀).length + 1]
        (some ⟨some (.inr (.inr .p0)), (v1, v2, o), fk M1 M2 S1 S2 t ou⟩) =
      some ⟨some (.inr (.inr .p1)), (v1, v2, none),
        fk M1 M2 (Function.update S1 M1.k₀ []) S2 (((S1 M1.k₀).map e1i).reverse ++ t) ou⟩ := by
  refine (move_run M1 M2 e1i e1o e2i e2o (.inr (.inl M1.k₀)) (.inl false) (by simp) e1i
    (fun b => b) .p0 _ rfl (S1 M1.k₀) v1 v2 o (fk M1 M2 S1 S2 t ou) rfl).trans ?_
  rw [fupd_1, fupd_t]; rfl

theorem phE (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool) :
    (FF M1 M2 e1i e1o e2i e2o)^[(S2 M2.k₁).length + 1]
        (some ⟨some (.inr (.inr .f1)), (v1, v2, o), fk M1 M2 S1 S2 t ou⟩) =
      some ⟨some (.inr (.inr .f2)), (v1, v2, none),
        fk M1 M2 S1 (Function.update S2 M2.k₁ []) (((S2 M2.k₁).map e2o).reverse ++ t) ou⟩ := by
  refine (move_run M1 M2 e1i e1o e2i e2o (.inr (.inr M2.k₁)) (.inl false) (by simp) e2o
    (fun b => b) .f1 _ rfl (S2 M2.k₁) v1 v2 o (fk M1 M2 S1 S2 t ou) rfl).trans ?_
  rw [fupd_2, fupd_t]; rfl

theorem phG (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool) :
    (FF M1 M2 e1i e1o e2i e2o)^[(S1 M1.k₁).length + 1]
        (some ⟨some (.inr (.inr .f3)), (v1, v2, o), fk M1 M2 S1 S2 t ou⟩) =
      some ⟨some (.inr (.inr .f4)), (v1, v2, none),
        fk M1 M2 (Function.update S1 M1.k₁ []) S2 (((S1 M1.k₁).map e1o).reverse ++ t) ou⟩ := by
  refine (move_run M1 M2 e1i e1o e2i e2o (.inr (.inl M1.k₁)) (.inl false) (by simp) e1o
    (fun b => b) .f3 _ rfl (S1 M1.k₁) v1 v2 o (fk M1 M2 S1 S2 t ou) rfl).trans ?_
  rw [fupd_1, fupd_t]; rfl

theorem phF (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool) :
    (FF M1 M2 e1i e1o e2i e2o)^[t.length + 1]
        (some ⟨some (.inr (.inr .f2)), (v1, v2, o), fk M1 M2 S1 S2 t ou⟩) =
      some ⟨some (.inr (.inr .f3)), (v1, v2, none), fk M1 M2 S1 S2 [] (t.reverse ++ ou)⟩ := by
  refine (move_run M1 M2 e1i e1o e2i e2o (.inl false) (.inl true) (by simp) (fun b => b)
    (fun b => b) .f2 _ rfl t v1 v2 o (fk M1 M2 S1 S2 t ou) rfl).trans ?_
  rw [fupd_t, fupd_o, show List.map ((fun b : Bool => b) ∘ fun b => b) t = t from List.map_id t]
  rfl

theorem phH (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool) :
    (FF M1 M2 e1i e1o e2i e2o)^[t.length + 1]
        (some ⟨some (.inr (.inr .f4)), (v1, v2, o), fk M1 M2 S1 S2 t ou⟩) =
      some ⟨none, (v1, v2, none), fk M1 M2 S1 S2 [] (t.reverse ++ ou)⟩ := by
  refine (move_run M1 M2 e1i e1o e2i e2o (.inl false) (.inl true) (by simp) (fun b => b)
    (fun b => b) .f4 _ rfl t v1 v2 o (fk M1 M2 S1 S2 t ou) rfl).trans ?_
  rw [fupd_t, fupd_o, show List.map ((fun b : Bool => b) ∘ fun b => b) t = t from List.map_id t]
  rfl

theorem phB (l : List Bool) : ∀ (S1 : ∀ k, List (M1.Γ k)) (S2 : ∀ k, List (M2.Γ k))
    (ou : List Bool) (v1 : M1.σ) (v2 : M2.σ) (o : Option Bool),
    (FF M1 M2 e1i e1o e2i e2o)^[l.length + 1]
        (some ⟨some (.inr (.inr .p1)), (v1, v2, o), fk M1 M2 S1 S2 l ou⟩) =
      some ⟨some (.inl M1.main), (v1, v2, none),
        fk M1 M2 (Function.update S1 M1.k₀ ((l.map e1i.symm).reverse ++ S1 M1.k₀))
          (Function.update S2 M2.k₀ ((l.map e2i.symm).reverse ++ S2 M2.k₀)) [] ou⟩ := by
  induction l with
  | nil =>
    intro S1 S2 ou v1 v2 o
    show some (TM2.stepAux (p1Stmt M1 M2 e1i e2i) (v1, v2, o) (fk M1 M2 S1 S2 [] ou)) = _
    simp only [p1Stmt, TM2.stepAux]
    show some (TM2.stepAux (goto fun _ => Sum.inl M1.main) (v1, v2, none)
      (Function.update (fk M1 M2 S1 S2 [] ou) (.inl false) [])) = _
    rw [fupd_t]
    simp
  | cons x l ih =>
    intro S1 S2 ou v1 v2 o
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : FF M1 M2 e1i e1o e2i e2o
        (some ⟨some (.inr (.inr .p1)), (v1, v2, o), fk M1 M2 S1 S2 (x :: l) ou⟩) =
        some ⟨some (.inr (.inr .p1)), (v1, v2, some x),
          fk M1 M2 (Function.update S1 M1.k₀ (e1i.symm x :: S1 M1.k₀))
            (Function.update S2 M2.k₀ (e2i.symm x :: S2 M2.k₀)) l ou⟩ := by
      show some (TM2.stepAux (p1Stmt M1 M2 e1i e2i) (v1, v2, o)
        (fk M1 M2 S1 S2 (x :: l) ou)) = _
      simp only [p1Stmt, TM2.stepAux]
      show some (TM2.stepAux (goto fun _ => Sum.inr (Sum.inr FP.p1)) (v1, v2, some x)
        (Function.update (Function.update (Function.update (fk M1 M2 S1 S2 (x :: l) ou)
          (.inl false) l) (.inr (.inl M1.k₀)) (e1i.symm x :: S1 M1.k₀))
          (.inr (.inr M2.k₀)) (e2i.symm x :: S2 M2.k₀))) = _
      rw [fupd_t, fupd_1, fupd_2]; rfl
    rw [e, ih]
    simp

/-! ### Lifting the two machines -/

def liftCA (c : M1.Cfg) (v2 : M2.σ) (o : Option Bool) (S2 : ∀ k, List (M2.Γ k))
    (t ou : List Bool) : FCfg M1 M2 :=
  ⟨some (match c.l with | none => .inr (.inl M2.main) | some l => .inl l), (c.var, v2, o),
    fk M1 M2 c.stk S2 t ou⟩

def liftCB (c : M2.Cfg) (v1 : M1.σ) (o : Option Bool) (S1 : ∀ k, List (M1.Γ k))
    (t ou : List Bool) : FCfg M1 M2 :=
  ⟨some (match c.l with | none => .inr (.inr .f1) | some l => .inr (.inl l)), (v1, c.var, o),
    fk M1 M2 S1 c.stk t ou⟩

theorem stepAux_liftA (v2 : M2.σ) (o : Option Bool) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ) (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (liftA M1 M2 q) (v, v2, o) (fk M1 M2 S S2 t ou) =
      liftCA M1 M2 (TM2.stepAux q v S) v2 o S2 t ou := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (liftA M1 M2 q) (v, v2, o)
      (Function.update (fk M1 M2 S S2 t ou) (.inr (.inl k)) (f v :: S k)) = _
    rw [fupd_1]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (liftA M1 M2 q) (f v (S k).head?, v2, o)
      (Function.update (fk M1 M2 S S2 t ou) (.inr (.inl k)) (S k).tail) = _
    rw [fupd_1]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftCA M1 M2 (cond (f v) _ _) v2 o S2 t ou
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem stepAux_liftB (v1 : M1.σ) (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (t ou : List Bool)
    (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ) (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (liftB M1 M2 q) (v1, v, o) (fk M1 M2 S1 S t ou) =
      liftCB M1 M2 (TM2.stepAux q v S) v1 o S1 t ou := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (liftB M1 M2 q) (v1, v, o)
      (Function.update (fk M1 M2 S1 S t ou) (.inr (.inr k)) (f v :: S k)) = _
    rw [fupd_2]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (liftB M1 M2 q) (v1, f v (S k).head?, o)
      (Function.update (fk M1 M2 S1 S t ou) (.inr (.inr k)) (S k).tail) = _
    rw [fupd_2]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftCB M1 M2 (cond (f v) _ _) v1 o S1 t ou
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem iterate_liftA (v2 : M2.σ) (o : Option Bool) (S2 : ∀ k, List (M2.Γ k)) (t ou : List Bool)
    (n : ℕ) (c d : M1.Cfg) (h : (flip bind (TM2.step M1.m))^[n] (some c) = some d) :
    (FF M1 M2 e1i e1o e2i e2o)^[n] (some (liftCA M1 M2 c v2 o S2 t ou)) =
      some (liftCA M1 M2 d v2 o S2 t ou) := by
  induction n generalizing c with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind (TM2.step M1.m))^[n] none = some d at h
      rw [flip_bind_iterate_none] at h; cases h
    · change (flip bind (TM2.step M1.m))^[n] (some (TM2.stepAux (M1.m l) v S)) = some d at h
      change (FF M1 M2 e1i e1o e2i e2o)^[n]
        (some (TM2.stepAux (liftA M1 M2 (M1.m l)) (v, v2, o) (fk M1 M2 S S2 t ou))) = _
      rw [stepAux_liftA]
      exact ih _ h

theorem iterate_liftB (v1 : M1.σ) (o : Option Bool) (S1 : ∀ k, List (M1.Γ k)) (t ou : List Bool)
    (n : ℕ) (c d : M2.Cfg) (h : (flip bind (TM2.step M2.m))^[n] (some c) = some d) :
    (FF M1 M2 e1i e1o e2i e2o)^[n] (some (liftCB M1 M2 c v1 o S1 t ou)) =
      some (liftCB M1 M2 d v1 o S1 t ou) := by
  induction n generalizing c with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind (TM2.step M2.m))^[n] none = some d at h
      rw [flip_bind_iterate_none] at h; cases h
    · change (flip bind (TM2.step M2.m))^[n] (some (TM2.stepAux (M2.m l) v S)) = some d at h
      change (FF M1 M2 e1i e1o e2i e2o)^[n]
        (some (TM2.stepAux (liftB M1 M2 (M2.m l)) (v1, v, o) (fk M1 M2 S1 S t ou))) = _
      rw [stepAux_liftB]
      exact ih _ h

theorem iter_chain {α : Type*} {f : α → α} {a b : ℕ} {x y z : α} (h1 : f^[a] x = y)
    (h2 : f^[b] y = z) : f^[b + a] x = z := by
  rw [Function.iterate_add_apply, h1, h2]

theorem initList_fan (l : List (M1.Γ M1.k₀)) :
    initList (fanTM M1 M2 e1i e1o e2i e2o) l =
      ⟨some (.inr (.inr .p0)), (M1.initialState, M2.initialState, none),
        fk M1 M2 (Function.update (fun _ => []) M1.k₀ l) (fun _ => []) [] []⟩ := by
  simp only [initList]
  congr 1
  funext j
  rcases j with (_ | _) | j | j
  · rfl
  · rfl
  · by_cases h : j = M1.k₀
    · subst h; simp [fanTM, fk]; rfl
    · simp [fanTM, fk, h]
  · rfl

theorem haltList_fan (l : List Bool) :
    haltList (fanTM M1 M2 e1i e1o e2i e2o) l =
      ⟨none, (M1.initialState, M2.initialState, none),
        fk M1 M2 (fun _ => []) (fun _ => []) [] l⟩ := by
  simp only [haltList]
  congr 1
  funext j
  rcases j with (_ | _) | j | j
  · rfl
  · simp [fanTM, fk]; rfl
  · rfl
  · rfl

/-- The whole fan-out run. -/
theorem fan_run (x o1 o2 : List Bool) (n1 n2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[n1] (some (initList M1 (x.map e1i.symm))) =
      some (haltList M1 (o1.map e1o.symm)))
    (h2 : (flip bind (TM2.step M2.m))^[n2] (some (initList M2 (x.map e2i.symm))) =
      some (haltList M2 (o2.map e2o.symm))) :
    ∃ n, n ≤ 2 * x.length + n1 + n2 + 2 * o1.length + 2 * o2.length + 8 ∧
      (FF M1 M2 e1i e1o e2i e2o)^[n] (some (initList (fanTM M1 M2 e1i e1o e2i e2o)
        (x.map e1i.symm))) = some (haltList (fanTM M1 M2 e1i e1o e2i e2o) (o1 ++ o2)) := by
  have hA := phA M1 M2 e1i e1o e2i e2o (Function.update (fun _ => []) M1.k₀ (x.map e1i.symm))
    (fun _ => []) [] [] M1.initialState M2.initialState none
  simp only [Function.update_idem, nil_upd1, Function.update_self, List.map_map,
    Equiv.self_comp_symm, List.map_id, List.append_nil, List.length_map] at hA
  have hB := phB M1 M2 e1i e1o e2i e2o x.reverse (fun _ => []) (fun _ => []) []
    M1.initialState M2.initialState none
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] at hB
  have hC := iterate_liftA M1 M2 e1i e1o e2i e2o M2.initialState none
    (Function.update (fun _ => []) M2.k₀ (x.map e2i.symm)) [] [] n1 _ _ h1
  have eC1 : liftCA M1 M2 (initList M1 (x.map e1i.symm)) M2.initialState none
      (Function.update (fun _ => []) M2.k₀ (x.map e2i.symm)) [] [] =
      ⟨some (.inl M1.main), (M1.initialState, M2.initialState, none),
        fk M1 M2 (Function.update (fun _ => []) M1.k₀ (x.map e1i.symm))
          (Function.update (fun _ => []) M2.k₀ (x.map e2i.symm)) [] []⟩ := by
    simp only [liftCA, initList_stk]; rfl
  have eC2 : liftCA M1 M2 (haltList M1 (o1.map e1o.symm)) M2.initialState none
      (Function.update (fun _ => []) M2.k₀ (x.map e2i.symm)) [] [] =
      ⟨some (.inr (.inl M2.main)), (M1.initialState, M2.initialState, none),
        fk M1 M2 (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm))
          (Function.update (fun _ => []) M2.k₀ (x.map e2i.symm)) [] []⟩ := by
    simp only [liftCA, haltList_stk]; rfl
  rw [eC1, eC2] at hC
  have hD := iterate_liftB M1 M2 e1i e1o e2i e2o M1.initialState none
    (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm)) [] [] n2 _ _ h2
  have eD1 : liftCB M1 M2 (initList M2 (x.map e2i.symm)) M1.initialState none
      (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm)) [] [] =
      ⟨some (.inr (.inl M2.main)), (M1.initialState, M2.initialState, none),
        fk M1 M2 (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm))
          (Function.update (fun _ => []) M2.k₀ (x.map e2i.symm)) [] []⟩ := by
    simp only [liftCB, initList_stk]; rfl
  have eD2 : liftCB M1 M2 (haltList M2 (o2.map e2o.symm)) M1.initialState none
      (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm)) [] [] =
      ⟨some (.inr (.inr .f1)), (M1.initialState, M2.initialState, none),
        fk M1 M2 (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm))
          (Function.update (fun _ => []) M2.k₁ (o2.map e2o.symm)) [] []⟩ := by
    simp only [liftCB, haltList_stk]; rfl
  rw [eD1, eD2] at hD
  have hE := phE M1 M2 e1i e1o e2i e2o (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm))
    (Function.update (fun _ => []) M2.k₁ (o2.map e2o.symm)) [] [] M1.initialState
    M2.initialState none
  simp only [Function.update_idem, nil_upd2, Function.update_self, List.map_map,
    Equiv.self_comp_symm, List.map_id, List.append_nil, List.length_map] at hE
  have hF := phF M1 M2 e1i e1o e2i e2o (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm))
    (fun _ => []) o2.reverse [] M1.initialState M2.initialState none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hF
  have hG := phG M1 M2 e1i e1o e2i e2o (Function.update (fun _ => []) M1.k₁ (o1.map e1o.symm))
    (fun _ => []) [] o2 M1.initialState M2.initialState none
  simp only [Function.update_idem, nil_upd1, Function.update_self, List.map_map,
    Equiv.self_comp_symm, List.map_id, List.append_nil, List.length_map] at hG
  have hH := phH M1 M2 e1i e1o e2i e2o (fun _ => []) (fun _ => []) o1.reverse o2
    M1.initialState M2.initialState none
  simp only [List.reverse_reverse, List.length_reverse] at hH
  erw [initList_fan, haltList_fan]
  refine ⟨_, ?_, iter_chain hA (iter_chain hB (iter_chain hC (iter_chain hD
    (iter_chain hE (iter_chain hF (iter_chain hG hH))))))⟩
  omega

end Fan

/-- **Fan-out**: if `f` and `g` are polynomial-time computable, so is `x ↦ f x ++ g x`. -/
noncomputable def fanComputable {f g : List Bool → List Bool}
    (h1 : TM2ComputableInPolyTime strEnc strEnc f) (h2 : TM2ComputableInPolyTime strEnc strEnc g) :
    TM2ComputableInPolyTime strEnc strEnc (fun x => f x ++ g x) where
  tm := fanTM h1.tm h2.tm h1.inputAlphabet h1.outputAlphabet h2.inputAlphabet h2.outputAlphabet
  inputAlphabet := h1.inputAlphabet
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + h1.time + h2.time +
    2 * (Polynomial.X + (pushTotal h1.tm : Polynomial ℕ) * h1.time) +
    2 * (Polynomial.X + (pushTotal h2.tm : Polynomial ℕ) * h2.time) + 8
  outputsFun x := by
    have hx1 := h1.outputsFun x
    have hx2 := h2.outputsFun x
    have e1 := hx1.evals_in_steps
    have e2 := hx2.evals_in_steps
    simp only [Option.map_some] at e1 e2
    have H := fan_run h1.tm h2.tm h1.inputAlphabet h1.outputAlphabet h2.inputAlphabet
      h2.outputAlphabet x (f x) (g x) _ _ e1 e2
    refine
      { steps := Classical.choose H
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have hr := (Classical.choose_spec H).2
      erw [List.map_id, Option.map_some]
      exact hr
    · have hn := (Classical.choose_spec H).1
      have hs1 := hx1.steps_le_m
      have hs2 := hx2.steps_le_m
      have hl1 := outLen_bound h1 x
      have hl2 := outLen_bound h2 x
      simp only [strEnc, List.length_map] at *
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
      have hC1 : pushTotal h1.tm * hx1.steps ≤ pushTotal h1.tm * h1.time.eval x.length :=
        Nat.mul_le_mul_left _ hs1
      omega

end PvnpReal
