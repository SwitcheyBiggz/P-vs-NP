/-
  PvnpReal.IterTM — **iteration combinator**: if `g` is polytime and its iterates grow at most
  polynomially, then `1ᵗ 0 y ↦ g^[t] y` is polytime (a verified loop machine running a lifted
  copy of the machine for `g`, `t` times).
-/
import PvnpReal.NormalForm

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

namespace IterTM

open TM2.Stmt

inductive IK | I | C | X | O
  deriving DecidableEq

instance : Fintype IK := ⟨{.I, .C, .X, .O}, fun k => by cases k <;> simp⟩

inductive IL | A | B | XM | L | F | Z1 | Z2
  deriving DecidableEq

instance : Fintype IL := ⟨{.A, .B, .XM, .L, .F, .Z1, .Z2}, fun k => by cases k <;> simp⟩

section Defs

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

abbrev K := IK ⊕ M.K

abbrev Γ : K M → Type
  | .inl _ => Bool
  | .inr k => M.Γ k

abbrev Λ := M.Λ ⊕ IL
abbrev σ := M.σ × Option Bool

def stk (i c x o : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k, List (Γ M k)
  | .inl .I => i
  | .inl .C => c
  | .inl .X => x
  | .inl .O => o
  | .inr k => S k

variable {M}

@[simp] theorem stk_I (i c x o S) : stk M i c x o S (.inl .I) = i := rfl
@[simp] theorem stk_C (i c x o S) : stk M i c x o S (.inl .C) = c := rfl
@[simp] theorem stk_X (i c x o S) : stk M i c x o S (.inl .X) = x := rfl
@[simp] theorem stk_O (i c x o S) : stk M i c x o S (.inl .O) = o := rfl
@[simp] theorem stk_M (i c x o S) (k : M.K) : stk M i c x o S (.inr k) = S k := rfl

@[simp] theorem upd_I (i c x o S) (i' : List Bool) :
    Function.update (stk M i c x o S) (.inl .I) i' = stk M i' c x o S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_self]; rfl
  all_goals (rw [Function.update_of_ne (by simp)]; rfl)

@[simp] theorem upd_C (i c x o S) (c' : List Bool) :
    Function.update (stk M i c x o S) (.inl .C) c' = stk M i c' x o S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals (rw [Function.update_of_ne (by simp)]; rfl)

@[simp] theorem upd_X (i c x o S) (x' : List Bool) :
    Function.update (stk M i c x o S) (.inl .X) x' = stk M i c x' o S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals (rw [Function.update_of_ne (by simp)]; rfl)

@[simp] theorem upd_O (i c x o S) (o' : List Bool) :
    Function.update (stk M i c x o S) (.inl .O) o' = stk M i c x o' S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

@[simp] theorem upd_M (i c x o S) (k : M.K) (l : List (M.Γ k)) :
    Function.update (stk M i c x o S) (.inr k) l = stk M i c x o (Function.update S k l) := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  any_goals (rw [Function.update_of_ne (by simp)]; rfl)
  by_cases h : j = k
  · subst h; rw [Function.update_self]
    show l = Function.update S j l j
    rw [Function.update_self]
  · rw [Function.update_of_ne (by simpa using h)]
    show S j = Function.update S k l j
    rw [Function.update_of_ne h]

variable (M)

def lift : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (Γ M) (Λ M) (σ M)
  | .push k f q => push (.inr k) (fun s => f s.1) (lift q)
  | .peek k f q => peek (.inr k) (fun s o => (f s.1 o, s.2)) (lift q)
  | .pop k f q => pop (.inr k) (fun s o => (f s.1 o, s.2)) (lift q)
  | .load a q => load (fun s => (a s.1, s.2)) (lift q)
  | .branch f q₁ q₂ => branch (fun s => f s.1) (lift q₁) (lift q₂)
  | .goto f => goto (fun s => .inl (f s.1))
  | .halt => goto (fun _ => .inr .F)

def isT : Option Bool → Bool
  | some true => true
  | _ => false

def sA : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .I) (fun s o => (s.1, o)) (branch (fun s => isT s.2)
    (push (.inl .C) (fun _ => true) (goto fun _ => .inr .A)) (goto fun _ => .inr .B))

def sB : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .I) (fun s o => (s.1, o)) (branch (fun s => s.2.isSome)
    (push (.inl .X) (fun s => s.2.getD false) (goto fun _ => .inr .B)) (goto fun _ => .inr .XM))

def sXM : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .X) (fun s o => (s.1, o)) (branch (fun s => s.2.isSome)
    (push (.inr M.k₀) (fun s => e.symm (s.2.getD false)) (goto fun _ => .inr .XM))
    (goto fun _ => .inr .L))

def sL : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .C) (fun s o => (s.1, o)) (branch (fun s => s.2.isSome)
    (load (fun s => (s.1, none)) (goto fun _ => .inl M.main)) (goto fun _ => .inr .Z1))

def sF : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inr M.k₁) (fun s o => (s.1, o.map eo)) (branch (fun s => s.2.isSome)
    (push (.inl .X) (fun s => s.2.getD false) (goto fun _ => .inr .F)) (goto fun _ => .inr .XM))

def sZ1 : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inr M.k₀) (fun s o => (s.1, o.map e)) (branch (fun s => s.2.isSome)
    (push (.inl .X) (fun s => s.2.getD false) (goto fun _ => .inr .Z1)) (goto fun _ => .inr .Z2))

def sZ2 : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .X) (fun s o => (s.1, o)) (branch (fun s => s.2.isSome)
    (push (.inl .O) (fun s => s.2.getD false) (goto fun _ => .inr .Z2)) halt)

def pm : Λ M → TM2.Stmt (Γ M) (Λ M) (σ M)
  | .inl l => lift M (M.m l)
  | .inr .A => sA M
  | .inr .B => sB M
  | .inr .XM => sXM M e
  | .inr .L => sL M
  | .inr .F => sF M eo
  | .inr .Z1 => sZ1 M e
  | .inr .Z2 => sZ2 M

def tm : FinTM2 where
  K := K M
  kDecidableEq := inferInstance
  kFin := @instFintypeSum _ _ inferInstance M.kFin
  k₀ := .inl .I
  k₁ := .inl .O
  Γ := Γ M
  Λ := Λ M
  main := .inr .A
  ΛFin := @instFintypeSum _ _ M.ΛFin inferInstance
  σ := σ M
  initialState := (M.initialState, none)
  σFin := @instFintypeProd _ _ M.σFin inferInstance
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := pm M e eo

end Defs

section Runs

variable {M : FinTM2} {e : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}

local notation "Fs" => flip bind (TM2.step (pm M e eo))

abbrev PC := TM2.Cfg (Γ M) (Λ M) (σ M)

theorem runA (l : List Bool) (a : ℕ) (v : M.σ) (w : Option Bool) (S : ∀ k, List (M.Γ k)) :
    ∃ w', Fs^[lpN l + 1] (some (⟨some (.inr .A), (v, w), stk M l (List.replicate a true) [] [] S⟩ : PC)) =
      some ⟨some (.inr .B), (v, w'), stk M (lpX l) (List.replicate (a + lpN l) true) [] [] S⟩ := by
  induction l generalizing a w with
  | nil => exact ⟨none, by simp [TM2.step, pm, sA, TM2.stepAux, isT, flip, lpN, lpX]⟩
  | cons b l ih =>
    cases b
    · exact ⟨some false, by
        simp [TM2.step, pm, sA, TM2.stepAux, isT, flip, LoopTM.lpN_cons_false,
          LoopTM.lpX_cons_false]⟩
    · obtain ⟨w', h⟩ := ih (a + 1) (some true)
      refine ⟨w', ?_⟩
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply]
      have e1 : Fs (some (⟨some (.inr .A), (v, w), stk M (true :: l) (List.replicate a true) [] [] S⟩ : PC)) =
          some ⟨some (.inr .A), (v, some true), stk M l (List.replicate (a + 1) true) [] [] S⟩ := by
        simp [TM2.step, pm, sA, TM2.stepAux, isT, flip, List.replicate_succ]
      rw [e1, h, show a + 1 + lpN l = a + (lpN l + 1) by omega]

theorem runB (y : List Bool) (v : M.σ) (w : Option Bool) (c x : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[y.length + 1] (some (⟨some (.inr .B), (v, w), stk M y c x [] S⟩ : PC)) =
      some ⟨some (.inr .XM), (v, none), stk M [] c (y.reverse ++ x) [] S⟩ := by
  induction y generalizing w x with
  | nil => simp [TM2.step, pm, sB, TM2.stepAux, flip]
  | cons b y ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .B), (v, w), stk M (b :: y) c x [] S⟩ : PC)) =
        some ⟨some (.inr .B), (v, some b), stk M y c (b :: x) [] S⟩ := by
      simp [TM2.step, pm, sB, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem runXM (l : List Bool) (v : M.σ) (w : Option Bool) (c : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .XM), (v, w), stk M [] c l [] S⟩ : PC)) =
      some ⟨some (.inr .L), (v, none), stk M [] c [] []
        (Function.update S M.k₀ (l.reverse.map e.symm ++ S M.k₀))⟩ := by
  induction l generalizing w S with
  | nil => simp [TM2.step, pm, sXM, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .XM), (v, w), stk M [] c (b :: l) [] S⟩ : PC)) =
        some ⟨some (.inr .XM), (v, some b), stk M [] c l []
          (Function.update S M.k₀ (e.symm b :: S M.k₀))⟩ := by
      simp [TM2.step, pm, sXM, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem runL_some (v : M.σ) (w : Option Bool) (b : Bool) (c : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[1] (some (⟨some (.inr .L), (v, w), stk M [] (b :: c) [] [] S⟩ : PC)) =
      some ⟨some (.inl M.main), (v, none), stk M [] c [] [] S⟩ := by
  simp [TM2.step, pm, sL, TM2.stepAux, flip]

theorem runL_none (v : M.σ) (w : Option Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[1] (some (⟨some (.inr .L), (v, w), stk M [] [] [] [] S⟩ : PC)) =
      some ⟨some (.inr .Z1), (v, none), stk M [] [] [] [] S⟩ := by
  simp [TM2.step, pm, sL, TM2.stepAux, flip]

theorem runF (l : List (M.Γ M.k₁)) (v : M.σ) (w : Option Bool) (c x : List Bool)
    (S : ∀ k, List (M.Γ k)) (hS : S M.k₁ = l) :
    Fs^[l.length + 1] (some (⟨some (.inr .F), (v, w), stk M [] c x [] S⟩ : PC)) =
      some ⟨some (.inr .XM), (v, none),
        stk M [] c ((l.map eo).reverse ++ x) [] (Function.update S M.k₁ [])⟩ := by
  induction l generalizing w x S with
  | nil =>
    have : Function.update S M.k₁ [] = S := by rw [← hS]; simp
    simp [TM2.step, pm, sF, TM2.stepAux, flip, hS, this]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .F), (v, w), stk M [] c x [] S⟩ : PC)) =
        some ⟨some (.inr .F), (v, some (eo b)),
          stk M [] c (eo b :: x) [] (Function.update S M.k₁ l)⟩ := by
      simp [TM2.step, pm, sF, TM2.stepAux, flip, hS]
    rw [e1, ih _ _ _ (by simp)]; simp

theorem runZ1 (l : List (M.Γ M.k₀)) (v : M.σ) (w : Option Bool) (x : List Bool)
    (S : ∀ k, List (M.Γ k)) (hS : S M.k₀ = l) :
    Fs^[l.length + 1] (some (⟨some (.inr .Z1), (v, w), stk M [] [] x [] S⟩ : PC)) =
      some ⟨some (.inr .Z2), (v, none),
        stk M [] [] ((l.map e).reverse ++ x) [] (Function.update S M.k₀ [])⟩ := by
  induction l generalizing w x S with
  | nil =>
    have : Function.update S M.k₀ [] = S := by rw [← hS]; simp
    simp [TM2.step, pm, sZ1, TM2.stepAux, flip, hS, this]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .Z1), (v, w), stk M [] [] x [] S⟩ : PC)) =
        some ⟨some (.inr .Z1), (v, some (e b)),
          stk M [] [] (e b :: x) [] (Function.update S M.k₀ l)⟩ := by
      simp [TM2.step, pm, sZ1, TM2.stepAux, flip, hS]
    rw [e1, ih _ _ _ (by simp)]; simp

theorem runZ2 (l : List Bool) (v : M.σ) (w : Option Bool) (o : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .Z2), (v, w), stk M [] [] l o S⟩ : PC)) =
      some ⟨none, (v, none), stk M [] [] [] (l.reverse ++ o) S⟩ := by
  induction l generalizing w o with
  | nil => simp [TM2.step, pm, sZ2, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .Z2), (v, w), stk M [] [] (b :: l) o S⟩ : PC)) =
        some ⟨some (.inr .Z2), (v, some b), stk M [] [] l (b :: o) S⟩ := by
      simp [TM2.step, pm, sZ2, TM2.stepAux, flip]
    rw [e1, ih]; simp

end Runs

section Lift

variable {M : FinTM2} {e : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}

local notation "Fs" => flip bind (TM2.step (pm M e eo))

def liftC (c0 : List Bool) (c : M.Cfg) : PC (M := M) :=
  ⟨some (match c.l with | none => .inr .F | some l => .inl l), (c.var, none), stk M [] c0 [] [] c.stk⟩

theorem stepAux_lift (c0 : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (lift M q) (v, none) (stk M [] c0 [] [] S) = liftC c0 (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (lift M q) (v, none)
      (Function.update (stk M [] c0 [] [] S) (.inr k) (f v :: S k)) = _
    rw [upd_M]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (lift M q) (f v (S k).head?, none)
      (Function.update (stk M [] c0 [] [] S) (.inr k) (S k).tail) = _
    rw [upd_M]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftC c0 (cond (f v) _ _)
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem iterate_lift (c0 : List Bool) (n : ℕ) (c d : M.Cfg)
    (h : (flip bind (TM2.step M.m))^[n] (some c) = some d) :
    Fs^[n] (some (liftC c0 c)) = some (liftC c0 d) := by
  induction n generalizing c with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind (TM2.step M.m))^[n] none = some d at h
      rw [flip_bind_iterate_none] at h; cases h
    · change (flip bind (TM2.step M.m))^[n] (some (TM2.stepAux (M.m l) v S)) = some d at h
      change Fs^[n] (some (TM2.stepAux (lift M (M.m l)) (v, none) (stk M [] c0 [] [] S))) = _
      rw [stepAux_lift]
      exact ih _ h

/-- One round of the loop: run `M` on `y`, then move its output back to its input stack. -/
theorem round (g : List Bool → List Bool) (y : List Bool) (c : List Bool) (b : Bool) (w : Option Bool)
    (n : ℕ) (hM : (flip bind (TM2.step M.m))^[n] (some (initList M (y.map e.symm))) =
      some (haltList M ((g y).map eo.symm))) :
    Fs^[((g y).length + 1) + (((g y).length + 1) + (n + 1))]
      (some (⟨some (.inr .L), (M.initialState, w), stk M [] (b :: c) [] []
        (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ : PC)) =
      some ⟨some (.inr .L), (M.initialState, none), stk M [] c [] []
        (Function.update (fun _ => []) M.k₀ ((g y).map e.symm))⟩ := by
  have h1 := runL_some (e := e) (eo := eo) M.initialState w b c
    (Function.update (fun _ => []) M.k₀ (y.map e.symm))
  have h2 := iterate_lift (e := e) (eo := eo) c n _ _ hM
  have q1 : liftC c (initList M (y.map e.symm)) =
      (⟨some (.inl M.main), (M.initialState, none), stk M [] c [] []
        (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ : PC (M := M)) := by
    simp only [liftC, initList_stk]; rfl
  have q2 : liftC c (haltList M ((g y).map eo.symm)) =
      (⟨some (.inr .F), (M.initialState, none), stk M [] c [] []
        (Function.update (fun _ => []) M.k₁ ((g y).map eo.symm))⟩ : PC (M := M)) := by
    simp only [liftC, haltList_stk]; rfl
  rw [q1, q2] at h2
  have h3 := runF (e := e) (eo := eo) ((g y).map eo.symm) M.initialState none c []
    (Function.update (fun _ => []) M.k₁ ((g y).map eo.symm)) (by rw [Function.update_self])
  rw [List.append_nil, List.length_map, List.map_map, Function.update_idem,
    Function.update_eq_self_iff.2 rfl] at h3
  have hy : List.map (eo ∘ eo.symm) (g y) = g y := by
    conv_rhs => rw [← List.map_id (g y)]
    apply List.map_congr_left; intro b _; simp
  rw [hy] at h3
  have h4 := runXM (e := e) (eo := eo) (g y).reverse M.initialState none c (fun _ => [])
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at h4
  exact iter_chain (iter_chain (iter_chain h1 h2) h3) h4

/-- The loop: `j` rounds. -/
theorem loop (g : List Bool → List Bool) (R0 Lb : ℕ) (j : ℕ) : ∀ (y : List Bool) (w : Option Bool),
    (∀ i < j, ∃ n ≤ R0, (flip bind (TM2.step M.m))^[n] (some (initList M ((g^[i] y).map e.symm))) =
      some (haltList M ((g^[i + 1] y).map eo.symm))) →
    (∀ i < j, (g^[i + 1] y).length ≤ Lb) →
    ∃ s ≤ j * (2 * Lb + R0 + 3) + 1,
      Fs^[s] (some (⟨some (.inr .L), (M.initialState, w), stk M [] (List.replicate j true) [] []
        (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ : PC)) =
      some ⟨some (.inr .Z1), (M.initialState, none), stk M [] [] [] []
        (Function.update (fun _ => []) M.k₀ ((g^[j] y).map e.symm))⟩ := by
  induction j with
  | zero =>
    intro y w _ _
    exact ⟨1, by omega, runL_none _ _ _⟩
  | succ j ih =>
    intro y w hrun hlen
    obtain ⟨n, hn, hM⟩ := hrun 0 (by omega)
    simp only [Function.iterate_zero, id, zero_add, Function.iterate_one] at hM
    have hr := round (e := e) (eo := eo) g y (List.replicate j true) true w n hM
    obtain ⟨s, hs, hl⟩ := ih (g y) none
      (fun i hi => by
        obtain ⟨n', hn', h'⟩ := hrun (i + 1) (by omega)
        refine ⟨n', hn', ?_⟩
        rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply]; exact h')
      (fun i hi => by
        have := hlen (i + 1) (by omega)
        rwa [← Function.iterate_succ_apply])
    have hg1 : (g y).length ≤ Lb := by simpa using hlen 0 (by omega)
    refine ⟨_, ?_, (iter_chain hr hl).trans (by rw [← Function.iterate_succ_apply])⟩
    have : (j + 1) * (2 * Lb + R0 + 3) = j * (2 * Lb + R0 + 3) + (2 * Lb + R0 + 3) := by ring
    omega

end Lift

theorem initList_eq (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) (l : List Bool) :
    initList (tm M e eo) l =
      (⟨some (.inr .A), (M.initialState, none), stk M l [] [] [] (fun _ => [])⟩ : PC (M := M)) := by
  simp only [initList]; congr 1; funext k; rcases k with ((_ | _ | _ | _) | k) <;> rfl

theorem haltList_eq (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) (l : List Bool) :
    haltList (tm M e eo) l =
      (⟨none, (M.initialState, none), stk M [] [] [] l (fun _ => [])⟩ : PC (M := M)) := by
  simp only [haltList]; congr 1; funext k; rcases k with ((_ | _ | _ | _) | k) <;> rfl

end IterTM

/-- **Iteration combinator.** If `g` is polytime and `|g^[i] y| ≤ q(|y| + i)`, then
`1ᵗ 0 y ↦ g^[t] y` is polytime. -/
theorem iter_exists {g : List Bool → List Bool} (h : TM2ComputableInPolyTime strEnc strEnc g)
    (q : Polynomial ℕ) (hq : ∀ y i, (g^[i] y).length ≤ q.eval (y.length + i)) :
    ∃ h' : TM2ComputableInPolyTime strEnc strEnc (fun z => g^[lpN z] (lpX z)),
      h'.time = 3 * Polynomial.X + 6 + Polynomial.X * (2 * q + h.time.comp q + 3) + 2 * q := by
  let M := h.tm
  let e := h.inputAlphabet
  let eo := h.outputAlphabet
  let P := h.time
  refine ⟨{
    tm := IterTM.tm M e eo
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := 3 * Polynomial.X + 6 + Polynomial.X * (2 * q + P.comp q + 3) + 2 * q
    outputsFun := fun z => ?_ }, rfl⟩
  have hex : ∃ s ≤ 3 * z.length + 6 + z.length * (2 * q.eval z.length + P.eval (q.eval z.length) + 3) +
      2 * q.eval z.length,
      (flip bind (TM2.step (IterTM.pm M e eo)))^[s] (some (initList (IterTM.tm M e eo) z)) =
        some (haltList (IterTM.tm M e eo) (g^[lpN z] (lpX z))) := by
    set n := z.length
    set t := lpN z
    set y := lpX z
    have hl : t + y.length ≤ n := LoopTM.lp_len z
    set Q := q.eval n
    have hQ : ∀ i ≤ t, (g^[i] y).length ≤ Q := fun i hi =>
      (hq y i).trans (poly_eval_mono q (by omega))
    rw [IterTM.initList_eq, IterTM.haltList_eq]
    obtain ⟨w1, h1⟩ := IterTM.runA (e := e) (eo := eo) z 0 M.initialState none (fun _ => [])
    have h2 := IterTM.runB (e := e) (eo := eo) y M.initialState w1 (List.replicate (0 + t) true) []
      (fun _ => [])
    have h3 := IterTM.runXM (e := e) (eo := eo) (y.reverse ++ []) M.initialState none
      (List.replicate (0 + t) true) (fun _ => [])
    simp only [Nat.zero_add, List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2 h3
    have h3' : (flip bind (TM2.step (IterTM.pm M e eo)))^[y.length + 1]
        (some ⟨some (.inr .XM), (M.initialState, none),
          IterTM.stk M [] (List.replicate t true) y.reverse [] (fun _ => [])⟩) =
        some ⟨some (.inr .L), (M.initialState, none), IterTM.stk M [] (List.replicate t true) [] []
          (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ := by
      rw [h3]
    obtain ⟨s, hs, h4⟩ := IterTM.loop (M := M) (e := e) (eo := eo) g (P.eval Q) Q t y none
      (fun i hi => by
        have hx := h.outputsFun (g^[i] y)
        have ev := hx.evals_in_steps
        simp only [Option.map_some] at ev
        refine ⟨hx.steps, ?_, ?_⟩
        · have := hx.steps_le_m
          simp only [strEnc] at this
          exact this.trans (poly_eval_mono P (hQ i (by omega)))
        · rw [Function.iterate_succ_apply']; exact ev)
      (fun i hi => hQ (i + 1) (by omega))
    have h5 := IterTM.runZ1 (e := e) (eo := eo) ((g^[t] y).map e.symm) M.initialState none []
      (Function.update (fun _ => []) M.k₀ ((g^[t] y).map e.symm)) (by rw [Function.update_self])
    rw [List.append_nil, List.length_map, List.map_map, Function.update_idem,
      Function.update_eq_self_iff.2 rfl] at h5
    have hy : List.map (e ∘ e.symm) (g^[t] y) = g^[t] y := by
      conv_rhs => rw [← List.map_id (g^[t] y)]
      apply List.map_congr_left; intro b _; simp
    rw [hy] at h5
    have h6 := IterTM.runZ2 (e := e) (eo := eo) (g^[t] y).reverse M.initialState none [] (fun _ => [])
    rw [List.reverse_reverse, List.append_nil, List.length_reverse] at h6
    have := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain h1 h2) h3') h4) h5) h6
    refine ⟨_, ?_, this⟩
    have hyt := hQ t le_rfl
    have hm : t * (2 * Q + P.eval Q + 3) ≤ n * (2 * Q + P.eval Q + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have : n = z.length := rfl
    omega
  exact
    { steps := Classical.choose hex
      evals_in_steps := by
        erw [List.map_id, List.map_id, Option.map_some]
        exact (Classical.choose_spec hex).2
      steps_le_m := by
        have := (Classical.choose_spec hex).1
        simp only [strEnc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_ofNat, Polynomial.eval_comp, Polynomial.eval_natCast]
        simpa [strEnc] using this }

/-- **Iteration combinator.** If `g` is polytime and `|g^[i] y| ≤ q(|y| + i)`, then
`1ᵗ 0 y ↦ g^[t] y` is polytime. -/
theorem PS.iter {g : List Bool → List Bool} (hg : PS g) (q : Polynomial ℕ)
    (hq : ∀ y i, (g^[i] y).length ≤ q.eval (y.length + i)) :
    PS (fun z => g^[lpN z] (lpX z)) := by
  obtain ⟨h⟩ := hg
  exact ⟨(iter_exists h q hq).choose⟩

end PvnpReal
