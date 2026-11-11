/-
  PvnpReal.PairMap — a machine that applies a polytime bit-string function to the first
  component of a verifier input: `x # w ↦ f(x) # w`.
-/
import PvnpReal.Closure

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

namespace PairMap

open TM2.Stmt

inductive PK | I | X | W | O
  deriving DecidableEq

instance : Fintype PK := ⟨{.I, .X, .W, .O}, fun k => by cases k <;> simp⟩

inductive PL | A | B | D | E | F | G
  deriving DecidableEq

instance : Fintype PL := ⟨{.A, .B, .D, .E, .F, .G}, fun k => by cases k <;> simp⟩

section Defs

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

abbrev K := PK ⊕ M.K

abbrev Γ : K M → Type
  | .inl .X => Bool
  | .inl _ => Option Bool
  | .inr k => M.Γ k

abbrev Λ := M.Λ ⊕ PL
abbrev σ := M.σ × Option (Option Bool)

def stk (i : List (Option Bool)) (x : List Bool) (w o : List (Option Bool))
    (S : ∀ k, List (M.Γ k)) : ∀ k, List (Γ M k)
  | .inl .I => i
  | .inl .X => x
  | .inl .W => w
  | .inl .O => o
  | .inr k => S k

variable {M}

@[simp] theorem stk_I (i x w o S) : stk M i x w o S (.inl .I) = i := rfl
@[simp] theorem stk_X (i x w o S) : stk M i x w o S (.inl .X) = x := rfl
@[simp] theorem stk_W (i x w o S) : stk M i x w o S (.inl .W) = w := rfl
@[simp] theorem stk_O (i x w o S) : stk M i x w o S (.inl .O) = o := rfl
@[simp] theorem stk_M (i x w o S) (k : M.K) : stk M i x w o S (.inr k) = S k := rfl

@[simp] theorem upd_I (i x w o S) (i' : List (Option Bool)) :
    Function.update (stk M i x w o S) (.inl .I) i' = stk M i' x w o S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_self]; rfl
  all_goals (rw [Function.update_of_ne (by simp)]; rfl)

@[simp] theorem upd_X (i x w o S) (x' : List Bool) :
    Function.update (stk M i x w o S) (.inl .X) x' = stk M i x' w o S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals (rw [Function.update_of_ne (by simp)]; rfl)

@[simp] theorem upd_W (i x w o S) (w' : List (Option Bool)) :
    Function.update (stk M i x w o S) (.inl .W) w' = stk M i x w' o S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals (rw [Function.update_of_ne (by simp)]; rfl)

@[simp] theorem upd_O (i x w o S) (o' : List (Option Bool)) :
    Function.update (stk M i x w o S) (.inl .O) o' = stk M i x w o' S := by
  funext j; rcases j with ((_ | _ | _ | _) | j)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

@[simp] theorem upd_M (i x w o S) (k : M.K) (l : List (M.Γ k)) :
    Function.update (stk M i x w o S) (.inr k) l = stk M i x w o (Function.update S k l) := by
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
  | .halt => goto (fun _ => .inr .D)

def isSS : Option (Option Bool) → Bool
  | some (some _) => true
  | _ => false

def getB : Option (Option Bool) → Bool
  | some (some b) => b
  | _ => false

def sA : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .I) (fun s o => (s.1, o)) (branch (fun s => isSS s.2)
    (push (.inl .X) (fun s => getB s.2) (goto fun _ => .inr .A)) (goto fun _ => .inr .B))

def sB : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .X) (fun s o => (s.1, o.map some)) (branch (fun s => s.2.isSome)
    (push (.inr M.k₀) (fun s => e.symm (getB s.2)) (goto fun _ => .inr .B))
    (goto fun _ => .inl M.main))

def sD : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .I) (fun s o => (s.1, o)) (branch (fun s => s.2.isSome)
    (push (.inl .W) (fun s => s.2.getD none) (goto fun _ => .inr .D)) (goto fun _ => .inr .E))

def sE : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .W) (fun s o => (s.1, o)) (branch (fun s => s.2.isSome)
    (push (.inl .O) (fun s => s.2.getD none) (goto fun _ => .inr .E))
    (push (.inl .O) (fun _ => none) (goto fun _ => .inr .F)))

def sF : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inr M.k₁) (fun s o => (s.1, o.map (fun g => some (eo g)))) (branch (fun s => s.2.isSome)
    (push (.inl .X) (fun s => getB s.2) (goto fun _ => .inr .F)) (goto fun _ => .inr .G))

def sG : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  pop (.inl .X) (fun s o => (s.1, o.map some)) (branch (fun s => s.2.isSome)
    (push (.inl .O) (fun s => s.2.getD none) (goto fun _ => .inr .G)) halt)

def pm : Λ M → TM2.Stmt (Γ M) (Λ M) (σ M)
  | .inl l => lift M (M.m l)
  | .inr .A => sA M
  | .inr .B => sB M e
  | .inr .D => sD M
  | .inr .E => sE M
  | .inr .F => sF M eo
  | .inr .G => sG M

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
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := pm M e eo

end Defs

section Runs

variable {M : FinTM2} {e : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}

local notation "Fs" => flip bind (TM2.step (pm M e eo))

abbrev PC := TM2.Cfg (Γ M) (Λ M) (σ M)

theorem runA (x : List Bool) (r : List (Option Bool)) (v : M.σ) (t : Option (Option Bool))
    (X : List Bool) (W O : List (Option Bool)) (S : ∀ k, List (M.Γ k)) :
    Fs^[x.length + 1] (some (⟨some (.inr .A), (v, t), stk M (x.map some ++ none :: r) X W O S⟩ : PC)) =
      some ⟨some (.inr .B), (v, some none), stk M r (x.reverse ++ X) W O S⟩ := by
  induction x generalizing t X with
  | nil => simp [TM2.step, pm, sA, TM2.stepAux, isSS, flip]
  | cons b x ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .A), (v, t), stk M ((b :: x).map some ++ none :: r) X W O S⟩ : PC)) =
        some ⟨some (.inr .A), (v, some (some b)), stk M (x.map some ++ none :: r) (b :: X) W O S⟩ := by
      simp [TM2.step, pm, sA, TM2.stepAux, isSS, getB, flip]
    rw [e1, ih]; simp

theorem runB (l : List Bool) (v : M.σ) (t : Option (Option Bool)) (i W O : List (Option Bool))
    (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .B), (v, t), stk M i l W O S⟩ : PC)) =
      some ⟨some (.inl M.main), (v, none),
        stk M i [] W O (Function.update S M.k₀ (l.reverse.map e.symm ++ S M.k₀))⟩ := by
  induction l generalizing t S with
  | nil => simp [TM2.step, pm, sB, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .B), (v, t), stk M i (b :: l) W O S⟩ : PC)) =
        some ⟨some (.inr .B), (v, some (some b)),
          stk M i l W O (Function.update S M.k₀ (e.symm b :: S M.k₀))⟩ := by
      simp [TM2.step, pm, sB, TM2.stepAux, getB, flip]
    rw [e1, ih]; simp

theorem runD (r : List (Option Bool)) (v : M.σ) (t : Option (Option Bool)) (X : List Bool)
    (W O : List (Option Bool)) (S : ∀ k, List (M.Γ k)) :
    Fs^[r.length + 1] (some (⟨some (.inr .D), (v, t), stk M r X W O S⟩ : PC)) =
      some ⟨some (.inr .E), (v, none), stk M [] X (r.reverse ++ W) O S⟩ := by
  induction r generalizing t W with
  | nil => simp [TM2.step, pm, sD, TM2.stepAux, flip]
  | cons b r ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .D), (v, t), stk M (b :: r) X W O S⟩ : PC)) =
        some ⟨some (.inr .D), (v, some b), stk M r X (b :: W) O S⟩ := by
      simp [TM2.step, pm, sD, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem runE (l : List (Option Bool)) (v : M.σ) (t : Option (Option Bool)) (i : List (Option Bool))
    (X : List Bool) (O : List (Option Bool)) (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .E), (v, t), stk M i X l O S⟩ : PC)) =
      some ⟨some (.inr .F), (v, none), stk M i X [] (none :: (l.reverse ++ O)) S⟩ := by
  induction l generalizing t O with
  | nil => simp [TM2.step, pm, sE, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .E), (v, t), stk M i X (b :: l) O S⟩ : PC)) =
        some ⟨some (.inr .E), (v, some b), stk M i X l (b :: O) S⟩ := by
      simp [TM2.step, pm, sE, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem runF (l : List (M.Γ M.k₁)) (v : M.σ) (t : Option (Option Bool)) (i : List (Option Bool))
    (X : List Bool) (W O : List (Option Bool)) (S : ∀ k, List (M.Γ k)) (hS : S M.k₁ = l) :
    Fs^[l.length + 1] (some (⟨some (.inr .F), (v, t), stk M i X W O S⟩ : PC)) =
      some ⟨some (.inr .G), (v, none),
        stk M i ((l.map eo).reverse ++ X) W O (Function.update S M.k₁ [])⟩ := by
  induction l generalizing t X S with
  | nil =>
    have : Function.update S M.k₁ [] = S := by rw [← hS]; simp
    simp [TM2.step, pm, sF, TM2.stepAux, flip, hS, this]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .F), (v, t), stk M i X W O S⟩ : PC)) =
        some ⟨some (.inr .F), (v, some (some (eo b))),
          stk M i (eo b :: X) W O (Function.update S M.k₁ l)⟩ := by
      simp [TM2.step, pm, sF, TM2.stepAux, getB, flip, hS]
    rw [e1, ih _ _ _ (by simp)]; simp

theorem runG (l : List Bool) (v : M.σ) (t : Option (Option Bool)) (i W O : List (Option Bool))
    (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .G), (v, t), stk M i l W O S⟩ : PC)) =
      some ⟨none, (v, none), stk M i [] W (l.reverse.map some ++ O) S⟩ := by
  induction l generalizing t O with
  | nil => simp [TM2.step, pm, sG, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .G), (v, t), stk M i (b :: l) W O S⟩ : PC)) =
        some ⟨some (.inr .G), (v, some (some b)), stk M i l W (some b :: O) S⟩ := by
      simp [TM2.step, pm, sG, TM2.stepAux, flip]
    rw [e1, ih]; simp

end Runs


section Lift

variable {M : FinTM2} {e : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}

local notation "Fs" => flip bind (TM2.step (pm M e eo))

def liftC (i : List (Option Bool)) (x : List Bool) (w o : List (Option Bool)) (c : M.Cfg) : PC (M := M) :=
  ⟨some (match c.l with | none => .inr .D | some l => .inl l), (c.var, none), stk M i x w o c.stk⟩

theorem stepAux_lift (i : List (Option Bool)) (x : List Bool) (w o : List (Option Bool))
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (lift M q) (v, none) (stk M i x w o S) = liftC i x w o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (lift M q) (v, none)
      (Function.update (stk M i x w o S) (.inr k) (f v :: S k)) = _
    rw [upd_M]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (lift M q) (f v (S k).head?, none)
      (Function.update (stk M i x w o S) (.inr k) (S k).tail) = _
    rw [upd_M]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftC i x w o (cond (f v) _ _)
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem iterate_lift (i : List (Option Bool)) (x : List Bool) (w o : List (Option Bool))
    (n : ℕ) (c d : M.Cfg) (h : (flip bind (TM2.step M.m))^[n] (some c) = some d) :
    Fs^[n] (some (liftC i x w o c)) = some (liftC i x w o d) := by
  induction n generalizing c with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind (TM2.step M.m))^[n] none = some d at h
      rw [flip_bind_iterate_none] at h; cases h
    · change (flip bind (TM2.step M.m))^[n] (some (TM2.stepAux (M.m l) v S)) = some d at h
      change Fs^[n] (some (TM2.stepAux (lift M (M.m l)) (v, none) (stk M i x w o S))) = _
      rw [stepAux_lift]
      exact ih _ h

end Lift

theorem initList_eq (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
    (l : List (Option Bool)) :
    initList (tm M e eo) l =
      (⟨some (.inr .A), (M.initialState, none), stk M l [] [] [] (fun _ => [])⟩ : PC (M := M)) := by
  simp only [initList]; congr 1; funext k; rcases k with ((_ | _ | _ | _) | k) <;> rfl

theorem haltList_eq (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)
    (l : List (Option Bool)) :
    haltList (tm M e eo) l =
      (⟨none, (M.initialState, none), stk M [] [] [] l (fun _ => [])⟩ : PC (M := M)) := by
  simp only [haltList]; congr 1; funext k; rcases k with ((_ | _ | _ | _) | k) <;> rfl

theorem pm_run (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) (x w y : List Bool) (n : ℕ)
    (h1 : (flip bind (TM2.step M.m))^[n] (some (initList M (x.map e.symm))) =
      some (haltList M (y.map eo.symm))) :
    (flip bind (TM2.step (pm M e eo)))^[(y.length + 1) + ((y.length + 1) + ((w.length + 1) +
        ((w.length + 1) + (n + ((x.length + 1) + (x.length + 1))))))]
      (some (⟨some (.inr .A), (M.initialState, none),
        stk M (x.map some ++ none :: w.map some) [] [] [] (fun _ => [])⟩ : PC (M := M))) =
      some ⟨none, (M.initialState, none),
        stk M [] [] [] (y.map some ++ none :: w.map some) (fun _ => [])⟩ := by
  have hA := runA (e := e) (eo := eo) x (w.map some) M.initialState none [] [] [] (fun _ => [])
  rw [List.append_nil] at hA
  have hB := runB (e := e) (eo := eo) x.reverse M.initialState (some none) (w.map some) [] []
    (fun _ => [])
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at hB
  have hC := iterate_lift (e := e) (eo := eo) (w.map some) [] [] [] _ _ _ h1
  have eC1 : liftC (w.map some) [] [] [] (initList M (x.map e.symm)) =
      (⟨some (.inl M.main), (M.initialState, none), stk M (w.map some) [] [] []
        (Function.update (fun _ => []) M.k₀ (x.map e.symm))⟩ : PC (M := M)) := by
    simp only [liftC, initList_stk]; rfl
  have eC2 : liftC (w.map some) [] [] [] (haltList M (y.map eo.symm)) =
      (⟨some (.inr .D), (M.initialState, none), stk M (w.map some) [] [] []
        (Function.update (fun _ => []) M.k₁ (y.map eo.symm))⟩ : PC (M := M)) := by
    simp only [liftC, haltList_stk]; rfl
  rw [eC1, eC2] at hC
  have hD := runD (e := e) (eo := eo) (w.map some) M.initialState none [] [] []
    (Function.update (fun _ => []) M.k₁ (y.map eo.symm))
  rw [List.append_nil, List.length_map] at hD
  have hE := runE (e := e) (eo := eo) (w.map some).reverse M.initialState none [] [] []
    (Function.update (fun _ => []) M.k₁ (y.map eo.symm))
  rw [List.reverse_reverse, List.append_nil, List.length_reverse, List.length_map] at hE
  have hF := runF (e := e) (eo := eo) (y.map eo.symm) M.initialState none [] [] []
    (none :: w.map some) (Function.update (fun _ => []) M.k₁ (y.map eo.symm))
    (by rw [Function.update_self])
  rw [List.append_nil, List.length_map, List.map_map] at hF
  have hy : List.map (eo ∘ eo.symm) y = y := by
    conv_rhs => rw [← List.map_id y]
    apply List.map_congr_left; intro b _; simp
  rw [hy, Function.update_idem, Function.update_eq_self_iff.2 rfl] at hF
  have hG := runG (e := e) (eo := eo) y.reverse M.initialState none [] [] (none :: w.map some)
    (fun _ => [])
  rw [List.reverse_reverse, List.length_reverse] at hG
  exact iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain hA hB) hC) hD) hE)
    hF) hG

end PairMap

/-- **Apply a polytime function to the first component of a verifier input**:
`x # w ↦ f(x) # w` is polynomial-time (as a `pairEnc → pairEnc` machine). -/
noncomputable def pairMapComputable {f : List Bool → List Bool}
    (h : TM2ComputableInPolyTime strEnc strEnc f) :
    TM2ComputableInPolyTime pairEnc pairEnc (fun p : List Bool × List Bool => (f p.1, p.2)) where
  tm := PairMap.tm h.tm h.inputAlphabet h.outputAlphabet
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 6 + (1 + 2 * (pushTotal h.tm : Polynomial ℕ)) * h.time
  outputsFun p :=
    { steps := ((f p.1).length + 1) + (((f p.1).length + 1) + ((p.2.length + 1) +
          ((p.2.length + 1) + ((h.outputsFun p.1).steps + ((p.1.length + 1) + (p.1.length + 1))))))
      evals_in_steps := by
        have e1 := (h.outputsFun p.1).evals_in_steps
        simp only [Option.map_some] at e1
        erw [List.map_id, List.map_id, PairMap.initList_eq]
        exact (PairMap.pm_run h.tm h.inputAlphabet h.outputAlphabet p.1 p.2 (f p.1) _ e1).trans
          (congrArg some (PairMap.haltList_eq h.tm h.inputAlphabet h.outputAlphabet _).symm)
      steps_le_m := by
        have hs := (h.outputsFun p.1).steps_le_m
        have hlen := outLen_bound h p.1
        have hN : p.1.length ≤ (pairEnc p).length := by simp [pairEnc]
        have hm := poly_eval_mono h.time hN
        have hC := Nat.mul_le_mul_left (pushTotal h.tm) hm
        simp only [strEnc] at hs hlen
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id, Polynomial.eval_one]
        have hP : (pairEnc p).length = p.1.length + 1 + p.2.length := by simp [pairEnc]; omega
        rw [hP] at hm hC ⊢
        nlinarith }

end PvnpReal
