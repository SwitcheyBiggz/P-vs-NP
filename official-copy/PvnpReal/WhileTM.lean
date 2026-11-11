/-
  PvnpReal.WhileTM — a **while-loop machine with a space proof**.

  Given a machine `M` for `g`, the loop machine starts from the state `true :: false :: x`, and while
  the state begins with `true` it replaces the state `y` by `g y` (running a lifted copy of `M`);
  when the state no longer begins with `true`, it outputs the state's tail. Unlike `PS.iter`
  there is no unary counter: any counter lives (in binary) inside the state, so the space used
  is `n + Lb + C·(round length)` where `Lb` bounds the state lengths — polynomial even when the
  number of rounds is exponential.
-/
import PvnpReal.IterTM
import PvnpReal.Space

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

namespace WhileTM

open TM2.Stmt IterTM

section Defs

variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

def sP0 : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  push (.inl .X) (fun _ => true) (push (.inl .X) (fun _ => false) (goto fun _ => .inr .B))

def sLW : TM2.Stmt (Γ M) (Λ M) (σ M) :=
  peek (.inr M.k₀) (fun s o => (s.1, o.map e)) (branch (fun s => isT s.2)
    (load (fun s => (s.1, none)) (goto fun _ => .inl M.main))
    (pop (.inr M.k₀) (fun s _ => (s.1, none)) (goto fun _ => .inr .Z1)))

def pmW : Λ M → TM2.Stmt (Γ M) (Λ M) (σ M)
  | .inl l => lift M (M.m l)
  | .inr .A => sP0 M
  | .inr .B => sB M
  | .inr .XM => sXM M e
  | .inr .L => sLW M e
  | .inr .F => sF M eo
  | .inr .Z1 => sZ1 M e
  | .inr .Z2 => sZ2 M

def tmW : FinTM2 where
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
  m := pmW M e eo

end Defs

section Runs

variable {M : FinTM2} {e : M.Γ M.k₀ ≃ Bool} {eo : M.Γ M.k₁ ≃ Bool}

local notation "Fs" => flip bind (TM2.step (pmW M e eo))

theorem runP0 (v : M.σ) (w : Option Bool) (z : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[1] (some (⟨some (.inr .A), (v, w), stk M z [] [] [] S⟩ : PC)) =
      some ⟨some (.inr .B), (v, w), stk M z [] [false, true] [] S⟩ := by
  simp [TM2.step, pmW, sP0, TM2.stepAux, flip]

theorem runB (y : List Bool) (v : M.σ) (w : Option Bool) (c x : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[y.length + 1] (some (⟨some (.inr .B), (v, w), stk M y c x [] S⟩ : PC)) =
      some ⟨some (.inr .XM), (v, none), stk M [] c (y.reverse ++ x) [] S⟩ := by
  induction y generalizing w x with
  | nil => simp [TM2.step, pmW, sB, TM2.stepAux, flip]
  | cons b y ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .B), (v, w), stk M (b :: y) c x [] S⟩ : PC)) =
        some ⟨some (.inr .B), (v, some b), stk M y c (b :: x) [] S⟩ := by
      simp [TM2.step, pmW, sB, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem runXM (l : List Bool) (v : M.σ) (w : Option Bool) (c : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .XM), (v, w), stk M [] c l [] S⟩ : PC)) =
      some ⟨some (.inr .L), (v, none), stk M [] c [] []
        (Function.update S M.k₀ (l.reverse.map e.symm ++ S M.k₀))⟩ := by
  induction l generalizing w S with
  | nil => simp [TM2.step, pmW, sXM, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .XM), (v, w), stk M [] c (b :: l) [] S⟩ : PC)) =
        some ⟨some (.inr .XM), (v, some b), stk M [] c l []
          (Function.update S M.k₀ (e.symm b :: S M.k₀))⟩ := by
      simp [TM2.step, pmW, sXM, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem runL_true (v : M.σ) (w : Option Bool) (y : List Bool) (hy : y.head? = some true) :
    Fs^[1] (some (⟨some (.inr .L), (v, w), stk M [] [] [] []
      (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ : PC)) =
      some ⟨some (.inl M.main), (v, none), stk M [] [] [] []
        (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ := by
  obtain ⟨y', rfl⟩ : ∃ y', y = true :: y' := by
    cases y with
    | nil => simp at hy
    | cons b y' => simp at hy; exact ⟨y', by rw [hy]⟩
  simp [TM2.step, pmW, sLW, TM2.stepAux, flip, isT]

theorem runL_false (v : M.σ) (w : Option Bool) (y : List Bool) (hy : y.head? ≠ some true) :
    Fs^[1] (some (⟨some (.inr .L), (v, w), stk M [] [] [] []
      (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ : PC)) =
      some ⟨some (.inr .Z1), (v, none), stk M [] [] [] []
        (Function.update (fun _ => []) M.k₀ (y.tail.map e.symm))⟩ := by
  cases y with
  | nil => simp [TM2.step, pmW, sLW, TM2.stepAux, flip, isT]
  | cons b y' =>
    cases b
    · simp [TM2.step, pmW, sLW, TM2.stepAux, flip, isT]
    · simp at hy

theorem runF (l : List (M.Γ M.k₁)) (v : M.σ) (w : Option Bool) (c x : List Bool)
    (S : ∀ k, List (M.Γ k)) (hS : S M.k₁ = l) :
    Fs^[l.length + 1] (some (⟨some (.inr .F), (v, w), stk M [] c x [] S⟩ : PC)) =
      some ⟨some (.inr .XM), (v, none),
        stk M [] c ((l.map eo).reverse ++ x) [] (Function.update S M.k₁ [])⟩ := by
  induction l generalizing w x S with
  | nil =>
    have : Function.update S M.k₁ [] = S := by rw [← hS]; simp
    simp [TM2.step, pmW, sF, TM2.stepAux, flip, hS, this]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .F), (v, w), stk M [] c x [] S⟩ : PC)) =
        some ⟨some (.inr .F), (v, some (eo b)),
          stk M [] c (eo b :: x) [] (Function.update S M.k₁ l)⟩ := by
      simp [TM2.step, pmW, sF, TM2.stepAux, flip, hS]
    rw [e1, ih _ _ _ (by simp)]; simp

theorem runZ1 (l : List (M.Γ M.k₀)) (v : M.σ) (w : Option Bool) (x : List Bool)
    (S : ∀ k, List (M.Γ k)) (hS : S M.k₀ = l) :
    Fs^[l.length + 1] (some (⟨some (.inr .Z1), (v, w), stk M [] [] x [] S⟩ : PC)) =
      some ⟨some (.inr .Z2), (v, none),
        stk M [] [] ((l.map e).reverse ++ x) [] (Function.update S M.k₀ [])⟩ := by
  induction l generalizing w x S with
  | nil =>
    have : Function.update S M.k₀ [] = S := by rw [← hS]; simp
    simp [TM2.step, pmW, sZ1, TM2.stepAux, flip, hS, this]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .Z1), (v, w), stk M [] [] x [] S⟩ : PC)) =
        some ⟨some (.inr .Z1), (v, some (e b)),
          stk M [] [] (e b :: x) [] (Function.update S M.k₀ l)⟩ := by
      simp [TM2.step, pmW, sZ1, TM2.stepAux, flip, hS]
    rw [e1, ih _ _ _ (by simp)]; simp

theorem runZ2 (l : List Bool) (v : M.σ) (w : Option Bool) (o : List Bool) (S : ∀ k, List (M.Γ k)) :
    Fs^[l.length + 1] (some (⟨some (.inr .Z2), (v, w), stk M [] [] l o S⟩ : PC)) =
      some ⟨none, (v, none), stk M [] [] [] (l.reverse ++ o) S⟩ := by
  induction l generalizing w o with
  | nil => simp [TM2.step, pmW, sZ2, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e1 : Fs (some (⟨some (.inr .Z2), (v, w), stk M [] [] (b :: l) o S⟩ : PC)) =
        some ⟨some (.inr .Z2), (v, some b), stk M [] [] l (b :: o) S⟩ := by
      simp [TM2.step, pmW, sZ2, TM2.stepAux, flip]
    rw [e1, ih]; simp

theorem iterate_liftW (c0 : List Bool) (n : ℕ) (c d : M.Cfg)
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
      rw [IterTM.stepAux_lift]
      exact ih _ h

/-- The `L`-configuration holding state `y`. -/
def Lcfg (M : FinTM2) (y : List Bool) (e : M.Γ M.k₀ ≃ Bool) : PC (M := M) :=
  ⟨some (.inr .L), (M.initialState, none), stk M [] [] [] []
    (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩

/-- One round: state `y` (starting with `true`) becomes `g y`. -/
theorem roundW (g : List Bool → List Bool) (y : List Bool) (hy : y.head? = some true)
    (n : ℕ) (hM : (flip bind (TM2.step M.m))^[n] (some (initList M (y.map e.symm))) =
      some (haltList M ((g y).map eo.symm))) :
    Fs^[((g y).length + 1) + (((g y).length + 1) + (n + 1))] (some (Lcfg M y e)) =
      some (Lcfg M (g y) e) := by
  have h1 := runL_true (e := e) (eo := eo) M.initialState none y hy
  have h2 := iterate_liftW (e := e) (eo := eo) [] n _ _ hM
  have q1 : liftC [] (initList M (y.map e.symm)) =
      (⟨some (.inl M.main), (M.initialState, none), stk M [] [] [] []
        (Function.update (fun _ => []) M.k₀ (y.map e.symm))⟩ : PC (M := M)) := by
    simp only [liftC, initList_stk]; rfl
  have q2 : liftC [] (haltList M ((g y).map eo.symm)) =
      (⟨some (.inr .F), (M.initialState, none), stk M [] [] [] []
        (Function.update (fun _ => []) M.k₁ ((g y).map eo.symm))⟩ : PC (M := M)) := by
    simp only [liftC, haltList_stk]; rfl
  rw [q1, q2] at h2
  have h3 := runF (e := e) (eo := eo) ((g y).map eo.symm) M.initialState none [] []
    (Function.update (fun _ => []) M.k₁ ((g y).map eo.symm)) (by rw [Function.update_self])
  rw [List.append_nil, List.length_map, List.map_map, Function.update_idem,
    Function.update_eq_self_iff.2 rfl] at h3
  have hy' : List.map (eo ∘ eo.symm) (g y) = g y := by
    conv_rhs => rw [← List.map_id (g y)]
    apply List.map_congr_left; intro b _; simp
  rw [hy'] at h3
  have h4 := runXM (e := e) (eo := eo) (g y).reverse M.initialState none [] (fun _ => [])
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at h4
  exact iter_chain (iter_chain (iter_chain h1 h2) h3) h4

/-- Exit: a state not starting with `true` is output without its head. -/
theorem finishW (y : List Bool) (hy : y.head? ≠ some true) :
    Fs^[(y.tail.length + 1) + ((y.tail.length + 1) + 1)] (some (Lcfg M y e)) =
      some ⟨none, (M.initialState, none), stk M [] [] [] y.tail (fun _ => [])⟩ := by
  have h1 := runL_false (e := e) (eo := eo) M.initialState none y hy
  have h2 := runZ1 (e := e) (eo := eo) (y.tail.map e.symm) M.initialState none []
    (Function.update (fun _ => []) M.k₀ (y.tail.map e.symm)) (by rw [Function.update_self])
  rw [List.append_nil, List.length_map, List.map_map, Function.update_idem,
    Function.update_eq_self_iff.2 rfl] at h2
  have hy' : List.map (e ∘ e.symm) y.tail = y.tail := by
    conv_rhs => rw [← List.map_id y.tail]
    apply List.map_congr_left; intro b _; simp
  rw [hy'] at h2
  have h3 := runZ2 (e := e) (eo := eo) y.tail.reverse M.initialState none [] (fun _ => [])
  rw [List.reverse_reverse, List.append_nil, List.length_reverse] at h3
  exact iter_chain (iter_chain h1 h2) h3

/-- Start: input `z` becomes the `L`-configuration with state `true :: false :: z`. -/
theorem startW (z : List Bool) :
    Fs^[(z.length + 2 + 1) + ((z.length + 1) + 1)]
      (some (⟨some (.inr .A), (M.initialState, none), stk M z [] [] [] (fun _ => [])⟩ : PC)) =
      some (Lcfg M (true :: false :: z) e) := by
  have h1 := runP0 (e := e) (eo := eo) M.initialState none z (fun _ => [])
  have h2 := runB (e := e) (eo := eo) z M.initialState none [] [false, true] (fun _ => [])
  have h3 := runXM (e := e) (eo := eo) (z.reverse ++ [false, true]) M.initialState none []
    (fun _ => [])
  simp only [List.length_append, List.length_reverse, List.reverse_append, List.reverse_reverse,
    List.append_nil] at h3
  have := iter_chain (iter_chain h1 h2) h3
  simpa [Lcfg] using this

end Runs

theorem initList_eqW (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) (l : List Bool) :
    initList (tmW M e eo) l =
      (⟨some (.inr .A), (M.initialState, none), stk M l [] [] [] (fun _ => [])⟩ : PC (M := M)) := by
  simp only [initList]; congr 1; funext k; rcases k with ((_ | _ | _ | _) | k) <;> rfl

theorem haltList_eqW (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool) (l : List Bool) :
    haltList (tmW M e eo) l =
      (⟨none, (M.initialState, none), stk M [] [] [] l (fun _ => [])⟩ : PC (M := M)) := by
  simp only [haltList]; congr 1; funext k; rcases k with ((_ | _ | _ | _) | k) <;> rfl

end WhileTM

/-- **Space from checkpoints**: if a run starts at a good configuration, good configurations have
stacks `≤ B`, and from every good configuration the next good one is reached within `W` steps
(or the machine halts), then every configuration of the run has stacks `≤ B + C·W`. -/
theorem space_of_good (tm : FinTM2) (c0 : tm.Cfg) (Good : tm.Cfg → Prop) (B W : ℕ) (hW : 1 ≤ W)
    (h0 : Good c0) (hB : ∀ c, Good c → ∀ k, (c.stk k).length ≤ B)
    (hsucc : ∀ c, Good c → (∃ δ, 1 ≤ δ ∧ δ ≤ W ∧ ∃ d, (flip bind tm.step)^[δ] (some c) = some d ∧
      Good d) ∨ tm.step c = none) :
    ∀ t c, (flip bind tm.step)^[t] (some c0) = some c → ∀ k,
      (c.stk k).length ≤ B + pushTotal tm * W := by
  set F := flip bind tm.step
  have claim : ∀ t, F^[t] (some c0) ≠ none → ∃ τ ≤ t, t < τ + W ∧ ∃ c, F^[τ] (some c0) = some c ∧
      Good c := by
    intro t
    induction t with
    | zero => intro _; exact ⟨0, le_rfl, by omega, c0, rfl, h0⟩
    | succ t ih =>
      intro ht
      have ht' : F^[t] (some c0) ≠ none := by
        intro e; apply ht; rw [Function.iterate_succ_apply', e]; rfl
      obtain ⟨τ, hτ, hτW, c, hc, hgc⟩ := ih ht'
      by_cases hlt : t + 1 < τ + W
      · exact ⟨τ, by omega, hlt, c, hc, hgc⟩
      · rcases hsucc c hgc with ⟨δ, hδ1, hδW, d, hd, hgd⟩ | hnone
        · refine ⟨τ + δ, by omega, by omega, d, ?_, hgd⟩
          rw [add_comm, Function.iterate_add_apply, hc, hd]
        · exfalso; apply ht
          have e1 : F^[τ + 1] (some c0) = none := by
            rw [Function.iterate_succ_apply', hc]; exact hnone
          rw [show t + 1 = (t - τ) + (τ + 1) by omega, Function.iterate_add_apply, e1,
            flip_bind_iterate_none]
  intro t c hc k
  obtain ⟨τ, hτ, hτW, cτ, hcτ, hg⟩ := claim t (by rw [hc]; simp)
  have hrun : F^[t - τ] (some cτ) = some c := by
    rw [← hcτ, ← Function.iterate_add_apply, show t - τ + τ = t by omega]; exact hc
  have := iterate_len tm (t - τ) cτ c hrun B (hB cτ hg) k
  have : pushTotal tm * (t - τ) ≤ pushTotal tm * W := Nat.mul_le_mul_left _ (by omega)
  omega

end PvnpReal
