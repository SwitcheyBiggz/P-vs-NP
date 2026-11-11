/-
  PvnpReal.PSubsetNP — a real proof that P ⊆ NP in this model.

  Given a polynomial-time decider `M` for `L` (a Mathlib `FinTM2`), we build an actual
  verifier machine `verifierTM M` that reads `x # w`, and then:
    phase A: moves the bits of `x` onto a scratch stack (reversing them),
    phase B: throws away the witness `w`,
    phase C: moves the bits back onto `M`'s input stack (restoring the order),
  and then runs `M` itself, instruction by instruction (`liftStmt`).
  We prove the verifier outputs `f x` and runs in time `p(n) + 2n + 3`.
-/
import PvnpReal.Complexity

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

/-- Monotonicity of evaluation of natural-number polynomials. -/
theorem poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-- The three preprocessing phases of the verifier. -/
inductive Phase | A | B | C
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{Phase.A, Phase.B, Phase.C}, fun x => by cases x <;> simp⟩

section Construction

variable (M : FinTM2)

/-- Stacks: `none` = verifier input, `some none` = scratch, `some (some k)` = `M`'s stack `k`. -/
abbrev VK := Option (Option M.K)

abbrev VΓ : VK M → Type
  | none => Option Bool
  | some none => Bool
  | some (some k) => M.Γ k

abbrev VΛ := M.Λ ⊕ Phase
abbrev Vσ := M.σ × Option (Option Bool)

def dec : Option (Option Bool) → Bool
  | some (some b) => b
  | _ => false

def isBit : Option (Option Bool) → Bool
  | some (some _) => true
  | _ => false

/-- Run one of `M`'s instructions on the corresponding stacks of the verifier. -/
def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (VΓ M) (VΛ M) (Vσ M)
  | .push k f q => push (some (some k)) (fun s => f s.1) (liftStmt q)
  | .peek k f q => peek (some (some k)) (fun s o => (f s.1 o, s.2)) (liftStmt q)
  | .pop k f q => pop (some (some k)) (fun s o => (f s.1 o, s.2)) (liftStmt q)
  | .load a q => load (fun s => (a s.1, s.2)) (liftStmt q)
  | .branch f q₁ q₂ => branch (fun s => f s.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => goto (fun s => Sum.inl (f s.1))
  | .halt => halt

def phaseA : TM2.Stmt (VΓ M) (VΛ M) (Vσ M) :=
  pop none (fun s o => (s.1, o))
    (branch (fun s => isBit s.2)
      (push (some none) (fun s => dec s.2) (goto fun _ => Sum.inr Phase.A))
      (goto fun _ => Sum.inr Phase.B))

def phaseB : TM2.Stmt (VΓ M) (VΛ M) (Vσ M) :=
  pop none (fun s o => (s.1, o))
    (branch (fun s => s.2.isSome) (goto fun _ => Sum.inr Phase.B)
      (goto fun _ => Sum.inr Phase.C))

variable (e : M.Γ M.k₀ ≃ Bool)

def phaseC : TM2.Stmt (VΓ M) (VΛ M) (Vσ M) :=
  pop (some none) (fun s o => (s.1, o.map some))
    (branch (fun s => s.2.isSome)
      (push (some (some M.k₀)) (fun s => e.symm (dec s.2)) (goto fun _ => Sum.inr Phase.C))
      (goto fun _ => Sum.inl M.main))

def Vm : VΛ M → TM2.Stmt (VΓ M) (VΛ M) (Vσ M)
  | Sum.inl l => liftStmt M (M.m l)
  | Sum.inr Phase.A => phaseA M
  | Sum.inr Phase.B => phaseB M
  | Sum.inr Phase.C => phaseC M e

/-- The verifier machine. -/
def verifierTM : FinTM2 where
  K := VK M
  kDecidableEq := inferInstance
  kFin := @instFintypeOption _ (@instFintypeOption _ M.kFin)
  k₀ := none
  k₁ := some (some M.k₁)
  Γ := VΓ M
  Λ := VΛ M
  main := Sum.inr Phase.A
  ΛFin := @instFintypeSum _ _ M.ΛFin inferInstance
  σ := Vσ M
  initialState := (M.initialState, none)
  σFin := @instFintypeProd _ _ M.σFin inferInstance
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := Vm M e

/-- Build verifier stacks from (input, scratch, `M`'s stacks). -/
def mkStk (inp : List (Option Bool)) (tmp : List Bool) (S : ∀ k, List (M.Γ k)) :
    ∀ k, List (VΓ M k)
  | none => inp
  | some none => tmp
  | some (some k) => S k

theorem update_mkStk_inp (inp inp' : List (Option Bool)) (tmp : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk M inp tmp S) none inp' = mkStk M inp' tmp S := by
  funext j
  rcases j with _ | _ | j
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem update_mkStk_tmp (inp : List (Option Bool)) (tmp tmp' : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    Function.update (mkStk M inp tmp S) (some none) tmp' = mkStk M inp tmp' S := by
  funext j
  rcases j with _ | _ | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem update_mkStk_M (inp : List (Option Bool)) (tmp : List Bool)
    (S : ∀ k, List (M.Γ k)) (k : M.K) (x : List (M.Γ k)) :
    Function.update (mkStk M inp tmp S) (some (some k)) x =
      mkStk M inp tmp (Function.update S k x) := by
  funext j
  rcases j with _ | _ | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]

/-- Embed a configuration of `M` into the verifier (scratch and input stacks empty). -/
def liftCfg (c : M.Cfg) : TM2.Cfg (VΓ M) (VΛ M) (Vσ M) :=
  ⟨c.l.map Sum.inl, (c.var, none), mkStk M [] [] c.stk⟩

theorem stepAux_lift (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftStmt M q) (v, none) (mkStk M [] [] S) =
      liftCfg M (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (liftStmt M q) (v, none)
      (Function.update (mkStk M [] [] S) (some (some k)) (f v :: S k)) = _
    rw [update_mkStk_M]
    exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (liftStmt M q) (f v (S k).head?, none)
      (Function.update (mkStk M [] [] S) (some (some k)) (S k).tail) = _
    rw [update_mkStk_M]
    exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftCfg M (cond (f v) _ _)
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem step_lift (c : M.Cfg) :
    TM2.step (Vm M e) (liftCfg M c) = (TM2.step M.m c).map (liftCfg M) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftStmt M (M.m l)) (v, none) (mkStk M [] [] S)) = _
    rw [stepAux_lift]
    rfl

theorem iterate_lift (n : ℕ) (c : M.Cfg) :
    (flip bind (TM2.step (Vm M e)))^[n] (some (liftCfg M c)) =
      ((flip bind (TM2.step M.m))^[n] (some c)).map (liftCfg M) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    show (flip bind (TM2.step (Vm M e)))^[n] (TM2.step (Vm M e) (liftCfg M c)) =
      ((flip bind (TM2.step M.m))^[n] (TM2.step M.m c)).map (liftCfg M)
    rw [step_lift]
    cases h : TM2.step M.m c with
    | none =>
      exact (flip_bind_iterate_none _ n).trans
        (congrArg (Option.map (liftCfg M)) (flip_bind_iterate_none _ n)).symm
    | some c' => exact ih c'

/-! ### The preprocessing phases, step by step -/

theorem flip_bind_some {σ : Type} (f : σ → Option σ) (c : σ) :
    flip bind f (some c) = f c := rfl

theorem stepA_bit (s : Vσ M) (b : Bool) (inp : List (Option Bool)) (tmp : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.step (Vm M e) ⟨some (Sum.inr Phase.A), s, mkStk M (some b :: inp) tmp S⟩ =
      some ⟨some (Sum.inr Phase.A), (s.1, some (some b)), mkStk M inp (b :: tmp) S⟩ := by
  show some (TM2.stepAux (phaseA M) s _) = _
  simp only [phaseA, TM2.stepAux, mkStk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isBit, dec, Option.isSome_some, Option.isSome_none, Option.map_some,
    Option.map_none, Bool.cond_true, Bool.cond_false, update_mkStk_inp, update_mkStk_tmp,
    update_mkStk_M]

theorem stepA_sep (s : Vσ M) (inp : List (Option Bool)) (tmp : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.step (Vm M e) ⟨some (Sum.inr Phase.A), s, mkStk M (none :: inp) tmp S⟩ =
      some ⟨some (Sum.inr Phase.B), (s.1, some none), mkStk M inp tmp S⟩ := by
  show some (TM2.stepAux (phaseA M) s _) = _
  simp only [phaseA, TM2.stepAux, mkStk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isBit, dec, Option.isSome_some, Option.isSome_none, Option.map_some,
    Option.map_none, Bool.cond_true, Bool.cond_false, update_mkStk_inp, update_mkStk_tmp,
    update_mkStk_M]

theorem runA (x : List Bool) (s : Vσ M) (inp : List (Option Bool)) (tmp : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    (flip bind (TM2.step (Vm M e)))^[x.length + 1]
        (some ⟨some (Sum.inr Phase.A), s, mkStk M (x.map some ++ none :: inp) tmp S⟩) =
      some ⟨some (Sum.inr Phase.B), (s.1, some none), mkStk M inp (x.reverse ++ tmp) S⟩ := by
  induction x generalizing s tmp with
  | nil =>
    simp only [List.length_nil, zero_add, Function.iterate_one, List.map_nil, List.nil_append,
      List.reverse_nil]
    exact stepA_sep M e s inp tmp S
  | cons b x ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.map_cons, List.cons_append]
    rw [flip_bind_some]
    rw [stepA_bit, ih]
    simp

theorem stepB_cons (s : Vσ M) (a : Option Bool) (inp : List (Option Bool)) (tmp : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.step (Vm M e) ⟨some (Sum.inr Phase.B), s, mkStk M (a :: inp) tmp S⟩ =
      some ⟨some (Sum.inr Phase.B), (s.1, some a), mkStk M inp tmp S⟩ := by
  show some (TM2.stepAux (phaseB M) s _) = _
  simp only [phaseB, TM2.stepAux, mkStk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isBit, dec, Option.isSome_some, Option.isSome_none, Option.map_some,
    Option.map_none, Bool.cond_true, Bool.cond_false, update_mkStk_inp, update_mkStk_tmp,
    update_mkStk_M]

theorem stepB_nil (s : Vσ M) (tmp : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.step (Vm M e) ⟨some (Sum.inr Phase.B), s, mkStk M [] tmp S⟩ =
      some ⟨some (Sum.inr Phase.C), (s.1, none), mkStk M [] tmp S⟩ := by
  show some (TM2.stepAux (phaseB M) s _) = _
  simp only [phaseB, TM2.stepAux, mkStk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isBit, dec, Option.isSome_some, Option.isSome_none, Option.map_some,
    Option.map_none, Bool.cond_true, Bool.cond_false, update_mkStk_inp, update_mkStk_tmp,
    update_mkStk_M]

theorem runB (inp : List (Option Bool)) (s : Vσ M) (tmp : List Bool) (S : ∀ k, List (M.Γ k)) :
    (flip bind (TM2.step (Vm M e)))^[inp.length + 1]
        (some ⟨some (Sum.inr Phase.B), s, mkStk M inp tmp S⟩) =
      some ⟨some (Sum.inr Phase.C), (s.1, none), mkStk M [] tmp S⟩ := by
  induction inp generalizing s with
  | nil =>
    simp only [List.length_nil, zero_add, Function.iterate_one]
    exact stepB_nil M e s tmp S
  | cons a inp ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [flip_bind_some]
    rw [stepB_cons, ih]

theorem stepC_cons (s : Vσ M) (b : Bool) (tmp : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.step (Vm M e) ⟨some (Sum.inr Phase.C), s, mkStk M [] (b :: tmp) S⟩ =
      some ⟨some (Sum.inr Phase.C), (s.1, some (some b)),
        mkStk M [] tmp (Function.update S M.k₀ (e.symm b :: S M.k₀))⟩ := by
  show some (TM2.stepAux (phaseC M e) s _) = _
  simp only [phaseC, TM2.stepAux, mkStk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isBit, dec, Option.isSome_some, Option.isSome_none, Option.map_some,
    Option.map_none, Bool.cond_true, Bool.cond_false, update_mkStk_inp, update_mkStk_tmp,
    update_mkStk_M]

theorem stepC_nil (s : Vσ M) (S : ∀ k, List (M.Γ k)) :
    TM2.step (Vm M e) ⟨some (Sum.inr Phase.C), s, mkStk M [] [] S⟩ =
      some ⟨some (Sum.inl M.main), (s.1, none), mkStk M [] [] S⟩ := by
  show some (TM2.stepAux (phaseC M e) s _) = _
  simp only [phaseC, TM2.stepAux, mkStk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isBit, dec, Option.isSome_some, Option.isSome_none, Option.map_some,
    Option.map_none, Bool.cond_true, Bool.cond_false, update_mkStk_inp, update_mkStk_tmp,
    update_mkStk_M]

theorem runC (tmp : List Bool) (s : Vσ M) (S : ∀ k, List (M.Γ k)) :
    (flip bind (TM2.step (Vm M e)))^[tmp.length + 1]
        (some ⟨some (Sum.inr Phase.C), s, mkStk M [] tmp S⟩) =
      some ⟨some (Sum.inl M.main), (s.1, none),
        mkStk M [] [] (Function.update S M.k₀ (tmp.reverse.map e.symm ++ S M.k₀))⟩ := by
  induction tmp generalizing s S with
  | nil =>
    simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
      List.map_nil, List.nil_append, Function.update_eq_self]
    exact stepC_nil M e s S
  | cons b tmp ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [flip_bind_some]
    rw [stepC_cons, ih]
    simp [Function.update_idem, Function.update_self]

theorem initList_verifier (l : List (Option Bool)) :
    initList (verifierTM M e) (List.map (Equiv.refl (Option Bool)).invFun l) =
      ⟨some (Sum.inr Phase.A), (M.initialState, none), mkStk M l [] (fun _ => [])⟩ := by
  simp only [initList]
  congr 1
  funext j
  rcases j with _ | _ | j
  · exact List.map_id l
  · rfl
  · rfl

theorem initList_stk (l : List (M.Γ M.k₀)) :
    (initList M l).stk = Function.update (fun _ => []) M.k₀ l := by
  funext j
  by_cases h : j = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_verifier (s : List (M.Γ M.k₁)) :
    haltList (verifierTM M e) s = liftCfg M (haltList M s) := by
  simp only [haltList, liftCfg]
  congr 1
  funext j
  rcases j with _ | _ | j
  · rfl
  · rfl
  · by_cases h : j = M.k₁
    · subst h; simp [verifierTM, mkStk]; rfl
    · simp [verifierTM, mkStk, h]

theorem start_eq (l : List (M.Γ M.k₀)) :
    (⟨some (Sum.inl M.main), (M.initialState, none),
        mkStk M [] [] (Function.update (fun _ => []) M.k₀ l)⟩ :
        TM2.Cfg (VΓ M) (VΛ M) (Vσ M)) =
      liftCfg M (initList M l) := by
  simp only [liftCfg, initList_stk]
  rfl

/-- The whole run of the verifier on `x # w`: preprocessing, then `M` itself. -/
theorem verifier_run (x w : List Bool) (n : ℕ) (out : List (M.Γ M.k₁))
    (hM : (flip bind (TM2.step M.m))^[n] (some (initList M (List.map e.symm x))) =
      some (haltList M out)) :
    (flip bind (TM2.step (Vm M e)))^[n + ((x.length + 1) + ((w.length + 1) + (x.length + 1)))]
        (some ⟨some (Sum.inr Phase.A), (M.initialState, none),
          mkStk M (x.map some ++ none :: w.map some) [] (fun _ => [])⟩) =
      some (liftCfg M (haltList M out)) := by
  have hA := runA M e x (M.initialState, none) (w.map some) [] (fun _ => [])
  have hB := runB M e (w.map some) (M.initialState, some none) (x.reverse ++ []) (fun _ => [])
  have hC := runC M e (x.reverse ++ []) (M.initialState, none) (fun _ => [])
  rw [List.length_map] at hB
  rw [List.append_nil, List.length_reverse] at hC
  rw [List.append_nil] at hB
  rw [Function.iterate_add_apply _ n, Function.iterate_add_apply _ (x.length + 1),
    Function.iterate_add_apply _ (w.length + 1)]
  rw [hA]
  rw [List.append_nil]
  rw [hB, hC]
  dsimp only
  rw [List.append_nil, List.reverse_reverse, start_eq, iterate_lift, hM]
  rfl

end Construction

/-- The verifier built from a polynomial-time decider for `f` is a polynomial-time
verifier computing `(x, w) ↦ f x`. -/
noncomputable def verifierComputable {f : List Bool → Bool}
    (hf : TM2ComputableInPolyTime strEnc encodeBool f) :
    TM2ComputableInPolyTime pairEnc encodeBool (fun p => f p.1) where
  tm := verifierTM hf.tm hf.inputAlphabet
  inputAlphabet := Equiv.refl _
  outputAlphabet := hf.outputAlphabet
  time := hf.time + 2 * Polynomial.X + 3
  outputsFun p := by
    obtain ⟨x, w⟩ := p
    let M := hf.tm
    let e := hf.inputAlphabet
    let S0 : ∀ k, List (M.Γ k) := fun _ => []
    let hx := hf.outputsFun x
    let nM := hx.steps
    have hM := hx.evals_in_steps
    have hle : nM ≤ _ := hx.steps_le_m
    refine
      { steps := nM + ((x.length + 1) + ((w.length + 1) + (x.length + 1)))
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have hrun := verifier_run M e x w nM _ hM
      erw [initList_verifier M e (pairEnc (x, w))]
      erw [hrun]
      exact congrArg some (haltList_verifier M e _).symm
    · simp only [List.length_append, List.length_reverse, List.length_nil, List.length_map,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat,
        pairEnc, List.length_cons, add_zero]
      have hmono := poly_eval_mono hf.time
        (show x.length ≤ x.length + (w.length + 1) by omega)
      simp only [strEnc] at hle
      omega

/-- **P ⊆ NP**, proved in this model with a real machine construction. -/
theorem P_subset_NP (L : Language) (h : InP L) : InNP L := by
  obtain ⟨f, ⟨hf⟩, hL⟩ := h
  refine ⟨fun p => f p.1, 0, ⟨verifierComputable hf⟩, fun x => ?_⟩
  rw [hL]
  constructor
  · intro h; exact ⟨[], by simp, h⟩
  · rintro ⟨w, -, h⟩; exact h

end PvnpReal
