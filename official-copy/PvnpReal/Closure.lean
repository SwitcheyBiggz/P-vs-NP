/-
  PvnpReal.Closure — closure properties: generalized composition, P closed under ∩ and ∪.
-/
import PvnpReal.PvsNP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

/-- **Composition with an arbitrary intermediate alphabet** (same machine as `composeComputable`). -/
noncomputable def composeGen {α β γ αΓ βΓ γΓ : Type} [Inhabited βΓ] {ea : α → List αΓ}
    {eb : β → List βΓ} {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime ea eb f) (h2 : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) where
  tm := composeTM h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet
  inputAlphabet := h1.inputAlphabet
  outputAlphabet := h2.outputAlphabet
  time := h1.time + 2 * (Polynomial.X + (pushTotal h1.tm : Polynomial ℕ) * h1.time) + 2 +
    h2.time.comp (Polynomial.X + (pushTotal h1.tm : Polynomial ℕ) * h1.time)
  outputsFun x := by
    let hx1 := h1.outputsFun x
    let hx2 := h2.outputsFun (f x)
    refine
      { steps := hx2.steps + (((List.map h1.outputAlphabet.invFun (eb (f x))).length + 1) +
          (((List.map h1.outputAlphabet.invFun (eb (f x))).length + 1) + hx1.steps))
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have e1 := hx1.evals_in_steps
      simp only [Option.map_some] at e1
      have e2 : (flip bind (TM2.step h2.tm.m))^[hx2.steps] (some (initList h2.tm
          ((List.map h1.outputAlphabet.invFun (eb (f x))).map
            (conv h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet)))) =
          some (haltList h2.tm (List.map h2.outputAlphabet.invFun (ec (g (f x))))) := by
        rw [map_conv]; exact hx2.evals_in_steps
      have := compose_run h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet _ _ _ _ _ e1 e2
      erw [initList_compose]
      exact this.trans (congrArg some (haltList_compose _ _ _ _ _).symm)
    · have hs1 := hx1.steps_le_m
      have hs2 := hx2.steps_le_m
      have hlen := outLen_bound h1 x
      have hmono := poly_eval_mono h2.time hlen
      simp only [List.length_map] at *
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
      have hC : pushTotal h1.tm * hx1.steps ≤ pushTotal h1.tm * h1.time.eval (ea x).length :=
        Nat.mul_le_mul_left _ hs1
      omega

/-! ### An AND machine -/

namespace SmallTM

open TM2.Stmt

def andStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o) (pop UK.inp (fun s o => some (isT s && isT o))
      (push UK.out (fun v => isT v) (goto fun _ => .l2)))
  | .l2 => pop UK.inp (fun _ o => o) (branch isS (goto fun _ => .l2) halt)

def andF (y : List Bool) : List Bool := [isT y.head? && isT y.tail.head?]

theorem and_clear (l : List Bool) (v : Option Bool) (o : List Bool) :
    (flip bind (TM2.step andStmt))^[l.length + 1] (some ⟨some .l2, v, st l o⟩) =
      some ⟨none, none, st [] o⟩ := by
  induction l generalizing v with
  | nil => simp [TM2.step, andStmt, TM2.stepAux, isS, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step andStmt) (some ⟨some .l2, v, st (b :: l) o⟩) =
        some ⟨some .l2, some b, st l o⟩ := by
      simp [TM2.step, andStmt, TM2.stepAux, isS, flip]
    rw [e, ih]

theorem and_first (y : List Bool) :
    flip bind (TM2.step andStmt) (some ⟨some .l1, none, st y []⟩) =
      some ⟨some .l2, some (isT y.head? && isT y.tail.head?), st y.tail.tail (andF y)⟩ := by
  rcases y with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp [TM2.step, andStmt, TM2.stepAux, isT, andF, flip]
  · cases a <;> simp [TM2.step, andStmt, TM2.stepAux, isT, andF, flip]
  · cases a <;> cases b <;> simp [TM2.step, andStmt, TM2.stepAux, isT, andF, flip]

end SmallTM

noncomputable def andComputable : TM2ComputableInPolyTime strEnc strEnc SmallTM.andF where
  tm := SmallTM.mk SmallTM.andStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun y :=
    { steps := y.tail.tail.length + 1 + 1
      evals_in_steps := by
        erw [List.map_id, List.map_id, SmallTM.initList_eq, Option.map_some,
          SmallTM.haltList_eq]
        rw [Function.iterate_succ_apply]
        erw [SmallTM.and_first y]
        exact SmallTM.and_clear y.tail.tail _ _
      steps_le_m := by
        simp [strEnc]; rcases y with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp <;> omega }

/-- **P is closed under intersection.** -/
theorem InP.inter {L L' : Language} (h : InP L) (h' : InP L') : InP (fun x => L x ∧ L' x) := by
  obtain ⟨f, ⟨hf⟩, hL⟩ := h
  obtain ⟨g, ⟨hg⟩, hL'⟩ := h'
  have hn : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => [f x && g x])) :=
    computable_congr (fun x => by
      show SmallTM.andF ([f x] ++ [g x]) = [f x && g x]
      cases f x <;> cases g x <;> rfl)
      ⟨composeComputable (fanComputable (deciderToStr hf) (deciderToStr hg)) andComputable⟩
  obtain ⟨hn⟩ := hn
  exact ⟨fun x => f x && g x, ⟨strToDecider hn⟩, fun x => by
    show L x ∧ L' x ↔ (f x && g x) = true
    rw [hL, hL', Bool.and_eq_true]⟩

/-- **P is closed under union.** -/
theorem InP.union {L L' : Language} (h : InP L) (h' : InP L') : InP (fun x => L x ∨ L' x) :=
  (InP.inter h.compl h'.compl).compl.congr (fun x => by tauto)

end PvnpReal
