/-
  PvnpReal.PvsNP — standard equivalent forms of the (open) P vs NP question.

  Nothing here decides P vs NP. These are reformulations: `P_eq_NP ↔ InP SATLang`, and
  `P_eq_NP ↔` some/every NP-complete language is in P. Also: P is closed under reductions and
  complement, and P = NP would imply NP = coNP.
-/
import PvnpReal.CookLevin2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

/-! ### Deciders as bit-string functions -/

/-- A decider `strEnc → encodeBool` is the same thing as a bit-string function `x ↦ [f x]`
(`encodeBool b = [b]`, `strEnc = id`); the same machine works. -/
noncomputable def deciderToStr {f : List Bool → Bool}
    (h : TM2ComputableInPolyTime strEnc encodeBool f) :
    TM2ComputableInPolyTime strEnc strEnc (fun x => [f x]) where
  tm := h.tm
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := h.time
  outputsFun x := h.outputsFun x

noncomputable def strToDecider {f : List Bool → Bool}
    (h : TM2ComputableInPolyTime strEnc strEnc (fun x => [f x])) :
    TM2ComputableInPolyTime strEnc encodeBool f where
  tm := h.tm
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := h.time
  outputsFun x := h.outputsFun x

/-- **P is closed under polynomial-time reductions.** -/
theorem InP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InP L') : InP L := by
  obtain ⟨g, ⟨hg⟩, hL⟩ := hr
  obtain ⟨f, ⟨hf⟩, hL'⟩ := h
  refine ⟨fun x => f (g x), ⟨strToDecider (composeComputable hg (deciderToStr hf))⟩, fun x => ?_⟩
  rw [hL, hL']

/-! ### A negation machine and closure of P under complement -/

namespace SmallTM

open TM2.Stmt

def notStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o)
      (branch isT (push UK.out (fun _ => false) (goto fun _ => .l2))
        (push UK.out (fun _ => true) (goto fun _ => .l2)))
  | .l2 => pop UK.inp (fun _ o => o) (branch isS (goto fun _ => .l2) halt)

def notF (y : List Bool) : List Bool := [!(isT y.head?)]

theorem not_clear (l : List Bool) (v : Option Bool) (o : List Bool) :
    (flip bind (TM2.step notStmt))^[l.length + 1] (some ⟨some .l2, v, st l o⟩) =
      some ⟨none, none, st [] o⟩ := by
  induction l generalizing v with
  | nil => simp [TM2.step, notStmt, TM2.stepAux, isS, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step notStmt) (some ⟨some .l2, v, st (b :: l) o⟩) =
        some ⟨some .l2, some b, st l o⟩ := by
      simp [TM2.step, notStmt, TM2.stepAux, isS, flip]
    rw [e, ih]

theorem not_first (y : List Bool) :
    flip bind (TM2.step notStmt) (some ⟨some .l1, none, st y []⟩) =
      some ⟨some .l2, y.head?, st y.tail (notF y)⟩ := by
  cases y with
  | nil => simp [TM2.step, notStmt, TM2.stepAux, isT, notF, flip]
  | cons b l => cases b <;> simp [TM2.step, notStmt, TM2.stepAux, isT, notF, flip]

end SmallTM

/-- `y ↦ [¬ (head of y)]` in time `X + 2`. -/
noncomputable def notComputable : TM2ComputableInPolyTime strEnc strEnc SmallTM.notF where
  tm := SmallTM.mk SmallTM.notStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun y :=
    { steps := y.tail.length + 1 + 1
      evals_in_steps := by
        erw [List.map_id, List.map_id, SmallTM.initList_eq, Option.map_some,
          SmallTM.haltList_eq]
        rw [Function.iterate_succ_apply]
        erw [SmallTM.not_first y]
        exact SmallTM.not_clear y.tail y.head? _
      steps_le_m := by simp [strEnc]; cases y <;> simp }

/-- **P is closed under complement.** -/
theorem InP.compl {L : Language} (h : InP L) : InP (fun x => ¬ L x) := by
  obtain ⟨f, ⟨hf⟩, hL⟩ := h
  have hn : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => [!f x])) :=
    computable_congr (fun x => by
      show SmallTM.notF [f x] = [!f x]
      cases f x <;> rfl) ⟨composeComputable (deciderToStr hf) notComputable⟩
  obtain ⟨hn⟩ := hn
  exact ⟨fun x => !f x, ⟨strToDecider hn⟩, fun x => by
    show ¬ L x ↔ (!f x) = true
    rw [hL]; cases f x <;> simp⟩

theorem InP.congr {L L' : Language} (h : InP L) (e : ∀ x, L x ↔ L' x) : InP L' := by
  obtain ⟨f, hf, hL⟩ := h
  exact ⟨f, hf, fun x => (e x).symm.trans (hL x)⟩

/-! ### Equivalent forms of `P = NP` (none of them is decided here) -/

/-- NP-completeness propagates: an NP language that an NP-complete language reduces to is
NP-complete. -/
theorem NPComplete.of_reduces {L L' : Language} (h : NPComplete L) (hL' : InNP L')
    (hr : PolyReduces L L') : NPComplete L' :=
  ⟨hL', fun L'' hL'' => (h.2 L'' hL'').trans hr⟩

theorem SAT_NPComplete : NPComplete SATLang := cookLevin

/-- If some NP-hard language is in P, then every NP language is in P. -/
theorem NP_subset_P_of_NPHard_in_P {L : Language} (hH : NPHard L) (hP : InP L) :
    ∀ L', InNP L' → InP L' := fun L' hL' => InP.of_reduces (hH L' hL') hP

/-- **`P = NP` iff SAT is in P.** -/
theorem P_eq_NP_iff_SAT_in_P : P_eq_NP ↔ InP SATLang := by
  constructor
  · intro h; exact (h SATLang).2 SAT_in_NP
  · intro hS L
    exact ⟨P_subset_NP L, fun hL => NP_subset_P_of_NPHard_in_P SAT_NPHard hS L hL⟩

/-- **`P = NP` iff some NP-complete language is in P.** -/
theorem P_eq_NP_iff_exists_NPComplete_in_P :
    P_eq_NP ↔ ∃ L, NPComplete L ∧ InP L := by
  constructor
  · intro h; exact ⟨SATLang, SAT_NPComplete, P_eq_NP_iff_SAT_in_P.1 h⟩
  · rintro ⟨L, hC, hP⟩ L'
    exact ⟨P_subset_NP L', fun hL' => NP_subset_P_of_NPHard_in_P hC.2 hP L' hL'⟩

/-- **`P = NP` iff every NP-complete language is in P.** -/
theorem P_eq_NP_iff_all_NPComplete_in_P :
    P_eq_NP ↔ ∀ L, NPComplete L → InP L := by
  constructor
  · intro h L hC; exact (h L).2 hC.1
  · intro h; exact P_eq_NP_iff_SAT_in_P.2 (h SATLang SAT_NPComplete)

/-- **`P ≠ NP` iff SAT is not in P.** -/
theorem P_ne_NP_iff_SAT_not_in_P : ¬ P_eq_NP ↔ ¬ InP SATLang :=
  not_congr P_eq_NP_iff_SAT_in_P

/-- **`P ≠ NP` iff no NP-complete language is in P.** -/
theorem P_ne_NP_iff_no_NPComplete_in_P : ¬ P_eq_NP ↔ ∀ L, NPComplete L → ¬ InP L := by
  rw [P_eq_NP_iff_exists_NPComplete_in_P]
  constructor
  · intro h L hC hP; exact h ⟨L, hC, hP⟩
  · rintro h ⟨L, hC, hP⟩; exact h L hC hP

/-- `P = NP` is equivalent to "NP ⊆ P" (P ⊆ NP is proven). -/
theorem P_eq_NP_iff_NP_subset_P : P_eq_NP ↔ ∀ L, InNP L → InP L :=
  ⟨fun h L hL => (h L).2 hL, fun h L => ⟨P_subset_NP L, h L⟩⟩

/-! ### coNP -/

/-- **coNP**: languages whose complement is in NP. -/
def InCoNP (L : Language) : Prop := InNP (fun x => ¬ L x)

/-- P ⊆ coNP. -/
theorem P_subset_coNP (L : Language) (h : InP L) : InCoNP L := P_subset_NP _ h.compl

/-- **If P = NP then NP = coNP.** (The converse is not known and not claimed.) -/
theorem NP_eq_coNP_of_P_eq_NP (h : P_eq_NP) : ∀ L, InNP L ↔ InCoNP L := by
  intro L
  constructor
  · intro hL; exact P_subset_coNP L ((h L).2 hL)
  · intro hL
    have h1 : InP (fun x => ¬ L x) := (h _).2 hL
    exact P_subset_NP L (h1.compl.congr (fun x => not_not))

/-- Contrapositive: if NP ≠ coNP then P ≠ NP. -/
theorem P_ne_NP_of_NP_ne_coNP (h : ¬ ∀ L, InNP L ↔ InCoNP L) : ¬ P_eq_NP :=
  fun hp => h (NP_eq_coNP_of_P_eq_NP hp)

end PvnpReal
