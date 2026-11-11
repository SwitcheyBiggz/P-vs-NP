/-
  PvnpReal.CircBuild — converse bridge between gate lists and `BCirc`: a well-formed gate list
  (every input index `< n + |gs|`) with an in-range output index is a `BCirc` with `|gs|` gates
  computing the same function.  Foundation for the (not yet proven) direction
  `InPpoly → InPpolyCirc`.
-/
import PvnpReal.CircEval

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

/-- Clamp the opcode into `Fin 3` (opcodes `≥ 2` already mean NOT in `opN`). -/
def clampG (g : CGate) : CGate := (min g.1 2, g.2.1, g.2.2)

theorem opN_min (op : ℕ) (a b : Bool) : opN (min op 2) a b = opN op a b := by
  unfold opN
  rcases Nat.lt_or_ge op 2 with h | h
  · rw [Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right h]; simp [show op ≠ 0 by omega, show op ≠ 1 by omega]

theorem pRun_clamp : ∀ (gs : List CGate) (v : List Bool), pRun v (gs.map clampG) = pRun v gs
  | [], v => rfl
  | g :: gs, v => by
    rw [List.map_cons, pRun_cons, pRun_cons, pRun_clamp gs]
    simp [pStep, clampG, opN_min]

/-- The circuit described by a well-formed gate list. -/
def circOfGates (n : ℕ) (gs : List CGate)
    (hwf : ∀ g ∈ gs, g.2.1 < n + gs.length ∧ g.2.2 < n + gs.length)
    (out : ℕ) (hout : out < n + gs.length) : BCirc n gs.length :=
  (fun i => (⟨min (gs[i.1]'i.2).1 2, by omega⟩,
      ⟨(gs[i.1]'i.2).2.1, (hwf _ (List.getElem_mem i.2)).1⟩,
      ⟨(gs[i.1]'i.2).2.2, (hwf _ (List.getElem_mem i.2)).2⟩),
    ⟨out, by omega⟩)

theorem gatesOf_circOfGates (n : ℕ) (gs : List CGate) hwf out hout :
    gatesOf (circOfGates n gs hwf out hout) = gs.map clampG := by
  apply List.ext_getElem
  · simp [gatesOf]
  · intro i h1 h2
    simp [gatesOf, circOfGates, clampG]

theorem circOfGates_eval (n : ℕ) (gs : List CGate) hwf out hout (x : Fin n → Bool) :
    (circOfGates n gs hwf out hout).eval x = (pRun (List.ofFn x) gs).getD out false := by
  rw [eval_pRun, gatesOf_circOfGates, pRun_clamp]
  rfl

/-- **Gate lists give circuits.** -/
theorem hasCircuit_of_gates {n : ℕ} (f : BFun n) (gs : List CGate)
    (hwf : ∀ g ∈ gs, g.2.1 < n + gs.length ∧ g.2.2 < n + gs.length)
    (out : ℕ) (hout : out < n + gs.length)
    (hf : ∀ x, f x = (pRun (List.ofFn x) gs).getD out false) : HasCircuit n gs.length f :=
  ⟨gs.length, le_rfl, circOfGates n gs hwf out hout, funext fun x => by
    rw [circOfGates_eval, hf]⟩

/-- Circuits and well-formed gate lists define the same functions (up to the gate count). -/
theorem hasCircuit_iff_gates {n s : ℕ} (f : BFun n) :
    HasCircuit n s f ↔ ∃ gs : List CGate, gs.length ≤ s ∧
      (∀ g ∈ gs, g.2.1 < n + gs.length ∧ g.2.2 < n + gs.length) ∧
      ∃ out, out < n + gs.length + 1 ∧ ∀ x, f x = (pRun (List.ofFn x) gs).getD out false := by
  constructor
  · rintro ⟨s', hs, C, rfl⟩
    have hG : (gatesOf C).length = s' := by simp [gatesOf]
    refine ⟨gatesOf C, by omega, ?_, C.2, by have := C.2.2; omega, fun x => eval_pRun C x⟩
    intro g hg
    simp only [gatesOf, List.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    rw [hG]; exact ⟨(C.1 i).2.1.2, (C.1 i).2.2.2⟩
  · rintro ⟨gs, hs, hwf, out, hout, hf⟩
    by_cases ho : out < n + gs.length
    · exact (hasCircuit_of_gates f gs hwf out ho hf).mono hs
    · -- output reads past the wires: constant false; use the same list with output index 0-wire
      -- replaced by a fresh AND(j,j) gate placed after everything (forward read ⇒ false).
      have hfalse : ∀ x, f x = false := by
        intro x; rw [hf]
        simp [List.getD_eq_getElem?_getD, pRun_length, List.getElem?_eq_none (show
          (pRun (List.ofFn x) gs).length ≤ out by rw [pRun_length]; simp; omega)]
      refine ⟨gs.length, hs, (fun i => (0, ⟨0, by have := i.2; omega⟩, ⟨0, by have := i.2; omega⟩),
        ⟨n + gs.length, by omega⟩), funext fun x => ?_⟩
      rw [hfalse]; simp [BCirc.eval]

end PvnpReal
