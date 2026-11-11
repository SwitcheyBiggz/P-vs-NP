/-
  PvnpReal.PpolyUndec — **P/poly contains an undecidable language.**

  Every Boolean function decided by *any* clocked `FinTM2` (`TM2ComputableInTime`, no time bound
  required) is reproduced by the concrete interpreter `U` of `NormalForm.lean` under a fixed code
  `cN N`.  Diagonalizing over the codes `N` gives a unary language `Ldiag` that no `FinTM2`
  decides (`¬ TM2Decidable Ldiag`), hence it is in no time-bounded class of the tree (EXP, DTIME,
  P).  Yet `Ldiag` has 1 bit of advice per length, so it is in `InPpoly` and `InPpolyCirc`.

  Honest scope: "decidable" here means decided by a total `FinTM2` with the tree's string
  encoding (`TM2Decidable`).  No bridge to Mathlib's `ComputablePred` is proven.
-/
import PvnpReal.CircPpoly
import PvnpReal.NormalForm
import PvnpReal.TimeHierarchy

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-- Clocked runs of `NProg` are monotone in the clock. -/
theorem nrunFor_mono (p : NProg) {t t' : ℕ} (htt : t ≤ t') {c h : NCfg}
    (e : nrunFor p t c = some h) : nrunFor p t' c = some h := by
  induction t generalizing c t' with
  | zero =>
    simp only [nrunFor] at e
    split_ifs at e with hc
    cases e
    cases t' with
    | zero => simp [nrunFor, hc]
    | succ t' => simp [nrunFor, hc]
  | succ t ih =>
    obtain ⟨t', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    simp only [nrunFor] at e ⊢
    split at e
    · exact e
    · exact ih (by omega) e

/-- Outputs of `U` persist under a larger clock. -/
theorem U_mono {x y : List Bool} {t t' : ℕ} {b : Bool} (htt : t ≤ t') (e : U x y t = some b) :
    U x y t' = some b := by
  unfold U at e ⊢
  simp only at e ⊢
  split at e
  · next c hc => rw [nrunFor_mono _ htt hc]; exact e
  · exact absurd e (by simp)

/-- `U` is deterministic: two halting clocks give the same output. -/
theorem U_det {x y : List Bool} {t t' : ℕ} {b b' : Bool} (e : U x y t = some b)
    (e' : U x y t' = some b') : b = b' := by
  rcases le_total t t' with h | h
  · have := U_mono h e; rw [this] at e'; exact Option.some.inj e'
  · have := U_mono h e'; rw [this] at e; exact (Option.some.inj e).symm

/-- The code naming program number `N`. -/
def cN (N : ℕ) : List Bool := List.replicate 0 true ++ false :: (List.replicate N true ++ [false])

/-- **Universality for all total `FinTM2` deciders** (no time bound needed). -/
theorem U_sim {f : List Bool → Bool} (h : TM2ComputableInTime strEnc encodeBool f) (y : List Bool) :
    U (cN (Encodable.encode (Sim.prog h.tm h.inputAlphabet h.outputAlphabet))) y
      (h.time (strEnc y).length) = some (f y) := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = Sim.prog h.tm h.inputAlphabet h.outputAlphabet := ⟨_, rfl⟩
  rw [← hpdef]
  have hp : (Encodable.decode (α := NProg) (lpN (lpX (cN (Encodable.encode p))))).getD default
      = p := by
    simp only [cN, lpX_rep, lpN_rep, Encodable.encodek, Option.getD_some]
  have hr := runFor_computable h y
  obtain ⟨i1, i2⟩ := Sim.init_enc h.tm h.inputAlphabet h.outputAlphabet y
  obtain ⟨s1, s2⟩ := Sim.simulate h.tm h.inputAlphabet h.outputAlphabet _ _ _ i2 hr
  have s1' : nrunFor p (h.time (strEnc y).length) (NInit p y) = some (Sim.encCfg h.tm
      (haltList h.tm [h.outputAlphabet.invFun (f y)])) := by
    rw [hpdef, ← i1]; exact s1
  unfold U
  simp only [hp]
  rw [s1']
  subst hpdef
  exact Sim.halt_out h.tm h.inputAlphabet h.outputAlphabet (f y) s2

/-- **Decidable by some total `FinTM2`** (string encoding, Boolean output, any time). -/
def TM2Decidable (L : Language) : Prop :=
  ∃ f : List Bool → Bool, Nonempty (TM2ComputableInTime strEnc encodeBool f) ∧
    ∀ x, L x ↔ f x = true

/-- The language accepted by program number `N` (via the interpreter `U`). -/
def NLang (N : ℕ) : Language := fun y => ∃ t, U (cN N) y t = some true

/-- Every `TM2Decidable` language is some `NLang N`. -/
theorem TM2Decidable.exists_code {L : Language} (hL : TM2Decidable L) :
    ∃ N, ∀ y, L y ↔ NLang N y := by
  obtain ⟨f, ⟨h⟩, hf⟩ := hL
  refine ⟨Encodable.encode (Sim.prog h.tm h.inputAlphabet h.outputAlphabet), fun y => ?_⟩
  have hs := U_sim h y
  rw [hf]
  constructor
  · intro e; exact ⟨_, e ▸ hs⟩
  · rintro ⟨t, ht⟩; exact (U_det hs ht)

theorem InEXP.tm2Decidable {L : Language} (h : InEXP L) : TM2Decidable L := by
  obtain ⟨f, _, ⟨h, _⟩, hf⟩ := h
  exact ⟨f, ⟨h⟩, hf⟩

theorem InDTIME.tm2Decidable {T : ℕ → ℕ} {L : Language} (h : InDTIME T L) : TM2Decidable L := by
  obtain ⟨f, h, _, hf⟩ := h
  exact ⟨f, ⟨h⟩, hf⟩

theorem InP.tm2Decidable {L : Language} (h : InP L) : TM2Decidable L := by
  obtain ⟨f, ⟨h⟩, hf⟩ := h
  exact ⟨f, ⟨h.toTM2ComputableInTime⟩, hf⟩

/-- **The diagonal unary language**: `1ⁿ` is in iff program `n` does not accept `1ⁿ`. -/
def Ldiag : Language := fun y =>
  y = List.replicate y.length true ∧ ¬ NLang y.length (List.replicate y.length true)

/-- **`Ldiag` is not decided by any total `FinTM2`.** -/
theorem Ldiag_not_tm2Decidable : ¬ TM2Decidable Ldiag := by
  intro h
  obtain ⟨N, hN⟩ := h.exists_code
  have := hN (List.replicate N true)
  simp only [Ldiag, List.length_replicate, true_and] at this
  tauto

theorem Ldiag_not_InEXP : ¬ InEXP Ldiag := fun h => Ldiag_not_tm2Decidable h.tm2Decidable

theorem Ldiag_not_InDTIME (T : ℕ → ℕ) : ¬ InDTIME T Ldiag :=
  fun h => Ldiag_not_tm2Decidable h.tm2Decidable

theorem lpN_eq_length_iff (x : List Bool) : lpN x = x.length ↔ x = List.replicate x.length true := by
  induction x with
  | nil => simp [lpN]
  | cons b x ih =>
    cases b
    · simp [lpN, List.replicate_succ]
    · rw [LoopTM.lpN_cons_true]; simp [List.replicate_succ, ih]

/-- **`Ldiag` ∈ P/poly** (advice form: one advice bit per length). -/
theorem Ldiag_InPpoly : InPpoly Ldiag := by
  classical
  refine ⟨fun s => lpN (decP s).1 = (decP s).1.length ∧ NthTM.bit (decP s).2 0 = 1, 1,
    fun n => [decide (¬ NLang n (List.replicate n true))], ?_, fun n => by simp, fun x => ?_⟩
  · exact InP.inter (InP.ofPUeq (PU.fst.comp PS.fstP) (PU.lenX.comp PS.fstP))
      (InP.ofPUeq ((PU.bitAt 0).comp PS.sndP) (PU.const 1))
  · simp only [decP_codeP, Ldiag, lpN_eq_length_iff]
    by_cases hc : NLang x.length (List.replicate x.length true) <;> simp [hc, NthTM.bit]

/-- **`Ldiag` ∈ P/poly** (circuit form). -/
theorem Ldiag_InPpolyCirc : InPpolyCirc Ldiag := InPpolyCirc_of_InPpoly Ldiag_InPpoly

/-- **P/poly contains a language that no `FinTM2` decides** (so in particular it is not in EXP,
nor in any `DTIME(T)`). -/
theorem Ppoly_has_undecidable :
    ∃ L, InPpolyCirc L ∧ InPpoly L ∧ ¬ TM2Decidable L ∧ ¬ InEXP L ∧ ∀ T, ¬ InDTIME T L :=
  ⟨Ldiag, Ldiag_InPpolyCirc, Ldiag_InPpoly, Ldiag_not_tm2Decidable, Ldiag_not_InEXP,
    Ldiag_not_InDTIME⟩

/-- Hence **P/poly ⊄ EXP** (in the tree's definitions). -/
theorem Ppoly_not_subset_EXP : ¬ ∀ L, InPpolyCirc L → InEXP L :=
  fun h => Ldiag_not_InEXP (h _ Ldiag_InPpolyCirc)

end PvnpReal
