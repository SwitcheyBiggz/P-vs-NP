/-
  PvnpReal.Complexity — P, NP and the statement `P_eq_NP`, built on Mathlib's
  Turing-machine model (`Turing.FinTM2`) and Mathlib's notion of polynomial-time
  computation (`Turing.TM2ComputableInPolyTime`).

  Here, unlike v76:
  * the output of a machine is whatever its configuration contains after actually
    running Mathlib's step function `Turing.TM2.step` until it halts;
  * the step count is the number of applications of that step function;
  * the time bound is a genuine polynomial in the input length.
-/
import Mathlib.Computability.TuringMachine.Computable
import PvnpReal.Sat

namespace PvnpReal

open Turing Computability StateTransition

/-- A language (decision problem) over the binary alphabet. -/
abbrev Language := List Bool → Prop

/-- Input encoding for deciders: a bit string is given to the machine as itself. -/
def strEnc : List Bool → List Bool := fun x => x

/-- Input encoding for verifiers: the pair `(x, w)` is written as `x # w` over the
three-letter alphabet `Option Bool` (`none` plays the role of the separator `#`). -/
def pairEnc (p : List Bool × List Bool) : List (Option Bool) :=
  p.1.map some ++ none :: p.2.map some

theorem pairEnc_injective : Function.Injective pairEnc := by
  rintro ⟨x, w⟩ ⟨x', w'⟩ h
  simp only [pairEnc] at h
  induction x generalizing x' with
  | nil =>
    cases x' with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      have := List.map_injective_iff.2 (Option.some_injective Bool) h
      subst this; rfl
    | cons b x' => simp at h
  | cons b x ih =>
    cases x' with
    | nil => simp at h
    | cons b' x' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Option.some.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih x' h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl

/-- **P**: `L` is decided by a Turing machine (Mathlib's `FinTM2`) that, on input `x`,
halts with output `[L x]` within `p(|x|)` steps for some polynomial `p`. -/
def InP (L : Language) : Prop :=
  ∃ f : List Bool → Bool,
    Nonempty (TM2ComputableInPolyTime strEnc encodeBool f) ∧ ∀ x, L x ↔ f x = true

/-- **NP**: there is a polynomial-time verifier `V` (a Turing machine reading `x # w`)
and a polynomial `q` such that `x ∈ L` iff some witness `w` with `|w| ≤ q(|x|)` makes `V`
accept. -/
def InNP (L : Language) : Prop :=
  ∃ (V : List Bool × List Bool → Bool) (q : Polynomial ℕ),
    Nonempty (TM2ComputableInPolyTime pairEnc encodeBool V) ∧
    ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ q.eval x.length ∧ V (x, w) = true

/-- **The P vs NP question**, stated (not proved): the classes coincide. -/
def P_eq_NP : Prop := ∀ L : Language, InP L ↔ InNP L

/-- Polynomial-time many-one (Karp) reduction. -/
def PolyReduces (L L' : Language) : Prop :=
  ∃ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime strEnc strEnc f) ∧ ∀ x, L x ↔ L' (f x)

/-- NP-completeness. -/
def NPComplete (L : Language) : Prop :=
  InNP L ∧ ∀ L' : Language, InNP L' → PolyReduces L' L

/-- **The Cook–Levin theorem, stated (not proved here).** -/
def CookLevinStatement : Prop := NPComplete SATLang

/-! ## Machines really determine their outputs -/

theorem flip_bind_iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- If a deterministic system reaches two halting states from the same start,
they are the same state. -/
theorem evalsTo_halt_unique {σ : Type} {f : σ → Option σ} {a b c : σ}
    (hb : f b = none) (hc : f c = none)
    (h1 : EvalsTo f a (some b)) (h2 : EvalsTo f a (some c)) : b = c := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have key : ∀ {n m : ℕ} {b c : σ}, f b = none → n ≤ m →
      (flip bind f)^[n] (some a) = some b → (flip bind f)^[m] (some a) = some c → b = c := by
    intro n m b c hb hnm hn hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [Nat.add_comm, Function.iterate_add_apply, hn] at hm
    cases d with
    | zero => simpa using hm
    | succ d =>
      rw [Function.iterate_succ_apply] at hm
      have : flip bind f (some b) = none := by simp [flip, hb]
      rw [this, flip_bind_iterate_none] at hm
      cases hm
  rcases le_total n m with h | h
  · exact key hb h hn hm
  · exact (key hc h hm hn).symm

theorem step_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    tm.step (haltList tm s) = none := rfl

theorem haltList_injective (tm : FinTM2) : Function.Injective (haltList tm) := by
  intro s t h
  have := congrArg (fun c : tm.Cfg => c.stk tm.k₁) h
  simpa [haltList] using this

/-- **Anti-v76 lemma.** A single machine cannot compute two different functions:
the function is determined by running the machine. (In v76, `TM.output` ignored the
machine entirely.) -/
theorem computed_function_unique {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    (heb : Function.Injective eb) {f g : α → β}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime ea eb g)
    (hsame : hf.toTM2ComputableAux = hg.toTM2ComputableAux) : f = g := by
  obtain ⟨aux, tf, of⟩ := hf
  obtain ⟨aux', tg, og⟩ := hg
  simp only at hsame
  subst hsame
  funext a
  have e := evalsTo_halt_unique (step_haltList _ _) (step_haltList _ _)
    (of a).toEvalsTo (og a).toEvalsTo
  have e2 := haltList_injective _ e
  have e3 : eb (f a) = eb (g a) :=
    List.map_injective_iff.2 aux.outputAlphabet.symm.injective e2
  exact heb e3

theorem encodeBool_injective : Function.Injective encodeBool := by
  intro a b h; simpa [encodeBool] using h

end PvnpReal
