/-
  PvnpReal.Clock — first proven sub-pieces toward a deterministic time hierarchy theorem.

  * `runFor`: clocked evaluation of a `TM2` machine (stop at halt, give up after `t` steps),
    with exact agreement with Mathlib's step semantics (`runFor_iff`), monotonicity in the clock,
    determinism of the halting configuration, and agreement with any `TM2ComputableInTime`.
  * `exp_time_constructible`: the padding machine witnesses that `2ⁿ` is time-constructible.
  * `diag_step`: the (purely logical) diagonal step of the hierarchy theorem, abstracted over a
    clocked interpreter.

  NOT done here: a universal `FinTM2` that implements `runFor` for encoded machines, and its
  overhead bound. That is the main missing ingredient of the time hierarchy theorem.
-/
import PvnpReal.BruteEXP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

section Clock

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ : Type} {σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)

/-- Clocked evaluation: return the first halting configuration reached within `t` steps. -/
def runFor : ℕ → TM2.Cfg Γ Λ σ → Option (TM2.Cfg Γ Λ σ)
  | 0, c => if c.l = none then some c else none
  | t + 1, c => match c.l with
    | none => some c
    | some _ => (TM2.step M c).bind (runFor t)

theorem iterate_none (s : ℕ) : (flip bind (TM2.step M))^[s] none = none := by
  induction s with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply]; exact ih

theorem step_some {c : TM2.Cfg Γ Λ σ} {l : Λ} (hc : c.l = some l) :
    TM2.step M c = some (TM2.stepAux (M l) c.var c.stk) := by
  obtain ⟨cl, v, S⟩ := c
  simp only at hc; subst hc; rfl

theorem step_none {c : TM2.Cfg Γ Λ σ} (hc : c.l = none) : TM2.step M c = none := by
  obtain ⟨cl, v, S⟩ := c
  simp only at hc; subst hc; rfl

/-- Reaching a halting configuration in `s ≤ t` steps makes `runFor t` return it. -/
theorem runFor_of_iterate (s : ℕ) : ∀ (t : ℕ) (c h : TM2.Cfg Γ Λ σ), s ≤ t →
    (flip bind (TM2.step M))^[s] (some c) = some h → h.l = none → runFor M t c = some h := by
  induction s with
  | zero =>
    intro t c h _ e hh
    simp only [Function.iterate_zero, id, Option.some.injEq] at e
    subst e
    cases t <;> simp [runFor, hh]
  | succ s ih =>
    intro t c h hst e hh
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Function.iterate_succ_apply] at e
    cases hc : c.l with
    | none =>
      have : flip bind (TM2.step M) (some c) = none := by
        simp [flip, step_none M hc]
      rw [this, iterate_none] at e; cases e
    | some l =>
      have hs := step_some M hc
      have e' : flip bind (TM2.step M) (some c) = some (TM2.stepAux (M l) c.var c.stk) := by
        simp [flip, hs]
      rw [e'] at e
      have := ih t _ h (by omega) e hh
      simp only [runFor, hc, hs, Option.bind_some, this]

/-- Conversely, `runFor t c = some h` means `h` halts and is reached in at most `t` steps. -/
theorem iterate_of_runFor (t : ℕ) : ∀ (c h : TM2.Cfg Γ Λ σ), runFor M t c = some h →
    h.l = none ∧ ∃ s ≤ t, (flip bind (TM2.step M))^[s] (some c) = some h := by
  induction t with
  | zero =>
    intro c h e
    simp only [runFor] at e
    split at e
    · next hc => cases e; exact ⟨hc, 0, le_rfl, rfl⟩
    · cases e
  | succ t ih =>
    intro c h e
    cases hc : c.l with
    | none =>
      simp only [runFor, hc] at e
      cases e; exact ⟨hc, 0, by omega, rfl⟩
    | some l =>
      have hs := step_some M hc
      simp only [runFor, hc, hs, Option.bind_some] at e
      obtain ⟨hh, s, hst, he⟩ := ih _ _ e
      refine ⟨hh, s + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simpa [flip, hs] using he

theorem runFor_iff (t : ℕ) (c h : TM2.Cfg Γ Λ σ) :
    runFor M t c = some h ↔ h.l = none ∧ ∃ s ≤ t, (flip bind (TM2.step M))^[s] (some c) = some h :=
  ⟨iterate_of_runFor M t c h, fun ⟨hh, s, hs, e⟩ => runFor_of_iterate M s t c h hs e hh⟩

/-- The clock is monotone: more time never changes a halting answer. -/
theorem runFor_mono {t t' : ℕ} (htt : t ≤ t') {c h : TM2.Cfg Γ Λ σ} (e : runFor M t c = some h) :
    runFor M t' c = some h := by
  obtain ⟨hh, s, hs, he⟩ := iterate_of_runFor M t c h e
  exact runFor_of_iterate M s t' c h (by omega) he hh

/-- Determinism: a machine reaches at most one halting configuration. -/
theorem halt_unique {c h h' : TM2.Cfg Γ Λ σ} {s s' : ℕ}
    (e : (flip bind (TM2.step M))^[s] (some c) = some h) (hh : h.l = none)
    (e' : (flip bind (TM2.step M))^[s'] (some c) = some h') (hh' : h'.l = none) : h = h' := by
  have a := runFor_of_iterate M s (max s s') c h (le_max_left _ _) e hh
  have b := runFor_of_iterate M s' (max s s') c h' (le_max_right _ _) e' hh'
  rw [a] at b; exact Option.some.inj b

end Clock

/-- **Clocked evaluation agrees with any machine within its time bound.** -/
theorem runFor_computable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInTime ea eb f) (a : α) :
    runFor h.tm.m (h.time (ea a).length) (initList h.tm (List.map h.inputAlphabet.invFun (ea a))) =
      some (haltList h.tm (List.map h.outputAlphabet.invFun (eb (f a)))) := by
  have hx := h.outputsFun a
  have e := hx.evals_in_steps
  simp only [Option.map_some] at e
  exact runFor_of_iterate h.tm.m hx.steps _ _ _ hx.steps_le_m e rfl

/-- **`2ⁿ` is time-constructible**: `x ↦ 1^{2^|x|} 0 x` in time `≤ 16·2ⁿ`. -/
theorem exp_time_constructible :
    ∃ h : TM2ComputableInTime strEnc strEnc padF, ∀ n, h.time n ≤ 16 * 2 ^ n := by
  refine ⟨padComputable, fun n => ?_⟩
  change 4 * 2 ^ n + 5 * n + 4 ≤ 16 * 2 ^ n
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- **The diagonal step** (purely logical). For any clocked interpreter
`run : code → input → budget → Option Bool` and budget `T`, the diagonal language
`D x := run x x (T |x|) ≠ some true` differs from every decider `f` that the interpreter
reproduces, within budget, on at least one code `x` (`run x x (T |x|) = some (f x)`).
The time hierarchy theorem needs, in addition, a universal machine implementing `run` with
small overhead and a padding argument giving such an `x` for every fast machine; neither is
formalized here. -/
theorem diag_step (run : List Bool → List Bool → ℕ → Option Bool) (T : ℕ → ℕ)
    (f : List Bool → Bool) (x : List Bool) (hx : run x x (T x.length) = some (f x)) :
    ¬ ((run x x (T x.length) ≠ some true) ↔ f x = true) := by
  rw [hx]
  cases f x <;> simp

end PvnpReal
