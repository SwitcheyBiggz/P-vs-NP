/-
  PvnpReal.TimeHierarchy — a **deterministic time hierarchy theorem** for Mathlib `FinTM2`
  deciders, generalizing the `P ≠ EXP` diagonalization (`U2`, `Prm.reproduce`, `PS.dW`).

  * `reproducesT`: `U2` reproduces every decider with an *arbitrary* time bound `T`, with clock
    `D·T(|x|) + 1` (constant `D` depending on the machine).
  * `diagT t`: the diagonal of `U2` clocked at `t(|x|)`.
  * **`diagT_not_in_DTIME`**: `diagT t ∉ DTIME(T)` whenever `D·T(n) + 1 ≤ t(n)` eventually for every `D`
    (i.e. `T = o(t)` in this sense).
  * **`diagT_in_DTIME`**: there is ONE polynomial `P` (independent of `t`) such that, for every `t`
    whose padding `x ↦ 1^{t(|x|)} 0 x` is computed by a `FinTM2` `hp`, `diagT t ∈ DTIME(τ)` with
    `τ(n) = s(n) + 2(n + C·s(n)) + 2 + P(n + C·s(n))`, where `s = hp.time`, `C = pushTotal hp.tm`.
    So `diagT t ∈ DTIME(poly(t(n) + n))` with a fixed universal polynomial when `s = O(t + n)`.
  * **`time_hierarchy`** combines both; corollaries **`P_not_sub_DTIME_pow`** (for every `k`, some
    `L ∈ P` is not in `DTIME(nᵏ)`), **`DTIME_pow_sub_P`**, **`DTIME_pow_ssubset_P`**.

  Not proven: the sharp `t log t` bound (our `P` is not computed explicitly), and any statement
  about P vs NP.
-/
import PvnpReal.Reproduce2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Flat

/-- `L ∈ DTIME(T)`: decided by a Mathlib `FinTM2` within `T(|x|)` steps. -/
def InDTIME (T : ℕ → ℕ) (L : Language) : Prop :=
  ∃ (f : List Bool → Bool) (h : TM2ComputableInTime strEnc encodeBool f),
    (∀ n, h.time n ≤ T n) ∧ ∀ x, L x ↔ f x = true

/-- Padding by a time function: `1^{t(|x|)} 0 x`. -/
def padWith (t : ℕ → ℕ) (x : List Bool) : List Bool := List.replicate (t x.length) true ++ false :: x

/-- The diagonal of `U2` with clock `t(|x|)`. -/
def diagT (t : ℕ → ℕ) : Language := fun x => U2 x x (t x.length) ≠ some true

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

/-- **`U2` reproduces deciders on arbitrary inputs**: any program string whose `lpX` encodes the
compiled program `Pc` runs `f` on every input `y`, once the clock is `≥ D·T(|y|) + 1` and `≥ |Pc| - |y|`. -/
theorem reproducesG (f : List Bool → Bool) (h : TM2ComputableInTime strEnc encodeBool f) :
    ∃ D : ℕ, ∃ Pc : List ℕ, ∀ x, numsOf (lpX x) = Pc → ∀ y t, D * h.time y.length + 1 ≤ t →
      Pc.length ≤ y.length + t → U2 x y t = some (f y) := by
  let P := Sim.prm h.tm h.inputAlphabet h.outputAlphabet
  refine ⟨P.D, P.Pc, fun x hx y t ht hPc => ?_⟩
  have hr := runFor_computable h y
  obtain ⟨i1, i2⟩ := Sim.init_enc h.tm h.inputAlphabet h.outputAlphabet y
  obtain ⟨s1, s2⟩ := Sim.simulate h.tm h.inputAlphabet h.outputAlphabet _ _ _ i2 hr
  rw [i1] at s1
  have hb := Sim.halt_out h.tm h.inputAlphabet h.outputAlphabet (f y) s2
  have hcard : ∀ (k : h.tm.K), (Sim.eK h.tm k : ℕ) < Fintype.card h.tm.K := fun k => (Sim.eK h.tm k).2
  refine Prm.reproduce P (Sim.nwf_nodes _ _ _) (hcard _) (hcard _) (Sim.eσ h.tm h.tm.initialState).2
    ?_ x y hx _ _ s1 (f y) hb t ht hPc
  intro b
  cases b <;> exact Sim.code_le _ _

/-- **`U2` reproduces deciders with arbitrary time bounds**, with linear clock overhead. -/
theorem reproducesT (f : List Bool → Bool) (h : TM2ComputableInTime strEnc encodeBool f) :
    ∃ D, ∀ n0, ∃ x : List Bool, n0 ≤ x.length ∧
      ∀ t, D * h.time x.length + 1 ≤ t → U2 x x t = some (f x) := by
  obtain ⟨D, Pc, hD⟩ := reproducesG f h
  refine ⟨D, fun n0 => ?_⟩
  let x : List Bool := List.replicate n0 true ++ false :: encNums Pc
  have hx : numsOf (lpX x) = Pc := by simp only [x, lpX_rep, numsOf_encNums]
  have hPc : Pc.length ≤ x.length := by
    have := encNums_length_ge Pc
    simp only [x, List.length_append, List.length_replicate, List.length_cons]; omega
  exact ⟨x, by simp [x], fun t ht => hD x hx x t ht (by omega)⟩

/-- **Lower bound**: `diagT t ∉ DTIME(T)` when `T = o(t)` (for every `D`, eventually `D·T + 1 ≤ t`). -/
theorem diagT_not_in_DTIME (t T : ℕ → ℕ) (hT : ∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) :
    ¬ InDTIME T (diagT t) := by
  rintro ⟨f, h, hb, hL⟩
  obtain ⟨D, hD⟩ := reproducesT f h
  obtain ⟨N, hN⟩ := hT D
  obtain ⟨x, hx, hrun⟩ := hD N
  have e := hrun (t x.length)
    ((Nat.add_le_add_right (Nat.mul_le_mul_left _ (hb _)) 1).trans (hN _ hx))
  have := hL x
  unfold diagT at this
  rw [e] at this
  cases hfx : f x <;> simp [hfx] at this

/-- The diagonal decision factors through the padding. -/
theorem diagT_iff (t : ℕ → ℕ) (x : List Bool) : diagT t x ↔ dW (padWith t x) = true := by
  have h1 : lpN (padWith t x) = t x.length := by simp [padWith, lpN_rep]
  have h2 : lpX (padWith t x) = x := by simp [padWith, lpX_rep]
  simp only [diagT, U2, dW, srcW, h1, h2]
  constructor
  · intro h; simpa using fun e => h (by simp [e])
  · intro h; simp at h; split <;> simp_all

/-- **Upper bound** with one universal polynomial `P`. -/
theorem diagT_in_DTIME : ∃ P : Polynomial ℕ, ∀ (t : ℕ → ℕ)
    (hp : TM2ComputableInTime strEnc strEnc (padWith t)),
    InDTIME (fun n => hp.time n + 2 * (n + pushTotal hp.tm * hp.time n) + 2 +
      P.eval (n + pushTotal hp.tm * hp.time n)) (diagT t) := by
  obtain ⟨hs⟩ := PS.dW
  let h2 := strToDecider hs
  refine ⟨h2.time, fun t hp => ?_⟩
  let hc := composeInTime hp h2.toTM2ComputableInTime (fun m => h2.time.eval m)
    (fun m => le_rfl) (fun a b h => poly_eval_mono h2.time h)
  exact ⟨dW ∘ padWith t, hc, fun n => le_rfl, fun x => diagT_iff t x⟩

/-- **Time hierarchy theorem** (for `FinTM2` deciders). There is a universal polynomial `P` such that
for every time function `t` with a padding machine `hp` and every `T = o(t)`, the language `diagT t`
is decidable within `τ(n) = s + 2(n + C s) + 2 + P(n + C s)` (`s = hp.time n`) but not within `T`. -/
theorem time_hierarchy : ∃ P : Polynomial ℕ, ∀ (t : ℕ → ℕ)
    (hp : TM2ComputableInTime strEnc strEnc (padWith t)),
    InDTIME (fun n => hp.time n + 2 * (n + pushTotal hp.tm * hp.time n) + 2 +
      P.eval (n + pushTotal hp.tm * hp.time n)) (diagT t) ∧
    ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (diagT t) := by
  obtain ⟨P, hP⟩ := diagT_in_DTIME
  exact ⟨P, fun t hp => ⟨hP t hp, fun T hT => diagT_not_in_DTIME t T hT⟩⟩

/-- Polynomial clocks have polynomial-time padding. -/
theorem PS.padWith (q : Polynomial ℕ) : PS (padWith (fun n => q.eval n)) :=
  (PS.append (PU.poly q) (PS.cons false PS.id)).congr (fun x => rfl)

/-- With a polynomial clock, the diagonal is in P. -/
theorem diagT_poly_in_P (q : Polynomial ℕ) : InP (diagT (fun n => q.eval n)) := by
  obtain ⟨hs⟩ := (PS.padWith q).comp PS.dW
  exact ⟨fun x => dW (padWith (fun n => q.eval n) x), ⟨strToDecider hs⟩,
    fun x => diagT_iff _ x⟩

/-- **P is not contained in any fixed polynomial time bound**: for every `k`, some language in P
is not decidable within `nᵏ` steps. -/
theorem P_not_sub_DTIME_pow (k : ℕ) : ∃ L, InP L ∧ ¬ InDTIME (fun n => n ^ k) L := by
  refine ⟨diagT (fun n => (Polynomial.X ^ (k + 1) : Polynomial ℕ).eval n), diagT_poly_in_P _, ?_⟩
  apply diagT_not_in_DTIME
  intro D
  refine ⟨D + 1, fun n hn => ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  have h1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ (by omega)
  have : n ^ (k + 1) = n * n ^ k := by ring
  rw [this]
  nlinarith

/-- `DTIME(nᵏ) ⊆ P`. -/
theorem DTIME_pow_sub_P (k : ℕ) (L : Language) (hL : InDTIME (fun n => n ^ k) L) : InP L := by
  obtain ⟨f, h, hb, hf⟩ := hL
  let h' : TM2ComputableInPolyTime strEnc encodeBool f :=
    { tm := h.tm
      inputAlphabet := h.inputAlphabet
      outputAlphabet := h.outputAlphabet
      time := Polynomial.X ^ k
      outputsFun := fun x =>
        { steps := (h.outputsFun x).steps
          evals_in_steps := (h.outputsFun x).evals_in_steps
          steps_le_m := (h.outputsFun x).steps_le_m.trans (by simpa using hb _) } }
  exact ⟨f, ⟨h'⟩, hf⟩

/-- **`DTIME(nᵏ) ⊊ P`** for every `k`. -/
theorem DTIME_pow_ssubset_P (k : ℕ) :
    (∀ L, InDTIME (fun n => n ^ k) L → InP L) ∧ ∃ L, InP L ∧ ¬ InDTIME (fun n => n ^ k) L :=
  ⟨DTIME_pow_sub_P k, P_not_sub_DTIME_pow k⟩

end PvnpReal
