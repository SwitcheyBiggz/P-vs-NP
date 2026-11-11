/-
  PvnpReal.TimeHierarchy2 — the time hierarchy with a **universal exponent**.

  The `U2` interpreter is built from polytime combinators, so its overhead is a polynomial `P` whose
  degree we do not compute. Here we turn `time_hierarchy` into the cleanest statement reachable without
  an explicit cost analysis of the interpreter:

  * **`time_hierarchy_pow`**: there is ONE exponent `k ≥ 1` such that for every time function `t` whose
    padding `x ↦ 1^{t(|x|)} 0 x` is computed within `A·(t(n)+n+1)^a` steps (`a ≥ 1`), there is `K` with
    `diagT t ∈ DTIME(K·(t(n)+n+1)^{k·a})` and `diagT t ∉ DTIME(T)` for every `T = o(t)`.
  * **`exp_time_hierarchy`**: with the exponential padding machine (`t = 2ⁿ`, `a = 1`), there are `k, K`
    and a language in `DTIME(K·(2ⁿ+n+1)^k)` that is not in `DTIME(2ⁿ/(n+1))`.

  NOT proven: the textbook `DTIME(t) ⊊ DTIME(t log t)` / `t·polylog t` forms — those need an explicit
  (quasi-linear) cost bound for the universal interpreter, which we do not have (`k` is not computed).
-/
import PvnpReal.TimeHierarchy
import PvnpReal.OracleSep

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

theorem InDTIME.mono {T T' : ℕ → ℕ} {L : Language} (h : InDTIME T L) (hT : ∀ n, T n ≤ T' n) :
    InDTIME T' L := by
  obtain ⟨f, h, hb, hL⟩ := h
  exact ⟨f, h, fun n => (hb n).trans (hT n), hL⟩

/-- Arithmetic core: the overhead `s + 2(n + C s) + 2 + P(n + C s)` is `≤ K·M^{k0+1}`. -/
theorem overhead_le (k0 A C n s M : ℕ) (P : Polynomial ℕ) (hP : ∀ x, P.eval x ≤ BGS.clk k0 x)
    (hM1 : 1 ≤ M) (hn : n ≤ M) (hs : s ≤ A * M) :
    s + 2 * (n + C * s) + 2 + P.eval (n + C * s) ≤
      (A + 2 * (C * A + 1) + 2 + k0 * (C * A + 2) ^ k0) * M ^ (k0 + 1) := by
  have hx : n + C * s ≤ (C * A + 1) * M := by
    have : C * s ≤ C * (A * M) := Nat.mul_le_mul_left _ hs
    have e : (C * A + 1) * M = C * (A * M) + M := by ring
    omega
  have hPx : P.eval (n + C * s) ≤ k0 * (C * A + 2) ^ k0 * M ^ k0 := by
    refine (hP _).trans ?_
    unfold BGS.clk
    have h1 : n + C * s + 1 ≤ (C * A + 2) * M := by
      have e : (C * A + 2) * M = (C * A + 1) * M + M := by ring
      omega
    calc k0 * (n + C * s + 1) ^ k0 ≤ k0 * ((C * A + 2) * M) ^ k0 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = k0 * (C * A + 2) ^ k0 * M ^ k0 := by rw [mul_pow]; ring
  have hQ1 : M ≤ M ^ (k0 + 1) := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ (k0 + 1) := Nat.pow_le_pow_right hM1 (by omega)
  have hQ2 : M ^ k0 ≤ M ^ (k0 + 1) := Nat.pow_le_pow_right hM1 (by omega)
  generalize M ^ (k0 + 1) = Q at hQ1 hQ2
  generalize M ^ k0 = R at hPx hQ2
  generalize k0 * (C * A + 2) ^ k0 = E at hPx ⊢
  have a1 : (A + 2 * (C * A + 1)) * M ≤ (A + 2 * (C * A + 1)) * Q := Nat.mul_le_mul_left _ hQ1
  have a2 : E * R ≤ E * Q := Nat.mul_le_mul_left _ hQ2
  have a3 : C * s ≤ C * (A * M) := Nat.mul_le_mul_left _ hs
  have e1 : (A + 2 * (C * A + 1) + 2 + E) * Q = (A + 2 * (C * A + 1)) * Q + 2 * Q + E * Q := by ring
  have e2 : (A + 2 * (C * A + 1)) * M = A * M + 2 * (C * (A * M)) + 2 * M := by ring
  have hQ0 : 1 ≤ Q := hM1.trans hQ1
  omega

/-- **Time hierarchy with a universal exponent.** -/
theorem time_hierarchy_pow : ∃ k : ℕ, 1 ≤ k ∧ ∀ (t : ℕ → ℕ)
    (hp : TM2ComputableInTime strEnc strEnc (padWith t)) (A a : ℕ), 1 ≤ a →
    (∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) →
    ∃ K, InDTIME (fun n => K * (t n + n + 1) ^ (k * a)) (diagT t) ∧
      ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (diagT t) := by
  obtain ⟨P, hP⟩ := diagT_in_DTIME
  obtain ⟨k0, hk0⟩ := BGS.poly_le_clk P
  refine ⟨k0 + 1, by omega, fun t hp A a ha hA =>
    ⟨A + 2 * (pushTotal hp.tm * A + 1) + 2 + k0 * (pushTotal hp.tm * A + 2) ^ k0, ?_,
      fun T hT => diagT_not_in_DTIME t T hT⟩⟩
  refine (hP t hp).mono (fun n => ?_)
  have hm : 1 ≤ t n + n + 1 := by omega
  have hM1 : 1 ≤ (t n + n + 1) ^ a := Nat.one_le_pow _ _ hm
  have hn : n ≤ (t n + n + 1) ^ a :=
    le_trans (by omega : n ≤ t n + n + 1) (by
      calc t n + n + 1 = (t n + n + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right hm ha)
  have := overhead_le k0 A (pushTotal hp.tm) n (hp.time n) ((t n + n + 1) ^ a) P hk0 hM1 hn (hA n)
  rw [← pow_mul, mul_comm a (k0 + 1)] at this
  exact this

/-- `padWith (2^·)` is the exponential padding `padF`. -/
noncomputable def padExp : TM2ComputableInTime strEnc strEnc (padWith (fun n => 2 ^ n)) :=
  padComputable

/-- **Exponential-time hierarchy instance**: some language is decidable in time `K·(2ⁿ+n+1)^k`
but not in time `2ⁿ/(n+1)`. -/
theorem exp_time_hierarchy : ∃ k K : ℕ, ∃ L : Language,
    InDTIME (fun n => K * (2 ^ n + n + 1) ^ k) L ∧ ¬ InDTIME (fun n => 2 ^ n / (n + 1)) L := by
  obtain ⟨k, -, hk⟩ := time_hierarchy_pow
  obtain ⟨K, h1, h2⟩ := hk (fun n => 2 ^ n) padExp 9 1 le_rfl (fun n => by
    show 4 * 2 ^ n + 5 * n + 4 ≤ 9 * (2 ^ n + n + 1) ^ 1
    rw [pow_one]; omega)
  refine ⟨k * 1, K, _, h1, h2 _ (fun D => ⟨D, fun n hn => ?_⟩)⟩
  have h3 : (n + 1) * (2 ^ n / (n + 1)) ≤ 2 ^ n := Nat.mul_div_le _ _
  have h4 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h5 : 1 ≤ 2 ^ n / (n + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h6 : D * (2 ^ n / (n + 1)) ≤ n * (2 ^ n / (n + 1)) := Nat.mul_le_mul_right _ hn
  have e : (n + 1) * (2 ^ n / (n + 1)) = n * (2 ^ n / (n + 1)) + 2 ^ n / (n + 1) := by ring
  omega

end PvnpReal
