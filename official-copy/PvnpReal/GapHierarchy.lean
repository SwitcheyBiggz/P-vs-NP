/-
  PvnpReal.GapHierarchy — time hierarchies with an **explicit exponent gap**, without computing the
  interpreter's overhead degree.

  The universal interpreter `U2` has an (uncomputed) polynomial overhead, so `time_hierarchy_pow`
  only gives an unknown exponent `k`. Here we extract explicit-gap statements by a pure
  *chain (pigeonhole) argument*: if `L ∉ DTIME(T₀)` and `L ∈ DTIME(T_j)` for a chain
  `T₀ ≤ T₁ ≤ … ≤ T_j`, then some consecutive pair separates `L`.

  * `dtime_chain` — the chain lemma.
  * `poly_gap_hierarchy` — for every `k` there is an `e ≥ k` and `L ∈ P` with
    `L ∈ DTIME((n+2)^{e+1})` and `L ∉ DTIME(n^e)`; hence the gap `n^e ⊊ (n+2)^{e+1}` occurs at
    infinitely many (unboundedly large) exponents `e`.
  * `time_hierarchy_gap` — for every padding-constructible `t`, with `M = t(n)+n+2`, `diagT t` is either
    in `DTIME(M)` (and outside `DTIME(o(t))`), or there is `e ≥ 1` with `diagT t ∈ DTIME(M^{e+1}) \ DTIME(M^e)`.

  NOT proven: the gap at EVERY exponent (`DTIME(n^e) ⊊ DTIME(n^{e+1})` for all `e`), nor
  `t·log t`/`t·polylog t` — those need an explicit cost bound for a universal simulator.
-/
import PvnpReal.TimeHierarchy2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-- **Chain lemma**: a language outside `DTIME(T 0)` but inside `DTIME(T j)` is separated by some
consecutive pair of the chain. -/
theorem dtime_chain (L : Language) (T : ℕ → ℕ → ℕ) :
    ∀ j, ¬ InDTIME (T 0) L → InDTIME (T j) L → ∃ i < j, ¬ InDTIME (T i) L ∧ InDTIME (T (i + 1)) L := by
  intro j
  induction j with
  | zero => intro h0 hj; exact absurd hj h0
  | succ j ih =>
    intro h0 hj
    by_cases hJ : InDTIME (T j) L
    · obtain ⟨i, hi, h1, h2⟩ := ih h0 hJ
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨j, by omega, hJ, hj⟩

/-- `K·x^d ≤ (x+1)^{d+K}` for `x ≥ 1`. -/
theorem absorb_const (K d x : ℕ) (hx : 1 ≤ x) : K * x ^ d ≤ (x + 1) ^ (d + K) := by
  have h1 : K ≤ (x + 1) ^ K :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
  have h2 : x ^ d ≤ (x + 1) ^ d := Nat.pow_le_pow_left (by omega) _
  rw [pow_add, mul_comm ((x + 1) ^ d)]
  exact Nat.mul_le_mul h1 h2

/-- Every language in P is in `DTIME((n+2)^d)` for some `d`. -/
theorem InP.dtime_pow {L : Language} (h : InP L) : ∃ d, InDTIME (fun n => (n + 2) ^ d) L := by
  obtain ⟨f, ⟨h⟩, hL⟩ := h
  obtain ⟨k, hk⟩ := BGS.poly_le_clk h.time
  refine ⟨k + k, f, h.toTM2ComputableInTime, fun n => ?_, hL⟩
  refine (hk n).trans ?_
  have := absorb_const k k (n + 1) (by omega)
  unfold BGS.clk
  simpa [mul_comm] using this

/-- **Explicit-gap polynomial hierarchy**: for every `k` there are `e ≥ k` and `L ∈ P` with
`L ∈ DTIME((n+2)^{e+1})` but `L ∉ DTIME(n^e)`. -/
theorem poly_gap_hierarchy (k : ℕ) : ∃ e ≥ k, ∃ L, InP L ∧
    InDTIME (fun n => (n + 2) ^ (e + 1)) L ∧ ¬ InDTIME (fun n => n ^ e) L := by
  obtain ⟨L, hP, hN⟩ := P_not_sub_DTIME_pow k
  obtain ⟨d, hd⟩ := hP.dtime_pow
  let T : ℕ → ℕ → ℕ := fun i n => if i = 0 then n ^ k else (n + 2) ^ (k + i)
  have hj : InDTIME (T (d + 1)) L := hd.mono (fun n => by
    simp only [T, if_neg (by omega : d + 1 ≠ 0)]
    exact Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨i, -, h1, h2⟩ := dtime_chain L T (d + 1) (by simpa [T] using hN) hj
  refine ⟨k + i, by omega, L, hP, ?_, fun hc => h1 ?_⟩
  · simpa [T, add_assoc] using h2
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simpa [T] using hc
    · refine hc.mono (fun n => ?_)
      simp only [T, if_neg (by omega : i ≠ 0)]
      exact Nat.pow_le_pow_left (by omega) _

/-- Consequence: the inclusion `DTIME((n+2)^{e+1}) ⊆ DTIME(n^e)` fails for unboundedly many `e`. -/
theorem poly_gap_infinitely_often (k : ℕ) :
    ∃ e ≥ k, ¬ ∀ L, InDTIME (fun n => (n + 2) ^ (e + 1)) L → InDTIME (fun n => n ^ e) L := by
  obtain ⟨e, he, L, -, h1, h2⟩ := poly_gap_hierarchy k
  exact ⟨e, he, fun h => h2 (h L h1)⟩

/-- Generic gap extraction for a base `B ≥ 1`. -/
theorem gap_of_pow_bound (L : Language) (B : ℕ → ℕ) (hB : ∀ n, 1 ≤ B n) (E : ℕ)
    (hE : InDTIME (fun n => B n ^ E) L) :
    InDTIME (fun n => B n ^ 1) L ∨
      ∃ e ≥ 1, InDTIME (fun n => B n ^ (e + 1)) L ∧ ¬ InDTIME (fun n => B n ^ e) L := by
  by_cases h1 : InDTIME (fun n => B n ^ 1) L
  · exact Or.inl h1
  · right
    let T : ℕ → ℕ → ℕ := fun i n => B n ^ (i + 1)
    have hj : InDTIME (T E) L := hE.mono (fun n => Nat.pow_le_pow_right (hB n) (by omega))
    obtain ⟨i, -, h3, h4⟩ := dtime_chain L T E h1 hj
    exact ⟨i + 1, by omega, h4, h3⟩

/-- **Time hierarchy with an explicit gap** for a padding-constructible `t`, `M = t(n)+n+2`:
either `diagT t ∈ DTIME(M)` (the linear-overhead case), or the separation
`DTIME(M^e) ⊊ DTIME(M^{e+1})` is witnessed by `diagT t` at some `e ≥ 1`. In both cases
`diagT t ∉ DTIME(T)` for every `T = o(t)`. -/
theorem time_hierarchy_gap (t : ℕ → ℕ) (hp : TM2ComputableInTime strEnc strEnc (padWith t))
    (A a : ℕ) (ha : 1 ≤ a) (hA : ∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) :
    (∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (diagT t)) ∧
    (InDTIME (fun n => (t n + n + 2) ^ 1) (diagT t) ∨
      ∃ e ≥ 1, InDTIME (fun n => (t n + n + 2) ^ (e + 1)) (diagT t) ∧
        ¬ InDTIME (fun n => (t n + n + 2) ^ e) (diagT t)) := by
  obtain ⟨k, -, hk⟩ := time_hierarchy_pow
  obtain ⟨K, hK, hT⟩ := hk t hp A a ha hA
  refine ⟨hT, gap_of_pow_bound _ _ (fun n => by omega) (k * a + K) (hK.mono (fun n => ?_))⟩
  simpa using absorb_const K (k * a) (t n + n + 1) (by omega)

/-- Exponential instance: with `M = 2ⁿ+n+2`, `diagT 2ⁿ ∉ DTIME(2ⁿ/(n+1))`, and either it is in
`DTIME(M)` or some `e ≥ 1` has it in `DTIME(M^{e+1}) \ DTIME(M^e)`. -/
theorem exp_time_hierarchy_gap :
    ¬ InDTIME (fun n => 2 ^ n / (n + 1)) (diagT (fun n => 2 ^ n)) ∧
    (InDTIME (fun n => (2 ^ n + n + 2) ^ 1) (diagT (fun n => 2 ^ n)) ∨
      ∃ e ≥ 1, InDTIME (fun n => (2 ^ n + n + 2) ^ (e + 1)) (diagT (fun n => 2 ^ n)) ∧
        ¬ InDTIME (fun n => (2 ^ n + n + 2) ^ e) (diagT (fun n => 2 ^ n))) := by
  obtain ⟨h1, h2⟩ := time_hierarchy_gap (fun n => 2 ^ n) padExp 9 1 le_rfl (fun n => by
    show 4 * 2 ^ n + 5 * n + 4 ≤ 9 * (2 ^ n + n + 1) ^ 1
    rw [pow_one]; omega)
  refine ⟨h1 _ (fun D => ⟨D, fun n hn => ?_⟩), h2⟩
  have h3 : (n + 1) * (2 ^ n / (n + 1)) ≤ 2 ^ n := Nat.mul_div_le _ _
  have h4 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h5 : 1 ≤ 2 ^ n / (n + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h6 : D * (2 ^ n / (n + 1)) ≤ n * (2 ^ n / (n + 1)) := Nat.mul_le_mul_right _ hn
  have e : (n + 1) * (2 ^ n / (n + 1)) = n * (2 ^ n / (n + 1)) + 2 ^ n / (n + 1) := by ring
  omega

end PvnpReal
