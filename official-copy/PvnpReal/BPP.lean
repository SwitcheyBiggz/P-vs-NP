/-
  PvnpReal.BPP — **bounded-error probabilistic polynomial time**, by counting.

  `accCount V x m` = number of random strings `w ∈ {0,1}^m` with `V (codeP x w)`.
  `InBPP L`: a polynomial-time `V` and a polynomial `q` with, for `m = q(|x|)`,
  `x ∈ L → accCount ≥ (2/3)·2^m` and `x ∉ L → accCount ≤ (1/3)·2^m` (stated multiplied out).
  No measure theory: everything is `Finset.card` over `Fin m → Bool`.

  * `P_subset_BPP`, `InBPP.compl` (closure under complement);
  * `maj_count`: the **counting Chernoff bound** for majority votes: if at most a third of `Ω` is
    bad, then the number of `2m`-tuples with `≥ m` bad entries is `≤ (8/9)^m · |Ω|^{2m}`
    (proof: weight `2^{#bad}`, `Σ_f Π_i w(f i) = (Σ_ω w ω)^{2m} = (|Ω| + |bad|)^{2m}`).
-/
import PvnpReal.Kannan

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

section Cl

open scoped Classical

/-- Accepting random strings of length `m`. -/
noncomputable def accCount (V : Language) (x : List Bool) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin m → Bool => V (codeP x (List.ofFn w)))).card

/-- **BPP** (two-sided error `1/3`). -/
def InBPP (L : Language) : Prop :=
  ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
    (L x → 2 * 2 ^ q.eval x.length ≤ 3 * accCount V x (q.eval x.length)) ∧
    (¬ L x → 3 * accCount V x (q.eval x.length) ≤ 2 ^ q.eval x.length)

theorem accCount_le (V : Language) (x : List Bool) (m : ℕ) : accCount V x m ≤ 2 ^ m := by
  unfold accCount
  calc _ ≤ (Finset.univ : Finset (Fin m → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ m := by simp

theorem accCount_compl (V : Language) (x : List Bool) (m : ℕ) :
    accCount (fun s => ¬ V s) x m = 2 ^ m - accCount V x m := by
  unfold accCount
  beta_reduce
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m → Bool)))
    (fun w : Fin m → Bool => V (codeP x (List.ofFn w)))
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  convert (Nat.eq_sub_of_add_eq' h) using 3

/-- **P ⊆ BPP** (no randomness: `q = 0`). -/
theorem P_subset_BPP {L : Language} (h : InP L) : InBPP L := by
  refine ⟨fun s => L (decP s).1, 0, h.compPS PS.fstP, fun x => ?_⟩
  simp only [Polynomial.eval_zero, pow_zero, accCount, decP_codeP]
  by_cases hx : L x
  · simp [hx]
  · simp [hx]

/-- **BPP is closed under complement.** -/
theorem InBPP.compl {L : Language} (h : InBPP L) : InBPP (fun x => ¬ L x) := by
  obtain ⟨V, q, hV, hq⟩ := h
  refine ⟨fun s => ¬ V s, q, hV.compl, fun x => ?_⟩
  rw [accCount_compl]
  have hle := accCount_le V x (q.eval x.length)
  obtain ⟨h1, h2⟩ := hq x
  constructor
  · intro hx; have := h2 hx; omega
  · intro hx; have := h1 (not_not.1 hx); omega

end Cl

/-! ### The counting Chernoff bound for majority votes -/

theorem sum_weight {Ω : Type} [Fintype Ω] (bad : Ω → Prop) [DecidablePred bad] :
    (∑ ω : Ω, (if bad ω then 2 else 1 : ℕ)) = Fintype.card Ω + (Finset.univ.filter bad).card := by
  have : ∀ ω : Ω, (if bad ω then 2 else 1 : ℕ) = 1 + (if bad ω then 1 else 0) := fun ω => by
    split_ifs <;> rfl
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Finset.sum_boole, Nat.cast_id]

theorem prod_weight {Ω : Type} {t : ℕ} (bad : Ω → Prop) [DecidablePred bad] (f : Fin t → Ω) :
    (∏ i : Fin t, (if bad (f i) then 2 else 1 : ℕ)) = 2 ^ (Finset.univ.filter (fun i => bad (f i))).card := by
  rw [Finset.prod_ite]
  simp

/-- **Majority-vote error count**: with at most a third of `Ω` bad, at most `(8/9)^m |Ω|^{2m}`
tuples of length `2m` have at least `m` bad entries. -/
theorem maj_count {Ω : Type} [Fintype Ω] (bad : Ω → Prop) [DecidablePred bad] (m : ℕ)
    (h : 3 * (Finset.univ.filter bad).card ≤ Fintype.card Ω) :
    9 ^ m * (Finset.univ.filter (fun f : Fin (2 * m) → Ω =>
      m ≤ (Finset.univ.filter (fun i => bad (f i))).card)).card ≤ 8 ^ m * Fintype.card Ω ^ (2 * m) := by
  set N := Fintype.card Ω
  set B := (Finset.univ.filter bad).card
  set W := Finset.univ.filter (fun f : Fin (2 * m) → Ω =>
      m ≤ (Finset.univ.filter (fun i => bad (f i))).card)
  have htot : (∑ f : Fin (2 * m) → Ω, ∏ i : Fin (2 * m), (if bad (f i) then 2 else 1 : ℕ)) =
      (N + B) ^ (2 * m) := by
    have := Finset.prod_univ_sum (fun _ : Fin (2 * m) => (Finset.univ : Finset Ω))
      (fun _ ω => (if bad ω then 2 else 1 : ℕ))
    rw [Fintype.piFinset_univ] at this
    rw [← this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, sum_weight]
  have hW : 2 ^ m * W.card ≤ (N + B) ^ (2 * m) := by
    rw [← htot]
    calc 2 ^ m * W.card = ∑ _f ∈ W, 2 ^ m := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ f ∈ W, ∏ i : Fin (2 * m), (if bad (f i) then 2 else 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro f hf
        rw [prod_weight]
        exact Nat.pow_le_pow_right (by norm_num) (Finset.mem_filter.1 hf).2
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hsq : 9 * (N + B) ^ 2 ≤ 16 * N ^ 2 := by nlinarith
  have h2 : (9 * (N + B) ^ 2) ^ m ≤ (16 * N ^ 2) ^ m := Nat.pow_le_pow_left hsq m
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 m] at h2
  have h16 : (16 : ℕ) ^ m = 2 ^ m * 8 ^ m := by rw [← mul_pow]; norm_num
  rw [h16] at h2
  have : 2 ^ m * (9 ^ m * W.card) ≤ 2 ^ m * (8 ^ m * N ^ (m * 2)) := by
    calc 2 ^ m * (9 ^ m * W.card) = 9 ^ m * (2 ^ m * W.card) := by ring
      _ ≤ 9 ^ m * (N + B) ^ (2 * m) := Nat.mul_le_mul_left _ hW
      _ = 9 ^ m * (N + B) ^ (m * 2) := by rw [mul_comm 2 m]
      _ ≤ 2 ^ m * 8 ^ m * N ^ (m * 2) := h2
      _ = 2 ^ m * (8 ^ m * N ^ (m * 2)) := by ring
  have e : N ^ (2 * m) = N ^ (m * 2) := by rw [mul_comm 2 m]
  rw [e]
  exact Nat.le_of_mul_le_mul_left this (by positivity)

end PvnpReal
