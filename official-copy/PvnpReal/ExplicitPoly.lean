/-
  PvnpReal.ExplicitPoly — the polynomial time hierarchy with explicit exponents, from
  `time_hierarchy_42` and an explicit-degree padding machine for `t(n) = nᵏ`.
-/
import PvnpReal.ExplicitCost2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-- `x ↦ 1^{|x|} 0 1^{|x|^k}`. -/
def powF (k : ℕ) (x : List Bool) : List Bool := pairU x.length (x.length ^ k)

theorem PSl.powF (k : ℕ) : PSl (2 * (k + 1)) (k + 1) (powF k) := by
  induction k with
  | zero =>
    have h1 : PSl 1 1 SmallTM.lenF := PSl.of (PSd.of_lin SmallTM.lenComputable 1 2
      (by simp [SmallTM.lenComputable])) 2 (fun x => by simp [SmallTM.lenF])
    have hl : ∀ x, SmallTM.lenF x = pairU x.length 0 := fun x => by simp [SmallTM.lenF, pairU]
    have h2 := PSl.compT h1 (PSd.horner 1) le_rfl 2 (l := 1) (fun x => by
      rw [hl, hornerF_pairU]; simp [pairU]; omega)
    refine (h2.mono (by norm_num) le_rfl).congr (fun x => ?_)
    rw [hl, hornerF_pairU]; simp [PvnpReal.powF]
  | succ k ih =>
    have h2 := PSl.compT ih (PSd.horner 0) (by omega) 2 (l := k + 2) (fun x => by
      rw [PvnpReal.powF, hornerF_pairU]
      simp only [pairU, List.length_append, List.length_replicate, List.length_cons]
      have a1 : x.length + 1 ≤ (x.length + 1) ^ (k + 2) := by
        calc x.length + 1 = (x.length + 1) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have a2 : x.length * x.length ^ k ≤ (x.length + 1) ^ (k + 2) := by
        rw [← pow_succ']
        exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
      omega)
    refine (h2.mono (by omega) le_rfl).congr (fun x => ?_)
    simp [PvnpReal.powF, hornerF_pairU, pow_succ, mul_comm]

/-- Padding for `t(n) = nᵏ` with explicit degrees. -/
theorem PSl.padPow (k : ℕ) : PSl (2 * (k + 1)) (k + 1) (padWith (fun n => n ^ k)) := by
  have hs := PSl.compT (PSl.powF k) (PSd.of_lin SmallTM.sndComputable 1 2
    (by simp [SmallTM.sndComputable])) (by omega) 1 (l := k + 1) (fun x => by
      simp only [PvnpReal.powF, SmallTM.sndF, hM_pairU, List.length_replicate, one_mul]
      exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  have hs' : PSl (2 * (k + 1)) (k + 1) (fun x => List.replicate (x.length ^ k) true) :=
    (hs.mono (max_le le_rfl (by omega)) le_rfl).congr (fun x => by
      simp [PvnpReal.powF, SmallTM.sndF, hM_pairU])
  have hc := PSl.cons false (PSl.id.mono (by omega : 1 ≤ 2 * (k + 1)) (by omega : 1 ≤ k + 1))
    (by omega)
  exact ((PSl.append hs' hc (by omega)).mono (by simp) (by simp)).congr (fun x => rfl)

theorem succ_pow_le (n k : ℕ) : (n + 1) ^ k ≤ 2 ^ k * (n ^ k + n + 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
    exact le_trans Nat.one_le_two_pow (Nat.le_mul_of_pos_right _ (by positivity))
  · calc (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ k * n ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (n ^ k + n + 1) := Nat.mul_le_mul_left _ (by omega)

/-- **Explicit polynomial time hierarchy, per level**: for every `k`,
`diagT nᵏ ∈ DTIME(K·(nᵏ+n+1)^{168})` and `diagT nᵏ ∉ DTIME(T)` for every `T = o(nᵏ)`. -/
theorem poly_time_hierarchy_168 (k : ℕ) :
    ∃ K, InDTIME (fun n => K * (n ^ k + n + 1) ^ 168) (diagT (fun n => n ^ k)) ∧
      ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ n ^ k) →
        ¬ InDTIME T (diagT (fun n => n ^ k)) := by
  obtain ⟨h, K, hT, -⟩ := PSl.padPow k
  have hA : ∀ n, h.toTM2ComputableInTime.time n ≤ K * 4 ^ k * (n ^ k + n + 1) ^ 4 := by
    intro n
    show h.time.eval n ≤ _
    refine (hT n).trans ?_
    rw [mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    set M := n ^ k + n + 1
    have h1 := succ_pow_le n k
    have h2 : n + 1 ≤ M := by omega
    calc (n + 1) ^ (2 * (k + 1)) = ((n + 1) ^ k) ^ 2 * (n + 1) ^ 2 := by ring
      _ ≤ (2 ^ k * M) ^ 2 * M ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left h1 _)
          (Nat.pow_le_pow_left h2 _)
      _ = (2 ^ k) ^ 2 * M ^ 4 := by ring
      _ = 4 ^ k * M ^ 4 := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  obtain ⟨K', h1, h2⟩ := time_hierarchy_42 (fun n => n ^ k) h.toTM2ComputableInTime (K * 4 ^ k) 4
    (by norm_num) hA
  exact ⟨K', by simpa using h1, h2⟩

/-- **`DTIME(nʲ) ⊊ DTIME(n^{168(j+1)})`** (up to the constant `K`): an explicit-exponent polynomial
time hierarchy. -/
theorem poly_hierarchy_explicit (j : ℕ) : ∃ K, ∃ L : Language,
    InDTIME (fun n => K * (n + 1) ^ (168 * (j + 1))) L ∧ ¬ InDTIME (fun n => n ^ j) L := by
  obtain ⟨K, h1, h2⟩ := poly_time_hierarchy_168 (j + 1)
  refine ⟨K * 3 ^ 168, _, h1.mono (fun n => ?_), h2 _ (fun D => ⟨D + 1, fun n hn => ?_⟩)⟩
  · have hM : n ^ (j + 1) + n + 1 ≤ 3 * (n + 1) ^ (j + 1) := by
      have a1 : n ^ (j + 1) ≤ (n + 1) ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
      have a2 : n + 1 ≤ (n + 1) ^ (j + 1) := by
        calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    calc K * (n ^ (j + 1) + n + 1) ^ 168 ≤ K * (3 * (n + 1) ^ (j + 1)) ^ 168 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM _)
      _ = K * 3 ^ 168 * (n + 1) ^ (168 * (j + 1)) := by rw [mul_pow, ← pow_mul]; ring
  · have h3 : 1 ≤ n ^ j := Nat.one_le_pow _ _ (by omega)
    have h4 : (D + 1) * n ^ j ≤ n * n ^ j := Nat.mul_le_mul_right _ hn
    have e : n ^ (j + 1) = n * n ^ j := by ring
    have e2 : (D + 1) * n ^ j = D * n ^ j + n ^ j := by ring
    omega

end PvnpReal
