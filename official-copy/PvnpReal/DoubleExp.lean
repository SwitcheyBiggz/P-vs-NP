/-
  PvnpReal.DoubleExp — concrete instances of the time and space hierarchies with a doubly
  exponential clock `t₂(n) = 2^(2ⁿ + n + 1)`, whose padding is computed by `padF ∘ padF` followed
  by a polytime rearrangement.

  * **`double_exp_hierarchy`**: there are `c, K` and a language `L` with
    `L ∈ DTIME(K·(t₂(n)+n+1)^c)`, `L ∈ DSPACE(K·(t₂(n)+n+1)^c)`, `L ∉ EXP` and `L ∉ PSPACE`.
-/
import PvnpReal.Space
import PvnpReal.Hierarchy

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

def t2 (n : ℕ) : ℕ := 2 ^ (2 ^ n + n + 1)

/-- Transport a timed machine along an equality of functions (time unchanged). -/
noncomputable def tmCast {f g : List Bool → List Bool}
    (h : TM2ComputableInTime strEnc strEnc f) (e : f = g) : TM2ComputableInTime strEnc strEnc g :=
  e ▸ h

theorem tmCast_time {f g : List Bool → List Bool}
    (h : TM2ComputableInTime strEnc strEnc f) (e : f = g) : (tmCast h e).time = h.time := by
  subst e; rfl

theorem PS.rearr : PS (fun z => List.replicate (lpN z) true ++ false :: lpX (lpX z)) :=
  PS.append PU.fst (PS.cons false PS.drop2)

theorem T1_le (m : ℕ) : 4 * 2 ^ m + 5 * m + 4 ≤ 13 * 2 ^ m := by
  have := @Nat.lt_two_pow_self m
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

theorem T1_mono : Monotone (fun m : ℕ => 4 * 2 ^ m + 5 * m + 4) := by
  intro a b h
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
  simp only; omega

noncomputable def pad2 : TM2ComputableInTime strEnc strEnc (padF ∘ padF) :=
  composeInTime padComputable padComputable (fun m => 4 * 2 ^ m + 5 * m + 4) (fun _ => le_rfl) T1_mono

theorem pad2_time (n : ℕ) :
    pad2.time n ≤ (30 + 2 * (13 * pushTotal padComputable.tm + 1)) *
      (2 ^ 2 ^ n) ^ (13 * pushTotal padComputable.tm + 1) := by
  set C := pushTotal padComputable.tm
  set c1 := 13 * C + 1
  show (4 * 2 ^ n + 5 * n + 4) + 2 * (n + C * (4 * 2 ^ n + 5 * n + 4)) + 2 +
    (4 * 2 ^ (n + C * (4 * 2 ^ n + 5 * n + 4)) + 5 * (n + C * (4 * 2 ^ n + 5 * n + 4)) + 4) ≤ _
  set u := 2 ^ n with hu
  have hn : n < u := Nat.lt_two_pow_self
  have hT : 4 * u + 5 * n + 4 ≤ 13 * u := T1_le n
  have hm1 : n + C * (4 * u + 5 * n + 4) ≤ c1 * u := by
    have : C * (4 * u + 5 * n + 4) ≤ C * (13 * u) := Nat.mul_le_mul_left _ hT
    have e : c1 * u = C * (13 * u) + u := by simp only [c1]; ring
    omega
  set E := 2 ^ u
  have hE : 2 ^ (c1 * u) = E ^ c1 := by rw [mul_comm, pow_mul]
  have h2 := (T1_mono hm1).trans (T1_le (c1 * u))
  simp only at h2
  rw [hE] at h2
  have huE : u ≤ E := (Nat.lt_two_pow_self).le
  have hc1 : 1 ≤ c1 := by omega
  have hEc : E ≤ E ^ c1 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ c1 := Nat.pow_le_pow_right (Nat.one_le_two_pow) hc1
  have hm1' : n + C * (4 * u + 5 * n + 4) ≤ c1 * E ^ c1 :=
    hm1.trans (Nat.mul_le_mul_left _ (huE.trans hEc))
  have h1E : 1 ≤ E ^ c1 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  generalize E ^ c1 = Q at h2 hm1' hEc h1E
  have e1 : (30 + 2 * c1) * Q = 30 * Q + 2 * (c1 * Q) := by ring
  omega

noncomputable def hRe : TM2ComputableInPolyTime strEnc strEnc
    (fun z => List.replicate (lpN z) true ++ false :: lpX (lpX z)) := Classical.choice PS.rearr

theorem padT2_eq : (fun z => List.replicate (lpN z) true ++ false :: lpX (lpX z)) ∘ (padF ∘ padF) =
    padWith t2 := by
  funext x
  simp only [Function.comp, padF, padWith, t2, lpN_rep, lpX_rep, List.length_append,
    List.length_replicate, List.length_cons]
  congr 3

noncomputable def pad3 := composeInTime pad2 hRe.toTM2ComputableInTime (fun m => hRe.time.eval m)
    (fun _ => le_rfl) (fun _ _ h => poly_eval_mono _ h)

/-- A padding machine for `t₂`. -/
noncomputable def padT2 : TM2ComputableInTime strEnc strEnc (padWith t2) := tmCast pad3 padT2_eq

theorem padT2_time : ∃ A a : ℕ, 1 ≤ a ∧ ∀ n, padT2.time n ≤ A * (t2 n + n + 1) ^ a := by
  obtain ⟨k0, hk0⟩ := BGS.poly_le_clk hRe.time
  set C := pushTotal padComputable.tm
  set c1 := 13 * C + 1
  set A1 := 30 + 2 * (13 * C + 1)
  set C2 := pushTotal pad2.tm
  have hc1 : 1 ≤ c1 := by omega
  refine ⟨A1 + 2 * (C2 * A1 + 1) + 2 + k0 * (C2 * A1 + 2) ^ k0, c1 * (k0 + 1),
    by have := Nat.mul_le_mul hc1 (show 1 ≤ k0 + 1 by omega); simpa using this, fun n => ?_⟩
  rw [padT2, tmCast_time]
  show pad2.time n + 2 * (n + C2 * pad2.time n) + 2 + hRe.time.eval (n + C2 * pad2.time n) ≤ _
  set E := 2 ^ 2 ^ n
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have hEc : E ≤ E ^ c1 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ c1 := Nat.pow_le_pow_right hE1 hc1
  have hnE : n ≤ E := le_trans (Nat.lt_two_pow_self).le (Nat.lt_two_pow_self).le
  have := overhead_le k0 A1 C2 n (pad2.time n) (E ^ c1) hRe.time hk0
    (Nat.one_le_pow _ _ hE1) (hnE.trans hEc) (pad2_time n)
  refine this.trans (Nat.mul_le_mul_left _ ?_)
  rw [← pow_mul]
  apply Nat.pow_le_pow_left
  have : E ≤ t2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem t2_dominates (D A B : ℕ) (p : Polynomial ℕ) :
    ∃ N, ∀ n ≥ N, D * (A * B ^ p.eval n) + 1 ≤ t2 n := by
  obtain ⟨N, hN⟩ := poly_le_two_pow_eventually (Polynomial.C (D + A) + Polynomial.C B * p)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul] at h1
  set m := p.eval n
  have hB : B ^ m ≤ 2 ^ (B * m) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have hD : D + 1 ≤ 2 ^ D := Nat.lt_two_pow_self
  have hA : A + 1 ≤ 2 ^ A := Nat.lt_two_pow_self
  have hX : 1 ≤ 2 ^ (B * m) := Nat.one_le_two_pow
  have s1 : D * (A * B ^ m) + 1 ≤ (D + 1) * ((A + 1) * 2 ^ (B * m)) := by
    have : A * B ^ m ≤ A * 2 ^ (B * m) := Nat.mul_le_mul_left _ hB
    have : D * (A * B ^ m) ≤ D * ((A + 1) * 2 ^ (B * m)) :=
      Nat.mul_le_mul_left _ (this.trans (Nat.mul_le_mul_right _ (by omega)))
    have : 1 ≤ (A + 1) * 2 ^ (B * m) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have s2 : (D + 1) * ((A + 1) * 2 ^ (B * m)) ≤ 2 ^ D * (2 ^ A * 2 ^ (B * m)) :=
    Nat.mul_le_mul hD (Nat.mul_le_mul_right _ hA)
  have s3 : 2 ^ D * (2 ^ A * 2 ^ (B * m)) = 2 ^ (D + A + B * m) := by rw [pow_add, pow_add]; ring
  have s4 : 2 ^ (D + A + B * m) ≤ t2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Doubly exponential instance of the time and space hierarchies**: some language is decidable
in time and space `K·(t₂(n)+n+1)^c` (`t₂(n) = 2^(2ⁿ+n+1)`) but lies neither in EXP nor in PSPACE. -/
theorem double_exp_hierarchy : ∃ (c K : ℕ) (L : Language),
    InDTIME (fun n => K * (t2 n + n + 1) ^ c) L ∧ InDSPACE (fun n => K * (t2 n + n + 1) ^ c) L ∧
      ¬ InEXP L ∧ ¬ InPSPACE L := by
  obtain ⟨A, a, ha, hA⟩ := padT2_time
  obtain ⟨k, hk, hT⟩ := time_hierarchy_pow
  obtain ⟨K1, h1, hlow⟩ := hT t2 padT2 A a ha hA
  obtain ⟨k', hk', hS⟩ := space_hierarchy
  obtain ⟨K2, h2, hlowS⟩ := hS t2 padT2 A a ha hA
  refine ⟨(k + k') * a, K1 + K2, diagT t2,
    h1.mono (fun n => Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))),
    h2.mono (fun n => Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))), ?_, ?_⟩
  · rintro ⟨f, p, ⟨h, hb⟩, hf⟩
    refine hlow (fun n => 2 ^ p.eval n) (fun D => ?_) ⟨f, h, hb, hf⟩
    obtain ⟨N, hN⟩ := t2_dominates D 1 2 p
    exact ⟨N, fun n hn => by simpa using hN n hn⟩
  · rintro ⟨p, hp⟩
    exact hlowS _ (fun A B D => t2_dominates D A B p) hp

end PvnpReal
