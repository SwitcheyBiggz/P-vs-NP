/-
  PvnpReal.BruteEXP — **SAT ∈ EXP** by brute force, hence **NP ⊆ EXP** (unconditionally).

  Decider: `x ↦ pad x = 1^{2^|x|} 0 x` (exponential-time machine `padComputable`), then the
  polynomial-time search `1ᴺ0x ↦ ∃ i < N, verify x (binL i)` (in time polynomial in `N + |x|`).
-/
import PvnpReal.PadTM
import PvnpReal.Classes
import PvnpReal.Tab2Print

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

theorem codeL_eq_range (a : List Bool) :
    codeL a = (List.range a.length).flatMap
      (fun j => true :: (List.replicate (NthTM.bit a j) true ++ [false])) := by
  induction a with
  | nil => simp [codeL]
  | cons c a ih =>
    have hb : ∀ j, NthTM.bit (c :: a) (j + 1) = NthTM.bit a j := fun j => by simp [NthTM.bit]
    have h0 : (if c = true then [true, false] else [false]) =
        List.replicate (NthTM.bit (c :: a) 0) true ++ [false] := by
      cases c <;> simp [NthTM.bit]
    simp only [codeL] at ih ⊢
    rw [List.flatMap_cons, ih, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp only [Function.comp_def, hb, h0]

/-- Printing the self-delimiting code of a polytime string is polytime. -/
theorem PS.codeL {s : List Bool → List Bool} (hs : PS s) : PS (fun z => codeL (s z)) := by
  have hN : PU (fun z => (s z).length) := PU.lenX.comp hs
  have hg : PS (fun z => List.replicate (lpN z) true ++ false :: s (lpX z)) :=
    PS.append PU.fst (PS.cons false (PS.comp PS.drop hs))
  have hU : PU (fun z => NthTM.bit (s (lpX z)) (lpN z)) :=
    (PU.nth.comp hg).congr (fun z => by simp only [lpN_rep, lpX_rep])
  have hb : PS (fun z => true :: (List.replicate (NthTM.bit (s (lpX z)) (lpN z)) true ++ [false])) :=
    PS.cons true (PS.append hU (PS.const [false]))
  exact (PS.flatRange hN (fun j z => true :: (List.replicate (NthTM.bit (s z) j) true ++ [false]))
    hb).congr (fun z => (codeL_eq_range _).symm)

/-- The search body `1ⁱ0 1ʲ0 x ↦ [verify x (binL i)]` is polytime. -/
theorem PS.body : PS (fun z => [verify (lpX (lpX z)) (PvnpReal.binL (lpN z))]) := by
  have hc : PS (fun z => codeP (lpX (lpX z)) (PvnpReal.binL (lpN z))) :=
    PS.append (PS.codeL PS.drop2) (PS.cons false (PS.codeL PS.binL))
  have hv : PS (fun y => [verify (decP y).1 (decP y).2]) :=
    ⟨deciderToStr (composeGen decComputable satVerifierComputable)⟩
  exact (PS.comp hc hv).congr (fun z => by simp only [decP_codeP])

/-- Brute-force search over the first `N` assignments, input `1ᴺ0x`. -/
def searchB (y : List Bool) : Bool := (List.range (lpN y)).any (fun i => verify (lpX y) (binL i))

theorem PS.search : PS (fun y => [searchB y]) := by
  have h1 := PS.flatRange PU.fst (fun i y => [verify (lpX y) (PvnpReal.binL i)]) PS.body
  refine (PS.comp h1 ⟨orComputable⟩).congr (fun y => ?_)
  simp only [SmallTM.orF, searchB, List.cons.injEq, and_true]
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

theorem searchB_padF (x : List Bool) : searchB (padF x) = true ↔ SATLang x := by
  rw [SATLang_iff_exists_bin, searchB, padF, lpN_rep, lpX_rep]
  simp [List.any_eq_true]

/-- A polynomial evaluated at `2^m` is at most `2^{r(m)}` for a polynomial `r`. -/
theorem poly_two_pow (p : Polynomial ℕ) : ∃ r : Polynomial ℕ, ∀ m, p.eval (2 ^ m) ≤ 2 ^ (r.eval m) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 1, fun m => ?_⟩
    have h1 := ha m
    have h2 := hb m
    have e1 : 2 ^ a.eval m ≤ 2 ^ (a.eval m + b.eval m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : 2 ^ b.eval m ≤ 2 ^ (a.eval m + b.eval m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_one, pow_succ]
    omega
  | monomial n c =>
    refine ⟨Polynomial.C c + Polynomial.C n * Polynomial.X, fun m => ?_⟩
    simp only [Polynomial.eval_monomial, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X]
    calc c * (2 ^ m) ^ n ≤ 2 ^ c * 2 ^ (n * m) :=
          Nat.mul_le_mul (Nat.lt_two_pow_self).le (by rw [← pow_mul, Nat.mul_comm])
      _ = 2 ^ (c + n * m) := (pow_add _ _ _).symm

/-- **SAT ∈ EXP** (brute force over all `2^|x|` candidate assignments). -/
theorem SAT_in_EXP : InEXP SATLang := by
  obtain ⟨hs⟩ := PS.search
  let h2 := strToDecider hs
  let P := h2.time
  let hc := composeInTime padComputable h2.toTM2ComputableInTime (fun m => P.eval m)
    (fun m => le_rfl) (fun a b h => poly_eval_mono P h)
  obtain ⟨r, hr⟩ := poly_two_pow P
  set C := pushTotal padComputable.tm
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C (C + 5)) +
    r.comp (Polynomial.X + Polynomial.C (C + 5)) + 3
  refine ⟨searchB ∘ padF, q, ⟨hc, fun n => ?_⟩, fun x => (searchB_padF x).symm⟩
  change (4 * 2 ^ n + 5 * n + 4) + 2 * (n + C * (4 * 2 ^ n + 5 * n + 4)) + 2 +
    P.eval (n + C * (4 * 2 ^ n + 5 * n + 4)) ≤ 2 ^ q.eval n
  set E := n + (C + 5) with hE
  set R := r.eval E
  have hq : q.eval n = E + R + 3 := by
    simp only [q, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_ofNat]
    rfl
  rw [hq]
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have hT : 4 * 2 ^ n + 5 * n + 4 ≤ 16 * 2 ^ n := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hC1 : C + 1 ≤ 2 ^ (C + 1) := (Nat.lt_two_pow_self).le
  have hEe : 2 ^ E = 2 ^ (C + 1) * (16 * 2 ^ n) := by
    rw [hE, show n + (C + 5) = (C + 1) + (4 + n) by omega, pow_add, pow_add]; ring
  have hM : n + C * (4 * 2 ^ n + 5 * n + 4) ≤ 2 ^ E := by
    have a1 : C * (4 * 2 ^ n + 5 * n + 4) ≤ C * (16 * 2 ^ n) := Nat.mul_le_mul_left _ hT
    have a2 : (C + 1) * (16 * 2 ^ n) ≤ 2 ^ (C + 1) * (16 * 2 ^ n) := Nat.mul_le_mul_right _ hC1
    have a3 : (C + 1) * (16 * 2 ^ n) = C * (16 * 2 ^ n) + 16 * 2 ^ n := by ring
    omega
  have h16 : 16 * 2 ^ n ≤ 2 ^ E := by
    rw [hEe]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hP : P.eval (n + C * (4 * 2 ^ n + 5 * n + 4)) ≤ 2 ^ R :=
    (poly_eval_mono P hM).trans (hr E)
  have g1 : 2 ^ E ≤ 2 ^ (E + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have g2 : 2 ^ R ≤ 2 ^ (E + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have g3 : 1 ≤ 2 ^ (E + R) := Nat.one_le_two_pow
  have g4 : 2 ^ (E + R + 3) = 8 * 2 ^ (E + R) := by rw [pow_add]; ring
  omega

/-- **NP ⊆ EXP** (unconditional). -/
theorem NP_subset_EXP (L : Language) (hL : InNP L) : InEXP L :=
  NP_subset_EXP_of_SAT_in_EXP SAT_in_EXP L hL

end PvnpReal
