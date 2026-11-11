/-
  PvnpReal.LadnerH — Ladner's diagonal padding function, by clocked "lazy" diagonalization over
  `U2` programs. Definitions of the stage table `tab`, the slowly growing `H`, `gL m = m ^ H m`,
  and the combinatorial/semantic lemmas (M1–M7 of NOTES). The polytime machine for `H` is in
  `LadnerMachine.lean`; here, results needing it take it as a hypothesis `hH`.
-/
import PvnpReal.LadnerTools
import PvnpReal.OracleSep

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Flat

attribute [local instance] Classical.propDecidable

/-! ### Enumeration of programs -/

/-- The `s`-th program string: `binL s` without its leading-one (last) bit. -/
def prog (s : ℕ) : List Bool := (binL s).dropLast

theorem prog_surj (x : List Bool) : ∃ s, prog s = x := by
  obtain ⟨s, hs⟩ := binL_surj x
  exact ⟨s, by simp [prog, hs]⟩

theorem binL_len_pow : ∀ j, 0 < j → 2 ^ (binL j).length ≤ 2 * j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [binL]
    simp only [List.length_cons]
    by_cases hm : (n + 1) / 2 = 0
    · rw [hm, binL_zero]; simp
    · have := ih ((n + 1) / 2) (by omega) (by omega)
      rw [pow_succ]; omega

theorem prog_len (j : ℕ) : 2 ^ (prog j).length ≤ j + 1 := by
  rw [prog, List.length_dropLast]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [binL_zero]
  · have h := binL_len_pow j hj
    rcases Nat.eq_zero_or_pos (binL j).length with h0 | h0
    · rw [h0]; simp
    · have : 2 ^ (binL j).length = 2 * 2 ^ ((binL j).length - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega

theorem prog_len_le (j : ℕ) : (prog j).length ≤ j := by
  have h1 := prog_len j
  have h2 := Nat.lt_two_pow_self (n := (prog j).length)
  omega

/-! ### The stage table -/

/-- Clock of program `x` on inputs of length `m`: `k (m+1)^k`, `k = lpN x`. -/
def lclk (x : List Bool) (m : ℕ) : ℕ := lpN x * (m + 1) ^ lpN x

/-- Tag of the clocked interpreter. -/
def uTag (x y : List Bool) (t : ℕ) : ℕ := tagOf (stepL^[t] (initL (srcL x y t)))

theorem U2_uTag (x y : List Bool) (t : ℕ) :
    U2 x y t = if uTag x y t = 5 then some true else if uTag x y t = 0 then some false else none :=
  rfl

/-- The clock capped at `n + 1` (computed without ever writing large numbers). -/
def ccap (n : ℕ) (x : List Bool) (m : ℕ) : ℕ :=
  min (lpN x * min ((m + 1) ^ lpN x) (n + 1)) (n + 1)

theorem ccap_eq (n : ℕ) (x : List Bool) (m : ℕ) : ccap n x m = min (lclk x m) (n + 1) := by
  unfold ccap lclk
  generalize lpN x = k
  generalize (m + 1) ^ k = P
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · by_cases hP : P ≤ n + 1
    · rw [min_eq_left hP]
    · rw [min_eq_right (by omega : n + 1 ≤ P)]
      have h1 : n + 1 ≤ k * (n + 1) := Nat.le_mul_of_pos_left _ hk
      have h2 : n + 1 ≤ k * P := le_trans (by omega) (Nat.le_mul_of_pos_left P hk)
      rw [min_eq_right h1, min_eq_right h2]

/-- `0/1`-valued guess of `LH` membership at stage table `T`, for the `j`-th input `y`. -/
def LvN (T : List ℕ) (j : ℕ) (y : List Bool) : ℕ :=
  (if lpN y = min ((lpX y).length ^ T.getD (lpX y).length 0) (lpN y + 1) then 1 else 0) *
    lpN [searchB (List.replicate (j + 1) true ++ false :: lpX y)]

def badK (c n tg L : ℕ) : ℕ :=
  (if c = min c n then 1 else 0) *
    (1 - ((if tg = 5 then 1 else 0) * L + (if tg = 0 then 1 else 0) * (1 - L)))

/-- Is the `j`-th input a (clocked, within budget `n`) counterexample for the current program? -/
def badN (n : ℕ) (T : List ℕ) (j : ℕ) : ℕ :=
  badK (ccap n (prog (T.getD n 0)) (prog j).length) n
    (uTag (prog (T.getD n 0)) (prog j) (ccap n (prog (T.getD n 0)) (prog j).length))
    (LvN T j (prog j))

def found (n : ℕ) (T : List ℕ) : Bool := (List.range n).any (fun j => decide (badN n T j = 1))

/-- Stage table: entry `n` is the index of the program being diagonalized against at stage `n`. -/
def tab : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => tab n ++ [min ((tab n).getD n 0 + lpN [found n (tab n)]) (n + 1)]

def H (n : ℕ) : ℕ := (tab n).getD n 0

/-- **Ladner's padding function.** -/
def gL (m : ℕ) : ℕ := m ^ H m

theorem tab_len (n : ℕ) : (tab n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tab, ih]

theorem tab_get {n i : ℕ} (h : i ≤ n) : (tab n).getD i 0 = H i := by
  induction n with
  | zero => rw [show i = 0 by omega]; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with hi | hi
    · rw [tab, List.getD_append _ _ _ _ (by rw [tab_len]; omega), ih (by omega)]
    · rw [show i = n + 1 by omega]; rfl

theorem lpN_single (b : Bool) : lpN [b] = if b then 1 else 0 := by
  cases b <;> simp [lpN]

theorem H_succ' (n : ℕ) :
    H (n + 1) = min (H n + (if found n (tab n) then 1 else 0)) (n + 1) := by
  show (tab (n + 1)).getD (n + 1) 0 = _
  rw [tab, List.getD_append_right _ _ _ _ (by rw [tab_len])]
  simp [tab_len, lpN_single, H]

theorem H_le (n : ℕ) : H n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [H_succ']; exact min_le_right _ _

theorem H_succ (n : ℕ) : H (n + 1) = H n + (if found n (tab n) then 1 else 0) := by
  rw [H_succ']; have := H_le n; split_ifs <;> omega

theorem H_mono : Monotone H :=
  monotone_nat_of_le_succ (fun n => by rw [H_succ]; omega)

/-! ### Semantics of a stage -/

theorem searchB_bit (j : ℕ) (s : List Bool) (hs : 2 ^ s.length ≤ j + 1) :
    lpN [searchB (List.replicate (j + 1) true ++ false :: s)] = if SATLang s then 1 else 0 := by
  rw [lpN_single]
  by_cases h : SATLang s
  · rw [if_pos ((searchB_const hs).2 h), if_pos h]
  · rw [if_neg h, if_neg (fun e => h ((searchB_const hs).1 (by simpa using e)))]

theorem LvN_tab {n j : ℕ} (hj : j < n) :
    LvN (tab n) j (prog j) = if LH gL (prog j) then 1 else 0 := by
  have hl : (lpX (prog j)).length ≤ (prog j).length := by simp [lpX]
  have hj2 := prog_len_le j
  have hpow : 2 ^ (lpX (prog j)).length ≤ j + 1 :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hl) (prog_len j)
  unfold LvN
  rw [tab_get (by omega), searchB_bit j _ hpow]
  have e := check_iff gL (prog j)
  simp only [gL] at e
  by_cases h1 : lpN (prog j) = (lpX (prog j)).length ^ H (lpX (prog j)).length
  · have h1' := e.2 h1
    by_cases h2 : SATLang (lpX (prog j))
    · rw [if_pos h1', if_pos (show LH gL (prog j) from ⟨h1, h2⟩), if_pos h2]
    · rw [if_pos h1', if_neg (fun h : LH gL (prog j) => h2 h.2), if_neg h2]
  · have h1' : ¬ _ := fun x => h1 (e.1 x)
    rw [if_neg h1', if_neg (fun h : LH gL (prog j) => h1 h.1)]; simp

theorem badN_iff {n j : ℕ} (hj : j < n) :
    badN n (tab n) j = 1 ↔ lclk (prog (H n)) (prog j).length ≤ n ∧
      U2 (prog (H n)) (prog j) (lclk (prog (H n)) (prog j).length) ≠
        some (decide (LH gL (prog j))) := by
  unfold badN
  rw [LvN_tab hj, tab_get (le_refl n), ccap_eq, U2_uTag]
  generalize lclk (prog (H n)) (prog j).length = c
  by_cases hc : c ≤ n
  · rw [min_eq_left (by omega : c ≤ n + 1)]
    generalize uTag (prog (H n)) (prog j) c = tg
    unfold badK
    by_cases hL : LH gL (prog j) <;> by_cases h5 : tg = 5 <;> by_cases h0 : tg = 0 <;>
      simp [hL, h5, h0, hc] <;> omega
  · rw [min_eq_right (by omega : n + 1 ≤ c)]
    unfold badK
    simp only [hc, false_and, iff_false]
    rw [if_neg (by omega)]; simp

theorem found_iff (n : ℕ) :
    found n (tab n) = true ↔ ∃ j < n, lclk (prog (H n)) (prog j).length ≤ n ∧
      U2 (prog (H n)) (prog j) (lclk (prog (H n)) (prog j).length) ≠
        some (decide (LH gL (prog j))) := by
  unfold found
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (badN_iff hj).1 h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (badN_iff hj).2 h⟩

/-! ### The diagonalization lemmas -/

/-- Program `s` decides `LH gL` within its clock. -/
def Correct (s : ℕ) : Prop :=
  ∀ y, U2 (prog s) y (lclk (prog s) y.length) = some (decide (LH gL y))

/-- (M3) A correct program is never passed: `H n ≤ s`. -/
theorem H_le_of_correct {s : ℕ} (hs : Correct s) (n : ℕ) : H n ≤ s := by
  induction n with
  | zero => show (tab 0).getD 0 0 ≤ s; simp [tab]
  | succ n ih =>
    rw [H_succ]
    rcases Nat.lt_or_ge (H n) s with h | h
    · split_ifs <;> omega
    · have hH : H n = s := by omega
      have : found n (tab n) = false := by
        rcases Bool.eq_false_or_eq_true (found n (tab n)) with e | e
        · obtain ⟨j, -, -, hne⟩ := (found_iff n).1 e
          rw [hH] at hne; exact absurd (hs _) hne
        · exact e
      rw [this]; simp; omega

/-- (M2) If `H` stabilizes at `s`, program `s` is correct. -/
theorem correct_of_stable {N s : ℕ} (hN : ∀ n ≥ N, H n = s) : Correct s := by
  intro y
  by_contra hne
  obtain ⟨j, rfl⟩ := prog_surj y
  let n := max N (max (j + 1) (lclk (prog s) (prog j).length))
  have hn : N ≤ n := le_max_left _ _
  have hfound : found n (tab n) = true := by
    rw [found_iff, hN n hn]
    exact ⟨j, by omega, by omega, hne⟩
  have h1 := H_succ n
  rw [hfound, hN n hn, hN (n + 1) (by omega)] at h1
  simp at h1

/-- (M4) A bounded `H` is eventually constant. -/
theorem stable_of_bounded {B : ℕ} (hB : ∀ n, H n ≤ B) : ∃ N s, ∀ n ≥ N, H n = s := by
  classical
  let P : ℕ → Prop := fun v => ∃ n, v ≤ H n
  let s := Nat.findGreatest P B
  have hs : P s := Nat.findGreatest_spec (P := P) (Nat.zero_le B) ⟨0, Nat.zero_le _⟩
  obtain ⟨n0, hn0⟩ := hs
  refine ⟨n0, s, fun n hn => ?_⟩
  have h1 : s ≤ H n := le_trans hn0 (H_mono hn)
  have h2 : H n ≤ s := Nat.le_findGreatest (P := P) (hB n) ⟨n, le_refl _⟩
  omega

/-- A polytime decider for `LH gL` yields a correct program. -/
theorem correct_of_inP (h : InP (LH gL)) : ∃ s, Correct s := by
  obtain ⟨f, ⟨hf⟩, hfL⟩ := h
  obtain ⟨D, Pc, hD⟩ := reproducesG f hf.toTM2ComputableInTime
  obtain ⟨k0, hk0⟩ := BGS.poly_le_clk hf.time
  let k := D * k0 + k0 + Pc.length + 1
  let x : List Bool := List.replicate k true ++ false :: encNums Pc
  obtain ⟨s, hs⟩ := prog_surj x
  refine ⟨s, fun y => ?_⟩
  rw [hs]
  have hx : numsOf (lpX x) = Pc := by simp only [x, lpX_rep, numsOf_encNums]
  have hk : lpN x = k := by simp only [x, lpN_rep]
  have hfy : f y = decide (LH gL y) := by
    rcases Bool.eq_false_or_eq_true (f y) with e | e
    · rw [e]; exact (decide_eq_true ((hfL y).2 e)).symm
    · rw [e]; exact (decide_eq_false (fun h => by rw [(hfL y).1 h] at e; simp at e)).symm
  rw [← hfy]
  apply hD x hx y
  · have ht : hf.toTM2ComputableInTime.time y.length ≤ BGS.clk k0 y.length := hk0 _
    unfold BGS.clk at ht
    unfold lclk; rw [hk]
    have hP : (y.length + 1) ^ k0 ≤ (y.length + 1) ^ k :=
      Nat.pow_le_pow_right (by omega) (by simp only [k]; nlinarith)
    have hP1 : 1 ≤ (y.length + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    generalize (y.length + 1) ^ k = P at hP hP1
    generalize (y.length + 1) ^ k0 = P0 at hP ht
    generalize hf.toTM2ComputableInTime.time y.length = tm at ht
    simp only [k]
    have : D * tm ≤ D * (k0 * P) := Nat.mul_le_mul_left _ (le_trans ht (Nat.mul_le_mul_left _ hP))
    nlinarith
  · unfold lclk; rw [hk]
    have hP1 : 1 ≤ (y.length + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    generalize (y.length + 1) ^ k = P at hP1
    have : Pc.length ≤ k * P := le_trans (by simp only [k]; omega) (Nat.le_mul_of_pos_right _ hP1)
    omega

/-- A correct program puts `LH gL` in P. -/
theorem inP_of_correct {s : ℕ} (hs : Correct s) : InP (LH gL) := by
  let x := prog s
  let k := lpN x
  have hT : PU (fun y => lclk x y.length) :=
    (PU.poly (Polynomial.C k * (Polynomial.X + 1) ^ k)).congr (fun y => by simp [lclk, k])
  have hu := PU.u2tag (PS.const x) PS.id hT
  obtain ⟨hD⟩ := PS.iteEq hu (PU.const 5) (PS.const [true]) (PS.const [false])
  have hD' : TM2ComputableInPolyTime strEnc strEnc
      (fun y => [decide (uTag x y (lclk x y.length) = 5)]) := by
    have e : (fun y => if tagOf (stepL^[lclk x y.length] (initL (srcL x y (lclk x y.length)))) = 5
        then [true] else [false]) = (fun y => [decide (uTag x y (lclk x y.length) = 5)]) := by
      funext y; unfold uTag; split_ifs with h <;> simp [h]
    exact e ▸ hD
  refine ⟨_, ⟨strToDecider hD'⟩, fun y => ?_⟩
  have := hs y
  rw [U2_uTag] at this
  simp only [decide_eq_true_eq]
  constructor
  · intro hy
    by_contra h5
    rw [if_neg h5] at this
    split_ifs at this with h0 <;> simp [hy] at this
  · intro h5
    rw [if_pos h5] at this
    simpa using this.symm

/-- (M5) Under `¬ P_eq_NP`, `H` is unbounded (needs the polytime machine for `H`). -/
theorem H_unbounded (hH : PU (fun x => H x.length)) (hPNP : ¬ P_eq_NP) : ∀ B, ∃ n, B < H n := by
  intro B
  by_contra hc
  push_neg at hc
  obtain ⟨N, s, hN⟩ := stable_of_bounded hc
  have hP := inP_of_correct (correct_of_stable hN)
  have hg : PU (fun x => gL x.length) :=
    (PU.cpow PU.lenX hH (PU.poly (Polynomial.X ^ B + 1))).congr (fun x => by
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, gL]
      apply min_eq_left
      rcases Nat.eq_zero_or_pos x.length with h0 | h0
      · rw [h0, show H 0 = 0 from Nat.le_zero.1 (H_le 0)]; simp
      · exact le_trans (Nat.pow_le_pow_right h0 (hc _)) (Nat.le_succ _))
  exact hPNP (P_eq_NP_iff_SAT_in_P.2 (InP.of_reduces (SAT_le_LH gL hg) hP))

theorem clk_lt_pow {k n : ℕ} (hn : k + 2 ≤ n) : k * (n + 1) ^ k < n ^ (2 * k + 1) := by
  have h1 : (n + 1) ^ k ≤ (n * n) ^ k := Nat.pow_le_pow_left (by nlinarith) _
  have h2 : (n * n) ^ k = n ^ (2 * k) := by rw [← pow_two, ← pow_mul, mul_comm]
  have h3 : 0 < n ^ (2 * k) := Nat.pow_pos (by omega)
  calc k * (n + 1) ^ k ≤ k * n ^ (2 * k) := Nat.mul_le_mul_left _ (h2 ▸ h1)
    _ < n * n ^ (2 * k) := Nat.mul_lt_mul_of_pos_right (by omega) h3
    _ = n ^ (2 * k + 1) := by rw [pow_succ']

/-- (M7) An unbounded `H` makes `gL` superpolynomial. -/
theorem superPoly_of_unbounded (hu : ∀ B, ∃ n, B < H n) : SuperPoly gL := by
  intro P
  obtain ⟨k, hk⟩ := BGS.poly_le_clk P
  obtain ⟨n1, hn1⟩ := hu (2 * k)
  refine ⟨max n1 (k + 2), fun n hn => ?_⟩
  have hHn : 2 * k + 1 ≤ H n := le_trans hn1 (H_mono (le_trans (le_max_left _ _) hn))
  have hn2 : k + 2 ≤ n := le_trans (le_max_right _ _) hn
  calc P.eval n ≤ BGS.clk k n := hk n
    _ < n ^ (2 * k + 1) := clk_lt_pow hn2
    _ ≤ n ^ H n := Nat.pow_le_pow_right (by omega) hHn

/-- (G1) Checkability of `gL` from the machine for `H`. -/
theorem checkable_gL (hH : PU (fun x => H x.length)) : Checkable gL :=
  (PU.cpow (PU.lenX.comp PS.drop) (hH.comp PS.drop) (PU.add PU.fst (PU.const 1))).congr
    (fun y => by simp [gL])

/-- **Ladner's theorem, modulo the polytime computability of `n ↦ H n`** (proved in
`LadnerMachine.lean`). -/
theorem ladner_of_H (hH : PU (fun x => H x.length)) (hPNP : ¬ P_eq_NP) :
    InNP (LH gL) ∧ ¬ InP (LH gL) ∧ ¬ NPComplete (LH gL) := by
  have hu := H_unbounded hH hPNP
  refine ladner_of_padding hPNP gL (checkable_gL hH) (fun hP => ?_)
    (fun _ => superPoly_of_unbounded hu)
  exfalso
  obtain ⟨s, hs⟩ := correct_of_inP hP
  obtain ⟨n, hn⟩ := hu s
  exact absurd (H_le_of_correct hs n) (by omega)

end PvnpReal
