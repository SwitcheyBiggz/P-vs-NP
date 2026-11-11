/-
  PvnpReal.SatSpace — **SAT ∈ PSPACE** and **NP ⊆ PSPACE** via a space-reusing brute-force loop:
  the state holds the formula and a *binary* counter `binL i`; one round checks
  `verify x (binL i)` and increments the counter (`incL`), stopping at the first satisfying
  assignment or when the counter exceeds `|x|` bits. Space is polynomial by `whileDecider`.
-/
import PvnpReal.WhileSpace
import PvnpReal.LadnerH
import PvnpReal.BruteEXP
import PvnpReal.PvsNP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### Bit-list helpers -/

theorem flat_bits_map (x : List Bool) :
    (List.range x.length).map (fun j => decide (NthTM.bit x j = 1)) = x := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range]
    simp only [NthTM.bit, List.getElem?_eq_getElem h2]
    cases x[n] <;> simp

theorem tail_eq_flatMap (s : List Bool) :
    (List.range (s.length - 1)).flatMap (fun j => [decide (NthTM.bit s (j + 1) = 1)]) = s.tail := by
  rw [flatMap_singleton_range]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_tail]
    simp only [List.length_tail] at h2
    simp only [NthTM.bit, List.getElem?_eq_getElem (show n + 1 < s.length by omega)]
    cases s[n + 1] <;> simp

theorem PS.tail : PS (fun s => s.tail) := by
  have hb : PU (fun w => NthTM.bit (lpX w) (lpN w + 1)) :=
    (PU.nth.comp (PS.cons true PS.id)).congr (fun w => by
      simp only [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true])
  exact (PS.flatRange (PU.sub PU.lenX (PU.const 1))
    (fun j s => [decide (NthTM.bit s (j + 1) = 1)]) (PS.boolOf hb)).congr tail_eq_flatMap

theorem PU.bit0 : PU (fun s => NthTM.bit s 0) :=
  (PU.nth.comp (PS.cons false PS.id)).congr (fun s => by
    simp only [LoopTM.lpN_cons_false, LoopTM.lpX_cons_false])

theorem PU.bit1 : PU (fun s => NthTM.bit s 1) :=
  (PU.nth.comp (PS.cons true (PS.cons false PS.id))).congr (fun s => by
    simp only [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, LoopTM.lpN_cons_false,
      LoopTM.lpX_cons_false])

/-! ### Binary increment -/

def incL (l : List Bool) : List Bool := List.replicate (lpN l) false ++ true :: lpX l

theorem PS.incL : PS incL :=
  PS.append ((PS.flatRange PU.fst (fun _ _ => [false]) (PS.const [false])).congr (fun z => by
    rw [flatMap_singleton_range (lpN z) (fun _ => false)]; simp)) (PS.cons true PS.drop)

theorem incL_true (r : List Bool) : incL (true :: r) = false :: incL r := by
  simp [incL, LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, List.replicate_succ]

theorem incL_false (r : List Bool) : incL (false :: r) = true :: r := by
  simp [incL, LoopTM.lpN_cons_false, LoopTM.lpX_cons_false]

theorem binL_odd (m : ℕ) : binL (2 * m + 1) = true :: binL m := by
  rw [binL]
  have h1 : ((2 * m + 1) % 2 == 1) = true := by simp [Nat.add_mod]
  rw [h1, show (2 * m + 1) / 2 = m by omega]

theorem binL_even (m : ℕ) : binL (2 * m + 2) = false :: binL (m + 1) := by
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, binL]
  have h1 : ((2 * m + 1 + 1) % 2 == 1) = false := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]; simp
  rw [h1, show (2 * m + 1 + 1) / 2 = m + 1 by omega]

theorem binL_succ (i : ℕ) : binL (i + 1) = incL (binL i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.even_or_odd' i with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [binL, binL_zero, incL, lpN, lpX]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [show 2 * (m' + 1) = 2 * m' + 2 by ring, binL_even, incL_false,
          show 2 * m' + 2 + 1 = 2 * (m' + 1) + 1 by ring, binL_odd]
    · rw [binL_odd, incL_true, show 2 * m + 1 + 1 = 2 * m + 2 by ring, binL_even, ih m (by omega)]

theorem binL_lt (j : ℕ) : j < 2 ^ (binL j).length := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [binL_zero]
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      rw [binL, List.length_cons, pow_succ]
      have := ih ((n + 1) / 2) (by omega)
      omega

/-- `|binL (i+1)| > m ↔ 2^m ≤ i + 1`. -/
theorem binL_len_gt_iff (i m : ℕ) : m < (binL (i + 1)).length ↔ 2 ^ m ≤ i + 1 := by
  constructor
  · intro h
    have h1 := binL_len_pow (i + 1) (by omega)
    have h2 : 2 ^ (m + 1) ≤ 2 ^ (binL (i + 1)).length := Nat.pow_le_pow_right (by norm_num) h
    rw [pow_succ] at h2; omega
  · intro h
    by_contra h'
    have h1 := binL_lt (i + 1)
    have h2 : 2 ^ (binL (i + 1)).length ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem binL_len_le (i m : ℕ) (h : i < 2 ^ m) : (binL i).length ≤ m := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [binL_zero]
  · have h1 := binL_len_pow i hi
    by_contra h'
    have h2 : 2 ^ (m + 1) ≤ 2 ^ (binL i).length := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at h2; omega

/-! ### The loop state -/

/-- Running state payload: `1^{|x|} 0 1^{|c|} 0 bits(x) bits(c)`. -/
def Rof (x c : List Bool) : List Bool :=
  List.replicate x.length true ++ false :: (List.replicate c.length true ++ false ::
    (bitsEnc x ++ bitsEnc c))

theorem PS.Rof {X C : List Bool → List Bool} (hX : PS X) (hC : PS C) :
    PS (fun s => Rof (X s) (C s)) :=
  PS.append (PU.lenX.comp hX) (PS.cons false (PS.append (PU.lenX.comp hC) (PS.cons false
    (PS.append (PS.bitsEnc hX) (PS.bitsEnc hC)))))

def decX (R : List Bool) : List Bool :=
  (List.range (lpN R)).flatMap (fun j => [decide ((numsOf R).getD (2 + j) 0 = 1)])

def decC (R : List Bool) : List Bool :=
  (List.range (lpN (lpX R))).flatMap (fun j => [decide ((numsOf R).getD (2 + lpN R + j) 0 = 1)])

theorem PS.decX : PS decX :=
  PS.flatRange PU.fst (fun j R => [decide ((numsOf R).getD (2 + j) 0 = 1)])
    (PS.boolOf (PU.getNum (PU.add (PU.const 2) PU.fst) PS.drop))

theorem PS.decC : PS decC :=
  PS.flatRange PU.fst2 (fun j R => [decide ((numsOf R).getD (2 + lpN R + j) 0 = 1)])
    (PS.boolOf (PU.getNum (PU.add (PU.add (PU.const 2) PU.fst2) PU.fst) PS.drop))

theorem bitsEnc_eq (w : List Bool) :
    bitsEnc w = encNums ((List.range w.length).map (fun j => NthTM.bit w j)) := by
  simp [bitsEnc, encNums, List.flatMap_map]

theorem numsOf_Rof (x c : List Bool) : numsOf (Rof x c) = [x.length, c.length] ++
    (List.range x.length).map (fun j => NthTM.bit x j) ++
    (List.range c.length).map (fun j => NthTM.bit c j) := by
  have : Rof x c = encNums ([x.length, c.length] ++
      (List.range x.length).map (fun j => NthTM.bit x j) ++
      (List.range c.length).map (fun j => NthTM.bit c j)) := by
    simp [Rof, bitsEnc_eq, encNums, List.flatMap_append]
  rw [this, numsOf_encNums]

theorem decX_Rof (x c : List Bool) : decX (Rof x c) = x := by
  unfold decX
  rw [show lpN (Rof x c) = x.length by simp [Rof, lpN_rep], flatMap_singleton_range]
  conv_rhs => rw [← flat_bits_map x]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [numsOf_Rof]
  congr 2
  rw [List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [show 2 + j - (0 + 1 + 1) = j by omega, List.getElem?_append_left (by simp; omega)]
  simp [hj]

theorem decC_Rof (x c : List Bool) : decC (Rof x c) = c := by
  unfold decC
  rw [show lpN (Rof x c) = x.length by simp [Rof, lpN_rep],
    show lpN (lpX (Rof x c)) = c.length by simp [Rof, lpN_rep, lpX_rep], flatMap_singleton_range]
  conv_rhs => rw [← flat_bits_map c]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [numsOf_Rof]
  congr 2
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [show 2 + x.length + j - (0 + 1 + 1 + x.length) = j by omega]
  simp [hj]

theorem bitsEnc_len (w : List Bool) : (bitsEnc w).length ≤ 2 * w.length := by
  rw [bitsEnc_eq, encNums]
  simp only [List.length_flatMap, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, List.map_map]
  have : ∀ j, NthTM.bit w j ≤ 1 := fun j => by unfold NthTM.bit; split <;> omega
  calc ((List.map ((fun a => a + (0 + 1)) ∘ fun j => NthTM.bit w j) (List.range w.length))).sum
      ≤ ((List.range w.length).map (fun _ => 2)).sum := by
        apply List.sum_le_sum; intro j _; simp only [Function.comp]; have := this j; omega
    _ = 2 * w.length := by simp [List.sum_replicate, mul_comm]

theorem Rof_len (x c : List Bool) : (Rof x c).length ≤ 3 * x.length + 3 * c.length + 2 := by
  have h1 := bitsEnc_len x
  have h2 := bitsEnc_len c
  simp only [Rof, List.length_append, List.length_replicate, List.length_cons]
  omega

/-! ### One round of the brute-force loop -/

/-- The loop body, parameterised by a reduction `r` applied once at the start. -/
def gS (r : List Bool → List Bool) (s : List Bool) : List Bool :=
  if NthTM.bit s 0 = 1 then
    (if NthTM.bit s 1 = 1 then
      (if lpN [verify (decX s.tail.tail) (decC s.tail.tail)] = 1 then [false, true]
       else if (incL (decC s.tail.tail)).length - (decX s.tail.tail).length = 0 then
         true :: true :: Rof (decX s.tail.tail) (incL (decC s.tail.tail))
       else [false, false])
     else true :: true :: Rof (r s.tail.tail) [])
  else [false, false]

theorem PS.gS {r : List Bool → List Bool} (hr : PS r) : PS (gS r) := by
  have hT2 : PS (fun s => s.tail.tail) := PS.comp PS.tail PS.tail
  have hX := PS.comp hT2 PS.decX
  have hC := PS.comp hT2 PS.decC
  have hv : PS (fun y => [verify (decP y).1 (decP y).2]) :=
    ⟨deciderToStr (composeGen decComputable satVerifierComputable)⟩
  have hV : PS (fun s => [verify (PvnpReal.decX s.tail.tail) (PvnpReal.decC s.tail.tail)]) :=
    (PS.comp (PS.append (PS.codeL hX) (PS.cons false (PS.codeL hC))) hv).congr (fun s => by
      show [verify (decP (codeP _ _)).1 (decP (codeP _ _)).2] = _
      rw [decP_codeP])
  have hInc := PS.comp hC PS.incL
  have i3 := PS.iteEq (PU.sub (PU.lenX.comp hInc) (PU.lenX.comp hX)) (PU.const 0)
    (PS.cons true (PS.cons true (PS.Rof hX hInc))) (PS.const [false, false])
  have i2 := PS.iteEq (PU.comp PU.fst hV) (PU.const 1) (PS.const [false, true]) i3
  have i1 := PS.iteEq PU.bit1 (PU.const 1) i2
    (PS.cons true (PS.cons true (PS.Rof (PS.comp hT2 hr) (PS.const []))))
  exact (PS.iteEq PU.bit0 (PU.const 1) i1 (PS.const [false, false])).congr (fun s => rfl)

/-- Running state. -/
def stS (X c : List Bool) : List Bool := true :: true :: Rof X c

theorem gS_start (r : List Bool → List Bool) (x : List Bool) :
    gS r (true :: false :: x) = stS (r x) [] := by
  simp [gS, NthTM.bit, stS]

theorem gS_st (r : List Bool → List Bool) (X c : List Bool) :
    gS r (stS X c) = if lpN [verify X c] = 1 then [false, true]
      else if (incL c).length - X.length = 0 then stS X (incL c) else [false, false] := by
  simp only [gS, stS, NthTM.bit, List.tail_cons, decX_Rof, decC_Rof]
  simp

/-! ### The loop analysis -/

theorem InPSPACE.congr {L L' : Language} (h : InPSPACE L) (e : ∀ x, L x ↔ L' x) : InPSPACE L' := by
  obtain ⟨p, f, hf, hb, hL⟩ := h
  exact ⟨p, f, hf, hb, fun x => (e x).symm.trans (hL x)⟩

/-- **`x ↦ SAT(r x)` is in PSPACE** for every polytime `r` (brute force with a binary counter). -/
theorem SAT_comp_in_PSPACE {r : List Bool → List Bool} (hr : PS r) :
    InPSPACE (fun x => SATLang (r x)) := by
  classical
  let hg : TM2ComputableInPolyTime strEnc strEnc (gS r) := Classical.choice (PS.gS hr)
  let hR : TM2ComputableInPolyTime strEnc strEnc r := Classical.choice hr
  let Cr := pushTotal hR.tm
  let Pr := hR.time
  let mB : ℕ → ℕ := fun n => n + Cr * Pr.eval n
  have hm : ∀ x, (r x).length ≤ mB x.length := fun x => by
    exact outLen_boundT hR.toTM2ComputableInTime x
  let Lb : ℕ → ℕ := fun n => 6 * mB n + n + 4
  let J : ℕ → ℕ := fun n => 2 ^ mB n + 2
  let f : List Bool → Bool := fun x => decide (SATLang (r x))
  have hF : ∀ x, ∃ j ≤ J x.length, (∀ i < j, ((gS r)^[i] (true :: false :: x)).head? = some true) ∧
      ((gS r)^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, ((gS r)^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      ((gS r)^[j] (true :: false :: x)).tail = [f x] := by
    intro x
    set X := r x
    have hmx : X.length ≤ mB x.length := hm x
    let Q : ℕ → Prop := fun i => verify X (binL i) = true ∨ X.length < (binL (i + 1)).length
    have hQ : ∃ i, Q i := ⟨2 ^ X.length - 1, Or.inr ((binL_len_gt_iff _ _).2 (by
      have := Nat.one_le_two_pow (n := X.length); omega))⟩
    set is := Nat.find hQ with his
    have his_le : is ≤ 2 ^ X.length - 1 := Nat.find_min' hQ (Or.inr ((binL_len_gt_iff _ _).2 (by
      have := Nat.one_le_two_pow (n := X.length); omega)))
    have hpos : 1 ≤ 2 ^ X.length := Nat.one_le_two_pow
    have hnot : ∀ i < is, verify X (binL i) = false ∧ (binL (i + 1)).length ≤ X.length := by
      intro i hi
      have := Nat.find_min hQ hi
      simp only [Q, not_or, not_lt, Bool.not_eq_true] at this
      exact this
    have hQis : Q is := Nat.find_spec hQ
    -- iterates
    have hA : ∀ i ≤ is, (gS r)^[i + 1] (true :: false :: x) = stS X (binL i) := by
      intro i
      induction i with
      | zero => intro _; simp [gS_start, binL_zero, X]
      | succ i ih =>
        intro hi
        rw [Function.iterate_succ_apply', ih (by omega), gS_st]
        obtain ⟨h1, h2⟩ := hnot i (by omega)
        rw [lpN_single, h1, ← binL_succ]
        simp only [Bool.false_eq_true, ite_false, if_neg (by decide : ¬ (0 = 1))]
        rw [if_pos (by omega)]
    have hfin : (gS r)^[is + 2] (true :: false :: x) =
        if verify X (binL is) then [false, true] else [false, false] := by
      rw [Function.iterate_succ_apply', hA is le_rfl, gS_st, lpN_single, ← binL_succ]
      rcases hv : verify X (binL is)
      · have : X.length < (binL (is + 1)).length := hQis.resolve_left (by simp [hv])
        simp only [Bool.false_eq_true, ite_false, if_neg (by decide : ¬ (0 = 1))]
        rw [if_neg (by omega)]
      · simp
    have hans : verify X (binL is) = f x := by
      simp only [f]
      rcases hv : verify X (binL is)
      · symm; rw [decide_eq_false_iff_not]
        intro hs
        obtain ⟨i, hi, hvi⟩ := (SATLang_iff_exists_bin X).1 hs
        have hQi : Q i := Or.inl hvi
        have h1 : is ≤ i := Nat.find_min' hQ hQi
        have h2 : X.length < (binL (is + 1)).length := hQis.resolve_left (by simp [hv])
        have h3 := (binL_len_gt_iff _ _).1 h2
        have : i = is := by omega
        rw [this, hv] at hvi; cases hvi
      · symm; rw [decide_eq_true_iff]
        exact (SATLang_iff_exists_bin X).2 ⟨is, by omega, hv⟩
    refine ⟨is + 2, ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
    · show is + 2 ≤ 2 ^ mB x.length + 2
      have : 2 ^ X.length ≤ 2 ^ mB x.length := Nat.pow_le_pow_right (by norm_num) hmx
      omega
    · rcases i with _ | i
      · rfl
      · rw [hA i (by omega)]; rfl
    · rw [hfin]; split <;> simp
    · rcases Nat.lt_or_ge i (is + 2) with h | h
      · rcases i with _ | i
        · simp [Lb]; omega
        · rw [hA i (by omega)]
          have hb := binL_len_le i X.length (by omega)
          have := Rof_len X (binL i)
          simp only [stS, List.length_cons, Lb]
          omega
      · rw [show i = is + 2 by omega, hfin]
        split <;> simp [Lb]
    · rw [hfin, ← hans]; split <;> simp_all
  obtain ⟨h, hsp⟩ := whileDecider hg f J Lb hF
  let C := pushTotal h.tm
  let Lp : Polynomial ℕ := 6 * (Polynomial.X + Polynomial.C Cr * Pr) + Polynomial.X + 4
  let p : Polynomial ℕ := Polynomial.X + Lp + Polynomial.C C *
    (2 * Polynomial.X + 2 * Lp + hg.time.comp Lp + 6)
  refine ⟨p, f, h, fun x i c hi hc k => (hsp x i c hi hc k).trans (le_of_eq ?_), fun x => ?_⟩
  · simp [p, Lp, Lb, mB, C, Polynomial.eval_comp]
  · simp [f]

/-- **SAT ∈ PSPACE.** -/
theorem SAT_in_PSPACE : InPSPACE SATLang :=
  SAT_comp_in_PSPACE (r := fun x => x) PS.id

/-- **NP ⊆ PSPACE** (via the Cook–Levin reduction to SAT and the space-reusing brute force). -/
theorem NP_subset_PSPACE (L : Language) (hL : InNP L) : InPSPACE L := by
  obtain ⟨r, ⟨hr⟩, hrL⟩ := SAT_NPComplete.2 L hL
  exact (SAT_comp_in_PSPACE (r := r) ⟨hr⟩).congr (fun x => (hrL x).symm)

/-- `P = PSPACE`. -/
def P_eq_PSPACE : Prop := ∀ L : Language, InP L ↔ InPSPACE L

/-- **`P = PSPACE → P = NP`.** -/
theorem P_eq_NP_of_P_eq_PSPACE (h : P_eq_PSPACE) : P_eq_NP :=
  fun L => ⟨P_subset_NP L, fun hL => (h L).2 (NP_subset_PSPACE L hL)⟩

/-- Contrapositive: **`P ≠ NP → P ≠ PSPACE`.** -/
theorem P_ne_PSPACE_of_P_ne_NP (h : ¬ P_eq_NP) : ¬ P_eq_PSPACE :=
  fun h' => h (P_eq_NP_of_P_eq_PSPACE h')

/-- **SAT ∈ P ↔ (P = NP)**, and `SAT ∈ PSPACE`: so `P = PSPACE` would put SAT in P. -/
theorem SAT_in_P_of_P_eq_PSPACE (h : P_eq_PSPACE) : InP SATLang := (h _).2 SAT_in_PSPACE

/-- **P ≠ PSPACE or PSPACE ≠ EXP** (unconditional, from `P ≠ EXP` and `P ⊆ PSPACE ⊆ EXP`). -/
theorem P_ne_PSPACE_or_PSPACE_ne_EXP :
    (∃ L, InPSPACE L ∧ ¬ InP L) ∨ (∃ L, InEXP L ∧ ¬ InPSPACE L) := by
  obtain ⟨L, hE, hP⟩ := p_ne_exp
  by_cases hS : InPSPACE L
  · exact Or.inl ⟨L, hS, hP⟩
  · exact Or.inr ⟨L, hE, hS⟩

/-- **NP ⊆ PSPACE ⊆ EXP**, packaged. -/
theorem NP_subset_PSPACE_subset_EXP (L : Language) (hL : InNP L) : InPSPACE L ∧ InEXP L :=
  ⟨NP_subset_PSPACE L hL, PSPACE_subset_EXP L (NP_subset_PSPACE L hL)⟩

end PvnpReal
