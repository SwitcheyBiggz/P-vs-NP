/-
  PvnpReal.LadnerTools — polytime building blocks for Ladner's diagonal function:
  `PU.min`, `PS.boolOf`, `PS.dropLast`, `binL_surj`, capped powers `PU.cpow`, and the
  general clocked interpreter tag `PU.u2tag` (program, input and clock all computed).
-/
import PvnpReal.Ladner
import PvnpReal.TimeHierarchy

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Flat

theorem PU.minU {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) : PU (fun x => min (u x) (v x)) :=
  (PU.sub hu (PU.sub hu hv)).congr (fun x => by omega)

/-- A `0/1` unary value as a one-bit string. -/
theorem PS.boolOf {u : List Bool → ℕ} (hu : PU u) : PS (fun x => [decide (u x = 1)]) :=
  (PS.iteEq hu (PU.const 1) (PS.const [true]) (PS.const [false])).congr (fun x => by
    by_cases h : u x = 1 <;> simp [h])

theorem flatMap_singleton_range (n : ℕ) (f : ℕ → Bool) :
    (List.range n).flatMap (fun j => [f j]) = (List.range n).map f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.map_append]; simp

theorem dropLast_eq_flatMap (x : List Bool) :
    x.dropLast = (List.range (x.length - 1)).flatMap
      (fun j => [decide (NthTM.bit x j = 1)]) := by
  rw [flatMap_singleton_range]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.length_dropLast] at h1
    rw [List.getElem_dropLast, List.getElem_map, List.getElem_range]
    simp only [NthTM.bit, List.getElem?_eq_getElem (show n < x.length by omega)]
    cases x[n] <;> simp

theorem PS.dropLast : PS (fun x => x.dropLast) := by
  have hb : PS (fun z => [decide (NthTM.bit (lpX z) (lpN z) = 1)]) := PS.boolOf PU.nth
  exact (PS.flatRange (PU.sub PU.lenX (PU.const 1)) (fun j x => [decide (NthTM.bit x j = 1)]) hb).congr
    (fun x => (dropLast_eq_flatMap x).symm)

/-- Every string followed by `true` is a binary numeral (LSB first). -/
theorem binL_surj (l : List Bool) : ∃ s, binL s = l ++ [true] := by
  induction l with
  | nil => exact ⟨1, by rw [binL]; simp [binL_zero]⟩
  | cons b l ih =>
    obtain ⟨s, hs⟩ := ih
    have hs0 : s ≠ 0 := by rintro rfl; rw [binL_zero] at hs; simp at hs
    cases b
    · refine ⟨2 * s, ?_⟩
      rw [show 2 * s = (2 * s - 1) + 1 by omega, binL]
      have h1 : ((2 * s - 1 + 1) % 2 == 1) = false := by
        rw [show 2 * s - 1 + 1 = 2 * s by omega]; simp
      have h2 : (2 * s - 1 + 1) / 2 = s := by omega
      rw [h1, h2, hs]; rfl
    · refine ⟨2 * s + 1, ?_⟩
      rw [binL]
      have h1 : ((2 * s + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      have h2 : (2 * s + 1) / 2 = s := by omega
      rw [h1, h2, hs]; rfl

/-! ### Capped powers -/

def cstep (z : List Bool) : List Bool :=
  List.replicate (min (lpN z * lpN (lpX z)) (lpN (lpX (lpX z)))) true ++ false :: lpX z

theorem lpX_cstep (z : List Bool) : lpX (cstep z) = lpX z := by simp [cstep, lpX_rep]

theorem lpX_cstep_iter (z : List Bool) (i : ℕ) : lpX (cstep^[i] z) = lpX z := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', lpX_cstep, ih]

theorem lpX_len_le (z : List Bool) : (lpX z).length ≤ z.length := by
  simp only [lpX, List.length_drop]; omega

theorem cstep_iter_len (z : List Bool) (i : ℕ) : (cstep^[i] z).length ≤ 2 * z.length + 1 := by
  rcases i with _ | i
  · simp; omega
  · rw [Function.iterate_succ_apply']
    have e := lpX_cstep_iter z i
    simp only [cstep, List.length_append, List.length_replicate, List.length_cons, e]
    have h1 := lpN_le (lpX (lpX z))
    have h2 := lpX_len_le (lpX z)
    have h3 := lpX_len_le z
    have := min_le_right (lpN (cstep^[i] z) * lpN (lpX z)) (lpN (lpX (lpX z)))
    omega

theorem cstep_iter_val (v : ℕ) (r : List Bool) (i : ℕ) :
    lpN (cstep^[i] (List.replicate v true ++ false :: r)) =
      Nat.rec v (fun _ f => min (f * lpN r) (lpN (lpX r))) i := by
  induction i with
  | zero => simp [lpN_rep]
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    simp only [cstep, lpN_rep, lpX_cstep_iter, lpX_rep, ih]

theorem cpow_rec (a C : ℕ) (i : ℕ) :
    (Nat.rec (min 1 C) (fun _ f => min (f * a) C) i : ℕ) = min (a ^ i) C := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [ih]
    by_cases h : a ^ i ≤ C
    · rw [min_eq_left h, pow_succ]
    · push_neg at h
      rw [min_eq_right h.le]
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        rcases i with _ | i
        · simp at h; omega
        · simp at h
      · have : C ≤ C * a := Nat.le_mul_of_pos_right _ ha
        have h2 : a ^ i ≤ a ^ (i + 1) := Nat.pow_le_pow_right ha (by omega)
        rw [min_eq_right this, min_eq_right (by omega)]

/-- **Capped powers are polytime**: `min (a^b) C` for polytime unary `a, b, C`. -/
theorem PU.cpow {a b C : List Bool → ℕ} (ha : PU a) (hb : PU b) (hC : PU C) :
    PU (fun x => min (a x ^ b x) (C x)) := by
  have hI := PS.iter (PS.append ((PU.minU (PU.mul PU.fst (PU.fst.comp PS.drop)) (PU.fst.comp PS.drop2)))
    (PS.cons false PS.drop)) (2 * Polynomial.X + 1) (fun y i => by
      have := cstep_iter_len y i
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat]
      have e : (fun z => List.replicate (min (lpN z * lpN (lpX z)) (lpN (lpX (lpX z)))) true ++
          false :: lpX z) = cstep := rfl
      rw [e]; omega)
  have hin : PS (fun x => List.replicate (b x) true ++ false :: (List.replicate (min 1 (C x)) true ++
      false :: (List.replicate (a x) true ++ false :: (List.replicate (C x) true ++ [false])))) :=
    PS.append hb (PS.cons false (PS.append (PU.minU (PU.const 1) hC) (PS.cons false
      (PS.append ha (PS.cons false (PS.append hC (PS.const [false])))))))
  refine (PU.fst.comp (PS.comp hin hI)).congr (fun x => ?_)
  have e : (fun z => List.replicate (min (lpN z * lpN (lpX z)) (lpN (lpX (lpX z)))) true ++
      false :: lpX z) = cstep := rfl
  simp only [e, lpN_rep, lpX_rep, cstep_iter_val]
  exact cpow_rec _ _ _

/-! ### The clocked interpreter with computed program, input and clock -/

def srcBits2 (x y : List Bool) (t : ℕ) : List Bool :=
  List.replicate t true ++ false :: (List.replicate y.length true ++ false :: (bitsEnc y ++ lpX x))

theorem numsOf_srcBits2 (x y : List Bool) (t : ℕ) : numsOf (srcBits2 x y t) = srcL x y t := by
  have : srcBits2 x y t = encNums ([t, y.length] ++
      (List.range y.length).map (fun j => NthTM.bit y j)) ++ lpX x := by
    simp [srcBits2, bitsEnc, encNums, List.flatMap_map]
  rw [this, numsOf_encNums_append]; rfl

/-- **The tag of `U2 (X w) (Y w) (T w)` is polytime** in `w`. -/
theorem PU.u2tag {X Y : List Bool → List Bool} {T : List Bool → ℕ} (hX : PS X) (hY : PS Y)
    (hT : PU T) : PU (fun w => tagOf (stepL^[T w] (initL (srcL (X w) (Y w) (T w))))) := by
  have hsrc : PS (fun w => srcBits2 (X w) (Y w) (T w)) :=
    PS.append hT (PS.cons false (PS.append (PU.lenX.comp hY) (PS.cons false
      (PS.append (PS.bitsEnc hY) (PS.comp hX PS.drop)))))
  have hI : PS (fun w => encNums (initL (srcL (X w) (Y w) (T w)))) :=
    (PS.comp hsrc (PS.mapNums iN initE)).congr (fun w => by
      simp only [numsOf_srcBits2]; rfl)
  have hZ : PS (fun w => List.replicate (T w) true ++ false :: encNums (initL (srcL (X w) (Y w) (T w)))) :=
    PS.append hT (PS.cons false hI)
  have hIt : PS (fun w => stepB^[T w] (encNums (initL (srcL (X w) (Y w) (T w))))) :=
    (PS.comp hZ PS.stepIter).congr (fun w => by simp only [lpN_rep, lpX_rep])
  exact (PU.comp (NE.pu0 tagE) hIt).congr (fun w => by
    simp only [numsOf_stepB_iter, tagOf])

theorem U2_eq (x y : List Bool) (t : ℕ) :
    U2 x y t = (let tg := tagOf (stepL^[t] (initL (srcL x y t)))
      if tg = 5 then some true else if tg = 0 then some false else none) := rfl

end PvnpReal
