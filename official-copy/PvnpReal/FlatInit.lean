/-
  PvnpReal.FlatInit — the initial array `initL (srcL x y t)` lays out the flat start
  configuration (state `Pc[5]`, input `y` on stack `Pc[2]` coded by `Pc[3]`/`Pc[4]`).
-/
import PvnpReal.FlatComp

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability NE

namespace Flat

theorem eq_zero_iff (a b : NE) (i : ℕ) (L : List ℕ) :
    (eq a b).ev i L = 0 ↔ ¬ a.ev i L = b.ev i L := by rw [ev_eq]; exact ite10_eq0
theorem lt_zero_iff (a b : NE) (i : ℕ) (L : List ℕ) :
    (ltE a b).ev i L = 0 ↔ ¬ a.ev i L < b.ev i L := by rw [ev_lt]; exact ite10_eq0
theorem mul_lt_zero_iff (a b c d : NE) (i : ℕ) (L : List ℕ) :
    (mul (ltE a b) (ltE c d)).ev i L = 0 ↔ ¬ (a.ev i L < b.ev i L ∧ c.ev i L < d.ev i L) := by
  rw [ev_mul, ev_lt, ev_lt]; exact ite10_mul_eq0

theorem initE_ev (i : ℕ) (S : List ℕ) : initE.ev i S =
    if i = 0 then iStart.ev i S else if i = 1 then iCap.ev i S else if i = 2 then iNK.ev i S
    else if i = 3 then iW.ev i S else if i = 4 then iN.ev i S
    else if i < 5 + iNK.ev i S then (if i - 5 = iK0.ev i S then sN.ev i S else 0)
    else if i < iPB.ev i S then
      (if i < iBase.ev i S + sN.ev i S ∧ iBase.ev i S < i + 1 then iCell.ev i S else 0)
    else (sPc (sub p iPB)).ev i S := by
  simp only [initE, ev_ite, eq_zero_iff, lt_zero_iff, mul_lt_zero_iff, ite_not]
  rfl

theorem encNums_length_ge (l : List ℕ) : l.length ≤ (encNums l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [encNums] at ih ⊢; omega

/-- The source array, written with the program as an explicit list. -/
def srcP (Pc : List ℕ) (y : List Bool) (t : ℕ) : List ℕ :=
  [t, y.length] ++ (List.range y.length).map (fun j => NthTM.bit y j) ++ Pc

theorem srcL_eq (x y : List Bool) (t : ℕ) : srcL x y t = srcP (numsOf (lpX x)) y t := rfl

/-- The flat start configuration for input `y`. -/
def S0 (Pc : List ℕ) (y : List Bool) (k : ℕ) : List ℕ :=
  if k = Pc.getD 2 0 then y.map (fun b => if b then Pc.getD 4 0 else Pc.getD 3 0) else []

section
variable (Pc : List ℕ) (y : List Bool) (t : ℕ)

theorem srcP_len : (srcP Pc y t).length = 2 + y.length + Pc.length := by
  simp [srcP]; omega

theorem srcP_0 : (srcP Pc y t).getD 0 0 = t := by simp [srcP]
theorem srcP_1 : (srcP Pc y t).getD 1 0 = y.length := by simp [srcP]

theorem srcP_bit {j : ℕ} (hj : j < y.length) : (srcP Pc y t).getD (2 + j) 0 = NthTM.bit y j := by
  unfold srcP
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem srcP_pc (m : ℕ) : (srcP Pc y t).getD (2 + y.length + m) 0 = Pc.getD m 0 := by
  unfold srcP
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  congr 1; simp; omega

end

/-- **Initial layout lemma.** -/
theorem rep_init (Pc : List ℕ) (y : List Bool) (t : ℕ) (hPc : Pc.length ≤ y.length + t)
    (hk0 : Pc.getD 2 0 < Pc.getD 0 0) :
    Rep (y.length + t + 1) (Pc.getD 0 0) Pc (initL (srcP Pc y t)) ⟨Pc.getD 5 0, S0 Pc y⟩ := by
  set Sr := srcP Pc y t
  set N := y.length
  set nK := Pc.getD 0 0
  set Cap := N + t + 1
  have e0 := srcP_0 Pc y t
  have e1 := srcP_1 Pc y t
  have epc := srcP_pc Pc y t
  have vT : ∀ i, sT.ev i Sr = t := fun i => e0
  have vN : ∀ i, sN.ev i Sr = N := fun i => e1
  have vPc : ∀ i m, (sPc m).ev i Sr = Pc.getD (m.ev i Sr) 0 := by
    intro i m; simp only [sPc, ev_get, ev_add, ev_c, vN]; rw [← Nat.add_assoc]; exact epc _
  have vNK : ∀ i, iNK.ev i Sr = nK := fun i => by simp only [iNK, vPc, ev_c]; rfl
  have vCap : ∀ i, iCap.ev i Sr = Cap := fun i => by simp only [iCap, ev_add, ev_c, vT, vN]; omega
  have vPB : ∀ i, iPB.ev i Sr = 5 + nK + nK * Cap := fun i => by
    simp only [iPB, ev_add, ev_mul, ev_c, vNK, vCap]; omega
  have vN' : ∀ i, iN.ev i Sr = 5 + nK + nK * Cap + (N + t) := fun i => by
    simp only [iN, ev_add, vPB, vN, vT]
  have vK0 : ∀ i, iK0.ev i Sr = Pc.getD 2 0 := fun i => by simp only [iK0, vPc, ev_c]
  have vBase : ∀ i, iBase.ev i Sr = 5 + nK + Pc.getD 2 0 * Cap := fun i => by
    simp only [iBase, ev_add, ev_mul, ev_c, vNK, vK0, vCap]; omega
  have hlen : (initL Sr).length = 5 + nK + nK * Cap + (N + t) := by
    simp [initL, vN']
  have gD : ∀ i, (initL Sr).getD i 0 = if i < 5 + nK + nK * Cap + (N + t) then initE.ev i Sr else 0 := by
    intro i
    simp only [initL, List.getD_eq_getElem?_getD, List.getElem?_map, vN']
    split
    · next h => rw [List.getElem?_range h]; rfl
    · next h => rw [List.getElem?_eq_none (by simp; omega)]; rfl
  refine ⟨by rw [hlen]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gD, if_pos (by omega), initE_ev, if_pos rfl]; simp only [iStart, vPc, ev_c]
  · rw [gD, if_pos (by omega), initE_ev, if_neg (by omega), if_pos rfl, vCap]
  · rw [gD, if_pos (by omega), initE_ev, if_neg (by omega), if_neg (by omega), if_pos rfl, vNK]
  · rw [gD, if_pos (by omega), initE_ev, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]; simp only [iW, vPc, ev_c]
  · rw [gD, if_pos (by omega), initE_ev, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl, vN', hlen]
  · intro k hk
    have hkc : k * Cap + 0 < nK * Cap := kcap_lt hk (by omega)
    have hlen5 : (initL Sr).getD (5 + k) 0 = (S0 Pc y k).length := by
      rw [gD, if_pos (by omega), initE_ev, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), vNK, if_pos (by omega), vK0, vN]
      unfold S0
      by_cases e : k = Pc.getD 2 0
      · rw [if_pos (by omega), if_pos e]; simp [N]
      · rw [if_neg (by omega), if_neg e]; rfl
    refine ⟨hlen5, ?_, ?_⟩
    · show (S0 Pc y k).length ≤ Cap
      unfold S0; split <;> simp [N, Cap] <;> omega
    · intro d hd
      change d < (S0 Pc y k).length at hd
      have hk0' : k = Pc.getD 2 0 := by
        by_contra e; rw [show S0 Pc y k = [] from if_neg e] at hd; simp at hd
      have hS : S0 Pc y k = y.map (fun b => if b then Pc.getD 4 0 else Pc.getD 3 0) := if_pos hk0'
      have hdN : d < N := by rw [hS, List.length_map] at hd; exact hd
      show (initL Sr).getD _ 0 = (S0 Pc y k).getD ((S0 Pc y k).length - 1 - d) 0
      have hpos : 5 + nK + k * Cap + d < 5 + nK + nK * Cap := by
        have := kcap_lt hk (show d < Cap by omega); omega
      rw [gD, if_pos (by omega), initE_ev, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), vNK, if_neg (by omega), vPB, if_pos hpos, vBase, vN,
        if_pos (by rw [← hk0']; omega)]
      simp only [iCell, ev_ite, sBit, ev_get, ev_add, ev_sub, ev_c, ev_p, vN, vBase, iIn0, iIn1, vPc]
      have hidx : N - 1 - (5 + nK + k * Cap + d - (5 + nK + Pc.getD 2 0 * Cap)) = N - 1 - d := by
        rw [← hk0']; omega
      rw [hidx, srcP_bit Pc y t (by omega), hS, List.length_map]
      have hd' : N - 1 - d < y.length := by omega
      unfold NthTM.bit
      simp only [N] at hd' ⊢
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hd',
        Option.map_some, Option.getD_some]
      cases y[y.length - 1 - d] <;> simp
  · intro m
    rw [gD]
    split
    · next hm =>
      rw [initE_ev, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), vNK, if_neg (by omega), vPB, if_neg (by omega), vPc]
      simp only [ev_sub, ev_p, vPB]
      congr 1; omega
    · next hm =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

end Flat

end PvnpReal
