/-
  PvnpReal.PHSpace — **PH ⊆ PSPACE**.

  A generalized TQBF evaluator: the depth-first evaluator `gQ` of `Qbf.lean` with the CNF leaf test
  `verify X p` replaced by an arbitrary polytime leaf `V X p` (`gG V`, `tvG V`); copied proofs.
  A Σ_k language is the generalized formula with prefix = the quantifier blocks and leaf
  `R (codeP x p)`, so it reduces to this PSPACE language.
-/
import PvnpReal.PH
import PvnpReal.PspaceRed

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PvnpReal

open Turing Computability

/-- Value of the generalized quantified formula (leaf `V`). -/
def tvG (V : List Bool → List Bool → Bool) (X : List Bool) : List Bool → List Bool → Bool
  | [], w => V X w
  | q :: qs, w => if q then (tvG V X qs (w ++ [false]) && tvG V X qs (w ++ [true]))
      else (tvG V X qs (w ++ [false]) || tvG V X qs (w ++ [true]))

section Gen
variable {V : List Bool → List Bool → Bool}

/-- One step of the depth-first QBF evaluator. -/
def gG (V : List Bool → List Bool → Bool) (s : List Bool) : List Bool :=
  if NthTM.bit s 0 = 1 then
    (if NthTM.bit s 1 = 1 then
      (if NthTM.bit s 2 = 1 then
        (if (Qs s).length - (Ps s).length = 0 then
          true :: true :: false :: ([V (Xs s) (Ps s)] ++ Rof (Qs s) (Rof (Xs s) (Ps s)))
         else true :: true :: true :: false :: Rof (Qs s) (Rof (Xs s) (Ps s ++ [false])))
       else
        (if (Ps s).length = 0 then [false] ++ [decide (NthTM.bit s 3 = 1)]
         else if NthTM.bit (Ps s) ((Ps s).length - 1) = 1 then
           true :: true :: false :: ([decide (NthTM.bit s 3 = 1)] ++
             Rof (Qs s) (Rof (Xs s) (Ps s).dropLast))
         else if NthTM.bit (Qs s) ((Ps s).length - 1) = NthTM.bit s 3 then
           true :: true :: true :: false :: Rof (Qs s) (Rof (Xs s) ((Ps s).dropLast ++ [true]))
         else true :: true :: false :: ([decide (NthTM.bit s 3 = 1)] ++
             Rof (Qs s) (Rof (Xs s) (Ps s).dropLast))))
     else true :: true :: true :: false :: Rof (decX s.tail.tail) (Rof (decC s.tail.tail) []))
  else [false, false]

theorem PS.gG (hv : PS (fun y => [V (decP y).1 (decP y).2])) : PS (gG V) := by
  have hV : PS (fun s => [V (Xs s) (Ps s)]) :=
    (PS.comp (PS.append (PS.codeL PS.xsF) (PS.cons false (PS.codeL PS.psF))) hv).congr (fun s => by
      show [V (decP (codeP _ _)).1 (decP (codeP _ _)).2] = _
      rw [decP_codeP])
  have hLeaf := PS.cons true (PS.cons true (PS.cons false (PS.append hV (PS.Rof PS.qsF (PS.Rof PS.xsF PS.psF)))))
  have hNext := PS.cons true (PS.cons true (PS.cons true (PS.cons false
    (PS.Rof PS.qsF (PS.Rof PS.xsF (PS.append PS.psF (PS.const [false])))))))
  have hDown := PS.iteEq (PU.sub (PU.lenX.comp PS.qsF) (PU.lenX.comp PS.psF)) (PU.const 0) hLeaf hNext
  have hvb := PS.boolOf (PU.bitAt 3)
  have hPd := PS.comp PS.psF PS.dropLast
  have hUpP := PS.cons true (PS.cons true (PS.cons false (PS.append hvb
    (PS.Rof PS.qsF (PS.Rof PS.xsF hPd)))))
  have hDR := PS.cons true (PS.cons true (PS.cons true (PS.cons false
    (PS.Rof PS.qsF (PS.Rof PS.xsF (PS.append hPd (PS.const [true])))))))
  have hLast : PU (fun s => NthTM.bit (Ps s) ((Ps s).length - 1)) :=
    (PU.nth.comp (PS.append (PU.sub (PU.lenX.comp PS.psF) (PU.const 1)) (PS.cons false PS.psF))).congr
      (fun s => by simp only [lpN_rep, lpX_rep])
  have hQb : PU (fun s => NthTM.bit (Qs s) ((Ps s).length - 1)) :=
    (PU.nth.comp (PS.append (PU.sub (PU.lenX.comp PS.psF) (PU.const 1)) (PS.cons false PS.qsF))).congr
      (fun s => by simp only [lpN_rep, lpX_rep])
  have hUp3 := PS.iteEq hQb (PU.bitAt 3) hDR hUpP
  have hUp2 := PS.iteEq hLast (PU.const 1) hUpP hUp3
  have hUp := PS.iteEq (PU.lenX.comp PS.psF) (PU.const 0) (PS.append (PS.const [false]) hvb) hUp2
  have hRun := PS.iteEq (PU.bitAt 2) (PU.const 1) hDown hUp
  have hT2 : PS (fun s => s.tail.tail) := PS.comp PS.tail PS.tail
  have hStart := PS.cons true (PS.cons true (PS.cons true (PS.cons false
    (PS.Rof (PS.comp hT2 PS.decX) (PS.Rof (PS.comp hT2 PS.decC) (PS.const []))))))
  have hIn := PS.iteEq (PU.bitAt 1) (PU.const 1) hRun hStart
  exact (PS.iteEq (PU.bitAt 0) (PU.const 1) hIn (PS.const [false, false])).congr (fun s => rfl)

theorem gG_start (y : List Bool) : (gG V) (true :: false :: y) = St true false (decX y) (decC y) [] := by
  simp [gG, NthTM.bit, St]

theorem gG_leaf (v : Bool) (qs X p : List Bool) (h : qs.length ≤ p.length) :
    (gG V) (St true v qs X p) = St false (V X p) qs X p := by
  have h' : qs.length - p.length = 0 := by omega
  unfold gG; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  simp [h', St]

theorem gG_down (v : Bool) (qs X p : List Bool) (h : p.length < qs.length) :
    (gG V) (St true v qs X p) = St true false qs X (p ++ [false]) := by
  have h' : qs.length - p.length ≠ 0 := by omega
  unfold gG; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  simp [h', St]

theorem gG_up_nil (v : Bool) (qs X : List Bool) : (gG V) (St false v qs X []) = [false, v] := by
  unfold gG; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  cases v <;> simp

theorem gG_up_true (v : Bool) (qs X p : List Bool) :
    (gG V) (St false v qs X (p ++ [true])) = St false v qs X p := by
  unfold gG; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  have hb : NthTM.bit (p ++ [true]) p.length = 1 := by simp [NthTM.bit]
  cases v <;> simp [hb, St]

theorem gG_up_false (v : Bool) (qs X p : List Bool) (h : p.length < qs.length) :
    (gG V) (St false v qs X (p ++ [false])) =
      if qs.getD p.length false = v then St true false qs X (p ++ [true]) else St false v qs X p := by
  have hq : NthTM.bit qs p.length = if qs.getD p.length false then 1 else 0 := by
    simp only [NthTM.bit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    cases qs[p.length] <;> simp
  have hb : NthTM.bit (p ++ [false]) ((p ++ [false]).length - 1) = 0 := by
    rw [bit_concat_last]; rfl
  unfold gG
  simp only [bit0_St, bit1_St, bit2_St, bit3_St, Ps_St, Qs_St, Xs_St, hb]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, hq]
  cases hg : qs.getD p.length false <;> cases v <;> simp [St]

/-! ### The run -/

theorem tvG_split (X qs p : List Bool) (h : p.length < qs.length) :
    (tvG V) X (qs.drop p.length) p = if qs.getD p.length false then
      ((tvG V) X (qs.drop (p.length + 1)) (p ++ [false]) && (tvG V) X (qs.drop (p.length + 1)) (p ++ [true]))
      else ((tvG V) X (qs.drop (p.length + 1)) (p ++ [false]) || (tvG V) X (qs.drop (p.length + 1)) (p ++ [true])) := by
  rw [List.drop_eq_getElem_cons h]
  simp [tvG, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- **Correctness and step bound of the evaluator**: from a descending state at path `p`, the evaluator
returns the value of the subformula at `p` within `4·2^{|qs|-|p|} - 3` steps, through valid states. -/
theorem runG_down (qs X : List Bool) : ∀ k p v, qs.length - p.length = k → p.length ≤ qs.length →
    ∃ j, j + 3 ≤ 4 * 2 ^ k ∧
      (gG V)^[j] (St true v qs X p) = St false ((tvG V) X (qs.drop p.length) p) qs X p ∧
      ∀ i ≤ j, GoodQ qs X ((gG V)^[i] (St true v qs X p)) := by
  intro k
  induction k with
  | zero =>
    intro p v hk hp
    have hd : qs.drop p.length = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨1, by norm_num, ?_, good_one ⟨true, v, p, rfl, hp⟩ ?_⟩
    · rw [Function.iterate_one, gG_leaf (V := V) v qs X p (by omega), hd]; rfl
    · rw [gG_leaf (V := V) v qs X p (by omega)]; exact ⟨false, _, p, rfl, hp⟩
  | succ k ih =>
    intro p v hk hp
    have hlt : p.length < qs.length := by omega
    have e1 : (gG V)^[1] (St true v qs X p) = St true false qs X (p ++ [false]) := by
      rw [Function.iterate_one, gG_down (V := V) v qs X p hlt]
    have G1 : ∀ i ≤ 1, GoodQ qs X ((gG V)^[i] (St true v qs X p)) :=
      good_one ⟨true, v, p, rfl, hp⟩ (by rw [gG_down (V := V) v qs X p hlt]; exact ⟨_, _, _, rfl, by simp; omega⟩)
    obtain ⟨j0, hj0, e0, G0⟩ := ih (p ++ [false]) false (by simp; omega) (by simp; omega)
    simp only [List.length_append, List.length_singleton] at e0
    have hsplit := tvG_split (V := V) X qs p hlt
    obtain ⟨v0, hv0⟩ : ∃ v0, v0 = (tvG V) X (qs.drop (p.length + 1)) (p ++ [false]) := ⟨_, rfl⟩
    rw [← hv0] at e0 hsplit
    have eup := gG_up_false (V := V) v0 qs X p hlt
    have h2k : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by ring
    by_cases hq : qs.getD p.length false = v0
    · rw [if_pos hq] at eup
      obtain ⟨j1, hj1, e1', G1'⟩ := ih (p ++ [true]) false (by simp; omega) (by simp; omega)
      simp only [List.length_append, List.length_singleton] at e1'
      obtain ⟨v1, hv1⟩ : ∃ v1, v1 = (tvG V) X (qs.drop (p.length + 1)) (p ++ [true]) := ⟨_, rfl⟩
      rw [← hv1] at e1' hsplit
      have e2 : (gG V)^[1] (St false v0 qs X (p ++ [false])) = St true false qs X (p ++ [true]) := by
        rw [Function.iterate_one, eup]
      have e3 : (gG V)^[1] (St false v1 qs X (p ++ [true])) = St false v1 qs X p := by
        rw [Function.iterate_one, gG_up_true (V := V)]
      have hval : (tvG V) X (qs.drop p.length) p = v1 := by
        rw [hsplit, hq]; cases v0 <;> simp
      refine ⟨1 + (j1 + (1 + (j0 + 1))), by omega, ?_, ?_⟩
      · rw [hval]; exact iter_chain (iter_chain (iter_chain (iter_chain e1 e0) e2) e1') e3
      · have Gs2 : ∀ i ≤ 1, GoodQ qs X ((gG V)^[i] (St false v0 qs X (p ++ [false]))) :=
          good_one ⟨_, _, _, rfl, by simp; omega⟩ (by rw [eup]; exact ⟨_, _, _, rfl, by simp; omega⟩)
        have Gs3 : ∀ i ≤ 1, GoodQ qs X ((gG V)^[i] (St false v1 qs X (p ++ [true]))) :=
          good_one ⟨_, _, _, rfl, by simp; omega⟩ (by rw [gG_up_true (V := V)]; exact ⟨_, _, _, rfl, hp⟩)
        exact good_chain (good_chain (good_chain (good_chain G1 e1 G0) (iter_chain e1 e0) Gs2)
          (iter_chain (iter_chain e1 e0) e2) G1')
          (iter_chain (iter_chain (iter_chain e1 e0) e2) e1') Gs3
    · rw [if_neg hq] at eup
      have e2 : (gG V)^[1] (St false v0 qs X (p ++ [false])) = St false v0 qs X p := by
        rw [Function.iterate_one, eup]
      have hval : (tvG V) X (qs.drop p.length) p = v0 := by
        rw [hsplit]
        cases hg : qs.getD p.length false <;> rw [hg] at hq <;> cases v0 <;> simp at hq ⊢
      refine ⟨1 + (j0 + 1), by omega, ?_, ?_⟩
      · rw [hval]; exact iter_chain (iter_chain e1 e0) e2
      · have Gs2 : ∀ i ≤ 1, GoodQ qs X ((gG V)^[i] (St false v0 qs X (p ++ [false]))) :=
          good_one ⟨_, _, _, rfl, by simp; omega⟩ (by rw [eup]; exact ⟨_, _, _, rfl, hp⟩)
        exact good_chain (good_chain G1 e1 G0) (iter_chain e1 e0) Gs2

theorem evalG_in_PSPACE (hv : PS (fun y => [V (decP y).1 (decP y).2])) :
    InPSPACE (fun y => tvG V (decC y) (decX y) [] = true) := by
  classical
  let hg : TM2ComputableInPolyTime strEnc strEnc (gG V) := Classical.choice (PS.gG hv)
  let f : List Bool → Bool := fun y => (tvG V) (decC y) (decX y) []
  let Lb : ℕ → ℕ := fun n => 21 * n + 14
  let J : ℕ → ℕ := fun n => 4 * 2 ^ n + 2
  have hF : ∀ x, ∃ j ≤ J x.length, (∀ i < j, ((gG V)^[i] (true :: false :: x)).head? = some true) ∧
      ((gG V)^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, ((gG V)^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      ((gG V)^[j] (true :: false :: x)).tail = [f x] := by
    intro y
    set qs := decX y
    set X := decC y
    have hqs : qs.length ≤ y.length := decX_len y
    have hX : X.length ≤ y.length := decC_len y
    obtain ⟨j, hj, e, G⟩ := runG_down qs X qs.length [] false (by simp) (by simp)
    simp only [List.length_nil, List.drop_zero] at e
    have eS : (gG V)^[1] (true :: false :: y) = St true false qs X [] := by
      rw [Function.iterate_one, gG_start (V := V)]
    have eF : (gG V)^[1] (St false ((tvG V) X qs []) qs X []) = [false, (tvG V) X qs []] := by
      rw [Function.iterate_one, gG_up_nil (V := V)]
    have eAll := iter_chain (iter_chain eS e) eF
    have hmid : ∀ i ≤ j, GoodQ qs X ((gG V)^[i + 1] (true :: false :: y)) := by
      intro i hi
      rw [Function.iterate_succ_apply, gG_start (V := V)]; exact G i hi
    have hpow : 2 ^ qs.length ≤ 2 ^ y.length := Nat.pow_le_pow_right (by norm_num) hqs
    refine ⟨1 + (j + 1), by show _ ≤ 4 * 2 ^ y.length + 2; omega, fun i hi => ?_, ?_,
      fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · rfl
      · obtain ⟨m, v, p, hs, -⟩ := hmid i (by omega)
        rw [hs]; rfl
    · rw [eAll]; simp
    · rcases i with _ | i
      · simp [Lb]; omega
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · obtain ⟨m, v, p, hs, hp⟩ := hmid i (by omega)
          rw [hs]
          have := St_len m v qs X p hp
          show _ ≤ 21 * y.length + 14
          omega
        · rw [show i + 1 = 1 + (j + 1) by omega, eAll]; simp [Lb]
    · rw [eAll]; rfl
  obtain ⟨h, hsp⟩ := whileDecider hg f J Lb hF
  let C := pushTotal h.tm
  let Lp : Polynomial ℕ := 21 * Polynomial.X + 14
  let p : Polynomial ℕ := Polynomial.X + Lp + Polynomial.C C *
    (2 * Polynomial.X + 2 * Lp + hg.time.comp Lp + 6)
  refine ⟨p, f, h, fun x i c hi hc k => (hsp x i c hi hc k).trans (le_of_eq ?_), fun x => ?_⟩
  · simp [p, Lp, Lb, C, Polynomial.eval_comp]
  · rfl

end Gen

/-! ### Σ_k ⊆ PSPACE -/

/-- A block of `m` equal quantifiers (`c = true`: ∀, `false`: ∃) is a quantifier over `{0,1}^m`. -/
theorem tvG_rep (V : List Bool → List Bool → Bool) (X rest : List Bool) (c : Bool) :
    ∀ (m : ℕ) (p : List Bool), tvG V X (List.replicate m c ++ rest) p = true ↔
      (if c then ∀ w : List Bool, w.length = m → tvG V X rest (p ++ w) = true
       else ∃ w : List Bool, w.length = m ∧ tvG V X rest (p ++ w) = true) := by
  intro m
  induction m with
  | zero => intro p; cases c <;> simp [List.length_eq_zero_iff]
  | succ m ih =>
    intro p
    cases c
    · simp only [List.replicate_succ, List.cons_append, tvG, Bool.false_eq_true, if_false,
        Bool.or_eq_true, ih]
      constructor
      · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
        · exact ⟨false :: u, by simp [hu], by simpa using h⟩
        · exact ⟨true :: u, by simp [hu], by simpa using h⟩
      · rintro ⟨u, hu, h⟩
        rcases u with _ | ⟨b, u⟩
        · simp at hu
        · simp only [List.length_cons, Nat.add_right_cancel_iff] at hu
          cases b
          · exact Or.inl ⟨u, hu, by simpa using h⟩
          · exact Or.inr ⟨u, hu, by simpa using h⟩
    · simp only [List.replicate_succ, List.cons_append, tvG, if_true, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h0, h1⟩ u hu
        rcases u with _ | ⟨b, u⟩
        · simp at hu
        · simp only [List.length_cons, Nat.add_right_cancel_iff] at hu
          cases b
          · simpa using h0 u hu
          · simpa using h1 u hu
      · intro h
        exact ⟨fun u hu => by simpa using h (false :: u) (by simp [hu]),
          fun u hu => by simpa using h (true :: u) (by simp [hu])⟩

/-- The quantifier prefix of a Σ_k/Π_k formula (`b = true`: first block existential). -/
def patQ (qs : ℕ → Polynomial ℕ) (n : ℕ) : ℕ → Bool → List Bool
  | 0, _ => []
  | k + 1, b => List.replicate ((qs k).eval n) (!b) ++ patQ qs n k (!b)

theorem tvG_patQ (R : Language) (f : List Bool → Bool) (hf : ∀ s, R s ↔ f s = true)
    (qs : ℕ → Polynomial ℕ) (x : List Bool) :
    ∀ k b u, tvG (fun X p => f (codeP X p)) x (patQ qs x.length k b) u = true ↔ altQ R qs x k b u := by
  intro k
  induction k with
  | zero => intro b u; simp [patQ, tvG, hf]
  | succ k ih =>
    intro b u
    cases b
    · simp only [patQ, Bool.not_false, tvG_rep, if_true, ih, altQ_succ_false]
    · simp only [patQ, Bool.not_true, tvG_rep, Bool.false_eq_true, if_false, ih, altQ_succ_true]

theorem PS.patQ (qs : ℕ → Polynomial ℕ) : ∀ k b, PS (fun x => patQ qs x.length k b) := by
  intro k
  induction k with
  | zero => intro b; exact PS.const []
  | succ k ih =>
    intro b
    have hr : PS (fun x => List.replicate ((qs k).eval x.length) (!b)) := by
      cases b
      · exact PU.poly (qs k)
      · exact PS.repF (PU.poly (qs k))
    exact PS.append hr (ih (!b))

/-- **Σ_k ⊆ PSPACE.** -/
theorem Sigma_subset_PSPACE (k : ℕ) (L : Language) (h : InSigma k L) : InPSPACE L := by
  obtain ⟨R, qs, ⟨f, ⟨hf⟩, hfR⟩, hL⟩ := h
  let V : List Bool → List Bool → Bool := fun X p => f (codeP X p)
  have hv : PS (fun y => [V (decP y).1 (decP y).2]) :=
    PS.comp (PS.codePF PS.fstP PS.sndP) ⟨deciderToStr hf⟩
  refine InPSPACE.of_reduces ⟨fun x => Rof (patQ qs x.length k true) x,
    PS.Rof (PS.patQ qs k true) PS.id, fun x => ?_⟩ (evalG_in_PSPACE hv)
  simp only [decX_Rof, decC_Rof]
  exact (hL x).trans (tvG_patQ R f hfR qs x k true []).symm

/-- **Π_k ⊆ PSPACE.** -/
theorem Pi_subset_PSPACE (k : ℕ) (L : Language) (h : InPi k L) : InPSPACE L :=
  (Sigma_subset_PSPACE k _ ((InPi_iff_compl k L).1 h)).compl.congr (fun _ => not_not)

/-- **PH ⊆ PSPACE.** -/
theorem PH_subset_PSPACE (L : Language) (h : InPH L) : InPSPACE L :=
  let ⟨k, hk⟩ := h; Sigma_subset_PSPACE k L hk

end PvnpReal
