/-
  PvnpReal.CircEval — circuits as gate lists, a bit encoding of `BCirc`, and a polynomial-time
  circuit evaluator; hence **`InPpolyCirc L → InPpoly L`** (circuit description as advice).
-/
import PvnpReal.KarpLipton

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing Computability

open scoped Classical

/-! ### CGate-list semantics -/

def opN (op : ℕ) (a b : Bool) : Bool := if op = 0 then a && b else if op = 1 then a || b else !a

abbrev CGate := ℕ × ℕ × ℕ

/-- Append the value of gate `g` (reading `false` outside the current wires). -/
def pStep (v : List Bool) (g : CGate) : List Bool :=
  v ++ [opN g.1 (v.getD g.2.1 false) (v.getD g.2.2 false)]

def pRun (v : List Bool) (gs : List CGate) : List Bool := gs.foldl pStep v

theorem pRun_nil (v : List Bool) : pRun v [] = v := rfl

theorem pRun_cons (v : List Bool) (g : CGate) (gs : List CGate) : pRun v (g :: gs) = pRun (pStep v g) gs := rfl

theorem pRun_append (v : List Bool) (gs hs : List CGate) : pRun v (gs ++ hs) = pRun (pRun v gs) hs := by
  simp [pRun, List.foldl_append]

theorem pRun_length : ∀ (gs : List CGate) (v : List Bool), (pRun v gs).length = v.length + gs.length
  | [], v => by simp [pRun]
  | g :: gs, v => by rw [pRun_cons, pRun_length gs]; simp [pStep]; omega

theorem pRun_getD : ∀ (gs : List CGate) (v : List Bool) {j : ℕ}, j < v.length →
    (pRun v gs).getD j false = v.getD j false
  | [], v, j, _ => rfl
  | g :: gs, v, j, hj => by
    rw [pRun_cons, pRun_getD gs _ (by simp [pStep]; omega)]
    simp [pStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

def gatesOf {n s : ℕ} (C : BCirc n s) : List CGate :=
  (List.finRange s).map (fun i => (((C.1 i).1 : ℕ), ((C.1 i).2.1 : ℕ), ((C.1 i).2.2 : ℕ)))

theorem opN_eq (o : Fin 3) (a b : Bool) : opN o a b = opApply o a b := by
  fin_cases o <;> rfl

theorem wire_pRun {n s : ℕ} (C : BCirc n s) (x : Fin n → Bool) :
    ∀ j < n + s, wire C.1 x j = (pRun (List.ofFn x) (gatesOf C)).getD j false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hG : (gatesOf C).length = s := by simp [gatesOf]
    by_cases hjn : j < n
    · rw [wire, dif_pos hjn, pRun_getD _ _ (by simpa using hjn)]
      simp [List.getD_eq_getElem?_getD, hjn]
    · have his : j - n < s := by omega
      rw [wire, dif_neg hjn, dif_pos his]
      set V := pRun (List.ofFn x) ((gatesOf C).take (j - n)) with hV
      have hVl : V.length = j := by rw [hV, pRun_length]; simp [hG]; omega
      have hsplit : gatesOf C = (gatesOf C).take (j - n) ++ (gatesOf C)[j - n]'(by omega) ::
          (gatesOf C).drop (j - n + 1) := by
        rw [← List.drop_eq_getElem_cons]; simp
      have hfull : pRun (List.ofFn x) (gatesOf C) =
          pRun (pStep V ((gatesOf C)[j - n]'(by omega))) ((gatesOf C).drop (j - n + 1)) := by
        conv_lhs => rw [hsplit]
        rw [pRun_append, pRun_cons]
      rw [hfull, pRun_getD _ _ (by simp [pStep]; omega)]
      have hg : (gatesOf C)[j - n]'(by omega) = (((C.1 ⟨j - n, his⟩).1 : ℕ), ((C.1 ⟨j - n, his⟩).2.1 : ℕ),
          ((C.1 ⟨j - n, his⟩).2.2 : ℕ)) := by simp [gatesOf]
      have hrd : ∀ a : ℕ, a < n + s → (if _h : a < j then wire C.1 x a else false) = V.getD a false := by
        intro a ha
        by_cases haj : a < j
        · rw [dif_pos haj, ih a haj ha, hfull, pRun_getD _ _ (by simp [pStep]; omega)]
          simp [pStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show a < V.length by omega)]
        · rw [dif_neg haj]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show V.length ≤ a by omega)]
      rw [hg, hrd _ (C.1 ⟨j - n, his⟩).2.1.2, hrd _ (C.1 ⟨j - n, his⟩).2.2.2]
      simp [pStep, List.getD_eq_getElem?_getD, hVl, opN_eq]

theorem eval_pRun {n s : ℕ} (C : BCirc n s) (x : Fin n → Bool) :
    C.eval x = (pRun (List.ofFn x) (gatesOf C)).getD C.2 false := by
  unfold BCirc.eval
  split_ifs with h
  · exact wire_pRun C x _ h
  · have hl : (pRun (List.ofFn x) (gatesOf C)).length = n + s := by
      rw [pRun_length]; simp [gatesOf]
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show (pRun (List.ofFn x) (gatesOf C)).length ≤ (C.2 : ℕ) by omega)]

/-! ### Bit encoding of circuits -/

def encG (g : CGate) : List Bool := encNs [g.1, g.2.1, g.2.2]

/-- `1^out 0 1^s 0` followed by the gates `1^op 0 1^a 0 1^b 0`. -/
def encC {n s : ℕ} (C : BCirc n s) : List Bool := encNs [(C.2 : ℕ), s] ++ (gatesOf C).flatMap encG

theorem encNs_length (l : List ℕ) : (encNs l).length = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [encNs_cons]; simp [ih]; omega

theorem encC_length_le {n s : ℕ} (C : BCirc n s) :
    (encC C).length ≤ (n + s + 1) + (s + 1) + s * (2 * (n + s) + 5) := by
  unfold encC
  rw [List.length_append, encNs_length, List.length_flatMap]
  have h1 : ∀ g ∈ gatesOf C, (encG g).length ≤ 2 * (n + s) + 5 := by
    intro g hg
    simp only [gatesOf, List.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    have h1 := (C.1 i).1.2; have h2 := (C.1 i).2.1.2; have h3 := (C.2.2)
    have h4 := (C.1 i).2.2.2
    simp [encG, encNs_length]; omega
  have h2 : ((gatesOf C).map (fun g => (encG g).length)).sum ≤ (gatesOf C).length * (2 * (n + s) + 5) := by
    have := List.sum_le_card_nsmul ((gatesOf C).map (fun g => (encG g).length)) (2 * (n + s) + 5)
      (by intro a ha; obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha; exact h1 g hg)
    simpa using this
  have hG : (gatesOf C).length = s := by simp [gatesOf]
  have := C.2.2
  simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] 
  rw [hG] at h2
  omega

/-! ### The evaluator -/

/-- One gate: state `codeP (gate codes) (wire values)`. -/
def cStep (y : List Bool) : List Bool :=
  codeP (lpX (lpX (lpX (decP y).1)))
    (pStep (decP y).2 (lpN (decP y).1, lpN (lpX (decP y).1), lpN (lpX (lpX (decP y).1))))

theorem lpN_encNs (a : ℕ) (l : List ℕ) (r : List Bool) : lpN (encNs (a :: l) ++ r) = a := by
  rw [encNs_cons, List.append_assoc, List.cons_append, lpN_rep]

theorem lpX_encNs (a : ℕ) (l : List ℕ) (r : List Bool) : lpX (encNs (a :: l) ++ r) = encNs l ++ r := by
  rw [encNs_cons, List.append_assoc, List.cons_append, lpX_rep]

theorem cStep_code (g : CGate) (gs : List CGate) (r v : List Bool) :
    cStep (codeP ((g :: gs).flatMap encG ++ r) v) = codeP (gs.flatMap encG ++ r) (pStep v g) := by
  rcases g with ⟨a, b, c⟩
  simp only [cStep, decP_codeP, List.flatMap_cons, encG, List.append_assoc]
  simp only [lpX_encNs, lpN_encNs]
  simp [encNs]

theorem cStep_iter : ∀ (gs : List CGate) (r v : List Bool),
    cStep^[gs.length] (codeP (gs.flatMap encG ++ r) v) = codeP r (pRun v gs)
  | [], r, v => rfl
  | g :: gs, r, v => by
    rw [List.length_cons, Function.iterate_succ_apply, cStep_code, cStep_iter gs, pRun_cons]

/-- The circuit-evaluation language on `codeP x e`: `e` = `1^out 0 1^s 0` + gate codes (+ junk). -/
def CEval : Language := fun t =>
  (decP (cStep^[lpN (lpX (decP t).2)] (codeP (lpX (lpX (decP t).2)) (decP t).1))).2.getD
    (lpN (decP t).2) false = true

theorem CEval_code {n s : ℕ} (C : BCirc n s) (x : Fin n → Bool) (pad : List Bool) :
    CEval (codeP (List.ofFn x) (encC C ++ pad)) ↔ C.eval x = true := by
  have hG : (gatesOf C).length = s := by simp [gatesOf]
  simp only [CEval, decP_codeP, encC, List.append_assoc]
  simp only [lpX_encNs, lpN_encNs, show encNs [] = [] from rfl, List.nil_append]
  have := cStep_iter (gatesOf C) pad (List.ofFn x)
  rw [hG] at this
  rw [this, decP_codeP, eval_pRun]

theorem codeL_drop_len (k : ℕ) (g : List Bool) : (codeL (g.drop k)).length ≤ (codeL g).length := by
  conv_rhs => rw [← List.take_append_drop k g]
  rw [codeL_append, List.length_append]; omega

theorem lpX_drop (y : List Bool) : ∃ k, lpX y = y.drop k := ⟨_, rfl⟩

theorem cStep_len_code (g v : List Bool) : (cStep (codeP g v)).length ≤ (codeP g v).length + 3 := by
  simp only [cStep, decP_codeP]
  obtain ⟨k, hk⟩ : ∃ k, lpX (lpX (lpX g)) = g.drop k := by
    refine ⟨lpN g + 1 + (lpN (lpX g) + 1) + (lpN (lpX (lpX g)) + 1), ?_⟩
    simp only [lpX, List.drop_drop]
  rw [hk]
  have := codeL_drop_len k g
  have hb : ∀ b, (codeL [b]).length ≤ 3 := by intro b; cases b <;> simp [codeL]
  simp only [codeP, pStep, codeL_append, List.length_append, List.length_cons]
  have := hb (opN (lpN g) (v.getD (lpN (lpX g)) false) (v.getD (lpN (lpX (lpX g))) false))
  omega

theorem cStep_len (y : List Bool) : (cStep y).length ≤ 3 * y.length + 4 := by
  have h1 := codeP_length_le (lpX (lpX (lpX (decP y).1)))
    (pStep (decP y).2 (lpN (decP y).1, lpN (lpX (decP y).1), lpN (lpX (lpX (decP y).1))))
  have hB : (pStep (decP y).2 (lpN (decP y).1, lpN (lpX (decP y).1), lpN (lpX (lpX (decP y).1)))).length =
      (decP y).2.length + 1 := by simp [pStep]
  have h2 := decP_len y.length y le_rfl
  have h3 : (lpX (lpX (lpX (decP y).1))).length ≤ (decP y).1.length := by
    have := LoopTM.lp_len (decP y).1; have := LoopTM.lp_len (lpX (decP y).1)
    have := LoopTM.lp_len (lpX (lpX (decP y).1)); omega
  show (codeP _ _).length ≤ _
  omega

theorem cStep_iter_len : ∀ i y, (cStep^[i] y).length ≤ 3 * y.length + 4 + 3 * i := by
  have hc : ∀ i g v, (cStep^[i] (codeP g v)).length ≤ (codeP g v).length + 3 * i := by
    intro i
    induction i with
    | zero => intro g v; simp
    | succ i ih =>
      intro g v
      rw [Function.iterate_succ_apply]
      have e : cStep (codeP g v) = codeP (decP (cStep (codeP g v))).1 (decP (cStep (codeP g v))).2 := by
        simp [cStep, decP_codeP]
      rw [e]
      have := ih (decP (cStep (codeP g v))).1 (decP (cStep (codeP g v))).2
      have := cStep_len_code g v
      rw [e] at this
      omega
  intro i y
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply]
    have e : cStep y = codeP (decP (cStep y)).1 (decP (cStep y)).2 := by simp [cStep, decP_codeP]
    rw [e]
    have := hc i (decP (cStep y)).1 (decP (cStep y)).2
    have := cStep_len y
    rw [e] at this
    omega

theorem PS.cStepP : PS cStep := by
  have hg : PS (fun y => (decP y).1) := PS.fstP
  have hv : PS (fun y => (decP y).2) := PS.sndP
  have hop : PU (fun y => lpN (decP y).1) := PU.fst.comp hg
  have ha : PU (fun y => lpN (lpX (decP y).1)) := PU.fst.comp (PS.comp hg PS.drop)
  have hb : PU (fun y => lpN (lpX (lpX (decP y).1))) := PU.fst.comp (PS.comp (PS.comp hg PS.drop) PS.drop)
  have hbit : ∀ {u : List Bool → ℕ}, PU u → PU (fun y => NthTM.bit (decP y).2 (u y)) := fun hu =>
    (PU.nth.comp (PS.append hu (PS.cons false hv))).congr (fun y => by simp only [lpN_rep, lpX_rep])
  have hz0 := PU.indEq hop (PU.const 0)
  have hz1 := PU.indEq hop (PU.const 1)
  have hr : PU (fun y => (if lpN (decP y).1 = 0 then 1 else 0) *
        (NthTM.bit (decP y).2 (lpN (lpX (decP y).1)) * NthTM.bit (decP y).2 (lpN (lpX (lpX (decP y).1)))) +
      (if lpN (decP y).1 = 1 then 1 else 0) *
        min 1 (NthTM.bit (decP y).2 (lpN (lpX (decP y).1)) + NthTM.bit (decP y).2 (lpN (lpX (lpX (decP y).1)))) +
      (1 - (if lpN (decP y).1 = 0 then 1 else 0) - (if lpN (decP y).1 = 1 then 1 else 0)) *
        (1 - NthTM.bit (decP y).2 (lpN (lpX (decP y).1)))) :=
    ((hz0.mul ((hbit ha).mul (hbit hb))).add (hz1.mul (PU.minU (PU.const 1) ((hbit ha).add (hbit hb))))).add
      (((PU.const 1).sub hz0).sub hz1 |>.mul ((PU.const 1).sub (hbit ha)))
  have hnew := PS.boolOf hr
  refine (PS.codePF (PS.comp (PS.comp (PS.comp hg PS.drop) PS.drop) PS.drop) (PS.append hv hnew)).congr
    (fun y => ?_)
  simp only [cStep, pStep, List.append_cancel_left_eq, List.cons.injEq, and_true]
  have bv : ∀ (l : List Bool) (i : ℕ), NthTM.bit l i = if l.getD i false then 1 else 0 := by
    intro l i
    simp only [NthTM.bit, List.getD_eq_getElem?_getD]
    rcases l[i]? with _ | _ | _ <;> simp
  rw [bv, bv]
  unfold opN
  by_cases h0 : lpN (decP y).1 = 0
  · simp only [h0, if_true]
    cases (decP y).2.getD (lpN (lpX (decP y).1)) false <;>
      cases (decP y).2.getD (lpN (lpX (lpX (decP y).1))) false <;> simp
  · by_cases h1 : lpN (decP y).1 = 1
    · simp only [h1, if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
      cases (decP y).2.getD (lpN (lpX (decP y).1)) false <;>
        cases (decP y).2.getD (lpN (lpX (lpX (decP y).1))) false <;> simp
    · simp only [h0, h1, if_false]
      cases (decP y).2.getD (lpN (lpX (decP y).1)) false <;> simp

theorem InP.CEvalP : InP CEval := by
  have he : PS (fun t => (decP t).2) := PS.sndP
  have hI := PS.iter PS.cStepP (3 * Polynomial.X + 4) (fun y i => by
    have := cStep_iter_len i y
    simp; nlinarith)
  have hz : PS (fun t => List.replicate (lpN (lpX (decP t).2)) true ++
      false :: codeP (lpX (lpX (decP t).2)) (decP t).1) :=
    PS.append (PU.fst.comp (PS.comp he PS.drop))
      (PS.cons false (PS.codePF (PS.comp (PS.comp he PS.drop) PS.drop) PS.fstP))
  have hV : PS (fun t => (decP (cStep^[lpN (lpX (decP t).2)] (codeP (lpX (lpX (decP t).2)) (decP t).1))).2) :=
    (PS.comp (PS.comp hz hI) PS.sndP).congr (fun t => by simp only [lpN_rep, lpX_rep])
  have hb : PU (fun t => NthTM.bit (decP (cStep^[lpN (lpX (decP t).2)]
      (codeP (lpX (lpX (decP t).2)) (decP t).1))).2 (lpN (decP t).2)) :=
    (PU.nth.comp (PS.append (PU.fst.comp he) (PS.cons false hV))).congr
      (fun t => by simp only [lpN_rep, lpX_rep])
  refine (InP.ofPUeq hb (PU.const 1)).congr (fun t => ?_)
  simp only [CEval, NthTM.bit, List.getD_eq_getElem?_getD]
  rcases (decP (cStep^[lpN (lpX (decP t).2)] (codeP (lpX (lpX (decP t).2)) (decP t).1))).2[lpN (decP t).2]?
    with _ | _ | _ <;> simp

/-! ### Circuits ⇒ advice -/

/-- **Polynomial-size circuits ⇒ polynomial advice** (`InPpolyCirc L → InPpoly L`). -/
theorem InPpoly_of_circ {L : Language} (h : InPpolyCirc L) : InPpoly L := by
  obtain ⟨q, hq⟩ := h
  have hc : ∀ n, ∃ s, s ≤ q.eval n ∧ ∃ C : BCirc n s,
      C.eval = fun x : Fin n → Bool => decide (L (List.ofFn x)) := fun n => by
    obtain ⟨s, hs, C, hC⟩ := hq n; exact ⟨s, hs, C, hC⟩
  choose s hs C hC using hc
  set QB : Polynomial ℕ := (Polynomial.X + q + 1) + (q + 1) + q * (2 * (Polynomial.X + q) + 5)
  have hlen : ∀ n, (encC (C n)).length ≤ QB.eval n := by
    intro n
    have := encC_length_le (C n)
    have h1 := hs n
    simp only [QB, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    have : s n * (2 * (n + s n) + 5) ≤ q.eval n * (2 * (n + q.eval n) + 5) :=
      Nat.mul_le_mul h1 (by omega)
    omega
  refine ⟨CEval, QB, fun n => encC (C n) ++ List.replicate (QB.eval n - (encC (C n)).length) false,
    InP.CEvalP, fun n => by have := hlen n; simp; omega, fun x => ?_⟩
  have hx : List.ofFn (fun i : Fin x.length => x[i]) = x := List.ofFn_getElem
  conv_rhs => rw [show codeP x _ = codeP (List.ofFn (fun i : Fin x.length => x[i])) _ by rw [hx]]
  rw [CEval_code, hC]
  simp [hx]

/-- Karp–Lipton with the **circuit** hypothesis: `NP ⊆ P/poly(circuits) → PH = Σ₂`. -/
theorem karpLipton_circ (H : ∀ L, InNP L → InPpolyCirc L) (L : Language) : InPH L ↔ InSigma 2 L :=
  karpLipton (fun L' hL' => InPpoly_of_circ (H L' hL')) L

theorem NP_not_subset_PpolyCirc_of_PH_ne_Sigma2 (h : ¬ ∀ L, InPH L ↔ InSigma 2 L) :
    ¬ ∀ L, InNP L → InPpolyCirc L :=
  fun H => h (karpLipton_circ H)

end PvnpReal
