/-
  PvnpReal.Qbf — quantified Boolean formulas and **TQBF ∈ PSPACE**.

  * A QBF is a quantifier prefix `qs` (`true` = ∀, `false` = ∃; `qs[i]` binds variable `xᵢ`) and a
    CNF matrix `φ` (variables not bound by the prefix default to `false`, as in `asg`).
  * Encoding `encodeQBF Q = Rof qs (encodeCNF φ)`; `TQBF y` decodes `y` with the total decoders
    `decX`/`decC` and evaluates the matrix with the SAT verifier `verify` (which rejects non-codes).
  * The evaluator `gQ` is a non-recursive depth-first search whose state holds only the prefix,
    the matrix, the current path `p` (≤ |qs| bits), a mode bit and one value bit; it is run by the
    space-bounded while-loop machine (`whileDecider`).
-/
import PvnpReal.SatSpace

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### Definitions -/

/-- A quantified Boolean formula in prenex form with a CNF matrix. -/
structure QBF where
  qs : List Bool
  φ : CNF

/-- Value of the formula under the partial assignment `w` with remaining prefix `qs`. -/
def qval (φ : CNF) : List Bool → List Bool → Bool
  | [], w => evalCNF φ (asg w)
  | q :: qs, w => if q then (qval φ qs (w ++ [false]) && qval φ qs (w ++ [true]))
      else (qval φ qs (w ++ [false]) || qval φ qs (w ++ [true]))

def QBF.val (Q : QBF) : Bool := qval Q.φ Q.qs []

def encodeQBF (Q : QBF) : List Bool := Rof Q.qs (encodeCNF Q.φ)

/-- The same evaluation on a string-coded matrix (via the SAT verifier). -/
def tv (X : List Bool) : List Bool → List Bool → Bool
  | [], w => verify X w
  | q :: qs, w => if q then (tv X qs (w ++ [false]) && tv X qs (w ++ [true]))
      else (tv X qs (w ++ [false]) || tv X qs (w ++ [true]))

/-- **TQBF**: the true quantified Boolean formulas (strings decoded by `decX`/`decC`). -/
def TQBF : Language := fun y => tv (decC y) (decX y) [] = true

theorem tv_encode (φ : CNF) : ∀ qs w, tv (encodeCNF φ) qs w = qval φ qs w := by
  intro qs
  induction qs with
  | nil => intro w; simp [tv, qval, verify_encode]
  | cons q qs ih => intro w; simp [tv, qval, ih]

/-- **TQBF is exactly the set of codes of true QBFs** (on codes). -/
theorem TQBF_encode (Q : QBF) : TQBF (encodeQBF Q) ↔ Q.val = true := by
  simp [TQBF, encodeQBF, decX_Rof, decC_Rof, tv_encode, QBF.val]

/-- Sanity checks: `∀x₀. x₀` is false, `∃x₀. x₀` is true, `∀x₀ ∃x₁. (x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)` is true. -/
theorem qbf_ex1 : (QBF.mk [true] [[⟨0, false⟩]]).val = false := by decide
theorem qbf_ex2 : (QBF.mk [false] [[⟨0, false⟩]]).val = true := by decide
theorem qbf_ex3 :
    (QBF.mk [true, false] [[⟨0, false⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨1, true⟩]]).val = true := by decide

/-! ### The evaluator -/

/-- Running state: mode `m` (`true` = descend, `false` = return value `v`), path `p`. -/
def St (m v : Bool) (qs X p : List Bool) : List Bool := true :: true :: m :: v :: Rof qs (Rof X p)

def R4 (s : List Bool) : List Bool := s.tail.tail.tail.tail
def Qs (s : List Bool) : List Bool := decX (R4 s)
def Xs (s : List Bool) : List Bool := decX (decC (R4 s))
def Ps (s : List Bool) : List Bool := decC (decC (R4 s))

/-- One step of the depth-first QBF evaluator. -/
def gQ (s : List Bool) : List Bool :=
  if NthTM.bit s 0 = 1 then
    (if NthTM.bit s 1 = 1 then
      (if NthTM.bit s 2 = 1 then
        (if (Qs s).length - (Ps s).length = 0 then
          true :: true :: false :: ([verify (Xs s) (Ps s)] ++ Rof (Qs s) (Rof (Xs s) (Ps s)))
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

theorem PU.bitAt (k : ℕ) : PU (fun s => NthTM.bit s k) :=
  (PU.nth.comp (PS.append (PU.const k) (PS.cons false PS.id))).congr (fun s => by
    simp only [lpN_rep, lpX_rep])

theorem PS.r4F : PS R4 :=
  (PS.comp (PS.comp (PS.comp PS.tail PS.tail) PS.tail) PS.tail).congr (fun _ => rfl)
theorem PS.qsF : PS Qs := (PS.comp PS.r4F PS.decX).congr (fun _ => rfl)
theorem PS.xsF : PS Xs := (PS.comp (PS.comp PS.r4F PS.decC) PS.decX).congr (fun _ => rfl)
theorem PS.psF : PS Ps := (PS.comp (PS.comp PS.r4F PS.decC) PS.decC).congr (fun _ => rfl)

theorem PS.gQ : PS gQ := by
  have hv : PS (fun y => [verify (decP y).1 (decP y).2]) :=
    ⟨deciderToStr (composeGen decComputable satVerifierComputable)⟩
  have hV : PS (fun s => [verify (Xs s) (Ps s)]) :=
    (PS.comp (PS.append (PS.codeL PS.xsF) (PS.cons false (PS.codeL PS.psF))) hv).congr (fun s => by
      show [verify (decP (codeP _ _)).1 (decP (codeP _ _)).2] = _
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

/-! ### Step lemmas -/

@[simp] theorem Qs_St (m v : Bool) (qs X p : List Bool) : Qs (St m v qs X p) = qs := by
  simp [Qs, R4, St, decX_Rof]
@[simp] theorem Xs_St (m v : Bool) (qs X p : List Bool) : Xs (St m v qs X p) = X := by
  simp [Xs, R4, St, decX_Rof, decC_Rof]
@[simp] theorem Ps_St (m v : Bool) (qs X p : List Bool) : Ps (St m v qs X p) = p := by
  simp [Ps, R4, St, decC_Rof]
@[simp] theorem bit0_St (m v : Bool) (qs X p : List Bool) : NthTM.bit (St m v qs X p) 0 = 1 := by
  simp [St, NthTM.bit]
@[simp] theorem bit1_St (m v : Bool) (qs X p : List Bool) : NthTM.bit (St m v qs X p) 1 = 1 := by
  simp [St, NthTM.bit]
@[simp] theorem bit2_St (m v : Bool) (qs X p : List Bool) :
    NthTM.bit (St m v qs X p) 2 = if m then 1 else 0 := by
  cases m <;> simp [St, NthTM.bit]
@[simp] theorem bit3_St (m v : Bool) (qs X p : List Bool) :
    NthTM.bit (St m v qs X p) 3 = if v then 1 else 0 := by
  cases v <;> simp [St, NthTM.bit]

theorem gQ_start (y : List Bool) : gQ (true :: false :: y) = St true false (decX y) (decC y) [] := by
  simp [gQ, NthTM.bit, St]

theorem gQ_leaf (v : Bool) (qs X p : List Bool) (h : qs.length ≤ p.length) :
    gQ (St true v qs X p) = St false (verify X p) qs X p := by
  have h' : qs.length - p.length = 0 := by omega
  unfold gQ; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  simp [h', St]

theorem gQ_down (v : Bool) (qs X p : List Bool) (h : p.length < qs.length) :
    gQ (St true v qs X p) = St true false qs X (p ++ [false]) := by
  have h' : qs.length - p.length ≠ 0 := by omega
  unfold gQ; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  simp [h', St]

theorem gQ_up_nil (v : Bool) (qs X : List Bool) : gQ (St false v qs X []) = [false, v] := by
  unfold gQ; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  cases v <;> simp

theorem bit_concat_last (p : List Bool) (b : Bool) :
    NthTM.bit (p ++ [b]) ((p ++ [b]).length - 1) = if b then 1 else 0 := by
  cases b <;> simp [NthTM.bit]

theorem gQ_up_true (v : Bool) (qs X p : List Bool) :
    gQ (St false v qs X (p ++ [true])) = St false v qs X p := by
  unfold gQ; simp only [bit0_St, bit1_St, bit2_St, bit3_St, Qs_St, Xs_St, Ps_St]
  have hb : NthTM.bit (p ++ [true]) p.length = 1 := by simp [NthTM.bit]
  cases v <;> simp [hb, St]

theorem gQ_up_false (v : Bool) (qs X p : List Bool) (h : p.length < qs.length) :
    gQ (St false v qs X (p ++ [false])) =
      if qs.getD p.length false = v then St true false qs X (p ++ [true]) else St false v qs X p := by
  have hq : NthTM.bit qs p.length = if qs.getD p.length false then 1 else 0 := by
    simp only [NthTM.bit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    cases qs[p.length] <;> simp
  have hb : NthTM.bit (p ++ [false]) ((p ++ [false]).length - 1) = 0 := by
    rw [bit_concat_last]; rfl
  unfold gQ
  simp only [bit0_St, bit1_St, bit2_St, bit3_St, Ps_St, Qs_St, Xs_St, hb]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, hq]
  cases hg : qs.getD p.length false <;> cases v <;> simp [St]

/-! ### The run -/

def GoodQ (qs X s : List Bool) : Prop := ∃ m v p, s = St m v qs X p ∧ p.length ≤ qs.length

theorem good_chain {α : Type*} {g : α → α} {P : α → Prop} {x y : α} {a b : ℕ}
    (G1 : ∀ i ≤ a, P (g^[i] x)) (e : g^[a] x = y) (G2 : ∀ i ≤ b, P (g^[i] y)) :
    ∀ i ≤ b + a, P (g^[i] x) := by
  intro i hi
  rcases Nat.lt_or_ge i (a + 1) with h | h
  · exact G1 i (by omega)
  · have : g^[i] x = g^[i - a] y := by
      rw [← e, ← Function.iterate_add_apply]; congr 1; omega
    rw [this]; exact G2 _ (by omega)

theorem good_one {α : Type*} {g : α → α} {P : α → Prop} {x : α} (h0 : P x) (h1 : P (g x)) :
    ∀ i ≤ 1, P (g^[i] x) := by
  intro i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · exact h0
  · exact h1

theorem tv_split (X qs p : List Bool) (h : p.length < qs.length) :
    tv X (qs.drop p.length) p = if qs.getD p.length false then
      (tv X (qs.drop (p.length + 1)) (p ++ [false]) && tv X (qs.drop (p.length + 1)) (p ++ [true]))
      else (tv X (qs.drop (p.length + 1)) (p ++ [false]) || tv X (qs.drop (p.length + 1)) (p ++ [true])) := by
  rw [List.drop_eq_getElem_cons h]
  simp [tv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- **Correctness and step bound of the evaluator**: from a descending state at path `p`, the evaluator
returns the value of the subformula at `p` within `4·2^{|qs|-|p|} - 3` steps, through valid states. -/
theorem run_down (qs X : List Bool) : ∀ k p v, qs.length - p.length = k → p.length ≤ qs.length →
    ∃ j, j + 3 ≤ 4 * 2 ^ k ∧
      gQ^[j] (St true v qs X p) = St false (tv X (qs.drop p.length) p) qs X p ∧
      ∀ i ≤ j, GoodQ qs X (gQ^[i] (St true v qs X p)) := by
  intro k
  induction k with
  | zero =>
    intro p v hk hp
    have hd : qs.drop p.length = [] := List.drop_eq_nil_of_le (by omega)
    refine ⟨1, by norm_num, ?_, good_one ⟨true, v, p, rfl, hp⟩ ?_⟩
    · rw [Function.iterate_one, gQ_leaf v qs X p (by omega), hd]; rfl
    · rw [gQ_leaf v qs X p (by omega)]; exact ⟨false, _, p, rfl, hp⟩
  | succ k ih =>
    intro p v hk hp
    have hlt : p.length < qs.length := by omega
    have e1 : gQ^[1] (St true v qs X p) = St true false qs X (p ++ [false]) := by
      rw [Function.iterate_one, gQ_down v qs X p hlt]
    have G1 : ∀ i ≤ 1, GoodQ qs X (gQ^[i] (St true v qs X p)) :=
      good_one ⟨true, v, p, rfl, hp⟩ (by rw [gQ_down v qs X p hlt]; exact ⟨_, _, _, rfl, by simp; omega⟩)
    obtain ⟨j0, hj0, e0, G0⟩ := ih (p ++ [false]) false (by simp; omega) (by simp; omega)
    simp only [List.length_append, List.length_singleton] at e0
    have hsplit := tv_split X qs p hlt
    obtain ⟨v0, hv0⟩ : ∃ v0, v0 = tv X (qs.drop (p.length + 1)) (p ++ [false]) := ⟨_, rfl⟩
    rw [← hv0] at e0 hsplit
    have eup := gQ_up_false v0 qs X p hlt
    have h2k : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by ring
    by_cases hq : qs.getD p.length false = v0
    · rw [if_pos hq] at eup
      obtain ⟨j1, hj1, e1', G1'⟩ := ih (p ++ [true]) false (by simp; omega) (by simp; omega)
      simp only [List.length_append, List.length_singleton] at e1'
      obtain ⟨v1, hv1⟩ : ∃ v1, v1 = tv X (qs.drop (p.length + 1)) (p ++ [true]) := ⟨_, rfl⟩
      rw [← hv1] at e1' hsplit
      have e2 : gQ^[1] (St false v0 qs X (p ++ [false])) = St true false qs X (p ++ [true]) := by
        rw [Function.iterate_one, eup]
      have e3 : gQ^[1] (St false v1 qs X (p ++ [true])) = St false v1 qs X p := by
        rw [Function.iterate_one, gQ_up_true]
      have hval : tv X (qs.drop p.length) p = v1 := by
        rw [hsplit, hq]; cases v0 <;> simp
      refine ⟨1 + (j1 + (1 + (j0 + 1))), by omega, ?_, ?_⟩
      · rw [hval]; exact iter_chain (iter_chain (iter_chain (iter_chain e1 e0) e2) e1') e3
      · have Gs2 : ∀ i ≤ 1, GoodQ qs X (gQ^[i] (St false v0 qs X (p ++ [false]))) :=
          good_one ⟨_, _, _, rfl, by simp; omega⟩ (by rw [eup]; exact ⟨_, _, _, rfl, by simp; omega⟩)
        have Gs3 : ∀ i ≤ 1, GoodQ qs X (gQ^[i] (St false v1 qs X (p ++ [true]))) :=
          good_one ⟨_, _, _, rfl, by simp; omega⟩ (by rw [gQ_up_true]; exact ⟨_, _, _, rfl, hp⟩)
        exact good_chain (good_chain (good_chain (good_chain G1 e1 G0) (iter_chain e1 e0) Gs2)
          (iter_chain (iter_chain e1 e0) e2) G1')
          (iter_chain (iter_chain (iter_chain e1 e0) e2) e1') Gs3
    · rw [if_neg hq] at eup
      have e2 : gQ^[1] (St false v0 qs X (p ++ [false])) = St false v0 qs X p := by
        rw [Function.iterate_one, eup]
      have hval : tv X (qs.drop p.length) p = v0 := by
        rw [hsplit]
        cases hg : qs.getD p.length false <;> rw [hg] at hq <;> cases v0 <;> simp at hq ⊢
      refine ⟨1 + (j0 + 1), by omega, ?_, ?_⟩
      · rw [hval]; exact iter_chain (iter_chain e1 e0) e2
      · have Gs2 : ∀ i ≤ 1, GoodQ qs X (gQ^[i] (St false v0 qs X (p ++ [false]))) :=
          good_one ⟨_, _, _, rfl, by simp; omega⟩ (by rw [eup]; exact ⟨_, _, _, rfl, hp⟩)
        exact good_chain (good_chain G1 e1 G0) (iter_chain e1 e0) Gs2

theorem decX_len (y : List Bool) : (decX y).length ≤ y.length := by
  unfold decX
  rw [flatMap_singleton_range]
  simp only [List.length_map, List.length_range]
  have := LoopTM.lp_len y; omega

theorem decC_len (y : List Bool) : (decC y).length ≤ y.length := by
  unfold decC
  rw [flatMap_singleton_range]
  simp only [List.length_map, List.length_range]
  have h1 := LoopTM.lp_len y
  have h2 := LoopTM.lp_len (lpX y)
  omega

theorem St_len (m v : Bool) (qs X p : List Bool) (hp : p.length ≤ qs.length) :
    (St m v qs X p).length ≤ 12 * qs.length + 9 * X.length + 12 := by
  have h1 := Rof_len qs (Rof X p)
  have h2 := Rof_len X p
  simp only [St, List.length_cons]
  omega

/-- **TQBF ∈ PSPACE.** -/
theorem TQBF_in_PSPACE : InPSPACE TQBF := by
  classical
  let hg : TM2ComputableInPolyTime strEnc strEnc gQ := Classical.choice PS.gQ
  let f : List Bool → Bool := fun y => tv (decC y) (decX y) []
  let Lb : ℕ → ℕ := fun n => 21 * n + 14
  let J : ℕ → ℕ := fun n => 4 * 2 ^ n + 2
  have hF : ∀ x, ∃ j ≤ J x.length, (∀ i < j, (gQ^[i] (true :: false :: x)).head? = some true) ∧
      (gQ^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, (gQ^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      (gQ^[j] (true :: false :: x)).tail = [f x] := by
    intro y
    set qs := decX y
    set X := decC y
    have hqs : qs.length ≤ y.length := decX_len y
    have hX : X.length ≤ y.length := decC_len y
    obtain ⟨j, hj, e, G⟩ := run_down qs X qs.length [] false (by simp) (by simp)
    simp only [List.length_nil, List.drop_zero] at e
    have eS : gQ^[1] (true :: false :: y) = St true false qs X [] := by
      rw [Function.iterate_one, gQ_start]
    have eF : gQ^[1] (St false (tv X qs []) qs X []) = [false, tv X qs []] := by
      rw [Function.iterate_one, gQ_up_nil]
    have eAll := iter_chain (iter_chain eS e) eF
    have hmid : ∀ i ≤ j, GoodQ qs X (gQ^[i + 1] (true :: false :: y)) := by
      intro i hi
      rw [Function.iterate_succ_apply, gQ_start]; exact G i hi
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

/-! ## Part 5: SAT ≤ TQBF (purely existential prefix), NP-hardness and corollaries -/

theorem tv_exists (X : List Bool) : ∀ (k : ℕ) (w : List Bool),
    tv X (List.replicate k false) w = true ↔ ∃ u : List Bool, u.length = k ∧ verify X (w ++ u) = true := by
  intro k
  induction k with
  | zero => intro w; simp [tv]
  | succ k ih =>
    intro w
    simp only [List.replicate_succ, tv, Bool.false_eq_true, if_false, Bool.or_eq_true, ih]
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

theorem asg_pad (w : List Bool) (n : ℕ) : asg (w ++ List.replicate n false) = asg w := by
  funext v
  unfold asg
  rcases Nat.lt_or_ge v w.length with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getElem?_replicate,
      List.getElem?_eq_none h]
    split_ifs <;> rfl

theorem verify_pad (x w : List Bool) (n : ℕ) (h : verify x w = true) :
    verify x (w ++ List.replicate n false) = true := by
  obtain ⟨φ, rfl, h2⟩ := verify_sound x w h
  rw [verify_encode, asg_pad, h2]

/-- The reduction: the CNF `x` with an all-`∃` prefix of length `|x|`. -/
def satToQbf (x : List Bool) : List Bool := Rof (List.replicate x.length false) x

theorem SATLang_iff_TQBF (x : List Bool) : SATLang x ↔ TQBF (satToQbf x) := by
  simp only [TQBF, satToQbf, decX_Rof, decC_Rof, tv_exists, List.nil_append, SATLang_iff_verify]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w ++ List.replicate (x.length - w.length) false, by simp; omega, verify_pad x w _ h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu.le, h⟩

theorem PS.replFalse : PS (fun x : List Bool => List.replicate x.length false) :=
  (PS.flatRange PU.lenX (fun _ _ => [false]) (PS.const [false])).congr (fun z => by
    rw [flatMap_singleton_range z.length (fun _ => false)]; simp)

theorem PS.satToQbf : PS satToQbf := PS.Rof PS.replFalse PS.id

theorem SAT_reduces_TQBF : PolyReduces SATLang TQBF :=
  ⟨satToQbf, PS.satToQbf, SATLang_iff_TQBF⟩

/-- **TQBF is NP-hard**: every NP language reduces to it in polynomial time. -/
theorem TQBF_NPHard (L : Language) (hL : InNP L) : PolyReduces L TQBF :=
  (SAT_NPComplete.2 L hL).trans SAT_reduces_TQBF

/-- **`P = PSPACE → TQBF ∈ P`.** -/
theorem TQBF_in_P_of_P_eq_PSPACE (h : P_eq_PSPACE) : InP TQBF := (h TQBF).2 TQBF_in_PSPACE

/-- **`TQBF ∈ P → P = NP`.** -/
theorem P_eq_NP_of_TQBF_in_P (h : InP TQBF) : P_eq_NP :=
  fun L => ⟨P_subset_NP L, fun hL => InP.of_reduces (TQBF_NPHard L hL) h⟩

/-- Contrapositive: **`P ≠ NP → TQBF ∉ P`.** -/
theorem TQBF_not_in_P_of_P_ne_NP (h : ¬ P_eq_NP) : ¬ InP TQBF :=
  fun h' => h (P_eq_NP_of_TQBF_in_P h')

end PvnpReal
