/-
  PvnpReal.Diag2 — the flat interpreter `U2` and **`diagU2_in_EXP : InEXP (diagLang U2)`**
  (unconditional): pad to `1^{2^n} 0 x`, build the initial flat configuration, run
  `PS.stepIter`, read the state's tag.
-/
import PvnpReal.Flat

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability NE

/-- **Exponential padding then polytime** gives EXP. -/
theorem InEXP_of_padF (d : List Bool → Bool) (hd : PS (fun w => [d w])) (L : Language)
    (hL : ∀ x, L x ↔ d (padF x) = true) : InEXP L := by
  obtain ⟨hs⟩ := hd
  let h2 := strToDecider hs
  let P := h2.time
  let hc := composeInTime padComputable h2.toTM2ComputableInTime (fun m => P.eval m)
    (fun m => le_rfl) (fun a b h => poly_eval_mono P h)
  obtain ⟨r, hr⟩ := poly_two_pow P
  set C := pushTotal padComputable.tm
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C (C + 5)) +
    r.comp (Polynomial.X + Polynomial.C (C + 5)) + 3
  refine ⟨d ∘ padF, q, ⟨hc, fun n => ?_⟩, hL⟩
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

namespace Flat

def ltE (a b : NE) : NE := sgn (sub b a)

@[simp] theorem ev_sgn (a : NE) (i L) : (sgn a).ev i L = if a.ev i L = 0 then 0 else 1 := by
  simp only [sgn, ev_sub, ev_c]; split <;> omega

@[simp] theorem ev_lt (a b : NE) (i L) : (ltE a b).ev i L = if a.ev i L < b.ev i L then 1 else 0 := by
  unfold ltE sgn; simp only [ev_sub, ev_c]; split_ifs <;> omega

/-! Source list `S = [T, n] ++ bits(y) ++ Pc` and the initial configuration. -/

def sT : NE := gt 0
def sN : NE := gt 1
def sBit (j : NE) : NE := get (add (c 2) j)
def sPc (m : NE) : NE := get (add (c 2) (add sN m))
def iNK : NE := sPc (c 0)
def iW : NE := sPc (c 1)
def iK0 : NE := sPc (c 2)
def iIn0 : NE := sPc (c 3)
def iIn1 : NE := sPc (c 4)
def iStart : NE := sPc (c 5)
def iCap : NE := add sN (add sT (c 1))
def iPB : NE := add (c 5) (add iNK (mul iNK iCap))
def iN : NE := add iPB (add sN sT)
def iBase : NE := add (c 5) (add iNK (mul iK0 iCap))
def iCell : NE := ite (sBit (sub (sub sN (c 1)) (sub p iBase))) iIn1 iIn0

def initE : NE :=
  ite (eq p (c 0)) iStart (ite (eq p (c 1)) iCap (ite (eq p (c 2)) iNK (ite (eq p (c 3)) iW
    (ite (eq p (c 4)) iN (ite (ltE p (add (c 5) iNK)) (ite (eq (sub p (c 5)) iK0) sN (c 0))
      (ite (ltE p iPB) (ite (mul (ltE p (add iBase sN)) (ltE iBase (add p (c 1)))) iCell (c 0))
        (sPc (sub p iPB))))))))

def initL (S : List ℕ) : List ℕ := (List.range (iN.ev 0 S)).map (fun i => initE.ev i S)

def srcL (x y : List Bool) (t : ℕ) : List ℕ :=
  [t, y.length] ++ (List.range y.length).map (fun j => NthTM.bit y j) ++ numsOf (lpX x)

def tagOf (L : List ℕ) : ℕ := tagE.ev 0 L

end Flat

open Flat

/-- **The flat interpreter**: program `numsOf (lpX x)`, input `y`, clock `t` (also used for the
stack capacity `|y| + t + 1`). Answer: accept-tag `5` ↦ `true`, reject-tag `0` ↦ `false`. -/
def U2 (x y : List Bool) (t : ℕ) : Option Bool :=
  let tg := tagOf (stepL^[t] (initL (srcL x y t)))
  if tg = 5 then some true else if tg = 0 then some false else none

theorem numsOf_encNums_append (l : List ℕ) (r : List Bool) : numsOf (encNums l ++ r) = l ++ numsOf r := by
  induction l with
  | nil => simp [encNums]
  | cons a l ih =>
    have : encNums (a :: l) ++ r = List.replicate a true ++ false :: (encNums l ++ r) := by
      simp [encNums]
    rw [this, numsOf_ne (by simp), lpN_rep, lpX_rep, ih]; rfl

theorem numsOf_stepB_iter (t : ℕ) (L : List ℕ) : numsOf (stepB^[t] (encNums L)) = stepL^[t] L := by
  induction t with
  | zero => simp [numsOf_encNums]
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    simp [stepB, numsOf_encNums]

def srcW (w : List Bool) : List ℕ := srcL (lpX w) (lpX w) (lpN w)

def bitsEnc (x : List Bool) : List Bool :=
  (List.range x.length).flatMap (fun j => List.replicate (NthTM.bit x j) true ++ [false])

theorem PS.bitsEnc {s : List Bool → List Bool} (hs : PS s) : PS (fun w => bitsEnc (s w)) := by
  have hg : PS (fun z => List.replicate (lpN z) true ++ false :: s (lpX z)) :=
    PS.append PU.fst (PS.cons false (PS.comp PS.drop hs))
  have hU : PU (fun z => NthTM.bit (s (lpX z)) (lpN z)) :=
    (PU.nth.comp hg).congr (fun z => by simp only [lpN_rep, lpX_rep])
  exact PS.flatRange (PU.lenX.comp hs) (fun j w => List.replicate (NthTM.bit (s w) j) true ++ [false])
    (PS.append hU (PS.const [false]))

def srcBits (w : List Bool) : List Bool :=
  List.replicate (lpN w) true ++ false :: (List.replicate (lpX w).length true ++ false ::
    (bitsEnc (lpX w) ++ lpX (lpX w)))

theorem numsOf_srcBits (w : List Bool) : numsOf (srcBits w) = srcW w := by
  have : srcBits w = encNums ([lpN w, (lpX w).length] ++
      (List.range (lpX w).length).map (fun j => NthTM.bit (lpX w) j)) ++ lpX (lpX w) := by
    simp [srcBits, bitsEnc, encNums, List.flatMap_map]
  rw [this, numsOf_encNums_append]; rfl

theorem PS.srcBits : PS srcBits :=
  PS.append PU.fst (PS.cons false (PS.append (PU.lenX.comp PS.drop) (PS.cons false
    (PS.append (PS.bitsEnc PS.drop) (PS.comp PS.drop PS.drop)))))

/-- The diagonal decision on padded inputs. -/
def dW (w : List Bool) : Bool := decide (tagOf (stepL^[lpN w] (initL (srcW w))) ≠ 5)

theorem PS.dW : PS (fun w => [dW w]) := by
  have hI : PS (fun w => encNums (initL (srcW w))) :=
    (PS.comp PS.srcBits (PS.mapNums iN initE)).congr (fun w => by
      simp only [numsOf_srcBits]; rfl)
  have hZ : PS (fun w => List.replicate (lpN w) true ++ false :: encNums (initL (srcW w))) :=
    PS.append PU.fst (PS.cons false hI)
  have hIt : PS (fun w => stepB^[lpN w] (encNums (initL (srcW w)))) :=
    (PS.comp hZ PS.stepIter).congr (fun w => by simp only [lpN_rep, lpX_rep])
  have hR : PU (fun w => (sub (c 1) (eq tagE (c 5))).ev 0 (numsOf (stepB^[lpN w] (encNums (initL (srcW w)))))) :=
    PU.comp (NE.pu0 _) hIt
  refine (PS.comp hR ⟨orComputable⟩).congr (fun w => ?_)
  simp only [numsOf_stepB_iter, SmallTM.orF, PvnpReal.dW, tagOf, ev_sub, ev_eq, ev_c]
  by_cases h : tagE.ev 0 (stepL^[lpN w] (initL (srcW w))) = 5 <;> simp [h]

/-- **The diagonal language of `U2` is in EXP** (unconditional). -/
theorem diagU2_in_EXP : InEXP (diagLang U2) := by
  refine InEXP_of_padF dW PS.dW _ (fun x => ?_)
  have h1 : lpN (padF x) = 2 ^ x.length := by simp [padF, lpN_rep]
  have h2 : lpX (padF x) = x := by simp [padF, lpX_rep]
  simp only [diagLang, U2, dW, srcW, h1, h2]
  constructor
  · intro h; simpa using fun e => h (by simp [e])
  · intro h; simp at h; split <;> simp_all

end PvnpReal
