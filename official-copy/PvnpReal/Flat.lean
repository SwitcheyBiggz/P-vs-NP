/-
  PvnpReal.Flat — the flat universal machine.

  * `NE`: a tiny expression language over a number sequence `L` and a position `i`
    (constants, `i`, `L[e]`, `+`, `*`, truncated `-`), with **`NE.pu`**: every expression is
    computable in polynomial time on `1ⁱ 0 enc(L)` (from the two primitive machines in `NumTM`).
  * `PS.mapNums`: pointwise maps of number sequences given by expressions are polytime.
  * `stepL`: one step of the flat machine (state, capacity, stack lengths, stack cells and the
    program all live in one number list), defined by an `NE` formula; `PS.stepIter`: running it
    `t` times (`1ᵗ 0 enc(L) ↦ enc(stepL^[t] L)`) is polytime.
-/
import PvnpReal.NumTM

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

inductive NE
  | c (n : ℕ)
  | p
  | get (e : NE)
  | add (a b : NE)
  | mul (a b : NE)
  | sub (a b : NE)

namespace NE

def ev : NE → ℕ → List ℕ → ℕ
  | c n, _, _ => n
  | p, i, _ => i
  | get e, i, L => L.getD (e.ev i L) 0
  | add a b, i, L => a.ev i L + b.ev i L
  | mul a b, i, L => a.ev i L * b.ev i L
  | sub a b, i, L => a.ev i L - b.ev i L

/-- **Every expression is polytime** on inputs `1ⁱ 0 enc(L)`. -/
theorem pu (e : NE) : PU (fun z => e.ev (lpN z) (numsOf (lpX z))) := by
  induction e with
  | c n => exact PU.const n
  | p => exact PU.fst
  | get e ih => exact PU.getNum ih PS.drop
  | add a b iha ihb => exact PU.add iha ihb
  | mul a b iha ihb => exact PU.mul iha ihb
  | sub a b iha ihb => exact PU.sub iha ihb

def sgn (a : NE) : NE := sub (c 1) (sub (c 1) a)
def ite (b x y : NE) : NE := add (mul (sgn b) x) (mul (sub (c 1) b) y)
def eq (a b : NE) : NE := sub (c 1) (add (sub a b) (sub b a))

@[simp] theorem ev_c (n i L) : (c n).ev i L = n := rfl
@[simp] theorem ev_p (i L) : p.ev i L = i := rfl
@[simp] theorem ev_get (e : NE) (i L) : (get e).ev i L = L.getD (e.ev i L) 0 := rfl
@[simp] theorem ev_add (a b : NE) (i L) : (add a b).ev i L = a.ev i L + b.ev i L := rfl
@[simp] theorem ev_mul (a b : NE) (i L) : (mul a b).ev i L = a.ev i L * b.ev i L := rfl
@[simp] theorem ev_sub (a b : NE) (i L) : (sub a b).ev i L = a.ev i L - b.ev i L := rfl

@[simp] theorem ev_ite (b x y : NE) (i L) :
    (ite b x y).ev i L = if b.ev i L = 0 then y.ev i L else x.ev i L := by
  simp only [ite, sgn, ev_add, ev_mul, ev_sub, ev_c]
  split
  · next h => rw [h]; simp
  · next h =>
    have : 1 - (1 - b.ev i L) = 1 := by omega
    have h2 : 1 - b.ev i L = 0 := by omega
    rw [this, h2]; simp

@[simp] theorem ev_eq (a b : NE) (i L) : (eq a b).ev i L = if a.ev i L = b.ev i L then 1 else 0 := by
  simp only [eq, ev_add, ev_sub, ev_c]
  split <;> omega

end NE

theorem numsOf_cons_false (y : List Bool) : numsOf (false :: y) = 0 :: numsOf y := by
  rw [numsOf_ne (by simp), LoopTM.lpN_cons_false, LoopTM.lpX_cons_false]

/-- Expressions evaluated at position 0 are polytime on plain encodings. -/
theorem NE.pu0 (e : NE) : PU (fun y => e.ev 0 (numsOf y)) :=
  (PU.comp e.pu (PS.cons false PS.id)).congr (fun y => by
    simp only [LoopTM.lpN_cons_false, LoopTM.lpX_cons_false])

/-- **Pointwise maps of number sequences given by expressions are polytime.** -/
theorem PS.mapNums (N F : NE) :
    PS (fun y => encNums ((List.range (N.ev 0 (numsOf y))).map (fun i => F.ev i (numsOf y)))) := by
  have hb : PS (fun z => List.replicate (F.ev (lpN z) (numsOf (lpX z))) true ++ [false]) :=
    PS.append F.pu (PS.const [false])
  exact (PS.flatRange N.pu0 (fun i y => List.replicate (F.ev i (numsOf y)) true ++ [false]) hb).congr
    (fun y => by simp [encNums, List.flatMap_map])

/-! ### The flat machine

Layout of the list `L`:
`L[0]` state `q`, `L[1]` capacity `Cap`, `L[2]` number of stacks `nK`, `L[3]` instruction width
`W`, `L[4]` total length `N`; `L[5+k]` length of stack `k`; `L[5+nK+k·Cap+d]` the `d`-th cell
(from the bottom) of stack `k`; from `PB = 5+nK+nK·Cap` the program `Pc`, whose instruction `q`
has fields `Pc[6+q·W+f]`: `f=0` tag (0 reject, 1 push, 2 pop, 3 peek, 4 nop, 5 accept),
`f=1` stack, `f=2` symbol, `f=3` next state, `f=4+o` next state after reading `o`
(`o = 0` empty stack, `o = s+1` top symbol `s`). -/

namespace Flat

open NE

def gt (n : ℕ) : NE := get (c n)
def qE : NE := gt 0
def capE : NE := gt 1
def nKE : NE := gt 2
def wE : NE := gt 3
def nE : NE := gt 4
def pbE : NE := add (c 5) (add nKE (mul nKE capE))
def fld (f : NE) : NE := get (add pbE (add (c 6) (add (mul qE wE) f)))
def tagE : NE := fld (c 0)
def kE : NE := fld (c 1)
def aE : NE := fld (c 2)
def nxE : NE := fld (c 3)
def lenE : NE := get (add (c 5) kE)
def baseE (k : NE) : NE := add (c 5) (add nKE (mul k capE))
def topE : NE := get (add (baseE kE) (sub lenE (c 1)))
def oE : NE := ite lenE (add topE (c 1)) (c 0)
def tnE : NE := fld (add (c 4) oE)
def isPush : NE := eq tagE (c 1)
def isPop : NE := eq tagE (c 2)
def isPeek : NE := eq tagE (c 3)
def isNop : NE := eq tagE (c 4)
def newQ : NE := ite isPush nxE (ite isNop nxE (ite (add isPop isPeek) tnE qE))
def newLen : NE := ite isPush (add lenE (c 1)) (ite isPop (sub lenE (c 1)) lenE)
def stepE : NE :=
  ite (eq p (c 0)) newQ (ite (eq p (add (c 5) kE)) newLen
    (ite (mul isPush (eq p (add (baseE kE) lenE))) aE (get p)))

/-- One step of the flat machine. -/
def stepL (L : List ℕ) : List ℕ := (List.range (nE.ev 0 L)).map (fun i => stepE.ev i L)

/-- One step on bit strings. -/
def stepB (y : List Bool) : List Bool := encNums (stepL (numsOf y))

theorem PS.stepB : PS stepB := (PS.mapNums nE stepE).congr (fun y => rfl)

def maxL (L : List ℕ) : ℕ := L.foldr max 0

theorem getD_le (L : List ℕ) (j : ℕ) : L.getD j 0 ≤ maxL L := by
  induction L generalizing j with
  | nil => simp
  | cons a L ih =>
    cases j with
    | zero => simp [maxL]
    | succ j => simp only [List.getD_cons_succ, maxL, List.foldr_cons]; exact (ih j).trans (le_max_right _ _)

theorem le_maxL {L : List ℕ} {a : ℕ} (h : a ∈ L) : a ≤ maxL L := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [maxL, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem maxL_le {L : List ℕ} {B : ℕ} (h : ∀ a ∈ L, a ≤ B) : maxL L ≤ B := by
  induction L with
  | nil => simp [maxL]
  | cons b L ih =>
    simp only [maxL, List.foldr_cons]
    exact max_le (h b (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem newQ_le (i : ℕ) (L : List ℕ) : newQ.ev i L ≤ maxL L := by
  simp only [newQ, ev_ite, nxE, tnE, qE, gt, fld]
  split_ifs <;> exact getD_le _ _

theorem newLen_le (i : ℕ) (L : List ℕ) : newLen.ev i L ≤ maxL L + 1 := by
  have := getD_le L ((add (c 5) kE).ev i L)
  simp only [newLen, ev_ite, ev_add, ev_sub, ev_c, lenE, ev_get] at this ⊢
  split_ifs <;> omega

theorem stepE_le (i : ℕ) (L : List ℕ) : stepE.ev i L ≤ maxL L + 1 := by
  have h1 := newQ_le i L
  have h2 := newLen_le i L
  have h3 := getD_le L ((add pbE (add (c 6) (add (mul qE wE) (c 2)))).ev i L)
  have h4 := getD_le L i
  simp only [stepE, ev_ite, aE, fld, ev_get, ev_p] at h3 ⊢
  split_ifs <;> omega

theorem stepL_max (L : List ℕ) : maxL (stepL L) ≤ maxL L + 1 :=
  maxL_le (fun a ha => by
    simp only [stepL, List.mem_map, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    exact stepE_le i L)

theorem stepL_len (L : List ℕ) : (stepL L).length = L.getD 4 0 := by
  simp [stepL, nE, gt]

/-- Position 4 (the total length) is copied by a step. -/
theorem stepE_four (L : List ℕ) : stepE.ev 4 L = L.getD 4 0 := by
  have e0 : (eq NE.p (c 0)).ev 4 L = 0 := by simp
  have e1 : (eq NE.p (add (c 5) kE)).ev 4 L = 0 := by rw [ev_eq, if_neg]; simp only [ev_p, ev_add, ev_c]; omega
  have e2 : (mul isPush (eq NE.p (add (baseE kE) lenE))).ev 4 L = 0 := by
    rw [ev_mul, ev_eq, if_neg]
    · simp
    · simp only [ev_p, ev_add, baseE, ev_c]; omega
  simp only [stepE, ev_ite, e0, e1, e2, if_true, ev_get, ev_p]

/-- Position 4 (the total length) is copied by a step. -/
theorem stepL_get4 (L : List ℕ) : (stepL L).getD 4 0 ≤ L.getD 4 0 := by
  by_cases h : 4 < L.getD 4 0
  · have h' : 4 < (nE.ev 0 L) := by simpa [nE, gt] using h
    have : (stepL L).getD 4 0 = stepE.ev 4 L := by
      simp only [stepL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h',
        Option.map_some, Option.getD_some]
    rw [this, stepE_four]
  · have : (stepL L).length ≤ 4 := by rw [stepL_len]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp

theorem encNums_length (L : List ℕ) : (encNums L).length ≤ L.length * (maxL L + 1) := by
  induction L with
  | nil => simp [encNums]
  | cons a L ih =>
    have e : encNums (a :: L) = List.replicate a true ++ false :: encNums L := by simp [encNums]
    rw [e]
    simp only [List.length_append, List.length_replicate, List.length_cons, maxL, List.foldr_cons]
    have h1 : a ≤ max a (List.foldr max 0 L) := le_max_left _ _
    have h2 : List.foldr max 0 L ≤ max a (List.foldr max 0 L) := le_max_right _ _
    have h3 : L.length * (maxL L + 1) ≤ L.length * (max a (List.foldr max 0 L) + 1) :=
      Nat.mul_le_mul_left _ (by simp only [maxL]; omega)
    simp only [maxL] at ih h3
    nlinarith

theorem numsOf_len_le (y : List Bool) : (numsOf y).length ≤ y.length := by
  induction h : y.length using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    by_cases hy : y = []
    · subst hy; simp [numsOf_nil]
    · rw [numsOf_ne hy, List.length_cons]
      have := lpX_length_lt hy
      have := ih _ (by omega) (lpX y) rfl
      omega

theorem numsOf_max_le (y : List Bool) : maxL (numsOf y) ≤ y.length := by
  induction h : y.length using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    by_cases hy : y = []
    · subst hy; simp [numsOf_nil, maxL]
    · rw [numsOf_ne hy]
      have h1 := lpX_length_lt hy
      have h2 := ih _ (by omega) (lpX y) rfl
      have h3 := LoopTM.lp_len y
      simp only [maxL, List.foldr_cons] at h2 ⊢
      omega

theorem iter_bounds (L : List ℕ) (i : ℕ) :
    (stepL^[i + 1] L).length ≤ L.getD 4 0 ∧ (stepL^[i + 1] L).getD 4 0 ≤ L.getD 4 0 ∧
      maxL (stepL^[i + 1] L) ≤ maxL L + (i + 1) := by
  induction i with
  | zero =>
    simp only [zero_add, Function.iterate_one]
    exact ⟨(stepL_len L).le, stepL_get4 L, stepL_max L⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨a, b, c⟩ := ih
    refine ⟨?_, (stepL_get4 _).trans b, (stepL_max _).trans (by omega)⟩
    rw [stepL_len]; exact b

theorem stepB_iter (y : List Bool) (i : ℕ) : stepB^[i + 1] y = encNums (stepL^[i + 1] (numsOf y)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [stepB, numsOf_encNums]
    rw [← Function.iterate_succ_apply' stepL]

/-- Growth bound for the iterates of `stepB`. -/
theorem stepB_growth (y : List Bool) (i : ℕ) :
    (stepB^[i] y).length ≤ (y.length + i) * (y.length + i + 1) + y.length := by
  rcases i with _ | i
  · simp
  · rw [stepB_iter]
    have h := encNums_length (stepL^[i + 1] (numsOf y))
    obtain ⟨a, _, c⟩ := iter_bounds (numsOf y) i
    have g4 : (numsOf y).getD 4 0 ≤ y.length := (getD_le _ _).trans (numsOf_max_le y)
    have m := numsOf_max_le y
    have : (stepL^[i + 1] (numsOf y)).length * (maxL (stepL^[i + 1] (numsOf y)) + 1) ≤
        (y.length + (i + 1)) * (y.length + (i + 1) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

/-- **Running the flat machine `t` steps is polytime** (`1ᵗ 0 y ↦ stepB^[t] y`). -/
theorem PS.stepIter : PS (fun z => Flat.stepB^[lpN z] (lpX z)) :=
  PS.iter PS.stepB (Polynomial.X * (Polynomial.X + 1) + Polynomial.X) (fun y i => by
    have := stepB_growth y i; simp; omega)

end Flat

end PvnpReal
