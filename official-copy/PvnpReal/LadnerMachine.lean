/-
  PvnpReal.LadnerMachine — `n ↦ H n` is polytime (unary), and hence **Ladner's theorem**:
  `¬ P_eq_NP → ∃ L, InNP L ∧ ¬ InP L ∧ ¬ NPComplete L`.
-/
import PvnpReal.LadnerH

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Flat

/-- One `bad` test, on input `1^j 0 z` with `z = 1^n 0 T`. -/
theorem PS.badBody : PS (fun w => [decide (badN (lpN (lpX w)) (numsOf (lpX (lpX w))) (lpN w) = 1)]) := by
  have hs : PU (fun w => (numsOf (lpX (lpX w))).getD (lpN (lpX w)) 0) := PU.getNum PU.fst2 PS.drop2
  have hy : PS (fun w => prog (lpN w)) := PS.comp PS.binL PS.dropLast
  have hx : PS (fun w => prog ((numsOf (lpX (lpX w))).getD (lpN (lpX w)) 0)) :=
    PS.comp (((PS.append hs (PS.cons false PS.id)).comp PS.binL).congr (fun w => by
      simp only [lpN_rep])) PS.dropLast
  have hk := PU.comp PU.fst hx
  have hm := PU.comp PU.lenX hy
  have hn1 : PU (fun w => lpN (lpX w) + 1) := PU.add PU.fst2 (PU.const 1)
  have hc := PU.minU (PU.mul hk (PU.cpow (PU.add hm (PU.const 1)) hk hn1)) hn1
  have htg := PU.u2tag hx hy hc
  have hly : PU (fun w => (lpX (prog (lpN w))).length) := PU.comp PU.lenX (PS.comp hy PS.drop)
  have hny : PU (fun w => lpN (prog (lpN w))) := PU.comp PU.fst hy
  have a1 := PU.indEq hny (PU.cpow hly (PU.getNum hly PS.drop2) (PU.add hny (PU.const 1)))
  have a2 : PU (fun w => lpN [searchB (List.replicate (lpN w + 1) true ++ false ::
      lpX (prog (lpN w)))]) :=
    PU.comp PU.fst (PS.comp (PS.append (PU.add PU.fst (PU.const 1))
      (PS.cons false (PS.comp hy PS.drop))) PS.search)
  have hL := PU.mul a1 a2
  have hb := PU.mul (PU.indEq hc (PU.minU hc PU.fst2))
    (PU.sub (PU.const 1) (PU.add (PU.mul (PU.indEq htg (PU.const 5)) hL)
      (PU.mul (PU.indEq htg (PU.const 0)) (PU.sub (PU.const 1) hL))))
  exact (PS.boolOf hb).congr (fun w => rfl)

theorem PS.foundS : PS (fun z => [found (lpN z) (numsOf (lpX z))]) := by
  have h1 := PS.flatRange PU.fst
    (fun j z => [decide (badN (lpN z) (numsOf (lpX z)) j = 1)]) PS.badBody
  refine (PS.comp h1 ⟨orComputable⟩).congr (fun z => ?_)
  simp only [SmallTM.orF, found, List.cons.injEq, and_true]
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

def newV (z : List Bool) : ℕ :=
  min ((numsOf (lpX z)).getD (lpN z) 0 + lpN [found (lpN z) (numsOf (lpX z))]) (lpN z + 1)

/-- One stage of the table computation. -/
def stepH (z : List Bool) : List Bool :=
  List.replicate (lpN z + 1) true ++ false :: (lpX z ++ (List.replicate (newV z) true ++ [false]))

theorem PS.stepH : PS stepH :=
  PS.append (PU.add PU.fst (PU.const 1)) (PS.cons false (PS.append PS.drop
    (PS.append (PU.minU (PU.add (PU.getNum PU.fst PS.drop) (PU.comp PU.fst PS.foundS))
      (PU.add PU.fst (PU.const 1))) (PS.const [false]))))

def stH (n : ℕ) : List Bool := List.replicate n true ++ false :: encNums (tab n)

theorem stepH_stH (n : ℕ) : stepH (stH n) = stH (n + 1) := by
  simp only [stepH, stH, newV, lpN_rep, lpX_rep, numsOf_encNums]
  simp [tab, encNums, List.flatMap_append]

theorem stepH_iter (n : ℕ) : stepH^[n] (stH 0) = stH n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, stepH_stH]

theorem lpN_lpX_len (z : List Bool) : lpN z + (lpX z).length ≤ z.length := by
  have := lpN_le z
  simp only [lpX, List.length_drop]; omega

theorem stepH_len (z : List Bool) :
    lpN (stepH z) = lpN z + 1 ∧ (stepH z).length ≤ z.length + lpN z + 4 := by
  refine ⟨by simp only [stepH, lpN_rep], ?_⟩
  have h1 := lpN_lpX_len z
  have h2 : newV z ≤ lpN z + 1 := min_le_right _ _
  simp only [stepH, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem stepH_iter_len (y : List Bool) (i : ℕ) :
    lpN (stepH^[i] y) = lpN y + i ∧
      (stepH^[i] y).length ≤ y.length + i * (y.length + i + 4) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨a, b⟩ := stepH_len (stepH^[i] y)
    have hy := lpN_le y
    refine ⟨by omega, ?_⟩
    have : y.length + i * (y.length + i + 4) + (lpN y + i) + 4 ≤
        y.length + (i + 1) * (y.length + (i + 1) + 4) := by nlinarith
    omega

/-- **`n ↦ H n` is polytime** (in unary). -/
theorem PU.H : PU (fun x => H x.length) := by
  have hI := PS.iter PS.stepH (Polynomial.X ^ 2 + 5 * Polynomial.X) (fun y i => by
    have := (stepH_iter_len y i).2
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    nlinarith)
  have hin : PS (fun x => List.replicate x.length true ++ false :: stH 0) :=
    PS.append PU.lenX (PS.cons false (PS.const _))
  refine (PU.getNum PU.fst PS.drop |>.comp (PS.comp hin hI)).congr (fun x => ?_)
  rw [lpN_rep, lpX_rep, stepH_iter]
  simp only [stH, lpN_rep, lpX_rep, numsOf_encNums]
  rfl

/-- **Ladner's theorem** (1975): if `P ≠ NP` then there is an NP language that is neither in P
nor NP-complete (under polytime many-one reductions). Witness: `LH gL`, `gL m = m ^ H m`. -/
theorem ladner (hPNP : ¬ P_eq_NP) : ∃ L, InNP L ∧ ¬ InP L ∧ ¬ NPComplete L :=
  ⟨LH gL, ladner_of_H PU.H hPNP⟩

end PvnpReal
