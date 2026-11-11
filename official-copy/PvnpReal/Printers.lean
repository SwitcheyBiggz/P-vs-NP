/-
  PvnpReal.Printers — printing combinators built from the verified machines:
  constant strings, `encVar` of a computed unary index, literals, and `encList` of a list whose
  `i`-th element is computable from `1ⁱ 0 x` (via `loopComputable` and `fanComputable`).
-/
import PvnpReal.Loop
import PvnpReal.PolyEval

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

namespace SmallTM

/-- Push the list `c` onto the output stack so that its head ends up on top. -/
def pushL : List Bool → St → St
  | [], q => q
  | b :: bs, q => pushL bs (push UK.out (fun _ => b) q)

theorem stepAux_pushL (c : List Bool) : ∀ (q : St) (v : Option Bool) (i o : List Bool),
    TM2.stepAux (pushL c q) v (st i o) = TM2.stepAux q v (st i (c ++ o)) := by
  induction c with
  | nil => intro q v i o; rfl
  | cons b bs ih =>
    intro q v i o
    show TM2.stepAux (pushL bs (push UK.out (fun _ => b) q)) v (st i o) = _
    rw [ih]
    show TM2.stepAux q v (Function.update (st i (bs ++ o)) UK.out (b :: (bs ++ o))) = _
    rw [upd_out]; rfl

def constStmt (c : List Bool) : UL → St
  | .l1 => pop UK.inp (fun _ o => o) (branch isS (goto fun _ => .l1) (pushL c halt))
  | .l2 => halt

theorem const_loop (c : List Bool) (l : List Bool) (v : Option Bool) :
    (flip bind (TM2.step (constStmt c)))^[l.length + 1] (some ⟨some .l1, v, st l []⟩) =
      some ⟨none, none, st [] c⟩ := by
  induction l generalizing v with
  | nil =>
    show some (TM2.stepAux (constStmt c .l1) v (st [] [])) = _
    simp only [constStmt, TM2.stepAux, st_inp, List.head?_nil, List.tail_nil, isS,
      Option.isSome_none, Bool.cond_false, upd_inp]
    rw [stepAux_pushL, List.append_nil]; rfl
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constStmt c)) (some ⟨some .l1, v, st (b :: l) []⟩) =
        some ⟨some .l1, some b, st l []⟩ := by
      simp [TM2.step, constStmt, TM2.stepAux, isS, flip]
    rw [e, ih]

end SmallTM

/-- Constant strings are polynomial-time (time `X + 1`). -/
noncomputable def constListComputable (c : List Bool) :
    TM2ComputableInPolyTime strEnc strEnc (fun _ => c) where
  tm := SmallTM.mk (SmallTM.constStmt c)
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun l :=
    { steps := l.length + 1
      evals_in_steps := by
        erw [List.map_id, List.map_id, SmallTM.initList_eq, Option.map_some,
          SmallTM.haltList_eq]
        exact SmallTM.const_loop c l none
      steps_le_m := by simp [strEnc] }

/-! ### Derived printers -/

theorem lpN_rep (n : ℕ) (x : List Bool) : lpN (List.replicate n true ++ false :: x) = n := by
  induction n with
  | zero => simp [lpN]
  | succ n ih => rw [List.replicate_succ, List.cons_append, LoopTM.lpN_cons_true, ih]

theorem lpX_rep (n : ℕ) (x : List Bool) : lpX (List.replicate n true ++ false :: x) = x := by
  induction n with
  | zero => simp [lpX, lpN]
  | succ n ih => rw [List.replicate_succ, List.cons_append, LoopTM.lpX_cons_true, ih]

/-- Transport along pointwise equality. -/
theorem computable_congr {f f' : List Bool → List Bool} (h : ∀ x, f x = f' x)
    (hf : Nonempty (TM2ComputableInPolyTime strEnc strEnc f)) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc f') := by
  have : f = f' := funext h
  exact this ▸ hf

/-- `encVar` of a polynomial-time unary index. -/
theorem encVar_computable (u : List Bool → ℕ)
    (hu : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (u x) true))) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => encVar (u x))) := by
  obtain ⟨hu⟩ := hu
  exact ⟨fanComputable hu (constListComputable [false])⟩

/-- `encLit` of a literal whose variable is a polynomial-time unary index and whose sign is
fixed. -/
theorem encLit_computable (u : List Bool → ℕ) (neg : Bool)
    (hu : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (u x) true))) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => encLit ⟨u x, neg⟩)) := by
  obtain ⟨h⟩ := encVar_computable u hu
  exact ⟨fanComputable (constListComputable [neg]) h⟩

/-- The loop's input `1^{N x} 0 x` is polynomial-time computable from `x`. -/
theorem loopInput_computable (N : List Bool → ℕ)
    (hN : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (N x) true))) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc
      (fun x => List.replicate (N x) true ++ false :: x)) := by
  obtain ⟨hN⟩ := hN
  exact ⟨fanComputable hN (fanComputable (constListComputable [false])
    (idComputableInPolyTime strEnc))⟩

/-- **Concatenation over a polynomial-time range**: if `N` is a polynomial-time unary function
and `G (1ⁱ 0 x) = b i x` for all `i < N x` with `G` polynomial-time, then
`x ↦ b 0 x ++ … ++ b (N x - 1) x` is polynomial-time. -/
theorem flatRange_computable (N : List Bool → ℕ) (b : ℕ → List Bool → List Bool)
    (hN : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (N x) true)))
    (G : List Bool → List Bool) (hG : Nonempty (TM2ComputableInPolyTime strEnc strEnc G))
    (hGb : ∀ x i, i < N x → G (List.replicate i true ++ false :: x) = b i x) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc
      (fun x => (List.range (N x)).flatMap fun i => b i x)) := by
  obtain ⟨hin⟩ := loopInput_computable N hN
  obtain ⟨hG⟩ := hG
  refine computable_congr ?_ ⟨composeComputable hin (loopComputable hG)⟩
  intro x
  simp only [Function.comp, loopF, lpN_rep, lpX_rep]
  apply List.flatMap_congr
  intro i hi
  exact hGb x i (List.mem_range.1 hi)

/-- **`encList` printer**: if the `i`-th element's code `e (a i x)` is polynomial-time from
`1ⁱ 0 x` (for `i < N x`) and `N` is polynomial-time unary, then
`x ↦ encList e [a 0 x, …, a (N x - 1) x]` is polynomial-time. -/
theorem encList_computable {α : Type} (e : α → List Bool) (N : List Bool → ℕ)
    (a : ℕ → List Bool → α)
    (hN : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (N x) true)))
    (G : List Bool → List Bool) (hG : Nonempty (TM2ComputableInPolyTime strEnc strEnc G))
    (hGe : ∀ x i, i < N x → G (List.replicate i true ++ false :: x) = e (a i x)) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc
      (fun x => encList e ((List.range (N x)).map fun i => a i x))) := by
  obtain ⟨hG⟩ := hG
  obtain ⟨hF⟩ := flatRange_computable N (fun i x => true :: e (a i x)) hN
    (fun z => true :: G z) ⟨fanComputable (constListComputable [true]) hG⟩
    (fun x i hi => by rw [hGe x i hi])
  refine computable_congr ?_ ⟨fanComputable hF (constListComputable [false])⟩
  intro x
  show (List.range (N x)).flatMap (fun i => true :: e (a i x)) ++ [false] = _
  generalize List.range (N x) = l
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.flatMap_cons, List.map_cons, encList, List.cons_append,
      List.append_assoc, ih]


/-- Polynomials of a polynomial-time unary quantity are polynomial-time unary. -/
theorem polyOfUnary_computable (u : List Bool → ℕ) (P : Polynomial ℕ)
    (hu : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (u x) true))) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc
      (fun x => List.replicate (P.eval (u x)) true)) := by
  obtain ⟨hu⟩ := hu
  refine computable_congr ?_ ⟨composeComputable hu (polyEvalComputable P)⟩
  intro x
  simp [Function.comp, polyU]

/-- The length of the input, in unary, as a polynomial: `x ↦ 1^{P(|x|)}`. -/
theorem polyLen_computable (P : Polynomial ℕ) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc
      (fun x => List.replicate (P.eval x.length) true)) :=
  ⟨polyEvalComputable P⟩

/-- **Nested ranges**: two nested polynomial-time loops. The inner loop sees `1ⁱ 0 x`. -/
theorem flatRange2_computable (N : List Bool → ℕ) (N' : List Bool → ℕ)
    (b : ℕ → ℕ → List Bool → List Bool)
    (hN : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (N x) true)))
    (hN' : Nonempty (TM2ComputableInPolyTime strEnc strEnc (fun x => List.replicate (N' x) true)))
    (G : List Bool → List Bool) (hG : Nonempty (TM2ComputableInPolyTime strEnc strEnc G))
    (hGb : ∀ x i j, i < N x → j < N' (List.replicate i true ++ false :: x) →
      G (List.replicate j true ++ false :: (List.replicate i true ++ false :: x)) = b i j x) :
    Nonempty (TM2ComputableInPolyTime strEnc strEnc
      (fun x => (List.range (N x)).flatMap fun i =>
        (List.range (N' (List.replicate i true ++ false :: x))).flatMap fun j => b i j x)) := by
  obtain ⟨hin⟩ := flatRange_computable N' (fun j y => G (List.replicate j true ++ false :: y)) hN'
    G hG (fun _ _ _ => rfl)
  obtain ⟨hout⟩ := flatRange_computable N
    (fun i x => (List.range (N' (List.replicate i true ++ false :: x))).flatMap
      fun j => G (List.replicate j true ++ false :: (List.replicate i true ++ false :: x)))
    hN _ ⟨hin⟩ (fun _ _ _ => rfl)
  refine computable_congr ?_ ⟨hout⟩
  intro x
  apply List.flatMap_congr
  intro i hi
  apply List.flatMap_congr
  intro j hj
  exact hGb x i j (List.mem_range.1 hi) (List.mem_range.1 hj)

end PvnpReal
