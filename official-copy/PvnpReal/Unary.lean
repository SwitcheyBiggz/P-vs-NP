/-
  PvnpReal.Unary — small verified machines for reading loop inputs `1ⁱ 0 x`, and closure
  properties of "polynomial-time unary quantities".

  * `fstF z = 1^{lpN z}`, `revF z = reverse z`, `revDropF z = reverse (lpX z)`,
    `nthF z = 1^{[ (lpX z)[lpN z] = 1 ]}`.
  * `PU u` (`x ↦ 1^{u x}` is polytime) is closed under constants, `+`, `*`, polynomials of
    `|x|`, and precomposition with polytime maps; `PS f` is "f is polytime".
-/
import PvnpReal.Printers

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

namespace SmallTM

/-! ### `fstTM`: `1ⁿ 0 x ↦ 1ⁿ` -/

def fstStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o)
      (branch isT (push UK.out (fun _ => true) (goto fun _ => .l1)) (goto fun _ => .l2))
  | .l2 => pop UK.inp (fun _ o => o) (branch isS (goto fun _ => .l2) halt)

abbrev FF : Option Cfg → Option Cfg := flip bind (TM2.step fstStmt)
theorem FF_some (c : Cfg) : FF (some c) = TM2.step fstStmt c := rfl

theorem fst_count (l : List Bool) (v : Option Bool) (o : List Bool) :
    ∃ v', FF^[lpN l + 1] (some ⟨some .l1, v, st l o⟩) =
      some ⟨some .l2, v', st (lpX l) (List.replicate (lpN l) true ++ o)⟩ := by
  induction l generalizing v o with
  | nil => exact ⟨none, by simp [FF_some, TM2.step, fstStmt, TM2.stepAux, isT, lpN, lpX]⟩
  | cons b l ih =>
    cases b with
    | false => exact ⟨some false, by simp [FF_some, TM2.step, fstStmt, TM2.stepAux, isT, lpN, lpX]⟩
    | true =>
      obtain ⟨v', hv⟩ := ih (some true) (true :: o)
      refine ⟨v', ?_⟩
      have e : FF (some ⟨some .l1, v, st (true :: l) o⟩) =
          some ⟨some .l1, some true, st l (true :: o)⟩ := by
        simp [FF_some, TM2.step, fstStmt, TM2.stepAux, isT]
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply, e, hv,
        List.replicate_succ', List.append_assoc]
      rfl

theorem fst_clear (l : List Bool) (v : Option Bool) (o : List Bool) :
    FF^[l.length + 1] (some ⟨some .l2, v, st l o⟩) = some ⟨none, none, st [] o⟩ := by
  induction l generalizing v with
  | nil => simp [FF_some, TM2.step, fstStmt, TM2.stepAux, isS]
  | cons b l ih =>
    have e : FF (some ⟨some .l2, v, st (b :: l) o⟩) = some ⟨some .l2, some b, st l o⟩ := by
      simp [FF_some, TM2.step, fstStmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]

theorem lp_len' (y : List Bool) : lpN y + (lpX y).length ≤ y.length := LoopTM.lp_len y

def fstF (z : List Bool) : List Bool := List.replicate (lpN z) true

noncomputable def fstComputable : TM2ComputableInPolyTime strEnc strEnc fstF where
  tm := mk fstStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun l :=
    { steps := ((lpX l).length + 1) + (lpN l + 1)
      evals_in_steps := by
        obtain ⟨v', h1⟩ := fst_count l none []
        have h2 := fst_clear (lpX l) v' (List.replicate (lpN l) true ++ [])
        erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
        change FF^[((lpX l).length + 1) + (lpN l + 1)] (some ⟨some .l1, none, st l []⟩) =
          some ⟨none, none, st [] (fstF l)⟩
        rw [Function.iterate_add_apply, h1, h2, List.append_nil]; rfl
      steps_le_m := by
        have := lp_len' l
        simp [strEnc]; omega }

/-! ### `revTM`: `z ↦ reverse z`, and `revDropTM`: `1ⁿ 0 x ↦ reverse x` -/

def revStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o)
      (branch isS (push UK.out (fun s => s.getD false) (goto fun _ => .l1)) halt)
  | .l2 => halt

def rdStmt : UL → St
  | .l1 => pop UK.inp (fun _ o => o) (branch isT (goto fun _ => .l1) (goto fun _ => .l2))
  | .l2 => pop UK.inp (fun _ o => o)
      (branch isS (push UK.out (fun s => s.getD false) (goto fun _ => .l2)) halt)

abbrev FR : Option Cfg → Option Cfg := flip bind (TM2.step revStmt)
theorem FR_some (c : Cfg) : FR (some c) = TM2.step revStmt c := rfl
abbrev FD : Option Cfg → Option Cfg := flip bind (TM2.step rdStmt)
theorem FD_some (c : Cfg) : FD (some c) = TM2.step rdStmt c := rfl

theorem rev_loop (l : List Bool) (v : Option Bool) (o : List Bool) :
    FR^[l.length + 1] (some ⟨some .l1, v, st l o⟩) = some ⟨none, none, st [] (l.reverse ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [FR_some, TM2.step, revStmt, TM2.stepAux, isS]
  | cons b l ih =>
    have e : FR (some ⟨some .l1, v, st (b :: l) o⟩) = some ⟨some .l1, some b, st l (b :: o)⟩ := by
      simp [FR_some, TM2.step, revStmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]
    simp

theorem rd_copy (l : List Bool) (v : Option Bool) (o : List Bool) :
    FD^[l.length + 1] (some ⟨some .l2, v, st l o⟩) = some ⟨none, none, st [] (l.reverse ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [FD_some, TM2.step, rdStmt, TM2.stepAux, isS]
  | cons b l ih =>
    have e : FD (some ⟨some .l2, v, st (b :: l) o⟩) = some ⟨some .l2, some b, st l (b :: o)⟩ := by
      simp [FD_some, TM2.step, rdStmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]
    simp

theorem rd_skip (l : List Bool) (v : Option Bool) :
    ∃ v', FD^[lpN l + 1] (some ⟨some .l1, v, st l []⟩) = some ⟨some .l2, v', st (lpX l) []⟩ := by
  induction l generalizing v with
  | nil => exact ⟨none, by simp [FD_some, TM2.step, rdStmt, TM2.stepAux, isT, lpN, lpX]⟩
  | cons b l ih =>
    cases b with
    | false => exact ⟨some false, by simp [FD_some, TM2.step, rdStmt, TM2.stepAux, isT, lpN, lpX]⟩
    | true =>
      obtain ⟨v', hv⟩ := ih (some true)
      refine ⟨v', ?_⟩
      have e : FD (some ⟨some .l1, v, st (true :: l) []⟩) = some ⟨some .l1, some true, st l []⟩ := by
        simp [FD_some, TM2.step, rdStmt, TM2.stepAux, isT]
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply, e, hv]

noncomputable def revComputable : TM2ComputableInPolyTime strEnc strEnc List.reverse where
  tm := mk revStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun l :=
    { steps := l.length + 1
      evals_in_steps := by
        have h := rev_loop l none []
        erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
        rw [List.append_nil] at h
        exact h
      steps_le_m := by simp [strEnc] }

def revDropF (z : List Bool) : List Bool := (lpX z).reverse

noncomputable def revDropComputable : TM2ComputableInPolyTime strEnc strEnc revDropF where
  tm := mk rdStmt
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun l :=
    { steps := ((lpX l).length + 1) + (lpN l + 1)
      evals_in_steps := by
        obtain ⟨v', h1⟩ := rd_skip l none
        have h2 := rd_copy (lpX l) v' []
        erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
        change FD^[((lpX l).length + 1) + (lpN l + 1)] (some ⟨some .l1, none, st l []⟩) =
          some ⟨none, none, st [] (revDropF l)⟩
        rw [Function.iterate_add_apply, h1, h2, List.append_nil]; rfl
      steps_le_m := by
        have := lp_len' l
        simp [strEnc]; omega }

end SmallTM

/-! ### `nthTM`: `1ⁱ 0 x ↦ 1^{[x_i = 1]}` -/

namespace NthTM

open SmallTM

inductive NL | a | b | c
  deriving DecidableEq

instance : Fintype NL := ⟨{.a, .b, .c}, fun k => by cases k <;> simp⟩

abbrev St3 := TM2.Stmt SmallTM.Γ NL (Option Bool)
abbrev Cfg3 := TM2.Cfg SmallTM.Γ NL (Option Bool)

def stmt : NL → St3
  | .a => pop UK.inp (fun _ o => o)
      (branch isT (push UK.out (fun _ => true) (goto fun _ => .a)) (goto fun _ => .b))
  | .b => pop UK.out (fun _ o => o)
      (branch isS (pop UK.inp (fun s _ => s) (goto fun _ => .b))
        (pop UK.inp (fun _ o => o)
          (branch isT (push UK.out (fun _ => true) (goto fun _ => .c)) (goto fun _ => .c))))
  | .c => pop UK.inp (fun _ o => o) (branch isS (goto fun _ => .c) halt)

def tm : FinTM2 where
  K := UK
  k₀ := UK.inp
  k₁ := UK.out
  Γ := SmallTM.Γ
  Λ := NL
  main := .a
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := stmt

abbrev F : Option Cfg3 → Option Cfg3 := flip bind (TM2.step stmt)
theorem F_some (c : Cfg3) : F (some c) = TM2.step stmt c := rfl

theorem count (l : List Bool) (v : Option Bool) (o : List Bool) :
    ∃ v', F^[lpN l + 1] (some ⟨some .a, v, st l o⟩) =
      some ⟨some .b, v', st (lpX l) (List.replicate (lpN l) true ++ o)⟩ := by
  induction l generalizing v o with
  | nil => exact ⟨none, by simp [F_some, TM2.step, stmt, TM2.stepAux, isT, lpN, lpX]⟩
  | cons b l ih =>
    cases b with
    | false => exact ⟨some false, by simp [F_some, TM2.step, stmt, TM2.stepAux, isT, lpN, lpX]⟩
    | true =>
      obtain ⟨v', hv⟩ := ih (some true) (true :: o)
      refine ⟨v', ?_⟩
      have e : F (some ⟨some .a, v, st (true :: l) o⟩) =
          some ⟨some .a, some true, st l (true :: o)⟩ := by
        simp [F_some, TM2.step, stmt, TM2.stepAux, isT]
      rw [LoopTM.lpN_cons_true, LoopTM.lpX_cons_true, Function.iterate_succ_apply, e, hv,
        List.replicate_succ', List.append_assoc]
      rfl

theorem sync (n : ℕ) : ∀ (x : List Bool) (v : Option Bool),
    ∃ v', F^[n] (some ⟨some .b, v, st x (List.replicate n true)⟩) =
      some ⟨some .b, v', st (x.drop n) []⟩ := by
  induction n with
  | zero => intro x v; exact ⟨v, rfl⟩
  | succ n ih =>
    intro x v
    obtain ⟨v', hv⟩ := ih x.tail (some true)
    refine ⟨v', ?_⟩
    have e : F (some ⟨some .b, v, st x (List.replicate (n + 1) true)⟩) =
        some ⟨some .b, some true, st x.tail (List.replicate n true)⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS, List.replicate_succ]
    rw [Function.iterate_succ_apply, e, hv, List.drop_tail, Nat.add_comm]

def bit (x : List Bool) (i : ℕ) : ℕ := if x[i]? = some true then 1 else 0

theorem final (y : List Bool) (v : Option Bool) :
    ∃ v', F^[1] (some ⟨some .b, v, st y []⟩) =
      some ⟨some .c, v', st y.tail (List.replicate (bit y 0) true)⟩ := by
  cases y with
  | nil => exact ⟨none, by simp [F_some, TM2.step, stmt, TM2.stepAux, isS, isT, bit]⟩
  | cons b y =>
    cases b
    · exact ⟨some false, by simp [F_some, TM2.step, stmt, TM2.stepAux, isS, isT, bit]⟩
    · exact ⟨some true, by simp [F_some, TM2.step, stmt, TM2.stepAux, isS, isT, bit]⟩

theorem clear (l : List Bool) (v : Option Bool) (o : List Bool) :
    F^[l.length + 1] (some ⟨some .c, v, st l o⟩) = some ⟨none, none, st [] o⟩ := by
  induction l generalizing v with
  | nil => simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
  | cons b l ih =>
    have e : F (some ⟨some .c, v, st (b :: l) o⟩) = some ⟨some .c, some b, st l o⟩ := by
      simp [F_some, TM2.step, stmt, TM2.stepAux, isS]
    rw [List.length_cons, Function.iterate_succ_apply, e, ih]

def nthF (z : List Bool) : List Bool := List.replicate (bit (lpX z) (lpN z)) true

theorem bit_drop (x : List Bool) (i : ℕ) : bit (x.drop i) 0 = bit x i := by
  simp [bit]

noncomputable def nthComputable : TM2ComputableInPolyTime strEnc strEnc nthF where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 4
  outputsFun z :=
    { steps := ((((lpX z).drop (lpN z)).tail.length + 1 + 1) + lpN z) + (lpN z + 1)
      evals_in_steps := by
        obtain ⟨v1, h1⟩ := count z none []
        obtain ⟨v2, h2⟩ := sync (lpN z) (lpX z) v1
        obtain ⟨v3, h3⟩ := final ((lpX z).drop (lpN z)) v2
        have h4 := clear ((lpX z).drop (lpN z)).tail v3
          (List.replicate (bit ((lpX z).drop (lpN z)) 0) true)
        rw [List.append_nil] at h1
        erw [List.map_id, List.map_id, Option.map_some]
        have ei : initList tm z = (⟨some .a, none, st z []⟩ : Cfg3) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList tm (nthF z) = (⟨none, none, st [] (nthF z)⟩ : Cfg3) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [ei, eh]
        change F^[_] _ = _
        exact (iter_chain h1 (iter_chain h2 (iter_chain h3 h4))).trans (by rw [bit_drop]; rfl)
      steps_le_m := by
        have := LoopTM.lp_len z
        simp only [strEnc, List.length_map, List.length_tail, List.length_drop, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
        omega }

end NthTM

/-! ### Closure properties -/

/-- `f` is polynomial-time computable (bit strings to bit strings). -/
def PS (f : List Bool → List Bool) : Prop := Nonempty (TM2ComputableInPolyTime strEnc strEnc f)

/-- `u` is a polynomial-time unary quantity. -/
def PU (u : List Bool → ℕ) : Prop := PS (fun x => List.replicate (u x) true)

theorem PS.comp {f g : List Bool → List Bool} (hf : PS f) (hg : PS g) : PS (fun x => g (f x)) := by
  obtain ⟨hf⟩ := hf; obtain ⟨hg⟩ := hg; exact ⟨composeComputable hf hg⟩

theorem PS.append {f g : List Bool → List Bool} (hf : PS f) (hg : PS g) :
    PS (fun x => f x ++ g x) := by
  obtain ⟨hf⟩ := hf; obtain ⟨hg⟩ := hg; exact ⟨fanComputable hf hg⟩

theorem PS.const (c : List Bool) : PS (fun _ => c) := ⟨constListComputable c⟩

theorem PS.id : PS (fun x => x) := ⟨idComputableInPolyTime strEnc⟩

theorem PS.congr {f g : List Bool → List Bool} (hf : PS f) (h : ∀ x, f x = g x) : PS g :=
  computable_congr h hf

theorem PS.cons (b : Bool) {f : List Bool → List Bool} (hf : PS f) : PS (fun x => b :: f x) :=
  (PS.const [b]).append hf

theorem PU.const (n : ℕ) : PU (fun _ => n) := PS.const _

theorem PU.add {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) : PU (fun x => u x + v x) :=
  (hu.append hv).congr (fun x => by rw [List.replicate_add])

theorem PU.poly (P : Polynomial ℕ) : PU (fun x => P.eval x.length) := ⟨polyEvalComputable P⟩

theorem PU.polyOf (P : Polynomial ℕ) {u : List Bool → ℕ} (hu : PU u) :
    PU (fun x => P.eval (u x)) := polyOfUnary_computable u P hu

theorem PU.comp {u : List Bool → ℕ} (hu : PU u) {f : List Bool → List Bool} (hf : PS f) :
    PU (fun x => u (f x)) := hf.comp hu

theorem PU.mul {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) : PU (fun x => u x * v x) := by
  have hp : PS (fun x => pairU (u x) (v x)) := (hu.append (PS.cons false hv)).congr
    (fun x => by simp [pairU])
  have hh : PS (fun x => hornerF 0 (pairU (u x) (v x))) := hp.comp ⟨hornerComputable 0⟩
  exact (hh.comp ⟨SmallTM.sndComputable⟩).congr (fun x => by
    simp [hornerF_pairU, SmallTM.sndF, hM_pairU])

theorem PU.fst : PU lpN := ⟨SmallTM.fstComputable⟩

theorem PS.drop : PS lpX :=
  (PS.comp ⟨SmallTM.revDropComputable⟩ ⟨SmallTM.revComputable⟩).congr
    (fun x => by simp [SmallTM.revDropF])

theorem PU.nth : PU (fun z => NthTM.bit (lpX z) (lpN z)) := ⟨NthTM.nthComputable⟩

end PvnpReal
