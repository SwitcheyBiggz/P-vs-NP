/-
  PvnpReal.SatMachine — a real Mathlib `FinTM2` that computes `verify` (from
  `PvnpReal.SatVerify`) on input `x # w` in polynomial time, hence **SAT ∈ NP**.

  Stacks: `inp` (input `x # w`), `x`, `w` (the two parts, restored to reading order),
  `t`, `u` (scratch), `out` (the answer bit).
  Phases: `p1`–`p4` split and reorder the input; `mF/mC/mS/mV` are the four parsing modes of
  `run`; looking up variable `c` shifts `c` bits of `w` onto `t` and `rst` shifts them back;
  `clT/clX/clW` empty the work stacks; `fin` writes the answer.
-/
import PvnpReal.SatVerify
import PvnpReal.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

namespace SatTM

inductive SK | inp | x | w | t | u | out
  deriving DecidableEq

instance : Fintype SK :=
  ⟨{.inp, .x, .w, .t, .u, .out}, fun k => by cases k <;> simp⟩

abbrev Γ : SK → Type
  | .inp => Option Bool
  | .x => Bool
  | .w => Bool
  | .t => Bool
  | .u => Bool
  | .out => Bool

inductive SL | p1 | p2 | p3 | p4 | mF | mC | mS | mV | rst | clT | clX | clW | fin
  deriving DecidableEq

instance : Fintype SL :=
  ⟨{.p1, .p2, .p3, .p4, .mF, .mC, .mS, .mV, .rst, .clT, .clX, .clW, .fin},
    fun k => by cases k <;> simp⟩

/-- Internal state: `(fok, cok, ng, res, sto)`. -/
abbrev Sσ := Bool × Bool × Bool × Bool × Option Bool

def init : Sσ := (true, false, false, false, none)

def setSto (s : Sσ) (o : Option Bool) : Sσ := (s.1, s.2.1, s.2.2.1, s.2.2.2.1, o)
def setFok (s : Sσ) (b : Bool) : Sσ := (b, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2)
def setCok (s : Sσ) (b : Bool) : Sσ := (s.1, b, s.2.2.1, s.2.2.2.1, s.2.2.2.2)
def setNg (s : Sσ) (b : Bool) : Sσ := (s.1, s.2.1, b, s.2.2.2.1, s.2.2.2.2)
def setRes (s : Sσ) (b : Bool) : Sσ := (s.1, s.2.1, s.2.2.1, b, s.2.2.2.2)

def isT : Option Bool → Bool
  | some true => true
  | _ => false

def isF : Option Bool → Bool
  | some false => true
  | _ => false

abbrev Stmt := TM2.Stmt Γ SL Sσ

def gt (l : SL) : Stmt := goto fun _ => l
def failS : Stmt := load (fun s => setRes s false) (gt .clT)

def sp1 : Stmt :=
  pop .inp (fun s o => setSto s (o.bind id))
    (branch (fun s => s.2.2.2.2.isSome) (push .t (fun s => s.2.2.2.2.getD false) (gt .p1))
      (gt .p2))
def sp2 : Stmt :=
  pop .inp (fun s o => setSto s (o.bind id))
    (branch (fun s => s.2.2.2.2.isSome) (push .u (fun s => s.2.2.2.2.getD false) (gt .p2))
      (gt .p3))
def sp3 : Stmt :=
  pop .t (fun s o => setSto s o)
    (branch (fun s => s.2.2.2.2.isSome) (push .x (fun s => s.2.2.2.2.getD false) (gt .p3))
      (gt .p4))
def sp4 : Stmt :=
  pop .u (fun s o => setSto s o)
    (branch (fun s => s.2.2.2.2.isSome) (push .w (fun s => s.2.2.2.2.getD false) (gt .p4))
      (gt .mF))
def smF : Stmt :=
  pop .x (fun s o => setSto s o)
    (branch (fun s => isT s.2.2.2.2) (load (fun s => setCok s false) (gt .mC))
      (branch (fun s => isF s.2.2.2.2)
        (peek .x (fun s o => setRes s (s.1 && o.isNone)) (gt .clT))
        failS))
def smC : Stmt :=
  pop .x (fun s o => setSto s o)
    (branch (fun s => isF s.2.2.2.2) (load (fun s => setFok s (s.1 && s.2.1)) (gt .mF))
      (branch (fun s => isT s.2.2.2.2) (gt .mS) failS))
def smS : Stmt :=
  pop .x (fun s o => setSto s o)
    (branch (fun s => s.2.2.2.2.isSome) (load (fun s => setNg s (s.2.2.2.2.getD false)) (gt .mV))
      failS)
def smV : Stmt :=
  pop .x (fun s o => setSto s o)
    (branch (fun s => isT s.2.2.2.2)
      (pop .w (fun s o => setSto s o)
        (branch (fun s => s.2.2.2.2.isSome) (push .t (fun s => s.2.2.2.2.getD false) (gt .mV))
          (gt .mV)))
      (branch (fun s => isF s.2.2.2.2)
        (peek .w (fun s o => setCok s (s.2.1 || (s.2.2.1 != o.getD false))) (gt .rst))
        failS))
def srst : Stmt :=
  pop .t (fun s o => setSto s o)
    (branch (fun s => s.2.2.2.2.isSome) (push .w (fun s => s.2.2.2.2.getD false) (gt .rst))
      (gt .mC))
def sclT : Stmt :=
  pop .t (fun s o => setSto s o) (branch (fun s => s.2.2.2.2.isSome) (gt .clT) (gt .clX))
def sclX : Stmt :=
  pop .x (fun s o => setSto s o) (branch (fun s => s.2.2.2.2.isSome) (gt .clX) (gt .clW))
def sclW : Stmt :=
  pop .w (fun s o => setSto s o) (branch (fun s => s.2.2.2.2.isSome) (gt .clW) (gt .fin))
def sfin : Stmt :=
  push .out (fun s => s.2.2.2.1) (load (fun _ => init) halt)

def Sm : SL → Stmt
  | .p1 => sp1 | .p2 => sp2 | .p3 => sp3 | .p4 => sp4
  | .mF => smF | .mC => smC | .mS => smS | .mV => smV | .rst => srst
  | .clT => sclT | .clX => sclX | .clW => sclW | .fin => sfin

/-- The SAT verifier machine. -/
def satTM : FinTM2 where
  K := SK
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := SL
  main := .p1
  σ := Sσ
  initialState := init
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := Sm

abbrev Cfg := TM2.Cfg Γ SL Sσ

def mk (I : List (Option Bool)) (X W T U O : List Bool) : ∀ k, List (Γ k)
  | .inp => I
  | .x => X
  | .w => W
  | .t => T
  | .u => U
  | .out => O

section upd
variable (I : List (Option Bool)) (X W T U O : List Bool)

theorem upd_inp (I' : List (Option Bool)) :
    Function.update (mk I X W T U O) .inp I' = mk I' X W T U O := by
  funext j; cases j <;> first | (rw [Function.update_self]; rfl) |
    (rw [Function.update_of_ne (by decide)]; rfl)
theorem upd_x (X' : List Bool) :
    Function.update (mk I X W T U O) .x X' = mk I X' W T U O := by
  funext j; cases j <;> first | (rw [Function.update_self]; rfl) |
    (rw [Function.update_of_ne (by decide)]; rfl)
theorem upd_w (W' : List Bool) :
    Function.update (mk I X W T U O) .w W' = mk I X W' T U O := by
  funext j; cases j <;> first | (rw [Function.update_self]; rfl) |
    (rw [Function.update_of_ne (by decide)]; rfl)
theorem upd_t (T' : List Bool) :
    Function.update (mk I X W T U O) .t T' = mk I X W T' U O := by
  funext j; cases j <;> first | (rw [Function.update_self]; rfl) |
    (rw [Function.update_of_ne (by decide)]; rfl)
theorem upd_u (U' : List Bool) :
    Function.update (mk I X W T U O) .u U' = mk I X W T U' O := by
  funext j; cases j <;> first | (rw [Function.update_self]; rfl) |
    (rw [Function.update_of_ne (by decide)]; rfl)
theorem upd_out (O' : List Bool) :
    Function.update (mk I X W T U O) .out O' = mk I X W T U O' := by
  funext j; cases j <;> first | (rw [Function.update_self]; rfl) |
    (rw [Function.update_of_ne (by decide)]; rfl)
end upd


/-- Uniform tactic for one machine step. -/
macro "vstep" : tactic => `(tactic| (
  simp only [TM2.step, Sm, TM2.stepAux, sp1, sp2, sp3, sp4, smF, smC, smS, smV, srst, sclT,
    sclX, sclW, sfin, gt, failS, mk, List.head?_cons, List.head?_nil, List.tail_cons,
    List.tail_nil, isT, isF, Option.isSome_some, Option.isSome_none, Option.getD_some,
    Option.getD_none, Option.isNone_some, Option.isNone_none, Option.bind_some,
    Option.bind_none, id, Bool.cond_true, Bool.cond_false, setSto, setCok, setFok, setNg,
    setRes, upd_inp, upd_x, upd_w, upd_t, upd_u, upd_out, Option.some.injEq]))

section steps
variable (s : Sσ) (I : List (Option Bool)) (X W T U O : List Bool) (b : Bool)

local notation "step" => TM2.step Sm

theorem p1_bit : step ⟨some .p1, s, mk (some b :: I) X W T U O⟩ =
    some ⟨some .p1, setSto s (some b), mk I X W (b :: T) U O⟩ := by vstep
theorem p1_sep : step ⟨some .p1, s, mk (none :: I) X W T U O⟩ =
    some ⟨some .p2, setSto s none, mk I X W T U O⟩ := by vstep
theorem p2_bit : step ⟨some .p2, s, mk (some b :: I) X W T U O⟩ =
    some ⟨some .p2, setSto s (some b), mk I X W T (b :: U) O⟩ := by vstep
theorem p2_nil : step ⟨some .p2, s, mk [] X W T U O⟩ =
    some ⟨some .p3, setSto s none, mk [] X W T U O⟩ := by vstep
theorem p3_cons : step ⟨some .p3, s, mk I X W (b :: T) U O⟩ =
    some ⟨some .p3, setSto s (some b), mk I (b :: X) W T U O⟩ := by vstep
theorem p3_nil : step ⟨some .p3, s, mk I X W [] U O⟩ =
    some ⟨some .p4, setSto s none, mk I X W [] U O⟩ := by vstep
theorem p4_cons : step ⟨some .p4, s, mk I X W T (b :: U) O⟩ =
    some ⟨some .p4, setSto s (some b), mk I X (b :: W) T U O⟩ := by vstep
theorem p4_nil : step ⟨some .p4, s, mk I X W T [] O⟩ =
    some ⟨some .mF, setSto s none, mk I X W T [] O⟩ := by vstep
theorem mF_true : step ⟨some .mF, s, mk I (true :: X) W T U O⟩ =
    some ⟨some .mC, setCok (setSto s (some true)) false, mk I X W T U O⟩ := by vstep
theorem mF_false : step ⟨some .mF, s, mk I (false :: X) W T U O⟩ =
    some ⟨some .clT, setRes (setSto s (some false)) (s.1 && X.head?.isNone),
      mk I X W T U O⟩ := by vstep
theorem mF_nil : step ⟨some .mF, s, mk I [] W T U O⟩ =
    some ⟨some .clT, setRes (setSto s none) false, mk I [] W T U O⟩ := by vstep
theorem mC_false : step ⟨some .mC, s, mk I (false :: X) W T U O⟩ =
    some ⟨some .mF, setFok (setSto s (some false)) (s.1 && s.2.1), mk I X W T U O⟩ := by vstep
theorem mC_true : step ⟨some .mC, s, mk I (true :: X) W T U O⟩ =
    some ⟨some .mS, setSto s (some true), mk I X W T U O⟩ := by vstep
theorem mC_nil : step ⟨some .mC, s, mk I [] W T U O⟩ =
    some ⟨some .clT, setRes (setSto s none) false, mk I [] W T U O⟩ := by vstep
theorem mS_cons : step ⟨some .mS, s, mk I (b :: X) W T U O⟩ =
    some ⟨some .mV, setNg (setSto s (some b)) b, mk I X W T U O⟩ := by vstep
theorem mS_nil : step ⟨some .mS, s, mk I [] W T U O⟩ =
    some ⟨some .clT, setRes (setSto s none) false, mk I [] W T U O⟩ := by vstep
theorem mV_true_some : step ⟨some .mV, s, mk I (true :: X) (b :: W) T U O⟩ =
    some ⟨some .mV, setSto s (some b), mk I X W (b :: T) U O⟩ := by vstep
theorem mV_true_none : step ⟨some .mV, s, mk I (true :: X) [] T U O⟩ =
    some ⟨some .mV, setSto s none, mk I X [] T U O⟩ := by vstep
theorem mV_false : step ⟨some .mV, s, mk I (false :: X) W T U O⟩ =
    some ⟨some .rst, setCok (setSto s (some false)) (s.2.1 || (s.2.2.1 != W.head?.getD false)),
      mk I X W T U O⟩ := by vstep
theorem mV_nil : step ⟨some .mV, s, mk I [] W T U O⟩ =
    some ⟨some .clT, setRes (setSto s none) false, mk I [] W T U O⟩ := by vstep
theorem rst_cons : step ⟨some .rst, s, mk I X W (b :: T) U O⟩ =
    some ⟨some .rst, setSto s (some b), mk I X (b :: W) T U O⟩ := by vstep
theorem rst_nil : step ⟨some .rst, s, mk I X W [] U O⟩ =
    some ⟨some .mC, setSto s none, mk I X W [] U O⟩ := by vstep
theorem clT_cons : step ⟨some .clT, s, mk I X W (b :: T) U O⟩ =
    some ⟨some .clT, setSto s (some b), mk I X W T U O⟩ := by vstep
theorem clT_nil : step ⟨some .clT, s, mk I X W [] U O⟩ =
    some ⟨some .clX, setSto s none, mk I X W [] U O⟩ := by vstep
theorem clX_cons : step ⟨some .clX, s, mk I (b :: X) W T U O⟩ =
    some ⟨some .clX, setSto s (some b), mk I X W T U O⟩ := by vstep
theorem clX_nil : step ⟨some .clX, s, mk I [] W T U O⟩ =
    some ⟨some .clW, setSto s none, mk I [] W T U O⟩ := by vstep
theorem clW_cons : step ⟨some .clW, s, mk I X (b :: W) T U O⟩ =
    some ⟨some .clW, setSto s (some b), mk I X W T U O⟩ := by vstep
theorem clW_nil : step ⟨some .clW, s, mk I X [] T U O⟩ =
    some ⟨some .fin, setSto s none, mk I X [] T U O⟩ := by vstep
theorem fin_step : step ⟨some .fin, s, mk I X W T U O⟩ =
    some ⟨none, init, mk I X W T U (s.2.2.2.1 :: O)⟩ := by vstep

end steps

/-! ### Multi-step reachability with a step budget -/

/-- `Reach a b n`: from `a` the machine reaches `b` in at most `n` steps. -/
def Reach (a b : Cfg) (n : ℕ) : Prop :=
  ∃ m ≤ n, (flip bind (TM2.step Sm))^[m] (some a) = some b

theorem Reach.refl (a : Cfg) : Reach a a 0 := ⟨0, le_rfl, rfl⟩

theorem Reach.mono {a b : Cfg} {n n' : ℕ} (h : Reach a b n) (hn : n ≤ n') : Reach a b n' := by
  obtain ⟨m, hm, he⟩ := h; exact ⟨m, hm.trans hn, he⟩

theorem Reach.step {a b c : Cfg} {n : ℕ} (h : TM2.step Sm a = some b) (h2 : Reach b c n) :
    Reach a c (n + 1) := by
  obtain ⟨m, hm, he⟩ := h2
  refine ⟨m + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply]
  show (flip bind (TM2.step Sm))^[m] (TM2.step Sm a) = _
  rw [h]; exact he

theorem Reach.trans {a b c : Cfg} {n m : ℕ} (h1 : Reach a b n) (h2 : Reach b c m) :
    Reach a c (n + m) := by
  obtain ⟨m1, hm1, he1⟩ := h1
  obtain ⟨m2, hm2, he2⟩ := h2
  exact ⟨m2 + m1, by omega, by rw [Function.iterate_add_apply, he1, he2]⟩

theorem Reach.step' {a b c : Cfg} {n N : ℕ} (h : TM2.step Sm a = some b) (h2 : Reach b c n)
    (hN : n + 1 ≤ N) : Reach a c N :=
  (Reach.step h h2).mono hN

/-! ### Loops -/

theorem loop_p1 (x : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (X W T U O : List Bool),
    Reach ⟨some .p1, s, mk (x.map some ++ none :: I) X W T U O⟩
      ⟨some .p2, setSto s none, mk I X W (x.reverse ++ T) U O⟩ (x.length + 1) := by
  induction x with
  | nil => intro s I X W T U O; exact Reach.step (p1_sep ..) (Reach.refl _)
  | cons b x ih =>
    intro s I X W T U O
    rw [List.reverse_cons, List.append_assoc]
    exact Reach.step (p1_bit ..) (ih _ _ _ _ _ _ _)

theorem loop_p2 (w : List Bool) : ∀ (s : Sσ) (X W T U O : List Bool),
    Reach ⟨some .p2, s, mk (w.map some) X W T U O⟩
      ⟨some .p3, setSto s none, mk [] X W T (w.reverse ++ U) O⟩ (w.length + 1) := by
  induction w with
  | nil => intro s X W T U O; exact Reach.step (p2_nil ..) (Reach.refl _)
  | cons b w ih =>
    intro s X W T U O
    rw [List.reverse_cons, List.append_assoc]
    exact Reach.step (p2_bit ..) (ih _ _ _ _ _ _)

theorem loop_p3 (T : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (X W U O : List Bool),
    Reach ⟨some .p3, s, mk I X W T U O⟩
      ⟨some .p4, setSto s none, mk I (T.reverse ++ X) W [] U O⟩ (T.length + 1) := by
  induction T with
  | nil => intro s I X W U O; exact Reach.step (p3_nil ..) (Reach.refl _)
  | cons b T ih =>
    intro s I X W U O
    rw [List.reverse_cons, List.append_assoc]
    exact Reach.step (p3_cons ..) (ih _ _ _ _ _ _)

theorem loop_p4 (U : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (X W T O : List Bool),
    Reach ⟨some .p4, s, mk I X W T U O⟩
      ⟨some .mF, setSto s none, mk I X (U.reverse ++ W) T [] O⟩ (U.length + 1) := by
  induction U with
  | nil => intro s I X W T O; exact Reach.step (p4_nil ..) (Reach.refl _)
  | cons b U ih =>
    intro s I X W T O
    rw [List.reverse_cons, List.append_assoc]
    exact Reach.step (p4_cons ..) (ih _ _ _ _ _ _)

theorem loop_rst (T : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (X W U O : List Bool),
    Reach ⟨some .rst, s, mk I X W T U O⟩
      ⟨some .mC, setSto s none, mk I X (T.reverse ++ W) [] U O⟩ (T.length + 1) := by
  induction T with
  | nil => intro s I X W U O; exact Reach.step (rst_nil ..) (Reach.refl _)
  | cons b T ih =>
    intro s I X W U O
    rw [List.reverse_cons, List.append_assoc]
    exact Reach.step (rst_cons ..) (ih _ _ _ _ _ _)

theorem loop_clT (T : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (X W U O : List Bool),
    Reach ⟨some .clT, s, mk I X W T U O⟩
      ⟨some .clX, setSto s none, mk I X W [] U O⟩ (T.length + 1) := by
  induction T with
  | nil => intro s I X W U O; exact Reach.step (clT_nil ..) (Reach.refl _)
  | cons b T ih => intro s I X W U O; exact Reach.step (clT_cons ..) (ih _ _ _ _ _ _)

theorem loop_clX (X : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (W T U O : List Bool),
    Reach ⟨some .clX, s, mk I X W T U O⟩
      ⟨some .clW, setSto s none, mk I [] W T U O⟩ (X.length + 1) := by
  induction X with
  | nil => intro s I W T U O; exact Reach.step (clX_nil ..) (Reach.refl _)
  | cons b X ih => intro s I W T U O; exact Reach.step (clX_cons ..) (ih _ _ _ _ _ _)

theorem loop_clW (W : List Bool) : ∀ (s : Sσ) (I : List (Option Bool)) (X T U O : List Bool),
    Reach ⟨some .clW, s, mk I X W T U O⟩
      ⟨some .fin, setSto s none, mk I X [] T U O⟩ (W.length + 1) := by
  induction W with
  | nil => intro s I X T U O; exact Reach.step (clW_nil ..) (Reach.refl _)
  | cons b W ih => intro s I X T U O; exact Reach.step (clW_cons ..) (ih _ _ _ _ _ _)

/-- The halting configuration with answer `r`. -/
def final (r : Bool) : Cfg := ⟨none, init, mk [] [] [] [] [] [r]⟩

theorem cleanup (s : Sσ) (X W T : List Bool) :
    Reach ⟨some .clT, s, mk [] X W T [] []⟩ (final s.2.2.2.1)
      (T.length + X.length + W.length + 4) := by
  have h := ((loop_clT T s [] X W [] []).trans (loop_clX X _ [] W [] [] [])).trans
    (loop_clW W _ [] [] [] [] [])
  exact (h.trans (Reach.step (fin_step ..) (Reach.refl _))).mono (by omega)

/-! ### The parsing phase simulates `run` -/

/-- Step budget for the parsing phase on `n` remaining input bits. -/
def B (w : List Bool) (n : ℕ) : ℕ := n * (w.length + 3) + 2 * w.length + 6

theorem B_succ (w : List Bool) (n : ℕ) : B w (n + 1) = B w n + (w.length + 3) := by
  unfold B; ring

theorem B_ge (w : List Bool) (n : ℕ) : n + 2 * w.length + 6 ≤ B w n := by
  unfold B
  have : n ≤ n * (w.length + 3) := Nat.le_mul_of_pos_right n (by omega)
  omega

theorem head?_isNone_eq (r : List Bool) : r.head?.isNone = r.isEmpty := by cases r <;> rfl

theorem asg_eq (w : List Bool) (c : ℕ) : asg w c = (w.drop c).head?.getD false := by
  simp [asg, List.head?_drop, List.getD_eq_getElem?_getD]

theorem eval_sim (w : List Bool) (X : List Bool) :
    ∀ (fok cok ng res : Bool) (sto : Option Bool),
      Reach ⟨some .mF, (fok, cok, ng, res, sto), mk [] X w [] [] []⟩
          (final (run w .F fok false false 0 X)) (B w X.length) ∧
      Reach ⟨some .mC, (fok, cok, ng, res, sto), mk [] X w [] [] []⟩
          (final (run w .C fok cok false 0 X)) (B w X.length) ∧
      Reach ⟨some .mS, (fok, cok, ng, res, sto), mk [] X w [] [] []⟩
          (final (run w .S fok cok false 0 X)) (B w X.length) ∧
      ∀ c : ℕ, Reach ⟨some .mV, (fok, cok, ng, res, sto),
          mk [] X (w.drop c) (w.take c).reverse [] []⟩
          (final (run w .V fok cok ng c X)) (B w X.length) := by
  have hB0 := B_ge w 0
  induction X with
  | nil =>
    intro fok cok ng res sto
    refine ⟨?_, ?_, ?_, fun c => ?_⟩
    · exact Reach.step' (mF_nil ..) (cleanup _ _ _ _) (by simp; omega)
    · exact Reach.step' (mC_nil ..) (cleanup _ _ _ _) (by simp; omega)
    · exact Reach.step' (mS_nil ..) (cleanup _ _ _ _) (by simp; omega)
    · refine Reach.step' (mV_nil ..) (cleanup _ _ _ _) ?_
      simp only [List.length_reverse, List.length_take, List.length_drop, List.length_nil]
      omega
  | cons b r ih =>
    intro fok cok ng res sto
    have hBs := B_succ w r.length
    have hBg := B_ge w r.length
    simp only [List.length_cons]
    refine ⟨?_, ?_, ?_, fun c => ?_⟩
    · cases b
      · have e : run w .F fok false false 0 (false :: r) = (fok && r.head?.isNone) := by
          rw [head?_isNone_eq]; rfl
        rw [e]
        exact Reach.step' (mF_false ..) (cleanup _ _ _ _) (by simp; omega)
      · exact Reach.step' (mF_true ..) (ih fok false ng res (some true)).2.1 (by omega)
    · cases b
      · exact Reach.step' (mC_false ..) (ih (fok && cok) cok ng res (some false)).1 (by omega)
      · exact Reach.step' (mC_true ..) (ih fok cok ng res (some true)).2.2.1 (by omega)
    · have h := (ih fok cok b res (some b)).2.2.2 0
      simp only [List.drop_zero, List.take_zero, List.reverse_nil] at h
      exact Reach.step' (mS_cons ..) h (by omega)
    · cases b
      · -- end of the variable index: look up, then restore `w`
        have hr := loop_rst (w.take c).reverse
          (fok, cok || (ng != (w.drop c).head?.getD false), ng, res, some false) []
          r (w.drop c) [] []
        rw [List.reverse_reverse, List.take_append_drop] at hr
        have hc := (ih fok (cok || (ng != (w.drop c).head?.getD false)) ng res none).2.1
        have e : run w .V fok cok ng c (false :: r) =
            run w .C fok (cok || (ng != (w.drop c).head?.getD false)) false 0 r := by
          rw [← asg_eq]; rfl
        rw [e]
        refine Reach.step' (mV_false ..) (hr.trans hc) ?_
        simp only [List.length_reverse, List.length_take]
        omega
      · -- one more unary digit: shift one bit of `w` onto `t`
        have e : run w .V fok cok ng c (true :: r) = run w .V fok cok ng (c + 1) r := rfl
        rw [e]
        have h := (ih fok cok ng res none).2.2.2 (c + 1)
        cases hd : w.drop c with
        | nil =>
          have h1 : w.drop (c + 1) = [] := by rw [← List.tail_drop, hd]; rfl
          have h2 : w.take (c + 1) = w.take c := by
            rw [List.take_add_one, ← List.head?_drop, hd]; simp
          rw [h1, h2] at h
          exact Reach.step' (mV_true_none ..) h (by omega)
        | cons b' D =>
          have h1 : w.drop (c + 1) = D := by rw [← List.tail_drop, hd]; rfl
          have h2 : (w.take (c + 1)).reverse = b' :: (w.take c).reverse := by
            rw [List.take_add_one, ← List.head?_drop, hd]; simp
          have h' := (ih fok cok ng res (some b')).2.2.2 (c + 1)
          rw [h1, h2] at h'
          exact Reach.step' (mV_true_some ..) h' (by omega)

/-! ### The whole run on `x # w` -/

theorem total (x w : List Bool) :
    Reach ⟨some .p1, init, mk (pairEnc (x, w)) [] [] [] [] []⟩ (final (verify x w))
      (2 * x.length + 2 * w.length + 4 + B w x.length) := by
  have h1 := loop_p1 x init (w.map some) [] [] [] [] []
  have h2 := loop_p2 w (setSto init none) [] [] (x.reverse ++ []) [] []
  have h3 := loop_p3 (x.reverse ++ []) (setSto (setSto init none) none) [] [] []
    (w.reverse ++ []) []
  have h4 := loop_p4 (w.reverse ++ []) (setSto (setSto (setSto init none) none) none) []
    ((x.reverse ++ []).reverse ++ []) [] [] []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2 h3 h4
  have h5 := (eval_sim w x true false false false none).1
  have h := (((h1.trans h2).trans h3).trans h4).trans h5
  exact h.mono (by omega)

theorem initList_sat (l : List (Option Bool)) :
    initList satTM (List.map (Equiv.refl (Option Bool)).invFun l) =
      ⟨some .p1, init, mk l [] [] [] [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k
  · exact List.map_id l
  all_goals rfl

theorem haltList_sat (r : Bool) :
    haltList satTM (List.map (Equiv.refl Bool).invFun (encodeBool r)) = final r := by
  simp only [haltList, final]
  congr 1
  funext k
  cases k <;> rfl

end SatTM

open SatTM in
/-- The SAT verifier is a polynomial-time Turing machine (time `n² + 6n + 10`). -/
noncomputable def satVerifierComputable :
    TM2ComputableInPolyTime pairEnc encodeBool (fun p => verify p.1 p.2) where
  tm := satTM
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X * Polynomial.X + 6 * Polynomial.X + 10
  outputsFun p := by
    obtain ⟨x, w⟩ := p
    have h := total x w
    refine
      { steps := Classical.choose h
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have e := (Classical.choose_spec h).2
      erw [initList_sat, Option.map_some, haltList_sat]
      exact e
    · have hle := (Classical.choose_spec h).1
      simp only [pairEnc, List.length_append, List.length_map, List.length_cons,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      unfold B at hle
      refine hle.trans ?_
      generalize x.length = a
      generalize w.length = b
      nlinarith [Nat.zero_le (a * b), Nat.zero_le (a * a), Nat.zero_le (b * b)]

/-- **SAT ∈ NP**, with a real polynomial-time Turing-machine verifier. -/
theorem SAT_in_NP : InNP SATLang := by
  refine ⟨fun p => verify p.1 p.2, Polynomial.X, ⟨satVerifierComputable⟩, fun x => ?_⟩
  rw [SATLang_iff_verify]
  simp

end PvnpReal
