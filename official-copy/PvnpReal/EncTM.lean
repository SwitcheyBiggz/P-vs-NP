/-
  PvnpReal.EncTM — a transducer machine `pairEnc → strEnc` that rewrites `x # w` symbol by
  symbol: `x.flatMap τ1 ++ τs ++ w.flatMap τ2`. Instances: the code `codeP x w`, and the two
  projections; with `decComputable` this gives polytime projections of `decP`.
-/
import PvnpReal.BruteEXP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

namespace EncTM

open TM2.Stmt

inductive EK | inp | sc | out
  deriving DecidableEq

instance : Fintype EK := ⟨{.inp, .sc, .out}, fun k => by cases k <;> simp⟩

inductive EL | a1 | a2 | mv
  deriving DecidableEq

instance : Fintype EL := ⟨{.a1, .a2, .mv}, fun k => by cases k <;> simp⟩

abbrev Γ : EK → Type
  | .inp => Option Bool
  | _ => Bool

abbrev σ := Option (Option Bool)
abbrev St := TM2.Stmt Γ EL σ
abbrev Cfg := TM2.Cfg Γ EL σ

def st (i : List (Option Bool)) (s o : List Bool) : ∀ k : EK, List (Γ k)
  | .inp => i
  | .sc => s
  | .out => o

@[simp] theorem upd_inp (i s o x) : Function.update (st i s o) .inp x = st x s o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_sc (i s o x) : Function.update (st i s o) .sc x = st i x o := by
  funext k; cases k <;> rfl
@[simp] theorem upd_out (i s o x) : Function.update (st i s o) .out x = st i s x := by
  funext k; cases k <;> rfl
@[simp] theorem st_inp (i s o) : st i s o .inp = i := rfl
@[simp] theorem st_sc (i s o) : st i s o .sc = s := rfl
@[simp] theorem st_out (i s o) : st i s o .out = o := rfl

def gB : σ → Bool
  | some (some b) => b
  | _ => false

def isSep : σ → Bool
  | some none => true
  | _ => false

def pushL : List Bool → St → St
  | [], k => k
  | b :: l, k => push .sc (fun _ => b) (pushL l k)

theorem stepAux_pushL (l : List Bool) (k : St) (v : σ) (i : List (Option Bool)) (s o : List Bool) :
    TM2.stepAux (pushL l k) v (st i s o) = TM2.stepAux k v (st i (l.reverse ++ s) o) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp [pushL, TM2.stepAux, ih]

variable (τ1 τ2 : Bool → List Bool) (τs : List Bool)

def stmt : EL → St
  | .a1 => pop .inp (fun _ o => o) (branch (fun s => s.isSome)
      (branch isSep (pushL τs (goto fun _ => .a2))
        (branch gB (pushL (τ1 true) (goto fun _ => .a1)) (pushL (τ1 false) (goto fun _ => .a1))))
      (goto fun _ => .mv))
  | .a2 => pop .inp (fun _ o => o) (branch (fun s => s.isSome)
      (branch isSep (goto fun _ => .a2)
        (branch gB (pushL (τ2 true) (goto fun _ => .a2)) (pushL (τ2 false) (goto fun _ => .a2))))
      (goto fun _ => .mv))
  | .mv => pop .sc (fun _ o => o.map some) (branch (fun s => s.isSome)
      (push .out (fun s => gB s) (goto fun _ => .mv)) halt)

def tm : FinTM2 where
  K := EK
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := EL
  main := .a1
  σ := σ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := stmt τ1 τ2 τs

local notation "F" => flip bind (TM2.step (stmt τ1 τ2 τs))

theorem run_mv (l o : List Bool) (v : σ) :
    F^[l.length + 1] (some ⟨some .mv, v, st [] l o⟩) = some ⟨none, none, st [] [] (l.reverse ++ o)⟩ := by
  induction l generalizing v o with
  | nil => simp [TM2.step, stmt, TM2.stepAux, flip]
  | cons b l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .mv, v, st [] (b :: l) o⟩) = some ⟨some .mv, some (some b), st [] l (b :: o)⟩ := by
      simp [TM2.step, stmt, TM2.stepAux, flip, gB]
    rw [e, ih]; simp

theorem run_1 (x : List Bool) (r : List (Option Bool)) (s : List Bool) (v : σ) :
    ∃ v', F^[x.length] (some ⟨some .a1, v, st (x.map some ++ r) s []⟩) =
      some ⟨some .a1, v', st r ((x.flatMap τ1).reverse ++ s) []⟩ := by
  induction x generalizing s v with
  | nil => exact ⟨v, by simp⟩
  | cons b x ih =>
    obtain ⟨v', h⟩ := ih ((τ1 b).reverse ++ s) (some (some b))
    refine ⟨v', ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .a1, v, st ((b :: x).map some ++ r) s []⟩) =
        some ⟨some .a1, some (some b), st (x.map some ++ r) ((τ1 b).reverse ++ s) []⟩ := by
      cases b <;> simp [TM2.step, stmt, TM2.stepAux, flip, gB, isSep, stepAux_pushL]
    rw [e, h]; simp

theorem run_2 (w : List Bool) (s : List Bool) (v : σ) :
    ∃ v', F^[w.length] (some ⟨some .a2, v, st (w.map some) s []⟩) =
      some ⟨some .a2, v', st [] ((w.flatMap τ2).reverse ++ s) []⟩ := by
  induction w generalizing s v with
  | nil => exact ⟨v, by simp⟩
  | cons b w ih =>
    obtain ⟨v', h⟩ := ih ((τ2 b).reverse ++ s) (some (some b))
    refine ⟨v', ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F (some ⟨some .a2, v, st ((b :: w).map some) s []⟩) =
        some ⟨some .a2, some (some b), st (w.map some) ((τ2 b).reverse ++ s) []⟩ := by
      cases b <;> simp [TM2.step, stmt, TM2.stepAux, flip, gB, isSep, stepAux_pushL]
    rw [e, h]; simp

def outF (p : List Bool × List Bool) : List Bool := p.1.flatMap τ1 ++ τs ++ p.2.flatMap τ2

theorem run_all (p : List Bool × List Bool) :
    F^[p.1.length + 1 + p.2.length + 1 + ((outF τ1 τ2 τs p).length + 1)]
      (some ⟨some .a1, none, st (pairEnc p) [] []⟩) =
      some ⟨none, none, st [] [] (outF τ1 τ2 τs p)⟩ := by
  obtain ⟨x, w⟩ := p
  obtain ⟨v1, h1⟩ := run_1 τ1 τ2 τs x (none :: w.map some) [] none
  have h2 : F^[1] (some ⟨some .a1, v1, st (none :: w.map some) ((x.flatMap τ1).reverse ++ []) []⟩) =
      some ⟨some .a2, some none, st (w.map some) (τs.reverse ++ (x.flatMap τ1).reverse) []⟩ := by
    simp [TM2.step, stmt, TM2.stepAux, flip, gB, isSep, stepAux_pushL]
  obtain ⟨v3, h3⟩ := run_2 τ1 τ2 τs w (τs.reverse ++ (x.flatMap τ1).reverse) (some none)
  have h4 : F^[1] (some ⟨some .a2, v3, st [] ((w.flatMap τ2).reverse ++
      (τs.reverse ++ (x.flatMap τ1).reverse)) []⟩) =
      some ⟨some .mv, none, st [] ((w.flatMap τ2).reverse ++
      (τs.reverse ++ (x.flatMap τ1).reverse)) []⟩ := by
    simp [TM2.step, stmt, TM2.stepAux, flip]
  have h5 := run_mv τ1 τ2 τs ((w.flatMap τ2).reverse ++ (τs.reverse ++ (x.flatMap τ1).reverse)) [] none
  have e := iter_chain (iter_chain (iter_chain (iter_chain h1 h2) h3) h4) h5
  have hl : ((w.flatMap τ2).reverse ++ (τs.reverse ++ (x.flatMap τ1).reverse)).length =
      (outF τ1 τ2 τs (x, w)).length := by simp [outF]; omega
  have hr : ((w.flatMap τ2).reverse ++ (τs.reverse ++ (x.flatMap τ1).reverse)).reverse ++ [] =
      outF τ1 τ2 τs (x, w) := by simp [outF]
  rw [hl, hr] at e
  simp only [pairEnc, List.nil_append] at e ⊢
  convert e using 2
  omega

/-- Length bound for the transducer output. -/
theorem outF_len (C : ℕ) (h1 : ∀ b, (τ1 b).length ≤ C) (h2 : ∀ b, (τ2 b).length ≤ C)
    (p : List Bool × List Bool) : (outF τ1 τ2 τs p).length ≤ C * (p.1.length + p.2.length) + τs.length := by
  have a : ∀ (τ : Bool → List Bool), (∀ b, (τ b).length ≤ C) → ∀ l : List Bool,
      (l.flatMap τ).length ≤ C * l.length := by
    intro τ hτ l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := hτ b; nlinarith
  have := a τ1 h1 p.1; have := a τ2 h2 p.2
  simp only [outF, List.length_append]; nlinarith

end EncTM

/-- **The transducer**: `x # w ↦ x.flatMap τ1 ++ τs ++ w.flatMap τ2`. -/
noncomputable def transComputable (τ1 τ2 : Bool → List Bool) (τs : List Bool) (C : ℕ)
    (h1 : ∀ b, (τ1 b).length ≤ C) (h2 : ∀ b, (τ2 b).length ≤ C) :
    TM2ComputableInPolyTime pairEnc strEnc (EncTM.outF τ1 τ2 τs) where
  tm := EncTM.tm τ1 τ2 τs
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C (C + 2) * Polynomial.X + Polynomial.C (τs.length + 3)
  outputsFun p :=
    { steps := p.1.length + 1 + p.2.length + 1 + ((EncTM.outF τ1 τ2 τs p).length + 1)
      evals_in_steps := by
        have := EncTM.run_all τ1 τ2 τs p
        have ei : initList (EncTM.tm τ1 τ2 τs) (pairEnc p) =
            (⟨some .a1, none, EncTM.st (pairEnc p) [] []⟩ : EncTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList (EncTM.tm τ1 τ2 τs) (EncTM.outF τ1 τ2 τs p) =
            (⟨none, none, EncTM.st [] [] (EncTM.outF τ1 τ2 τs p)⟩ : EncTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact this
      steps_le_m := by
        have := EncTM.outF_len τ1 τ2 τs C h1 h2 p
        simp only [pairEnc, strEnc, List.length_append, List.length_map, List.length_cons,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        nlinarith }

theorem trans_ne {f : List Bool × List Bool → List Bool} (τ1 τ2 : Bool → List Bool) (τs : List Bool)
    (C : ℕ) (h1 : ∀ b, (τ1 b).length ≤ C) (h2 : ∀ b, (τ2 b).length ≤ C)
    (e : ∀ p, EncTM.outF τ1 τ2 τs p = f p) : Nonempty (TM2ComputableInPolyTime pairEnc strEnc f) := by
  have : EncTM.outF τ1 τ2 τs = f := funext e
  exact this ▸ ⟨transComputable τ1 τ2 τs C h1 h2⟩

theorem codeL_flatMap (a : List Bool) : a.flatMap (fun c => codeL [c]) = codeL a := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [List.flatMap_cons, ih]; simp [codeL]

/-- `x # w ↦ codeP x w`. -/
theorem encP : Nonempty (TM2ComputableInPolyTime pairEnc strEnc (fun p => codeP p.1 p.2)) :=
  trans_ne (fun c => codeL [c]) (fun c => codeL [c]) [false] 3
    (fun b => by cases b <;> simp [codeL]) (fun b => by cases b <;> simp [codeL])
    (fun p => by simp [EncTM.outF, codeP, codeL_flatMap])

/-- `x # w ↦ x`. -/
theorem encFst : Nonempty (TM2ComputableInPolyTime pairEnc strEnc (fun p => p.1)) :=
  trans_ne (fun c => [c]) (fun _ => []) [] 1 (fun b => by simp) (fun b => by simp)
    (fun p => by simp [EncTM.outF])

/-- `x # w ↦ w`. -/
theorem encSnd : Nonempty (TM2ComputableInPolyTime pairEnc strEnc (fun p => p.2)) :=
  trans_ne (fun _ => []) (fun c => [c]) [] 1 (fun b => by simp) (fun b => by simp)
    (fun p => by simp [EncTM.outF])

/-- Projections of the decoder are polytime. -/
theorem PS.fstP : PS (fun s => (decP s).1) := by
  obtain ⟨h⟩ := encFst; exact ⟨composeGen decComputable h⟩

theorem PS.sndP : PS (fun s => (decP s).2) := by
  obtain ⟨h⟩ := encSnd; exact ⟨composeGen decComputable h⟩

theorem PS.codePF {a b : List Bool → List Bool} (ha : PS a) (hb : PS b) :
    PS (fun s => codeP (a s) (b s)) :=
  PS.append (PS.codeL ha) (PS.cons false (PS.codeL hb))

end PvnpReal
