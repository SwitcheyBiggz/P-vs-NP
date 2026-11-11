/-
  PvnpReal.Stream — printing CNF encodings with the polytime combinators.

  `encodeCNF F = clStream F ++ [false]`, where `clStream` prints the clauses one after another.
  Generic lemmas show that clause streams built from polytime unary indices over constant lists
  and polytime ranges are polytime; in particular the one-hot CSP clauses `conClauses`
  and `aloClause` for scopes made of polytime unary indices.
-/
import PvnpReal.Unary
import PvnpReal.CSP

set_option linter.unusedSimpArgs false

namespace PvnpReal

theorem PU.congr {u v : List Bool → ℕ} (hu : PU u) (h : ∀ x, u x = v x) : PU v :=
  PS.congr hu (fun x => by rw [h x])

def clStream (F : CNF) : List Bool := F.flatMap (fun c => true :: encList encLit c)

theorem encodeCNF_eq (F : CNF) : encodeCNF F = clStream F ++ [false] := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    show true :: (encList encLit c ++ encList (encList encLit) F) = _
    rw [show encList (encList encLit) F = encodeCNF F from rfl, ih]
    simp [clStream]

theorem clStream_append (F G : CNF) : clStream (F ++ G) = clStream F ++ clStream G := by
  simp [clStream]

theorem clStream_flatMap {α : Type*} (l : List α) (f : α → CNF) :
    clStream (l.flatMap f) = l.flatMap (fun a => clStream (f a)) := by
  simp [clStream, List.flatMap_assoc]

theorem clStream_map {α : Type*} (l : List α) (f : α → Clause) :
    clStream (l.map f) = l.flatMap (fun a => true :: encList encLit (f a)) := by
  simp [clStream, List.flatMap_map]

/-- Concatenation over a constant list. -/
theorem PS.flatMap_const {α : Type*} (L : List α) (f : α → List Bool → List Bool)
    (h : ∀ a ∈ L, PS (f a)) : PS (fun x => L.flatMap (fun a => f a x)) := by
  induction L with
  | nil => exact PS.const []
  | cons a L ih =>
    exact ((h a (by simp)).append (ih (fun b hb => h b (by simp [hb])))).congr
      (fun x => by simp)

/-- Concatenation over a polytime range; the body sees `i` and `x` through `1ⁱ 0 x`. -/
theorem PS.flatRange {N : List Bool → ℕ} (hN : PU N) (b : ℕ → List Bool → List Bool)
    (hb : PS (fun z => b (lpN z) (lpX z))) :
    PS (fun x => (List.range (N x)).flatMap fun i => b i x) :=
  flatRange_computable N b hN _ hb (fun x i _ => by rw [lpN_rep, lpX_rep])

/-- Literal lists with polytime unary indices and fixed signs. -/
theorem PS.encLits {α : Type*} (L : List α) (g : α → List Bool → ℕ) (neg : α → Bool)
    (hg : ∀ a ∈ L, PU (g a)) :
    PS (fun x => encList encLit (L.map fun a => (⟨g a x, neg a⟩ : Literal))) := by
  induction L with
  | nil => exact PS.const [false]
  | cons a L ih =>
    have hl : PS (fun x => encLit ⟨g a x, neg a⟩) :=
      encLit_computable (g a) (neg a) (hg a (by simp))
    exact (PS.cons true (hl.append (ih (fun b hb => hg b (by simp [hb]))))).congr
      (fun x => by simp [encList])

variable {D : Type*} [DecidableEq D]

theorem forbidClause_eq (U : List D) {β : Type*} (fs : List β) (ev : β → ℕ) (ds : List D) :
    forbidClause U (fs.map ev) ds =
      (fs.zip ds).map (fun p => (⟨ev p.1 * U.length + U.idxOf p.2, true⟩ : Literal)) := by
  unfold forbidClause hotVar
  rw [List.zip_map_left, List.map_map]
  rfl

/-- **Printing one constraint**: its forbidden-tuple clauses, for a scope of polytime unary
indices and a fixed relation. -/
theorem PS.conCl (U : List D) (fs : List (List Bool → ℕ)) (hfs : ∀ f ∈ fs, PU f)
    (rel : List D → Bool) :
    PS (fun x => clStream (conClauses U ⟨fs.map (fun f => f x), rel⟩)) := by
  unfold PvnpReal.conClauses
  simp only [List.length_map, clStream_map]
  refine PS.flatMap_const _ (fun ds x => true :: encList encLit
    (forbidClause U (fs.map (fun f => f x)) ds)) (fun ds _ => ?_)
  refine (PS.cons true (PS.encLits (fs.zip ds) (fun p x => p.1 x * U.length + U.idxOf p.2)
    (fun _ => true) (fun p hp => ?_))).congr (fun x => by rw [forbidClause_eq U fs (fun f => f x)])
  have hf := hfs p.1 (List.of_mem_zip hp).1
  exact PU.congr ((hf.polyOf (Polynomial.C U.length * Polynomial.X)).add (PU.const (U.idxOf p.2)))
    (fun x => by simp [Nat.mul_comm])

end PvnpReal
