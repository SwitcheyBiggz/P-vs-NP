/-
  PvnpReal.Sat — CNF formulas, evaluation, a faithful (injective) binary
  encoding of CNF formulas, and SAT as a language of bit strings.

  The `Literal` / `Clause` / `CNF` / `evalLiteral` / `evalClause` / `evalCNF` / `SAT`
  definitions are reused verbatim from Ian's v76 file. What is NEW is the encoding:
  v76's `decodeCNF` mapped every input to a satisfiable formula; here SAT is the set
  of strings that are the encoding of a genuinely satisfiable formula.
-/
import Mathlib.Computability.Encoding

namespace PvnpReal

/-! ## 1. Ian's CNF code (reused unchanged) -/

structure Literal where
  var : ℕ
  neg : Bool

abbrev Clause := List Literal
abbrev CNF := List Clause

def evalLiteral (lit : Literal) (a : ℕ → Bool) : Bool :=
  if lit.neg then !a lit.var else a lit.var

def evalClause (cl : Clause) (a : ℕ → Bool) : Bool :=
  cl.any (fun lit => evalLiteral lit a)

def evalCNF (cnf : CNF) (a : ℕ → Bool) : Bool :=
  cnf.all (fun cl => evalClause cl a)

def SAT (cnf : CNF) : Prop :=
  ∃ a : ℕ → Bool, evalCNF cnf a

/-! ## 2. Correctness lemmas for evaluation -/

theorem evalLiteral_pos (v : ℕ) (a : ℕ → Bool) :
    evalLiteral ⟨v, false⟩ a = a v := rfl

theorem evalLiteral_neg (v : ℕ) (a : ℕ → Bool) :
    evalLiteral ⟨v, true⟩ a = !a v := rfl

theorem evalClause_iff (cl : Clause) (a : ℕ → Bool) :
    evalClause cl a = true ↔ ∃ lit ∈ cl, evalLiteral lit a = true := by
  simp [evalClause]

theorem evalCNF_iff (cnf : CNF) (a : ℕ → Bool) :
    evalCNF cnf a = true ↔ ∀ cl ∈ cnf, ∃ lit ∈ cl, evalLiteral lit a = true := by
  simp [evalCNF, evalClause]

/-- The empty clause is false under every assignment. -/
theorem evalClause_nil (a : ℕ → Bool) : evalClause [] a = false := rfl

/-- A formula containing the empty clause is unsatisfiable. -/
theorem not_SAT_of_nil_mem (cnf : CNF) (h : [] ∈ cnf) : ¬ SAT cnf := by
  rintro ⟨a, ha⟩
  obtain ⟨lit, hlit, _⟩ := (evalCNF_iff cnf a).1 ha [] h
  simp at hlit

theorem SAT_empty : SAT [] := ⟨fun _ => true, rfl⟩

/-- `x0` is satisfiable. -/
theorem SAT_x0 : SAT [[⟨0, false⟩]] := ⟨fun _ => true, rfl⟩

/-- `x0 ∧ ¬x0` is NOT satisfiable. This is exactly what v76 could not express:
there, every input decoded to a satisfiable formula. -/
theorem not_SAT_x0_and_not_x0 : ¬ SAT [[⟨0, false⟩], [⟨0, true⟩]] := by
  rintro ⟨a, ha⟩
  cases h : a 0 <;> simp [evalCNF, evalClause, evalLiteral, h] at ha

/-! ## 3. A faithful binary encoding of CNF formulas -/

/-- `e` is prefix-free: an encoding can be uniquely peeled off the front of a string. -/
def PrefixFree {α : Type} (e : α → List Bool) : Prop :=
  ∀ a b r s, e a ++ r = e b ++ s → a = b ∧ r = s

theorem PrefixFree.injective {α : Type} {e : α → List Bool} (h : PrefixFree e) :
    Function.Injective e := fun a b hab =>
  (h a b [] [] (by simpa using hab)).1

/-- Self-delimiting bit string: each bit `b` becomes `1 b`, the end is marked by `0`. -/
def delim : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delim l

theorem delim_prefixFree : PrefixFree delim := by
  intro a
  induction a with
  | nil => intro b r s h; cases b <;> simp_all [delim]
  | cons x a ih =>
    intro b r s h
    cases b with
    | nil => simp [delim] at h
    | cons y b =>
      simp only [delim, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hxy, h⟩ := h
      obtain ⟨rfl, rfl⟩ := ih b r s h
      exact ⟨by rw [hxy], rfl⟩

/-- A list of items: each item is preceded by `1`, the list ends with `0`. -/
def encList {α : Type} (e : α → List Bool) : List α → List Bool
  | [] => [false]
  | x :: xs => true :: (e x ++ encList e xs)

theorem encList_prefixFree {α : Type} {e : α → List Bool} (he : PrefixFree e) :
    PrefixFree (encList e) := by
  intro a
  induction a with
  | nil => intro b r s h; cases b <;> simp_all [encList]
  | cons x xs ih =>
    intro b r s h
    cases b with
    | nil => simp [encList] at h
    | cons y ys =>
      simp only [encList, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := he x y _ _ h
      obtain ⟨rfl, rfl⟩ := ih ys r s h2
      exact ⟨rfl, rfl⟩

/-- A variable index `v` in unary: `v` ones followed by a zero.
(Milestone 2 changed this from binary to unary; see NOTES.md for why.) -/
def encVar (v : ℕ) : List Bool := List.replicate v true ++ [false]

theorem encVar_prefixFree : PrefixFree encVar := by
  intro a
  induction a with
  | zero => intro b r s h; cases b <;> simp_all [encVar, List.replicate_succ]
  | succ a ih =>
    intro b r s h
    cases b with
    | zero => simp [encVar, List.replicate_succ] at h
    | succ b =>
      simp only [encVar, List.replicate_succ, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨rfl, rfl⟩ := ih b r s (by simpa [encVar, List.append_assoc] using h)
      exact ⟨rfl, rfl⟩

/-- A literal: its sign bit, then its variable index in unary. -/
def encLit (l : Literal) : List Bool :=
  l.neg :: encVar l.var

theorem encLit_prefixFree : PrefixFree encLit := by
  rintro ⟨v, n⟩ ⟨v', n'⟩ r s h
  simp only [encLit, List.cons_append, List.cons.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, rfl⟩ := encVar_prefixFree _ _ _ _ h
  exact ⟨rfl, rfl⟩

/-- The encoding of a CNF formula as a bit string. -/
def encodeCNF : CNF → List Bool := encList (encList encLit)

theorem encodeCNF_prefixFree : PrefixFree encodeCNF :=
  encList_prefixFree (encList_prefixFree encLit_prefixFree)

/-- Faithfulness: different formulas get different codes. -/
theorem encodeCNF_injective : Function.Injective encodeCNF :=
  encodeCNF_prefixFree.injective

/-! ## 4. SAT as a language of bit strings -/

/-- `x ∈ SATLang` iff `x` is the code of a satisfiable CNF formula. Strings that are not
valid codes are NOT in the language. -/
def SATLang (x : List Bool) : Prop :=
  ∃ φ : CNF, encodeCNF φ = x ∧ SAT φ

theorem SATLang_encode_iff (φ : CNF) : SATLang (encodeCNF φ) ↔ SAT φ := by
  constructor
  · rintro ⟨ψ, hψ, hs⟩
    rwa [← encodeCNF_injective hψ]
  · exact fun h => ⟨φ, rfl, h⟩

/-- SAT is not the trivial "everything" language (v76's SAT language was). -/
theorem SATLang_not_univ : ∃ x, ¬ SATLang x :=
  ⟨encodeCNF [[⟨0, false⟩], [⟨0, true⟩]],
    (SATLang_encode_iff _).not.2 not_SAT_x0_and_not_x0⟩

/-- SAT is not the empty language either. -/
theorem SATLang_nonempty : ∃ x, SATLang x :=
  ⟨encodeCNF [[⟨0, false⟩]], (SATLang_encode_iff _).2 SAT_x0⟩

/-- The empty bit string is not a valid code, so it is not in SAT. -/
theorem not_SATLang_nil : ¬ SATLang [] := by
  rintro ⟨φ, h, -⟩
  cases φ <;> simp [encodeCNF, encList] at h

end PvnpReal
