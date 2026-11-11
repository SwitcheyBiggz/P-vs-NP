/-
  ======================================================================
  Benchmarks.lean: Machine-Verified Computational SAT Benchmark Engine
  ======================================================================
  Extracts and formalizes the exact, self-contained SAT benchmark infrastructure:
  * Exact 2ⁿ hypercube solver `solveSAT`, soundness & completeness
  * Prefix-free unary-delimited CNF encoding & linear-time decoding
  * F₂ Nullstellensatz falsification polynomials (`evalClauseF2_vanishes_iff`)
  * Conflict-nogood auto-pruning soundness (`nogood_pruning_sound`)
  * Tseitin circuit gate transformation (`gateCNF_iff`)
  * Karp reduction invariants (k-Clique and Subset-Sum)
  * 4 machine-verified benchmarks:
      1. `deceptive_trap_4v` (n = 4, m = 13, unique satisfying state)
      2. `cook_levin_gadget_3v` (n = 3, m = 4, SAT gadget)
      3. `phase_transition_5v` (n = 5, m = 21, α = 4.2, unique state)
      4. `unsat_core_3v` (n = 3, m = 8, 100% unsatisfiable resolution core)
  * Theorems: `unsat_core_3v_unsat`, `SATLang_nontrivial`, `UNSATLang_unsat_core`
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Computability.TuringMachine.Computable

namespace Benchmarks

-- ============================================================
-- 1. CONCRETE 3-SAT VERIFIER & EXACT SOLVER (SOUND & COMPLETE)
-- ============================================================

/-- A Boolean literal: 1-indexed variable number and negation flag. -/
structure Literal where
  var : ℕ
  neg : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Literal
abbrev CNF := List Clause
abbrev Assignment := ℕ → Bool

/-- Evaluates a single literal under truth assignment `a`. -/
def evalLiteral (a : Assignment) (lit : Literal) : Bool :=
  if lit.neg then !(a lit.var) else a lit.var

/-- Evaluates a disjunction of literals (clause) in O(k) time. -/
def evalClause (a : Assignment) (cl : Clause) : Bool :=
  cl.any (evalLiteral a)

/-- Deterministic O(m) polynomial-time CNF certificate verifier. -/
def evalCNF (cnf : CNF) (a : Assignment) : Bool :=
  cnf.all (evalClause a)

/-- A CNF formula is satisfiable iff some truth assignment makes `evalCNF` true. -/
def SAT (cnf : CNF) : Prop :=
  ∃ a : Assignment, evalCNF cnf a = true

/-- Locality of literal evaluation: depends only on `a lit.var`. -/
theorem evalLiteral_congr {a₁ a₂ : Assignment} {lit : Literal}
    (h : a₁ lit.var = a₂ lit.var) : evalLiteral a₁ lit = evalLiteral a₂ lit := by
  simp [evalLiteral, h]

/-- Locality of clause evaluation: depends only on variables appearing in `cl`. -/
theorem evalClause_congr {a₁ a₂ : Assignment} {cl : Clause}
    (h : ∀ lit ∈ cl, a₁ lit.var = a₂ lit.var) : evalClause a₁ cl = evalClause a₂ cl := by
  induction cl with
  | nil => rfl
  | cons lit lits ih =>
    unfold evalClause at ih ⊢
    simp only [List.any_cons]
    rw [evalLiteral_congr (h lit List.mem_cons_self),
        ih (fun l hl => h l (List.mem_cons_of_mem lit hl))]

/-- Locality of CNF evaluation: depends only on variables appearing in `cnf`. -/
theorem evalCNF_congr {a₁ a₂ : Assignment} {cnf : CNF}
    (h : ∀ cl ∈ cnf, ∀ lit ∈ cl, a₁ lit.var = a₂ lit.var) :
    evalCNF cnf a₁ = evalCNF cnf a₂ := by
  induction cnf with
  | nil => rfl
  | cons cl cls ih =>
    unfold evalCNF at ih ⊢
    simp only [List.all_cons]
    rw [evalClause_congr (h cl List.mem_cons_self),
        ih (fun c hc => h c (List.mem_cons_of_mem cl hc))]

/-- Decodes a bitmask `mask : ℕ` into a 1-indexed truth assignment (`v ↦ bit (v-1)`).
    Variable `v` reads bit `v-1`, so variables 0 and 1 get bit 0.
    This is standard because variables are numbered from 1. -/
def assignOfMask (mask : ℕ) : Assignment :=
  fun v => Nat.testBit mask (v - 1)

/-- Searches bitmasks `0 .. bound - 1` for a satisfying assignment. -/
def findMaskAux (cnf : CNF) : ℕ → Option ℕ
  | 0 => none
  | m + 1 =>
    if evalCNF cnf (assignOfMask m) then some m
    else findMaskAux cnf m

/-- Exact exhaustive 2ⁿ SAT solver returning a verified truth assignment when one exists. -/
def solveSAT (numVars : ℕ) (cnf : CNF) : Option Assignment :=
  (findMaskAux cnf (2 ^ numVars)).map assignOfMask

theorem findMaskAux_sound (cnf : CNF) :
    ∀ bound m, findMaskAux cnf bound = some m → evalCNF cnf (assignOfMask m) = true
  | 0, _, h => by cases h
  | bound + 1, m, h => by
    unfold findMaskAux at h
    split at h
    · rename_i hsat
      cases h
      exact hsat
    · exact findMaskAux_sound cnf bound m h

/-- Soundness of `solveSAT`: any returned assignment is a valid satisfying witness. -/
theorem solveSAT_sound (numVars : ℕ) (cnf : CNF) (a : Assignment)
    (h : solveSAT numVars cnf = some a) : evalCNF cnf a = true := by
  unfold solveSAT at h
  rcases Option.mem_map.mp h with ⟨m, hm, rfl⟩
  exact findMaskAux_sound cnf (2 ^ numVars) m hm

/-- Any assignment returned by `solveSAT` witnesses `SAT cnf`. -/
theorem solveSAT_implies_SAT (numVars : ℕ) (cnf : CNF) (a : Assignment)
    (h : solveSAT numVars cnf = some a) : SAT cnf :=
  ⟨a, solveSAT_sound numVars cnf a h⟩

/-- Soundness and Completeness of `findMaskAux` over `0 .. bound - 1`. -/
theorem findMaskAux_isSome_iff (cnf : CNF) :
    ∀ bound, (findMaskAux cnf bound).isSome = true ↔
      ∃ m < bound, evalCNF cnf (assignOfMask m) = true
  | 0 => by simp [findMaskAux]
  | bound + 1 => by
    unfold findMaskAux
    by_cases hsat : evalCNF cnf (assignOfMask bound) = true
    · simp only [hsat, ↓reduceIte, Option.isSome_some, true_iff]
      exact ⟨bound, Nat.lt_succ_self bound, hsat⟩
    · simp only [hsat, Bool.false_eq_true, ↓reduceIte, findMaskAux_isSome_iff cnf bound]
      constructor
      · rintro ⟨m, hm, h⟩
        exact ⟨m, Nat.lt_succ_of_lt hm, h⟩
      · rintro ⟨m, hm, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
        · exact ⟨m, hlt, h⟩
        · exact False.elim (hsat h)

/-- Full Soundness & Completeness of `solveSAT` over the 2ⁿ hypercube. -/
theorem solveSAT_isSome_iff (numVars : ℕ) (cnf : CNF) :
    (solveSAT numVars cnf).isSome = true ↔
      ∃ m < 2 ^ numVars, evalCNF cnf (assignOfMask m) = true := by
  unfold solveSAT
  rw [Option.isSome_map, findMaskAux_isSome_iff]

/-- Counts how many hypercube states in `0 .. 2^n - 1` satisfy `cnf`. -/
def countSatisfyingMasks (numVars : ℕ) (cnf : CNF) : ℕ :=
  (List.range (2 ^ numVars)).countP (fun m => evalCNF cnf (assignOfMask m))

-- ============================================================
-- 2. BINARY ENCODING OF CNF & TOTAL DECODER
-- ============================================================

/-- Prefix-free unary-delimited binary encoding of a variable index `v`. -/
def encodeVar : ℕ → List Bool
  | 0 => [false]
  | n + 1 => true :: encodeVar n

/-- Prefix-free binary encoding of a literal (`true :: neg :: encodeVar var`). -/
def encodeLit (l : Literal) : List Bool :=
  true :: l.neg :: encodeVar l.var

/-- Prefix-free binary encoding of a clause (`concatMap encodeLit ++ [false]`). -/
def encodeClause : Clause → List Bool
  | [] => [false]
  | l :: ls => encodeLit l ++ encodeClause ls

/-- Prefix-free binary encoding of a CNF formula. -/
def encodeCNF : CNF → List Bool
  | [] => []
  | cl :: cls => encodeClause cl ++ encodeCNF cls

/-- Linear-time single-pass decoder for unary-delimited CNF bitstreams. -/
def decodeCNFAux : List Bool → ℕ → Bool → ℕ → Clause → CNF → CNF
  | [], 0, _, _, _, acc => acc.reverse
  | [], 1, _, _, curCl, acc => (curCl.reverse :: acc).reverse
  | [], _, neg, curVar, curCl, acc => (⟨curVar, neg⟩ :: curCl).reverse :: acc |>.reverse
  | b :: bs, 0, _, _, curCl, acc =>
    if b then decodeCNFAux bs 2 false 0 curCl acc
    else decodeCNFAux bs 0 false 0 [] (curCl.reverse :: acc)
  | b :: bs, 1, _, _, curCl, acc =>
    if b then decodeCNFAux bs 2 false 0 curCl acc
    else decodeCNFAux bs 0 false 0 [] (curCl.reverse :: acc)
  | b :: bs, 2, _, _, curCl, acc =>
    decodeCNFAux bs 3 b 0 curCl acc
  | b :: bs, _, neg, curVar, curCl, acc =>
    if b then decodeCNFAux bs 3 neg (curVar + 1) curCl acc
    else decodeCNFAux bs 1 false 0 (⟨curVar, neg⟩ :: curCl) acc

/-- Canonical total decoder `List Bool → CNF`. -/
def decodeCNF (bits : List Bool) : CNF :=
  decodeCNFAux bits 0 false 0 [] []

theorem decodeCNFAux_encodeVar (v : ℕ) (rest : List Bool) (neg : Bool)
    (curVar : ℕ) (curCl : Clause) (acc : CNF) :
    decodeCNFAux (encodeVar v ++ rest) 3 neg curVar curCl acc =
      decodeCNFAux rest 1 false 0 (⟨curVar + v, neg⟩ :: curCl) acc := by
  induction v generalizing curVar with
  | zero =>
    simp [encodeVar, decodeCNFAux]
  | succ n ih =>
    simp only [encodeVar, List.cons_append, decodeCNFAux, ↓reduceIte]
    have hadd : curVar + 1 + n = curVar + (n + 1) := by omega
    rw [ih (curVar + 1), hadd]

theorem decodeCNFAux_encodeLit (l : Literal) (rest : List Bool) (mode : ℕ)
    (hmode : mode = 0 ∨ mode = 1) (curCl : Clause) (acc : CNF) :
    decodeCNFAux (encodeLit l ++ rest) mode false 0 curCl acc =
      decodeCNFAux rest 1 false 0 (l :: curCl) acc := by
  rcases l with ⟨v, neg⟩
  rcases hmode with rfl | rfl <;>
  · simp only [encodeLit, List.cons_append, decodeCNFAux, ↓reduceIte]
    simpa using decodeCNFAux_encodeVar v rest neg 0 curCl acc

theorem decodeCNFAux_encodeClause (cl : Clause) (rest : List Bool) (mode : ℕ)
    (hmode : mode = 0 ∨ mode = 1) (curCl : Clause) (acc : CNF) :
    decodeCNFAux (encodeClause cl ++ rest) mode false 0 curCl acc =
      decodeCNFAux rest 0 false 0 [] ((curCl.reverse ++ cl) :: acc) := by
  induction cl generalizing mode curCl with
  | nil =>
    rcases hmode with rfl | rfl <;> simp [encodeClause, decodeCNFAux]
  | cons l ls ih =>
    simp only [encodeClause, List.append_assoc]
    rw [decodeCNFAux_encodeLit l (encodeClause ls ++ rest) mode hmode curCl acc]
    rw [ih 1 (Or.inr rfl) (l :: curCl)]
    simp [List.reverse_cons, List.append_assoc]

theorem decodeCNFAux_encodeCNF (cnf : CNF) (acc : CNF) :
    decodeCNFAux (encodeCNF cnf) 0 false 0 [] acc = acc.reverse ++ cnf := by
  induction cnf generalizing acc with
  | nil =>
    simp [encodeCNF, decodeCNFAux]
  | cons cl cls ih =>
    simp only [encodeCNF]
    rw [decodeCNFAux_encodeClause cl (encodeCNF cls) 0 (Or.inl rfl) [] acc]
    simp only [List.reverse_nil, List.nil_append]
    rw [ih (cl :: acc)]
    simp [List.reverse_cons, List.append_assoc]

/-- Exact round-trip invertibility: `decodeCNF (encodeCNF cnf) = cnf`. -/
@[simp]
theorem decodeCNF_encodeCNF (cnf : CNF) : decodeCNF (encodeCNF cnf) = cnf := by
  unfold decodeCNF
  simpa using decodeCNFAux_encodeCNF cnf []

/-- `encodeCNF` is injective. -/
theorem encodeCNF_injective : Function.Injective encodeCNF :=
  Function.LeftInverse.injective decodeCNF_encodeCNF

/-- The decision language `SATLang : List Bool → Bool`. -/
def SATLang (x : List Bool) : Bool :=
  (solveSAT x.length (decodeCNF x)).isSome

-- ============================================================
-- 3. F₂ BOOLEAN POLYNOMIAL EQUIVALENCE & NOGOOD PRUNING
-- ============================================================

/-- Evaluates the F₂ falsification polynomial `∏_{l ∈ cl} (1 ⊕ l~)` of a clause. -/
def evalClauseF2 (a : Assignment) (cl : Clause) : Bool :=
  cl.foldr (fun lit acc => !(evalLiteral a lit) && acc) true

/-- Duality between Boolean disjunction and the F₂ falsification monomial. -/
theorem evalClauseF2_eq_not_evalClause (a : Assignment) :
    ∀ cl : Clause, evalClauseF2 a cl = !(evalClause a cl)
  | [] => rfl
  | lit :: cl => by
    have ih := evalClauseF2_eq_not_evalClause a cl
    unfold evalClauseF2 evalClause at ih ⊢
    simp only [List.foldr_cons, List.any_cons, Bool.not_or, ih]

/-- Nullstellensatz correspondence per clause: `P_j(a) = 0` in F₂ iff `cl` is satisfied. -/
theorem evalClauseF2_vanishes_iff (a : Assignment) (cl : Clause) :
    evalClauseF2 a cl = false ↔ evalClause a cl = true := by
  rw [evalClauseF2_eq_not_evalClause, Bool.not_eq_false']

/-- Checks whether assignment `a` matches the forbidden conflict nogood cube of clause `cl`. -/
def matchesForbiddenCube (a : Assignment) (cl : Clause) : Bool :=
  cl.all (fun lit => !(evalLiteral a lit))

theorem matchesForbiddenCube_eq_not_evalClause (a : Assignment) :
    ∀ cl : Clause, matchesForbiddenCube a cl = !(evalClause a cl)
  | [] => rfl
  | lit :: cl => by
    have ih := matchesForbiddenCube_eq_not_evalClause a cl
    unfold matchesForbiddenCube evalClause at ih ⊢
    simp only [List.all_cons, List.any_cons, Bool.not_or, ih]

/-- Soundness of Conflict-Nogood Auto-Pruning:
    any assignment matching a learned conflict cube of `cl ∈ cnf` falsifies `evalCNF cnf a`. -/
theorem nogood_pruning_sound (a : Assignment) (cnf : CNF) (cl : Clause)
    (hcl : cl ∈ cnf) (hmatch : matchesForbiddenCube a cl = true) :
    evalCNF cnf a = false := by
  rw [matchesForbiddenCube_eq_not_evalClause, Bool.not_eq_true'] at hmatch
  unfold evalCNF
  exact List.all_eq_false.mpr ⟨cl, hcl, by simp [hmatch]⟩

-- ============================================================
-- 4. TSEITIN GATE TRANSFORMATION
-- ============================================================

/-- A Boolean logic gate in a circuit: constants, NOT, AND, or OR over wire indices. -/
inductive Gate where
  | const (b : Bool)
  | not (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)
  deriving DecidableEq, Repr

/-- Evaluates a single `Gate` under wire assignment `a : ℕ → Bool`. -/
def Gate.eval (g : Gate) (a : Assignment) : Bool :=
  match g with
  | .const b => b
  | .not i => !(a i)
  | .and i j => a i && a j
  | .or i j => a i || a j

def posL (v : ℕ) : Literal := ⟨v, false⟩
def negL (v : ℕ) : Literal := ⟨v, true⟩

/-- Tseitin 3-CNF clauses enforcing `a w = g.eval a` for output wire `w` and gate `g`. -/
def gateCNF (w : ℕ) : Gate → CNF
  | .const true => [[posL w]]
  | .const false => [[negL w]]
  | .not i => [[negL w, negL i], [posL w, posL i]]
  | .and i j => [[negL w, posL i], [negL w, posL j], [posL w, negL i, negL j]]
  | .or i j => [[posL w, negL i], [posL w, negL j], [negL w, posL i, posL j]]

/-- Correctness of the Tseitin gate transformation: `gateCNF w g` is satisfied by `a`
    if and only if wire `w` carries the exact Boolean value `g.eval a`. -/
theorem gateCNF_iff (w : ℕ) (g : Gate) (a : Assignment) :
    evalCNF (gateCNF w g) a = true ↔ a w = g.eval a := by
  cases g with
  | const b =>
    cases b <;> cases h : a w <;>
      simp [gateCNF, Gate.eval, evalCNF, evalClause, evalLiteral, posL, negL, h]
  | not i =>
    cases hw : a w <;> cases hi : a i <;>
      simp [gateCNF, Gate.eval, evalCNF, evalClause, evalLiteral, posL, negL, hw, hi]
  | and i j =>
    cases hw : a w <;> cases hi : a i <;> cases hj : a j <;>
      simp [gateCNF, Gate.eval, evalCNF, evalClause, evalLiteral, posL, negL, hw, hi, hj]
  | or i j =>
    cases hw : a w <;> cases hi : a i <;> cases hj : a j <;>
      simp [gateCNF, Gate.eval, evalCNF, evalClause, evalLiteral, posL, negL, hw, hi, hj]

/-- Conjunction of CNF formulas: `evalCNF (cnf₁ ++ cnf₂) a = (evalCNF cnf₁ a && evalCNF cnf₂ a)`. -/
theorem evalCNF_append (cnf₁ cnf₂ : CNF) (a : Assignment) :
    evalCNF (cnf₁ ++ cnf₂) a = (evalCNF cnf₁ a && evalCNF cnf₂ a) := by
  unfold evalCNF
  exact List.all_append

-- ============================================================
-- 5. KARP k-CLIQUE & EXACT SUBSET-SUM REDUCTION INVARIANTS
-- ============================================================

/-- Two literals are compatible (in a k-Clique) iff they do not assign opposite polarities
    to the same variable. -/
def compatibleLiterals (l₁ l₂ : Literal) : Bool :=
  !(l₁.var == l₂.var && l₁.neg != l₂.neg)

/-- Soundness of the k-Clique reduction edge rule: two literals that both evaluate
    to `true` under `a` are necessarily non-contradictory. -/
theorem true_literals_compatible (a : Assignment) (l₁ l₂ : Literal)
    (h₁ : evalLiteral a l₁ = true) (h₂ : evalLiteral a l₂ = true) :
    compatibleLiterals l₁ l₂ = true := by
  rcases l₁ with ⟨v₁, n₁⟩
  rcases l₂ with ⟨v₂, n₂⟩
  by_cases hvar : v₁ = v₂
  · subst hvar
    cases n₁ <;> cases n₂ <;> simp_all [compatibleLiterals, evalLiteral]
  · simp [compatibleLiterals, hvar]

/-- Soundness of the Karp Subset-Sum clause column target (= 4) with slack (+1, +2):
    for any 3-clause with `count ≤ 3` true literals, slack bits reach sum `4` iff `1 ≤ count`. -/
theorem subset_sum_slack_iff :
    ∀ count ≤ 3,
      ((∃ b₁ b₂ : Bool, count + (if b₁ then 1 else 0) + (if b₂ then 2 else 0) = 4) ↔
        1 ≤ count) := by
  decide

-- ============================================================
-- 6. MACHINE-VERIFIED COOK–LEVIN LAB BENCHMARKS
-- ============================================================

/-- Helper to construct a 1-indexed literal. -/
def mkLit (v : ℕ) (neg : Bool) : Literal := ⟨v, neg⟩

/-- Benchmark 1: Adversarial Deceptive Trap (n = 4, m = 13, Unique Witness mask = 10). -/
def deceptive_trap_4v : CNF := [
  [mkLit 1 false, mkLit 2 false, mkLit 3 true],
  [mkLit 1 false, mkLit 2 true,  mkLit 4 false],
  [mkLit 1 false, mkLit 3 false, mkLit 4 false],
  [mkLit 2 true,  mkLit 3 false, mkLit 4 false],
  [mkLit 1 true,  mkLit 2 false, mkLit 3 true],
  [mkLit 1 true,  mkLit 2 true,  mkLit 3 false],
  [mkLit 1 false, mkLit 2 true,  mkLit 3 true],
  [mkLit 1 false, mkLit 2 false, mkLit 4 true],
  [mkLit 1 true,  mkLit 2 true,  mkLit 4 true],
  [mkLit 1 true,  mkLit 2 false, mkLit 4 false],
  [mkLit 1 true,  mkLit 2 true,  mkLit 3 true],
  [mkLit 1 true,  mkLit 3 false, mkLit 4 true],
  [mkLit 2 false, mkLit 3 true,  mkLit 4 false]
]

/-- Benchmark 2: Compact Cook–Levin Gadget (n = 3, m = 4, SAT witness mask = 5). -/
def cook_levin_gadget_3v : CNF := [
  [mkLit 1 false, mkLit 2 false, mkLit 3 false],
  [mkLit 1 true,  mkLit 2 true,  mkLit 3 false],
  [mkLit 1 false, mkLit 2 true,  mkLit 3 true],
  [mkLit 1 true,  mkLit 2 false, mkLit 3 false]
]

/-- Benchmark 3: Phase Transition Threshold α = 4.2 (n = 5, m = 21, Unique Witness mask = 11). -/
def phase_transition_5v : CNF := [
  [mkLit 2 true,  mkLit 4 false, mkLit 5 true],
  [mkLit 1 false, mkLit 4 false, mkLit 5 false],
  [mkLit 1 true,  mkLit 4 true,  mkLit 5 true],
  [mkLit 1 false, mkLit 2 true,  mkLit 3 false],
  [mkLit 2 false, mkLit 4 true,  mkLit 5 true],
  [mkLit 1 false, mkLit 2 true,  mkLit 4 true],
  [mkLit 1 false, mkLit 4 true,  mkLit 5 false],
  [mkLit 1 true,  mkLit 4 false, mkLit 5 true],
  [mkLit 3 false, mkLit 4 true,  mkLit 5 true],
  [mkLit 2 true,  mkLit 4 false, mkLit 5 false],
  [mkLit 1 false, mkLit 3 true,  mkLit 4 false],
  [mkLit 2 false, mkLit 3 false, mkLit 5 false],
  [mkLit 2 false, mkLit 3 true,  mkLit 5 true],
  [mkLit 2 false, mkLit 4 false, mkLit 5 true],
  [mkLit 1 false, mkLit 4 true,  mkLit 5 true],
  [mkLit 1 true,  mkLit 2 false, mkLit 5 false],
  [mkLit 2 true,  mkLit 4 true,  mkLit 5 true],
  [mkLit 1 false, mkLit 2 true,  mkLit 5 true],
  [mkLit 1 false, mkLit 2 false, mkLit 5 false],
  [mkLit 1 false, mkLit 3 true,  mkLit 4 true],
  [mkLit 3 true,  mkLit 4 true,  mkLit 5 false]
]

/-- Benchmark 4: Unsatisfiable Resolution Core (UNSAT, n = 3, m = 8). -/
def unsat_core_3v : CNF := [
  [mkLit 1 false, mkLit 2 false, mkLit 3 false],
  [mkLit 1 false, mkLit 2 false, mkLit 3 true],
  [mkLit 1 false, mkLit 2 true,  mkLit 3 false],
  [mkLit 1 false, mkLit 2 true,  mkLit 3 true],
  [mkLit 1 true,  mkLit 2 false, mkLit 3 false],
  [mkLit 1 true,  mkLit 2 false, mkLit 3 true],
  [mkLit 1 true,  mkLit 2 true,  mkLit 3 false],
  [mkLit 1 true,  mkLit 2 true,  mkLit 3 true]
]

/-- Exact characterization of `deceptive_trap_4v`: satisfied iff x = (0, 1, 0, 1). -/
theorem deceptive_trap_4v_iff (a : Assignment) :
    evalCNF deceptive_trap_4v a = true ↔
      (a 1 = false ∧ a 2 = true ∧ a 3 = false ∧ a 4 = true) := by
  simp only [deceptive_trap_4v, evalCNF, evalClause, evalLiteral, mkLit,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  cases a 1 <;> cases a 2 <;> cases a 3 <;> cases a 4 <;> decide

/-- `deceptive_trap_4v` has a unique satisfying state in the 2⁴ = 16 hypercube. -/
theorem deceptive_trap_4v_unique_mask :
    countSatisfyingMasks 4 deceptive_trap_4v = 1 := by decide

/-- `deceptive_trap_4v` is satisfiable. -/
theorem deceptive_trap_4v_sat : SAT deceptive_trap_4v :=
  ⟨assignOfMask 10, by decide⟩

/-- `cook_levin_gadget_3v` is satisfiable. -/
theorem cook_levin_gadget_3v_sat : SAT cook_levin_gadget_3v :=
  ⟨assignOfMask 5, by decide⟩

/-- Exact characterization of `phase_transition_5v`: satisfied iff x = (1, 1, 0, 1, 0). -/
theorem phase_transition_5v_iff (a : Assignment) :
    evalCNF phase_transition_5v a = true ↔
      (a 1 = true ∧ a 2 = true ∧ a 3 = false ∧ a 4 = true ∧ a 5 = false) := by
  simp only [phase_transition_5v, evalCNF, evalClause, evalLiteral, mkLit,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  cases a 1 <;> cases a 2 <;> cases a 3 <;> cases a 4 <;> cases a 5 <;> decide

/-- `phase_transition_5v` has a unique satisfying state in the 2⁵ = 32 hypercube. -/
theorem phase_transition_5v_unique_mask :
    countSatisfyingMasks 5 phase_transition_5v = 1 := by decide

/-- `phase_transition_5v` is satisfiable. -/
theorem phase_transition_5v_sat : SAT phase_transition_5v :=
  ⟨assignOfMask 11, by decide⟩

/-- `unsat_core_3v` has 0 satisfying states in the 2³ = 8 hypercube. -/
theorem unsat_core_3v_zero_masks :
    countSatisfyingMasks 3 unsat_core_3v = 0 := by decide

/-- `unsat_core_3v` is unsatisfiable over all assignments `ℕ → Bool`. -/
theorem unsat_core_3v_unsat : ¬ SAT unsat_core_3v := by
  rintro ⟨a, ha⟩
  revert ha
  simp only [unsat_core_3v, evalCNF, evalClause, evalLiteral, mkLit,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  cases a 1 <;> cases a 2 <;> cases a 3 <;> decide

/-- `SATLang` accepts the binary encoding of the satisfiable `cook_levin_gadget_3v`. -/
theorem SATLang_cook_levin_gadget :
    SATLang (encodeCNF cook_levin_gadget_3v) = true := by
  unfold SATLang
  rw [decodeCNF_encodeCNF, solveSAT_isSome_iff]
  refine ⟨5, ?_, ?_⟩
  · decide
  · decide

/-- `SATLang` rejects the binary encoding of the unsatisfiable `unsat_core_3v`. -/
theorem SATLang_unsat_core :
    SATLang (encodeCNF unsat_core_3v) = false := by
  unfold SATLang
  rw [decodeCNF_encodeCNF]
  by_contra h
  have hs : (solveSAT (encodeCNF unsat_core_3v).length unsat_core_3v).isSome = true :=
    Bool.eq_true_of_not_eq_false h
  rcases (solveSAT_isSome_iff _ _).mp hs with ⟨m, _, hsat⟩
  exact unsat_core_3v_unsat ⟨assignOfMask m, hsat⟩

/-- `SATLang` is non-trivial (neither the empty language nor the universal language). -/
theorem SATLang_nontrivial :
    (∃ x, SATLang x = true) ∧ (∃ y, SATLang y = false) :=
  ⟨⟨encodeCNF cook_levin_gadget_3v, SATLang_cook_levin_gadget⟩,
   ⟨encodeCNF unsat_core_3v, SATLang_unsat_core⟩⟩

/-- The complement language `UNSATLang : List Bool → Bool` over binary strings. -/
def UNSATLang (x : List Bool) : Bool :=
  !(SATLang x)

/-- `UNSATLang` accepts the binary encoding of the unsatisfiable `unsat_core_3v`. -/
theorem UNSATLang_unsat_core :
    UNSATLang (encodeCNF unsat_core_3v) = true := by
  simp [UNSATLang, SATLang_unsat_core]

/-- `UNSATLang` rejects the binary encoding of the satisfiable `cook_levin_gadget_3v`. -/
theorem UNSATLang_cook_levin_gadget :
    UNSATLang (encodeCNF cook_levin_gadget_3v) = false := by
  simp [UNSATLang, SATLang_cook_levin_gadget]

end Benchmarks
