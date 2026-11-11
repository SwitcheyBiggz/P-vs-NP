/-
  Constructive witness extraction and Schaefer syntactic classification.
  One finite CNF is not an NP-complete language. `SchaeferP` means the clause
  set is Horn, dual-Horn, Krom (2-CNF), 0-valid, or 1-valid. That is not a
  proof of P = NP.
-/
import Benchmarks

namespace Benchmarks

def posCount (cl : Clause) : ℕ :=
  cl.countP (fun l => !l.neg)

def negCount (cl : Clause) : ℕ :=
  cl.countP (fun l => l.neg)

def isHorn (cnf : CNF) : Bool :=
  cnf.all (fun cl => decide (posCount cl ≤ 1))

def isDualHorn (cnf : CNF) : Bool :=
  cnf.all (fun cl => decide (negCount cl ≤ 1))

def isKrom (cnf : CNF) : Bool :=
  cnf.all (fun cl => decide (cl.length ≤ 2))

def is0Valid (cnf : CNF) : Bool :=
  evalCNF cnf (fun _ => false)

def is1Valid (cnf : CNF) : Bool :=
  evalCNF cnf (fun _ => true)

/-- Syntactic Schaefer P-tractable classes for one CNF. -/
def isSchaeferP (cnf : CNF) : Bool :=
  isHorn cnf || isDualHorn cnf || isKrom cnf || is0Valid cnf || is1Valid cnf

/-- `decideSAT` is the exhaustive solver. Correctness is the hypercube characterization. -/
def decideSAT (numVars : ℕ) (cnf : CNF) : Bool :=
  (solveSAT numVars cnf).isSome

theorem decideSAT_correct (numVars : ℕ) (cnf : CNF) :
    decideSAT numVars cnf = true ↔
      ∃ m < 2 ^ numVars, evalCNF cnf (assignOfMask m) = true := by
  unfold decideSAT
  exact solveSAT_isSome_iff numVars cnf

/-- Every run either returns a satisfying assignment or refutes every mask below `2^n`. -/
theorem solveSAT_extracts_witness_or_refutes (numVars : ℕ) (cnf : CNF) :
    (∃ a, solveSAT numVars cnf = some a ∧ evalCNF cnf a = true) ∨
      (solveSAT numVars cnf = none ∧
        ∀ m, m < 2 ^ numVars → evalCNF cnf (assignOfMask m) = false) := by
  cases h : solveSAT numVars cnf with
  | some a =>
    exact Or.inl ⟨a, rfl, solveSAT_sound numVars cnf a h⟩
  | none =>
    refine Or.inr ⟨rfl, fun m hm => ?_⟩
    cases hsat : evalCNF cnf (assignOfMask m) with
    | false => rfl
    | true =>
      have hs : (solveSAT numVars cnf).isSome = true :=
        (solveSAT_isSome_iff numVars cnf).mpr ⟨m, hm, hsat⟩
      simp [h] at hs

/-! Horn-SAT #00: five Horn clauses, unique hypercube witness `x = 1110` (mask 7). -/

def horn_sat_00 : CNF := [
  [mkLit 1 false],
  [mkLit 2 false],
  [mkLit 3 false],
  [mkLit 4 true],
  [mkLit 4 true, mkLit 1 false]
]

theorem horn_sat_00_isHorn : isHorn horn_sat_00 = true := by decide

theorem horn_sat_00_schaefer : isSchaeferP horn_sat_00 = true := by decide

theorem horn_sat_00_mask : findMaskAux horn_sat_00 16 = some 7 := by decide

theorem horn_sat_00_witness :
    assignOfMask 7 1 = true ∧ assignOfMask 7 2 = true ∧
      assignOfMask 7 3 = true ∧ assignOfMask 7 4 = false := by decide

theorem horn_sat_00_unique : countSatisfyingMasks 4 horn_sat_00 = 1 := by decide

/-! The four lab benchmarks. Classes are computed, not taken from the dashboard labels. -/

theorem deceptive_trap_mask : findMaskAux deceptive_trap_4v 16 = some 10 := by decide

theorem deceptive_trap_witness_bits :
    assignOfMask 10 1 = false ∧ assignOfMask 10 2 = true ∧
      assignOfMask 10 3 = false ∧ assignOfMask 10 4 = true := by decide

theorem deceptive_trap_not_schaefer : isSchaeferP deceptive_trap_4v = false := by decide

theorem cook_levin_not_horn : isHorn cook_levin_gadget_3v = false := by decide

theorem cook_levin_not_dual : isDualHorn cook_levin_gadget_3v = false := by decide

theorem cook_levin_not_krom : isKrom cook_levin_gadget_3v = false := by decide

theorem cook_levin_not_0valid : is0Valid cook_levin_gadget_3v = false := by decide

theorem cook_levin_1valid : is1Valid cook_levin_gadget_3v = true := by decide

theorem cook_levin_schaefer : isSchaeferP cook_levin_gadget_3v = true := by decide

theorem cook_levin_extracted_mask : findMaskAux cook_levin_gadget_3v 8 = some 7 := by decide

theorem cook_levin_witness_bits :
    assignOfMask 7 1 = true ∧ assignOfMask 7 2 = true ∧ assignOfMask 7 3 = true := by decide

theorem cook_levin_model_count : countSatisfyingMasks 3 cook_levin_gadget_3v = 4 := by decide

theorem phase_transition_mask : findMaskAux phase_transition_5v 32 = some 11 := by decide

theorem phase_transition_not_schaefer : isSchaeferP phase_transition_5v = false := by decide

theorem unsat_core_refutes : findMaskAux unsat_core_3v 8 = none := by decide

theorem unsat_core_not_schaefer : isSchaeferP unsat_core_3v = false := by decide

end Benchmarks
