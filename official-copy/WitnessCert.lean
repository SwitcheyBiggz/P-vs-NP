/-
  Constructive witness and refutation certificates for the finite SAT benchmarks.
  Each `solveSAT` result is the mask already decided by `findMaskAux` in
  `Schaefer.lean`. These are exhaustive checks of five concrete formulas.
  They are not a polynomial-time algorithm for general SAT, and they do not
  prove `P = NP`. `P_eq_NP` stays an open proposition.
-/
import Benchmarks
import Schaefer

namespace Benchmarks

/-! `solveSAT` returns `assignOfMask` of the mask `findMaskAux` already found. -/

theorem horn_sat_00_solveSAT :
    solveSAT 4 horn_sat_00 = some (assignOfMask 7) := by
  unfold solveSAT
  rw [show (2 : ℕ) ^ 4 = 16 by decide]
  rw [horn_sat_00_mask]
  rfl

theorem deceptive_trap_4v_solveSAT :
    solveSAT 4 deceptive_trap_4v = some (assignOfMask 10) := by
  unfold solveSAT
  rw [show (2 : ℕ) ^ 4 = 16 by decide]
  rw [deceptive_trap_mask]
  rfl

theorem cook_levin_gadget_3v_solveSAT :
    solveSAT 3 cook_levin_gadget_3v = some (assignOfMask 7) := by
  unfold solveSAT
  rw [show (2 : ℕ) ^ 3 = 8 by decide]
  rw [cook_levin_extracted_mask]
  rfl

theorem phase_transition_5v_solveSAT :
    solveSAT 5 phase_transition_5v = some (assignOfMask 11) := by
  unfold solveSAT
  rw [show (2 : ℕ) ^ 5 = 32 by decide]
  rw [phase_transition_mask]
  rfl

theorem unsat_core_3v_solveSAT :
    solveSAT 3 unsat_core_3v = none := by
  unfold solveSAT
  rw [show (2 : ℕ) ^ 3 = 8 by decide]
  rw [unsat_core_refutes]
  rfl

/-- Five instances of `solveSAT_extracts_witness_or_refutes`: a satisfying
assignment, or a refutation of every mask below `2^n`. -/
theorem witness_cert_or_refute :
    ((∃ a, solveSAT 4 deceptive_trap_4v = some a ∧
        evalCNF deceptive_trap_4v a = true) ∨
      (solveSAT 4 deceptive_trap_4v = none ∧
        ∀ m, m < 2 ^ 4 → evalCNF deceptive_trap_4v (assignOfMask m) = false)) ∧
    ((∃ a, solveSAT 3 cook_levin_gadget_3v = some a ∧
        evalCNF cook_levin_gadget_3v a = true) ∨
      (solveSAT 3 cook_levin_gadget_3v = none ∧
        ∀ m, m < 2 ^ 3 → evalCNF cook_levin_gadget_3v (assignOfMask m) = false)) ∧
    ((∃ a, solveSAT 5 phase_transition_5v = some a ∧
        evalCNF phase_transition_5v a = true) ∨
      (solveSAT 5 phase_transition_5v = none ∧
        ∀ m, m < 2 ^ 5 → evalCNF phase_transition_5v (assignOfMask m) = false)) ∧
    ((∃ a, solveSAT 3 unsat_core_3v = some a ∧
        evalCNF unsat_core_3v a = true) ∨
      (solveSAT 3 unsat_core_3v = none ∧
        ∀ m, m < 2 ^ 3 → evalCNF unsat_core_3v (assignOfMask m) = false)) ∧
    ((∃ a, solveSAT 4 horn_sat_00 = some a ∧
        evalCNF horn_sat_00 a = true) ∨
      (solveSAT 4 horn_sat_00 = none ∧
        ∀ m, m < 2 ^ 4 → evalCNF horn_sat_00 (assignOfMask m) = false)) :=
  ⟨solveSAT_extracts_witness_or_refutes 4 deceptive_trap_4v,
    solveSAT_extracts_witness_or_refutes 3 cook_levin_gadget_3v,
    solveSAT_extracts_witness_or_refutes 5 phase_transition_5v,
    solveSAT_extracts_witness_or_refutes 3 unsat_core_3v,
    solveSAT_extracts_witness_or_refutes 4 horn_sat_00⟩

end Benchmarks

#print axioms Benchmarks.horn_sat_00_solveSAT
#print axioms Benchmarks.deceptive_trap_4v_solveSAT
#print axioms Benchmarks.cook_levin_gadget_3v_solveSAT
#print axioms Benchmarks.phase_transition_5v_solveSAT
#print axioms Benchmarks.unsat_core_3v_solveSAT
#print axioms Benchmarks.witness_cert_or_refute
