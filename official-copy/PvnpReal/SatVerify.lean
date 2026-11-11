/-
  PvnpReal.SatVerify — a purely functional, one-pass verifier for SAT, and the proof that
  it is correct:

    SATLang x ↔ ∃ w, |w| ≤ |x| ∧ verify x w = true.

  `verify` reads `x` left to right, one bit at a time, with finitely many flags plus a counter
  (the unary variable index being read). The Turing machine in `PvnpReal.SatMachine` simulates
  exactly this procedure.
-/
import PvnpReal.Sat

set_option linter.unusedSimpArgs false

namespace PvnpReal

/-- Parsing modes: expecting a clause or the end of the formula (`F`), expecting a literal or
the end of a clause (`C`), expecting a sign bit (`S`), reading a unary variable index (`V`). -/
inductive Mode | F | C | S | V
  deriving DecidableEq

/-- The assignment given by a witness string: variable `v` gets bit `w[v]`, and `false`
if `w` is too short. -/
def asg (w : List Bool) (v : ℕ) : Bool := w.getD v false

/-- One pass over the input. Arguments: witness, mode, `fok` (all finished clauses true so far),
`cok` (current clause has a true literal), `ng` (sign of the current literal), `c` (unary count). -/
def run (w : List Bool) : Mode → Bool → Bool → Bool → ℕ → List Bool → Bool
  | .F, _, _, _, _, [] => false
  | .F, fok, _, _, _, false :: r => fok && r.isEmpty
  | .F, fok, _, _, _, true :: r => run w .C fok false false 0 r
  | .C, _, _, _, _, [] => false
  | .C, fok, cok, _, _, false :: r => run w .F (fok && cok) false false 0 r
  | .C, fok, cok, _, _, true :: r => run w .S fok cok false 0 r
  | .S, _, _, _, _, [] => false
  | .S, fok, cok, _, _, b :: r => run w .V fok cok b 0 r
  | .V, _, _, _, _, [] => false
  | .V, fok, cok, ng, c, true :: r => run w .V fok cok ng (c + 1) r
  | .V, fok, cok, ng, c, false :: r => run w .C fok (cok || (ng != asg w c)) false 0 r

/-- The verifier: run in mode `F` with `fok = true`. -/
def verify (x w : List Bool) : Bool := run w .F true false false 0 x

theorem evalLiteral_eq (l : Literal) (a : ℕ → Bool) :
    evalLiteral l a = (l.neg != a l.var) := by
  rcases l with ⟨v, n⟩; cases n <;> cases h : a v <;> simp [evalLiteral, h]

/-- Sanity checks, by evaluation: `x0` with `x0 := true` is accepted, with `x0 := false`
rejected; `x0 ∧ ¬x0` is rejected under both assignments; a non-code is rejected. -/
theorem verify_ex1 : verify (encodeCNF [[⟨0, false⟩]]) [true] = true := rfl
theorem verify_ex2 : verify (encodeCNF [[⟨0, false⟩]]) [false] = false := rfl
theorem verify_ex3 : verify (encodeCNF [[⟨0, false⟩], [⟨0, true⟩]]) [true] = false := rfl
theorem verify_ex4 : verify (encodeCNF [[⟨0, false⟩], [⟨0, true⟩]]) [false] = false := rfl
theorem verify_ex5 : verify [true, true] [true] = false := rfl

/-! ### Completeness: on a code, `run` computes `evalCNF` -/

theorem run_V (w : List Bool) (fok cok ng : Bool) (c k : ℕ) (r : List Bool) :
    run w .V fok cok ng c (List.replicate k true ++ false :: r) =
      run w .C fok (cok || (ng != asg w (c + k))) false 0 r := by
  induction k generalizing c with
  | zero => simp [run]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, run, ih, show c + 1 + k = c + (k + 1) by omega]

theorem run_lit (w : List Bool) (fok cok ng : Bool) (c : ℕ) (l : Literal) (r : List Bool) :
    run w .S fok cok ng c (encLit l ++ r) =
      run w .C fok (cok || evalLiteral l (asg w)) false 0 r := by
  simp only [encLit, encVar, List.cons_append, List.append_assoc, List.singleton_append, run,
    run_V, evalLiteral_eq, zero_add, List.nil_append]

theorem run_clause (w : List Bool) (fok cok ng : Bool) (c : ℕ) (cl : Clause) (r : List Bool) :
    run w .C fok cok ng c (encList encLit cl ++ r) =
      run w .F (fok && (cok || evalClause cl (asg w))) false false 0 r := by
  induction cl generalizing cok ng c with
  | nil => simp [encList, run, evalClause]
  | cons l cl ih =>
    simp only [encList, List.cons_append, List.append_assoc, run, run_lit, ih]
    simp [evalClause, Bool.or_assoc]

theorem run_cnf (w : List Bool) (fok cok ng : Bool) (c : ℕ) (φ : CNF) (r : List Bool) :
    run w .F fok cok ng c (encodeCNF φ ++ r) = (fok && evalCNF φ (asg w) && r.isEmpty) := by
  induction φ generalizing fok cok ng c with
  | nil => simp [encodeCNF, encList, run, evalCNF]
  | cons cl φ ih =>
    have := ih (fok && (false || evalClause cl (asg w))) false false 0
    simp only [encodeCNF] at this ⊢
    simp only [encList, List.cons_append, List.append_assoc, run, run_clause, this]
    simp [evalCNF, Bool.and_assoc]

theorem verify_encode (φ : CNF) (w : List Bool) :
    verify (encodeCNF φ) w = evalCNF φ (asg w) := by
  have := run_cnf w true false false 0 φ []
  simpa [verify] using this

/-! ### Soundness: if `run` accepts, the input is a code of a formula it satisfies -/

theorem run_V_sound (w : List Bool) (fok cok ng : Bool) (c : ℕ) (x : List Bool)
    (h : run w .V fok cok ng c x = true) :
    ∃ k r, x = List.replicate k true ++ false :: r ∧
      run w .C fok (cok || (ng != asg w (c + k))) false 0 r = true := by
  induction x generalizing c with
  | nil => simp [run] at h
  | cons b x ih =>
    cases b with
    | false => exact ⟨0, x, rfl, by simpa [run] using h⟩
    | true =>
      obtain ⟨k, r, rfl, hr⟩ := ih (c + 1) (by simpa [run] using h)
      exact ⟨k + 1, r, by simp [List.replicate_succ],
        by rw [show c + (k + 1) = c + 1 + k by omega]; exact hr⟩

theorem run_C_sound (w : List Bool) (n : ℕ) : ∀ (x : List Bool), x.length ≤ n →
    ∀ (fok cok ng : Bool) (c : ℕ), run w .C fok cok ng c x = true →
    ∃ cl r, x = encList encLit cl ++ r ∧
      run w .F (fok && (cok || evalClause cl (asg w))) false false 0 r = true := by
  induction n with
  | zero =>
    intro x hx fok cok ng c h
    rcases x with _ | ⟨b, x⟩
    · simp [run] at h
    · simp at hx
  | succ n ih =>
    intro x hx fok cok ng c h
    rcases x with _ | ⟨b, x⟩
    · simp [run] at h
    cases b with
    | false => exact ⟨[], x, rfl, by simpa [run, evalClause] using h⟩
    | true =>
      rcases x with _ | ⟨sgn, x⟩
      · simp [run] at h
      simp only [run] at h
      obtain ⟨k, r, rfl, hr⟩ := run_V_sound w fok cok sgn 0 x h
      have hlen : r.length ≤ n := by simp at hx; omega
      obtain ⟨cl, r', rfl, hr'⟩ := ih r hlen _ _ _ _ hr
      refine ⟨⟨k, sgn⟩ :: cl, r', ?_, ?_⟩
      · simp [encList, encLit, encVar]
      · rw [← hr']
        simp [evalClause, evalLiteral_eq, asg, Bool.or_assoc]

theorem run_F_sound (w : List Bool) (n : ℕ) : ∀ (x : List Bool), x.length ≤ n →
    ∀ (fok cok ng : Bool) (c : ℕ), run w .F fok cok ng c x = true →
    ∃ φ, x = encodeCNF φ ∧ fok = true ∧ evalCNF φ (asg w) = true := by
  induction n with
  | zero =>
    intro x hx fok cok ng c h
    rcases x with _ | ⟨b, x⟩
    · simp [run] at h
    · simp at hx
  | succ n ih =>
    intro x hx fok cok ng c h
    rcases x with _ | ⟨b, x⟩
    · simp [run] at h
    cases b with
    | false =>
      simp only [run, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨hf, rfl⟩ := h
      exact ⟨[], rfl, hf, rfl⟩
    | true =>
      simp only [run] at h
      obtain ⟨cl, r, rfl, hr⟩ := run_C_sound w x.length _ le_rfl _ _ _ _ h
      have hlen : r.length ≤ n := by simp at hx; omega
      obtain ⟨φ, rfl, hf, hφ⟩ := ih r hlen _ _ _ _ hr
      simp only [Bool.false_or, Bool.and_eq_true] at hf
      refine ⟨cl :: φ, rfl, hf.1, ?_⟩
      simp [evalCNF, hf.2, hφ]
      simpa [evalCNF] using hφ

theorem verify_sound (x w : List Bool) (h : verify x w = true) :
    ∃ φ, x = encodeCNF φ ∧ evalCNF φ (asg w) = true := by
  obtain ⟨φ, h1, -, h2⟩ := run_F_sound w x.length x le_rfl _ _ _ _ h
  exact ⟨φ, h1, h2⟩

/-! ### Short witnesses suffice -/

theorem encLit_infix_clause (l : Literal) (cl : Clause) (h : l ∈ cl) :
    encLit l <:+: encList encLit cl := by
  induction cl with
  | nil => simp at h
  | cons l' cl ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨[true], encList encLit cl, by simp [encList]⟩
    · obtain ⟨s, t, hst⟩ := ih h
      exact ⟨true :: encLit l' ++ s, t, by simp [encList, ← hst]⟩

theorem clause_infix_cnf (cl : Clause) (φ : CNF) (h : cl ∈ φ) :
    encList encLit cl <:+: encodeCNF φ := by
  induction φ with
  | nil => simp at h
  | cons cl' φ ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨[true], encodeCNF φ, by simp [encodeCNF, encList]⟩
    · obtain ⟨s, t, hst⟩ := ih h
      exact ⟨true :: encList encLit cl' ++ s, t, by simp [encodeCNF, encList, ← hst] at *; simp [hst]⟩

/-- Every variable index occurring in `φ` is smaller than the length of the code of `φ`. -/
theorem var_lt_length (φ : CNF) (cl : Clause) (hcl : cl ∈ φ) (l : Literal) (hl : l ∈ cl) :
    l.var < (encodeCNF φ).length := by
  have h1 := ((encLit_infix_clause l cl hl).trans (clause_infix_cnf cl φ hcl)).length_le
  simp [encLit, encVar] at h1
  omega

theorem evalClause_congr (cl : Clause) (a b : ℕ → Bool)
    (h : ∀ l ∈ cl, a l.var = b l.var) : evalClause cl a = evalClause cl b := by
  induction cl with
  | nil => rfl
  | cons l cl ih =>
    simp only [evalClause, List.any_cons] at *
    rw [ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    simp [evalLiteral, h l List.mem_cons_self]

theorem evalCNF_congr (φ : CNF) (a b : ℕ → Bool)
    (h : ∀ cl ∈ φ, ∀ l ∈ cl, a l.var = b l.var) : evalCNF φ a = evalCNF φ b := by
  induction φ with
  | nil => rfl
  | cons cl φ ih =>
    simp only [evalCNF, List.all_cons] at *
    rw [ih (fun cl' hcl' => h cl' (List.mem_cons_of_mem _ hcl')),
      evalClause_congr cl a b (h cl List.mem_cons_self)]

/-- **Correctness of the verifier.** -/
theorem SATLang_iff_verify (x : List Bool) :
    SATLang x ↔ ∃ w : List Bool, w.length ≤ x.length ∧ verify x w = true := by
  constructor
  · rintro ⟨φ, rfl, a, ha⟩
    refine ⟨(List.range (encodeCNF φ).length).map a, by simp, ?_⟩
    rw [verify_encode, ← ha]
    apply evalCNF_congr
    intro cl hcl l hl
    have := var_lt_length φ cl hcl l hl
    simp [asg, List.getD_eq_getElem?_getD, this]
  · rintro ⟨w, -, h⟩
    obtain ⟨φ, rfl, hφ⟩ := verify_sound x w h
    exact (SATLang_encode_iff φ).2 ⟨asg w, hφ⟩

end PvnpReal
