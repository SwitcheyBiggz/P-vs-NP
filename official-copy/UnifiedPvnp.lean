/-
  ======================================================================
  UnifiedPvnp.lean: Grand-Unified Formalization of P vs NP & Complexity
  ======================================================================
  A clean, self-contained, publication-ready formalization consolidating
  all proven results across the 109 modules of `PvnpReal` and `Benchmarks`
  into namespace `UnifiedPvnp` (with zero custom axioms):

  * Section 1: Faithful Complexity Classes on `Turing.FinTM2`
      (InP, InNP, InEXP, InCoNP, P ⊆ NP, P ⊆ EXP, P ⊆ coNP, NP ⊆ EXP, coNP ⊆ EXP)
  * Section 2: Faithful Open Proposition `P_eq_NP`
  * Section 3: Complete Structural Reductions around P vs NP & coNP
  * Section 4: Unconditional Cook–Levin Theorem
  * Section 5: Baker–Gill–Solovay Relativization Barrier
  * Section 6: Razborov–Rudich Natural Proofs Barrier
  * Section 7: Ladner's Theorem (NP & coNP Intermediate Languages)
  * Section 8: Time Hierarchies & Classical Diagonalization (P ≠ EXP, O(n⁴²), O(n¹⁶⁸⁽ʲ⁺¹⁾))
  * Section 9: Space Complexity, PSPACE Completeness & Savitch's Theorem (NPSPACE = PSPACE)
  * Section 10: Polynomial Hierarchy (PH, Σ_k, Π_k, PH ⊆ PSPACE, General Collapse & Σ_k-SAT Completeness)
  * Section 11: Non-Uniform Complexity (`P/poly`, Circuits, Karp–Lipton, Undecidability & Kannan's Theorem)
  * Section 12: Randomized Complexity (`BPP`, `RP`, `coRP`, `ZPP`, Adleman, SGL & `NP ⊆ BPP ⇒ NP = RP`)
  * Section 13: Unconditional Boolean & Polynomial-Reduction Closures
  * Section 14: Machine-Verified Concrete Computational Benchmarks
-/

import PvnpReal
import Benchmarks

set_option linter.unusedSimpArgs false

namespace UnifiedPvnp

open Classical

-- ============================================================
-- SECTION 1: FAITHFUL COMPLEXITY CLASSES ON Turing.FinTM2
-- ============================================================

/-- A language (decision problem) over the binary alphabet `List Bool`. -/
abbrev Language : Type := PvnpReal.Language

/-- **P**: Languages decidable in polynomial time by a `FinTM2` multi-stack Turing machine. -/
def InP (L : Language) : Prop := PvnpReal.InP L

/-- **NP**: Languages verifiable in polynomial time with polynomial-length certificates. -/
def InNP (L : Language) : Prop := PvnpReal.InNP L

/-- **EXP**: Languages decidable in exponential time `2^(p(|x|))` by a `FinTM2` machine. -/
def InEXP (L : Language) : Prop := PvnpReal.InEXP L

/-- **coNP**: Languages whose complement is in `NP`. -/
def InCoNP (L : Language) : Prop := PvnpReal.InCoNP L

/-- Unconditional inclusion `P ⊆ NP` over Mathlib's `FinTM2` Turing machines. -/
theorem P_subset_NP (L : Language) (h : InP L) : InNP L :=
  PvnpReal.P_subset_NP L h

/-- Unconditional inclusion `P ⊆ EXP` over Mathlib's `FinTM2` Turing machines. -/
theorem P_subset_EXP (L : Language) (h : InP L) : InEXP L :=
  PvnpReal.P_subset_EXP L h

/-- Unconditional inclusion `P ⊆ coNP` (`InP L → InCoNP L`). -/
theorem P_subset_coNP (L : Language) (h : InP L) : InCoNP L :=
  PvnpReal.P_subset_coNP L h

/-- Unconditional inclusion `NP ⊆ EXP` (via brute-force search over the certificate space). -/
theorem NP_subset_EXP (L : Language) (h : InNP L) : InEXP L :=
  PvnpReal.NP_subset_EXP L h

/-- Unconditional inclusion `coNP ⊆ EXP` (since `EXP` is closed under complement). -/
theorem coNP_subset_EXP (L : Language) (h : InCoNP L) : InEXP L := by
  obtain ⟨f, p, hf, hL⟩ := PvnpReal.InEXP.compl (NP_subset_EXP _ h)
  exact ⟨f, p, hf, fun x => not_not.symm.trans (hL x)⟩

/-- Empty language is in P. -/
theorem empty_in_P : InP (fun _ => False) := PvnpReal.empty_in_P

/-- Universal language is in P. -/
theorem univ_in_P : InP (fun _ => True) := PvnpReal.univ_in_P

/-- Empty language is in NP. -/
theorem empty_in_NP : InNP (fun _ => False) := PvnpReal.empty_in_NP

/-- Universal language is in NP. -/
theorem univ_in_NP : InNP (fun _ => True) := PvnpReal.univ_in_NP

-- ============================================================
-- SECTION 2: FAITHFUL OPEN PROPOSITION P_eq_NP
-- ============================================================

/-- The P vs NP Clay Millennium Problem stated as a faithful open proposition. -/
def P_eq_NP : Prop := ∀ L : Language, InP L ↔ InNP L

/-- The standard conjecture P ≠ NP. -/
def P_ne_NP : Prop := ¬ P_eq_NP

theorem P_eq_NP_def : P_eq_NP ↔ PvnpReal.P_eq_NP := Iff.rfl

-- ============================================================
-- SECTION 3: COMPLETE STRUCTURAL REDUCTIONS AROUND P VS NP
-- ============================================================

/-- The canonical propositional satisfiability language on Turing machines. -/
def SATLang : Language := PvnpReal.SATLang

/-- The canonical propositional unsatisfiability language (complement of SAT). -/
def UNSATLang : Language := fun x => ¬ SATLang x

/-- Polynomial-time many-one (Karp) reduction between languages. -/
def PolyReduces (L L' : Language) : Prop := PvnpReal.PolyReduces L L'

/-- NP-hardness: every NP language polynomial-time reduces to `L`. -/
def NPHard (L : Language) : Prop := PvnpReal.NPHard L

/-- NP-completeness: `L ∈ NP` and `L` is NP-hard. -/
def NPComplete (L : Language) : Prop := PvnpReal.NPComplete L

/-- coNP-hardness: every coNP language polynomial-time reduces to `L`. -/
def CoNPHard (L : Language) : Prop := ∀ L' : Language, InCoNP L' → PolyReduces L' L

/-- coNP-completeness: `L ∈ coNP` and `L` is coNP-hard. -/
def CoNPComplete (L : Language) : Prop := InCoNP L ∧ CoNPHard L

/-- Polynomial-time reductions commute with complementation. -/
theorem PolyReduces_compl {L L' : Language} (hr : PolyReduces L L') :
    PolyReduces (fun x => ¬ L x) (fun x => ¬ L' x) := by
  obtain ⟨g, hg, hL⟩ := hr
  exact ⟨g, hg, fun x => not_congr (hL x)⟩

/-- `L ∈ NP` iff `L` polynomial-time reduces to SAT. -/
theorem InNP_iff_reduces_SAT (L : Language) : InNP L ↔ PolyReduces L SATLang :=
  PvnpReal.InNP_iff_reduces_SAT L

/-- `NP ⊆ EXP` iff `SAT ∈ EXP`. -/
theorem NP_subset_EXP_iff_SAT_in_EXP : (∀ L, InNP L → InEXP L) ↔ InEXP SATLang :=
  PvnpReal.NP_subset_EXP_iff_SAT_in_EXP

/-- NP-completeness propagates along polynomial-time reductions. -/
theorem NPComplete_of_reduces {L L' : Language} (h : NPComplete L) (hL' : InNP L')
    (hr : PolyReduces L L') : NPComplete L' :=
  PvnpReal.NPComplete.of_reduces h hL' hr

/-- The complement of any NP-complete language is coNP-complete. -/
theorem CoNPComplete_of_NPComplete {L : Language} (h : NPComplete L) :
    CoNPComplete (fun x => ¬ L x) := by
  refine ⟨?_, fun L' hL' => ?_⟩
  · obtain ⟨V, q, hV, hL⟩ := h.1
    exact ⟨V, q, hV, fun x => not_not.trans (hL x)⟩
  · obtain ⟨g, hg, hred⟩ := h.2 (fun x => ¬ L' x) hL'
    exact ⟨g, hg, fun x => (not_not (a := L' x)).symm.trans (not_congr (hred x))⟩

/-- Dual characterization: `(¬ L)` is coNP-complete iff `L` is NP-complete. -/
theorem CoNPComplete_compl_iff_NPComplete (L : Language) :
    CoNPComplete (fun x => ¬ L x) ↔ NPComplete L := by
  constructor
  · rintro ⟨hC, hH⟩
    refine ⟨?_, fun L' hL' => ?_⟩
    · obtain ⟨V, q, hV, hL⟩ := hC
      exact ⟨V, q, hV, fun x => not_not.symm.trans (hL x)⟩
    · obtain ⟨V', q', hV', hL''⟩ := hL'
      have hCo : InCoNP (fun x => ¬ L' x) := ⟨V', q', hV', fun x => not_not.trans (hL'' x)⟩
      obtain ⟨g, hg, hred⟩ := hH (fun x => ¬ L' x) hCo
      exact ⟨g, hg, fun x => not_iff_not.mp (hred x)⟩
  · exact CoNPComplete_of_NPComplete

/-- UNSAT is in coNP. -/
theorem UNSAT_in_coNP : InCoNP UNSATLang := by
  obtain ⟨V, q, hV, hS⟩ := PvnpReal.SAT_in_NP
  exact ⟨V, q, hV, fun x => not_not.trans (hS x)⟩

/-- UNSAT is coNP-hard. -/
theorem UNSAT_CoNPHard : CoNPHard UNSATLang := by
  intro L hL
  obtain ⟨g, hg, hred⟩ := PvnpReal.SAT_NPHard (fun x => ¬ L x) hL
  exact ⟨g, hg, fun x => (not_not (a := L x)).symm.trans (not_congr (hred x))⟩

/-- UNSAT is coNP-complete. -/
theorem UNSAT_CoNPComplete : CoNPComplete UNSATLang :=
  ⟨UNSAT_in_coNP, UNSAT_CoNPHard⟩

/-- Structural equivalence: `P = NP` iff SAT is solvable in polynomial time. -/
theorem P_eq_NP_iff_SAT_in_P : P_eq_NP ↔ InP SATLang :=
  PvnpReal.P_eq_NP_iff_SAT_in_P

/-- Structural equivalence: `P = NP` iff UNSAT is solvable in polynomial time. -/
theorem P_eq_NP_iff_UNSAT_in_P : P_eq_NP ↔ InP UNSATLang := by
  rw [P_eq_NP_iff_SAT_in_P]
  constructor
  · intro h; exact PvnpReal.InP.compl h
  · intro h; exact (PvnpReal.InP.compl h).congr (fun x => not_not)

/-- Structural equivalence: `P = NP` iff some NP-complete language is in `P`. -/
theorem P_eq_NP_iff_exists_NPComplete_in_P : P_eq_NP ↔ ∃ L, NPComplete L ∧ InP L :=
  PvnpReal.P_eq_NP_iff_exists_NPComplete_in_P

/-- Structural equivalence: `P = NP` iff all NP-complete languages are in `P`. -/
theorem P_eq_NP_iff_all_NPComplete_in_P : P_eq_NP ↔ ∀ L, NPComplete L → InP L :=
  PvnpReal.P_eq_NP_iff_all_NPComplete_in_P

/-- Contrapositive: `P ≠ NP` iff SAT is not solvable in polynomial time. -/
theorem P_ne_NP_iff_SAT_not_in_P : ¬ P_eq_NP ↔ ¬ InP SATLang :=
  PvnpReal.P_ne_NP_iff_SAT_not_in_P

/-- Contrapositive: `P ≠ NP` iff no NP-complete language is in `P`. -/
theorem P_ne_NP_iff_no_NPComplete_in_P : ¬ P_eq_NP ↔ ∀ L, NPComplete L → ¬ InP L :=
  PvnpReal.P_ne_NP_iff_no_NPComplete_in_P

/-- Structural equivalence: `P = NP` iff `NP ⊆ P`. -/
theorem P_eq_NP_iff_NP_subset_P : P_eq_NP ↔ ∀ L, InNP L → InP L :=
  PvnpReal.P_eq_NP_iff_NP_subset_P

/-- If `P = NP`, then `NP = coNP`. -/
theorem NP_eq_coNP_of_P_eq_NP (h : P_eq_NP) : ∀ L : Language, InNP L ↔ InCoNP L :=
  PvnpReal.NP_eq_coNP_of_P_eq_NP h

/-- Contrapositive: if `NP ≠ coNP`, then `P ≠ NP`. -/
theorem P_ne_NP_of_NP_ne_coNP (h : ¬ ∀ L : Language, InNP L ↔ InCoNP L) : ¬ P_eq_NP :=
  PvnpReal.P_ne_NP_of_NP_ne_coNP h

/-- `NP = coNP` iff SAT ∈ coNP. -/
theorem NP_eq_coNP_iff_SAT_in_coNP :
    (∀ L : Language, InNP L ↔ InCoNP L) ↔ InCoNP SATLang := by
  constructor
  · intro h; exact (h SATLang).1 PvnpReal.SAT_in_NP
  · intro hS L
    constructor
    · intro hL
      exact PvnpReal.InNP.of_reduces (PolyReduces_compl (PvnpReal.SAT_NPHard L hL)) hS
    · intro hL
      have hr : PolyReduces (fun x => ¬ L x) SATLang := PvnpReal.SAT_NPHard _ hL
      have hnn : InNP (fun x => ¬ ¬ L x) := PvnpReal.InNP.of_reduces (PolyReduces_compl hr) hS
      obtain ⟨V, q, hV, hVspec⟩ := hnn
      exact ⟨V, q, hV, fun x => not_not.symm.trans (hVspec x)⟩

/-- `NP = coNP` iff UNSAT ∈ NP. -/
theorem NP_eq_coNP_iff_UNSAT_in_NP :
    (∀ L : Language, InNP L ↔ InCoNP L) ↔ InNP UNSATLang := by
  constructor
  · intro h; exact (h UNSATLang).2 UNSAT_in_coNP
  · intro hU
    exact NP_eq_coNP_iff_SAT_in_coNP.2 (by
      obtain ⟨V, q, hV, hS⟩ := hU
      exact ⟨V, q, hV, fun x => hS x⟩)

/-- If `P ≠ EXP`, then either `P ≠ NP` or `NP ≠ EXP`. -/
theorem P_ne_EXP_imp_P_ne_NP_or_NP_ne_EXP (h : ∃ L : Language, InEXP L ∧ ¬ InP L) :
    ¬ P_eq_NP ∨ (∃ L : Language, InEXP L ∧ ¬ InNP L) := by
  by_cases hP : P_eq_NP
  · obtain ⟨L, hE, hnP⟩ := h
    exact Or.inr ⟨L, hE, fun hNP => hnP ((hP L).2 hNP)⟩
  · exact Or.inl hP

-- ============================================================
-- SECTION 4: UNCONDITIONAL COOK–LEVIN THEOREM
-- ============================================================

/-- Unconditional Cook–Levin Theorem: SAT is NP-complete. -/
theorem cookLevin : PvnpReal.CookLevinStatement :=
  PvnpReal.cookLevin

/-- SAT is NP-hard: every language in NP polynomial-time reduces to SAT. -/
theorem SAT_NPHard : NPHard SATLang :=
  PvnpReal.SAT_NPHard

/-- SAT is NP-complete. -/
theorem SAT_NPComplete : NPComplete SATLang :=
  PvnpReal.SAT_NPComplete

-- ============================================================
-- SECTION 5: BAKER–GILL–SOLOVAY RELATIVIZATION BARRIER
-- ============================================================

/-- Relativized polynomial time with oracle `A`. -/
def InPO (A : Language) (L : Language) : Prop := PvnpReal.InPO A L

/-- Relativized non-deterministic polynomial time with oracle `A`. -/
def InNPO (A : Language) (L : Language) : Prop := PvnpReal.InNPO A L

/-- Every language in `P^A` is in `NP^A`. -/
theorem InPO.toNPO {A L : Language} (h : InPO A L) : InNPO A L :=
  PvnpReal.InPO.toNPO h

/-- There exists an oracle `A` relative to which `P^A = NP^A`. -/
theorem exists_oracle_P_eq_NP : ∃ A : Language, ∀ L, InPO A L ↔ InNPO A L :=
  PvnpReal.exists_oracle_P_eq_NP

/-- There exists an oracle `B` relative to which `P^B ≠ NP^B`. -/
theorem exists_oracle_P_ne_NP : ∃ B : Language, ∃ L, InNPO B L ∧ ¬ InPO B L :=
  PvnpReal.exists_oracle_P_ne_NP

/-- The Baker–Gill–Solovay Barrier: there exists an oracle `A` relative to which
    `P^A = NP^A`, and an oracle `B` relative to which `P^B ≠ NP^B`. -/
theorem baker_gill_solovay :
    (∃ A : Language, ∀ L, InPO A L ↔ InNPO A L) ∧
    (∃ B : Language, ∃ L, InNPO B L ∧ ¬ InPO B L) :=
  PvnpReal.baker_gill_solovay

/-- Unrelativized P embeds into P relative to any oracle. -/
theorem P_sub_PO (A L : Language) (hL : InP L) : InPO A L :=
  PvnpReal.P_sub_PO A L hL

/-- Unrelativized NP embeds into NP relative to any oracle. -/
theorem NP_sub_NPO (A L : Language) (hL : InNP L) : InNPO A L :=
  PvnpReal.NP_sub_NPO A L hL

-- ============================================================
-- SECTION 6: RAZBOROV–RUDICH NATURAL PROOFS BARRIER
-- ============================================================

/-- Circuit Counting Lemma: number of Boolean functions computed by size-s circuits. -/
theorem card_hasCircuit_le (n s : ℕ) :
    (Finset.univ.filter (PvnpReal.HasCircuit n s)).card ≤ (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s + 1)) :=
  PvnpReal.card_hasCircuit_le n s

/-- Super-polynomial circuit lower bounds exist unconditionally (Shannon counting). -/
theorem exists_superpoly_hard (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∃ f : PvnpReal.BFun n, ¬ PvnpReal.HasCircuit n (n ^ k) f :=
  PvnpReal.exists_superpoly_hard k

/-- The Razborov–Rudich Natural Proofs Barrier: if strong pseudorandom functions
    exist, no natural property can prove super-polynomial circuit lower bounds. -/
theorem razborov_rudich (h : ∃ F : PvnpReal.PRF, PvnpReal.Secure PvnpReal.Constructive F) :
    ∀ Pr : PvnpReal.CProp, ¬ PvnpReal.Natural Pr :=
  PvnpReal.razborov_rudich h

/-- Razborov–Rudich Natural Proofs Barrier for circuit-constructible properties. -/
theorem razborov_rudich_circuit (h : ∃ F : PvnpReal.PRF, PvnpReal.Secure PvnpReal.ConstructiveC F) :
    ∀ Pr : PvnpReal.CProp, ¬ PvnpReal.NaturalC Pr :=
  PvnpReal.razborov_rudich_circuit h

/-- Under pseudorandom functions, exact circuit hardness is not constructive. -/
theorem hard_not_constructive (h : ∃ F : PvnpReal.PRF, PvnpReal.Secure PvnpReal.Constructive F) :
    ¬ PvnpReal.Constructive PvnpReal.Hard :=
  PvnpReal.hard_not_constructive h

/-- Under circuit-secure pseudorandom functions, exact circuit hardness is not circuit-constructive. -/
theorem hard_not_constructiveC (h : ∃ F : PvnpReal.PRF, PvnpReal.Secure PvnpReal.ConstructiveC F) :
    ¬ PvnpReal.ConstructiveC PvnpReal.Hard :=
  PvnpReal.hard_not_constructiveC h

-- ============================================================
-- SECTION 7: LADNER'S THEOREM ON NP-INTERMEDIATE LANGUAGES
-- ============================================================

/-- Ladner's Theorem: If P ≠ NP, there exist NP-intermediate languages
    (in NP, but neither in P nor NP-complete). -/
theorem ladner (hPNP : ¬ P_eq_NP) :
    ∃ L : Language, InNP L ∧ ¬ InP L ∧ ¬ NPComplete L :=
  PvnpReal.ladner hPNP

/-- Dual Ladner Theorem for coNP: If P ≠ NP, there exist coNP-intermediate languages
    (in coNP, but neither in P nor coNP-complete). -/
theorem ladner_coNP (hPNP : ¬ P_eq_NP) :
    ∃ L : Language, InCoNP L ∧ ¬ InP L ∧ ¬ CoNPComplete L := by
  obtain ⟨L, hNP, hnP, hnC⟩ := ladner hPNP
  refine ⟨fun x => ¬ L x, ?_, ?_, ?_⟩
  · obtain ⟨V, q, hV, hL⟩ := hNP
    exact ⟨V, q, hV, fun x => not_not.trans (hL x)⟩
  · intro hp
    exact hnP ((PvnpReal.InP.compl hp).congr (fun x => not_not))
  · intro hC
    exact hnC ((CoNPComplete_compl_iff_NPComplete L).1 hC)

/-- Under P ≠ NP, NP splits into three non-empty strata: P, NP-intermediate, and NP-complete \ P. -/
theorem three_way_NP_partition_nonempty (hPNP : ¬ P_eq_NP) :
    (∃ L : Language, InP L ∧ InNP L) ∧
    (∃ L : Language, InNP L ∧ ¬ InP L ∧ ¬ NPComplete L) ∧
    (∃ L : Language, NPComplete L ∧ ¬ InP L) :=
  ⟨⟨fun _ => True, univ_in_P, univ_in_NP⟩,
   ladner hPNP,
   ⟨SATLang, SAT_NPComplete, (P_ne_NP_iff_SAT_not_in_P.1 hPNP)⟩⟩

-- ============================================================
-- SECTION 8: TIME HIERARCHIES & CLASSICAL DIAGONALIZATION
-- ============================================================

/-- Deterministic time class `DTIME(T)` on `FinTM2`. -/
def InDTIME (T : ℕ → ℕ) (L : Language) : Prop := PvnpReal.InDTIME T L

/-- Deterministic space class `DSPACE(S)` on `FinTM2`. -/
def InDSPACE (S : ℕ → ℕ) (L : Language) : Prop := PvnpReal.InDSPACE S L

/-- Unconditional separation of P from Exponential Time: `P ≠ EXP`. -/
theorem p_ne_exp : PvnpReal.P_ne_EXP :=
  PvnpReal.p_ne_exp

/-- Strict inclusion `P ⊊ EXP`. -/
theorem P_ssubset_EXP :
    (∀ L : Language, InP L → InEXP L) ∧ ∃ L : Language, InEXP L ∧ ¬ InP L :=
  ⟨P_subset_EXP, p_ne_exp⟩

/-- Clocked TM2 evaluator matches Mathlib step semantics within `t` steps. -/
theorem runFor_iff {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (t : ℕ) (c h : Turing.TM2.Cfg Γ Λ σ) :
    PvnpReal.runFor M t c = some h ↔
      h.l = none ∧ ∃ s ≤ t, (flip bind (Turing.TM2.step M))^[s] (some c) = some h :=
  PvnpReal.runFor_iff M t c h

/-- Clock monotonicity for `runFor`. -/
theorem runFor_mono {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {t t' : ℕ} (htt : t ≤ t') {c h : Turing.TM2.Cfg Γ Λ σ}
    (e : PvnpReal.runFor M t c = some h) : PvnpReal.runFor M t' c = some h :=
  PvnpReal.runFor_mono M htt e

/-- Halting configuration uniqueness on `TM2`. -/
theorem halt_unique {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {c h h' : Turing.TM2.Cfg Γ Λ σ} {s s' : ℕ}
    (e : (flip bind (Turing.TM2.step M))^[s] (some c) = some h) (hh : h.l = none)
    (e' : (flip bind (Turing.TM2.step M))^[s'] (some c) = some h') (hh' : h'.l = none) : h = h' :=
  PvnpReal.halt_unique M e hh e' hh'

open Turing TM2 Computability in
/-- Clocked evaluator agrees with any `TM2ComputableInTime`. -/
theorem runFor_computable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : Turing.TM2ComputableInTime ea eb f) (a : α) :
    PvnpReal.runFor h.tm.m (h.time (ea a).length)
        (initList h.tm (List.map h.inputAlphabet.invFun (ea a))) =
      some (haltList h.tm (List.map h.outputAlphabet.invFun (eb (f a)))) :=
  PvnpReal.runFor_computable h a

/-- Abstract diagonalization step for clocked interpreters. -/
theorem diag_step (run : List Bool → List Bool → ℕ → Option Bool) (T : ℕ → ℕ)
    (f : List Bool → Bool) (x : List Bool) (hx : run x x (T x.length) = some (f x)) :
    ¬ ((run x x (T x.length) ≠ some true) ↔ f x = true) :=
  PvnpReal.diag_step run T f x hx

/-- Time Hierarchy Theorem: strict separation of deterministic time classes. -/
theorem time_hierarchy : ∃ P : Polynomial ℕ, ∀ (t : ℕ → ℕ)
    (hp : Turing.TM2ComputableInTime PvnpReal.strEnc PvnpReal.strEnc (PvnpReal.padWith t)),
    InDTIME (fun n => hp.time n + 2 * (n + PvnpReal.pushTotal hp.tm * hp.time n) + 2 +
      P.eval (n + PvnpReal.pushTotal hp.tm * hp.time n)) (PvnpReal.diagT t) ∧
    ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (PvnpReal.diagT t) :=
  PvnpReal.time_hierarchy

/-- Universal-exponent time hierarchy theorem. -/
theorem time_hierarchy_pow : ∃ k : ℕ, 1 ≤ k ∧ ∀ (t : ℕ → ℕ)
    (hp : Turing.TM2ComputableInTime PvnpReal.strEnc PvnpReal.strEnc (PvnpReal.padWith t)) (A a : ℕ), 1 ≤ a →
    (∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) →
    ∃ K, InDTIME (fun n => K * (t n + n + 1) ^ (k * a)) (PvnpReal.diagT t) ∧
      ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (PvnpReal.diagT t) :=
  PvnpReal.time_hierarchy_pow

/-- Exponential time hierarchy instance. -/
theorem exp_time_hierarchy : ∃ k K : ℕ, ∃ L : Language,
    InDTIME (fun n => K * (2 ^ n + n + 1) ^ k) L ∧ ¬ InDTIME (fun n => 2 ^ n / (n + 1)) L :=
  PvnpReal.exp_time_hierarchy

/-- P is not contained in `DTIME(nᵏ)` for any fixed `k`. -/
theorem P_not_sub_DTIME_pow (k : ℕ) : ∃ L, InP L ∧ ¬ InDTIME (fun n => n ^ k) L :=
  PvnpReal.P_not_sub_DTIME_pow k

/-- `DTIME(nᵏ) ⊆ P`. -/
theorem DTIME_pow_sub_P (k : ℕ) (L : Language) (hL : InDTIME (fun n => n ^ k) L) : InP L :=
  PvnpReal.DTIME_pow_sub_P k L hL

/-- Strict inclusion `DTIME(nᵏ) ⊊ P` for every `k`. -/
theorem DTIME_pow_ssubset_P (k : ℕ) :
    (∀ L, InDTIME (fun n => n ^ k) L → InP L) ∧ ∃ L, InP L ∧ ¬ InDTIME (fun n => n ^ k) L :=
  PvnpReal.DTIME_pow_ssubset_P k

/-- Polynomial Gap Hierarchy: infinitely many polynomial time separations. -/
theorem poly_gap_hierarchy (k : ℕ) :
    ∃ e ≥ k, ∃ L : Language, InP L ∧
      InDTIME (fun n => (n + 2) ^ (e + 1)) L ∧
      ¬ InDTIME (fun n => n ^ e) L :=
  PvnpReal.poly_gap_hierarchy k

/-- `DTIME((n+2)^{e+1}) ⊊ DTIME(n^e)` fails for unboundedly many `e ≥ k`. -/
theorem poly_gap_infinitely_often (k : ℕ) :
    ∃ e ≥ k, ¬ ∀ L, InDTIME (fun n => (n + 2) ^ (e + 1)) L → InDTIME (fun n => n ^ e) L :=
  PvnpReal.poly_gap_infinitely_often k

/-- Explicit-gap time hierarchy theorem. -/
theorem time_hierarchy_gap (t : ℕ → ℕ)
    (hp : Turing.TM2ComputableInTime PvnpReal.strEnc PvnpReal.strEnc (PvnpReal.padWith t))
    (A a : ℕ) (ha : 1 ≤ a) (hA : ∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) :
    (∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (PvnpReal.diagT t)) ∧
    (InDTIME (fun n => (t n + n + 2) ^ 1) (PvnpReal.diagT t) ∨
      ∃ e ≥ 1, InDTIME (fun n => (t n + n + 2) ^ (e + 1)) (PvnpReal.diagT t) ∧
        ¬ InDTIME (fun n => (t n + n + 2) ^ e) (PvnpReal.diagT t)) :=
  PvnpReal.time_hierarchy_gap t hp A a ha hA

/-- Exponential explicit-gap hierarchy theorem. -/
theorem exp_time_hierarchy_gap :
    ¬ InDTIME (fun n => 2 ^ n / (n + 1)) (PvnpReal.diagT (fun n => 2 ^ n)) ∧
    (InDTIME (fun n => (2 ^ n + n + 2) ^ 1) (PvnpReal.diagT (fun n => 2 ^ n)) ∨
      ∃ e ≥ 1, InDTIME (fun n => (2 ^ n + n + 2) ^ (e + 1)) (PvnpReal.diagT (fun n => 2 ^ n)) ∧
        ¬ InDTIME (fun n => (2 ^ n + n + 2) ^ e) (PvnpReal.diagT (fun n => 2 ^ n))) :=
  PvnpReal.exp_time_hierarchy_gap

/-- Explicit O(n⁴²) Universal Interpreter Time Hierarchy Bound. -/
theorem time_hierarchy_42 (t : ℕ → ℕ) (hp : Turing.TM2ComputableInTime PvnpReal.strEnc PvnpReal.strEnc (PvnpReal.padWith t))
    (A a : ℕ) (ha : 1 ≤ a) (hA : ∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) :
    ∃ K, InDTIME (fun n => K * (t n + n + 1) ^ (a * 42)) (PvnpReal.diagT t) ∧
      ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (PvnpReal.diagT t) :=
  PvnpReal.time_hierarchy_42 t hp A a ha hA

/-- Explicit O((2^n)^42) exponential hierarchy instance. -/
theorem exp_time_hierarchy_42 : ∃ K, ∃ L : Language,
    InDTIME (fun n => K * (2 ^ n + n + 1) ^ 42) L ∧ ¬ InDTIME (fun n => 2 ^ n / (n + 1)) L :=
  PvnpReal.exp_time_hierarchy_42

/-- Explicit-exponent polynomial hierarchy `DTIME(n^j) ⊊ DTIME(K · (n+1)^{168(j+1)})`. -/
theorem poly_hierarchy_explicit (j : ℕ) : ∃ K, ∃ L : Language,
    InDTIME (fun n => K * (n + 1) ^ (168 * (j + 1))) L ∧ ¬ InDTIME (fun n => n ^ j) L :=
  PvnpReal.poly_hierarchy_explicit j

/-- Doubly exponential separation beating both `EXP` and `PSPACE`. -/
theorem double_exp_hierarchy : ∃ (c K : ℕ) (L : Language),
    InDTIME (fun n => K * (PvnpReal.t2 n + n + 1) ^ c) L ∧
    InDSPACE (fun n => K * (PvnpReal.t2 n + n + 1) ^ c) L ∧
    ¬ InEXP L ∧ ¬ PvnpReal.InPSPACE L :=
  PvnpReal.double_exp_hierarchy

-- ============================================================
-- SECTION 9: SPACE COMPLEXITY & PSPACE COMPLETENESS
-- ============================================================

/-- Languages decidable in polynomial space on `FinTM2`. -/
def InPSPACE (L : Language) : Prop := PvnpReal.InPSPACE L

/-- P = PSPACE question. -/
def P_eq_PSPACE : Prop := PvnpReal.P_eq_PSPACE

/-- True Quantified Boolean Formulas language. -/
def TQBF : Language := PvnpReal.TQBF

/-- PSPACE-completeness under polynomial-time many-one reductions. -/
def PSPACEComplete (L : Language) : Prop := PvnpReal.PSPACEComplete L

/-- Space-time hierarchy: `P ⊆ PSPACE`. -/
theorem P_subset_PSPACE (L : Language) (hL : InP L) : InPSPACE L :=
  PvnpReal.P_subset_PSPACE L hL

/-- Space-time hierarchy: `PSPACE ⊆ EXP`. -/
theorem PSPACE_subset_EXP (L : Language) (hL : InPSPACE L) : InEXP L :=
  PvnpReal.PSPACE_subset_EXP L hL

/-- Space Hierarchy Theorem on `FinTM2`. -/
theorem space_hierarchy : ∃ k : ℕ, 1 ≤ k ∧ ∀ (t : ℕ → ℕ)
    (hp : Turing.TM2ComputableInTime PvnpReal.strEnc PvnpReal.strEnc (PvnpReal.padWith t)) (A a : ℕ), 1 ≤ a →
    (∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) →
    ∃ K, InDSPACE (fun n => K * (t n + n + 1) ^ (k * a)) (PvnpReal.diagT t) ∧
      ∀ S : ℕ → ℕ, (∀ A B D : ℕ, ∃ N, ∀ n ≥ N, D * (A * B ^ S n) + 1 ≤ t n) →
        ¬ InDSPACE S (PvnpReal.diagT t) :=
  PvnpReal.space_hierarchy

/-- SAT is decidable in polynomial space. -/
theorem SAT_in_PSPACE : InPSPACE SATLang :=
  PvnpReal.SAT_in_PSPACE

/-- NP is contained in PSPACE. -/
theorem NP_subset_PSPACE (L : Language) (hL : InNP L) : InPSPACE L :=
  PvnpReal.NP_subset_PSPACE L hL

/-- Packaged chain: `NP ⊆ PSPACE ⊆ EXP`. -/
theorem NP_subset_PSPACE_subset_EXP (L : Language) (hL : InNP L) : InPSPACE L ∧ InEXP L :=
  PvnpReal.NP_subset_PSPACE_subset_EXP L hL

/-- TQBF is decidable in polynomial space. -/
theorem TQBF_in_PSPACE : InPSPACE TQBF :=
  PvnpReal.TQBF_in_PSPACE

/-- SAT polynomial-time reduces to TQBF. -/
theorem SAT_reduces_TQBF : PolyReduces SATLang TQBF :=
  PvnpReal.SAT_reduces_TQBF

/-- TQBF is NP-hard. -/
theorem TQBF_NPHard (L : Language) (hL : InNP L) : PolyReduces L TQBF :=
  PvnpReal.TQBF_NPHard L hL

/-- TQBF is PSPACE-hard: every language in PSPACE reduces to TQBF in polynomial time. -/
theorem TQBF_PSPACE_hard : ∀ L : Language, InPSPACE L → PolyReduces L TQBF :=
  PvnpReal.TQBF_PSPACE_hard

/-- Unconditional PSPACE-completeness of TQBF. -/
theorem TQBF_PSPACE_complete : PSPACEComplete TQBF :=
  PvnpReal.TQBF_PSPACE_complete

/-- Structural equivalence: `P = PSPACE` iff `TQBF ∈ P`. -/
theorem P_eq_PSPACE_iff_TQBF_in_P : P_eq_PSPACE ↔ InP TQBF :=
  PvnpReal.P_eq_PSPACE_iff_TQBF_in_P

/-- If `P = PSPACE`, then `TQBF ∈ P`. -/
theorem TQBF_in_P_of_P_eq_PSPACE (h : P_eq_PSPACE) : InP TQBF :=
  PvnpReal.TQBF_in_P_of_P_eq_PSPACE h

/-- If `P = PSPACE`, then `P = NP`. -/
theorem P_eq_NP_of_P_eq_PSPACE (h : P_eq_PSPACE) : P_eq_NP :=
  PvnpReal.P_eq_NP_of_P_eq_PSPACE h

/-- Contrapositive: `P ≠ NP → P ≠ PSPACE`. -/
theorem P_ne_PSPACE_of_P_ne_NP (h : ¬ P_eq_NP) : ¬ P_eq_PSPACE :=
  PvnpReal.P_ne_PSPACE_of_P_ne_NP h

/-- If `P = PSPACE`, then `SAT ∈ P`. -/
theorem SAT_in_P_of_P_eq_PSPACE (h : P_eq_PSPACE) : InP SATLang :=
  PvnpReal.SAT_in_P_of_P_eq_PSPACE h

/-- If `TQBF ∈ P`, then `P = NP`. -/
theorem P_eq_NP_of_TQBF_in_P (h : InP TQBF) : P_eq_NP :=
  PvnpReal.P_eq_NP_of_TQBF_in_P h

/-- If `P ≠ NP`, then `TQBF ∉ P`. -/
theorem TQBF_not_in_P_of_P_ne_NP (h : ¬ P_eq_NP) : ¬ InP TQBF :=
  PvnpReal.TQBF_not_in_P_of_P_ne_NP h

/-- Unconditional separation disjunction: either `P ≠ PSPACE` or `PSPACE ≠ EXP`. -/
theorem P_ne_PSPACE_or_PSPACE_ne_EXP :
    (∃ L, InPSPACE L ∧ ¬ InP L) ∨ (∃ L, InEXP L ∧ ¬ InPSPACE L) :=
  PvnpReal.P_ne_PSPACE_or_PSPACE_ne_EXP

/-- Language congruence closure for `PSPACE`. -/
theorem InPSPACE.congr {L L' : Language} (h : InPSPACE L) (e : ∀ x, L x ↔ L' x) : InPSPACE L' :=
  PvnpReal.InPSPACE.congr h e

/-- Any language polynomial-time reducing to TQBF is in PSPACE. -/
theorem InPSPACE.of_reduces_TQBF {L : Language} (hr : PolyReduces L TQBF) : InPSPACE L :=
  PvnpReal.InPSPACE.of_reduces_TQBF hr

/-- PSPACE is closed under polynomial-time many-one reductions. -/
theorem InPSPACE.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InPSPACE L') :
    InPSPACE L :=
  PvnpReal.InPSPACE.of_reduces hr h

/-- PSPACE is closed under complement (`PSPACE = coPSPACE`). -/
theorem InPSPACE.compl {L : Language} (h : InPSPACE L) : InPSPACE (fun x => ¬ L x) :=
  PvnpReal.InPSPACE.compl h

/-- Languages accepted in nondeterministic polynomial space on `FinTM2` (`NPSPACE`). -/
def InNPSPACE (L : Language) : Prop := PvnpReal.InNPSPACE L

/-- Complements of NPSPACE languages (`coNPSPACE`). -/
def InCoNPSPACE (L : Language) : Prop := PvnpReal.InCoNPSPACE L

/-- Deterministic polynomial space embeds into nondeterministic polynomial space (`PSPACE ⊆ NPSPACE`). -/
theorem PSPACE_subset_NPSPACE (L : Language) (hL : InPSPACE L) : InNPSPACE L :=
  PvnpReal.PSPACE_subset_NPSPACE L hL

/-- `NP ⊆ NPSPACE`. -/
theorem NP_subset_NPSPACE (L : Language) (hL : InNP L) : InNPSPACE L :=
  PvnpReal.NP_subset_NPSPACE L hL

/-- `P ⊆ NPSPACE`. -/
theorem P_subset_NPSPACE (L : Language) (hL : InP L) : InNPSPACE L :=
  PvnpReal.P_subset_NPSPACE L hL

/-- Every NPSPACE language polynomial-time reduces to TQBF. -/
theorem NPSPACE_reduces_TQBF (L : Language) (hL : InNPSPACE L) : PolyReduces L TQBF :=
  PvnpReal.NPSPACE_reduces_TQBF L hL

/-- Nontrivial direction of Savitch's Theorem: `NPSPACE ⊆ PSPACE`. -/
theorem NPSPACE_subset_PSPACE (L : Language) (hL : InNPSPACE L) : InPSPACE L :=
  PvnpReal.NPSPACE_subset_PSPACE L hL

/-- **Savitch's Theorem**: `NPSPACE = PSPACE`. -/
theorem NPSPACE_eq_PSPACE (L : Language) : InNPSPACE L ↔ InPSPACE L :=
  PvnpReal.NPSPACE_eq_PSPACE L

/-- `NPSPACE` is closed under complement (Immerman–Szelepcsényi / Savitch). -/
theorem InNPSPACE.compl {L : Language} (h : InNPSPACE L) : InNPSPACE (fun x => ¬ L x) :=
  PvnpReal.InNPSPACE.compl h

/-- `coNPSPACE = NPSPACE`. -/
theorem coNPSPACE_eq_NPSPACE (L : Language) : InCoNPSPACE L ↔ InNPSPACE L :=
  PvnpReal.coNPSPACE_eq_NPSPACE L

/-- `NP ⊆ coNPSPACE`. -/
theorem NP_subset_coNPSPACE (L : Language) (hL : InNP L) : InCoNPSPACE L :=
  PvnpReal.NP_subset_coNPSPACE L hL

/-- `coNP ⊆ NPSPACE`. -/
theorem coNP_subset_NPSPACE (L : Language) (hL : InCoNP L) : InNPSPACE L :=
  PvnpReal.coNP_subset_NPSPACE L hL

/-- `coNP ⊆ PSPACE`. -/
theorem coNP_subset_PSPACE (L : Language) (hL : InCoNP L) : InPSPACE L :=
  (NPSPACE_eq_PSPACE L).1 (coNP_subset_NPSPACE L hL)

/-- `PSPACE = coNPSPACE`. -/
theorem PSPACE_eq_coNPSPACE (L : Language) : InPSPACE L ↔ InCoNPSPACE L :=
  (NPSPACE_eq_PSPACE L).symm.trans (coNPSPACE_eq_NPSPACE L).symm

/-- `NPSPACE ⊆ EXP`. -/
theorem NPSPACE_subset_EXP (L : Language) (hL : InNPSPACE L) : InEXP L :=
  PSPACE_subset_EXP L (NPSPACE_subset_PSPACE L hL)

/-- Language congruence closure for `NPSPACE`. -/
theorem InNPSPACE.congr {L L' : Language} (h : InNPSPACE L) (e : ∀ x, L x ↔ L' x) :
    InNPSPACE L' :=
  (NPSPACE_eq_PSPACE L').2 (InPSPACE.congr ((NPSPACE_eq_PSPACE L).1 h) e)

/-- `NPSPACE` is closed under polynomial-time many-one reductions. -/
theorem InNPSPACE.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InNPSPACE L') :
    InNPSPACE L :=
  (NPSPACE_eq_PSPACE L).2 (InPSPACE.of_reduces hr ((NPSPACE_eq_PSPACE L').1 h))

/-- `coNPSPACE` is closed under polynomial-time many-one reductions. -/
theorem InCoNPSPACE.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InCoNPSPACE L') :
    InCoNPSPACE L :=
  (coNPSPACE_eq_NPSPACE L).2 (InNPSPACE.of_reduces hr ((coNPSPACE_eq_NPSPACE L').1 h))

/-- TQBF is NPSPACE-complete. -/
theorem TQBF_NPSPACE_complete :
    InNPSPACE TQBF ∧ ∀ L : Language, InNPSPACE L → PolyReduces L TQBF :=
  ⟨PSPACE_subset_NPSPACE TQBF TQBF_in_PSPACE, NPSPACE_reduces_TQBF⟩

-- ============================================================
-- SECTION 10: POLYNOMIAL HIERARCHY (`PH`, `Σ_k`, `Π_k`)
-- ============================================================
-- Note: Arora–Barak Def. 5.4 style alternating quantifier characterization.
-- Level-0/1 collapses, `PH ⊆ PSPACE`, general level-`k` collapse (`Σ_k = Π_k → PH = Σ_k`),
-- and `Σ_k`-completeness of `Σ_k-SAT` (`k ≥ 1`) are formally proven.

/-- `Σ_k`: `L x ↔ ∃ u₁ ∀ u₂ … Q u_k. R(x, u₁⋯u_k)` with `R ∈ P` and polynomial block lengths. -/
def InSigma (k : ℕ) (L : Language) : Prop := PvnpReal.InSigma k L

/-- `Π_k`: alternating polynomially-bounded quantifier hierarchy starting with `∀`. -/
def InPi (k : ℕ) (L : Language) : Prop := PvnpReal.InPi k L

/-- The Polynomial Hierarchy `PH = ⋃_k Σ_k`. -/
def InPH (L : Language) : Prop := PvnpReal.InPH L

/-- The proposition `NP = coNP`. -/
def NP_eq_coNP : Prop := ∀ L : Language, InNP L ↔ InCoNP L

/-- Language congruence closure for `Σ_k`. -/
theorem InSigma.congr {k : ℕ} {L L' : Language} (h : InSigma k L) (e : ∀ x, L x ↔ L' x) :
    InSigma k L' :=
  PvnpReal.InSigma.congr h e

/-- Language congruence closure for `Π_k`. -/
theorem InPi.congr {k : ℕ} {L L' : Language} (h : InPi k L) (e : ∀ x, L x ↔ L' x) :
    InPi k L' :=
  PvnpReal.InPi.congr h e

/-- Language congruence closure for `PH`. -/
theorem InPH.congr {L L' : Language} (h : InPH L) (e : ∀ x, L x ↔ L' x) :
    InPH L' :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.congr e⟩

/-- Complement duality: `Π_k = co-Σ_k`. -/
theorem InPi_iff_compl (k : ℕ) (L : Language) : InPi k L ↔ InSigma k (fun x => ¬ L x) :=
  PvnpReal.InPi_iff_compl k L

/-- Complement duality: `Σ_k = co-Π_k`. -/
theorem InSigma_iff_compl (k : ℕ) (L : Language) : InSigma k L ↔ InPi k (fun x => ¬ L x) :=
  PvnpReal.InSigma_iff_compl k L

/-- Base level: `Σ_0 = P`. -/
theorem Sigma0_iff_P (L : Language) : InSigma 0 L ↔ InP L :=
  PvnpReal.Sigma0_iff_P L

/-- Base level: `Π_0 = P`. -/
theorem Pi0_iff_P (L : Language) : InPi 0 L ↔ InP L :=
  PvnpReal.Pi0_iff_P L

/-- Level 1 characterization: `Σ_1 = NP`. -/
theorem Sigma1_iff_NP (L : Language) : InSigma 1 L ↔ InNP L :=
  PvnpReal.Sigma1_iff_NP L

/-- Level 1 characterization: `Π_1 = coNP`. -/
theorem Pi1_iff_coNP (L : Language) : InPi 1 L ↔ InCoNP L :=
  PvnpReal.Pi1_iff_coNP L

/-- `Σ_k ⊆ Σ_{k+1}`. -/
theorem InSigma.succ {k : ℕ} {L : Language} (h : InSigma k L) : InSigma (k + 1) L :=
  PvnpReal.InSigma.succ h

/-- `Π_k ⊆ Π_{k+1}`. -/
theorem InPi.succ {k : ℕ} {L : Language} (h : InPi k L) : InPi (k + 1) L :=
  PvnpReal.InPi.succ h

/-- `Π_k ⊆ Σ_{k+1}`. -/
theorem InPi.toSigma_succ {k : ℕ} {L : Language} (h : InPi k L) : InSigma (k + 1) L :=
  PvnpReal.InPi.toSigma_succ h

/-- `Σ_k ⊆ Π_{k+1}`. -/
theorem InSigma.toPi_succ {k : ℕ} {L : Language} (h : InSigma k L) : InPi (k + 1) L :=
  PvnpReal.InSigma.toPi_succ h

/-- Hierarchy inclusion across adjacent levels: `Σ_k ∪ Π_k ⊆ Σ_{k+1} ∩ Π_{k+1}`. -/
theorem Sigma_Pi_subset_succ (k : ℕ) (L : Language) (h : InSigma k L ∨ InPi k L) :
    InSigma (k + 1) L ∧ InPi (k + 1) L :=
  PvnpReal.Sigma_Pi_subset_succ k L h

/-- Level monotonicity for `Σ_k`: `k ≤ m → Σ_k ⊆ Σ_m`. -/
theorem InSigma.mono {k m : ℕ} {L : Language} (h : InSigma k L) (hkm : k ≤ m) :
    InSigma m L :=
  PvnpReal.InSigma.mono h hkm

/-- Level monotonicity for `Π_k`: `k ≤ m → Π_k ⊆ Π_m`. -/
theorem InPi.mono {k m : ℕ} {L : Language} (h : InPi k L) (hkm : k ≤ m) :
    InPi m L :=
  (InPi_iff_compl m L).2 (((InPi_iff_compl k L).1 h).mono hkm)

/-- Every `Σ_k` language lies in `PH`. -/
theorem InSigma.toPH {k : ℕ} {L : Language} (h : InSigma k L) : InPH L :=
  ⟨k, h⟩

/-- Every `Π_k` language lies in `PH`. -/
theorem InPi.toPH {k : ℕ} {L : Language} (h : InPi k L) : InPH L :=
  PvnpReal.InPi.toPH h

/-- `P ⊆ PH`. -/
theorem P_subset_PH (L : Language) (h : InP L) : InPH L :=
  PvnpReal.P_subset_PH L h

/-- `NP ⊆ PH`. -/
theorem NP_subset_PH (L : Language) (h : InNP L) : InPH L :=
  PvnpReal.NP_subset_PH L h

/-- `coNP ⊆ PH`. -/
theorem coNP_subset_PH (L : Language) (h : InCoNP L) : InPH L :=
  PvnpReal.coNP_subset_PH L h

/-- `PH` is closed under complement. -/
theorem InPH.compl {L : Language} (h : InPH L) : InPH (fun x => ¬ L x) :=
  PvnpReal.InPH.compl h

/-- Unconditional upper bound: `Σ_k ⊆ PSPACE` for every level `k`. -/
theorem Sigma_subset_PSPACE (k : ℕ) (L : Language) (h : InSigma k L) : InPSPACE L :=
  PvnpReal.Sigma_subset_PSPACE k L h

/-- Unconditional upper bound: `Π_k ⊆ PSPACE` for every level `k`. -/
theorem Pi_subset_PSPACE (k : ℕ) (L : Language) (h : InPi k L) : InPSPACE L :=
  PvnpReal.Pi_subset_PSPACE k L h

/-- Unconditional upper bound: `PH ⊆ PSPACE`. -/
theorem PH_subset_PSPACE (L : Language) (h : InPH L) : InPSPACE L :=
  PvnpReal.PH_subset_PSPACE L h

/-- Unconditional upper bound: `PH ⊆ NPSPACE`. -/
theorem PH_subset_NPSPACE (L : Language) (h : InPH L) : InNPSPACE L :=
  PSPACE_subset_NPSPACE L (PH_subset_PSPACE L h)

/-- Unconditional upper bound: `PH ⊆ EXP`. -/
theorem PH_subset_EXP (L : Language) (h : InPH L) : InEXP L :=
  PSPACE_subset_EXP L (PH_subset_PSPACE L h)

/-- Level-0 collapse: `P = NP → Σ_k ⊆ P` for every `k`. -/
theorem Sigma_subset_P_of_P_eq_NP (hPNP : P_eq_NP) (k : ℕ) (L : Language) (h : InSigma k L) :
    InP L :=
  PvnpReal.Sigma_subset_P_of_P_eq_NP hPNP k L h

/-- Level-0 collapse: `P = NP → Π_k ⊆ P` for every `k`. -/
theorem Pi_subset_P_of_P_eq_NP (hPNP : P_eq_NP) (k : ℕ) (L : Language) (h : InPi k L) :
    InP L :=
  PvnpReal.Pi_subset_P_of_P_eq_NP hPNP k L h

/-- Level-0 collapse: `P = NP → PH = P`. -/
theorem PH_eq_P_of_P_eq_NP (hPNP : P_eq_NP) (L : Language) : InPH L ↔ InP L :=
  PvnpReal.PH_eq_P_of_P_eq_NP hPNP L

/-- Level-1 collapse: `NP = coNP → Σ_k ⊆ NP` for every `k`. -/
theorem Sigma_subset_NP_of_NP_eq_coNP (hNC : NP_eq_coNP) (k : ℕ) (L : Language) (h : InSigma k L) :
    InNP L :=
  PvnpReal.Sigma_subset_NP_of_NP_eq_coNP hNC k L h

/-- Level-1 collapse: `NP = coNP → Π_k ⊆ NP` for every `k`. -/
theorem Pi_subset_NP_of_NP_eq_coNP (hNC : NP_eq_coNP) (k : ℕ) (L : Language) (h : InPi k L) :
    InNP L :=
  Sigma_subset_NP_of_NP_eq_coNP hNC (k + 1) L h.toSigma_succ

/-- Level-1 collapse: `NP = coNP → PH = NP`. -/
theorem PH_eq_NP_of_NP_eq_coNP (hNC : NP_eq_coNP) (L : Language) : InPH L ↔ InNP L :=
  PvnpReal.PH_eq_NP_of_NP_eq_coNP hNC L

/-- Level-1 collapse (dual): `NP = coNP → PH = coNP`. -/
theorem PH_eq_coNP_of_NP_eq_coNP (hNC : NP_eq_coNP) (L : Language) : InPH L ↔ InCoNP L :=
  (PH_eq_NP_of_NP_eq_coNP hNC L).trans (hNC L)

/-- Separation propagation: if `P ≠ PH` then `P ≠ PSPACE`. -/
theorem PSPACE_ne_P_of_PH_ne_P (h : ∃ L : Language, InPH L ∧ ¬ InP L) :
    ∃ L : Language, InPSPACE L ∧ ¬ InP L :=
  let ⟨L, hPH, hnP⟩ := h
  ⟨L, PH_subset_PSPACE L hPH, hnP⟩

/-- Closure of `Σ_k` under polynomial-time reductions. -/
theorem InSigma.of_reduces {k : ℕ} {L L' : Language} (hr : PolyReduces L L') (h : InSigma k L') :
    InSigma k L :=
  PvnpReal.InSigma.of_reduces hr h

/-- Closure of `Π_k` under polynomial-time reductions. -/
theorem InPi.of_reduces {k : ℕ} {L L' : Language} (hr : PolyReduces L L') (h : InPi k L') :
    InPi k L :=
  PvnpReal.InPi.of_reduces hr h

/-- Closure of `PH` under polynomial-time reductions. -/
theorem InPH.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InPH L') : InPH L :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.of_reduces hr⟩

/-- The proposition `Σ_k = Π_k`. -/
def Sigma_eq_Pi (k : ℕ) : Prop := PvnpReal.Sigma_eq_Pi k

/-- Unfolded characterization of `Σ_k = Π_k`. -/
theorem Sigma_eq_Pi_iff (k : ℕ) : Sigma_eq_Pi k ↔ ∀ L : Language, InSigma k L ↔ InPi k L :=
  Iff.rfl

/-- Collapse equivalence from one-sided inclusion: `Σ_k ⊆ Π_k → Σ_k = Π_k`. -/
theorem Sigma_eq_Pi_of_subset (k : ℕ) (h : ∀ L : Language, InSigma k L → InPi k L) :
    Sigma_eq_Pi k :=
  PvnpReal.Sigma_eq_Pi_of_subset k h

/-- **General PH Collapse Theorem**: for every `k ≥ 1`, `Σ_k = Π_k → PH = Σ_k`. -/
theorem PH_eq_Sigma_of_Sigma_eq_Pi (k : ℕ) (hk : 1 ≤ k) (H : Sigma_eq_Pi k) (L : Language) :
    InPH L ↔ InSigma k L :=
  PvnpReal.PH_eq_Sigma_of_Sigma_eq_Pi k hk H L

/-- **General PH Collapse Theorem (dual)**: for every `k ≥ 1`, `Σ_k = Π_k → PH = Π_k`. -/
theorem PH_eq_Pi_of_Sigma_eq_Pi (k : ℕ) (hk : 1 ≤ k) (H : Sigma_eq_Pi k) (L : Language) :
    InPH L ↔ InPi k L :=
  (PH_eq_Sigma_of_Sigma_eq_Pi k hk H L).trans (H L)

/-- **General PH Collapse from one-sided inclusion**: `k ≥ 1 → Σ_k ⊆ Π_k → PH = Σ_k`. -/
theorem PH_eq_Sigma_of_Sigma_subset_Pi (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ L : Language, InSigma k L → InPi k L) (L : Language) : InPH L ↔ InSigma k L :=
  PvnpReal.PH_eq_Sigma_of_Sigma_subset_Pi k hk h L

/-- Canonical `Σ_k`-complete satisfiability language (`Σ_k-SAT`). -/
def SigmaSAT (k : ℕ) : Language := PvnpReal.SigmaSAT k

/-- `Σ_k`-completeness: `L ∈ Σ_k` and every language in `Σ_k` poly-reduces to `L`. -/
def SigmaComplete (k : ℕ) (L : Language) : Prop := PvnpReal.SigmaComplete k L

/-- `Σ_k-SAT` lies in `Σ_k` for every `k`. -/
theorem SigmaSAT_in_Sigma (k : ℕ) : InSigma k (SigmaSAT k) :=
  PvnpReal.SigmaSAT_in_Sigma k

/-- `Σ_{j+1}-SAT` is `Σ_{j+1}`-hard for every `j`. -/
theorem SigmaSAT_hard (j : ℕ) (L : Language) (hL : InSigma (j + 1) L) :
    PolyReduces L (SigmaSAT (j + 1)) :=
  PvnpReal.SigmaSAT_hard j L hL

/-- **`Σ_k-SAT` is `Σ_k`-complete for every `k ≥ 1`.** -/
theorem SigmaSAT_complete (k : ℕ) (hk : 1 ≤ k) : SigmaComplete k (SigmaSAT k) :=
  PvnpReal.SigmaSAT_complete k hk

/-- If `Σ_k-SAT ∈ Π_k` (`k ≥ 1`), then the Polynomial Hierarchy collapses to `Σ_k`. -/
theorem PH_collapse_of_SigmaSAT_in_Pi (k : ℕ) (hk : 1 ≤ k) (h : InPi k (SigmaSAT k)) (L : Language) :
    InPH L ↔ InSigma k L :=
  PvnpReal.PH_collapse_of_SigmaSAT_in_Pi k hk h L

/-- Level-`k` symmetry equivalence: `Σ_k-SAT ∈ Π_k ↔ Σ_k = Π_k` (`k ≥ 1`). -/
theorem SigmaSAT_in_Pi_iff (k : ℕ) (hk : 1 ≤ k) : InPi k (SigmaSAT k) ↔ Sigma_eq_Pi k :=
  PvnpReal.SigmaSAT_in_Pi_iff k hk

-- ============================================================
-- SECTION 11: NON-UNIFORM COMPLEXITY (`P/poly`, CIRCUITS, KARP–LIPTON & KANNAN)
-- ============================================================
-- Note: `InPpoly` is polynomial time with exact polynomial-length advice (Arora–Barak Def. 6.18).
-- `InPpolyCirc` is polynomial-size Boolean circuit families. Full equivalence `InPpoly ↔ InPpolyCirc`,
-- circuit-form `P ⊆ P/poly`, equivalence of both Karp–Lipton hypotheses, an undecidable language
-- in `P/poly`, and Kannan's circuit lower bounds (`Σ_2` i.o. & `Σ_4`/`PH` a.e.) are formally proven.

/-- **`P/poly` (advice model)**: polynomial-time deciders with exact polynomial-length advice. -/
def InPpoly (L : Language) : Prop := PvnpReal.InPpoly L

/-- **`P/poly` (circuit model)**: languages computed by polynomial-size Boolean circuit families. -/
def InPpolyCirc (L : Language) : Prop := PvnpReal.InPpolyCirc L

/-- The hypothesis `NP ⊆ P/poly` (advice model). -/
def NP_subset_Ppoly : Prop := PvnpReal.NP_subset_Ppoly

/-- The hypothesis `NP ⊆ P/poly` (circuit model). -/
def NP_subset_PpolyCirc : Prop := ∀ L : Language, InNP L → InPpolyCirc L

/-- Polynomial-time universal Boolean gate-list evaluator language. -/
def CEval : Language := PvnpReal.CEval

/-- **Unconditional inclusion `P ⊆ P/poly`** (advice model, via empty advice). -/
theorem P_subset_Ppoly (L : Language) (h : InP L) : InPpoly L :=
  PvnpReal.P_subset_Ppoly L h

/-- Closure of `P/poly` under polynomial-time many-one reductions. -/
theorem InPpoly.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InPpoly L') :
    InPpoly L :=
  PvnpReal.InPpoly.of_reduces hr h

/-- Language congruence closure for `P/poly`. -/
theorem InPpoly.congr {L L' : Language} (h : InPpoly L) (e : ∀ x, L x ↔ L' x) : InPpoly L' :=
  PvnpReal.InPpoly.congr h e

/-- `SAT ∈ P/poly ↔ NP ⊆ P/poly`. -/
theorem SAT_Ppoly_iff : InPpoly SATLang ↔ NP_subset_Ppoly :=
  PvnpReal.SAT_Ppoly_iff

/-- Under `NP ⊆ P/poly`, `Π_2 ⊆ Σ_2`. -/
theorem Pi2_subset_Sigma2 (H : NP_subset_Ppoly) (L : Language) (hL : InPi 2 L) : InSigma 2 L :=
  PvnpReal.Pi2_subset_Sigma2 H L hL

/-- Under `NP ⊆ P/poly`, `Σ_2 ⊆ Π_2`. -/
theorem Sigma2_subset_Pi2 (H : NP_subset_Ppoly) (L : Language) (hL : InSigma 2 L) : InPi 2 L :=
  PvnpReal.Sigma2_subset_Pi2 H L hL

/-- **Karp–Lipton Theorem (advice form)**: if `NP ⊆ P/poly`, then `PH = Σ_2`. -/
theorem karpLipton (H : NP_subset_Ppoly) (L : Language) : InPH L ↔ InSigma 2 L :=
  PvnpReal.karpLipton H L

/-- **Karp–Lipton Theorem (SAT form)**: if `SAT ∈ P/poly`, then `PH = Σ_2`. -/
theorem karpLipton_SAT (h : InPpoly SATLang) (L : Language) : InPH L ↔ InSigma 2 L :=
  PvnpReal.karpLipton_SAT h L

/-- Under `NP ⊆ P/poly`, `Σ_2-SAT ∈ Π_2`. -/
theorem SigmaSAT2_in_Pi2 (H : NP_subset_Ppoly) : InPi 2 (SigmaSAT 2) :=
  PvnpReal.SigmaSAT2_in_Pi2 H

/-- Contrapositive: if `PH ≠ Σ_2`, then `NP ⊈ P/poly`. -/
theorem NP_not_subset_Ppoly_of_PH_ne_Sigma2 (h : ¬ ∀ L, InPH L ↔ InSigma 2 L) :
    ¬ NP_subset_Ppoly :=
  PvnpReal.NP_not_subset_Ppoly_of_PH_ne_Sigma2 h

/-- Contrapositive: if `PH ≠ Σ_2`, then `SAT ∉ P/poly`. -/
theorem SAT_not_Ppoly_of_PH_ne_Sigma2 (h : ¬ ∀ L, InPH L ↔ InSigma 2 L) :
    ¬ InPpoly SATLang :=
  PvnpReal.SAT_not_Ppoly_of_PH_ne_Sigma2 h

/-- The universal Boolean circuit evaluator `CEval` runs in polynomial time (`CEval ∈ P`). -/
theorem CEval_in_P : InP CEval :=
  PvnpReal.InP.CEvalP

/-- **Half-bridge (circuits → advice)**: polynomial-size circuits imply advice `P/poly`. -/
theorem InPpoly_of_circ {L : Language} (h : InPpolyCirc L) : InPpoly L :=
  PvnpReal.InPpoly_of_circ h

/-- **Karp–Lipton Theorem (circuit form)**: if `NP` has polynomial-size circuits, then `PH = Σ_2`. -/
theorem karpLipton_circ (H : NP_subset_PpolyCirc) (L : Language) : InPH L ↔ InSigma 2 L :=
  PvnpReal.karpLipton_circ H L

/-- Contrapositive (circuit form): if `PH ≠ Σ_2`, `NP` has no polynomial-size circuit families. -/
theorem NP_not_subset_PpolyCirc_of_PH_ne_Sigma2 (h : ¬ ∀ L, InPH L ↔ InSigma 2 L) :
    ¬ NP_subset_PpolyCirc :=
  PvnpReal.NP_not_subset_PpolyCirc_of_PH_ne_Sigma2 h

/-- Converse gate-list bridge: circuits of size `≤ s` iff well-formed gate lists of length `≤ s`. -/
theorem hasCircuit_iff_gates {n s : ℕ} (f : PvnpReal.BFun n) :
    PvnpReal.HasCircuit n s f ↔ ∃ gs : List PvnpReal.CGate, gs.length ≤ s ∧
      (∀ g ∈ gs, g.2.1 < n + gs.length ∧ g.2.2 < n + gs.length) ∧
      ∃ out, out < n + gs.length + 1 ∧
        ∀ x, f x = (PvnpReal.pRun (List.ofFn x) gs).getD out false :=
  PvnpReal.hasCircuit_iff_gates f

/-- **Other half-bridge (advice → circuits)**: polynomial-time with polynomial advice implies polynomial-size circuits. -/
theorem InPpolyCirc_of_InPpoly {L : Language} (hL : InPpoly L) : InPpolyCirc L :=
  PvnpReal.InPpolyCirc_of_InPpoly hL

/-- **Full `P/poly` Equivalence**: polynomial advice equals polynomial-size Boolean circuits (`InPpoly L ↔ InPpolyCirc L`). -/
theorem InPpoly_iff_circ (L : Language) : InPpoly L ↔ InPpolyCirc L :=
  PvnpReal.InPpoly_iff_circ L

/-- **Unconditional inclusion `P ⊆ P/poly` (circuit form)**. -/
theorem P_subset_PpolyCirc (L : Language) (h : InP L) : InPpolyCirc L :=
  PvnpReal.P_subset_PpolyCirc L h

/-- Closure of `P/poly` (circuit form) under polynomial-time many-one reductions. -/
theorem InPpolyCirc.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InPpolyCirc L') :
    InPpolyCirc L :=
  InPpolyCirc_of_InPpoly ((InPpoly_of_circ h).of_reduces hr)

/-- Language congruence closure for `P/poly` (circuit form). -/
theorem InPpolyCirc.congr {L L' : Language} (h : InPpolyCirc L) (e : ∀ x, L x ↔ L' x) :
    InPpolyCirc L' :=
  InPpolyCirc_of_InPpoly ((InPpoly_of_circ h).congr e)

/-- Equivalence of both `NP ⊆ P/poly` hypotheses (`advice ↔ circuits`). -/
theorem NP_subset_Ppoly_iff_circ : NP_subset_Ppoly ↔ NP_subset_PpolyCirc :=
  PvnpReal.NP_subset_Ppoly_iff_circ

/-- **Unified Karp–Lipton Equivalence**: both `NP ⊆ P/poly` formulations agree and each collapses `PH` to `Σ_2`. -/
theorem karpLipton_iff_forms :
    (NP_subset_Ppoly ↔ NP_subset_PpolyCirc) ∧
      (NP_subset_Ppoly → ∀ L, InPH L ↔ InSigma 2 L) ∧
      (NP_subset_PpolyCirc → ∀ L, InPH L ↔ InSigma 2 L) :=
  PvnpReal.karpLipton_iff_forms

/-- `SAT` has polynomial-size circuits iff `NP ⊆ P/poly` (circuit form). -/
theorem SAT_PpolyCirc_iff : InPpolyCirc SATLang ↔ NP_subset_PpolyCirc :=
  (InPpoly_iff_circ SATLang).symm.trans (SAT_Ppoly_iff.trans NP_subset_Ppoly_iff_circ)

/-- Languages decided by some always-halting `FinTM2` machine (no time bound required). -/
def TM2Decidable (L : Language) : Prop := PvnpReal.TM2Decidable L

/-- Diagonal unary language: `{1^n | program n does not accept 1^n}`. -/
def Ldiag : Language := PvnpReal.Ldiag

/-- Kannan's hard language for exponent `k`. -/
def KanL (k : ℕ) : Language := PvnpReal.KanL k

/-- Every `EXP` language is decided by some total `FinTM2`. -/
theorem InEXP.tm2Decidable {L : Language} (h : InEXP L) : TM2Decidable L :=
  PvnpReal.InEXP.tm2Decidable h

/-- Every `DTIME(T)` language is decided by some total `FinTM2`. -/
theorem InDTIME.tm2Decidable {T : ℕ → ℕ} {L : Language} (h : InDTIME T L) : TM2Decidable L :=
  PvnpReal.InDTIME.tm2Decidable h

/-- Every `P` language is decided by some total `FinTM2`. -/
theorem InP.tm2Decidable {L : Language} (h : InP L) : TM2Decidable L :=
  PvnpReal.InP.tm2Decidable h

/-- `Ldiag` is not decided by any total `FinTM2`. -/
theorem Ldiag_not_tm2Decidable : ¬ TM2Decidable Ldiag :=
  PvnpReal.Ldiag_not_tm2Decidable

/-- `Ldiag ∉ EXP`. -/
theorem Ldiag_not_InEXP : ¬ InEXP Ldiag :=
  PvnpReal.Ldiag_not_InEXP

/-- `Ldiag ∉ DTIME(T)` for any time bound `T`. -/
theorem Ldiag_not_InDTIME (T : ℕ → ℕ) : ¬ InDTIME T Ldiag :=
  PvnpReal.Ldiag_not_InDTIME T

/-- `Ldiag ∈ P/poly` (advice model, 1 advice bit per length). -/
theorem Ldiag_InPpoly : InPpoly Ldiag :=
  PvnpReal.Ldiag_InPpoly

/-- `Ldiag ∈ P/poly` (circuit model). -/
theorem Ldiag_InPpolyCirc : InPpolyCirc Ldiag :=
  PvnpReal.Ldiag_InPpolyCirc

/-- **`P/poly` contains an undecidable language**: not decided by any total `FinTM2`, hence outside `EXP` and every `DTIME(T)`. -/
theorem Ppoly_has_undecidable :
    ∃ L, InPpolyCirc L ∧ InPpoly L ∧ ¬ TM2Decidable L ∧ ¬ InEXP L ∧ ∀ T, ¬ InDTIME T L :=
  PvnpReal.Ppoly_has_undecidable

/-- `P/poly ⊈ EXP`. -/
theorem Ppoly_not_subset_EXP : ¬ ∀ L, InPpolyCirc L → InEXP L :=
  PvnpReal.Ppoly_not_subset_EXP

/-- Every `n`-bit Boolean function has a circuit with `2 + 4 · 2^n` gates. -/
theorem hasCircuit_any (n : ℕ) (f : PvnpReal.BFun n) :
    PvnpReal.HasCircuit n (2 + 4 * 2 ^ n) f :=
  PvnpReal.hasCircuit_any n f

/-- Any language outside `P/poly` lacks `n^k`-gate circuits infinitely often, for every `k`. -/
theorem io_hard_of_not_circ {L : Language} (h : ¬ InPpolyCirc L) (k : ℕ) :
    ∀ N, ∃ n ≥ N, ¬ PvnpReal.HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  convert PvnpReal.io_hard_of_not_circ h k

/-- `KanL k` has no `n^k`-gate circuits for all large input lengths `n`. -/
theorem KanL_hard (k : ℕ) : ∃ N, ∀ n ≥ N,
    ¬ PvnpReal.HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (KanL k (List.ofFn x))) := by
  convert PvnpReal.KanL_hard k; all_goals rfl

/-- `KanL k ∈ Σ_4`. -/
theorem KanL_Sigma4 (k : ℕ) : InSigma 4 (KanL k) :=
  PvnpReal.KanL_Sigma4 k

/-- `KanL k ∈ PH`. -/
theorem KanL_PH (k : ℕ) : InPH (KanL k) :=
  PvnpReal.KanL_PH k

/-- **Kannan's Theorem (`Σ_4` / almost-everywhere form)**: for every `k`, some `Σ_4` language lacks `n^k` circuits for all large `n`. -/
theorem kannan_Sigma4 (k : ℕ) : ∃ L, InSigma 4 L ∧ ∃ N, ∀ n ≥ N,
    ¬ PvnpReal.HasCircuit n (n ^ k)
        (fun x : Fin n → Bool => @decide (L (List.ofFn x)) (Classical.dec _)) :=
  PvnpReal.kannan_Sigma4 k

/-- **Kannan's Theorem (`Σ_2` form)**: for every `k`, `Σ_2` has a language with no `n^k`-size circuits for infinitely many `n`. -/
theorem kannan (k : ℕ) : ∃ L, InSigma 2 L ∧
    ∀ N, ∃ n ≥ N, ¬ PvnpReal.HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  convert PvnpReal.kannan k; all_goals rfl

/-- Equivalently: `Σ_2 ⊈ SIZE(n^k)` for every fixed `k`. -/
theorem Sigma2_not_subset_SIZE (k : ℕ) : ¬ ∀ L, InSigma 2 L →
    ∃ N, ∀ n ≥ N, PvnpReal.HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  convert PvnpReal.Sigma2_not_subset_SIZE k; all_goals rfl

/-- **Kannan's Theorem (`PH` form)**: `PH ⊈ SIZE(n^k)` with hardness at all large input lengths. -/
theorem PH_not_subset_SIZE (k : ℕ) : ∃ L, InPH L ∧ ∃ N, ∀ n ≥ N,
    ¬ PvnpReal.HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  convert PvnpReal.PH_not_subset_SIZE k; all_goals rfl

-- ============================================================
-- SECTION 12: RANDOMIZED COMPLEXITY (`BPP`, `RP`, `coRP`, `ZPP`, ADLEMAN, SGL & `NP ⊆ BPP`)
-- ============================================================
-- Note: `InBPP`, `InRP`, `InCoRP`, `InZPP`, and `InZPPq` are defined via finite-counting over
-- uniform Boolean coins (`accCount`). Covers `BPP` Boolean/reduction closures, polynomial error
-- amplification (`2^-p(n)`), Adleman (`BPP ⊆ P/poly`), Sipser–Gács–Lautemann (`BPP ⊆ Σ_2 ∩ Π_2`),
-- `P ⊆ ZPP = RP ∩ coRP ⊆ BPP`, `RP ⊆ NP`, `coRP ⊆ coNP`, `ZPP = ZPPq` ("answer or ?"),
-- `NP ⊆ BPP ⇒ NP = RP` (search-to-decision), `NP ⊆ BPP ⇒ PH = Σ_2`, and `P = NP ⇒ BPP = RP = ZPP = P`.

/-- **`BPP`**: languages decided by a polytime verifier with two-sided error `≤ 1/3`. -/
def InBPP (L : Language) : Prop := PvnpReal.InBPP L

/-- **`RP`**: one-sided error — yes-instances accepted by `≥ 1/2` of random strings, no-instances by none. -/
def InRP (L : Language) : Prop := PvnpReal.InRP L

/-- **`coRP`**: complement of `RP`. -/
def InCoRP (L : Language) : Prop := PvnpReal.InCoRP L

/-- **`ZPP`**: zero-error probabilistic polynomial time (`RP ∩ coRP`). -/
def InZPP (L : Language) : Prop := PvnpReal.InZPP L

/-- **Zero-error "answer or ?" form of `ZPP`**: `Y` and `N` never lie and answer on `≥ 1/2` of coins. -/
def InZPPq (L : Language) : Prop := PvnpReal.InZPPq L

/-- Language congruence closure for `BPP`. -/
theorem InBPP.congr {L L' : Language} (h : InBPP L) (e : ∀ x, L x ↔ L' x) : InBPP L' := by
  obtain ⟨V, q, hV, hq⟩ := h
  exact ⟨V, q, hV, fun x => ⟨fun hx => (hq x).1 ((e x).2 hx), fun hx => (hq x).2 (mt (e x).1 hx)⟩⟩

/-- **Unconditional inclusion `P ⊆ BPP`**. -/
theorem P_subset_BPP {L : Language} (h : InP L) : InBPP L :=
  PvnpReal.P_subset_BPP h

/-- **`BPP` is closed under complement**: `L ∈ BPP → co-L ∈ BPP`. -/
theorem InBPP.compl {L : Language} (h : InBPP L) : InBPP (fun x => ¬ L x) :=
  PvnpReal.InBPP.compl h

/-- Inverse complement closure for `BPP`: `co-L ∈ BPP → L ∈ BPP`. -/
theorem InBPP.of_compl {L : Language} (h : InBPP (fun x => ¬ L x)) : InBPP L :=
  PvnpReal.InBPP.of_compl h

/-- **`BPP` is closed under intersection**. -/
theorem InBPP.inter {L1 L2 : Language} (h1 : InBPP L1) (h2 : InBPP L2) :
    InBPP (fun x => L1 x ∧ L2 x) :=
  PvnpReal.InBPP.inter h1 h2

/-- **`BPP` is closed under union**. -/
theorem InBPP.union {L1 L2 : Language} (h1 : InBPP L1) (h2 : InBPP L2) :
    InBPP (fun x => L1 x ∨ L2 x) :=
  PvnpReal.InBPP.union h1 h2

/-- **`BPP` is closed under polynomial-time many-one reductions**. -/
theorem InBPP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InBPP L') : InBPP L :=
  PvnpReal.InBPP.of_reduces hr h

/-- **BPP Error Amplification**: error probability drops below `2^(-p(|x|))` for any polynomial `p`. -/
theorem InBPP.amplify {L : Language} (h : InBPP L) (p : Polynomial ℕ) :
    ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
      2 ^ p.eval x.length * (Finset.univ.filter (fun W : Fin (q.eval x.length) → Bool =>
        (V (PvnpReal.codeP x (List.ofFn W)) ↔ ¬ L x))).card < 2 ^ q.eval x.length :=
  PvnpReal.InBPP.amplify h p

/-- **Adleman's Theorem (advice form)**: `BPP ⊆ P/poly`. -/
theorem adleman {L : Language} (h : InBPP L) : InPpoly L :=
  PvnpReal.adleman h

/-- **Adleman's Theorem (circuit form)**: `BPP ⊆ P/poly` (polynomial-size circuit families). -/
theorem BPP_subset_PpolyCirc {L : Language} (h : InBPP L) : InPpolyCirc L :=
  PvnpReal.BPP_subset_PpolyCirc h

/-- **Sipser–Gács–Lautemann Theorem (`Σ_2` form)**: `BPP ⊆ Σ_2`. -/
theorem BPP_subset_Sigma2 {L : Language} (h : InBPP L) : InSigma 2 L :=
  PvnpReal.BPP_subset_Sigma2 h

/-- **Sipser–Gács–Lautemann Theorem (`Π_2` dual)**: `BPP ⊆ Π_2`, hence `BPP ⊆ Σ_2 ∩ Π_2`. -/
theorem BPP_subset_Pi2 {L : Language} (h : InBPP L) : InPi 2 L :=
  PvnpReal.BPP_subset_Pi2 h

/-- Unconditional inclusion `BPP ⊆ PH`. -/
theorem BPP_subset_PH {L : Language} (h : InBPP L) : InPH L :=
  (BPP_subset_Sigma2 h).toPH

/-- Unconditional inclusion `BPP ⊆ PSPACE`. -/
theorem BPP_subset_PSPACE {L : Language} (h : InBPP L) : InPSPACE L :=
  PH_subset_PSPACE L (BPP_subset_PH h)

/-- Unconditional inclusion `BPP ⊆ EXP`. -/
theorem BPP_subset_EXP {L : Language} (h : InBPP L) : InEXP L :=
  PSPACE_subset_EXP L (BPP_subset_PSPACE h)

/-- Language congruence closure for `RP`. -/
theorem InRP.congr {L L' : Language} (h : InRP L) (e : ∀ x, L x ↔ L' x) : InRP L' :=
  (funext fun x => propext (e x)) ▸ h

/-- Language congruence closure for `coRP`. -/
theorem InCoRP.congr {L L' : Language} (h : InCoRP L) (e : ∀ x, L x ↔ L' x) : InCoRP L' :=
  (funext fun x => propext (e x)) ▸ h

/-- Language congruence closure for `ZPP`. -/
theorem InZPP.congr {L L' : Language} (h : InZPP L) (e : ∀ x, L x ↔ L' x) : InZPP L' :=
  (funext fun x => propext (e x)) ▸ h

/-- Unconditional inclusion `P ⊆ RP`. -/
theorem P_subset_RP {L : Language} (h : InP L) : InRP L :=
  PvnpReal.P_subset_RP h

/-- Unconditional inclusion `P ⊆ coRP`. -/
theorem P_subset_coRP {L : Language} (h : InP L) : InCoRP L :=
  (PvnpReal.P_subset_ZPP h).2

/-- Unconditional inclusion `P ⊆ ZPP`. -/
theorem P_subset_ZPP {L : Language} (h : InP L) : InZPP L :=
  PvnpReal.P_subset_ZPP h

/-- `ZPP ⊆ RP`. -/
theorem ZPP_subset_RP {L : Language} (h : InZPP L) : InRP L :=
  PvnpReal.ZPP_subset_RP h

/-- `ZPP ⊆ coRP`. -/
theorem ZPP_subset_coRP {L : Language} (h : InZPP L) : InCoRP L :=
  PvnpReal.ZPP_subset_coRP h

/-- Unconditional inclusion `RP ⊆ NP`. -/
theorem RP_subset_NP {L : Language} (h : InRP L) : InNP L :=
  PvnpReal.RP_subset_NP h

/-- Unconditional inclusion `coRP ⊆ coNP`. -/
theorem coRP_subset_coNP {L : Language} (h : InCoRP L) : InCoNP L :=
  PvnpReal.RP_subset_NP h

/-- **One-sided amplification for `RP`**: error `≤ 2^(-p(n))` on yes-instances, zero on no-instances. -/
theorem InRP.amplify {L : Language} (h : InRP L) (p : Polynomial ℕ) :
    ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
      (L x → 2 ^ p.eval x.length * PvnpReal.accCount (fun s => ¬ V s) x (q.eval x.length) ≤ 2 ^ q.eval x.length) ∧
      (¬ L x → PvnpReal.accCount V x (q.eval x.length) = 0) :=
  PvnpReal.InRP.amplify h p

/-- Unconditional inclusion `RP ⊆ BPP`. -/
theorem RP_subset_BPP {L : Language} (h : InRP L) : InBPP L :=
  PvnpReal.RP_subset_BPP h

/-- Unconditional inclusion `coRP ⊆ BPP`. -/
theorem coRP_subset_BPP {L : Language} (h : InCoRP L) : InBPP L :=
  (PvnpReal.coRP_subset_coNP_inter_BPP h).2

/-- Unconditional inclusion `ZPP ⊆ BPP`. -/
theorem ZPP_subset_BPP {L : Language} (h : InZPP L) : InBPP L :=
  (PvnpReal.ZPP_subset h).2.2

/-- Packaged inclusion `RP ⊆ NP ∩ BPP`. -/
theorem RP_subset_NP_inter_BPP {L : Language} (h : InRP L) : InNP L ∧ InBPP L :=
  PvnpReal.RP_subset_NP_inter_BPP h

/-- Packaged inclusion `coRP ⊆ coNP ∩ BPP`. -/
theorem coRP_subset_coNP_inter_BPP {L : Language} (h : InCoRP L) : InCoNP L ∧ InBPP L :=
  PvnpReal.coRP_subset_coNP_inter_BPP h

/-- Packaged inclusion `ZPP ⊆ NP ∩ coNP ∩ BPP`. -/
theorem ZPP_subset {L : Language} (h : InZPP L) : InNP L ∧ InCoNP L ∧ InBPP L :=
  PvnpReal.ZPP_subset h

/-- **`ZPP` equals the zero-error "answer or ?" characterization `ZPPq`**. -/
theorem ZPP_iff_ZPPq (L : Language) : InZPP L ↔ InZPPq L :=
  PvnpReal.ZPP_iff_ZPPq L

/-- **`NP ⊆ BPP ⇒ PH = Σ₂`** (Adleman + Karp–Lipton). -/
theorem PH_collapse_of_NP_subset_BPP (H : ∀ L, InNP L → InBPP L) (L : Language) :
    InPH L ↔ InSigma 2 L :=
  PvnpReal.PH_collapse_of_NP_subset_BPP H L

/-- **`P = NP ⇒ BPP = P`** (Sipser–Gács–Lautemann + PH collapse). -/
theorem BPP_eq_P_of_P_eq_NP (h : P_eq_NP) (L : Language) : InBPP L ↔ InP L :=
  PvnpReal.BPP_eq_P_of_P_eq_NP h L

/-- **`P = NP ⇒ RP = P`**. -/
theorem RP_eq_P_of_P_eq_NP (h : P_eq_NP) (L : Language) : InRP L ↔ InP L :=
  PvnpReal.RP_eq_P_of_P_eq_NP h L

/-- **`P = NP ⇒ ZPP = P`**. -/
theorem ZPP_eq_P_of_P_eq_NP (h : P_eq_NP) (L : Language) : InZPP L ↔ InP L :=
  ⟨fun hz => (RP_eq_P_of_P_eq_NP h L).1 hz.1, P_subset_ZPP⟩

/-- **Search-to-decision for `NP`**: `NP ⊆ BPP ⇒ NP ⊆ RP`. -/
theorem NP_subset_RP_of_NP_subset_BPP (H : ∀ L, InNP L → InBPP L) {L : Language} (hL : InNP L) :
    InRP L :=
  PvnpReal.NP_subset_RP_of_NP_subset_BPP H hL

/-- **`NP ⊆ BPP ⟹ NP = RP`**. -/
theorem NP_eq_RP_of_NP_subset_BPP (H : ∀ L, InNP L → InBPP L) (L : Language) :
    InNP L ↔ InRP L :=
  PvnpReal.NP_eq_RP_of_NP_subset_BPP H L

-- ============================================================
-- SECTION 13: UNCONDITIONAL BOOLEAN & REDUCTION CLOSURES
-- ============================================================

section PairBridge

open Turing TM2 Computability

private inductive PBK | inp | sc | out
  deriving DecidableEq

private instance : Fintype PBK := ⟨{.inp, .sc, .out}, fun k => by cases k <;> simp⟩

private abbrev PBΓ : PBK → Type
  | .inp => Option Bool
  | _ => Bool

private abbrev PBσ := Option (Option Bool)

private def pbSt (i : List (Option Bool)) (s o : List Bool) : ∀ k : PBK, List (PBΓ k)
  | .inp => i
  | .sc => s
  | .out => o

@[simp] private theorem pb_upd_inp (i s o x) :
    Function.update (pbSt i s o) .inp x = pbSt x s o := by
  funext k; cases k <;> rfl
@[simp] private theorem pb_upd_sc (i s o x) :
    Function.update (pbSt i s o) .sc x = pbSt i x o := by
  funext k; cases k <;> rfl
@[simp] private theorem pb_upd_out (i s o x) :
    Function.update (pbSt i s o) .out x = pbSt i s x := by
  funext k; cases k <;> rfl

private def mvStmt {Λ : Type} (self : Λ) : TM2.Stmt PBΓ Λ PBσ :=
  TM2.Stmt.pop .sc (fun _ o => o.map some)
    (TM2.Stmt.branch Option.isSome
      (TM2.Stmt.push .out (fun s => match s with | some (some b) => b | _ => false)
        (TM2.Stmt.goto fun _ => self))
      TM2.Stmt.halt)

private theorem run_mv {Λ : Type} (m : Λ → TM2.Stmt PBΓ Λ PBσ) (mvL : Λ)
    (hm : m mvL = mvStmt mvL) (s o : List Bool) (v : PBσ) :
    (flip bind (TM2.step m))^[s.length + 1] (some ⟨some mvL, v, pbSt [] s o⟩) =
      some ⟨none, none, pbSt [] [] (s.reverse ++ o)⟩ := by
  induction s generalizing v o with
  | nil =>
    show some (TM2.stepAux (m mvL) v (pbSt [] [] o)) = _
    rw [hm]
    simp [mvStmt, TM2.stepAux, pbSt]
  | cons b s ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step m) (some ⟨some mvL, v, pbSt [] (b :: s) o⟩) =
        some ⟨some mvL, some (some b), pbSt [] s (b :: o)⟩ := by
      show some (TM2.stepAux (m mvL) v (pbSt [] (b :: s) o)) = _
      rw [hm]
      simp [mvStmt, TM2.stepAux, pbSt]
    rw [e, ih]; simp

private inductive PEncL | enc | mv
  deriving DecidableEq

private instance : Fintype PEncL := ⟨{.enc, .mv}, fun k => by cases k <;> simp⟩

private def encBit : Option Bool → List Bool
  | none => [false]
  | some false => [true, false]
  | some true => [true, true, false]

private def encSeq (l : List (Option Bool)) : List Bool :=
  l.flatMap encBit

private theorem encSeq_len (l : List (Option Bool)) : (encSeq l).length ≤ 3 * l.length := by
  induction l with
  | nil => simp [encSeq]
  | cons o l ih =>
    rcases o with _ | b <;> [skip; cases b] <;> simp [encSeq, encBit] at ih ⊢ <;> omega

private theorem encSeq_pairEnc (p : List Bool × List Bool) :
    encSeq (PvnpReal.pairEnc p) = PvnpReal.codeP p.1 p.2 := by
  have hc : ∀ a : List Bool, encSeq (a.map some) = PvnpReal.codeL a := by
    intro a
    induction a with
    | nil => simp [encSeq, PvnpReal.codeL]
    | cons b a ih => cases b <;> simp [encSeq, encBit, PvnpReal.codeL] at ih ⊢ <;> exact ih
  simp only [encSeq, PvnpReal.pairEnc, List.flatMap_append, List.flatMap_cons]
  change encSeq (p.1.map some) ++ (encBit none ++ encSeq (p.2.map some)) =
    PvnpReal.codeL p.1 ++ false :: PvnpReal.codeL p.2
  rw [hc p.1, hc p.2]
  rfl

private def encStmt : PEncL → TM2.Stmt PBΓ PEncL PBσ
  | .enc => TM2.Stmt.pop .inp (fun _ o => o)
      (TM2.Stmt.branch Option.isSome
        (TM2.Stmt.branch (fun s => match s with | some (some true) => true | _ => false)
          (TM2.Stmt.push .sc (fun _ => true)
            (TM2.Stmt.push .sc (fun _ => true)
              (TM2.Stmt.push .sc (fun _ => false) (TM2.Stmt.goto fun _ => .enc))))
          (TM2.Stmt.branch (fun s => match s with | some (some false) => true | _ => false)
            (TM2.Stmt.push .sc (fun _ => true)
              (TM2.Stmt.push .sc (fun _ => false) (TM2.Stmt.goto fun _ => .enc)))
            (TM2.Stmt.push .sc (fun _ => false) (TM2.Stmt.goto fun _ => .enc))))
        (TM2.Stmt.goto fun _ => .mv))
  | .mv => mvStmt .mv

private def encTM : Turing.FinTM2 where
  K := PBK
  k₀ := .inp
  k₁ := .out
  Γ := PBΓ
  Λ := PEncL
  main := .enc
  σ := PBσ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := encStmt

private theorem enc_loop (l : List (Option Bool)) (s : List Bool) (v : PBσ) :
    (flip bind (TM2.step encStmt))^[l.length + 1] (some ⟨some .enc, v, pbSt l s []⟩) =
      some ⟨some .mv, none, pbSt [] ((encSeq l).reverse ++ s) []⟩ := by
  induction l generalizing s v with
  | nil => simp [TM2.step, encStmt, TM2.stepAux, encSeq, pbSt, flip]
  | cons o l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    rcases o with _ | b
    · have e : flip bind (TM2.step encStmt) (some ⟨some .enc, v, pbSt (none :: l) s []⟩) =
          some ⟨some .enc, some none, pbSt l (false :: s) []⟩ := by
        simp [TM2.step, encStmt, TM2.stepAux, pbSt, flip]
      rw [e, ih]; simp [encSeq, encBit]
    · cases b
      · have e : flip bind (TM2.step encStmt)
            (some ⟨some .enc, v, pbSt (some false :: l) s []⟩) =
            some ⟨some .enc, some (some false), pbSt l (false :: true :: s) []⟩ := by
          simp [TM2.step, encStmt, TM2.stepAux, pbSt, flip]
        rw [e, ih]; simp [encSeq, encBit]
      · have e : flip bind (TM2.step encStmt)
            (some ⟨some .enc, v, pbSt (some true :: l) s []⟩) =
            some ⟨some .enc, some (some true), pbSt l (false :: true :: true :: s) []⟩ := by
          simp [TM2.step, encStmt, TM2.stepAux, pbSt, flip]
        rw [e, ih]; simp [encSeq, encBit]

private noncomputable def pairToCodeP :
    TM2ComputableInPolyTime PvnpReal.pairEnc PvnpReal.strEnc (fun p => PvnpReal.codeP p.1 p.2) where
  tm := encTM
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 2
  outputsFun p :=
    { steps := ((encSeq (PvnpReal.pairEnc p)).length + 1) + ((PvnpReal.pairEnc p).length + 1)
      evals_in_steps := by
        have h1 := enc_loop (PvnpReal.pairEnc p) [] none
        have h2 := run_mv encStmt .mv rfl (encSeq (PvnpReal.pairEnc p)).reverse [] none
        simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2
        have h3 := PvnpReal.iter_chain h1 h2
        rw [encSeq_pairEnc] at h3
        have ei : initList encTM (PvnpReal.pairEnc p) =
            (⟨some .enc, none, pbSt (PvnpReal.pairEnc p) [] []⟩ : encTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList encTM (PvnpReal.codeP p.1 p.2) =
            (⟨none, none, pbSt [] [] (PvnpReal.codeP p.1 p.2)⟩ : encTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        rw [encSeq_pairEnc]
        exact h3
      steps_le_m := by
        have hl := encSeq_len (PvnpReal.pairEnc p)
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_ofNat]
        omega }

private inductive PFstL | rd | clr | mv
  deriving DecidableEq

private instance : Fintype PFstL := ⟨{.rd, .clr, .mv}, fun k => by cases k <;> simp⟩

private def fstStmt : PFstL → TM2.Stmt PBΓ PFstL PBσ
  | .rd => TM2.Stmt.pop .inp (fun _ o => o)
      (TM2.Stmt.branch Option.isSome
        (TM2.Stmt.branch (fun s => s == some none) (TM2.Stmt.goto fun _ => .clr)
          (TM2.Stmt.push .sc (fun s => match s with | some (some b) => b | _ => false)
            (TM2.Stmt.goto fun _ => .rd)))
        (TM2.Stmt.goto fun _ => .mv))
  | .clr => TM2.Stmt.pop .inp (fun _ o => o)
      (TM2.Stmt.branch Option.isSome (TM2.Stmt.goto fun _ => .clr) (TM2.Stmt.goto fun _ => .mv))
  | .mv => mvStmt .mv

private def fstTM : Turing.FinTM2 where
  K := PBK
  k₀ := .inp
  k₁ := .out
  Γ := PBΓ
  Λ := PFstL
  main := .rd
  σ := PBσ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := fstStmt

private theorem fst_clr (b : List Bool) (s : List Bool) (v : PBσ) :
    (flip bind (TM2.step fstStmt))^[b.length + 1]
        (some ⟨some .clr, v, pbSt (b.map some) s []⟩) =
      some ⟨some .mv, none, pbSt [] s []⟩ := by
  induction b generalizing v with
  | nil => simp [TM2.step, fstStmt, TM2.stepAux, pbSt, flip]
  | cons x b ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step fstStmt)
        (some ⟨some .clr, v, pbSt ((x :: b).map some) s []⟩) =
        some ⟨some .clr, some (some x), pbSt (b.map some) s []⟩ := by
      simp [TM2.step, fstStmt, TM2.stepAux, pbSt, flip]
    rw [e, ih]

private theorem fst_rd (a b s : List Bool) (v : PBσ) :
    (flip bind (TM2.step fstStmt))^[a.length + 1]
        (some ⟨some .rd, v, pbSt (a.map some ++ none :: b.map some) s []⟩) =
      some ⟨some .clr, some none, pbSt (b.map some) (a.reverse ++ s) []⟩ := by
  induction a generalizing s v with
  | nil => simp [TM2.step, fstStmt, TM2.stepAux, pbSt, flip]
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step fstStmt)
        (some ⟨some .rd, v, pbSt ((x :: a).map some ++ none :: b.map some) s []⟩) =
        some ⟨some .rd, some (some x), pbSt (a.map some ++ none :: b.map some) (x :: s) []⟩ := by
      simp [TM2.step, fstStmt, TM2.stepAux, pbSt, flip]
    rw [e, ih]; simp

private noncomputable def pairFst :
    TM2ComputableInPolyTime PvnpReal.pairEnc PvnpReal.strEnc Prod.fst where
  tm := fstTM
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun p :=
    { steps := (p.1.length + 1) + (p.2.length + 1) + (p.1.length + 1)
      evals_in_steps := by
        rcases p with ⟨a, b⟩
        have h1 := fst_rd a b [] none
        have h2 := fst_clr b a.reverse (some none)
        have h3 := run_mv fstStmt .mv rfl a.reverse [] none
        simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2 h3
        have h4 := PvnpReal.iter_chain h1 (PvnpReal.iter_chain h2 h3)
        have ei : initList fstTM (PvnpReal.pairEnc (a, b)) =
            (⟨some .rd, none, pbSt (a.map some ++ none :: b.map some) [] []⟩ : fstTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList fstTM a = (⟨none, none, pbSt [] [] a⟩ : fstTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact h4
      steps_le_m := by
        simp only [PvnpReal.pairEnc, List.length_append, List.length_map, List.length_cons,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
        omega }

private inductive PSndL | sk | rd | mv
  deriving DecidableEq

private instance : Fintype PSndL := ⟨{.sk, .rd, .mv}, fun k => by cases k <;> simp⟩

private def sndStmt : PSndL → TM2.Stmt PBΓ PSndL PBσ
  | .sk => TM2.Stmt.pop .inp (fun _ o => o)
      (TM2.Stmt.branch Option.isSome
        (TM2.Stmt.branch (fun s => s == some none) (TM2.Stmt.goto fun _ => .rd)
          (TM2.Stmt.goto fun _ => .sk))
        (TM2.Stmt.goto fun _ => .mv))
  | .rd => TM2.Stmt.pop .inp (fun _ o => o)
      (TM2.Stmt.branch Option.isSome
        (TM2.Stmt.push .sc (fun s => match s with | some (some b) => b | _ => false)
          (TM2.Stmt.goto fun _ => .rd))
        (TM2.Stmt.goto fun _ => .mv))
  | .mv => mvStmt .mv

private def sndTM : Turing.FinTM2 where
  K := PBK
  k₀ := .inp
  k₁ := .out
  Γ := PBΓ
  Λ := PSndL
  main := .sk
  σ := PBσ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := sndStmt

private theorem snd_sk (a b : List Bool) (v : PBσ) :
    (flip bind (TM2.step sndStmt))^[a.length + 1]
        (some ⟨some .sk, v, pbSt (a.map some ++ none :: b.map some) [] []⟩) =
      some ⟨some .rd, some none, pbSt (b.map some) [] []⟩ := by
  induction a generalizing v with
  | nil => simp [TM2.step, sndStmt, TM2.stepAux, pbSt, flip]
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sndStmt)
        (some ⟨some .sk, v, pbSt ((x :: a).map some ++ none :: b.map some) [] []⟩) =
        some ⟨some .sk, some (some x), pbSt (a.map some ++ none :: b.map some) [] []⟩ := by
      simp [TM2.step, sndStmt, TM2.stepAux, pbSt, flip]
    rw [e, ih]

private theorem snd_rd (b s : List Bool) (v : PBσ) :
    (flip bind (TM2.step sndStmt))^[b.length + 1]
        (some ⟨some .rd, v, pbSt (b.map some) s []⟩) =
      some ⟨some .mv, none, pbSt [] (b.reverse ++ s) []⟩ := by
  induction b generalizing s v with
  | nil => simp [TM2.step, sndStmt, TM2.stepAux, pbSt, flip]
  | cons x b ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step sndStmt)
        (some ⟨some .rd, v, pbSt ((x :: b).map some) s []⟩) =
        some ⟨some .rd, some (some x), pbSt (b.map some) (x :: s) []⟩ := by
      simp [TM2.step, sndStmt, TM2.stepAux, pbSt, flip]
    rw [e, ih]; simp

private noncomputable def pairSnd :
    TM2ComputableInPolyTime PvnpReal.pairEnc PvnpReal.strEnc Prod.snd where
  tm := sndTM
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun p :=
    { steps := (p.2.length + 1) + (p.2.length + 1) + (p.1.length + 1)
      evals_in_steps := by
        rcases p with ⟨a, b⟩
        have h1 := snd_sk a b none
        have h2 := snd_rd b [] (some none)
        have h3 := run_mv sndStmt .mv rfl b.reverse [] none
        simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h2 h3
        have h4 := PvnpReal.iter_chain h1 (PvnpReal.iter_chain h2 h3)
        have ei : initList sndTM (PvnpReal.pairEnc (a, b)) =
            (⟨some .sk, none, pbSt (a.map some ++ none :: b.map some) [] []⟩ : sndTM.Cfg) := by
          simp only [initList]; congr 1; funext k; cases k <;> rfl
        have eh : haltList sndTM b = (⟨none, none, pbSt [] [] b⟩ : sndTM.Cfg) := by
          simp only [haltList]; congr 1; funext k; cases k <;> rfl
        erw [List.map_id, List.map_id, Option.map_some, ei, eh]
        exact h4
      steps_le_m := by
        simp only [PvnpReal.pairEnc, List.length_append, List.length_map, List.length_cons,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
        omega }

private theorem PS_decP1 : PvnpReal.PS (fun z => (PvnpReal.decP z).1) :=
  ⟨PvnpReal.composeGen PvnpReal.decComputable pairFst⟩

private theorem PS_decP2 : PvnpReal.PS (fun z => (PvnpReal.decP z).2) :=
  ⟨PvnpReal.composeGen PvnpReal.decComputable pairSnd⟩

private theorem codeL_len (a : List Bool) : (PvnpReal.codeL a).length ≤ 3 * a.length := by
  induction a with
  | nil => simp [PvnpReal.codeL]
  | cons b a ih => cases b <;> simp [PvnpReal.codeL] at ih ⊢ <;> omega

private theorem codeP_len (a b : List Bool) :
    (PvnpReal.codeP a b).length ≤ 3 * a.length + 3 * b.length + 1 := by
  have ha := codeL_len a
  have hb := codeL_len b
  simp only [PvnpReal.codeP, List.length_append, List.length_cons]
  omega

end PairBridge

/-- Language congruence closure for `P`. -/
theorem InP.congr {L L' : Language} (h : InP L) (e : ∀ x, L x ↔ L' x) : InP L' :=
  PvnpReal.InP.congr h e

/-- Language congruence closure for `NP`. -/
theorem InNP.congr {L L' : Language} (h : InNP L) (e : ∀ x, L x ↔ L' x) : InNP L' := by
  obtain ⟨V, q, hV, hL⟩ := h
  exact ⟨V, q, hV, fun x => (e x).symm.trans (hL x)⟩

/-- Language congruence closure for `EXP`. -/
theorem InEXP.congr {L L' : Language} (h : InEXP L) (e : ∀ x, L x ↔ L' x) : InEXP L' := by
  obtain ⟨f, p, hf, hL⟩ := h
  exact ⟨f, p, hf, fun x => (e x).symm.trans (hL x)⟩

/-- Language congruence closure for `coNP`. -/
theorem InCoNP.congr {L L' : Language} (h : InCoNP L) (e : ∀ x, L x ↔ L' x) : InCoNP L' :=
  InNP.congr h (fun x => not_congr (e x))

/-- P is closed under intersection. -/
theorem InP.inter {L L' : Language} (h : InP L) (h' : InP L') : InP (fun x => L x ∧ L' x) :=
  PvnpReal.InP.inter h h'

/-- P is closed under union. -/
theorem InP.union {L L' : Language} (h : InP L) (h' : InP L') : InP (fun x => L x ∨ L' x) :=
  PvnpReal.InP.union h h'

/-- P is closed under complement (`P = coP`). -/
theorem InP.compl {L : Language} (h : InP L) : InP (fun x => ¬ L x) :=
  PvnpReal.InP.compl h

/-- Unconditional closure of NP under intersection (`NP` intersection property). -/
theorem InNP.inter {L L' : Language} (h : InNP L) (h' : InNP L') :
    InNP (fun x => L x ∧ L' x) := by
  obtain ⟨g₁, ⟨hg₁⟩, hr₁⟩ := PvnpReal.cookLevin.2 L h
  obtain ⟨g₂, ⟨hg₂⟩, hr₂⟩ := PvnpReal.cookLevin.2 L' h'
  have hv : PvnpReal.PS (fun y => [PvnpReal.verify (PvnpReal.decP y).1 (PvnpReal.decP y).2]) :=
    ⟨PvnpReal.deciderToStr (PvnpReal.composeGen PvnpReal.decComputable PvnpReal.satVerifierComputable)⟩
  have hb₁ : PvnpReal.PS (fun z =>
      [PvnpReal.verify (g₁ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).1]) :=
    (PvnpReal.PS.comp (PvnpReal.PS.append (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP1 ⟨hg₁⟩))
      (PvnpReal.PS.cons false (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP2 PS_decP1)))) hv).congr
      (fun z => by
        show [PvnpReal.verify (PvnpReal.decP (PvnpReal.codeP _ _)).1
          (PvnpReal.decP (PvnpReal.codeP _ _)).2] = _
        rw [PvnpReal.decP_codeP])
  have hb₂ : PvnpReal.PS (fun z =>
      [PvnpReal.verify (g₂ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).2]) :=
    (PvnpReal.PS.comp (PvnpReal.PS.append (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP1 ⟨hg₂⟩))
      (PvnpReal.PS.cons false (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP2 PS_decP2)))) hv).congr
      (fun z => by
        show [PvnpReal.verify (PvnpReal.decP (PvnpReal.codeP _ _)).1
          (PvnpReal.decP (PvnpReal.codeP _ _)).2] = _
        rw [PvnpReal.decP_codeP])
  let V : List Bool × List Bool → Bool :=
    fun p => PvnpReal.verify (g₁ p.1) (PvnpReal.decP p.2).1 &&
      PvnpReal.verify (g₂ p.1) (PvnpReal.decP p.2).2
  have hVstr : PvnpReal.PS (fun z => [V (PvnpReal.decP z)]) := by
    refine (PvnpReal.PS.comp (PvnpReal.PS.append hb₁ hb₂) ⟨PvnpReal.andComputable⟩).congr
      (fun z => ?_)
    show PvnpReal.SmallTM.andF [PvnpReal.verify (g₁ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).1,
      PvnpReal.verify (g₂ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).2] = _
    dsimp only [V]
    cases PvnpReal.verify (g₁ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).1 <;>
      cases PvnpReal.verify (g₂ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).2 <;> rfl
  obtain ⟨hVs⟩ := hVstr
  have hVc : Turing.TM2ComputableInPolyTime PvnpReal.pairEnc Computability.encodeBool V := by
    have hcomp := PvnpReal.composeGen pairToCodeP (PvnpReal.strToDecider hVs)
    have hEq : ((fun z => V (PvnpReal.decP z)) ∘ fun p : List Bool × List Bool => PvnpReal.codeP p.1 p.2) = V := by
      funext p
      simp only [Function.comp_apply, PvnpReal.decP_codeP]
    exact hEq ▸ hcomp
  let q₁ : Polynomial ℕ := Polynomial.X + (PvnpReal.pushTotal hg₁.tm : Polynomial ℕ) * hg₁.time
  let q₂ : Polynomial ℕ := Polynomial.X + (PvnpReal.pushTotal hg₂.tm : Polynomial ℕ) * hg₂.time
  refine ⟨V, 3 * q₁ + 3 * q₂ + 1, ⟨hVc⟩, fun x => ?_⟩
  dsimp only
  rw [hr₁, hr₂]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    obtain ⟨w₁, hw₁, hv₁⟩ := (PvnpReal.SATLang_iff_verify (g₁ x)).1 hx₁
    obtain ⟨w₂, hw₂, hv₂⟩ := (PvnpReal.SATLang_iff_verify (g₂ x)).1 hx₂
    have hgl₁ := PvnpReal.outLen_bound hg₁ x
    have hgl₂ := PvnpReal.outLen_bound hg₂ x
    simp only [PvnpReal.strEnc] at hgl₁ hgl₂
    refine ⟨PvnpReal.codeP w₁ w₂, ?_, ?_⟩
    · have hc := codeP_len w₁ w₂
      simp only [q₁, q₂, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_one, Nat.cast_id] at *
      omega
    · simp only [V, PvnpReal.decP_codeP, Bool.and_eq_true]
      exact ⟨hv₁, hv₂⟩
  · rintro ⟨w, -, hv⟩
    simp only [V, Bool.and_eq_true] at hv
    obtain ⟨φ₁, hφ₁, hs₁⟩ := PvnpReal.verify_sound _ _ hv.1
    obtain ⟨φ₂, hφ₂, hs₂⟩ := PvnpReal.verify_sound _ _ hv.2
    rw [hφ₁, hφ₂]
    exact ⟨(PvnpReal.SATLang_encode_iff φ₁).2 ⟨PvnpReal.asg _, hs₁⟩,
           (PvnpReal.SATLang_encode_iff φ₂).2 ⟨PvnpReal.asg _, hs₂⟩⟩

/-- Unconditional closure of NP under union (`NP` union property). -/
theorem InNP.union {L L' : Language} (h : InNP L) (h' : InNP L') :
    InNP (fun x => L x ∨ L' x) := by
  obtain ⟨g₁, ⟨hg₁⟩, hr₁⟩ := PvnpReal.cookLevin.2 L h
  obtain ⟨g₂, ⟨hg₂⟩, hr₂⟩ := PvnpReal.cookLevin.2 L' h'
  have hv : PvnpReal.PS (fun y => [PvnpReal.verify (PvnpReal.decP y).1 (PvnpReal.decP y).2]) :=
    ⟨PvnpReal.deciderToStr (PvnpReal.composeGen PvnpReal.decComputable PvnpReal.satVerifierComputable)⟩
  have hb₁ : PvnpReal.PS (fun z =>
      [PvnpReal.verify (g₁ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).1]) :=
    (PvnpReal.PS.comp (PvnpReal.PS.append (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP1 ⟨hg₁⟩))
      (PvnpReal.PS.cons false (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP2 PS_decP1)))) hv).congr
      (fun z => by
        show [PvnpReal.verify (PvnpReal.decP (PvnpReal.codeP _ _)).1
          (PvnpReal.decP (PvnpReal.codeP _ _)).2] = _
        rw [PvnpReal.decP_codeP])
  have hb₂ : PvnpReal.PS (fun z =>
      [PvnpReal.verify (g₂ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).2]) :=
    (PvnpReal.PS.comp (PvnpReal.PS.append (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP1 ⟨hg₂⟩))
      (PvnpReal.PS.cons false (PvnpReal.PS.codeL (PvnpReal.PS.comp PS_decP2 PS_decP2)))) hv).congr
      (fun z => by
        show [PvnpReal.verify (PvnpReal.decP (PvnpReal.codeP _ _)).1
          (PvnpReal.decP (PvnpReal.codeP _ _)).2] = _
        rw [PvnpReal.decP_codeP])
  let V : List Bool × List Bool → Bool :=
    fun p => PvnpReal.verify (g₁ p.1) (PvnpReal.decP p.2).1 ||
      PvnpReal.verify (g₂ p.1) (PvnpReal.decP p.2).2
  have hVstr : PvnpReal.PS (fun z => [V (PvnpReal.decP z)]) := by
    refine (PvnpReal.PS.comp (PvnpReal.PS.append hb₁ hb₂) ⟨PvnpReal.orComputable⟩).congr
      (fun z => ?_)
    show PvnpReal.SmallTM.orF [PvnpReal.verify (g₁ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).1,
      PvnpReal.verify (g₂ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).2] = _
    dsimp only [V]
    cases PvnpReal.verify (g₁ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).1 <;>
      cases PvnpReal.verify (g₂ (PvnpReal.decP z).1) (PvnpReal.decP (PvnpReal.decP z).2).2 <;> rfl
  obtain ⟨hVs⟩ := hVstr
  have hVc : Turing.TM2ComputableInPolyTime PvnpReal.pairEnc Computability.encodeBool V := by
    have hcomp := PvnpReal.composeGen pairToCodeP (PvnpReal.strToDecider hVs)
    have hEq : ((fun z => V (PvnpReal.decP z)) ∘ fun p : List Bool × List Bool => PvnpReal.codeP p.1 p.2) = V := by
      funext p
      simp only [Function.comp_apply, PvnpReal.decP_codeP]
    exact hEq ▸ hcomp
  let q₁ : Polynomial ℕ := Polynomial.X + (PvnpReal.pushTotal hg₁.tm : Polynomial ℕ) * hg₁.time
  let q₂ : Polynomial ℕ := Polynomial.X + (PvnpReal.pushTotal hg₂.tm : Polynomial ℕ) * hg₂.time
  refine ⟨V, 3 * q₁ + 3 * q₂ + 1, ⟨hVc⟩, fun x => ?_⟩
  dsimp only
  rw [hr₁, hr₂]
  constructor
  · rintro (hx₁ | hx₂)
    · obtain ⟨w₁, hw₁, hv₁⟩ := (PvnpReal.SATLang_iff_verify (g₁ x)).1 hx₁
      have hgl₁ := PvnpReal.outLen_bound hg₁ x
      simp only [PvnpReal.strEnc] at hgl₁
      refine ⟨PvnpReal.codeP w₁ [], ?_, ?_⟩
      · have hc := codeP_len w₁ []
        simp only [List.length_nil, mul_zero, add_zero] at hc
        simp only [q₁, q₂, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_one, Nat.cast_id] at *
        omega
      · simp only [V, PvnpReal.decP_codeP, hv₁, Bool.true_or]
    · obtain ⟨w₂, hw₂, hv₂⟩ := (PvnpReal.SATLang_iff_verify (g₂ x)).1 hx₂
      have hgl₂ := PvnpReal.outLen_bound hg₂ x
      simp only [PvnpReal.strEnc] at hgl₂
      refine ⟨PvnpReal.codeP [] w₂, ?_, ?_⟩
      · have hc := codeP_len [] w₂
        simp only [List.length_nil, mul_zero, zero_add] at hc
        simp only [q₁, q₂, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_one, Nat.cast_id] at *
        omega
      · simp only [V, PvnpReal.decP_codeP, hv₂, Bool.or_true]
  · rintro ⟨w, -, hv⟩
    simp only [V, Bool.or_eq_true] at hv
    rcases hv with h1 | h2
    · obtain ⟨φ₁, hφ₁, hs₁⟩ := PvnpReal.verify_sound _ _ h1
      rw [hφ₁]
      exact Or.inl ((PvnpReal.SATLang_encode_iff φ₁).2 ⟨PvnpReal.asg _, hs₁⟩)
    · obtain ⟨φ₂, hφ₂, hs₂⟩ := PvnpReal.verify_sound _ _ h2
      rw [hφ₂]
      exact Or.inr ((PvnpReal.SATLang_encode_iff φ₂).2 ⟨PvnpReal.asg _, hs₂⟩)

/-- Unconditional closure of coNP under intersection. -/
theorem InCoNP.inter {L L' : Language} (h : InCoNP L) (h' : InCoNP L') :
    InCoNP (fun x => L x ∧ L' x) :=
  InNP.congr (InNP.union h h') (fun _ => not_and_or.symm)

/-- Unconditional closure of coNP under union. -/
theorem InCoNP.union {L L' : Language} (h : InCoNP L) (h' : InCoNP L') :
    InCoNP (fun x => L x ∨ L' x) :=
  InNP.congr (InNP.inter h h') (fun _ => not_or.symm)

/-- Under P = NP, NP is closed under intersection. -/
theorem InNP_inter_of_P_eq_NP (_ : P_eq_NP) {L L' : Language} (hL : InNP L) (hL' : InNP L') :
    InNP (fun x => L x ∧ L' x) :=
  InNP.inter hL hL'

/-- Under P = NP, NP is closed under union. -/
theorem InNP_union_of_P_eq_NP (_ : P_eq_NP) {L L' : Language} (hL : InNP L) (hL' : InNP L') :
    InNP (fun x => L x ∨ L' x) :=
  InNP.union hL hL'

/-- Under P = NP, coNP is closed under intersection. -/
theorem InCoNP_inter_of_P_eq_NP (_ : P_eq_NP) {L L' : Language} (hL : InCoNP L) (hL' : InCoNP L') :
    InCoNP (fun x => L x ∧ L' x) :=
  InCoNP.inter hL hL'

/-- Under P = NP, coNP is closed under union. -/
theorem InCoNP_union_of_P_eq_NP (_ : P_eq_NP) {L L' : Language} (hL : InCoNP L) (hL' : InCoNP L') :
    InCoNP (fun x => L x ∨ L' x) :=
  InCoNP.union hL hL'

/-- EXP is closed under complement. -/
theorem InEXP.compl {L : Language} (h : InEXP L) : InEXP (fun x => ¬ L x) :=
  PvnpReal.InEXP.compl h

/-- Unconditional closure of EXP under intersection (`EXP` intersection property). -/
theorem InEXP.inter {L L' : Language} (h : InEXP L) (h' : InEXP L') :
    InEXP (fun x => L x ∧ L' x) := by
  obtain ⟨f₁, p₁, ⟨hf₁, hfb₁⟩, hL₁⟩ := h
  obtain ⟨f₂, p₂, ⟨hf₂, hfb₂⟩, hL₂⟩ := h'
  let fm : List Bool → List Bool := fun x => [f₁ x, f₂ x]
  let hfan : Turing.TM2ComputableInTime PvnpReal.strEnc PvnpReal.strEnc fm :=
    { tm := PvnpReal.fanTM hf₁.tm hf₂.tm hf₁.inputAlphabet hf₁.outputAlphabet
        hf₂.inputAlphabet hf₂.outputAlphabet
      inputAlphabet := hf₁.inputAlphabet
      outputAlphabet := Equiv.refl Bool
      time := fun n => 2 * n + hf₁.time n + hf₂.time n + 12
      outputsFun x := by
        have hx₁ := hf₁.outputsFun x
        have hx₂ := hf₂.outputsFun x
        have e₁ := hx₁.evals_in_steps
        have e₂ := hx₂.evals_in_steps
        simp only [Option.map_some] at e₁ e₂
        have hfan_run := PvnpReal.fan_run hf₁.tm hf₂.tm hf₁.inputAlphabet hf₁.outputAlphabet
          hf₂.inputAlphabet hf₂.outputAlphabet x [f₁ x] [f₂ x] _ _ e₁ e₂
        refine
          { steps := Classical.choose hfan_run
            evals_in_steps := by
              have hr := (Classical.choose_spec hfan_run).2
              erw [List.map_id, Option.map_some]
              exact hr
            steps_le_m := by
              have hn := (Classical.choose_spec hfan_run).1
              have hs₁ := hx₁.steps_le_m
              have hs₂ := hx₂.steps_le_m
              simp only [PvnpReal.strEnc, List.length_singleton] at *
              omega } }
  have hBm : Monotone (fun m : ℕ => m + 2) := fun _ _ hab => Nat.add_le_add_right hab 2
  let hc := PvnpReal.composeInTime hfan PvnpReal.andComputable.toTM2ComputableInTime
    (fun m => m + 2)
    (fun m => by show Polynomial.eval m (Polynomial.X + 2) ≤ m + 2; simp) hBm
  let hfin : Turing.TM2ComputableInTime PvnpReal.strEnc Computability.encodeBool
      (fun x => f₁ x && f₂ x) :=
    ⟨hc.toTM2ComputableAux, hc.time, fun x => by
      have ho := hc.outputsFun x
      have e : (PvnpReal.SmallTM.andF ∘ fm) x = Computability.encodeBool (f₁ x && f₂ x) := by
        show PvnpReal.SmallTM.andF [f₁ x, f₂ x] = [f₁ x && f₂ x]
        cases f₁ x <;> cases f₂ x <;> rfl
      rw [e] at ho
      exact ho⟩
  let C₁ := PvnpReal.pushTotal hfan.tm
  let M : Polynomial ℕ := p₁ + p₂ + Polynomial.X
  let K := 48 * C₁ + 23
  refine ⟨fun x => f₁ x && f₂ x, M + Polynomial.C K, ⟨hfin, fun n => ?_⟩, fun x => ?_⟩
  · show hfan.time n + 2 * (n + C₁ * hfan.time n) + 2 + ((n + C₁ * hfan.time n) + 2) ≤
      2 ^ (M + Polynomial.C K).eval n
    have ht₁ : hf₁.time n ≤ 2 ^ M.eval n :=
      (hfb₁ n).trans (Nat.pow_le_pow_right (by norm_num) (by simp [M]; omega))
    have ht₂ : hf₂.time n ≤ 2 ^ M.eval n :=
      (hfb₂ n).trans (Nat.pow_le_pow_right (by norm_num) (by simp [M]; omega))
    have hnM : n ≤ 2 ^ M.eval n :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by simp [M]))
    have h1M : 1 ≤ 2 ^ M.eval n := Nat.one_le_two_pow
    have hfan_bd : hfan.time n ≤ 16 * 2 ^ M.eval n := by
      show 2 * n + hf₁.time n + hf₂.time n + 12 ≤ 16 * 2 ^ M.eval n
      omega
    have hK_le : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
    have hExp : (M + Polynomial.C K).eval n = M.eval n + K := by simp [M]
    rw [hExp, Nat.pow_add]
    have hmulK : (48 * C₁ + 23) * 2 ^ M.eval n ≤ 2 ^ M.eval n * 2 ^ K := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hK_le
    nlinarith
  · simp only [hL₁ x, hL₂ x, Bool.and_eq_true]

/-- Unconditional closure of EXP under union (`EXP` union property). -/
theorem InEXP.union {L L' : Language} (h : InEXP L) (h' : InEXP L') :
    InEXP (fun x => L x ∨ L' x) :=
  InEXP.congr (InEXP.compl (InEXP.inter (InEXP.compl h) (InEXP.compl h'))) (fun x => by tauto)

/-- Reflexivity of polynomial-time reductions: `L ≤_p L`. -/
theorem PolyReduces.refl (L : Language) : PolyReduces L L :=
  PvnpReal.PolyReduces.refl L

/-- Transitivity of polynomial-time reductions: `L₁ ≤_p L₂ ∧ L₂ ≤_p L₃ → L₁ ≤_p L₃`. -/
theorem PolyReduces.trans {L L' L'' : Language} (h1 : PolyReduces L L') (h2 : PolyReduces L' L'') :
    PolyReduces L L'' :=
  PvnpReal.PolyReduces.trans h1 h2

/-- Complementation closure of polynomial-time reductions. -/
theorem PolyReduces.compl {L L' : Language} (hr : PolyReduces L L') :
    PolyReduces (fun x => ¬ L x) (fun x => ¬ L' x) :=
  PolyReduces_compl hr

/-- Closure of P under polynomial reductions: `L ≤_p L' ∧ L' ∈ P → L ∈ P`. -/
theorem InP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InP L') : InP L :=
  PvnpReal.InP.of_reduces hr h

/-- Closure of NP under polynomial reductions: `L ≤_p L' ∧ L' ∈ NP → L ∈ NP`. -/
theorem InNP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InNP L') : InNP L :=
  PvnpReal.InNP.of_reduces hr h

/-- Closure of coNP under polynomial reductions: `L ≤_p L' ∧ L' ∈ coNP → L ∈ coNP`. -/
theorem InCoNP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InCoNP L') : InCoNP L :=
  InNP.of_reduces (PolyReduces_compl hr) h

/-- Closure of EXP under polynomial reductions: `L ≤_p L' ∧ L' ∈ EXP → L ∈ EXP`. -/
theorem InEXP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InEXP L') : InEXP L :=
  PvnpReal.InEXP.of_reduces hr h

-- ============================================================
-- SECTION 14: MACHINE-VERIFIED CONCRETE COMPUTATIONAL BENCHMARKS
-- ============================================================

/-- Benchmark 1: Adversarial Deceptive Trap (n = 4, m = 13, Unique Witness mask = 10). -/
def deceptive_trap_4v : Benchmarks.CNF := Benchmarks.deceptive_trap_4v

/-- Benchmark 2: Compact Cook–Levin Gadget (n = 3, m = 4, SAT witness mask = 5). -/
def cook_levin_gadget_3v : Benchmarks.CNF := Benchmarks.cook_levin_gadget_3v

/-- Benchmark 3: Phase Transition Threshold α = 4.2 (n = 5, m = 21, Unique Witness mask = 11). -/
def phase_transition_5v : Benchmarks.CNF := Benchmarks.phase_transition_5v

/-- Benchmark 4: Unsatisfiable Resolution Core (UNSAT, n = 3, m = 8). -/
def unsat_core_3v : Benchmarks.CNF := Benchmarks.unsat_core_3v

/-- Exact characterization of `deceptive_trap_4v`. -/
theorem deceptive_trap_4v_iff (a : Benchmarks.Assignment) :
    Benchmarks.evalCNF Benchmarks.deceptive_trap_4v a = true ↔
      (a 1 = false ∧ a 2 = true ∧ a 3 = false ∧ a 4 = true) :=
  Benchmarks.deceptive_trap_4v_iff a

/-- `deceptive_trap_4v` has a unique satisfying assignment among all 2⁴ = 16 states. -/
theorem deceptive_trap_4v_unique_mask :
    Benchmarks.countSatisfyingMasks 4 Benchmarks.deceptive_trap_4v = 1 :=
  Benchmarks.deceptive_trap_4v_unique_mask

/-- `deceptive_trap_4v` is satisfiable. -/
theorem deceptive_trap_4v_sat : Benchmarks.SAT Benchmarks.deceptive_trap_4v :=
  Benchmarks.deceptive_trap_4v_sat

/-- `cook_levin_gadget_3v` is satisfiable. -/
theorem cook_levin_gadget_3v_sat : Benchmarks.SAT Benchmarks.cook_levin_gadget_3v :=
  Benchmarks.cook_levin_gadget_3v_sat

/-- Exact characterization of `phase_transition_5v`. -/
theorem phase_transition_5v_iff (a : Benchmarks.Assignment) :
    Benchmarks.evalCNF Benchmarks.phase_transition_5v a = true ↔
      (a 1 = true ∧ a 2 = true ∧ a 3 = false ∧ a 4 = true ∧ a 5 = false) :=
  Benchmarks.phase_transition_5v_iff a

/-- `phase_transition_5v` has a unique satisfying assignment among all 2⁵ = 32 states. -/
theorem phase_transition_5v_unique_mask :
    Benchmarks.countSatisfyingMasks 5 Benchmarks.phase_transition_5v = 1 :=
  Benchmarks.phase_transition_5v_unique_mask

/-- `phase_transition_5v` is satisfiable. -/
theorem phase_transition_5v_sat : Benchmarks.SAT Benchmarks.phase_transition_5v :=
  Benchmarks.phase_transition_5v_sat

/-- `unsat_core_3v` has 0 satisfying states among all 2³ = 8 assignments. -/
theorem unsat_core_3v_zero_masks :
    Benchmarks.countSatisfyingMasks 3 Benchmarks.unsat_core_3v = 0 :=
  Benchmarks.unsat_core_3v_zero_masks

/-- `unsat_core_3v` is mathematically unsatisfiable over all assignments `ℕ → Bool`. -/
theorem unsat_core_3v_unsat : ¬ Benchmarks.SAT Benchmarks.unsat_core_3v :=
  Benchmarks.unsat_core_3v_unsat

/-- `SATLang` accepts `cook_levin_gadget_3v`. -/
theorem SATLang_cook_levin_gadget :
    Benchmarks.SATLang (Benchmarks.encodeCNF Benchmarks.cook_levin_gadget_3v) = true :=
  Benchmarks.SATLang_cook_levin_gadget

/-- `SATLang` rejects `unsat_core_3v`. -/
theorem SATLang_unsat_core :
    Benchmarks.SATLang (Benchmarks.encodeCNF Benchmarks.unsat_core_3v) = false :=
  Benchmarks.SATLang_unsat_core

/-- `SATLang` is non-trivial (neither constantly true nor constantly false). -/
theorem SATLang_nontrivial :
    (∃ x, Benchmarks.SATLang x = true) ∧ (∃ y, Benchmarks.SATLang y = false) :=
  Benchmarks.SATLang_nontrivial

/-- `UNSATLang` accepts the unsatisfiable resolution core benchmark. -/
theorem UNSATLang_unsat_core :
    Benchmarks.UNSATLang (Benchmarks.encodeCNF Benchmarks.unsat_core_3v) = true :=
  Benchmarks.UNSATLang_unsat_core

/-- `UNSATLang` rejects the satisfiable Cook–Levin gadget benchmark. -/
theorem UNSATLang_cook_levin_gadget :
    Benchmarks.UNSATLang (Benchmarks.encodeCNF Benchmarks.cook_levin_gadget_3v) = false :=
  Benchmarks.UNSATLang_cook_levin_gadget

/-- Soundness of `Benchmarks.solveSAT`. -/
theorem solveSAT_sound (numVars : ℕ) (cnf : Benchmarks.CNF) (a : Benchmarks.Assignment)
    (h : Benchmarks.solveSAT numVars cnf = some a) : Benchmarks.evalCNF cnf a = true :=
  Benchmarks.solveSAT_sound numVars cnf a h

/-- Soundness & completeness of `Benchmarks.solveSAT`. -/
theorem solveSAT_isSome_iff (numVars : ℕ) (cnf : Benchmarks.CNF) :
    (Benchmarks.solveSAT numVars cnf).isSome = true ↔
      ∃ m < 2 ^ numVars, Benchmarks.evalCNF cnf (Benchmarks.assignOfMask m) = true :=
  Benchmarks.solveSAT_isSome_iff numVars cnf

/-- F₂ Nullstellensatz clause correspondence. -/
theorem evalClauseF2_vanishes_iff (a : Benchmarks.Assignment) (cl : Benchmarks.Clause) :
    Benchmarks.evalClauseF2 a cl = false ↔ Benchmarks.evalClause a cl = true :=
  Benchmarks.evalClauseF2_vanishes_iff a cl

/-- Soundness of conflict-nogood auto-pruning. -/
theorem nogood_pruning_sound (a : Benchmarks.Assignment) (cnf : Benchmarks.CNF)
    (cl : Benchmarks.Clause) (hcl : cl ∈ cnf) (hmatch : Benchmarks.matchesForbiddenCube a cl = true) :
    Benchmarks.evalCNF cnf a = false :=
  Benchmarks.nogood_pruning_sound a cnf cl hcl hmatch

/-- Tseitin circuit gate correctness. -/
theorem gateCNF_iff (w : ℕ) (g : Benchmarks.Gate) (a : Benchmarks.Assignment) :
    Benchmarks.evalCNF (Benchmarks.gateCNF w g) a = true ↔ a w = g.eval a :=
  Benchmarks.gateCNF_iff w g a

/-- Soundness of Karp k-Clique literal compatibility rule. -/
theorem true_literals_compatible (a : Benchmarks.Assignment) (l₁ l₂ : Benchmarks.Literal)
    (h₁ : Benchmarks.evalLiteral a l₁ = true) (h₂ : Benchmarks.evalLiteral a l₂ = true) :
    Benchmarks.compatibleLiterals l₁ l₂ = true :=
  Benchmarks.true_literals_compatible a l₁ l₂ h₁ h₂

/-- Soundness of Karp Subset-Sum clause slack condition. -/
theorem subset_sum_slack_iff :
    ∀ count ≤ 3,
      ((∃ b₁ b₂ : Bool, count + (if b₁ then 1 else 0) + (if b₂ then 2 else 0) = 4) ↔
        1 ≤ count) :=
  Benchmarks.subset_sum_slack_iff

end UnifiedPvnp
