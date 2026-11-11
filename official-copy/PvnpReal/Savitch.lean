/-
  PvnpReal.Savitch — **Savitch's theorem** `NPSPACE = PSPACE`.

  The nondeterministic Savitch QBF `redQN` of `NHard.lean` is computed by a polynomial-time `FinTM2`
  (built from the proven printing combinators, as for `redQ`), so every NPSPACE language reduces to
  TQBF, which is in PSPACE; hence `NPSPACE ⊆ PSPACE`. With `PSPACE ⊆ NPSPACE` (`NSpace.lean`) and
  closure of PSPACE under complement (`PspaceRed.lean`): `NPSPACE = PSPACE`, `coNPSPACE = NPSPACE`.
-/
import PvnpReal.NHard
import PvnpReal.QbfPrint
import PvnpReal.PspaceRed

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

section PiecesN

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [DecidableEq (V2 Γ Λ σ)]
variable (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (d P : ℕ) (Ks : List K) (k₁ : K) (gacc : Γ k₁)
  (U : List (V2 Γ Λ σ))

theorem CFP.csTransN {Sf tf : List Bool → ℕ} (hS : PU Sf) (ht : PU tf)
    (hR2 : PU (fun x => Sf x - (d + P) - (d + 1))) :
    CFP U (fun x => csTransN m alt d P Ks (Sf x) (tf x)) := by
  have hS1 : PU (fun z => Sf (lpX z)) := hS.comp PS.drop
  have ht1 : PU (fun z => tf (lpX z)) := ht.comp PS.drop
  have p1 : CFP U (fun z => [(⟨[sv2 Ks (Sf z) (tf z), sv2 Ks (Sf z) (tf z + 1)],
      ctlRel2 (transCPN m alt)⟩ : Constraint (V2 Γ Λ σ))]) := by
    refine (CFP.single [fun z => sv2 Ks (Sf z) (tf z),
      fun z => sv2 Ks (Sf z) (tf z + 1)] ?_ _).congr (fun x => rfl)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro f (rfl | rfl)
    · exact PU.sv2 Ks hS ht
    · exact PU.sv2 Ks hS (ht.add (PU.const 1))
  have p2 : CFP U (fun z => Ks.flatMap (fun k =>
      (List.range (d + P)).map (fun p =>
        (⟨sv2 Ks (Sf z) (tf z) :: cv2 Ks (Sf z) (tf z + 1) k p ::
          (List.range (p + d + 1)).map (fun i => cv2 Ks (Sf z) (tf z) k i),
          tcRel m d k p p⟩ : Constraint (V2 Γ Λ σ))) ++
      (List.range (Sf z - (d + P) - (d + 1))).map (fun j =>
        (⟨sv2 Ks (Sf z) (tf z) :: cv2 Ks (Sf z) (tf z + 1) k (d + P + j) ::
          (List.range (P + d + 1)).map (fun i => cv2 Ks (Sf z) (tf z) k (d + j + i)),
          tcRel m d k P (d + P)⟩ : Constraint (V2 Γ Λ σ))))) := by
    refine CFP.flatMap_const Ks _ (fun k _ => CFP.append (CFP.map_const _ _ (fun p _ => ?_)) ?_)
    · refine (CFP.single ((fun z => sv2 Ks (Sf z) (tf z)) ::
        (fun z => cv2 Ks (Sf z) (tf z + 1) k p) ::
        (List.range (p + d + 1)).map (fun i z => cv2 Ks (Sf z) (tf z) k i)) ?_
        (tcRel m d k p p)).congr
        (fun x => by simp [List.map_map, Function.comp_def])
      simp only [List.mem_cons, List.mem_map]
      rintro f (rfl | rfl | ⟨i, -, rfl⟩)
      · exact PU.sv2 Ks hS ht
      · exact PU.cv2 Ks hS (ht.add (PU.const 1)) k (PU.const p)
      · exact PU.cv2 Ks hS ht k (PU.const i)
    · refine CFP.mapRange hR2 (fun j z =>
        (⟨sv2 Ks (Sf z) (tf z) :: cv2 Ks (Sf z) (tf z + 1) k (d + P + j) ::
          (List.range (P + d + 1)).map (fun i => cv2 Ks (Sf z) (tf z) k (d + j + i)),
          tcRel m d k P (d + P)⟩ : Constraint (V2 Γ Λ σ))) ?_
      refine (CFP.single ((fun z => sv2 Ks (Sf (lpX z)) (tf (lpX z))) ::
        (fun z => cv2 Ks (Sf (lpX z)) (tf (lpX z) + 1) k (d + P + lpN z)) ::
        (List.range (P + d + 1)).map (fun i z =>
          cv2 Ks (Sf (lpX z)) (tf (lpX z)) k (d + lpN z + i))) ?_
        (tcRel m d k P (d + P))).congr
        (fun x => by simp [List.map_map, Function.comp_def])
      simp only [List.mem_cons, List.mem_map]
      rintro f (rfl | rfl | ⟨i, -, rfl⟩)
      · exact PU.sv2 Ks hS1 ht1
      · exact PU.cv2 Ks hS1 (ht1.add (PU.const 1)) k ((PU.const (d + P)).add PU.fst)
      · exact PU.cv2 Ks hS1 ht1 k (((PU.const d).add PU.fst).add (PU.const i))
  exact (p1.append p2).congr (fun x => rfl)


/-! ### The reduction is polynomial-time computable -/

open scoped Classical


theorem CFP.csFinalH {Sf Tf : List Bool → ℕ} (hS : PU Sf) (hT : PU Tf) :
    CFP U (fun x => csFinalH (Λ := Λ) (σ := σ) Ks (Sf x) (Tf x) k₁ gacc) := by
  have h2 : CFP U (fun x => [(⟨[sv2 Ks (Sf x) (Tf x)], ctlRel1 (fun R => R.l = none)⟩ :
      Constraint (V2 Γ Λ σ))]) :=
    (CFP.single [fun x => sv2 Ks (Sf x) (Tf x)] (by
      simp only [List.mem_singleton]; rintro f rfl; exact PU.sv2 Ks hS hT) _).congr (fun x => rfl)
  exact ((CFP.csFinal Ks k₁ gacc U hS hT).append h2).congr (fun x => rfl)

end PiecesN

open scoped Classical

section NPrint

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (N : NTM) (p : Polynomial ℕ)

theorem PU.nSu : PU (fun x => nS N p x) :=
  ((((PU.poly p).add (PU.const (2 * clD N.tm))).add (PU.const (pushTotal N.tm))).add
    PU.lenX).add (PU.const 3) |>.congr (fun _ => rfl)

theorem PU.nku : PU (fun x => nk N p x) :=
  ((PU.const N.cA).add ((PU.const N.cB).mul (PU.poly p))).congr (fun _ => rfl)

theorem PU.nWu : PU (fun x => W2 (clKs N.tm) (nS N p x)) :=
  ((PU.const 1).add ((PU.const _).mul (PU.nSu N p))).congr (fun _ => rfl)

theorem PU.nnu : PU (fun x => nn N p x) := ((PU.nWu N p).mul (PU.const _)).congr (fun _ => rfl)

theorem PS.nTopP : PS (fun x => clStream (nTop N p x)) := by
  have hSP := PU.nSu N p
  have hR1 : PU (fun x => nS N p x - (x.length + 1 + 0)) :=
    hSP.sub ((PU.lenX.add (PU.const 1)).add (PU.const 0))
  have hC : CFP (nU N) (fun x => csZ (Λ := N.tm.Λ) (σ := N.tm.σ) N.tm.k₀ N.sb ++
      csInit (clKs N.tm) (nS N p x) N.tm.k₀ N.tm.main N.tm.initialState N.sb N.sep 0 x ++
        csFinalH (clKs N.tm) (nS N p x) 1 N.tm.k₁ N.acc) :=
    ((CFP.const _).append (CFP.csInit (clKs N.tm) N.tm.k₀ N.tm.main N.tm.initialState
      N.sb N.sep (nU N) hSP (PU.const 0) hR1)).append
      (CFP.csFinalH (clKs N.tm) N.tm.k₁ N.acc (nU N) hSP (PU.const 1))
  refine ((PS.ALP (nU N) (PU.const 0) (PU.sv2 (clKs N.tm) hSP (PU.const 2))).append
    (PS.HCP (nU N) hC)).congr (fun x => ?_)
  rw [nTop, tabTopN, clStream_append]

theorem PS.nBotP : PS (fun x => clStream (nBot N p x)) := by
  have hSP := PU.nSu N p
  have ht : PU (fun x => 4 * nk N p x) := (PU.const 4).mul (PU.nku N p)
  have hR2 : PU (fun x => nS N p x - (clD N.tm + pushTotal N.tm) - (clD N.tm + 1)) :=
    (hSP.sub (PU.const _)).sub (PU.const _)
  have hR3 : PU (fun x => nS N p x - (clD N.tm + 1)) := hSP.sub (PU.const _)
  have hC := ((CFP.csRow (Γ := N.tm.Γ) (Λ := N.tm.Λ) (σ := N.tm.σ) (clD N.tm)
    (clKs N.tm) (nU N) hSP ht hR3).append (CFP.csRow (clD N.tm) (clKs N.tm) (nU N) hSP
      (ht.add (PU.const 1)) hR3)).append
    (CFP.csTransN N.tm.m N.alt (clD N.tm) (pushTotal N.tm) (clKs N.tm) (nU N) hSP ht hR2)
  refine ((PS.ALP (nU N) (PU.sv2 (clKs N.tm) hSP ht) ((PU.const 2).mul (PU.nWu N p))).append
    (PS.HCP (nU N) hC)).congr (fun x => ?_)
  rw [nBot, tabBtN, clStream_append]

/-- **The nondeterministic Savitch reduction is computed by a polynomial-time `FinTM2`.** -/
theorem redQN_PS : PS (redQN N p) := by
  have hnP := PU.nnu N p
  have hkP := PU.nku N p
  have hX : PS (fun x => (redQBFN N p x).qs) :=
    (PS.repF ((PU.const (2 * (nU N).length)).add ((PU.const 2).mul hnP))).append
      (PS.lvlPreP hnP hkP)
  have hC : PS (fun x => encodeCNF (redQBFN N p x).φ) := by
    refine ((((PS.nTopP N p).append (PS.lvlCNFP hnP (PU.const (2 * (nU N).length)) hkP)).append
      (PS.nBotP N p)).append (PS.const [false])).congr (fun x => ?_)
    rw [encodeCNF_eq]
    simp only [redQBFN, clStream_append, List.append_assoc]
  exact (PS.Rof hX hC).congr (fun x => rfl)

end NPrint

/-! ### Savitch's theorem and corollaries -/

/-- **Every NPSPACE language poly-time reduces to TQBF.** -/
theorem NPSPACE_reduces_TQBF (L : Language) (hL : InNPSPACE L) : PolyReduces L TQBF := by
  obtain ⟨N, p, hsp, hNL⟩ := hL
  exact ⟨redQN N p, redQN_PS N p, fun x => (hNL x).trans (redQN_correct N p hsp x)⟩

/-- **NPSPACE ⊆ PSPACE** (the nontrivial half of Savitch's theorem). -/
theorem NPSPACE_subset_PSPACE (L : Language) (hL : InNPSPACE L) : InPSPACE L :=
  InPSPACE.of_reduces_TQBF (NPSPACE_reduces_TQBF L hL)

/-- **Savitch's theorem: NPSPACE = PSPACE.** -/
theorem NPSPACE_eq_PSPACE (L : Language) : InNPSPACE L ↔ InPSPACE L :=
  ⟨NPSPACE_subset_PSPACE L, PSPACE_subset_NPSPACE L⟩

/-- **NPSPACE is closed under complement.** -/
theorem InNPSPACE.compl {L : Language} (h : InNPSPACE L) : InNPSPACE (fun x => ¬ L x) :=
  (NPSPACE_eq_PSPACE _).2 (NPSPACE_subset_PSPACE L h).compl

/-- **coNPSPACE = NPSPACE.** -/
theorem coNPSPACE_eq_NPSPACE (L : Language) : InCoNPSPACE L ↔ InNPSPACE L := by
  unfold InCoNPSPACE
  constructor
  · intro h
    obtain ⟨N, p, hsp, hx⟩ := InNPSPACE.compl h
    exact ⟨N, p, hsp, fun x => not_not.symm.trans (hx x)⟩
  · exact InNPSPACE.compl

/-- **NP ⊆ coNPSPACE** and **coNP ⊆ NPSPACE**. -/
theorem NP_subset_coNPSPACE (L : Language) (hL : InNP L) : InCoNPSPACE L :=
  (coNPSPACE_eq_NPSPACE L).2 (NP_subset_NPSPACE L hL)

theorem coNP_subset_NPSPACE (L : Language) (hL : InCoNP L) : InNPSPACE L := by
  have h : InNPSPACE (fun x => ¬ L x) := NP_subset_NPSPACE _ hL
  obtain ⟨N, p, hsp, hx⟩ := InNPSPACE.compl h
  exact ⟨N, p, hsp, fun x => not_not.symm.trans (hx x)⟩

end PvnpReal
