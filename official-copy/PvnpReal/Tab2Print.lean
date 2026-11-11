/-
  PvnpReal.Tab2Print — the CNF encoding of the second tableau is printable in polynomial time,
  built only from the proven combinators (constant lists, polytime ranges, unary arithmetic).
-/
import PvnpReal.Tab2Comp
import PvnpReal.Stream

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

section CFP

variable {D : Type*} [DecidableEq D] (U : List D)

/-- A constraint family (depending on the input) whose one-hot clauses are printable. -/
def CFP (cs : List Bool → List (Constraint D)) : Prop :=
  PS (fun x => clStream ((cs x).flatMap (conClauses U)))

variable {U}

theorem CFP.congr {f g : List Bool → List (Constraint D)} (hf : CFP U f) (h : ∀ x, f x = g x) :
    CFP U g := PS.congr hf (fun x => by rw [h x])

theorem CFP.nil : CFP U (fun _ => []) := PS.const []

theorem CFP.const (cs : List (Constraint D)) : CFP U (fun _ => cs) := PS.const _

theorem CFP.append {f g : List Bool → List (Constraint D)} (hf : CFP U f) (hg : CFP U g) :
    CFP U (fun x => f x ++ g x) :=
  (PS.append hf hg).congr (fun x => by simp [List.flatMap_append, clStream_append])

theorem CFP.single (fs : List (List Bool → ℕ)) (hfs : ∀ f ∈ fs, PU f) (rel : List D → Bool) :
    CFP U (fun x => [⟨fs.map (fun f => f x), rel⟩]) :=
  (PS.conCl U fs hfs rel).congr (fun x => by simp)

theorem CFP.flatMap_const {α : Type*} (L : List α) (g : α → List Bool → List (Constraint D))
    (h : ∀ a ∈ L, CFP U (g a)) : CFP U (fun x => L.flatMap (fun a => g a x)) :=
  (PS.flatMap_const L (fun a x => clStream ((g a x).flatMap (conClauses U))) h).congr
    (fun x => by simp [List.flatMap_assoc, clStream_flatMap])

theorem CFP.map_const {α : Type*} (L : List α) (g : α → List Bool → Constraint D)
    (h : ∀ a ∈ L, CFP U (fun x => [g a x])) : CFP U (fun x => L.map (fun a => g a x)) :=
  (CFP.flatMap_const L (fun a x => [g a x]) h).congr (fun x => by rw [List.map_eq_flatMap])

theorem CFP.flatRange {n : List Bool → ℕ} (hn : PU n) (g : ℕ → List Bool → List (Constraint D))
    (h : CFP U (fun z => g (lpN z) (lpX z))) :
    CFP U (fun x => (List.range (n x)).flatMap (fun i => g i x)) :=
  (PS.flatRange hn (fun i x => clStream ((g i x).flatMap (conClauses U))) h).congr
    (fun x => by simp [List.flatMap_assoc, clStream_flatMap])

theorem CFP.mapRange {n : List Bool → ℕ} (hn : PU n) (g : ℕ → List Bool → Constraint D)
    (h : CFP U (fun z => [g (lpN z) (lpX z)])) :
    CFP U (fun x => (List.range (n x)).map (fun i => g i x)) :=
  (CFP.flatRange hn (fun i x => [g i x]) h).congr (fun x => by rw [List.map_eq_flatMap])

end CFP

/-! ### Unary index arithmetic -/

theorem PU.lenX : PU (fun x => x.length) :=
  (PU.poly Polynomial.X).congr (fun x => by simp)

theorem PS.drop2 : PS (fun z => lpX (lpX z)) := PS.drop.comp PS.drop

theorem PU.fst2 : PU (fun z => lpN (lpX z)) := PU.fst.comp PS.drop

section Idx

variable {K : Type} [DecidableEq K] (Ks : List K)

theorem PU.sv2 {s t : List Bool → ℕ} (hs : PU s) (ht : PU t) :
    PU (fun z => sv2 Ks (s z) (t z)) :=
  ((PU.const 2).add (ht.mul ((PU.const 1).add ((PU.const Ks.length).mul hs)))).congr
    (fun z => rfl)

theorem PU.cv2 {s t p : List Bool → ℕ} (hs : PU s) (ht : PU t) (k : K) (hp : PU p) :
    PU (fun z => cv2 Ks (s z) (t z) k (p z)) :=
  (((((PU.const 2).add (ht.mul ((PU.const 1).add ((PU.const Ks.length).mul hs)))).add
    (PU.const 1)).add ((PU.const (Ks.idxOf k)).mul hs)).add hp).congr
    (fun z => rfl)

end Idx

/-! ### Printing the whole second tableau -/

section Print

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [DecidableEq (V2 Γ Λ σ)]
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (gacc : Γ k₁) (U : List (V2 Γ Λ σ))

theorem tab2_print {Sf Tf Qf : List Bool → ℕ} (hS : PU Sf) (hT : PU Tf) (hQ : PU Qf)
    (hR1 : PU (fun x => Sf x - (x.length + 1 + Qf x)))
    (hR2 : PU (fun x => Sf x - (d + P) - (d + 1)))
    (hR3 : PU (fun x => Sf x - (d + 1))) :
    CFP U (fun x => tab2CS m d P Ks (Sf x) (Tf x) k₀ k₁ main v₀ sb sep (Qf x) gacc x) := by
  have hS1 : PU (fun z => Sf (lpX z)) := hS.comp PS.drop
  have hS2 : PU (fun z => Sf (lpX (lpX z))) := hS.comp PS.drop2
  -- csZ
  have pZ : CFP U (fun _ => csZ k₀ sb) := CFP.const _
  -- csInit
  have pI1 : CFP U (fun x => [(⟨[sv2 Ks (Sf x) 0], ctlRel1 (fun R => R.l = some main ∧ R.var = v₀)⟩ :
      Constraint (V2 Γ Λ σ))]) :=
    (CFP.single [fun x => sv2 Ks (Sf x) 0] (by
      simp only [List.mem_singleton]; rintro f rfl; exact PU.sv2 Ks hS (PU.const 0)) _).congr
      (fun x => rfl)
  have pI2 : CFP U (fun x => (List.range x.length).map (fun i =>
      (⟨[cv2 Ks (Sf x) 0 k₀ i, NthTM.bit x i], cellRel2 (· = ·)⟩ : Constraint (V2 Γ Λ σ)))) := by
    refine CFP.mapRange PU.lenX (fun i x => ⟨[cv2 Ks (Sf x) 0 k₀ i, NthTM.bit x i], cellRel2 (· = ·)⟩) ?_
    refine (CFP.single [fun z => cv2 Ks (Sf (lpX z)) 0 k₀ (lpN z), fun z => NthTM.bit (lpX z) (lpN z)]
      ?_ _).congr (fun x => rfl)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro f (rfl | rfl)
    · exact PU.cv2 Ks hS1 (PU.const 0) k₀ PU.fst
    · exact PU.nth
  have pI3 : CFP U (fun x => [(⟨[cv2 Ks (Sf x) 0 k₀ x.length], cellRel1 (· = some ⟨k₀, sep⟩)⟩ :
      Constraint (V2 Γ Λ σ))]) :=
    (CFP.single [fun x => cv2 Ks (Sf x) 0 k₀ x.length] (by
      simp only [List.mem_singleton]; rintro f rfl; exact PU.cv2 Ks hS (PU.const 0) k₀ PU.lenX) _).congr
      (fun x => rfl)
  have pI4 : CFP U (fun x => (List.range (Qf x)).map (fun j =>
      (⟨[cv2 Ks (Sf x) 0 k₀ (x.length + 1 + j), cv2 Ks (Sf x) 0 k₀ (x.length + 2 + j)],
        cellRel2 (witP sb)⟩ : Constraint (V2 Γ Λ σ)))) := by
    refine CFP.mapRange hQ (fun j x => ⟨[cv2 Ks (Sf x) 0 k₀ (x.length + 1 + j),
      cv2 Ks (Sf x) 0 k₀ (x.length + 2 + j)], cellRel2 (witP sb)⟩) ?_
    refine (CFP.single [fun z => cv2 Ks (Sf (lpX z)) 0 k₀ ((lpX z).length + 1 + lpN z),
      fun z => cv2 Ks (Sf (lpX z)) 0 k₀ ((lpX z).length + 2 + lpN z)] ?_ _).congr (fun x => rfl)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro f (rfl | rfl)
    · exact PU.cv2 Ks hS1 (PU.const 0) k₀ (((PU.lenX.comp PS.drop).add (PU.const 1)).add PU.fst)
    · exact PU.cv2 Ks hS1 (PU.const 0) k₀ (((PU.lenX.comp PS.drop).add (PU.const 2)).add PU.fst)
  have pI5 : CFP U (fun x => (List.range (Sf x - (x.length + 1 + Qf x))).map (fun j =>
      (⟨[cv2 Ks (Sf x) 0 k₀ (x.length + 1 + Qf x + j)], cellRel1 (· = none)⟩ :
        Constraint (V2 Γ Λ σ)))) := by
    refine CFP.mapRange hR1 (fun j x => ⟨[cv2 Ks (Sf x) 0 k₀ (x.length + 1 + Qf x + j)],
      cellRel1 (· = none)⟩) ?_
    refine (CFP.single [fun z => cv2 Ks (Sf (lpX z)) 0 k₀ ((lpX z).length + 1 + Qf (lpX z) + lpN z)]
      ?_ _).congr (fun x => rfl)
    simp only [List.mem_singleton]; rintro f rfl
    exact PU.cv2 Ks hS1 (PU.const 0) k₀
      ((((PU.lenX.comp PS.drop).add (PU.const 1)).add (hQ.comp PS.drop)).add PU.fst)
  have pI6 : CFP U (fun x => (Ks.filter (· ≠ k₀)).flatMap (fun k => (List.range (Sf x)).map (fun p =>
      (⟨[cv2 Ks (Sf x) 0 k p], cellRel1 (· = none)⟩ : Constraint (V2 Γ Λ σ))))) := by
    refine CFP.flatMap_const _ (fun k x => (List.range (Sf x)).map (fun p =>
      (⟨[cv2 Ks (Sf x) 0 k p], cellRel1 (· = none)⟩ : Constraint (V2 Γ Λ σ)))) (fun k _ => ?_)
    refine CFP.mapRange hS (fun p x => ⟨[cv2 Ks (Sf x) 0 k p], cellRel1 (· = none)⟩) ?_
    refine (CFP.single [fun z => cv2 Ks (Sf (lpX z)) 0 k (lpN z)] ?_ _).congr (fun x => rfl)
    simp only [List.mem_singleton]; rintro f rfl
    exact PU.cv2 Ks hS1 (PU.const 0) k PU.fst
  have pI : CFP U (fun x => csInit Ks (Sf x) k₀ main v₀ sb sep (Qf x) x) :=
    (((((pI1.append pI2).append pI3).append pI4).append pI5).append pI6).congr (fun x => rfl)
  -- rows
  have pR : CFP U (fun x => (List.range (Tf x + 1)).flatMap (csRow d Ks (Sf x))) := by
    refine CFP.flatRange (hT.add (PU.const 1)) (fun t x => csRow d Ks (Sf x) t) ?_
    refine CFP.flatMap_const Ks (fun k z =>
      (List.range d).map (fun i => (⟨[sv2 Ks (Sf (lpX z)) (lpN z), cv2 Ks (Sf (lpX z)) (lpN z) k i],
        linkRel k i⟩ : Constraint (V2 Γ Λ σ))) ++
      (List.range (d + 1)).map (fun j => (⟨[cv2 Ks (Sf (lpX z)) (lpN z) k (Sf (lpX z) - (d + 1) + j)],
        cellRel1 (· = none)⟩ : Constraint (V2 Γ Λ σ)))) (fun k _ => ?_)
    refine CFP.append (CFP.map_const _ _ (fun i _ => ?_)) (CFP.map_const _ _ (fun j _ => ?_))
    · refine (CFP.single [fun z => sv2 Ks (Sf (lpX z)) (lpN z),
        fun z => cv2 Ks (Sf (lpX z)) (lpN z) k i] ?_ _).congr (fun x => rfl)
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      rintro f (rfl | rfl)
      · exact PU.sv2 Ks hS1 PU.fst
      · exact PU.cv2 Ks hS1 PU.fst k (PU.const i)
    · refine (CFP.single [fun z => cv2 Ks (Sf (lpX z)) (lpN z) k (Sf (lpX z) - (d + 1) + j)] ?_ _).congr
        (fun x => rfl)
      simp only [List.mem_singleton]; rintro f rfl
      exact PU.cv2 Ks hS1 PU.fst k ((hR3.comp PS.drop).add (PU.const j))
  -- transitions
  have pT : CFP U (fun x => (List.range (Tf x)).flatMap (csTrans m d P Ks (Sf x))) := by
    refine CFP.flatRange hT (fun t x => csTrans m d P Ks (Sf x) t) ?_
    have p1 : CFP U (fun z => [(⟨[sv2 Ks (Sf (lpX z)) (lpN z), sv2 Ks (Sf (lpX z)) (lpN z + 1)],
        ctlRel2 (transCP m)⟩ : Constraint (V2 Γ Λ σ))]) := by
      refine (CFP.single [fun z => sv2 Ks (Sf (lpX z)) (lpN z),
        fun z => sv2 Ks (Sf (lpX z)) (lpN z + 1)] ?_ _).congr (fun x => rfl)
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      rintro f (rfl | rfl)
      · exact PU.sv2 Ks hS1 PU.fst
      · exact PU.sv2 Ks hS1 (PU.fst.add (PU.const 1))
    have p2 : CFP U (fun z => Ks.flatMap (fun k =>
        (List.range (d + P)).map (fun p =>
          (⟨sv2 Ks (Sf (lpX z)) (lpN z) :: cv2 Ks (Sf (lpX z)) (lpN z + 1) k p ::
            (List.range (p + d + 1)).map (fun i => cv2 Ks (Sf (lpX z)) (lpN z) k i),
            tcRel m d k p p⟩ : Constraint (V2 Γ Λ σ))) ++
        (List.range (Sf (lpX z) - (d + P) - (d + 1))).map (fun j =>
          (⟨sv2 Ks (Sf (lpX z)) (lpN z) :: cv2 Ks (Sf (lpX z)) (lpN z + 1) k (d + P + j) ::
            (List.range (P + d + 1)).map (fun i => cv2 Ks (Sf (lpX z)) (lpN z) k (d + j + i)),
            tcRel m d k P (d + P)⟩ : Constraint (V2 Γ Λ σ))))) := by
      refine CFP.flatMap_const Ks _ (fun k _ => CFP.append (CFP.map_const _ _ (fun p _ => ?_)) ?_)
      · refine (CFP.single ((fun z => sv2 Ks (Sf (lpX z)) (lpN z)) ::
          (fun z => cv2 Ks (Sf (lpX z)) (lpN z + 1) k p) ::
          (List.range (p + d + 1)).map (fun i z => cv2 Ks (Sf (lpX z)) (lpN z) k i)) ?_
          (tcRel m d k p p)).congr
          (fun x => by simp [List.map_map, Function.comp_def])
        simp only [List.mem_cons, List.mem_map]
        rintro f (rfl | rfl | ⟨i, -, rfl⟩)
        · exact PU.sv2 Ks hS1 PU.fst
        · exact PU.cv2 Ks hS1 (PU.fst.add (PU.const 1)) k (PU.const p)
        · exact PU.cv2 Ks hS1 PU.fst k (PU.const i)
      · refine CFP.mapRange (hR2.comp PS.drop) (fun j z =>
          (⟨sv2 Ks (Sf (lpX z)) (lpN z) :: cv2 Ks (Sf (lpX z)) (lpN z + 1) k (d + P + j) ::
            (List.range (P + d + 1)).map (fun i => cv2 Ks (Sf (lpX z)) (lpN z) k (d + j + i)),
            tcRel m d k P (d + P)⟩ : Constraint (V2 Γ Λ σ))) ?_
        refine (CFP.single ((fun z => sv2 Ks (Sf (lpX (lpX z))) (lpN (lpX z))) ::
          (fun z => cv2 Ks (Sf (lpX (lpX z))) (lpN (lpX z) + 1) k (d + P + lpN z)) ::
          (List.range (P + d + 1)).map (fun i z =>
            cv2 Ks (Sf (lpX (lpX z))) (lpN (lpX z)) k (d + lpN z + i))) ?_
          (tcRel m d k P (d + P))).congr
          (fun x => by simp [List.map_map, Function.comp_def])
        simp only [List.mem_cons, List.mem_map]
        rintro f (rfl | rfl | ⟨i, -, rfl⟩)
        · exact PU.sv2 Ks hS2 PU.fst2
        · exact PU.cv2 Ks hS2 (PU.fst2.add (PU.const 1)) k ((PU.const (d + P)).add PU.fst)
        · exact PU.cv2 Ks hS2 PU.fst2 k (((PU.const d).add PU.fst).add (PU.const i))
    exact (p1.append p2).congr (fun x => rfl)
  -- final
  have pF : CFP U (fun x => csFinal Ks (Sf x) (Tf x) k₁ gacc) :=
    (CFP.single [fun x => cv2 Ks (Sf x) (Tf x) k₁ 0] (by
      simp only [List.mem_singleton]; rintro f rfl; exact PU.cv2 Ks hS hT k₁ (PU.const 0)) _).congr
      (fun x => rfl)
  exact ((((pZ.append pI).append pR).append pT).append pF).congr (fun x => rfl)

/-- **The printed CNF** `x ↦ encodeCNF (cspCNF U (N x) (tab2CS …))` is polynomial-time
computable. -/
theorem tab2_encode_PS {Sf Tf Qf Nf : List Bool → ℕ} (hS : PU Sf) (hT : PU Tf) (hQ : PU Qf)
    (hN : PU Nf)
    (hR1 : PU (fun x => Sf x - (x.length + 1 + Qf x)))
    (hR2 : PU (fun x => Sf x - (d + P) - (d + 1)))
    (hR3 : PU (fun x => Sf x - (d + 1))) :
    PS (fun x => encodeCNF (cspCNF U (Nf x)
      (tab2CS m d P Ks (Sf x) (Tf x) k₀ k₁ main v₀ sb sep (Qf x) gacc x))) := by
  have hA : PS (fun x => clStream ((List.range (Nf x)).map (aloClause U))) := by
    refine (PS.flatRange hN (fun v _ => true :: encList encLit (aloClause U v)) ?_).congr
      (fun x => by rw [clStream_map])
    refine (PS.cons true (PS.encLits U (fun a z => lpN z * U.length + U.idxOf a) (fun _ => false)
      (fun a _ => (PU.fst.mul (PU.const _)).add (PU.const _)))).congr (fun z => rfl)
  have hB := tab2_print m d P Ks k₀ k₁ main v₀ sb sep gacc U hS hT hQ hR1 hR2 hR3
  refine ((hA.append hB).append (PS.const [false])).congr (fun x => ?_)
  rw [encodeCNF_eq, cspCNF, clStream_append]

end Print

end PvnpReal
