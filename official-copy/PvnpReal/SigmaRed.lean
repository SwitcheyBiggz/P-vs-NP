/-
  PvnpReal.SigmaRed — **Σ_k-SAT is Σ_k-complete** (k ≥ 1), and the collapse corollary.

  Reduction for `L ∈ Σ_{j+1}` (`x ∈ L ↔ ∃u₁ ∀u₂ … Q u_{j+1}. R(x, u₁⋯u_{j+1})`):
  the `j` outer blocks are kept as quantifier blocks, the innermost block is absorbed into the
  Cook–Levin tableau of the verifier "`R(x,u)` and `|u|` = total length" (for `j` even, innermost `∃`)
  or of "`¬R(x,u)` and …" (for `j` odd, innermost `∀`; the matrix is then the DNF `negCNF Φ`, i.e.
  `¬Φ`).  The outer witness bits are tied to the tableau's witness cells by the link clauses of
  `SigmaHard.lean`; the innermost block of the Σ_k-SAT instance is all tableau variables.
-/
import PvnpReal.SigmaHard
import PvnpReal.SigmaSat
import PvnpReal.QbfPrint

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

/-! ### Quantifier-block bookkeeping -/

/-- Block lengths of `altQ … j`, outermost first. -/
def blkL (qs : ℕ → Polynomial ℕ) (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 => (qs j).eval n :: blkL qs n j

theorem blkL_length (qs : ℕ → Polynomial ℕ) (n : ℕ) : ∀ j, (blkL qs n j).length = j
  | 0 => rfl
  | j + 1 => by simp [blkL, blkL_length qs n j]

theorem blkL_sum (qs : ℕ → Polynomial ℕ) (n : ℕ) :
    ∀ j, (blkL qs n j).sum = (∑ i ∈ Finset.range j, qs i).eval n
  | 0 => by simp [blkL]
  | j + 1 => by
    rw [blkL, List.sum_cons, blkL_sum qs n j, Finset.sum_range_succ, Polynomial.eval_add]; ring

theorem altQ_sval (R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) :
    ∀ j b u, altQ R qs x j b u ↔ sval (fun s => decide (R (codeP x s))) (blkL qs x.length j) b u := by
  intro j
  induction j with
  | zero => intro b u; simp [sval, blkL]
  | succ j ih => intro b u; cases b <;> simp [sval, blkL, ih]

theorem sval_append_last (leaf : List Bool → Bool) (M : ℕ) :
    ∀ (pre : List ℕ) b u, sval leaf (pre ++ [M]) b u ↔
      sval (fun p => decide (sval leaf [M] (innerT pre.length b) p)) pre b u := by
  intro pre
  induction pre with
  | nil => intro b u; simp [sval, innerT]
  | cons n pre ih => intro b u; cases b <;> simp [sval, ih, innerT]

theorem sval_congr_len {f g : List Bool → Bool} :
    ∀ (ns : List ℕ) b (u : List Bool),
      (∀ p : List Bool, p.length = u.length + ns.sum → (f p = true ↔ g p = true)) →
      (sval f ns b u ↔ sval g ns b u) := by
  intro ns
  induction ns with
  | nil => intro b u h; simpa [sval] using h u (by simp)
  | cons n ns ih =>
    intro b u h
    have h' : ∀ w : List Bool, w.length = n → (sval f ns (!b) (u ++ w) ↔ sval g ns (!b) (u ++ w)) :=
      fun w hw => ih _ _ (fun p hp => h p (by simp [List.sum_cons] at hp ⊢; omega))
    cases b
    · simp only [sval]
      exact forall_congr' fun w => imp_congr_right fun hw => h' w hw
    · simp only [sval]
      exact exists_congr fun w => and_congr_right fun hw => h' w hw

theorem innerT_true : ∀ j, innerT j true = decide (j % 2 = 0)
  | 0 => rfl
  | 1 => rfl
  | j + 2 => by
    rw [show innerT (j + 2) true = innerT j true from rfl, innerT_true j]
    congr 1; simp [Nat.add_mod]

theorem negCNF_negCNF (φ : CNF) : negCNF (negCNF φ) = φ := by
  simp [negCNF, List.map_map, Function.comp_def]

theorem evalDNF_negCNF (φ : CNF) (a : ℕ → Bool) : evalDNF (negCNF φ) a = !evalCNF φ a := by
  have := evalCNF_neg (negCNF φ) a
  rw [negCNF_negCNF] at this
  rw [this, Bool.not_not]

theorem rot_append (p z : List Bool) : rot p.length (p ++ z) = z ++ p := by
  simp [rot]

theorem SigmaSAT_encode' (k : ℕ) (ns : List ℕ) (hk : ns.length = k) (φ : CNF) :
    SigmaSAT k (encSigma ns φ) ↔
      sval (fun p => matVal k φ (asg (rot (ns.take (k - 1)).sum p))) ns true [] := by
  subst hk; exact SigmaSAT_encode ns φ

theorem encNs_append (l l' : List ℕ) : encNs (l ++ l') = encNs l ++ encNs l' := by
  simp [encNs]

theorem PS.encBlk (qs : ℕ → Polynomial ℕ) : ∀ j, PS (fun x => encNs (blkL qs x.length j))
  | 0 => PS.const []
  | j + 1 => ((PU.poly (qs j)).append (PS.cons false (PS.encBlk qs j))).congr
      (fun x => by simp [blkL, encNs_cons])

/-! ### Printing the tableau-with-links formula -/

section Print

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {V : List Bool × List Bool → Bool} (q : Polynomial ℕ)
  (h : TM2ComputableInPolyTime pairEnc encodeBool V)

theorem PU.c2N : PU (fun x => c2N q h x) :=
  ((PU.const 2).add (((PU.clT q h).add (PU.const 1)).mul
    ((PU.const 1).add ((PU.const _).mul (PU.c2S q h))))).congr (fun _ => rfl)

theorem PU.cM : PU (fun x => cM q h x) := ((PU.c2N q h).mul (PU.const _)).congr (fun _ => rfl)

theorem PS.linkIP : PS (fun z => clStream (linkI q h (lpX z) (lpN z))) := by
  have hC : PU (fun z => cCell q h (lpX z) (lpN z)) :=
    PU.cv2 (clKs h.tm) ((PU.c2S q h).comp PS.drop) (PU.const 0) h.tm.k₀
      (((PU.lenX.comp PS.drop).add (PU.const 1)).add PU.fst)
  have hH : ∀ e, PU (fun z => hotVar (cU h) (cCell q h (lpX z) (lpN z)) e) := fun e =>
    ((hC.mul (PU.const _)).add (PU.const _)).congr (fun _ => rfl)
  have hMi : PU (fun z => cM q h (lpX z) + lpN z) := ((PU.cM q h).comp PS.drop).add PU.fst
  have c1 := PS.clause [((fun z => cM q h (lpX z) + lpN z), true),
    ((fun z => hotVar (cU h) (cCell q h (lpX z) (lpN z)) (cSb h true)), false)]
    (by simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        rintro a (rfl | rfl); exact hMi; exact hH _)
  have c2 := PS.clause [((fun z => cM q h (lpX z) + lpN z), false),
    ((fun z => hotVar (cU h) (cCell q h (lpX z) (lpN z)) (cSb h true)), true)]
    (by simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        rintro a (rfl | rfl); exact hMi; exact hH _)
  have c3 := PS.clause [((fun z => hotVar (cU h) (cCell q h (lpX z) (lpN z)) (cSb h true)), true),
    ((fun z => hotVar (cU h) (cCell q h (lpX z) (lpN z)) (cSb h false)), true)]
    (by simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        rintro a (rfl | rfl); exact hH _; exact hH _)
  have c4 := PS.flatMap_const (cBad h) (fun e z => clStream [[(⟨hotVar (cU h)
      (cCell q h (lpX z) (lpN z)) e, true⟩ : Literal)]]) (fun e _ =>
    (PS.clause [((fun z => hotVar (cU h) (cCell q h (lpX z) (lpN z)) e), true)]
      (by simp only [List.mem_singleton]; rintro a rfl; exact hH _)).congr (fun z => rfl))
  refine (((c1.append c2).append c3).append c4).congr (fun z => ?_)
  simp [linkI, clStream, List.flatMap_map]

theorem PS.coreEnc {n : List Bool → ℕ} (hn : PU n) :
    PS (fun x => encodeCNF (coreCNF q h x (n x))) := by
  have hL : PS (fun x => clStream (linkCNF q h x (n x))) :=
    (PS.flatRange hn (fun i x => clStream (linkI q h x i)) (PS.linkIP q h)).congr
      (fun x => by rw [linkCNF, clStream_flatMap])
  refine (hL.append (cl2Map_PS q h)).congr (fun x => ?_)
  rw [coreCNF, cl2Map, encodeCNF_eq, encodeCNF_eq, clStream_append, List.append_assoc]

end Print

/-! ### Hardness -/

/-- The verifier language: `R` (or `¬R`) together with the exact total witness length. -/
def gVer (pos : Bool) (R : Language) (Q : Polynomial ℕ) : Language := fun s =>
  (if pos then R s else ¬ R s) ∧ (decP s).2.length = Q.eval (decP s).1.length

theorem InP.gVerP (pos : Bool) {R : Language} (hR : InP R) (Q : Polynomial ℕ) : InP (gVer pos R Q) := by
  have hl : InP (fun s => (decP s).2.length = Q.eval (decP s).1.length) :=
    InP.ofPUeq (PU.lenX.comp PS.sndP) (PU.polyOf Q (PU.lenX.comp PS.fstP))
  cases pos
  · exact (hR.compl.inter hl).congr (fun s => by simp [gVer])
  · exact (hR.inter hl).congr (fun s => by simp [gVer])

/-- **Σ_k-SAT is Σ_k-hard** (k ≥ 1): every Σ_{j+1} language poly-time reduces to `SigmaSAT (j+1)`. -/
theorem SigmaSAT_hard (j : ℕ) (L : Language) (hL : InSigma (j + 1) L) :
    PolyReduces L (SigmaSAT (j + 1)) := by
  obtain ⟨R, qs, hR, hLR⟩ := hL
  set qs' : ℕ → Polynomial ℕ := fun i => qs (i + 1) with hqs'
  set QO : Polynomial ℕ := ∑ i ∈ Finset.range j, qs' i with hQO
  set QT : Polynomial ℕ := qs 0 + QO with hQT
  set pos : Bool := decide (j % 2 = 0) with hpos
  obtain ⟨V, ⟨hV⟩, hVg⟩ := pairDecider (InP.gVerP pos hR QT)
  let f : List Bool → List Bool := fun x =>
    encSigma (blkL qs' x.length j ++ [cM QT hV x])
      (if pos then coreCNF QT hV x (QO.eval x.length) else negCNF (coreCNF QT hV x (QO.eval x.length)))
  refine ⟨f, ?_, fun x => ?_⟩
  · -- polynomial time
    have hΦ := PS.coreEnc QT hV (PU.poly QO)
    have hC : PS (fun x => encodeCNF (if pos then coreCNF QT hV x (QO.eval x.length)
        else negCNF (coreCNF QT hV x (QO.eval x.length)))) := by
      by_cases hp : pos = true
      · exact hΦ.congr (fun x => by simp [hp])
      · exact (PS.comp hΦ PS.flipS).congr (fun x => by simp [hp, flipS_encode])
    have hX : PS (fun x => encNs (blkL qs' x.length j ++ [cM QT hV x])) :=
      ((PS.encBlk qs' j).append ((PU.cM QT hV).append (PS.const [false]))).congr
        (fun x => by simp [encNs_append, encNs])
    exact PS.Rof hX hC
  · -- correctness
    have hprel : (blkL qs' x.length j).length = j := blkL_length _ _ _
    have hpres : (blkL qs' x.length j).sum = QO.eval x.length := by rw [blkL_sum]
    rw [hLR x, altQ_collapse R qs x j true [], altQ_sval, show f x = encSigma
      (blkL qs' x.length j ++ [cM QT hV x]) (if pos then coreCNF QT hV x (QO.eval x.length)
        else negCNF (coreCNF QT hV x (QO.eval x.length))) from rfl,
      SigmaSAT_encode' (j + 1) _ (by simp [hprel]),
      show (j + 1 - 1) = (blkL qs' x.length j).length by omega, List.take_left' rfl,
      sval_append_last, hprel, hpres]
    refine sval_congr_len _ true [] (fun p hp => ?_)
    simp only [List.length_nil, Nat.zero_add] at hp
    replace hp : p.length = QO.eval x.length := hp.trans hpres
    have hpQ : p.length ≤ QT.eval x.length := by
      rw [hQT, Polynomial.eval_add]; omega
    have hcore := core_iff QT hV x p hpQ
    rw [← hp]
    have hVw : ∀ w : List Bool, V (x, p ++ w) = true ↔
        ((if pos then R (codeP x (p ++ w)) else ¬ R (codeP x (p ++ w))) ∧
          w.length = (qs 0).eval x.length) := by
      intro w
      rw [hVg, gVer, decP_codeP]
      simp only [List.length_append, hQT, Polynomial.eval_add]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    by_cases hj : j % 2 = 0
    · have hp' : pos = true := by simp [hpos, hj]
      simp only [Rcol, decP_codeP, decide_eq_true_eq, innerT_true, hj, decide_true, if_true, sval,
        rot_append, hp', matVal, show (j + 1) % 2 = 1 by omega]
      rw [← hcore]
      constructor
      · rintro ⟨w, hw, hR'⟩
        refine ⟨w, ?_, (hVw w).2 ⟨by simpa [hp'] using hR', hw⟩⟩
        simp only [List.length_append, hQT, Polynomial.eval_add, hw]; omega
      · rintro ⟨w, -, hVw'⟩
        obtain ⟨h1, h2⟩ := (hVw w).1 hVw'
        exact ⟨w, h2, by simpa [hp'] using h1⟩
    · have hp' : pos = false := by simp [hpos, hj]
      simp only [Rcol, decP_codeP, decide_eq_true_eq, innerT_true, hj, decide_false,
        Bool.false_eq_true, if_false, sval, rot_append, hp', matVal,
        show ¬ (j + 1) % 2 = 1 by omega, evalDNF_negCNF, Bool.not_eq_true']
      have hneg : ¬ (∃ w : List Bool, (p ++ w).length ≤ QT.eval x.length ∧ V (x, p ++ w) = true) ↔
          ∀ z : List Bool, z.length = cM QT hV x →
            evalCNF (coreCNF QT hV x p.length) (asg (z ++ p)) = false := by
        rw [hcore]; push_neg
        exact forall_congr' fun z => imp_congr_right fun _ => by simp
      rw [← hneg]
      constructor
      · rintro hall ⟨w, -, hVw'⟩
        obtain ⟨h1, h2⟩ := (hVw w).1 hVw'
        simp only [hp', Bool.false_eq_true, if_false] at h1
        exact h1 (hall w h2)
      · intro hno w hw
        by_contra hRw
        refine hno ⟨w, ?_, (hVw w).2 ⟨by simpa [hp'] using hRw, hw⟩⟩
        simp only [List.length_append, hQT, Polynomial.eval_add, hw]; omega

/-- `L` is Σ_k-complete (under polynomial-time many-one reductions). -/
def SigmaComplete (k : ℕ) (L : Language) : Prop :=
  InSigma k L ∧ ∀ L' : Language, InSigma k L' → PolyReduces L' L

/-- **Σ_k-SAT is Σ_k-complete for every `k ≥ 1`.** -/
theorem SigmaSAT_complete (k : ℕ) (hk : 1 ≤ k) : SigmaComplete k (SigmaSAT k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨SigmaSAT_in_Sigma (j + 1), SigmaSAT_hard j⟩

/-- **Corollary: if Σ_k-SAT ∈ Π_k (k ≥ 1) then PH collapses to Σ_k.** -/
theorem PH_collapse_of_SigmaSAT_in_Pi (k : ℕ) (hk : 1 ≤ k) (h : InPi k (SigmaSAT k)) (L : Language) :
    InPH L ↔ InSigma k L :=
  PH_eq_Sigma_of_Sigma_subset_Pi k hk
    (fun L' hL' => InPi.of_reduces ((SigmaSAT_complete k hk).2 L' hL') h) L

/-- Σ_k-SAT ∈ Π_k exactly when Σ_k = Π_k (k ≥ 1). -/
theorem SigmaSAT_in_Pi_iff (k : ℕ) (hk : 1 ≤ k) : InPi k (SigmaSAT k) ↔ Sigma_eq_Pi k :=
  ⟨fun h => Sigma_eq_Pi_of_subset k
      (fun L' hL' => InPi.of_reduces ((SigmaSAT_complete k hk).2 L' hL') h),
    fun H => (H _).1 (SigmaSAT_in_Sigma k)⟩

end PvnpReal
