/-
  PvnpReal.RPClasses — RP, coRP, ZPP (counting style), reductions, and corollaries.
-/
import PvnpReal.RP

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

/-! ### Generic counting facts -/

theorem accCount_mono {V V' : Language} {x : List Bool} {m : ℕ}
    (h : ∀ w : Fin m → Bool, V (codeP x (List.ofFn w)) → V' (codeP x (List.ofFn w))) :
    accCount V x m ≤ accCount V' x m := by
  unfold accCount
  exact Finset.card_le_card (fun w hw => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢; exact h w hw)

theorem accCount_eq_zero {V : Language} {x : List Bool} {m : ℕ} :
    accCount V x m = 0 ↔ ∀ w : Fin m → Bool, ¬ V (codeP x (List.ofFn w)) := by
  unfold accCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

theorem take_ofFn_add {m d : ℕ} (w : Fin (m + d) → Bool) :
    (List.ofFn w).take m = List.ofFn (fun i : Fin m => w (Fin.castAdd d i)) := by
  rw [List.ofFn_add, List.take_left' (by simp)]; rfl

theorem drop_ofFn_add {m d : ℕ} (w : Fin (m + d) → Bool) :
    (List.ofFn w).drop m = List.ofFn (fun j : Fin d => w (Fin.natAdd m j)) := by
  rw [List.ofFn_add, List.drop_left' (by simp)]

/-! ### BPP is closed under polynomial-time reductions -/

/-- **BPP is closed under polynomial-time many-one reductions.** -/
theorem InBPP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InBPP L') : InBPP L := by
  obtain ⟨f, hf, hfL⟩ := hr
  have hfP : PS f := hf
  obtain ⟨Pf, hPf⟩ := PS.outPoly hfP
  obtain ⟨V', q', hV', hq'⟩ := h.wrong (Polynomial.C 2)
  set V : Language := fun s => V' (codeP (f (decP s).1) ((decP s).2.take (q'.eval (f (decP s).1).length)))
  have hV : InP V := hV'.compPS (PS.codePF (PS.comp PS.fstP hfP)
    (PS.takeU PS.sndP ((PU.poly q').comp (PS.comp PS.fstP hfP))))
  refine InBPP_of_wrong (q := q'.comp Pf) hV (fun x => ?_)
  set m := q'.eval (f x).length
  have hm : m ≤ q'.eval (Pf.eval x.length) := poly_eval_mono q' (hPf x)
  have e1 := hq' (f x)
  simp only [Polynomial.eval_C] at e1
  have key : ∀ M d, M = m + d → 3 * wrongCount V L x M ≤ 2 ^ M := by
    intro M d hM
    subst hM
    unfold wrongCount at e1 ⊢
    have ct : (Finset.univ.filter (fun W : Fin (m + d) → Bool =>
        (V (codeP x (List.ofFn W)) ↔ ¬ L x))).card =
        (Finset.univ.filter (fun W : Fin m → Bool =>
          (V' (codeP (f x) (List.ofFn W)) ↔ ¬ L' (f x)))).card * 2 ^ d := by
      calc _ = (Finset.univ.filter (fun W : Fin (m + d) → Bool =>
              (V' (codeP (f x) ((List.ofFn W).take m)) ↔ ¬ L' (f x)))).card := by
            congr 1; ext W; simp [V, decP_codeP, hfL x, m]
        _ = _ := by convert count_take (m := m) (d := d) (fun l => V' (codeP (f x) l) ↔ ¬ L' (f x))
    rw [ct, pow_add]
    have := Nat.mul_le_mul_right (2 ^ d) e1.le
    nlinarith
  have := key (q'.eval (Pf.eval x.length)) (q'.eval (Pf.eval x.length) - m) (by omega)
  rwa [Polynomial.eval_comp]

/-! ### RP, coRP, ZPP -/

/-- **RP**: one-sided error — yes-instances accepted by at least half the random strings,
no-instances by none. -/
def InRP (L : Language) : Prop :=
  ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
    (L x → 2 ^ q.eval x.length ≤ 2 * accCount V x (q.eval x.length)) ∧
    (¬ L x → accCount V x (q.eval x.length) = 0)

/-- **coRP**. -/
def InCoRP (L : Language) : Prop := InRP (fun x => ¬ L x)

/-- **ZPP := RP ∩ coRP**. -/
def InZPP (L : Language) : Prop := InRP L ∧ InCoRP L

/-- **Zero-error "answer or ?" form**: polytime `Y` ("yes") and `N` ("no") never lie, and at least
half the random strings give an answer. -/
def InZPPq (L : Language) : Prop :=
  ∃ (Y N : Language) (q : Polynomial ℕ), InP Y ∧ InP N ∧ ∀ x : List Bool,
    (∀ w : Fin (q.eval x.length) → Bool,
      (Y (codeP x (List.ofFn w)) → L x) ∧ (N (codeP x (List.ofFn w)) → ¬ L x)) ∧
    2 ^ q.eval x.length ≤ 2 * accCount (fun s => Y s ∨ N s) x (q.eval x.length)

theorem P_subset_RP {L : Language} (h : InP L) : InRP L := by
  refine ⟨fun s => L (decP s).1, 0, h.compPS PS.fstP, fun x => ?_⟩
  simp only [Polynomial.eval_zero, pow_zero, accCount, decP_codeP]
  by_cases hx : L x
  · simp [hx]
  · simp [hx]

theorem P_subset_ZPP {L : Language} (h : InP L) : InZPP L := ⟨P_subset_RP h, P_subset_RP h.compl⟩

theorem ZPP_subset_RP {L : Language} (h : InZPP L) : InRP L := h.1
theorem ZPP_subset_coRP {L : Language} (h : InZPP L) : InCoRP L := h.2

/-- **RP ⊆ NP.** -/
theorem RP_subset_NP {L : Language} (h : InRP L) : InNP L := by
  obtain ⟨V, q, hV, hq⟩ := h
  refine (Sigma1_iff_NP L).1 ⟨V, fun _ => q, hV, fun x => ?_⟩
  show L x ↔ ∃ w : List Bool, w.length = q.eval x.length ∧ V (codeP x ([] ++ w))
  simp only [List.nil_append]
  rw [exists_list_iff]
  constructor
  · intro hL
    have h1 := (hq x).1 hL
    by_contra hc
    simp only [not_exists] at hc
    have := (accCount_eq_zero (V := V) (x := x)).2 hc
    have : 0 < 2 ^ q.eval x.length := by positivity
    omega
  · rintro ⟨w, hw⟩
    by_contra hL
    exact (accCount_eq_zero.1 ((hq x).2 hL)) w hw

/-- One-sided verifier with `t` independent runs: accept iff some block accepts. -/
noncomputable def orV (V : Language) (q p : Polynomial ℕ) : Language := fun s =>
  1 ≤ ((List.range (p.eval (decP s).1.length)).flatMap (fun i =>
    if V (codeP (decP s).1 (subL (decP s).2 (i * q.eval (decP s).1.length) (q.eval (decP s).1.length)))
    then [true] else [])).length

theorem InP.orVP {V : Language} (hV : InP V) (q p : Polynomial ℕ) : InP (orV V q p) := by
  have X' : PS (fun z => (decP (lpX z)).1) := PS.comp PS.drop PS.fstP
  have Q' : PU (fun z => q.eval (decP (lpX z)).1.length) := (PU.poly q).comp X'
  have sub : PS (fun z => subL (decP (lpX z)).2 (lpN z * q.eval (decP (lpX z)).1.length)
      (q.eval (decP (lpX z)).1.length)) :=
    PS.subL (PS.comp PS.drop PS.sndP) (PU.mul PU.fst Q') Q'
  have hb0 := PS.ofInP (hV.compPS (PS.codePF X' sub))
  have hb : PS (fun z => (fun i s => if V (codeP (decP s).1 (subL (decP s).2 (i * q.eval (decP s).1.length)
      (q.eval (decP s).1.length))) then [true] else []) (lpN z) (lpX z)) :=
    (PS.iteEq ((PU.bitAt 0).comp hb0) (PU.const 1) (PS.const [true]) (PS.const [])).congr
      (fun z => by
        by_cases hz : V (codeP (decP (lpX z)).1 (subL (decP (lpX z)).2
          (lpN z * q.eval (decP (lpX z)).1.length) (q.eval (decP (lpX z)).1.length)))
        · simp [hz, NthTM.bit]
        · simp [hz, NthTM.bit])
  have hN : PU (fun s => p.eval (decP s).1.length) := (PU.poly p).comp PS.fstP
  have hF := PS.flatRange hN (fun i s => if V (codeP (decP s).1 (subL (decP s).2
      (i * q.eval (decP s).1.length) (q.eval (decP s).1.length))) then [true] else []) hb
  exact (InP.ofPUle (PU.const 1) (PU.lenX.comp hF)).congr (fun s => Iff.rfl)

theorem orV_code (V : Language) (q p : Polynomial ℕ) (x : List Bool)
    (W : Fin (p.eval x.length * q.eval x.length) → Bool) :
    orV V q p (codeP x (List.ofFn W)) ↔ ∃ i : Fin (p.eval x.length), V (codeP x (List.ofFn (blk W i))) := by
  simp only [orV, decP_codeP]
  rw [flatMap_count, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies, not_forall, not_not]
  constructor
  · rintro ⟨i, hi⟩; rw [subL_ofFn_blk W i] at hi; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [subL_ofFn_blk W i]; exact hi⟩

/-- **One-sided amplification for RP**: error `≤ 2^{-p(n)}` on yes-instances, still none on
no-instances. -/
theorem InRP.amplify {L : Language} (h : InRP L) (p : Polynomial ℕ) :
    ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
      (L x → 2 ^ p.eval x.length * accCount (fun s => ¬ V s) x (q.eval x.length) ≤ 2 ^ q.eval x.length) ∧
      (¬ L x → accCount V x (q.eval x.length) = 0) := by
  obtain ⟨V, q, hV, hq⟩ := h
  refine ⟨orV V q p, p * q, InP.orVP hV q p, fun x => ?_⟩
  set n := x.length
  set t := p.eval n
  set qn := q.eval n
  have key : ∀ M, M = t * qn →
      (L x → 2 ^ t * accCount (fun s => ¬ orV V q p s) x M ≤ 2 ^ M) ∧
      (¬ L x → accCount (orV V q p) x M = 0) := by
    intro M hM
    subst hM
    constructor
    · intro hL
      have h1 : 2 ^ qn ≤ 2 * accCount V x qn := (hq x).1 hL
      set R := Finset.univ.filter (fun w : Fin qn → Bool => ¬ V (codeP x (List.ofFn w)))
      have hR : R.card = 2 ^ qn - accCount V x qn := by
        rw [← accCount_compl]; unfold accCount; congr 1; ext w; simp [R]
      have hacc := accCount_le V x qn
      have hsub : (Finset.univ.filter (fun W : Fin (t * qn) → Bool =>
          ¬ orV V q p (codeP x (List.ofFn W)))).card ≤
          (Fintype.piFinset (fun _ : Fin t => R)).card := by
        apply Finset.card_le_card_of_injOn (fun W => blk W)
        · intro W hW
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hW
          rw [orV_code] at hW
          simp only [Finset.mem_coe, Fintype.mem_piFinset, R, Finset.mem_filter, Finset.mem_univ,
            true_and]
          intro i hi; exact hW ⟨i, hi⟩
        · intro W _ W' _ e
          funext k
          obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
          exact congrFun (congrFun e i) j
      rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hR] at hsub
      have h2 : 2 * (2 ^ qn - accCount V x qn) ≤ 2 ^ qn := by omega
      have h3 : (2 * (2 ^ qn - accCount V x qn)) ^ t ≤ (2 ^ qn) ^ t := Nat.pow_le_pow_left h2 t
      rw [mul_pow, ← pow_mul] at h3
      have e : accCount (fun s => ¬ orV V q p s) x (t * qn) =
          (Finset.univ.filter (fun W : Fin (t * qn) → Bool =>
            ¬ orV V q p (codeP x (List.ofFn W)))).card := by
        unfold accCount; congr 1; ext W; simp
      rw [e]
      calc 2 ^ t * _ ≤ 2 ^ t * (2 ^ qn - accCount V x qn) ^ t := Nat.mul_le_mul_left _ hsub
        _ ≤ 2 ^ (qn * t) := h3
        _ = 2 ^ (t * qn) := by rw [mul_comm]
    · intro hL
      rw [accCount_eq_zero]
      intro W hW
      rw [orV_code] at hW
      obtain ⟨i, hi⟩ := hW
      exact accCount_eq_zero.1 ((hq x).2 hL) _ hi
  exact key _ (Polynomial.eval_mul)

/-- **RP ⊆ BPP.** -/
theorem RP_subset_BPP {L : Language} (h : InRP L) : InBPP L := by
  obtain ⟨V, q, hV, hq⟩ := h.amplify (Polynomial.C 2)
  refine ⟨V, q, hV, fun x => ⟨fun hL => ?_, fun hL => ?_⟩⟩
  · have := (hq x).1 hL
    simp only [Polynomial.eval_C] at this
    rw [accCount_compl] at this
    have := accCount_le V x (q.eval x.length)
    omega
  · rw [(hq x).2 hL]; simp

theorem RP_subset_NP_inter_BPP {L : Language} (h : InRP L) : InNP L ∧ InBPP L :=
  ⟨RP_subset_NP h, RP_subset_BPP h⟩

theorem InBPP.of_compl {L : Language} (h : InBPP (fun x => ¬ L x)) : InBPP L :=
  h.compl.congr (fun _ => not_not)

/-- **coRP ⊆ coNP ∩ BPP.** -/
theorem coRP_subset_coNP_inter_BPP {L : Language} (h : InCoRP L) : InCoNP L ∧ InBPP L :=
  ⟨RP_subset_NP h, (RP_subset_BPP h).of_compl⟩

/-- **ZPP ⊆ NP ∩ coNP ∩ BPP.** -/
theorem ZPP_subset {L : Language} (h : InZPP L) : InNP L ∧ InCoNP L ∧ InBPP L :=
  ⟨RP_subset_NP h.1, RP_subset_NP h.2, RP_subset_BPP h.1⟩

/-! ### The zero-error characterization -/

theorem ZPPq_subset_ZPP {L : Language} (h : InZPPq L) : InZPP L := by
  obtain ⟨Y, N, q, hY, hN, hq⟩ := h
  refine ⟨⟨Y, q, hY, fun x => ⟨fun hL => ?_, fun hL => ?_⟩⟩,
    ⟨N, q, hN, fun x => ⟨fun hL => ?_, fun hL => ?_⟩⟩⟩
  · refine (hq x).2.trans (Nat.mul_le_mul_left _ (accCount_mono (fun w hw => ?_)))
    rcases hw with hw | hw
    · exact hw
    · exact absurd hL (((hq x).1 w).2 hw)
  · exact accCount_eq_zero.2 (fun w hw => hL (((hq x).1 w).1 hw))
  · refine (hq x).2.trans (Nat.mul_le_mul_left _ (accCount_mono (fun w hw => ?_)))
    rcases hw with hw | hw
    · exact absurd (((hq x).1 w).1 hw) hL
    · exact hw
  · exact accCount_eq_zero.2 (fun w hw => hL (((hq x).1 w).2 hw))

theorem ZPP_subset_ZPPq {L : Language} (h : InZPP L) : InZPPq L := by
  obtain ⟨⟨V1, q1, hV1, hq1⟩, ⟨V2, q2, hV2, hq2⟩⟩ := h
  refine ⟨fun s => V1 (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length))),
    fun s => V2 (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length))), q1 + q2,
    hV1.takeVP q1, hV2.dropVP q1, fun x => ?_⟩
  set n := x.length
  set m1 := q1.eval n
  set m2 := q2.eval n
  have key : ∀ M, M = m1 + m2 →
      (∀ w : Fin M → Bool,
        ((fun s => V1 (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length))))
          (codeP x (List.ofFn w)) → L x) ∧
        ((fun s => V2 (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length))))
          (codeP x (List.ofFn w)) → ¬ L x)) ∧
      2 ^ M ≤ 2 * accCount (fun s => V1 (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length))) ∨
        V2 (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length)))) x M := by
    intro M hM
    subst hM
    refine ⟨fun w => ⟨fun hw => ?_, fun hw hL => ?_⟩, ?_⟩
    · simp only [decP_codeP, take_ofFn_add] at hw
      by_contra hL
      exact accCount_eq_zero.1 ((hq1 x).2 hL) _ hw
    · simp only [decP_codeP, drop_ofFn_add] at hw
      exact accCount_eq_zero.1 ((hq2 x).2 (not_not.2 hL)) _ hw
    · by_cases hL : L x
      · have h1 : 2 ^ m1 ≤ 2 * accCount V1 x m1 := (hq1 x).1 hL
        have c : accCount (fun s => V1 (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length))))
            x (m1 + m2) = accCount V1 x m1 * 2 ^ m2 := by
          unfold accCount
          simp only [decP_codeP]
          convert count_take (m := m1) (d := m2) (fun l => V1 (codeP x l))
        have hm := accCount_mono (V := fun s => V1 (codeP (decP s).1 ((decP s).2.take
          (q1.eval (decP s).1.length)))) (V' := fun s => V1 (codeP (decP s).1 ((decP s).2.take
          (q1.eval (decP s).1.length))) ∨ V2 (codeP (decP s).1 ((decP s).2.drop
          (q1.eval (decP s).1.length)))) (x := x) (m := m1 + m2) (fun w hw => Or.inl hw)
        rw [c] at hm
        rw [pow_add]
        have := Nat.mul_le_mul_right (2 ^ m2) h1
        linarith
      · have h2 : 2 ^ m2 ≤ 2 * accCount V2 x m2 := (hq2 x).1 hL
        have c : accCount (fun s => V2 (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length))))
            x (m1 + m2) = 2 ^ m1 * accCount V2 x m2 := by
          unfold accCount
          simp only [decP_codeP]
          convert count_drop (m := m1) (d := m2) (fun l => V2 (codeP x l))
        have hm := accCount_mono (V := fun s => V2 (codeP (decP s).1 ((decP s).2.drop
          (q1.eval (decP s).1.length)))) (V' := fun s => V1 (codeP (decP s).1 ((decP s).2.take
          (q1.eval (decP s).1.length))) ∨ V2 (codeP (decP s).1 ((decP s).2.drop
          (q1.eval (decP s).1.length)))) (x := x) (m := m1 + m2) (fun w hw => Or.inr hw)
        rw [c] at hm
        rw [pow_add]
        have := Nat.mul_le_mul_left (2 ^ m1) h2
        linarith
  exact key _ (Polynomial.eval_add)

/-- **ZPP = RP ∩ coRP equals the zero-error "answer or ?" class.** -/
theorem ZPP_iff_ZPPq (L : Language) : InZPP L ↔ InZPPq L := ⟨ZPP_subset_ZPPq, ZPPq_subset_ZPP⟩

/-! ### Corollaries -/

/-- **NP ⊆ BPP ⇒ PH = Σ₂** (Adleman + Karp–Lipton). -/
theorem PH_collapse_of_NP_subset_BPP (H : ∀ L, InNP L → InBPP L) (L : Language) :
    InPH L ↔ InSigma 2 L :=
  karpLipton (fun L' hL' => adleman (H L' hL')) L

/-- **P = NP ⇒ BPP = P** (Sipser–Gács–Lautemann + PH collapse). -/
theorem BPP_eq_P_of_P_eq_NP (h : P_eq_NP) (L : Language) : InBPP L ↔ InP L :=
  ⟨fun hb => (PH_eq_P_of_P_eq_NP h L).1 ⟨2, BPP_subset_Sigma2 hb⟩, P_subset_BPP⟩

/-- **P = NP ⇒ RP = ZPP = P** as well. -/
theorem RP_eq_P_of_P_eq_NP (h : P_eq_NP) (L : Language) : InRP L ↔ InP L :=
  ⟨fun hr => (BPP_eq_P_of_P_eq_NP h L).1 (RP_subset_BPP hr), P_subset_RP⟩

end PvnpReal
