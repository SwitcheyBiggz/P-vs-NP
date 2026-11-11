/-
  PvnpReal.KarpLipton — **Karp–Lipton**: `NP ⊆ P/poly → PH = Σ₂`.

  Proof (self-reducibility). For `L ∈ Π₂`, `x ∈ L ↔ ∀u ∃w R(x,u,w)`. The *prefix language*
  `Lpre = {(x,u),p : ∃w', |p w'| = q₀(|x|) ∧ R(x,u,p w')}` is in NP, so (hypothesis) in P/poly with
  advice `adv`. Given any string `a` (read as a table of advice strings, one slot per input length
  up to a polynomial bound), the polynomial-time search `kSrch x u a` extends a prefix bit by bit,
  choosing `true` iff the advice machine accepts the extended prefix. Then
  `x ∈ L ↔ ∃a ∀u R(x, u, kSrch x u a)` (Σ₂): `←` needs nothing about `a`; `→` takes for `a` the true
  advice table (`advCat`), for which the search keeps the prefix extendable. Hence `Π₂ ⊆ Σ₂`,
  so `Σ₂ = Π₂` and PH collapses (`PH_eq_Sigma_of_Sigma_subset_Pi`).
  (The self-reducible NP language used is the generic prefix language, not SAT itself; with
  `SAT_Ppoly_iff` the hypothesis may equivalently be stated as `SAT ∈ P/poly`.)
-/
import PvnpReal.Ppoly
import PvnpReal.IterTM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing Computability

open scoped Classical

/-! ### The prefix language -/

def preBody (R : Language) (q₀ : Polynomial ℕ) (s w : List Bool) : Prop :=
  ((decP s).2 ++ w).length = q₀.eval (decP (decP s).1).1.length ∧
    R (codeP (decP (decP s).1).1 ((decP (decP s).1).2 ++ ((decP s).2 ++ w)))

/-- `codeP (codeP x u) p ∈ Lpre ↔ ∃ w', |p ++ w'| = q₀(|x|) ∧ R (codeP x (u ++ (p ++ w')))`. -/
def Lpre (R : Language) (q₀ : Polynomial ℕ) : Language := fun s => ∃ w, preBody R q₀ s w

theorem Lpre_code (R : Language) (q₀ : Polynomial ℕ) (x u p : List Bool) :
    Lpre R q₀ (codeP (codeP x u) p) ↔
      ∃ w, (p ++ w).length = q₀.eval x.length ∧ R (codeP x (u ++ (p ++ w))) := by
  simp [Lpre, preBody, decP_codeP]

theorem decP_fst_len (s : List Bool) : (decP s).1.length ≤ s.length := by
  have := decP_len s.length s le_rfl; omega

theorem Lpre_NP {R : Language} (hR : InP R) (q₀ : Polynomial ℕ) : InNP (Lpre R q₀) := by
  have hS : PS (fun t => (decP t).1) := PS.fstP
  have hY : PS (fun t => (decP (decP t).1).1) := PS.comp hS PS.fstP
  have hX : PS (fun t => (decP (decP (decP t).1).1).1) := PS.comp hY PS.fstP
  have hU : PS (fun t => (decP (decP (decP t).1).1).2) := PS.comp hY PS.sndP
  have hP : PS (fun t => (decP (decP t).1).2) := PS.comp hS PS.sndP
  have hPW : PS (fun t => (decP (decP t).1).2 ++ (decP t).2) := PS.append hP PS.sndP
  have hg : InP (fun t => preBody R q₀ (decP t).1 (decP t).2) :=
    ((InP.ofPUeq (PU.lenX.comp hPW) (PU.polyOf q₀ (PU.lenX.comp hX))).inter
      (hR.compPS (PS.codePF hX (PS.append hU hPW)))).congr (fun t => Iff.rfl)
  obtain ⟨V, hV, hVg⟩ := pairDecider hg
  refine ⟨V, q₀, hV, fun s => ?_⟩
  simp only [Lpre, hVg, decP_codeP]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    have h1 := hw.1
    rw [List.length_append] at h1
    have := decP_fst_len (decP s).1; have := decP_fst_len s
    exact le_trans (by omega) (poly_eval_mono q₀ (show (decP (decP s).1).1.length ≤ s.length by omega))
  · rintro ⟨w, -, hw⟩; exact ⟨w, hw⟩

/-! ### The advice-guided witness search -/

section Search

variable (A : Language) (qa NP : Polynomial ℕ)

/-- Next bit: does the advice machine accept the prefix extended by `true`?  The context is
`c = codeP (codeP x u) a`; the advice for input length `m` is read from slot `m` of `a`
(width `qa(NP(|x|))`, length `qa(m)`). -/
noncomputable def kBit (c p : List Bool) : Bool :=
  decide (A (codeP (codeP (decP c).1 (p ++ [true]))
    (subL (decP c).2 ((codeP (decP c).1 (p ++ [true])).length * (qa.comp NP).eval (decP (decP c).1).1.length)
      (qa.eval (codeP (decP c).1 (p ++ [true])).length))))

noncomputable def kStep (y : List Bool) : List Bool :=
  codeP (decP y).1 ((decP y).2 ++ [kBit A qa NP (decP y).1 (decP y).2])

noncomputable def kPref (c : List Bool) : ℕ → List Bool
  | 0 => []
  | i + 1 => kPref c i ++ [kBit A qa NP c (kPref c i)]

theorem kPref_length (c : List Bool) : ∀ i, (kPref A qa NP c i).length = i
  | 0 => rfl
  | i + 1 => by simp [kPref, kPref_length c i]

theorem kStep_iter (c : List Bool) : ∀ i, (kStep A qa NP)^[i] (codeP c []) = codeP c (kPref A qa NP c i)
  | 0 => rfl
  | i + 1 => by rw [Function.iterate_succ_apply', kStep_iter c i, kStep, decP_codeP]; rfl

/-- The search result for `x, u` with advice table `a`, of length `q₀(|x|)`. -/
noncomputable def kSrch (q₀ : Polynomial ℕ) (x u a : List Bool) : List Bool :=
  (decP ((kStep A qa NP)^[q₀.eval x.length] (codeP (codeP (codeP x u) a) []))).2

theorem kSrch_eq (q₀ : Polynomial ℕ) (x u a : List Bool) :
    kSrch A qa NP q₀ x u a = kPref A qa NP (codeP (codeP x u) a) (q₀.eval x.length) := by
  rw [kSrch, kStep_iter, decP_codeP]

theorem codeL_append (a b : List Bool) : codeL (a ++ b) = codeL a ++ codeL b := by
  simp [codeL]

theorem kStep_len_code (c p : List Bool) :
    (kStep A qa NP (codeP c p)).length ≤ (codeP c p).length + 3 := by
  rw [kStep, decP_codeP]
  simp only [codeP, codeL_append, List.length_append, List.length_cons]
  cases kBit A qa NP c p <;> simp [codeL] <;> omega

theorem kStep_len (y : List Bool) : (kStep A qa NP y).length ≤ 3 * y.length + 4 := by
  rw [kStep]
  have := codeP_length_le (decP y).1 ((decP y).2 ++ [kBit A qa NP (decP y).1 (decP y).2])
  have := decP_len y.length y le_rfl
  simp only [List.length_append, List.length_singleton] at *
  omega

theorem kStep_iter_len : ∀ i y, ((kStep A qa NP)^[i] y).length ≤ 3 * y.length + 4 + 3 * i := by
  have hc : ∀ i c p, ((kStep A qa NP)^[i] (codeP c p)).length ≤ (codeP c p).length + 3 * i := by
    intro i
    induction i with
    | zero => intro c p; simp
    | succ i ih =>
      intro c p
      rw [Function.iterate_succ_apply, show kStep A qa NP (codeP c p) = codeP c
        (p ++ [kBit A qa NP c p]) by rw [kStep, decP_codeP]]
      have := ih c (p ++ [kBit A qa NP c p])
      have := kStep_len_code A qa NP c p
      rw [show kStep A qa NP (codeP c p) = codeP c (p ++ [kBit A qa NP c p]) by
        rw [kStep, decP_codeP]] at this
      omega
  intro i y
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [Function.iterate_succ_apply, show kStep A qa NP y = codeP (decP y).1
      ((decP y).2 ++ [kBit A qa NP (decP y).1 (decP y).2]) from rfl]
    have := hc i (decP y).1 ((decP y).2 ++ [kBit A qa NP (decP y).1 (decP y).2])
    have := kStep_len A qa NP y
    rw [show kStep A qa NP y = codeP (decP y).1
      ((decP y).2 ++ [kBit A qa NP (decP y).1 (decP y).2]) from rfl] at this
    omega

theorem PS.kStepP (hA : InP A) : PS (kStep A qa NP) := by
  have hc : PS (fun y => (decP y).1) := PS.fstP
  have hp : PS (fun y => (decP y).2) := PS.sndP
  have hs1 : PS (fun y => codeP (decP (decP y).1).1 ((decP y).2 ++ [true])) :=
    PS.codePF (PS.comp hc PS.fstP) (PS.append hp (PS.const [true]))
  have hx : PS (fun y => (decP (decP (decP y).1).1).1) := PS.comp (PS.comp hc PS.fstP) PS.fstP
  have hslot : PS (fun y => PvnpReal.subL (decP (decP y).1).2
      ((codeP (decP (decP y).1).1 ((decP y).2 ++ [true])).length *
        (qa.comp NP).eval (decP (decP (decP y).1).1).1.length)
      (qa.eval (codeP (decP (decP y).1).1 ((decP y).2 ++ [true])).length)) :=
    PS.subL (PS.comp hc PS.sndP) ((PU.lenX.comp hs1).mul (PU.polyOf _ (PU.lenX.comp hx)))
      (PU.polyOf qa (PU.lenX.comp hs1))
  have hbit : PS (fun y => [kBit A qa NP (decP y).1 (decP y).2]) :=
    (PS.comp (PS.codePF hs1 hslot) (PS.ofInP hA)).congr (fun y => rfl)
  exact (PS.codePF hc (PS.append hp hbit)).congr (fun y => rfl)

theorem PS.kSrchP (hA : InP A) (q₀ : Polynomial ℕ) {X U Aa : List Bool → List Bool}
    (hX : PS X) (hU : PS U) (hAa : PS Aa) :
    PS (fun s => kSrch A qa NP q₀ (X s) (U s) (Aa s)) := by
  have hI := PS.iter (PS.kStepP A qa NP hA) (3 * Polynomial.X + 4) (fun y i => by
    have := kStep_iter_len A qa NP i y
    simp; nlinarith)
  have hz : PS (fun s => List.replicate (q₀.eval (X s).length) true ++
      false :: codeP (codeP (codeP (X s) (U s)) (Aa s)) []) :=
    PS.append (PU.polyOf q₀ (PU.lenX.comp hX))
      (PS.cons false (PS.codePF (PS.codePF (PS.codePF hX hU) hAa) (PS.const [])))
  exact (PS.comp (PS.comp hz hI) PS.sndP).congr (fun s => by simp only [lpN_rep, lpX_rep]; rfl)

end Search

/-! ### Karp–Lipton -/

/-- **`NP ⊆ P/poly → Π₂ ⊆ Σ₂`.** -/
theorem Pi2_subset_Sigma2 (H : NP_subset_Ppoly) (L : Language) (hL : InPi 2 L) : InSigma 2 L := by
  obtain ⟨R, qs, hR, hLR⟩ := hL
  obtain ⟨A, qa, adv, hA, hadv, hLA⟩ := H _ (Lpre_NP hR (qs 0))
  -- bound on the lengths of the queried strings
  set NP : Polynomial ℕ := 9 * Polynomial.X + 9 * qs 1 + 3 * qs 0 + 4 with hNP
  set WP : Polynomial ℕ := qa.comp NP with hWP
  set P1 : Polynomial ℕ := (NP + 1) * WP with hP1
  have hW : ∀ n, ∀ m ≤ NP.eval n, qa.eval m ≤ WP.eval n := fun n m hm => by
    simp only [hWP, Polynomial.eval_comp]; exact poly_eval_mono qa hm
  have hP1e : ∀ n, P1.eval n = (NP.eval n + 1) * WP.eval n := fun n => by
    simp [hP1, Polynomial.eval_mul, Polynomial.eval_add]
  let R2 : Language := fun s => R (codeP (decP s).1 (((decP s).2.drop (P1.eval (decP s).1.length)) ++
    kSrch A qa NP (qs 0) (decP s).1 ((decP s).2.drop (P1.eval (decP s).1.length))
      ((decP s).2.take (P1.eval (decP s).1.length))))
  have hR2 : InP R2 := by
    have hX : PS (fun s => (decP s).1) := PS.fstP
    have hU : PS (fun s => (decP s).2.drop (P1.eval (decP s).1.length)) :=
      PS.dropU PS.sndP (PU.polyOf P1 (PU.lenX.comp hX))
    have hAa : PS (fun s => (decP s).2.take (P1.eval (decP s).1.length)) :=
      PS.takeU PS.sndP (PU.polyOf P1 (PU.lenX.comp hX))
    exact hR.compPS (PS.codePF hX (PS.append hU (PS.kSrchP A qa NP hA (qs 0) hX hU hAa)))
  refine ⟨R2, fun i => if i = 0 then qs 1 else P1, hR2, fun x => ?_⟩
  rw [hLR x]
  simp only [altQ_succ_true, altQ_succ_false, altQ_zero, List.nil_append, if_pos, if_neg,
    one_ne_zero, ↓reduceIte]
  have hR2e : ∀ a u : List Bool, a.length = P1.eval x.length →
      (R2 (codeP x (a ++ u)) ↔ R (codeP x (u ++ kSrch A qa NP (qs 0) x u a))) := by
    intro a u ha
    simp only [R2, decP_codeP, ← ha, List.drop_left, List.take_left]
  constructor
  · -- completeness: the true advice table
    intro hall
    set N := NP.eval x.length
    set a := advCat adv qa N (WP.eval x.length)
    have ha : a.length = P1.eval x.length := by rw [advCat_length hadv (hW _), hP1e]
    refine ⟨a, ha, fun u hu => (hR2e a u ha).2 ?_⟩
    rw [kSrch_eq]
    set c := codeP (codeP x u) a
    -- each bit is the true answer
    have hbit : ∀ p : List Bool, p.length < (qs 0).eval x.length →
        (kBit A qa NP c p = true ↔ Lpre R (qs 0) (codeP (codeP x u) (p ++ [true]))) := by
      intro p hp
      have hlen : (codeP (codeP x u) (p ++ [true])).length ≤ N := by
        have h1 := codeP_length_le (codeP x u) (p ++ [true])
        have h2 := codeP_length_le x u
        simp only [List.length_append, List.length_singleton] at h1
        simp only [N, hNP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_ofNat]
        rw [hu] at h2; omega
      simp only [kBit, c, decP_codeP, decide_eq_true_eq]
      rw [advCat_slot hadv (hW _) hlen, ← hLA]
    have inv : ∀ i ≤ (qs 0).eval x.length, ∃ w,
        (kPref A qa NP c i ++ w).length = (qs 0).eval x.length ∧
          R (codeP x (u ++ (kPref A qa NP c i ++ w))) := by
      intro i
      induction i with
      | zero => intro _; obtain ⟨w, hw, hRw⟩ := hall u hu; exact ⟨w, by simpa [kPref] using hw, by simpa [kPref] using hRw⟩
      | succ i ih =>
        intro hi
        obtain ⟨w, hw, hRw⟩ := ih (by omega)
        have hpl := kPref_length A qa NP c i
        simp only [kPref]
        by_cases hb : kBit A qa NP c (kPref A qa NP c i) = true
        · rw [hb]
          exact (Lpre_code R (qs 0) x u _).1 ((hbit _ (by omega)).1 hb)
        · rw [Bool.not_eq_true] at hb
          rw [hb]
          rcases w with _ | ⟨b, w⟩
          · rw [List.append_nil, hpl] at hw; omega
          · cases b
            · exact ⟨w, by simpa [List.append_assoc] using hw, by simpa [List.append_assoc] using hRw⟩
            · exact absurd ((hbit (kPref A qa NP c i) (by omega)).2 ((Lpre_code R (qs 0) x u _).2
                ⟨w, by simpa [List.append_assoc] using hw, by simpa [List.append_assoc] using hRw⟩)) (by simp [hb])
    obtain ⟨w, hw, hRw⟩ := inv _ le_rfl
    have : w = [] := by
      rw [List.length_append, kPref_length] at hw
      exact List.length_eq_zero_iff.1 (by omega)
    subst this
    simpa using hRw
  · -- soundness: any table works
    rintro ⟨a, ha, hall⟩ u hu
    refine ⟨kSrch A qa NP (qs 0) x u a, by rw [kSrch_eq, kPref_length], (hR2e a u ha).1 (hall u hu)⟩

/-- Under `NP ⊆ P/poly`, also `Σ₂ ⊆ Π₂`. -/
theorem Sigma2_subset_Pi2 (H : NP_subset_Ppoly) (L : Language) (hL : InSigma 2 L) : InPi 2 L := by
  have h1 : InPi 2 (fun x => ¬ L x) := (InSigma_iff_compl 2 L).1 hL
  have h2 : InSigma 2 (fun x => ¬ L x) := Pi2_subset_Sigma2 H _ h1
  exact ((InSigma_iff_compl 2 _).1 h2).congr (fun x => not_not)

/-- **Karp–Lipton theorem**: `NP ⊆ P/poly → PH = Σ₂`. -/
theorem karpLipton (H : NP_subset_Ppoly) (L : Language) : InPH L ↔ InSigma 2 L :=
  PH_eq_Sigma_of_Sigma_subset_Pi 2 (by norm_num) (Sigma2_subset_Pi2 H) L

/-- Karp–Lipton with the hypothesis on SAT. -/
theorem karpLipton_SAT (h : InPpoly SATLang) (L : Language) : InPH L ↔ InSigma 2 L :=
  karpLipton (SAT_Ppoly_iff.1 h) L

/-- Under `NP ⊆ P/poly`, Σ₂-SAT ∈ Π₂ (equivalently, by `SigmaSAT_in_Pi_iff`, Σ₂ = Π₂). -/
theorem SigmaSAT2_in_Pi2 (H : NP_subset_Ppoly) : InPi 2 (SigmaSAT 2) :=
  Sigma2_subset_Pi2 H _ (SigmaSAT_in_Sigma 2)

/-- **Corollary**: if PH does not collapse to Σ₂, then `NP ⊄ P/poly` (in particular SAT ∉ P/poly). -/
theorem NP_not_subset_Ppoly_of_PH_ne_Sigma2 (h : ¬ ∀ L, InPH L ↔ InSigma 2 L) : ¬ NP_subset_Ppoly :=
  fun H => h (karpLipton H)

theorem SAT_not_Ppoly_of_PH_ne_Sigma2 (h : ¬ ∀ L, InPH L ↔ InSigma 2 L) : ¬ InPpoly SATLang :=
  fun hS => h (karpLipton_SAT hS)

end PvnpReal
