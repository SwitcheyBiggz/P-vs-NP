/-
  PvnpReal.PHNP — **`NP = coNP → PH = NP`**.

  Inside-out collapse with an NP leaf: under NP = coNP, absorbing the innermost quantifier block into
  an NP predicate of `codeP x u` keeps it in NP (`Rcol_NP`; the existential case merges the block with
  the NP witness into one witness `codeP w v`, `Rcol_true_NP`, which needs no hypothesis).
-/
import PvnpReal.PH

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

theorem InP.ofPUle {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) : InP (fun s => u s ≤ v s) :=
  (InP.ofPUeq (PU.sub hu hv) (PU.const 0)).congr (fun s => by
    show (u s - v s = 0) ↔ u s ≤ v s; omega)

theorem InNP.congr {L L' : Language} (h : InNP L) (e : ∀ x, L x ↔ L' x) : InNP L' :=
  InNP.of_reduces ⟨fun x => x, PS.id, fun x => (e x).symm⟩ h

theorem codeL_length_le (a : List Bool) : (codeL a).length ≤ 3 * a.length := by
  induction a with
  | nil => simp [codeL]
  | cons c a ih =>
    have e : codeL (c :: a) = true :: (if c then [true, false] else [false]) ++ codeL a := by
      simp [codeL]
    rw [e]; cases c <;> simp <;> omega

theorem codeP_length_le (a b : List Bool) : (codeP a b).length ≤ 3 * a.length + 3 * b.length + 1 := by
  have := codeL_length_le a; have := codeL_length_le b
  simp only [codeP, List.length_append, List.length_cons]; omega

/-- **NP is closed under an exact-length existential block** (in the `Rcol` form). -/
theorem Rcol_true_NP {R : Language} (hR : InNP R) (q : Polynomial ℕ) : InNP (Rcol true R q) := by
  obtain ⟨VR, qR, hVR, hRx⟩ := hR
  -- `t = codeP s (codeP w v)`
  let A : List Bool → List Bool := fun t => (decP (decP t).1).1
  let B : List Bool → List Bool := fun t => (decP (decP t).1).2
  let W : List Bool → List Bool := fun t => (decP (decP t).2).1
  let Vv : List Bool → List Bool := fun t => (decP (decP t).2).2
  have hA : PS A := PS.comp PS.fstP PS.fstP
  have hB : PS B := PS.comp PS.fstP PS.sndP
  have hW : PS W := PS.comp PS.sndP PS.fstP
  have hVv : PS Vv := PS.comp PS.sndP PS.sndP
  have hC : PS (fun t => codeP (A t) (B t ++ W t)) := PS.codePF hA (PS.append hB hW)
  have hg : InP (fun t => (VR (codeP (A t) (B t ++ W t), Vv t) = true ∧
      (W t).length = q.eval (A t).length) ∧
      (Vv t).length ≤ qR.eval (codeP (A t) (B t ++ W t)).length) :=
    ((((InP.ofPair hVR).compPS (PS.codePF hC hVv)).congr (fun t => by simp only [decP_codeP])).inter
      (InP.ofPUeq (PU.lenX.comp hW) (PU.polyOf q (PU.lenX.comp hA)))).inter
      (InP.ofPUle (PU.lenX.comp hVv) (PU.polyOf qR (PU.lenX.comp hC)))
  obtain ⟨V, hV, hVg⟩ := pairDecider hg
  let Q : Polynomial ℕ := 3 * q + 3 * qR.comp (3 * Polynomial.X + 3 * q + 1) + 1
  refine ⟨V, Q, hV, fun s => ?_⟩
  simp only [Rcol, if_true, hVg, A, B, W, Vv, decP_codeP]
  have hs := decP_len s.length s le_rfl
  constructor
  · rintro ⟨w, hw, hr⟩
    obtain ⟨v, hv, hvV⟩ := (hRx _).1 hr
    refine ⟨codeP w v, ?_, ?_⟩
    swap
    · simp only [decP_codeP]; exact ⟨⟨hvV, hw⟩, hv⟩
    have h1 := codeP_length_le w v
    have h2 : w.length ≤ q.eval s.length := hw ▸ poly_eval_mono q (by omega)
    have h3 := codeP_length_le (decP s).1 ((decP s).2 ++ w)
    have h4 : v.length ≤ qR.eval (3 * s.length + 3 * q.eval s.length + 1) :=
      hv.trans (poly_eval_mono qR (by simp at h3; omega))
    simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    omega
  · rintro ⟨z, -, ⟨hvV, hw⟩, hv⟩
    exact ⟨_, hw, (hRx _).2 ⟨_, hv, hvV⟩⟩

def NP_eq_coNP : Prop := ∀ L : Language, InNP L ↔ InCoNP L

theorem Rcol_NP (hNC : NP_eq_coNP) {R : Language} (hR : InNP R) (q : Polynomial ℕ) (c : Bool) :
    InNP (Rcol c R q) := by
  cases c
  · have hnR : InNP (fun s => ¬ R s) := (hNC R).1 hR
    have h1 : InNP (fun s => ¬ Rcol false R q s) := (Rcol_true_NP hnR q).congr (fun s => by
      simp only [Rcol, if_true, Bool.false_eq_true, if_false, not_forall, exists_prop])
    exact (hNC _).2 h1
  · exact Rcol_true_NP hR q

/-- Σ_k with an NP leaf predicate (auxiliary). -/
def InSigmaN (k : ℕ) (L : Language) : Prop :=
  ∃ (R : Language) (qs : ℕ → Polynomial ℕ), InNP R ∧ ∀ x, L x ↔ altQ R qs x k true []

theorem SigmaN_subset_NP (hNC : NP_eq_coNP) : ∀ k L, InSigmaN k L → InNP L := by
  intro k
  induction k with
  | zero =>
    intro L ⟨R, qs, hR, hL⟩
    exact InNP.of_reduces ⟨fun x => codeP x [], PS.codePnil, fun x => hL x⟩ hR
  | succ k ih =>
    intro L ⟨R, qs, hR, hL⟩
    exact ih L ⟨_, _, Rcol_NP hNC hR (qs 0) (innerT k true),
      fun x => (hL x).trans (altQ_collapse R qs x k true [])⟩

/-- **`NP = coNP → Σ_k ⊆ NP` for every `k`.** -/
theorem Sigma_subset_NP_of_NP_eq_coNP (hNC : NP_eq_coNP) (k : ℕ) (L : Language) (h : InSigma k L) :
    InNP L := by
  obtain ⟨R, qs, hR, hL⟩ := h
  exact SigmaN_subset_NP hNC k L ⟨R, qs, P_subset_NP R hR, hL⟩

/-- **Collapse: `NP = coNP → PH = NP`.** -/
theorem PH_eq_NP_of_NP_eq_coNP (hNC : NP_eq_coNP) (L : Language) : InPH L ↔ InNP L :=
  ⟨fun ⟨k, h⟩ => Sigma_subset_NP_of_NP_eq_coNP hNC k L h, NP_subset_PH L⟩

end PvnpReal
