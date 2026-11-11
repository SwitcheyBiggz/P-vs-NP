/-
  PvnpReal.PH — the **polynomial hierarchy** via alternating polynomially-bounded quantifiers
  over a P predicate (Arora–Barak Def. 5.4 style, with one polynomial per quantifier block).

  `altQ R qs x k b u`: `k` quantifier blocks remain, the next one is `∃` iff `b`; the block
  with `j+1` blocks remaining ranges over strings of length exactly `(qs j).eval |x|`; blocks are
  concatenated into `u`, and after the last block the P predicate `R` is applied to `codeP x u`.

  * `InSigma k L`: `L x ↔ ∃u₁ ∀u₂ … R(x,u₁…u_k)`; `InPi k L` the same starting with `∀`;
    `InPH L := ∃ k, InSigma k L`.
  * `Sigma0_iff_P`, `Sigma1_iff_NP`, `Pi1_iff_coNP`, `InPi_iff_compl`,
    `Sigma_Pi_subset_succ` (Σ_k ∪ Π_k ⊆ Σ_{k+1} ∩ Π_{k+1}),
    `PH_eq_P_of_P_eq_NP` (collapse).
-/
import PvnpReal.EncTM
import PvnpReal.LadnerTools

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### Bridges between P predicates on codes and pair-input machines -/

theorem InP.ofPUeq {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) : InP (fun s => u s = v s) := by
  obtain ⟨h⟩ := PS.boolOf (PU.indEq hu hv)
  refine ⟨_, ⟨strToDecider h⟩, fun s => ?_⟩
  by_cases e : u s = v s <;> simp [e]

/-- A P predicate on codes `codeP x w` gives a pair-input polytime decider. -/
theorem pairDecider {g : Language} (hg : InP g) :
    ∃ V : List Bool × List Bool → Bool, Nonempty (TM2ComputableInPolyTime pairEnc encodeBool V) ∧
      ∀ p, V p = true ↔ g (codeP p.1 p.2) := by
  obtain ⟨f, ⟨hf⟩, hfg⟩ := hg
  obtain ⟨he⟩ := encP
  exact ⟨_, ⟨composeGen he hf⟩, fun p => (hfg _).symm⟩

/-- A pair-input polytime decider gives a P predicate on codes (through the decoder). -/
theorem InP.ofPair {V : List Bool × List Bool → Bool}
    (hV : Nonempty (TM2ComputableInPolyTime pairEnc encodeBool V)) : InP (fun t => V (decP t) = true) := by
  obtain ⟨hV⟩ := hV
  exact ⟨_, ⟨composeGen decComputable hV⟩, fun _ => Iff.rfl⟩

theorem InP.compPS {R : Language} (hR : InP R) {f : List Bool → List Bool} (hf : PS f) :
    InP (fun s => R (f s)) :=
  InP.of_reduces ⟨f, hf, fun _ => Iff.rfl⟩ hR

/-! ### Definitions -/

/-- Alternating, exactly-length-bounded quantifier blocks over a predicate `R` of `codeP x u`. -/
def altQ (R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) : ℕ → Bool → List Bool → Prop
  | 0, _, u => R (codeP x u)
  | k + 1, true, u => ∃ w : List Bool, w.length = (qs k).eval x.length ∧ altQ R qs x k false (u ++ w)
  | k + 1, false, u => ∀ w : List Bool, w.length = (qs k).eval x.length → altQ R qs x k true (u ++ w)

@[simp] theorem altQ_zero (R : Language) (qs x b u) : altQ R qs x 0 b u = R (codeP x u) := rfl
@[simp] theorem altQ_succ_true (R : Language) (qs x k u) : altQ R qs x (k + 1) true u =
    ∃ w : List Bool, w.length = (qs k).eval x.length ∧ altQ R qs x k false (u ++ w) := rfl
@[simp] theorem altQ_succ_false (R : Language) (qs x k u) : altQ R qs x (k + 1) false u =
    ∀ w : List Bool, w.length = (qs k).eval x.length → altQ R qs x k true (u ++ w) := rfl

/-- **Σ_k**: `x ∈ L ↔ ∃u₁ ∀u₂ … Q u_k. R(x, u₁⋯u_k)` with `R ∈ P` and `|u_i|` polynomial in `|x|`. -/
def InSigma (k : ℕ) (L : Language) : Prop :=
  ∃ (R : Language) (qs : ℕ → Polynomial ℕ), InP R ∧ ∀ x, L x ↔ altQ R qs x k true []

/-- **Π_k**: the same with the first block universal. -/
def InPi (k : ℕ) (L : Language) : Prop :=
  ∃ (R : Language) (qs : ℕ → Polynomial ℕ), InP R ∧ ∀ x, L x ↔ altQ R qs x k false []

/-- **PH** = ⋃_k Σ_k. -/
def InPH (L : Language) : Prop := ∃ k, InSigma k L

theorem InSigma.congr {k : ℕ} {L L' : Language} (h : InSigma k L) (e : ∀ x, L x ↔ L' x) :
    InSigma k L' := by
  obtain ⟨R, qs, hR, hL⟩ := h; exact ⟨R, qs, hR, fun x => (e x).symm.trans (hL x)⟩

theorem InPi.congr {k : ℕ} {L L' : Language} (h : InPi k L) (e : ∀ x, L x ↔ L' x) : InPi k L' := by
  obtain ⟨R, qs, hR, hL⟩ := h; exact ⟨R, qs, hR, fun x => (e x).symm.trans (hL x)⟩

/-! ### Duality -/

theorem altQ_neg (R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) :
    ∀ k b u, ¬ altQ R qs x k b u ↔ altQ (fun s => ¬ R s) qs x k (!b) u := by
  intro k
  induction k with
  | zero => intro b u; rfl
  | succ k ih =>
    intro b u
    cases b
    · simp only [altQ_succ_false, Bool.not_false, altQ_succ_true, not_forall, ih, Bool.not_true]
      exact ⟨fun ⟨w, hw, h⟩ => ⟨w, hw, h⟩, fun ⟨w, hw, h⟩ => ⟨w, hw, h⟩⟩
    · simp only [altQ_succ_true, Bool.not_true, altQ_succ_false, not_exists, not_and, ih,
        Bool.not_false]

/-- **Π_k = co-Σ_k.** -/
theorem InPi_iff_compl (k : ℕ) (L : Language) : InPi k L ↔ InSigma k (fun x => ¬ L x) := by
  constructor
  · rintro ⟨R, qs, hR, hL⟩
    exact ⟨_, qs, hR.compl, fun x => (not_congr (hL x)).trans (altQ_neg R qs x k false [])⟩
  · rintro ⟨R, qs, hR, hL⟩
    refine ⟨_, qs, hR.compl, fun x => ?_⟩
    have := (not_congr (hL x)).trans (altQ_neg R qs x k true [])
    rw [not_not] at this; exact this

theorem InSigma_iff_compl (k : ℕ) (L : Language) : InSigma k L ↔ InPi k (fun x => ¬ L x) := by
  rw [InPi_iff_compl]
  exact ⟨fun h => h.congr (fun x => not_not.symm), fun h => h.congr (fun x => not_not)⟩

/-! ### Level 0 and level 1 -/

theorem PS.codePnil : PS (fun x => codeP x []) := PS.codePF PS.id (PS.const [])

/-- **Σ_0 = P.** -/
theorem Sigma0_iff_P (L : Language) : InSigma 0 L ↔ InP L := by
  constructor
  · rintro ⟨R, qs, hR, hL⟩
    exact (hR.compPS PS.codePnil).congr (fun x => (hL x).symm)
  · intro h
    refine ⟨fun s => L (decP s).1, fun _ => 0, h.compPS PS.fstP, fun x => ?_⟩
    simp [decP_codeP]

/-- **Π_0 = P.** -/
theorem Pi0_iff_P (L : Language) : InPi 0 L ↔ InP L := by
  rw [InPi_iff_compl, Sigma0_iff_P]
  exact ⟨fun h => h.compl.congr (fun x => not_not), InP.compl⟩

/-- **Σ_1 = NP.** -/
theorem Sigma1_iff_NP (L : Language) : InSigma 1 L ↔ InNP L := by
  constructor
  · rintro ⟨R, qs, hR, hL⟩
    have hg : InP (fun t => R t ∧ (decP t).2.length = (qs 0).eval (decP t).1.length) :=
      hR.inter (InP.ofPUeq (PU.lenX.comp PS.sndP) (PU.polyOf (qs 0) (PU.lenX.comp PS.fstP)))
    obtain ⟨V, hV, hVg⟩ := pairDecider hg
    refine ⟨V, qs 0, hV, fun x => ?_⟩
    rw [hL x]
    simp only [altQ_succ_true, altQ_zero, List.nil_append, hVg, decP_codeP]
    constructor
    · rintro ⟨w, hw, h⟩; exact ⟨w, hw.le, h, hw⟩
    · rintro ⟨w, -, h, hw⟩; exact ⟨w, hw, h⟩
  · rintro ⟨V, q, hV, hL⟩
    have hR : InP (fun s => V ((decP s).1, lpX (decP s).2) = true) :=
      ((InP.ofPair hV).compPS (PS.codePF PS.fstP (PS.comp PS.sndP PS.drop))).congr
        (fun s => by simp only [decP_codeP])
    refine ⟨_, fun _ => q + 1, hR, fun x => ?_⟩
    rw [hL x]
    simp only [altQ_succ_true, altQ_zero, List.nil_append, decP_codeP, Polynomial.eval_add,
      Polynomial.eval_one]
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨List.replicate (q.eval x.length - w.length) true ++ false :: w, ?_, ?_⟩
      · simp; omega
      · rw [lpX_rep]; exact h
    · rintro ⟨u, hu, h⟩
      refine ⟨lpX u, ?_, h⟩
      simp only [lpX, List.length_drop]; omega

/-- **Π_1 = coNP.** -/
theorem Pi1_iff_coNP (L : Language) : InPi 1 L ↔ InCoNP L := by
  rw [InPi_iff_compl, Sigma1_iff_NP]; rfl

/-! ### Dummy quantifier blocks: Σ_k ∪ Π_k ⊆ Σ_{k+1} ∩ Π_{k+1} -/

theorem altQ_congr (R : Language) (x : List Bool) :
    ∀ k (qs qs' : ℕ → Polynomial ℕ), (∀ i < k, qs i = qs' i) →
      ∀ b u, altQ R qs x k b u ↔ altQ R qs' x k b u := by
  intro k
  induction k with
  | zero => intro qs qs' _ b u; rfl
  | succ k ih =>
    intro qs qs' h b u
    have hk := h k (by omega)
    have h' := ih qs qs' (fun i hi => h i (by omega))
    cases b
    · simp only [altQ_succ_false, hk, h']
    · simp only [altQ_succ_true, hk, h']

/-- An empty innermost block. -/
noncomputable def qsIn (qs : ℕ → Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => 0
  | i + 1 => qs i

theorem altQ_inner (R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) :
    ∀ k b u, altQ R (qsIn qs) x (k + 1) b u ↔ altQ R qs x k b u := by
  intro k
  induction k with
  | zero =>
    intro b u
    cases b
    · simp only [altQ_succ_false, altQ_zero, qsIn, Polynomial.eval_zero, List.length_eq_zero_iff]
      exact ⟨fun h => by simpa using h [] rfl, fun h w hw => by subst hw; simpa using h⟩
    · simp only [altQ_succ_true, altQ_zero, qsIn, Polynomial.eval_zero, List.length_eq_zero_iff]
      exact ⟨fun ⟨w, hw, h⟩ => by subst hw; simpa using h, fun h => ⟨[], rfl, by simpa using h⟩⟩
  | succ k ih =>
    intro b u
    cases b
    · simp only [altQ_succ_false, qsIn, ih]
    · simp only [altQ_succ_true, qsIn, ih]

/-- An empty outermost block (at level `k`). -/
noncomputable def qsOut (qs : ℕ → Polynomial ℕ) (k : ℕ) : ℕ → Polynomial ℕ := fun i => if i = k then 0 else qs i

theorem altQ_outer (R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) (k : ℕ) (b : Bool) :
    altQ R (qsOut qs k) x (k + 1) b [] ↔ altQ R qs x k (!b) [] := by
  have hc := altQ_congr R x k (qsOut qs k) qs (fun i hi => by simp [qsOut]; omega)
  cases b
  · simp only [altQ_succ_false, qsOut, if_pos, Polynomial.eval_zero, List.length_eq_zero_iff,
      Bool.not_false, hc]
    exact ⟨fun h => by simpa using h [] rfl, fun h w hw => by subst hw; simpa using h⟩
  · simp only [altQ_succ_true, qsOut, if_pos, Polynomial.eval_zero, List.length_eq_zero_iff,
      Bool.not_true, hc]
    exact ⟨fun ⟨w, hw, h⟩ => by subst hw; simpa using h, fun h => ⟨[], rfl, by simpa using h⟩⟩

theorem InSigma.succ {k : ℕ} {L : Language} (h : InSigma k L) : InSigma (k + 1) L := by
  obtain ⟨R, qs, hR, hL⟩ := h
  exact ⟨R, qsIn qs, hR, fun x => (hL x).trans (altQ_inner R qs x k true []).symm⟩

theorem InPi.succ {k : ℕ} {L : Language} (h : InPi k L) : InPi (k + 1) L := by
  obtain ⟨R, qs, hR, hL⟩ := h
  exact ⟨R, qsIn qs, hR, fun x => (hL x).trans (altQ_inner R qs x k false []).symm⟩

theorem InPi.toSigma_succ {k : ℕ} {L : Language} (h : InPi k L) : InSigma (k + 1) L := by
  obtain ⟨R, qs, hR, hL⟩ := h
  exact ⟨R, qsOut qs k, hR, fun x => (hL x).trans (altQ_outer R qs x k true).symm⟩

theorem InSigma.toPi_succ {k : ℕ} {L : Language} (h : InSigma k L) : InPi (k + 1) L := by
  obtain ⟨R, qs, hR, hL⟩ := h
  exact ⟨R, qsOut qs k, hR, fun x => (hL x).trans (altQ_outer R qs x k false).symm⟩

/-- **Σ_k ∪ Π_k ⊆ Σ_{k+1} ∩ Π_{k+1}.** -/
theorem Sigma_Pi_subset_succ (k : ℕ) (L : Language) (h : InSigma k L ∨ InPi k L) :
    InSigma (k + 1) L ∧ InPi (k + 1) L := by
  rcases h with h | h
  · exact ⟨h.succ, h.toPi_succ⟩
  · exact ⟨h.toSigma_succ, h.succ⟩

theorem InSigma.mono {k m : ℕ} {L : Language} (h : InSigma k L) (hkm : k ≤ m) : InSigma m L := by
  induction m with
  | zero => obtain rfl : k = 0 := by omega
            exact h
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hl | hl
    · exact (ih (by omega)).succ
    · obtain rfl : k = m + 1 := by omega
      exact h

theorem InPi.toPH {k : ℕ} {L : Language} (h : InPi k L) : InPH L := ⟨k + 1, h.toSigma_succ⟩

theorem P_subset_PH (L : Language) (h : InP L) : InPH L := ⟨0, (Sigma0_iff_P L).2 h⟩
theorem NP_subset_PH (L : Language) (h : InNP L) : InPH L := ⟨1, (Sigma1_iff_NP L).2 h⟩
theorem coNP_subset_PH (L : Language) (h : InCoNP L) : InPH L := ((Pi1_iff_coNP L).2 h).toPH

/-- PH is closed under complement. -/
theorem InPH.compl {L : Language} (h : InPH L) : InPH (fun x => ¬ L x) := by
  obtain ⟨k, hk⟩ := h
  exact ((InSigma_iff_compl k L).1 hk).toPH

/-! ### Collapse: `P = NP → PH = P` -/

/-- Innermost quantifier type after `k` alternations starting with `b`. -/
def innerT : ℕ → Bool → Bool
  | 0, b => b
  | k + 1, b => innerT k (!b)

/-- The innermost block, absorbed into the predicate (on `codeP x u`). -/
def Rcol (c : Bool) (R : Language) (q : Polynomial ℕ) (s : List Bool) : Prop :=
  if c then ∃ w : List Bool, w.length = q.eval (decP s).1.length ∧ R (codeP (decP s).1 ((decP s).2 ++ w))
  else ∀ w : List Bool, w.length = q.eval (decP s).1.length → R (codeP (decP s).1 ((decP s).2 ++ w))

theorem altQ_collapse (R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) :
    ∀ k b u, altQ R qs x (k + 1) b u ↔
      altQ (Rcol (innerT k b) R (qs 0)) (fun i => qs (i + 1)) x k b u := by
  intro k
  induction k with
  | zero =>
    intro b u
    cases b <;> simp [Rcol, innerT, decP_codeP]
  | succ k ih =>
    intro b u
    cases b
    · simp only [altQ_succ_false, ih, innerT, Bool.not_false]
    · simp only [altQ_succ_true, ih, innerT, Bool.not_true]

/-- Under `P = NP`, an existential innermost block over a P predicate stays in P. -/
theorem Rcol_true_in_P (hPNP : P_eq_NP) {R : Language} (hR : InP R) (q : Polynomial ℕ) :
    InP (Rcol true R q) := by
  -- verifier on `codeP s w`
  have hA : PS (fun t => (decP (decP t).1).1) := PS.comp PS.fstP PS.fstP
  have hB : PS (fun t => (decP (decP t).1).2) := PS.comp PS.fstP PS.sndP
  have hg : InP (fun t => R (codeP (decP (decP t).1).1 ((decP (decP t).1).2 ++ (decP t).2)) ∧
      (decP t).2.length = q.eval (decP (decP t).1).1.length) :=
    (hR.compPS (PS.codePF hA (PS.append hB PS.sndP))).inter
      (InP.ofPUeq (PU.lenX.comp PS.sndP) (PU.polyOf q (PU.lenX.comp hA)))
  obtain ⟨V, hV, hVg⟩ := pairDecider hg
  have hNP : InNP (Rcol true R q) := by
    refine ⟨V, q, hV, fun s => ?_⟩
    simp only [Rcol, if_true, hVg, decP_codeP]
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨w, ?_, h, hw⟩
      rw [hw]; apply poly_eval_mono
      have := decP_len s.length s le_rfl; omega
    · rintro ⟨w, -, h, hw⟩; exact ⟨w, hw, h⟩
  exact (hPNP _).2 hNP

theorem Rcol_in_P (hPNP : P_eq_NP) {R : Language} (hR : InP R) (q : Polynomial ℕ) (c : Bool) :
    InP (Rcol c R q) := by
  cases c
  · have := (Rcol_true_in_P hPNP hR.compl q).compl
    refine this.congr (fun s => ?_)
    simp only [Rcol, if_true, Bool.false_eq_true, if_false, not_exists, not_and, not_not]
  · exact Rcol_true_in_P hPNP hR q

/-- **`P = NP → Σ_k ⊆ P` for every `k`.** -/
theorem Sigma_subset_P_of_P_eq_NP (hPNP : P_eq_NP) : ∀ k L, InSigma k L → InP L := by
  intro k
  induction k with
  | zero => intro L h; exact (Sigma0_iff_P L).1 h
  | succ k ih =>
    intro L h
    obtain ⟨R, qs, hR, hL⟩ := h
    exact ih L ⟨_, _, Rcol_in_P hPNP hR (qs 0) (innerT k true),
      fun x => (hL x).trans (altQ_collapse R qs x k true [])⟩

theorem Pi_subset_P_of_P_eq_NP (hPNP : P_eq_NP) (k : ℕ) (L : Language) (h : InPi k L) : InP L :=
  (Sigma_subset_P_of_P_eq_NP hPNP k _ ((InPi_iff_compl k L).1 h)).compl.congr (fun _ => not_not)

/-- **Collapse: `P = NP → PH = P`.** -/
theorem PH_eq_P_of_P_eq_NP (hPNP : P_eq_NP) (L : Language) : InPH L ↔ InP L :=
  ⟨fun ⟨k, h⟩ => Sigma_subset_P_of_P_eq_NP hPNP k L h, P_subset_PH L⟩

end PvnpReal
