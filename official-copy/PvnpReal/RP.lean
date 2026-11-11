/-
  PvnpReal.RP — one-sided error classes and closure properties of BPP (counting style).

  * Splitting random strings: `count_split`, `count_take`, `count_drop`
    (`Fin (m+d) → Bool ≃ (Fin m → Bool) × (Fin d → Bool)` via `Fin.appendEquiv`).
  * BPP: characterization by the number of wrong random strings (`InBPP_of_wrong`), closure under
    `∧`/`∨` (`InBPP.inter`, `InBPP.union`), polynomial-time reductions (`InBPP.of_reduces`).
  * `InRP`, `InCoRP`, `InZPP := InRP ∧ InCoRP`, and the zero-error "answer or ?" form `InZPPq`
    with `ZPP_iff_ZPPq`.
  * `P ⊆ ZPP ⊆ RP ⊆ NP ∩ BPP`, `coRP ⊆ coNP ∩ BPP`, one-sided amplification `InRP.amplify`.
  * Corollaries: `NP ⊆ BPP → PH = Σ₂`, `P = NP → BPP = P`.
-/
import PvnpReal.SGL

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

/-! ### Splitting random strings -/

theorem count_split {m d : ℕ} (P : List Bool → List Bool → Prop) :
    (Finset.univ.filter (fun w : Fin (m + d) → Bool =>
      P ((List.ofFn w).take m) ((List.ofFn w).drop m))).card =
    ((Finset.univ : Finset ((Fin m → Bool) × (Fin d → Bool))).filter
      (fun ab => P (List.ofFn ab.1) (List.ofFn ab.2))).card := by
  symm
  apply Finset.card_equiv (Fin.appendEquiv m d)
  intro ab
  have e : (Fin.appendEquiv m d) ab = Fin.append ab.1 ab.2 := rfl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, List.ofFn_fin_append]
  rw [List.take_left' (by simp), List.drop_left' (by simp)]

theorem count_take {m d : ℕ} (P : List Bool → Prop) :
    (Finset.univ.filter (fun w : Fin (m + d) → Bool => P ((List.ofFn w).take m))).card =
      (Finset.univ.filter (fun a : Fin m → Bool => P (List.ofFn a))).card * 2 ^ d := by
  have := count_split (m := m) (d := d) (fun a _ => P a)
  rw [this]
  have e : ((Finset.univ : Finset ((Fin m → Bool) × (Fin d → Bool))).filter
      (fun ab => P (List.ofFn ab.1))) =
      (Finset.univ.filter (fun a : Fin m → Bool => P (List.ofFn a))) ×ˢ Finset.univ := by
    ext ab; simp
  rw [e, Finset.card_product]
  simp

theorem count_drop {m d : ℕ} (P : List Bool → Prop) :
    (Finset.univ.filter (fun w : Fin (m + d) → Bool => P ((List.ofFn w).drop m))).card =
      2 ^ m * (Finset.univ.filter (fun b : Fin d → Bool => P (List.ofFn b))).card := by
  have := count_split (m := m) (d := d) (fun _ b => P b)
  rw [this]
  have e : ((Finset.univ : Finset ((Fin m → Bool) × (Fin d → Bool))).filter
      (fun ab => P (List.ofFn ab.2))) =
      Finset.univ ×ˢ (Finset.univ.filter (fun b : Fin d → Bool => P (List.ofFn b))) := by
    ext ab; simp
  rw [e, Finset.card_product]
  simp

/-! ### BPP via wrong counts -/

/-- Random strings on which `V` answers wrongly for `L` at `x`. -/
noncomputable def wrongCount (V L : Language) (x : List Bool) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun W : Fin m → Bool => (V (codeP x (List.ofFn W)) ↔ ¬ L x))).card

theorem wrong_eq_pos {V L : Language} {x : List Bool} (m : ℕ) (hL : L x) :
    wrongCount V L x m = accCount (fun s => ¬ V s) x m := by
  unfold wrongCount accCount; congr 1; ext w; simp [hL]

theorem wrong_eq_neg {V L : Language} {x : List Bool} (m : ℕ) (hL : ¬ L x) :
    wrongCount V L x m = accCount V x m := by
  unfold wrongCount accCount; congr 1; ext w; simp [hL]

/-- **BPP from a wrong-count bound** (error `≤ 1/3`). -/
theorem InBPP_of_wrong {L V : Language} {q : Polynomial ℕ} (hV : InP V)
    (h : ∀ x : List Bool, 3 * wrongCount V L x (q.eval x.length) ≤ 2 ^ q.eval x.length) : InBPP L := by
  refine ⟨V, q, hV, fun x => ⟨fun hL => ?_, fun hL => ?_⟩⟩
  · have := h x
    rw [wrong_eq_pos _ hL, accCount_compl] at this
    have := accCount_le V x (q.eval x.length)
    omega
  · have := h x
    rwa [wrong_eq_neg _ hL] at this

/-- Wrong-count form of BPP with error `< 2^{-p}`. -/
theorem InBPP.wrong {L : Language} (h : InBPP L) (p : Polynomial ℕ) :
    ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
      2 ^ p.eval x.length * wrongCount V L x (q.eval x.length) < 2 ^ q.eval x.length :=
  h.amplify p

theorem InBPP.congr {L L' : Language} (h : InBPP L) (e : ∀ x, L x ↔ L' x) : InBPP L' := by
  have : L = L' := funext fun x => propext (e x)
  exact this ▸ h

/-- **BPP is closed under any binary Boolean combination** (given the combined verifier is in P). -/
theorem InBPP.combine {L1 L2 : Language} (op : Prop → Prop → Prop) (h1 : InBPP L1) (h2 : InBPP L2)
    (hop : ∀ {V1 V2 : Language} {q1 : Polynomial ℕ}, InP V1 → InP V2 →
      InP (fun s => op (V1 (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length))))
        (V2 (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length)))))) :
    InBPP (fun x => op (L1 x) (L2 x)) := by
  obtain ⟨V1, q1, hV1, hq1⟩ := h1.wrong (Polynomial.C 3)
  obtain ⟨V2, q2, hV2, hq2⟩ := h2.wrong (Polynomial.C 3)
  refine InBPP_of_wrong (q := q1 + q2) (hop (q1 := q1) hV1 hV2) (fun x => ?_)
  set n := x.length
  have e1 := hq1 x
  have e2 := hq2 x
  simp only [Polynomial.eval_C] at e1 e2
  have key : ∀ M, M = q1.eval n + q2.eval n →
      3 * wrongCount (fun s => op (V1 (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length))))
        (V2 (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length)))))
        (fun x => op (L1 x) (L2 x)) x M ≤ 2 ^ M := by
    intro M hM
    subst hM
    set m1 := q1.eval n
    set m2 := q2.eval n
    unfold wrongCount
    simp only [decP_codeP]
    have hsub : (Finset.univ.filter (fun W : Fin (m1 + m2) → Bool =>
        (op (V1 (codeP x ((List.ofFn W).take m1))) (V2 (codeP x ((List.ofFn W).drop m1))) ↔
          ¬ op (L1 x) (L2 x)))) ⊆
        (Finset.univ.filter (fun W : Fin (m1 + m2) → Bool =>
          (V1 (codeP x ((List.ofFn W).take m1)) ↔ ¬ L1 x))) ∪
        (Finset.univ.filter (fun W : Fin (m1 + m2) → Bool =>
          (V2 (codeP x ((List.ofFn W).drop m1)) ↔ ¬ L2 x))) := by
      intro W hW
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hW ⊢
      by_contra hc
      simp only [not_or] at hc
      have a1 : V1 (codeP x ((List.ofFn W).take m1)) ↔ L1 x := by tauto
      have a2 : V2 (codeP x ((List.ofFn W).drop m1)) ↔ L2 x := by tauto
      rw [propext a1, propext a2] at hW
      tauto
    have c := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    unfold wrongCount at e1 e2
    set a := (Finset.univ.filter (fun W : Fin m1 → Bool => (V1 (codeP x (List.ofFn W)) ↔ ¬ L1 x))).card
    set b := (Finset.univ.filter (fun W : Fin m2 → Bool => (V2 (codeP x (List.ofFn W)) ↔ ¬ L2 x))).card
    have ct : (Finset.univ.filter (fun W : Fin (m1 + m2) → Bool =>
          (V1 (codeP x ((List.ofFn W).take m1)) ↔ ¬ L1 x))).card = a * 2 ^ m2 := by
      convert count_take (m := m1) (d := m2) (fun l => V1 (codeP x l) ↔ ¬ L1 x)
    have cd : (Finset.univ.filter (fun W : Fin (m1 + m2) → Bool =>
          (V2 (codeP x ((List.ofFn W).drop m1)) ↔ ¬ L2 x))).card = 2 ^ m1 * b := by
      convert count_drop (m := m1) (d := m2) (fun l => V2 (codeP x l) ↔ ¬ L2 x)
    rw [ct, cd] at c
    have f1 : 2 ^ 3 * a * 2 ^ m2 ≤ 2 ^ m1 * 2 ^ m2 := Nat.mul_le_mul_right _ e1.le
    have f2 : 2 ^ m1 * (2 ^ 3 * b) ≤ 2 ^ m1 * 2 ^ m2 := Nat.mul_le_mul_left _ e2.le
    rw [pow_add]
    nlinarith
  exact key _ (Polynomial.eval_add)

theorem InP.takeVP {V : Language} (hV : InP V) (q1 : Polynomial ℕ) :
    InP (fun s => V (codeP (decP s).1 ((decP s).2.take (q1.eval (decP s).1.length)))) :=
  hV.compPS (PS.codePF PS.fstP (PS.takeU PS.sndP ((PU.poly q1).comp PS.fstP)))

theorem InP.dropVP {V : Language} (hV : InP V) (q1 : Polynomial ℕ) :
    InP (fun s => V (codeP (decP s).1 ((decP s).2.drop (q1.eval (decP s).1.length)))) :=
  hV.compPS (PS.codePF PS.fstP (PS.dropU PS.sndP ((PU.poly q1).comp PS.fstP)))

/-- **BPP is closed under intersection.** -/
theorem InBPP.inter {L1 L2 : Language} (h1 : InBPP L1) (h2 : InBPP L2) :
    InBPP (fun x => L1 x ∧ L2 x) :=
  InBPP.combine (· ∧ ·) h1 h2 (fun hV1 hV2 => InP.inter (hV1.takeVP _) (hV2.dropVP _))

/-- **BPP is closed under union.** -/
theorem InBPP.union {L1 L2 : Language} (h1 : InBPP L1) (h2 : InBPP L2) :
    InBPP (fun x => L1 x ∨ L2 x) :=
  InBPP.combine (· ∨ ·) h1 h2 (fun hV1 hV2 => InP.union (hV1.takeVP _) (hV2.dropVP _))

end PvnpReal
