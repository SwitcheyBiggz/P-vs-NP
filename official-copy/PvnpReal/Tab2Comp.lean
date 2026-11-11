/-
  PvnpReal.Tab2Comp — completeness of the second tableau: an accepting run gives a solution.
-/
import PvnpReal.Tab2Sound

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

open scoped Classical

section Comp

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (S T : ℕ) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool)

/-- The assignment read off a run. -/
def assign2 (run : ℕ → Cfg Γ Λ σ) (v : ℕ) : V2 Γ Λ σ :=
  if v = 0 then Sum.inr (some ⟨k₀, sb false⟩) else
  if v = 1 then Sum.inr (some ⟨k₀, sb true⟩) else
  if (v - 2) % W2 Ks S = 0 then Sum.inl (ctlOf d (run ((v - 2) / W2 Ks S))) else
  match Ks[((v - 2) % W2 Ks S - 1) / S]? with
  | some k => Sum.inr (cellOf (run ((v - 2) / W2 Ks S)) k (((v - 2) % W2 Ks S - 1) % S))
  | none => Sum.inr none

variable {d Ks S k₀ sb}

theorem assign2_sv (run : ℕ → Cfg Γ Λ σ) (t : ℕ) :
    assign2 d Ks S k₀ sb run (sv2 Ks S t) = Sum.inl (ctlOf d (run t)) := by
  have hW : 0 < W2 Ks S := by unfold W2; omega
  unfold assign2 sv2
  rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left, Nat.mul_mod_left,
    if_pos rfl, Nat.mul_div_cancel _ hW]

theorem assign2_cv (run : ℕ → Cfg Γ Λ σ) (t : ℕ) {k : K} (hk : k ∈ Ks) {p : ℕ} (hp : p < S) :
    assign2 d Ks S k₀ sb run (cv2 Ks S t k p) = Sum.inr (cellOf (run t) k p) := by
  have hi := List.idxOf_lt_length_of_mem hk
  have hr : 1 + Ks.idxOf k * S + p < W2 Ks S := by
    unfold W2
    have : (Ks.idxOf k + 1) * S ≤ Ks.length * S := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul] at this; omega
  have e : cv2 Ks S t k p - 2 = (1 + Ks.idxOf k * S + p) + W2 Ks S * t := by
    unfold cv2; rw [Nat.mul_comm]; omega
  unfold assign2
  rw [if_neg (by unfold cv2; omega), if_neg (by unfold cv2; omega), e, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hr, if_neg (by omega), Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt hr, Nat.zero_add]
  have e2 : 1 + Ks.idxOf k * S + p - 1 = p + S * Ks.idxOf k := by rw [Nat.mul_comm]; omega
  rw [e2, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hp, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp, List.getElem?_idxOf hk]

theorem win_link (c : Cfg Γ Λ σ) (k : K) {i : ℕ} (hi : i < d) :
    ((ctlOf d c).win k)[i]? = cellOf c k i := by
  simp [ctlOf, cellOf, toSig, List.getElem?_take, hi]

variable {m P T k₁ main v₀ sep Q gacc xs}

local notation "CS" => tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs

/-- **Completeness of the second tableau.** -/
theorem tab2_complete (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S)
    (w : List Bool) (hw : w.length ≤ Q)
    (hlen : ∀ t ≤ T, ∀ k,
      (((stepStay m)^[t] (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb))).stk k).length ≤
        S - (d + 1))
    (hacc : cellOf ((stepStay m)^[T] (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb))) k₁ 0 =
        some ⟨k₁, gacc⟩)
    (U : List (V2 Γ Λ σ))
    (hU : ∀ v, assign2 d Ks S k₀ sb
      (fun t => (stepStay m)^[t] (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb))) v ∈ U) :
    CSPSat U CS := by
  set c0 := initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb) with hc0
  set run : ℕ → Cfg Γ Λ σ := fun t => (stepStay m)^[t] c0 with hrun
  refine ⟨assign2 d Ks S k₀ sb run, hU, ?_⟩
  have hst : c0.stk k₀ = xs.map sb ++ sep :: w.map sb := by simp [hc0, initCfg]
  have hst' : ∀ k, k ≠ k₀ → c0.stk k = [] := fun k hk => by simp [hc0, initCfg, hk]
  have hrun0 : run 0 = c0 := rfl
  have hrunS : ∀ t, run (t + 1) = stepStay m (run t) := fun t => by
    simp only [hrun]; rw [Function.iterate_succ_apply']
  have a0 : assign2 d Ks S k₀ sb run 0 = Sum.inr (some ⟨k₀, sb false⟩) := by simp [assign2]
  have a1 : assign2 d Ks S k₀ sb run 1 = Sum.inr (some ⟨k₀, sb true⟩) := by simp [assign2]
  intro c hc
  simp only [tab2CS, csZ, csInit, csRow, csTrans, csFinal, List.mem_append, List.mem_cons,
    List.mem_singleton, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_filter,
    List.not_mem_nil, or_false] at hc
  rcases hc with (((((rfl | rfl) | ((((((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) |
    ⟨j, hj, rfl⟩) | ⟨k, ⟨-, hk⟩, p, hp, rfl⟩))) | ⟨t, ht, k, -, (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)⟩) |
    ⟨t, ht, rfl | ⟨k, -, (⟨p, hp, rfl⟩ | ⟨j, hj, rfl⟩)⟩⟩) | rfl)
  · simp [cellRel1, a0]
  · simp [cellRel1, a1]
  · simp only [List.map_cons, List.map_nil, assign2_sv, ctlRel1, ctlOf, hrun0]
    simp [hc0, initCfg]
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show i < S by omega)]
    have hb : NthTM.bit xs i = if xs[i] then 1 else 0 := by
      simp [NthTM.bit, List.getElem?_eq_getElem hi]
    rw [hb]
    cases hx : xs[i]
    · simp only [if_neg (show ¬(false = true) by simp), a0, cellRel2, hrun0, cellOf, hst,
        List.getElem?_append_left (show i < (xs.map sb).length by simpa),
        List.getElem?_map, List.getElem?_eq_getElem hi, hx]
      simp [a0, a1]
    · simp only [if_pos rfl, a1, cellRel2, hrun0, cellOf, hst,
        List.getElem?_append_left (show i < (xs.map sb).length by simpa),
        List.getElem?_map, List.getElem?_eq_getElem hi, hx]
      simp [a0, a1]
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show xs.length < S by omega),
      cellRel1, hrun0, cellOf, hst, List.getElem?_append_right (show (xs.map sb).length ≤ xs.length
        by simp)]
    simp
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show xs.length + 1 + j < S by omega),
      assign2_cv run 0 (hKs k₀) (show xs.length + 2 + j < S by omega), cellRel2, hrun0, cellOf, hst,
      List.getElem?_append_right (show (xs.map sb).length ≤ xs.length + 1 + j by simp; omega),
      List.getElem?_append_right (show (xs.map sb).length ≤ xs.length + 2 + j by simp; omega),
      List.length_map, show xs.length + 1 + j - xs.length = j + 1 by omega,
      show xs.length + 2 + j - xs.length = j + 1 + 1 by omega, List.getElem?_cons_succ,
      decide_eq_true_eq]
    unfold witP
    constructor
    · rcases h : (w.map sb)[j]? with _ | g
      · simp
      · right
        simp only [List.getElem?_map] at h
        obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨b, rfl⟩
    · intro h
      simp only [Option.map_eq_none_iff, List.getElem?_eq_none_iff, List.length_map] at h ⊢
      omega
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k₀) (show xs.length + 1 + Q + j < S by omega),
      cellRel1, hrun0, cellOf, hst, decide_eq_true_eq, Option.map_eq_none_iff, List.getElem?_eq_none_iff]
    simp; omega
  · simp only [List.map_cons, List.map_nil, assign2_cv run 0 (hKs k) hp, cellRel1, hrun0, cellOf,
      hst' k (of_decide_eq_true hk)]
    simp
  · simp only [List.map_cons, List.map_nil, assign2_sv, assign2_cv run t (hKs k) (show i < S by omega),
      linkRel, win_link _ k hi]
    simp
  · simp only [List.map_cons, List.map_nil,
      assign2_cv run t (hKs k) (show S - (d + 1) + j < S by omega), cellRel1, cellOf,
      decide_eq_true_eq, Option.map_eq_none_iff, List.getElem?_eq_none_iff]
    exact le_trans (hlen t (by omega) k) (by omega)
  · simp only [List.map_cons, List.map_nil, assign2_sv, ctlRel2, decide_eq_true_eq,
      transCP_iff m d hd, hrunS]
    exact ⟨rfl, rfl⟩
  · simp only [List.map_cons, List.map_map, assign2_sv, assign2_cv run (t + 1) (hKs k)
      (show p < S by omega)]
    have eo : List.map (assign2 d Ks S k₀ sb run ∘ fun i => cv2 Ks S t k i) (List.range (p + d + 1)) =
        (List.range (p + d + 1)).map (fun i => Sum.inr (cellOf (run t) k (p - p + i))) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [Function.comp, Nat.sub_self, Nat.zero_add]
      exact assign2_cv run t (hKs k) (by omega)
    rw [eo]
    simp only [tcRel, decide_eq_true_eq]
    rw [tcP_iff m d P hd hP _ k p p p le_rfl (Or.inl ⟨rfl, rfl⟩), hrunS]
  · simp only [List.map_cons, List.map_map, assign2_sv, assign2_cv run (t + 1) (hKs k)
      (show d + P + j < S by omega)]
    have eo : List.map (assign2 d Ks S k₀ sb run ∘ fun i => cv2 Ks S t k (d + j + i))
        (List.range (P + d + 1)) =
        (List.range (P + d + 1)).map (fun i => Sum.inr (cellOf (run t) k (d + P + j - P + i))) := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [Function.comp]
      rw [show d + P + j - P + i = d + j + i by omega]
      exact assign2_cv run t (hKs k) (by omega)
    rw [eo]
    simp only [tcRel, decide_eq_true_eq]
    rw [tcP_iff m d P hd hP _ k (d + P + j) P (d + P) (by omega) (Or.inr ⟨rfl, by omega, rfl⟩),
      hrunS]
  · simp only [List.map_cons, List.map_nil, assign2_cv run T (hKs k₁) (show 0 < S by omega),
      cellRel1, decide_eq_true_eq]
    exact hacc

end Comp

end PvnpReal
