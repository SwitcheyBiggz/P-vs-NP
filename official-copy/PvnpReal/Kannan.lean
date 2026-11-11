/-
  PvnpReal.Kannan — **Kannan's theorem**: for every `k` there is a language in **Σ₂** that does
  not have circuits with `≤ n^k` gates (for infinitely many `n`).

  Proof (case split, as in the textbook):
  * if `NP ⊆ P/poly`, Karp–Lipton (`karpLipton`) collapses PH to Σ₂, so the Σ₄ language
    `KanL k` (`KannanSigma.lean`, hard for **all** large `n`) is in Σ₂;
  * otherwise some NP language `L` is not in P/poly (`InPpoly_iff_circ`); it is in Σ₁ ⊆ Σ₂, and a
    language outside P/poly cannot have `n^k`-gate circuits for all large `n`, because every
    `n`-bit function has *some* circuit (`hasCircuit_any`) and finitely many small lengths can be
    absorbed into a constant.
  Honest scope: the Σ₂ statement is "infinitely often" (as the second case only gives that);
  the Σ₄ statement `kannan_Sigma4` gives hardness for all large `n`.
-/
import PvnpReal.KannanSigma

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

/-- Every `n`-bit Boolean function has a circuit with `2 + 4·2ⁿ` gates (one fan-in-`n` node). -/
theorem hasCircuit_any (n : ℕ) (f : BFun n) : HasCircuit n (2 + 4 * 2 ^ n) f := by
  have h := hasCircuit_nval n n [(List.range n, fun bs => f (fun i => bs.getD i false))]
    (fun j hj d hd => by
      simp only [List.length_cons, List.length_nil] at hj
      obtain rfl : j = 0 := by omega
      simp at hd; omega)
    (fun nd hnd => by simp at hnd; subst hnd; simp) n (by simp)
  have e : (fun x : Fin n → Bool => (nval (List.ofFn x)
      [(List.range n, fun bs => f (fun i => bs.getD i false))]).getD n false) = f := by
    funext x
    simp only [nval, List.foldl_cons, List.foldl_nil, nStep_eq]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
    congr 1
    funext i
    rw [getD_range_map n _ i.2]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [e] at h
  simpa using h

/-- **Outside P/poly ⇒ infinitely often no `n^k` circuits**, for every `k`. -/
theorem io_hard_of_not_circ {L : Language} (h : ¬ InPpolyCirc L) (k : ℕ) :
    ∀ N, ∃ n ≥ N, ¬ HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  intro N
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  apply h
  refine ⟨Polynomial.X ^ k + Polynomial.C (2 + 4 * 2 ^ N), fun n => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  by_cases hn : N ≤ n
  · exact (hc n hn).mono (by omega)
  · refine (hasCircuit_any n _).mono ?_
    have : 2 ^ n ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **Kannan's theorem (Σ₂ form)**: for every `k` there is a language in Σ₂ without circuits of
size `n^k` for infinitely many input lengths `n`. -/
theorem kannan (k : ℕ) : ∃ L, InSigma 2 L ∧
    ∀ N, ∃ n ≥ N, ¬ HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  by_cases H : NP_subset_Ppoly
  · refine ⟨KanL k, (karpLipton H _).1 (KanL_PH k), fun N => ?_⟩
    obtain ⟨N0, hN0⟩ := KanL_hard k
    exact ⟨max N N0, le_max_left _ _, by convert hN0 (max N N0) (le_max_right _ _)⟩
  · simp only [NP_subset_Ppoly, not_forall] at H
    obtain ⟨L, hL, hnot⟩ := H
    exact ⟨L, ((Sigma1_iff_NP L).2 hL).mono (by norm_num),
      io_hard_of_not_circ (fun hc => hnot ((InPpoly_iff_circ L).2 hc)) k⟩

/-- Equivalently: **Σ₂ is not contained in `SIZE(n^k)`** (no `n^k`-gate circuits for all large `n`). -/
theorem Sigma2_not_subset_SIZE (k : ℕ) : ¬ ∀ L, InSigma 2 L →
    ∃ N, ∀ n ≥ N, HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  intro h
  obtain ⟨L, hL, hio⟩ := kannan k
  obtain ⟨N, hN⟩ := h L hL
  obtain ⟨n, hn, hnc⟩ := hio N
  exact hnc (hN n hn)

/-- **PH is not in `SIZE(n^k)`** for any fixed `k`, with hardness at *all* large lengths. -/
theorem PH_not_subset_SIZE (k : ℕ) : ∃ L, InPH L ∧ ∃ N, ∀ n ≥ N,
    ¬ HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (L (List.ofFn x))) := by
  obtain ⟨N, hN⟩ := KanL_hard k
  exact ⟨KanL k, KanL_PH k, N, fun n hn => by convert hN n hn⟩

end PvnpReal
