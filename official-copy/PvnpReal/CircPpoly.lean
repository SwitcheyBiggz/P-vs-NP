/-
  PvnpReal.CircPpoly — **`InPpoly L → InPpolyCirc L`**: a polynomial-time `FinTM2` with polynomial
  advice is simulated, for each input length `n`, by the tableau circuit of `CircTab.lean`
  (input bits enter row 0 directly; the advice and the unary length prefix are hard-wired as
  constants). Hence `InPpoly ↔ InPpolyCirc`, `P ⊆ P/poly` in circuit form, and the two
  Karp–Lipton hypotheses agree.
-/
import PvnpReal.CircTab
import PvnpReal.PSubsetNP

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

section Sim

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {V : List Bool × List Bool → Bool} (h : TM2ComputableInPolyTime pairEnc encodeBool V)

/-- The machine input for circuit input `x`: `1^n 0 x a`. -/
def czOf (n : ℕ) (a : List Bool) (x : Fin n → Bool) : List Bool :=
  List.replicate n true ++ false :: (List.ofFn x ++ a)

noncomputable def cstOf (n : ℕ) (a : List Bool) (x : Fin n → Bool) : List (h.tm.Γ h.tm.k₀) :=
  (czOf n a x).map (c2sb h) ++ [c2sep h]

noncomputable def crunOf (n : ℕ) (a : List Bool) (x : Fin n → Bool) (t : ℕ) :
    TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ :=
  (stepStay h.tm.m)^[t] (initCfg h.tm.main h.tm.initialState h.tm.k₀ (cstOf h n a x))

theorem zOf_length (n : ℕ) (a : List Bool) (x : Fin n → Bool) :
    (czOf n a x).length = 2 * n + 1 + a.length := by
  simp [czOf]; omega

theorem stOf_eq (n : ℕ) (a : List Bool) (x : Fin n → Bool) :
    cstOf h n a x = clPre h (czOf n a x) ++ ([] : List Bool).map (h.inputAlphabet.invFun ∘ some) := by
  have := c2_init h (czOf n a x) []
  simpa [cstOf] using this

theorem zOf_get_const (n : ℕ) (a : List Bool) (x x' : Fin n → Bool) (p : ℕ)
    (hp : p < n + 1 ∨ 2 * n + 1 ≤ p) : (czOf n a x)[p]? = (czOf n a x')[p]? := by
  have e : ∀ y : Fin n → Bool, czOf n a y = (List.replicate n true ++ [false]) ++ (List.ofFn y ++ a) := by
    intro y; simp [czOf]
  rw [e, e]
  rcases hp with hp | hp
  · have hA : p < (List.replicate n true ++ [false]).length := by simp; omega
    rw [List.getElem?_append_left hA, List.getElem?_append_left hA]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp

theorem zOf_get_inp (n : ℕ) (a : List Bool) (x : Fin n → Bool) (p : ℕ) (h1 : n + 1 ≤ p)
    (h2 : p < 2 * n + 1) : (czOf n a x)[p]? = some ((List.ofFn x).getD (p - n - 1) false) := by
  have e : czOf n a x = (List.replicate n true ++ [false]) ++ (List.ofFn x ++ a) := by simp [czOf]
  rw [e, List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  rw [show p - (n + 1) = p - n - 1 by omega, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp; omega)]
  rfl

theorem stOf_get (n : ℕ) (a : List Bool) (x : Fin n → Bool) (p : ℕ) :
    (cstOf h n a x)[p]? = if p < (czOf n a x).length then ((czOf n a x)[p]?).map (c2sb h)
      else if p = (czOf n a x).length then some (c2sep h) else none := by
  unfold cstOf
  split_ifs with h1 h2
  · rw [List.getElem?_append_left (by simpa using h1), List.getElem?_map]
  · rw [List.getElem?_append_right (by simp; omega)]; simp [h2]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp; omega

theorem runOf_cell0 (n : ℕ) (a : List Bool) (x : Fin n → Bool) (k : h.tm.K) (p : ℕ) :
    cellOf (crunOf h n a x 0) k p =
      if hk : k = h.tm.k₀ then (((cstOf h n a x)[p]?).map (fun g => (⟨h.tm.k₀, g⟩ : Sig h.tm.Γ)))
      else none := by
  unfold crunOf cellOf
  simp only [Function.iterate_zero, id, initCfg]
  split_ifs with hk
  · subst hk; simp
  · simp [Function.update_of_ne hk]

theorem runOf_cell0_const (n : ℕ) (a : List Bool) (x x' : Fin n → Bool) (k : h.tm.K) (p : ℕ)
    (hp : ¬ (k = h.tm.k₀ ∧ n + 1 ≤ p ∧ p < 2 * n + 1)) :
    cellOf (crunOf h n a x 0) k p = cellOf (crunOf h n a x' 0) k p := by
  rw [runOf_cell0, runOf_cell0]
  split_ifs with hk
  · have hp' : p < n + 1 ∨ 2 * n + 1 ≤ p := by
      by_contra hc; exact hp ⟨hk, by omega, by omega⟩
    rw [stOf_get, stOf_get, zOf_length, zOf_length, zOf_get_const n a x x' p hp']
  · rfl

theorem runOf_cell0_inp (n : ℕ) (a : List Bool) (x : Fin n → Bool) (p : ℕ) (h1 : n + 1 ≤ p)
    (h2 : p < 2 * n + 1) :
    cellOf (crunOf h n a x 0) h.tm.k₀ p =
      some ⟨h.tm.k₀, c2sb h ((List.ofFn x).getD (p - n - 1) false)⟩ := by
  rw [runOf_cell0, dif_pos rfl, stOf_get, if_pos (by rw [zOf_length]; omega),
    zOf_get_inp n a x p h1 h2]
  rfl

theorem clT_len' (q : Polynomial ℕ) {x y : List Bool} (e : x.length = y.length) :
    clT q h x = clT q h y := by
  simp [clT, clN, e]

theorem c2S_len' (q : Polynomial ℕ) {x y : List Bool} (e : x.length = y.length) :
    c2S q h x = c2S q h y := by
  simp [c2S, clT, clN, e]

/-- Row-0 nodes: input bits for the `x` region of the input stack, constants elsewhere. -/
noncomputable def cinit0Of (n : ℕ) (a : List Bool) (i p : ℕ) : ANode (V2 h.tm.Γ h.tm.Λ h.tm.σ) :=
  match (clKs h.tm)[i]? with
  | some k =>
    if k = h.tm.k₀ ∧ n + 1 ≤ p ∧ p < 2 * n + 1 then
      .inp (p - n - 1) (fun b => Sum.inr (some ⟨h.tm.k₀, c2sb h b⟩))
    else .fn [] (fun _ => Sum.inr (cellOf (crunOf h n a (fun _ => false) 0) k p))
  | none => .fn [] (fun _ => Sum.inr none)

noncomputable def simU : ℕ := (tab2Values (Λ := h.tm.Λ) (σ := h.tm.σ) (clD h.tm) (clL h.tm)).length

noncomputable def simC : ℕ := 2 * clD h.tm + pushTotal h.tm + 2 + (clKs h.tm).length * clD h.tm

/-- The gate bound for length `n` and advice length `la`. -/
noncomputable def simBound (n la : ℕ) : ℕ :=
  2 + ((clT 0 h (List.replicate (2 * n + 1 + la) false) + 1) *
      Wc (clKs h.tm) (c2S 0 h (List.replicate (2 * n + 1 + la) false)) * simU h + 1) *
    (4 * 2 ^ (simC h * simU h))

theorem cacc_iff (b : Bool) :
    (some ⟨h.tm.k₁, h.outputAlphabet.invFun b⟩ : Option (Sig h.tm.Γ)) = some ⟨h.tm.k₁, c2acc h⟩ ↔
      b = true := by
  constructor
  · intro e
    have e' := eq_of_heq (Sigma.mk.inj_iff.1 (Option.some.inj e)).2
    exact h.outputAlphabet.symm.injective e'
  · rintro rfl; rfl

/-- **The verifier, on inputs `1^n 0 x a`, is a polynomial-size circuit family in `x`.** -/
theorem hasCircuit_verifier (n : ℕ) (a : List Bool) :
    HasCircuit n (simBound h n a.length) (fun x => decide (V (czOf n a x, []) = true)) := by
  set z0 := List.replicate (2 * n + 1 + a.length) false with hz0
  have hzl : ∀ x, (czOf n a x).length = z0.length := fun x => by rw [zOf_length]; simp [hz0]
  set S := c2S 0 h z0 with hS
  set T := clT 0 h z0 with hT
  have hdS : clD h.tm ≤ S := by rw [hS]; unfold c2S; omega
  have hS0 : 0 < S := by rw [hS]; unfold c2S; omega
  have hC := hasCircuit_tab h.tm.m (clD h.tm) (pushTotal h.tm) S T n (clKs h.tm)
    (clD_spec h) (pushes_le_total h.tm) (clKs_spec h) hdS (clL h.tm) (cinit0Of h n a)
    (some h.tm.main) h.tm.initialState (crunOf h n a)
    (fun x t => by unfold crunOf; rw [Function.iterate_succ_apply'])
    (fun x t ht k => by
      have := c2_len 0 h (czOf n a x) [] (by simp) t (by rw [clT_len' h 0 (hzl x)]; exact ht) k
      have h2 : ((crunOf h n a x t).stk k).length ≤ c2S 0 h (czOf n a x) - (clD h.tm + 1) := this
      rw [c2S_len' h 0 (hzl x)] at h2
      omega)
    (fun x t => by
      unfold crunOf; rw [stOf_eq]
      exact run_syms h _ (init_syms h _ _) t)
    (fun x => rfl) (fun x => rfl)
    (fun i hi p hp => by
      unfold cinit0Of
      rw [List.getElem?_eq_getElem hi]
      by_cases hc : (clKs h.tm)[i] = h.tm.k₀ ∧ n + 1 ≤ p ∧ p < 2 * n + 1
      · left
        refine ⟨p - n - 1, (fun b => Sum.inr (some ⟨h.tm.k₀, c2sb h b⟩)), by omega,
          by simp only [if_pos hc], fun x => ?_⟩
        rw [hc.1, runOf_cell0_inp h n a x p hc.2.1 hc.2.2]
      · right
        refine ⟨(fun _ => Sum.inr (cellOf (crunOf h n a (fun _ => false) 0) (clKs h.tm)[i] p)),
          by simp only [if_neg hc], fun x => ?_⟩
        rw [runOf_cell0_const h n a x _ _ _ hc])
    h.tm.k₁ 0 hS0 (fun c => c = some ⟨h.tm.k₁, c2acc h⟩)
  have key : ∀ x, decide (V (czOf n a x, []) = true) =
      decide (cellOf (crunOf h n a x T) h.tm.k₁ 0 = some ⟨h.tm.k₁, c2acc h⟩) := by
    intro x
    have hrun : crunOf h n a x T = haltList h.tm ((encodeBool (V (czOf n a x, []))).map
        h.outputAlphabet.invFun) := by
      unfold crunOf
      rw [stOf_eq, hT, ← clT_len' h 0 (hzl x)]
      exact verifier_stay 0 h (czOf n a x) [] (by simp)
    rw [hrun, c2_acc_cell]
    exact decide_eq_decide.2 (cacc_iff h _).symm
  convert hC using 1
  · rfl
  · funext x
    rw [key x]
    exact decide_eq_decide.2 Iff.rfl

/-- The polynomial gate bound for advice-length polynomial `qa`. -/
noncomputable def simPoly (qa : Polynomial ℕ) : Polynomial ℕ :=
  let Np : Polynomial ℕ := Polynomial.C 2 * Polynomial.X + Polynomial.C 2 + qa
  let Tp : Polynomial ℕ := h.time.comp Np
  let Sp : Polynomial ℕ := Np + Polynomial.C (pushTotal h.tm) * Tp +
    Polynomial.C (2 * clD h.tm + pushTotal h.tm + 2)
  Polynomial.C 2 + ((Tp + 1) * (Polynomial.C (clKs h.tm).length * Sp + 1) * Polynomial.C (simU h) + 1) *
    Polynomial.C (4 * 2 ^ (simC h * simU h))

theorem simPoly_eval (qa : Polynomial ℕ) (n : ℕ) :
    (simPoly h qa).eval n = simBound h n (qa.eval n) := by
  set z := List.replicate (2 * n + 1 + qa.eval n) false
  have hN : clN 0 z = 2 * n + 2 + qa.eval n := by simp [clN, z]; omega
  have hT : clT 0 h z = h.time.eval (2 * n + 2 + qa.eval n) := by rw [clT, hN]
  have hS : c2S 0 h z = (2 * n + 2 + qa.eval n) + pushTotal h.tm * h.time.eval (2 * n + 2 + qa.eval n)
      + (2 * clD h.tm + pushTotal h.tm + 2) := by
    unfold c2S; rw [hN, hT]; ring
  unfold simBound simPoly Wc
  rw [hT, hS]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_comp]

end Sim

/-! ### The equivalence -/

/-- **Direction →: P with polynomial advice ⇒ polynomial-size circuits.** -/
theorem InPpolyCirc_of_InPpoly {L : Language} (hL : InPpoly L) : InPpolyCirc L := by
  obtain ⟨A, qa, adv, hA, hadv, hLA⟩ := hL
  have hB : InP (fun z => A (codeP ((lpX z).take (lpN z)) ((lpX z).drop (lpN z)))) :=
    InP.compPS hA (PS.codePF (PS.takeU PS.drop PU.fst) (PS.dropU PS.drop PU.fst))
  obtain ⟨f, ⟨hf⟩, hBf⟩ := hB
  refine ⟨simPoly (verifierComputable hf) qa, fun n => ?_⟩
  have hc := hasCircuit_verifier (verifierComputable hf) n (adv n)
  rw [hadv n, ← simPoly_eval] at hc
  convert hc using 1
  funext x
  apply decide_eq_decide.2
  show L (List.ofFn x) ↔ f (czOf n (adv n) x) = true
  rw [← hBf, czOf]
  show L (List.ofFn x) ↔ A (codeP ((lpX (List.replicate n true ++ false :: (List.ofFn x ++ adv n))).take
    (lpN (List.replicate n true ++ false :: (List.ofFn x ++ adv n))))
    ((lpX (List.replicate n true ++ false :: (List.ofFn x ++ adv n))).drop
    (lpN (List.replicate n true ++ false :: (List.ofFn x ++ adv n)))))
  rw [lpN_rep, lpX_rep, List.take_left' (by simp), List.drop_left' (by simp), hLA,
    List.length_ofFn]

/-- **P/poly: the advice definition and the circuit definition agree.** -/
theorem InPpoly_iff_circ (L : Language) : InPpoly L ↔ InPpolyCirc L :=
  ⟨InPpolyCirc_of_InPpoly, InPpoly_of_circ⟩

/-- **P ⊆ P/poly** (circuit form). -/
theorem P_subset_PpolyCirc (L : Language) (h : InP L) : InPpolyCirc L :=
  InPpolyCirc_of_InPpoly (P_subset_Ppoly L h)

/-- The two Karp–Lipton hypotheses coincide. -/
theorem NP_subset_Ppoly_iff_circ : NP_subset_Ppoly ↔ ∀ L, InNP L → InPpolyCirc L :=
  ⟨fun H L hL => InPpolyCirc_of_InPpoly (H L hL), fun H L hL => InPpoly_of_circ (H L hL)⟩

/-- **Karp–Lipton, both forms**: each of `NP ⊆ P/poly` (advice) and `NP ⊆ P/poly` (circuits)
collapses PH to `Σ₂`, and the hypotheses are equivalent. -/
theorem karpLipton_iff_forms :
    (NP_subset_Ppoly ↔ ∀ L, InNP L → InPpolyCirc L) ∧
      (NP_subset_Ppoly → ∀ L, InPH L ↔ InSigma 2 L) ∧
      ((∀ L, InNP L → InPpolyCirc L) → ∀ L, InPH L ↔ InSigma 2 L) :=
  ⟨NP_subset_Ppoly_iff_circ, karpLipton, karpLipton_circ⟩

end PvnpReal
