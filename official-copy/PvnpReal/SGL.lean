/-
  PvnpReal.SGL — **Sipser–Gács–Lautemann: BPP ⊆ Σ₂** (Lautemann's shifting proof).

  Amplify to error `< 2^{-p}` with `p = q + 10` (random length `Q`, and `Q + 1 ≤ 2^p`). With
  `k = Q + 1` shifts `S_0 … S_{k-1} ∈ {0,1}^Q`:
  * `x ∈ L`: some shift vector covers every `r`, i.e. `∀ r ∃ i, V'(x, r ⊕ S_i)`
    (`sgl_yes`: the number of bad shift vectors is `≤ 2^Q · |W|^k < 2^{Qk}`);
  * `x ∉ L`: for every shift vector some `r` is uncovered (`sgl_no`: `k · |A| < 2^Q`).
  The inner `∃ i < k` is checked in polynomial time (`InP.sglRP`), so `L ∈ Σ₂`
  (`BPP_subset_Sigma2`); with complement closure also `BPP ⊆ Π₂` (`BPP_subset_Pi2`).
-/
import PvnpReal.BPPAmp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

/-! ### Combinatorics of shifts -/

/-- Bitwise XOR of two random strings. -/
def xorF {Q : ℕ} (r s : Fin Q → Bool) : Fin Q → Bool := fun j => xor (r j) (s j)

theorem xorF_xorF {Q : ℕ} (r s : Fin Q → Bool) : xorF (xorF r s) s = r := by
  funext j; simp [xorF]

theorem xorF_inj {Q : ℕ} (r : Fin Q → Bool) : Function.Injective (fun s => xorF r s) := by
  intro s s' e
  funext j
  have := congrFun e j
  simpa [xorF] using this

/-- **Yes case**: if few strings are bad, some `k` shifts cover every `r`. -/
theorem sgl_yes {Q k p : ℕ} (W : Finset (Fin Q → Bool)) (hk : 1 ≤ k) (hW : 2 ^ p * W.card < 2 ^ Q)
    (hQ : Q ≤ p * k) : ∃ S : Fin k → Fin Q → Bool, ∀ r, ∃ i, xorF r (S i) ∉ W := by
  by_contra hne
  simp only [not_exists, not_forall, not_not] at hne
  have hsub : (Finset.univ : Finset (Fin k → Fin Q → Bool)) ⊆
      Finset.univ.biUnion (fun r : Fin Q → Bool =>
        Fintype.piFinset (fun _ : Fin k => W.image (fun w => xorF r w))) := by
    intro S _
    obtain ⟨r, hr⟩ := hne S
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_image]
    exact ⟨r, fun i => ⟨xorF r (S i), hr i, by funext j; simp [xorF]⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcard : ∀ r : Fin Q → Bool, (Fintype.piFinset (fun _ : Fin k =>
      W.image (fun w => xorF r w))).card = W.card ^ k := fun r => by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ (xorF_inj r)]
  simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, smul_eq_mul] at h1
  rw [← pow_mul] at h1
  have h2 : (2 ^ p * W.card) ^ k < (2 ^ Q) ^ k := Nat.pow_lt_pow_left hW (by omega)
  rw [mul_pow, ← pow_mul, ← pow_mul] at h2
  have h3 : 2 ^ Q ≤ 2 ^ (p * k) := Nat.pow_le_pow_right (by norm_num) hQ
  have h4 : 2 ^ Q * W.card ^ k ≤ 2 ^ (p * k) * W.card ^ k := Nat.mul_le_mul_right _ h3
  linarith

/-- **No case**: if few strings are accepted, `k ≤ 2^p` shifts never cover everything. -/
theorem sgl_no {Q k p : ℕ} (A : Finset (Fin Q → Bool)) (hk : k ≤ 2 ^ p) (hA : 2 ^ p * A.card < 2 ^ Q)
    (S : Fin k → Fin Q → Bool) : ∃ r, ∀ i, xorF r (S i) ∉ A := by
  set U := Finset.univ.biUnion (fun i : Fin k => A.image (fun a => xorF a (S i)))
  have h1 : U.card ≤ k * A.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ i : Fin k, (A.image (fun a => xorF a (S i))).card ≤ ∑ _i : Fin k, A.card :=
          Finset.sum_le_sum (fun i _ => Finset.card_image_le)
      _ = k * A.card := by simp
  have h2 : k * A.card ≤ 2 ^ p * A.card := Nat.mul_le_mul_right _ hk
  have hne : U ≠ Finset.univ := by
    intro e
    have : U.card = 2 ^ Q := by rw [e]; simp
    omega
  obtain ⟨r, hr⟩ : ∃ r, r ∉ U := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hne (Finset.eq_univ_iff_forall.2 hc)
  refine ⟨r, fun i hi => hr ?_⟩
  simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  exact ⟨i, _, hi, xorF_xorF r (S i)⟩

theorem shift_bound (a : ℕ) : 2 * (6 * (a + 10 + 1)) * a + 1 ≤ 2 ^ (a + 10) := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [show a + 1 + 10 = (a + 10) + 1 by ring, pow_succ]
    rcases Nat.lt_or_ge a 2 with h | h
    · obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
      all_goals norm_num
    · generalize 2 ^ (a + 10) = P at ih ⊢
      nlinarith

/-! ### The Σ₂ matrix -/

/-- XOR of the first `Q` bits. -/
def xorL (a b : List Bool) (Q : ℕ) : List Bool :=
  (List.range Q).flatMap (fun j => [xor (a.getD j false) (b.getD j false)])

theorem bit_eq_ite (A : List Bool) (j : ℕ) : NthTM.bit A j = if A.getD j false then 1 else 0 := by
  have := bit_eq_one_iff A j
  unfold NthTM.bit at this ⊢
  split_ifs at this ⊢ <;> simp_all

theorem PS.xorLP {A B : List Bool → List Bool} {N : List Bool → ℕ} (hA : PS A) (hB : PS B)
    (hN : PU N) : PS (fun s => xorL (A s) (B s) (N s)) := by
  have hb : PS (fun z => (fun j s => [xor ((A s).getD j false) ((B s).getD j false)]) (lpN z) (lpX z)) :=
    (PS.boolOf (PU.sub (PU.const 1) (PU.indEq (PU.bitP (PS.comp PS.drop hA) PU.fst)
      (PU.bitP (PS.comp PS.drop hB) PU.fst)))).congr (fun z => by
        simp only [bit_eq_ite]
        cases (A (lpX z)).getD (lpN z) false <;> cases (B (lpX z)).getD (lpN z) false <;> simp)
  exact PS.flatRange hN (fun j s => [xor ((A s).getD j false) ((B s).getD j false)]) hb

/-- The Σ₂ matrix on `codeP x (S ++ r)`: some shift `S_i` (`i ≤ Q`) has `V(x, r ⊕ S_i)`. -/
noncomputable def sglR (V : Language) (Qp : Polynomial ℕ) : Language := fun s =>
  1 ≤ ((List.range (Qp.eval (decP s).1.length + 1)).flatMap (fun i =>
    if V (codeP (decP s).1 (xorL (subL (decP s).2 ((Qp.eval (decP s).1.length + 1) *
        Qp.eval (decP s).1.length) (Qp.eval (decP s).1.length))
      (subL (decP s).2 (i * Qp.eval (decP s).1.length) (Qp.eval (decP s).1.length))
      (Qp.eval (decP s).1.length))) then [true] else [])).length

theorem InP.sglRP {V : Language} (hV : InP V) (Qp : Polynomial ℕ) : InP (sglR V Qp) := by
  have X' : PS (fun z => (decP (lpX z)).1) := PS.comp PS.drop PS.fstP
  have U' : PS (fun z => (decP (lpX z)).2) := PS.comp PS.drop PS.sndP
  have Q' : PU (fun z => Qp.eval (decP (lpX z)).1.length) := (PU.poly Qp).comp X'
  have rr := PS.subL U' (PU.mul (Q'.add (PU.const 1)) Q') Q'
  have ss := PS.subL U' (PU.mul PU.fst Q') Q'
  have hb0 := PS.ofInP (hV.compPS (PS.codePF X' (PS.xorLP rr ss Q')))
  have hb : PS (fun z => (fun i s => if V (codeP (decP s).1 (xorL (subL (decP s).2
        ((Qp.eval (decP s).1.length + 1) * Qp.eval (decP s).1.length) (Qp.eval (decP s).1.length))
      (subL (decP s).2 (i * Qp.eval (decP s).1.length) (Qp.eval (decP s).1.length))
      (Qp.eval (decP s).1.length))) then [true] else []) (lpN z) (lpX z)) :=
    (PS.iteEq ((PU.bitAt 0).comp hb0) (PU.const 1) (PS.const [true]) (PS.const [])).congr
      (fun z => by
        by_cases hz : V (codeP (decP (lpX z)).1 (xorL (subL (decP (lpX z)).2
            ((Qp.eval (decP (lpX z)).1.length + 1) * Qp.eval (decP (lpX z)).1.length)
            (Qp.eval (decP (lpX z)).1.length))
          (subL (decP (lpX z)).2 (lpN z * Qp.eval (decP (lpX z)).1.length)
            (Qp.eval (decP (lpX z)).1.length)) (Qp.eval (decP (lpX z)).1.length)))
        · simp [hz, NthTM.bit]
        · simp [hz, NthTM.bit])
  have hN : PU (fun s => Qp.eval (decP s).1.length + 1) := ((PU.poly Qp).comp PS.fstP).add (PU.const 1)
  have hF := PS.flatRange hN (fun i s => if V (codeP (decP s).1 (xorL (subL (decP s).2
        ((Qp.eval (decP s).1.length + 1) * Qp.eval (decP s).1.length) (Qp.eval (decP s).1.length))
      (subL (decP s).2 (i * Qp.eval (decP s).1.length) (Qp.eval (decP s).1.length))
      (Qp.eval (decP s).1.length))) then [true] else []) hb
  exact (InP.ofPUle (PU.const 1) (PU.lenX.comp hF)).congr (fun s => Iff.rfl)

theorem xorL_ofFn {Q : ℕ} (r s : Fin Q → Bool) :
    xorL (List.ofFn r) (List.ofFn s) Q = List.ofFn (xorF r s) := by
  unfold xorL
  rw [flatMap_singleton_range]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_ofFn] at h2
  simp [xorF, List.getD_eq_getElem?_getD, h2]

theorem sglR_code (V : Language) (Qp : Polynomial ℕ) (x : List Bool) (Q : ℕ)
    (hQ : Qp.eval x.length = Q) (S : Fin ((Q + 1) * Q) → Bool) (r : Fin Q → Bool) :
    sglR V Qp (codeP x (List.ofFn S ++ List.ofFn r)) ↔
      ∃ i : Fin (Q + 1), V (codeP x (List.ofFn (xorF r (blk S i)))) := by
  have hr : subL (List.ofFn S ++ List.ofFn r) ((Q + 1) * Q) Q = List.ofFn r :=
    subL_at (List.ofFn S) (List.ofFn r) [] (by simp) (by simp) (by simp)
  have hs : ∀ i : Fin (Q + 1), subL (List.ofFn S ++ List.ofFn r) (i * Q) Q = List.ofFn (blk S i) := by
    intro i
    rw [← subL_ofFn_blk S i]
    have hi := i.2
    have h1 : (i : ℕ) * Q + Q ≤ (Q + 1) * Q := by nlinarith
    rw [subL_eq _ _ _ (by simp; nlinarith), subL_eq _ _ _ (by simpa using h1),
      List.drop_append_of_le_length (by simp; nlinarith),
      List.take_append_of_le_length (by simp; omega)]
  simp only [sglR, decP_codeP, hQ]
  rw [flatMap_count]
  simp only [hr]
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies, not_forall, not_not]
  constructor
  · rintro ⟨i, hi⟩; rw [hs i, xorL_ofFn] at hi; exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by rw [hs i, xorL_ofFn]; exact hi⟩

/-! ### BPP ⊆ Σ₂ -/

theorem exists_list_iff (N : ℕ) (P : List Bool → Prop) :
    (∃ v : List Bool, v.length = N ∧ P v) ↔ ∃ w : Fin N → Bool, P (List.ofFn w) := by
  constructor
  · rintro ⟨v, rfl, h⟩
    have hx : List.ofFn (fun i : Fin v.length => v[i]) = v := List.ofFn_getElem
    exact ⟨fun i => v[i], by rw [hx]; exact h⟩
  · rintro ⟨w, h⟩; exact ⟨_, by simp, h⟩

theorem forall_list_iff (N : ℕ) (P : List Bool → Prop) :
    (∀ v : List Bool, v.length = N → P v) ↔ ∀ w : Fin N → Bool, P (List.ofFn w) := by
  constructor
  · intro h w; exact h _ (by simp)
  · intro h v hv
    subst hv
    have hx : List.ofFn (fun i : Fin v.length => v[i]) = v := List.ofFn_getElem
    have := h (fun i => v[i]); rwa [hx] at this

/-- **Sipser–Gács–Lautemann: BPP ⊆ Σ₂.** -/
theorem BPP_subset_Sigma2 {L : Language} (h : InBPP L) : InSigma 2 L := by
  obtain ⟨V, q, hV, hq⟩ := h
  set p := q + Polynomial.C 10
  set Qp := ampQ q p
  set V' := ampV V q p
  refine ⟨sglR V' Qp, fun j => if j = 1 then (Qp + 1) * Qp else Qp, InP.sglRP (InP.ampVP hV q p) Qp,
    fun x => ?_⟩
  set n := x.length
  set Q := Qp.eval n with hQdef
  have herr := amp_err hq p x
  have hQ : Q + 1 ≤ 2 ^ p.eval n := by
    have := shift_bound (q.eval n)
    have e : Q = 2 * (6 * (q.eval n + 10 + 1)) * q.eval n := by
      rw [hQdef, ampQ_eval]; simp [ampM, p]
    simp only [p, Polynomial.eval_add, Polynomial.eval_C]
    omega
  have hp1 : 1 ≤ p.eval n := by simp [p]
  show L x ↔ ∃ v1 : List Bool, v1.length = ((Qp + 1) * Qp).eval n ∧
    ∀ v2 : List Bool, v2.length = Qp.eval n → sglR V' Qp (codeP x ([] ++ v1 ++ v2))
  simp only [List.nil_append, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
  rw [exists_list_iff]
  simp only [forall_list_iff]
  simp only [sglR_code V' Qp x Q hQdef.symm]
  set W := Finset.univ.filter (fun w : Fin Q → Bool => (V' (codeP x (List.ofFn w)) ↔ ¬ L x))
  constructor
  · intro hL
    obtain ⟨S', hS'⟩ := sgl_yes (k := Q + 1) (p := p.eval n) W (by omega) herr
      (by nlinarith)
    refine ⟨fun t => S' (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2, fun r => ?_⟩
    obtain ⟨i, hi⟩ := hS' r
    refine ⟨i, ?_⟩
    have hb : blk (fun t => S' (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) i = S' i := by
      funext j; simp [blk]
    rw [hb]
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    tauto
  · rintro ⟨S, hS⟩
    by_contra hL
    obtain ⟨r, hr⟩ := sgl_no (k := Q + 1) (p := p.eval n) W hQ herr (blk S)
    obtain ⟨i, hi⟩ := hS r
    have := hr i
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at this
    tauto

/-- **BPP ⊆ Σ₂ ∩ Π₂** (Π₂ via closure under complement). -/
theorem BPP_subset_Pi2 {L : Language} (h : InBPP L) : InPi 2 L := by
  exact (InPi_iff_compl 2 L).2 (BPP_subset_Sigma2 h.compl)

end PvnpReal
