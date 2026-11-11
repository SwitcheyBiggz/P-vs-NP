/-
  PvnpReal.BPPAmp — **error amplification** for BPP by majority vote, and **Adleman's theorem**
  `BPP ⊆ P/poly`.

  * `ampV V q p`: on `codeP x R`, cut `R` into `2m` blocks of length `q(|x|)` (`m = 6(p(|x|)+1)`),
    run `V` on each, accept iff more than `m` blocks accept. Polynomial time (`InP.ampVP`).
  * `wrong_count`: the number of random strings on which `ampV` errs is `≤ (8/9)^m · 2^{q'}` —
    from `maj_count` through the bijection `Fin (2m·q) ≃ Fin (2m) × Fin q` (`finProdFinEquiv`).
  * **`InBPP.amplify`**: for every polynomial `p`, error `< 2^{-p(n)}` (stated as
    `2^{p(|x|)} · #wrong < 2^{q'(|x|)}`).
  * **`adleman` : InBPP L → InPpoly L**, and `BPP_subset_PpolyCirc` (via `InPpolyCirc_of_InPpoly`):
    with error `< 2^{-n}`, a union bound over the `2^n` inputs leaves a random string that is
    correct for all of them; it is the advice.
-/
import PvnpReal.BPP

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

/-- Half the number of votes. -/
def ampM (p : Polynomial ℕ) (n : ℕ) : ℕ := 6 * (p.eval n + 1)

/-- Number of accepting blocks. -/
noncomputable def goodCnt (V : Language) (q p : Polynomial ℕ) (x R : List Bool) : ℕ :=
  ((List.range (2 * ampM p x.length)).flatMap (fun i =>
    if V (codeP x (subL R (i * q.eval x.length) (q.eval x.length))) then [true] else [])).length

/-- The majority-vote verifier. -/
noncomputable def ampV (V : Language) (q p : Polynomial ℕ) : Language := fun s =>
  ampM p (decP s).1.length + 1 ≤ goodCnt V q p (decP s).1 (decP s).2

/-- New random-string length `2m·q`. -/
noncomputable def ampQ (q p : Polynomial ℕ) : Polynomial ℕ := 2 * (6 * (p + 1)) * q

theorem ampQ_eval (q p : Polynomial ℕ) (n : ℕ) :
    (ampQ q p).eval n = 2 * ampM p n * q.eval n := by
  simp [ampQ, ampM]

theorem PU.ampMP (p : Polynomial ℕ) : PU (fun s => ampM p (decP s).1.length) :=
  ((PU.poly (6 * (p + 1))).comp PS.fstP).congr (fun s => by simp [ampM])

theorem InP.ampVP {V : Language} (hV : InP V) (q p : Polynomial ℕ) : InP (ampV V q p) := by
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
  have hN : PU (fun s => 2 * ampM p (decP s).1.length) := (PU.const 2).mul (PU.ampMP p)
  have hF := PS.flatRange hN (fun i s => if V (codeP (decP s).1 (subL (decP s).2
      (i * q.eval (decP s).1.length) (q.eval (decP s).1.length))) then [true] else []) hb
  exact (InP.ofPUle ((PU.ampMP p).add (PU.const 1)) (PU.lenX.comp hF)).congr (fun s => Iff.rfl)

/-! ### Blocks of a random string -/

/-- Block `i` of a random string of length `t·q`. -/
def blk {t q : ℕ} (W : Fin (t * q) → Bool) (i : Fin t) : Fin q → Bool :=
  fun j => W (finProdFinEquiv (i, j))

theorem subL_ofFn_blk {t q : ℕ} (W : Fin (t * q) → Bool) (i : Fin t) :
    subL (List.ofFn W) (i * q) q = List.ofFn (blk W i) := by
  have hi := i.2
  have h1 : (i : ℕ) * q + q ≤ t * q := by nlinarith
  rw [subL_eq _ _ _ (by simpa using h1)]
  apply List.ext_getElem
  · simp; omega
  · intro j hj1 hj2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, blk]
    congr 1
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring

theorem flatMap_count (t : ℕ) (P : ℕ → Prop) :
    ((List.range t).flatMap (fun i => if P i then [true] else [])).length =
      (Finset.univ.filter (fun i : Fin t => P i)).card := by
  have h1 : ∀ t, ((List.range t).flatMap (fun i => if P i then [true] else [])).length =
      ∑ i ∈ Finset.range t, (if P i then 1 else 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
      by_cases h : P t <;> simp [h]
  rw [h1, Finset.card_filter, ← Fin.sum_univ_eq_sum_range (fun i => if P i then 1 else 0)]

theorem goodCnt_ofFn (V : Language) (q p : Polynomial ℕ) (x : List Bool)
    (W : Fin (2 * ampM p x.length * q.eval x.length) → Bool) :
    goodCnt V q p x (List.ofFn W) =
      (Finset.univ.filter (fun i : Fin (2 * ampM p x.length) =>
        V (codeP x (List.ofFn (blk W i))))).card := by
  unfold goodCnt
  rw [flatMap_count]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [subL_ofFn_blk W i]

/-! ### Counting the errors -/

theorem maj_wrong {m qn : ℕ} (V : Language) (Lx : Prop) (x : List Bool) (W : Fin (2 * m * qn) → Bool)
    (hW : m + 1 ≤ (Finset.univ.filter (fun i : Fin (2 * m) => V (codeP x (List.ofFn (blk W i))))).card
      ↔ ¬ Lx) :
    m ≤ (Finset.univ.filter (fun i : Fin (2 * m) =>
      (V (codeP x (List.ofFn (blk W i))) ↔ ¬ Lx))).card := by
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * m))))
    (fun i => V (codeP x (List.ofFn (blk W i))))
  rw [Finset.card_univ, Fintype.card_fin] at htot
  by_cases hL : Lx
  · have h1 := mt hW.1 (not_not.2 hL)
    have hsub := Finset.card_le_card (s := Finset.univ.filter
      (fun i : Fin (2 * m) => ¬ V (codeP x (List.ofFn (blk W i)))))
      (t := Finset.univ.filter (fun i : Fin (2 * m) => (V (codeP x (List.ofFn (blk W i))) ↔ ¬ Lx)))
      (fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; tauto)
    omega
  · have h1 := hW.2 hL
    have hsub := Finset.card_le_card (s := Finset.univ.filter
      (fun i : Fin (2 * m) => V (codeP x (List.ofFn (blk W i)))))
      (t := Finset.univ.filter (fun i : Fin (2 * m) => (V (codeP x (List.ofFn (blk W i))) ↔ ¬ Lx)))
      (fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; tauto)
    omega

theorem wrong_count {L : Language} {V : Language} {q : Polynomial ℕ}
    (hq : ∀ x : List Bool,
      (L x → 2 * 2 ^ q.eval x.length ≤ 3 * accCount V x (q.eval x.length)) ∧
      (¬ L x → 3 * accCount V x (q.eval x.length) ≤ 2 ^ q.eval x.length))
    (p : Polynomial ℕ) (x : List Bool) :
    9 ^ ampM p x.length * (Finset.univ.filter (fun W : Fin (2 * ampM p x.length * q.eval x.length) → Bool =>
      (ampV V q p (codeP x (List.ofFn W)) ↔ ¬ L x))).card ≤
      8 ^ ampM p x.length * 2 ^ (2 * ampM p x.length * q.eval x.length) := by
  set m := ampM p x.length
  set qn := q.eval x.length with hqn
  set bad : (Fin qn → Bool) → Prop := fun ω => (V (codeP x (List.ofFn ω)) ↔ ¬ L x)
  have hbad : 3 * (Finset.univ.filter bad).card ≤ Fintype.card (Fin qn → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    by_cases hL : L x
    · have e : (Finset.univ.filter bad).card = accCount (fun s => ¬ V s) x qn := by
        unfold accCount; congr 1; ext ω; simp [bad, hL]
      rw [e, accCount_compl]
      have h1 := (hq x).1 hL; rw [← hqn] at h1; have := accCount_le V x qn; omega
    · have e : (Finset.univ.filter bad).card = accCount V x qn := by
        unfold accCount; congr 1; ext ω; simp [bad, hL]
      rw [e]; exact (hq x).2 hL
  have hmc := @maj_count _ _ bad (fun _ => instDecidableIff) m hbad
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul] at hmc
  let Φ : (Fin (2 * m * qn) → Bool) → (Fin (2 * m) → Fin qn → Bool) := fun W => blk W
  have hinj : Function.Injective Φ := by
    intro W W' e
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    exact congrFun (congrFun e i) j
  have hcard : (Finset.univ.filter (fun W : Fin (2 * m * qn) → Bool =>
      (ampV V q p (codeP x (List.ofFn W)) ↔ ¬ L x))).card ≤
      (Finset.univ.filter (fun f : Fin (2 * m) → Fin qn → Bool =>
        m ≤ (Finset.univ.filter (fun i => bad (f i))).card)).card := by
    apply Finset.card_le_card_of_injOn Φ
    · intro W hW
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hW ⊢
      simp only [ampV, decP_codeP] at hW
      rw [goodCnt_ofFn] at hW
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * m))))
        (fun i => V (codeP x (List.ofFn (blk W i))))
      simp only [Finset.card_univ, Fintype.card_fin] at htot
      convert maj_wrong V (L x) x W (by convert hW using 2)
    · intro W _ W' _ e; exact hinj e
  calc 9 ^ m * _ ≤ 9 ^ m * _ := Nat.mul_le_mul_left _ hcard
    _ ≤ 8 ^ m * 2 ^ (qn * (2 * m)) := hmc
    _ = 8 ^ m * 2 ^ (2 * m * qn) := by rw [mul_comm qn]

theorem two_pow_eight_lt (n : ℕ) : 2 ^ n * 8 ^ (6 * (n + 1)) < 9 ^ (6 * (n + 1)) := by
  have h1 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : (2 : ℕ) ^ (n + 1) * 8 ^ (6 * (n + 1)) = (2 * 8 ^ 6) ^ (n + 1) := by
    rw [mul_pow, ← pow_mul, mul_comm 6]
  have h3 : (2 * 8 ^ 6 : ℕ) ^ (n + 1) ≤ (9 ^ 6) ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _
  have h4 : (9 : ℕ) ^ (6 * (n + 1)) = (9 ^ 6) ^ (n + 1) := by rw [← pow_mul]
  have h5 : 2 ^ n * 8 ^ (6 * (n + 1)) < 2 ^ (n + 1) * 8 ^ (6 * (n + 1)) :=
    Nat.mul_lt_mul_of_pos_right h1 (by positivity)
  omega

/-- The amplified verifier errs on fewer than a `2^{-p(n)}` fraction of its random strings. -/
theorem amp_err {L V : Language} {q : Polynomial ℕ}
    (hq : ∀ x : List Bool,
      (L x → 2 * 2 ^ q.eval x.length ≤ 3 * accCount V x (q.eval x.length)) ∧
      (¬ L x → 3 * accCount V x (q.eval x.length) ≤ 2 ^ q.eval x.length))
    (p : Polynomial ℕ) (x : List Bool) :
    2 ^ p.eval x.length * (Finset.univ.filter (fun W : Fin ((ampQ q p).eval x.length) → Bool =>
        (ampV V q p (codeP x (List.ofFn W)) ↔ ¬ L x))).card < 2 ^ (ampQ q p).eval x.length := by
  have hw := wrong_count hq p x
  set n := x.length
  have e := ampQ_eval q p n
  -- rewrite the length index of the Fin type
  have key : ∀ (Q : ℕ) (hQ : Q = 2 * ampM p n * q.eval n),
      2 ^ p.eval n * (Finset.univ.filter (fun W : Fin Q → Bool =>
        (ampV V q p (codeP x (List.ofFn W)) ↔ ¬ L x))).card < 2 ^ Q := by
    intro Q hQ
    subst hQ
    set c := (Finset.univ.filter (fun W : Fin (2 * ampM p n * q.eval n) → Bool =>
        (ampV V q p (codeP x (List.ofFn W)) ↔ ¬ L x))).card
    have hlt := two_pow_eight_lt (p.eval n)
    have hm : ampM p n = 6 * (p.eval n + 1) := rfl
    rw [← hm] at hlt
    set Q := 2 * ampM p n * q.eval n
    have hpos : 0 < 2 ^ Q := by positivity
    have : 9 ^ ampM p n * (2 ^ p.eval n * c) < 9 ^ ampM p n * 2 ^ Q := by
      calc 9 ^ ampM p n * (2 ^ p.eval n * c) = 2 ^ p.eval n * (9 ^ ampM p n * c) := by ring
        _ ≤ 2 ^ p.eval n * (8 ^ ampM p n * 2 ^ Q) := Nat.mul_le_mul_left _ hw
        _ = (2 ^ p.eval n * 8 ^ ampM p n) * 2 ^ Q := by ring
        _ < 9 ^ ampM p n * 2 ^ Q := Nat.mul_lt_mul_of_pos_right hlt hpos
    exact Nat.lt_of_mul_lt_mul_left this
  exact key _ e


/-- **Error amplification**: for every polynomial `p`, a BPP language has a polytime verifier
erring on fewer than a `2^{-p(n)}` fraction of random strings. -/
theorem InBPP.amplify {L : Language} (h : InBPP L) (p : Polynomial ℕ) :
    ∃ (V : Language) (q : Polynomial ℕ), InP V ∧ ∀ x : List Bool,
      2 ^ p.eval x.length * (Finset.univ.filter (fun W : Fin (q.eval x.length) → Bool =>
        (V (codeP x (List.ofFn W)) ↔ ¬ L x))).card < 2 ^ q.eval x.length := by
  obtain ⟨V, q, hV, hq⟩ := h
  exact ⟨ampV V q p, ampQ q p, InP.ampVP hV q p, fun x => amp_err hq p x⟩

/-! ### Adleman's theorem -/

/-- **Adleman: BPP ⊆ P/poly** (advice form). -/
theorem adleman {L : Language} (h : InBPP L) : InPpoly L := by
  obtain ⟨V, q, hV, hq⟩ := h.amplify Polynomial.X
  have hgood : ∀ n, ∃ W : Fin (q.eval n) → Bool, ∀ x : Fin n → Bool,
      (V (codeP (List.ofFn x) (List.ofFn W)) ↔ L (List.ofFn x)) := by
    intro n
    set bad : (Fin n → Bool) → Finset (Fin (q.eval n) → Bool) := fun x =>
      Finset.univ.filter (fun W : Fin (q.eval n) → Bool =>
        (V (codeP (List.ofFn x) (List.ofFn W)) ↔ ¬ L (List.ofFn x)))
    have hq' : ∀ y : List Bool, y.length = n → 2 ^ n * (Finset.univ.filter
        (fun W : Fin (q.eval n) → Bool => (V (codeP y (List.ofFn W)) ↔ ¬ L y))).card < 2 ^ q.eval n := by
      intro y hy; subst hy; simpa using hq y
    have hb : ∀ x, 2 ^ n * (bad x).card < 2 ^ q.eval n := fun x => hq' _ (List.length_ofFn)
    have hU : (Finset.univ.biUnion bad).card < 2 ^ q.eval n := by
      have h1 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n → Bool))) (t := bad)
      have h2 : ∑ x : Fin n → Bool, 2 ^ n * (bad x).card < ∑ _x : Fin n → Bool, 2 ^ q.eval n :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ => hb x)
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul] at h2
      have h3 := Nat.lt_of_mul_lt_mul_left h2
      omega
    have : (Finset.univ.biUnion bad) ≠ Finset.univ := by
      intro e
      rw [e, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hU
      omega
    obtain ⟨W, hW⟩ : ∃ W, W ∉ Finset.univ.biUnion bad := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact this (Finset.eq_univ_iff_forall.2 hc)
    refine ⟨W, fun x => ?_⟩
    have : W ∉ bad x := fun hx => hW (Finset.mem_biUnion.2 ⟨x, Finset.mem_univ _, hx⟩)
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at this
    tauto
  choose W hW using hgood
  refine ⟨V, q, fun n => List.ofFn (W n), hV, fun n => by simp, fun x => ?_⟩
  have hx : List.ofFn (fun i : Fin x.length => x[i]) = x := List.ofFn_getElem
  have := hW x.length (fun i => x[i])
  rw [hx] at this
  exact this.symm

/-- **Adleman: BPP ⊆ P/poly** (circuit form). -/
theorem BPP_subset_PpolyCirc {L : Language} (h : InBPP L) : InPpolyCirc L :=
  InPpolyCirc_of_InPpoly (adleman h)

end PvnpReal
