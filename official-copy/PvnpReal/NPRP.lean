/-
  PvnpReal.NPRP — search-to-decision for NP: if NP ⊆ BPP then NP = RP.
-/
import PvnpReal.RPClasses

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

/-! ### The prefix (self-reduction) language of an exact-length NP relation -/

/-- `preL R0 Q (codeP x u)`: `u` extends to a witness of length `Q(|x|)` for `R0`. -/
def preL (R0 : Language) (Q : Polynomial ℕ) : Language := fun t =>
  (decP t).2.length ≤ Q.eval (decP t).1.length ∧
  ∃ v : List Bool, v.length = Q.eval (decP t).1.length - (decP t).2.length ∧
    R0 (codeP (decP t).1 ((decP t).2 ++ v))

def preR (R0 : Language) (Q : Polynomial ℕ) : Language := fun s =>
  (decP (decP s).1).2.length ≤ Q.eval (decP (decP s).1).1.length ∧
  R0 (codeP (decP (decP s).1).1 ((decP (decP s).1).2 ++
    (decP s).2.take (Q.eval (decP (decP s).1).1.length - (decP (decP s).1).2.length)))

theorem InP.preRP {R0 : Language} (hR0 : InP R0) (Q : Polynomial ℕ) : InP (preR R0 Q) := by
  have X : PS (fun s => (decP (decP s).1).1) := PS.comp PS.fstP PS.fstP
  have U : PS (fun s => (decP (decP s).1).2) := PS.comp PS.fstP PS.sndP
  have QX : PU (fun s => Q.eval (decP (decP s).1).1.length) := (PU.poly Q).comp X
  have UL : PU (fun s => (decP (decP s).1).2.length) := PU.lenX.comp U
  have W := PS.takeU PS.sndP (PU.sub QX UL)
  exact (InP.ofPUle UL QX).inter (hR0.compPS (PS.codePF X (PS.append U W)))

theorem preL_NP {R0 : Language} (hR0 : InP R0) (Q : Polynomial ℕ) : InNP (preL R0 Q) := by
  refine (Sigma1_iff_NP _).1 ⟨preR R0 Q, fun _ => Q, InP.preRP hR0 Q, fun t => ?_⟩
  show preL R0 Q t ↔ ∃ w : List Bool, w.length = Q.eval t.length ∧ preR R0 Q (codeP t ([] ++ w))
  simp only [List.nil_append, preR, decP_codeP, preL]
  have hx : Q.eval (decP t).1.length ≤ Q.eval t.length := poly_eval_mono Q (decP_fst_len t)
  constructor
  · rintro ⟨hu, v, hv, hR⟩
    refine ⟨v ++ List.replicate (Q.eval t.length - v.length) false, by simp; omega, hu, ?_⟩
    rw [List.take_left' hv]; exact hR
  · rintro ⟨w, hw, hu, hR⟩
    exact ⟨hu, _, by simp; omega, hR⟩

theorem preL_code (R0 : Language) (Q : Polynomial ℕ) (x u : List Bool) :
    preL R0 Q (codeP x u) ↔ u.length ≤ Q.eval x.length ∧
      ∃ v : List Bool, v.length = Q.eval x.length - u.length ∧ R0 (codeP x (u ++ v)) := by
  simp [preL, decP_codeP]

/-! ### Bit-by-bit search -/

/-- The path built by a decision procedure: `u_{i+1} = u_i ++ [dec i u_i]`. -/
def pathU (dec : ℕ → List Bool → Bool) : ℕ → List Bool
  | 0 => []
  | i + 1 => pathU dec i ++ [dec i (pathU dec i)]

theorem pathU_length (dec : ℕ → List Bool → Bool) (i : ℕ) : (pathU dec i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [pathU, ih]

/-- **Search correctness**: if every decision along the path is right, the path ends in a
witness. -/
theorem search_correct (R0 : Language) (Q : Polynomial ℕ) (x : List Bool)
    (dec : ℕ → List Bool → Bool) (h0 : preL R0 Q (codeP x []))
    (hdec : ∀ i < Q.eval x.length,
      (dec i (pathU dec i) = true ↔ preL R0 Q (codeP x (pathU dec i ++ [true])))) :
    R0 (codeP x (pathU dec (Q.eval x.length))) := by
  have step : ∀ i ≤ Q.eval x.length, preL R0 Q (codeP x (pathU dec i)) := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ i ih =>
      intro hi
      have hp := ih (by omega)
      rw [preL_code] at hp
      obtain ⟨_, v, hv, hR⟩ := hp
      rw [pathU_length] at hv
      have hd := hdec i (by omega)
      show preL R0 Q (codeP x (pathU dec i ++ [dec i (pathU dec i)]))
      cases hb : dec i (pathU dec i)
      · rw [hb] at hd
        match v, hv, hR with
        | [], hv, _ => simp at hv; omega
        | b :: v', hv, hR =>
          cases b
          · rw [preL_code]
            refine ⟨by simp [pathU_length]; omega, v', by simp [pathU_length] at hv ⊢; omega, ?_⟩
            simpa using hR
          · exfalso
            have : preL R0 Q (codeP x (pathU dec i ++ [true])) := by
              rw [preL_code]
              refine ⟨by simp [pathU_length]; omega, v', by simp [pathU_length] at hv ⊢; omega, ?_⟩
              simpa using hR
            exact absurd (hd.2 this) (by simp)
      · rw [hb] at hd; exact hd.1 rfl
  have hp := step _ le_rfl
  rw [preL_code, pathU_length] at hp
  obtain ⟨_, v, hv, hR⟩ := hp
  rw [Nat.sub_self, List.length_eq_zero_iff] at hv
  subst hv; simpa using hR

/-! ### Counting lemmas -/

theorem card_exists_le {α ι : Type} [Fintype α] [Fintype ι] (P : ι → α → Prop) :
    (Finset.univ.filter (fun a => ∃ i, P i a)).card ≤
      ∑ i, (Finset.univ.filter (fun a => P i a)).card := by
  calc _ ≤ (Finset.univ.biUnion (fun i => Finset.univ.filter (fun a => P i a))).card := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        obtain ⟨i, hi⟩ := ha
        exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simpa using hi⟩
    _ ≤ _ := Finset.card_biUnion_le

theorem sum_two_pow_le (n : ℕ) : ∑ i : Fin n, 2 ^ (i : ℕ) < 2 ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i)]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Blocks as an equivalence. -/
def blkEquiv (t q : ℕ) : (Fin (t * q) → Bool) ≃ (Fin t → Fin q → Bool) where
  toFun W := fun i j => W (finProdFinEquiv (i, j))
  invFun f := fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv W := by
    funext k
    show W (finProdFinEquiv (finProdFinEquiv.symm k)) = W k
    rw [Equiv.apply_symm_apply]
  right_inv f := by funext i j; simp

theorem count_coord {t B : ℕ} (i : Fin t) (S : Finset (Fin B → Bool)) (c : ℕ)
    (hS : c * S.card ≤ 2 ^ B) :
    c * (Finset.univ.filter (fun W : Fin (t * B) → Bool => blk W i ∈ S)).card ≤ 2 ^ (t * B) := by
  have e1 : (Finset.univ.filter (fun W : Fin (t * B) → Bool => blk W i ∈ S)).card =
      (Fintype.piFinset (fun j : Fin t => if j = i then S else Finset.univ)).card := by
    apply Finset.card_equiv (blkEquiv t B)
    intro W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j; split_ifs with hj
      · subst hj; exact h
      · exact Finset.mem_univ _
    · intro h; have := h i; rw [if_pos rfl] at this; exact this
  rw [e1, Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [if_pos rfl]
  have e2 : ∏ j ∈ Finset.univ.erase i, (if j = i then S else Finset.univ).card =
      ∏ j ∈ Finset.univ.erase i, (2 ^ B) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
    simp
  have e3 : 2 ^ (t * B) = 2 ^ B * ∏ j ∈ Finset.univ.erase i, (2 ^ B) := by
    rw [Finset.mul_prod_erase _ (fun _ => 2 ^ B) (Finset.mem_univ i)]
    simp [Finset.prod_const, ← pow_mul, mul_comm]
  rw [e2, e3, ← mul_assoc]
  exact Nat.mul_le_mul_right _ hS

theorem count_take_le (m B : ℕ) (h : m ≤ B) (P : List Bool → Prop) :
    (Finset.univ.filter (fun r : Fin B → Bool => P ((List.ofFn r).take m))).card =
      (Finset.univ.filter (fun a : Fin m → Bool => P (List.ofFn a))).card * 2 ^ (B - m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  convert count_take (m := m) (d := d) P

/-! ### The RP verifier: run the search with independent random blocks -/

/-- Decision bit at state `codeP (codeP x R) u`: ask the BPP decider `D` whether `u ++ [true]`
extends to a witness, using block `|u|` (of length `B = Bp(|x|)`) of `R`. -/
noncomputable def stepBit (D : Language) (qD Bp : Polynomial ℕ) (y : List Bool) : Bool :=
  decide (D (codeP (codeP (decP (decP y).1).1 ((decP y).2 ++ [true]))
    ((subL (decP (decP y).1).2 ((decP y).2.length * Bp.eval (decP (decP y).1).1.length)
      (Bp.eval (decP (decP y).1).1.length)).take
      (qD.eval (codeP (decP (decP y).1).1 ((decP y).2 ++ [true])).length))))

noncomputable def stepG (D : Language) (qD Bp : Polynomial ℕ) (y : List Bool) : List Bool :=
  y ++ codeL [stepBit D qD Bp y]

/-- The RP verifier: iterate `Q(|x|)` search steps, then check the found witness with `R0`. -/
noncomputable def npV (R0 : Language) (Q : Polynomial ℕ) (D : Language) (qD Bp : Polynomial ℕ) :
    Language := fun s =>
  R0 (codeP (decP s).1 (decP ((stepG D qD Bp)^[Q.eval (decP s).1.length] (codeP s []))).2)

theorem stepBit_code (D : Language) (qD Bp : Polynomial ℕ) (x Rr u : List Bool) :
    stepBit D qD Bp (codeP (codeP x Rr) u) = decide (D (codeP (codeP x (u ++ [true]))
      ((subL Rr (u.length * Bp.eval x.length) (Bp.eval x.length)).take
        (qD.eval (codeP x (u ++ [true])).length)))) := by
  simp only [stepBit, decP_codeP]

theorem stepG_code (D : Language) (qD Bp : Polynomial ℕ) (s u : List Bool) :
    stepG D qD Bp (codeP s u) = codeP s (u ++ [stepBit D qD Bp (codeP s u)]) := by
  simp [stepG, codeP, codeL, List.flatMap_append]

theorem stepG_iter (D : Language) (qD Bp : Polynomial ℕ) (s : List Bool) (i : ℕ) :
    (stepG D qD Bp)^[i] (codeP s []) =
      codeP s (pathU (fun _ u => stepBit D qD Bp (codeP s u)) i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, stepG_code]; rfl

theorem npV_code (R0 : Language) (Q : Polynomial ℕ) (D : Language) (qD Bp : Polynomial ℕ)
    (x Rr : List Bool) :
    npV R0 Q D qD Bp (codeP x Rr) ↔
      R0 (codeP x (pathU (fun _ u => stepBit D qD Bp (codeP (codeP x Rr) u)) (Q.eval x.length))) := by
  unfold npV
  rw [decP_codeP, stepG_iter, decP_codeP]

theorem stepG_len1 (D : Language) (qD Bp : Polynomial ℕ) (z : List Bool) :
    (stepG D qD Bp z).length ≤ z.length + 3 := by
  unfold stepG; cases stepBit D qD Bp z <;> simp [codeL]

theorem stepG_len (D : Language) (qD Bp : Polynomial ℕ) (y : List Bool) (i : ℕ) :
    ((stepG D qD Bp)^[i] y).length ≤ (Polynomial.C 3 * Polynomial.X).eval (y.length + i) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  induction i with
  | zero => simp; omega
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := stepG_len1 D qD Bp ((stepG D qD Bp)^[i] y)
    omega

theorem PS.stepGP {D : Language} (hD : InP D) (qD Bp : Polynomial ℕ) : PS (stepG D qD Bp) := by
  have Xy : PS (fun y => (decP (decP y).1).1) := PS.comp PS.fstP PS.fstP
  have Ry : PS (fun y => (decP (decP y).1).2) := PS.comp PS.fstP PS.sndP
  have Ty : PS (fun y => codeP (decP (decP y).1).1 ((decP y).2 ++ [true])) :=
    PS.codePF Xy (PS.append PS.sndP (PS.const [true]))
  have By : PU (fun y => Bp.eval (decP (decP y).1).1.length) := (PU.poly Bp).comp Xy
  have Off : PU (fun y => (decP y).2.length * Bp.eval (decP (decP y).1).1.length) :=
    PU.mul (PU.lenX.comp PS.sndP) By
  have Sub := PS.subL Ry Off By
  have Mt : PU (fun y => qD.eval (codeP (decP (decP y).1).1 ((decP y).2 ++ [true])).length) :=
    (PU.poly qD).comp Ty
  have Rt := PS.takeU Sub Mt
  have hb0 := PS.ofInP (hD.compPS (PS.codePF Ty Rt))
  have hbits := PS.iteEq ((PU.bitAt 0).comp hb0) (PU.const 1) (PS.const [true, true, false])
    (PS.const [true, false])
  refine (PS.append PS.id hbits).congr (fun y => ?_)
  unfold stepG stepBit
  congr 1
  split_ifs with h <;> simp_all [NthTM.bit, codeL]
  · rfl
  · rfl

theorem InP.npVP {R0 D : Language} (hR0 : InP R0) (hD : InP D) (Q qD Bp : Polynomial ℕ) :
    InP (npV R0 Q D qD Bp) := by
  have hz : PS (fun s => List.replicate (Q.eval (decP s).1.length) true ++ false :: codeP s []) :=
    PS.append (PU.polyOf Q (PU.lenX.comp PS.fstP)) (PS.cons false (PS.codePF PS.id (PS.const [])))
  have hit : PS (fun s => (stepG D qD Bp)^[Q.eval (decP s).1.length] (codeP s [])) :=
    (PS.comp hz (PS.iter (PS.stepGP hD qD Bp) _ (stepG_len D qD Bp))).congr
      (fun s => by simp only [lpN_rep, lpX_rep])
  exact hR0.compPS (PS.codePF PS.fstP (PS.comp hit PS.sndP))

/-! ### Error analysis -/

/-- Yes-instances: at least half the random strings make the search succeed. -/
theorem npV_yes (R0 D : Language) (Q qD Bp : Polynomial ℕ)
    (hBp : ∀ n, Bp.eval n = qD.eval (3 * n + 3 * Q.eval n + 1))
    (hDerr : ∀ t : List Bool, 2 ^ (Q + 1).eval t.length *
      (Finset.univ.filter (fun W : Fin (qD.eval t.length) → Bool =>
        (D (codeP t (List.ofFn W)) ↔ ¬ preL R0 Q t))).card < 2 ^ qD.eval t.length)
    (x : List Bool) (h0 : preL R0 Q (codeP x [])) (Q' B : ℕ) (hQ : Q' = Q.eval x.length)
    (hB : B = Bp.eval x.length) :
    2 ^ (Q' * B) ≤ 2 * accCount (npV R0 Q D qD Bp) x (Q' * B) := by
  let S : List Bool → Finset (Fin B → Bool) := fun u => Finset.univ.filter (fun r =>
    (D (codeP (codeP x (u ++ [true])) ((List.ofFn r).take (qD.eval (codeP x (u ++ [true])).length)))
      ↔ ¬ preL R0 Q (codeP x (u ++ [true]))))
  -- one block is wrong for a fixed prefix with probability ≤ 2^{-(Q'+1)}
  have hS : ∀ u : List Bool, u.length < Q' → 2 ^ (Q' + 1) * (S u).card ≤ 2 ^ B := by
    intro u hu
    have ht : x.length ≤ (codeP x (u ++ [true])).length := by
      have := decP_fst_len (codeP x (u ++ [true])); rwa [decP_codeP] at this
    have htl := codeP_length_le x (u ++ [true])
    simp only [List.length_append, List.length_cons, List.length_nil] at htl
    have hm : qD.eval (codeP x (u ++ [true])).length ≤ B := by
      rw [hB, hBp]; exact poly_eval_mono qD (by rw [← hQ]; omega)
    have hc := count_take_le _ B hm (fun l => D (codeP (codeP x (u ++ [true])) l) ↔
      ¬ preL R0 Q (codeP x (u ++ [true])))
    have hcS : (S u).card = (Finset.univ.filter (fun W : Fin (qD.eval (codeP x (u ++ [true])).length) → Bool =>
        (D (codeP (codeP x (u ++ [true])) (List.ofFn W)) ↔ ¬ preL R0 Q (codeP x (u ++ [true]))))).card *
        2 ^ (B - qD.eval (codeP x (u ++ [true])).length) := by
      convert hc
    have he := hDerr (codeP x (u ++ [true]))
    rw [Polynomial.eval_add, Polynomial.eval_one] at he
    have hq : 2 ^ (Q' + 1) ≤ 2 ^ (Q.eval (codeP x (u ++ [true])).length + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [hQ]; have := poly_eval_mono Q ht; omega)
    rw [hcS]
    generalize (Finset.univ.filter (fun W : Fin (qD.eval (codeP x (u ++ [true])).length) → Bool =>
        (D (codeP (codeP x (u ++ [true])) (List.ofFn W)) ↔ ¬ preL R0 Q (codeP x (u ++ [true]))))).card = c
      at he
    have e : 2 ^ B = 2 ^ qD.eval (codeP x (u ++ [true])).length *
        2 ^ (B - qD.eval (codeP x (u ++ [true])).length) := by
      rw [← pow_add, Nat.add_sub_cancel' hm]
    rw [e, ← mul_assoc]
    apply Nat.mul_le_mul_right
    calc 2 ^ (Q' + 1) * c ≤ 2 ^ (Q.eval (codeP x (u ++ [true])).length + 1) * c :=
          Nat.mul_le_mul_right _ hq
      _ ≤ _ := he.le
  let dec : (Fin (Q' * B) → Bool) → ℕ → List Bool → Bool := fun W _ u =>
    stepBit D qD Bp (codeP (codeP x (List.ofFn W)) u)
  let G : (Fin (Q' * B) → Bool) → Prop := fun W => ∀ i : Fin Q', blk W i ∉ S (pathU (dec W) i)
  -- good random strings are accepted
  have hgood : ∀ W, G W → npV R0 Q D qD Bp (codeP x (List.ofFn W)) := by
    intro W hW
    rw [npV_code]
    apply search_correct R0 Q x (dec W) h0
    intro i hi
    have hi' : i < Q' := by omega
    have hn := hW ⟨i, hi'⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    show stepBit D qD Bp (codeP (codeP x (List.ofFn W)) (pathU (dec W) i)) = true ↔ _
    rw [stepBit_code, pathU_length, ← hB]
    have hsub := subL_ofFn_blk W ⟨i, hi'⟩
    simp only at hsub
    rw [hsub, decide_eq_true_eq]
    tauto
  -- bad random strings are rare
  have hbad : (Finset.univ.filter (fun W => ¬ G W)).card ≤
      ∑ i : Fin Q', ∑ u : Fin i → Bool,
        (Finset.univ.filter (fun W : Fin (Q' * B) → Bool => blk W i ∈ S (List.ofFn u))).card := by
    calc _ ≤ (Finset.univ.filter (fun W : Fin (Q' * B) → Bool =>
            ∃ i : Fin Q', ∃ u : Fin i → Bool, blk W i ∈ S (List.ofFn u))).card := by
          apply Finset.card_le_card
          intro W hW
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, G, not_forall, not_not] at hW ⊢
          obtain ⟨i, hi⟩ := hW
          exact ⟨i, (exists_list_iff (i : ℕ) (fun v => blk W i ∈ S v)).1
            ⟨_, pathU_length _ _, hi⟩⟩
      _ ≤ ∑ i : Fin Q', (Finset.univ.filter (fun W : Fin (Q' * B) → Bool =>
            ∃ u : Fin i → Bool, blk W i ∈ S (List.ofFn u))).card := by
          convert card_exists_le (fun (i : Fin Q') (W : Fin (Q' * B) → Bool) =>
            ∃ u : Fin i → Bool, blk W i ∈ S (List.ofFn u))
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          convert card_exists_le (fun (u : Fin i → Bool) (W : Fin (Q' * B) → Bool) =>
            blk W i ∈ S (List.ofFn u))
  have hsum : 2 ^ (Q' + 1) * (∑ i : Fin Q', ∑ u : Fin i → Bool,
        (Finset.univ.filter (fun W : Fin (Q' * B) → Bool => blk W i ∈ S (List.ofFn u))).card) ≤
      2 ^ Q' * 2 ^ (Q' * B) := by
    rw [Finset.mul_sum]
    calc _ = ∑ i : Fin Q', ∑ u : Fin i → Bool, 2 ^ (Q' + 1) *
          (Finset.univ.filter (fun W : Fin (Q' * B) → Bool => blk W i ∈ S (List.ofFn u))).card := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin Q', ∑ _u : Fin i → Bool, 2 ^ (Q' * B) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro u _
          exact count_coord i _ _ (hS _ (by simp))
      _ = (∑ i : Fin Q', 2 ^ (i : ℕ)) * 2 ^ (Q' * B) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; simp
      _ ≤ _ := Nat.mul_le_mul_right _ (sum_two_pow_le Q').le
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ) G
  have hall : (Finset.univ : Finset (Fin (Q' * B) → Bool)).card = 2 ^ (Q' * B) := by simp
  have hacc : (Finset.univ.filter G).card ≤ accCount (npV R0 Q D qD Bp) x (Q' * B) := by
    unfold accCount
    apply Finset.card_le_card
    intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
    exact hgood W hW
  have h2 : 2 ^ Q' * (2 * (Finset.univ.filter (fun W => ¬ G W)).card) ≤ 2 ^ Q' * 2 ^ (Q' * B) := by
    calc _ = 2 ^ (Q' + 1) * (Finset.univ.filter (fun W => ¬ G W)).card := by ring
      _ ≤ _ := (Nat.mul_le_mul_left _ hbad).trans hsum
  have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
  omega

/-- **If NP ⊆ BPP then NP ⊆ RP** (search-to-decision self-reducibility, done generically for
any exact-length NP relation via its prefix language). -/
theorem NP_subset_RP_of_NP_subset_BPP (H : ∀ L, InNP L → InBPP L) {L : Language} (hL : InNP L) :
    InRP L := by
  obtain ⟨R0, qs, hR0, hLR⟩ := (Sigma1_iff_NP L).2 hL
  have hLx : ∀ x, L x ↔ preL R0 (qs 0) (codeP x []) := by
    intro x; rw [hLR x, preL_code]; simp
  obtain ⟨D, qD, hD, hDerr⟩ := (H _ (preL_NP hR0 (qs 0))).amplify (qs 0 + 1)
  let Bp := qD.comp (Polynomial.C 3 * Polynomial.X + Polynomial.C 3 * qs 0 + 1)
  have hBp : ∀ n, Bp.eval n = qD.eval (3 * n + 3 * (qs 0).eval n + 1) := by
    intro n; simp [Bp, Polynomial.eval_comp]
  refine ⟨npV R0 (qs 0) D qD Bp, qs 0 * Bp, InP.npVP hR0 hD _ _ _, fun x => ?_⟩
  rw [Polynomial.eval_mul]
  constructor
  · intro h
    exact npV_yes R0 D (qs 0) qD Bp hBp hDerr x ((hLx x).1 h) _ _ rfl rfl
  · intro h
    apply accCount_eq_zero.2
    intro W hW
    rw [npV_code] at hW
    apply h; rw [hLx x, preL_code]
    refine ⟨Nat.zero_le _, _, ?_, by simpa using hW⟩
    simp [pathU_length]

/-- **NP ⊆ BPP ⟹ NP = RP.** -/
theorem NP_eq_RP_of_NP_subset_BPP (H : ∀ L, InNP L → InBPP L) (L : Language) :
    InNP L ↔ InRP L :=
  ⟨NP_subset_RP_of_NP_subset_BPP H, RP_subset_NP⟩

end PvnpReal
