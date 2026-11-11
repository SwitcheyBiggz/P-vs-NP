/-
  PvnpReal.PHGen — general structure of the hierarchy.

  * Polytime `take`/`drop` by unary amounts (`PS.takeU`, `PS.dropU`).
  * `altD`: alternating blocks whose exact lengths may depend on `x` and on the witnesses chosen so
    far (polytime, polynomially bounded in `|x|`). **Padding lemma** `altD_pad`: such a formula is an
    ordinary `altQ` formula (blocks padded to polynomial length, the leaf trims them back).
  * `InSigma.of_reduces`, `InPi.of_reduces`: Σ_k, Π_k are closed under polytime many-one reductions.
  * `Rcol_true_Sigma`: Σ_{k} (k ≥ 1) is closed under an exact-length ∃ block.
  * **`PH_eq_Sigma_of_Sigma_eq_Pi`**: `k ≥ 1`, `Σ_k = Π_k → PH = Σ_k`.
-/
import PvnpReal.PHNP

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### Polytime sublists -/

/-- `len` bits of `A` starting at `off`. -/
def subL (A : List Bool) (off len : ℕ) : List Bool :=
  (List.range len).flatMap (fun i => [decide (NthTM.bit A (off + i) = 1)])

theorem PS.subL {A : List Bool → List Bool} {off len : List Bool → ℕ} (hA : PS A) (ho : PU off)
    (hl : PU len) : PS (fun s => subL (A s) (off s) (len s)) := by
  have hb : PS (fun z => [decide (NthTM.bit (A (lpX z)) (off (lpX z) + lpN z) = 1)]) :=
    PS.boolOf ((PU.nth.comp (PS.append (PU.add (ho.comp PS.drop) PU.fst)
      (PS.cons false (PS.comp PS.drop hA)))).congr (fun z => by simp only [lpN_rep, lpX_rep]))
  exact PS.flatRange hl (fun i x => [decide (NthTM.bit (A x) (off x + i) = 1)]) hb

theorem subL_eq (A : List Bool) (off len : ℕ) (h : off + len ≤ A.length) :
    subL A off len = (A.drop off).take len := by
  unfold subL
  rw [flatMap_singleton_range]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
      NthTM.bit, List.getElem?_eq_getElem (show off + i < A.length by omega)]
    cases A[off + i] <;> simp

theorem PS.takeU {A : List Bool → List Bool} {c : List Bool → ℕ} (hA : PS A) (hc : PU c) :
    PS (fun s => (A s).take (c s)) :=
  (PS.subL hA (PU.const 0) (PU.sub hc (PU.sub hc (PU.lenX.comp hA)))).congr (fun s => by
    rw [subL_eq _ _ _ (by omega)]
    simp only [List.drop_zero]
    rw [List.take_eq_take_iff]; omega)

theorem PS.dropU {A : List Bool → List Bool} {c : List Bool → ℕ} (hA : PS A) (hc : PU c) :
    PS (fun s => (A s).drop (c s)) :=
  (PS.subL hA hc (PU.sub (PU.lenX.comp hA) hc)).congr (fun s => by
    by_cases h : c s ≤ (A s).length
    · rw [subL_eq _ _ _ (by omega)]; simp
    · have e : (A s).length - c s = 0 := by omega
      rw [e, List.drop_eq_nil_of_le (by omega)]; rfl)

/-! ### Dependent-length alternating blocks and padding -/

def altD (R : Language) (lens : ℕ → List Bool → List Bool → ℕ) (x : List Bool) :
    ℕ → Bool → List Bool → Prop
  | 0, _, u => R (codeP x u)
  | k + 1, true, u => ∃ w : List Bool, w.length = lens k x u ∧ altD R lens x k false (u ++ w)
  | k + 1, false, u => ∀ w : List Bool, w.length = lens k x u → altD R lens x k true (u ++ w)

@[simp] theorem altD_zero (R : Language) (lens x b u) : altD R lens x 0 b u = R (codeP x u) := rfl
@[simp] theorem altD_succ_true (R : Language) (lens x k u) : altD R lens x (k + 1) true u =
    ∃ w : List Bool, w.length = lens k x u ∧ altD R lens x k false (u ++ w) := rfl
@[simp] theorem altD_succ_false (R : Language) (lens x k u) : altD R lens x (k + 1) false u =
    ∀ w : List Bool, w.length = lens k x u → altD R lens x k true (u ++ w) := rfl

/-- Trimming padded blocks back to their logical lengths. -/
def trimD (lens : ℕ → List Bool → List Bool → ℕ) (P : ℕ → Polynomial ℕ) (x : List Bool) :
    ℕ → List Bool → List Bool → List Bool
  | 0, t, _ => t
  | j + 1, t, U => trimD lens P x j (t ++ U.take (lens j x t)) (U.drop ((P j).eval x.length))

theorem trimD_step (lens : ℕ → List Bool → List Bool → ℕ) (P : ℕ → Polynomial ℕ) (x : List Bool)
    (hP : ∀ j x u, lens j x u ≤ (P j).eval x.length) (j : ℕ) (t W V : List Bool)
    (hW : W.length = (P j).eval x.length) :
    trimD lens P x (j + 1) t (W ++ V) = trimD lens P x j (t ++ W.take (lens j x t)) V := by
  have h := hP j x t
  simp only [trimD]
  rw [List.take_append_of_le_length (by omega), ← hW, List.drop_left]

theorem PS.trimD (lens : ℕ → List Bool → List Bool → ℕ) (P : ℕ → Polynomial ℕ)
    (hl : ∀ j, PU (fun s => lens j (decP s).1 (decP s).2)) {A : List Bool → List Bool} (hA : PS A) :
    ∀ j {T U : List Bool → List Bool}, PS T → PS U → PS (fun s => trimD lens P (A s) j (T s) (U s)) := by
  intro j
  induction j with
  | zero => intro T U hT _; exact hT
  | succ j ih =>
    intro T U hT hU
    have hlen : PU (fun s => lens j (A s) (T s)) :=
      ((hl j).comp (PS.codePF hA hT)).congr (fun s => by simp only [decP_codeP])
    exact ih (PS.append hT (PS.takeU hU hlen)) (PS.dropU hU (PU.polyOf (P j) (PU.lenX.comp hA)))

/-- **Padding lemma**: dependent polytime block lengths bounded by polynomials of `|x|` can be
replaced by exact polynomial lengths. -/
theorem altD_pad {R : Language} (hR : InP R) (lens : ℕ → List Bool → List Bool → ℕ)
    (hl : ∀ j, PU (fun s => lens j (decP s).1 (decP s).2)) (P : ℕ → Polynomial ℕ)
    (hP : ∀ j x u, lens j x u ≤ (P j).eval x.length) (k : ℕ) :
    ∃ R' : Language, InP R' ∧ ∀ x b, altD R lens x k b [] ↔ altQ R' P x k b [] := by
  let R' : Language := fun s => R (codeP (decP s).1 (trimD lens P (decP s).1 k [] (decP s).2))
  have hR' : InP R' := hR.compPS (PS.codePF PS.fstP
    (PS.trimD lens P hl PS.fstP k (PS.const []) PS.sndP))
  refine ⟨R', hR', fun x b => ?_⟩
  have key : ∀ j b U0 t, (∀ V, trimD lens P x k [] (U0 ++ V) = trimD lens P x j t V) →
      (altQ R' P x j b U0 ↔ altD R lens x j b t) := by
    intro j
    induction j with
    | zero =>
      intro b U0 t h
      have := h []
      simp only [List.append_nil] at this
      simp only [altQ_zero, altD_zero, R', decP_codeP, this, trimD]
    | succ j ih =>
      intro b U0 t h
      have rel : ∀ W, W.length = (P j).eval x.length → ∀ V,
          trimD lens P x k [] (U0 ++ W ++ V) = trimD lens P x j (t ++ W.take (lens j x t)) V := by
        intro W hW V
        rw [List.append_assoc, h, trimD_step lens P x hP j t W V hW]
      have hle := hP j x t
      have pad : ∀ w : List Bool, w.length = lens j x t →
          (w ++ List.replicate ((P j).eval x.length - lens j x t) false).length = (P j).eval x.length ∧
          (w ++ List.replicate ((P j).eval x.length - lens j x t) false).take (lens j x t) = w := by
        intro w hw
        refine ⟨by simp; omega, ?_⟩
        rw [List.take_append_of_le_length (by omega), ← hw, List.take_length]
      have tl : ∀ W : List Bool, W.length = (P j).eval x.length → (W.take (lens j x t)).length = lens j x t := by
        intro W hW; simp; omega
      cases b
      · simp only [altQ_succ_false, altD_succ_false]
        constructor
        · intro H w hw
          obtain ⟨h1, h2⟩ := pad w hw
          have := (ih true _ _ (rel _ h1)).1 (H _ h1)
          rwa [h2] at this
        · intro H W hW
          exact (ih true _ _ (rel W hW)).2 (H _ (tl W hW))
      · simp only [altQ_succ_true, altD_succ_true]
        constructor
        · rintro ⟨W, hW, H⟩
          exact ⟨_, tl W hW, (ih false _ _ (rel W hW)).1 H⟩
        · rintro ⟨w, hw, H⟩
          obtain ⟨h1, h2⟩ := pad w hw
          refine ⟨_, h1, (ih false _ _ (rel _ h1)).2 ?_⟩
          rwa [h2]
  exact (key k b [] [] (fun V => by simp)).symm

/-! ### Closure under polytime reductions -/

theorem PS.outPoly {f : List Bool → List Bool} (hf : PS f) :
    ∃ Pf : Polynomial ℕ, ∀ x, (f x).length ≤ Pf.eval x.length := by
  classical
  let h : TM2ComputableInPolyTime strEnc strEnc f := Classical.choice hf
  refine ⟨Polynomial.X + Polynomial.C (pushTotal h.tm) * h.time, fun x => ?_⟩
  have := outLen_boundT h.toTM2ComputableInTime x
  have e : (Polynomial.X + Polynomial.C (pushTotal h.tm) * h.time).eval x.length =
      x.length + pushTotal h.tm * h.time.eval x.length := by simp
  rw [e]; exact this

theorem altQ_comp (R : Language) (qs : ℕ → Polynomial ℕ) (f : List Bool → List Bool) (x : List Bool) :
    ∀ k b u, altQ R qs (f x) k b u ↔
      altD (fun s => R (codeP (f (decP s).1) (decP s).2)) (fun j y _ => (qs j).eval (f y).length) x k b u := by
  intro k
  induction k with
  | zero => intro b u; simp [decP_codeP]
  | succ k ih =>
    intro b u; cases b
    · simp only [altQ_succ_false, altD_succ_false, ih]
    · simp only [altQ_succ_true, altD_succ_true, ih]

/-- **Σ_k is closed under polytime many-one reductions.** -/
theorem InSigma.of_reduces {k : ℕ} {L L' : Language} (hr : PolyReduces L L') (h : InSigma k L') :
    InSigma k L := by
  obtain ⟨f, hf, hfL⟩ := hr
  obtain ⟨R, qs, hR, hL⟩ := h
  obtain ⟨Pf, hPf⟩ := PS.outPoly hf
  have hR2 : InP (fun s => R (codeP (f (decP s).1) (decP s).2)) :=
    hR.compPS (PS.codePF (PS.comp PS.fstP hf) PS.sndP)
  obtain ⟨R', hR', e⟩ := altD_pad hR2 (fun j y _ => (qs j).eval (f y).length)
    (fun j => PU.polyOf (qs j) (PU.lenX.comp (PS.comp PS.fstP hf))) (fun j => (qs j).comp Pf)
    (fun j y _ => by rw [Polynomial.eval_comp]; exact poly_eval_mono _ (hPf y)) k
  exact ⟨R', _, hR', fun x => ((hfL x).trans (hL (f x))).trans
    ((altQ_comp R qs f x k true []).trans (e x true))⟩

theorem InPi.of_reduces {k : ℕ} {L L' : Language} (hr : PolyReduces L L') (h : InPi k L') :
    InPi k L := by
  obtain ⟨f, hf, hfL⟩ := hr
  rw [InPi_iff_compl] at h ⊢
  exact InSigma.of_reduces ⟨f, hf, fun x => not_congr (hfL x)⟩ h

/-! ### Σ_{j+1} is closed under an exact-length ∃ block -/

section Merge

variable (R0 : Language) (qs : ℕ → Polynomial ℕ) (q : Polynomial ℕ) (j : ℕ)

/-- Bound on the length of `codeP (decP s).1 ((decP s).2 ++ w)` for `|w| ≤ q(|(decP s).1|)`. -/
def mbM (s : List Bool) : ℕ := 3 * s.length + 3 * q.eval (decP s).1.length + 1

/-- The string fed to the inner Σ formula, from the merged first block `U`. -/
def tM (s U : List Bool) : List Bool :=
  codeP (decP s).1 ((decP s).2 ++ U.take (q.eval (decP s).1.length))

def lensM (i : ℕ) (s U : List Bool) : ℕ :=
  if i = j then q.eval (decP s).1.length + (qs j).eval (mbM q s)
  else (qs i).eval (tM q s U).length

def leafM (c : List Bool) : Prop :=
  R0 (codeP (tM q (decP c).1 (decP c).2)
    (((decP c).2.drop (q.eval (decP (decP c).1).1.length)).take
        ((qs j).eval (tM q (decP c).1 (decP c).2).length) ++
      (decP c).2.drop (lensM qs q j j (decP c).1 [])))

theorem tM_len_le (s U : List Bool) : (tM q s U).length ≤ mbM q s := by
  have h1 := codeP_length_le (decP s).1 ((decP s).2 ++ U.take (q.eval (decP s).1.length))
  have h2 := decP_len s.length s le_rfl
  have h3 : (U.take (q.eval (decP s).1.length)).length ≤ q.eval (decP s).1.length := by simp
  simp only [tM, mbM, List.length_append] at h1 ⊢; omega

theorem merge_inner (s W : List Bool) (hW : W.length = lensM qs q j j s []) :
    ∀ i ≤ j, ∀ b y, altD (leafM R0 qs q j) (lensM qs q j) s i b (W ++ y) ↔
      altQ R0 qs (tM q s W) i b
        ((W.drop (q.eval (decP s).1.length)).take ((qs j).eval (tM q s W).length) ++ y) := by
  have hWl : W.length = q.eval (decP s).1.length + (qs j).eval (mbM q s) := by
    rw [hW]; simp [lensM]
  have htk : ∀ y : List Bool, (W ++ y).take (q.eval (decP s).1.length) = W.take (q.eval (decP s).1.length) :=
    fun y => List.take_append_of_le_length (by omega)
  have htM : ∀ y, tM q s (W ++ y) = tM q s W := fun y => by simp only [tM, htk]
  intro i
  induction i with
  | zero =>
    intro _ b y
    simp only [altD_zero, altQ_zero, leafM, decP_codeP, htM]
    have hd : (W ++ y).drop (q.eval (decP s).1.length) =
        W.drop (q.eval (decP s).1.length) ++ y := List.drop_append_of_le_length (by omega)
    have hm : (tM q s W).length ≤ mbM q s := tM_len_le q s W
    have hm' := poly_eval_mono (qs j) hm
    rw [hd, List.take_append_of_le_length (by simp; omega)]
    have : (W ++ y).drop (lensM qs q j j s []) = y := by rw [← hW, List.drop_left]
    rw [this]
  | succ i ih =>
    intro hi b y
    have hne : i ≠ j := by omega
    have hlen : lensM qs q j i s (W ++ y) = (qs i).eval (tM q s W).length := by
      simp only [lensM, if_neg hne, htM]
    cases b
    · simp only [altD_succ_false, altQ_succ_false, hlen]
      exact forall_congr' fun w => imp_congr_right fun _ => by
        rw [List.append_assoc, ih (by omega), List.append_assoc]
    · simp only [altD_succ_true, altQ_succ_true, hlen]
      exact exists_congr fun w => and_congr_right fun _ => by
        rw [List.append_assoc, ih (by omega), List.append_assoc]

theorem merge_iff (R : Language) (hR : ∀ t, R t ↔ altQ R0 qs t (j + 1) true []) (s : List Bool) :
    Rcol true R q s ↔ altD (leafM R0 qs q j) (lensM qs q j) s (j + 1) true [] := by
  simp only [Rcol, if_true, altD_succ_true, List.nil_append]
  have hl : lensM qs q j j s [] = q.eval (decP s).1.length + (qs j).eval (mbM q s) := by simp [lensM]
  constructor
  · rintro ⟨w, hw, hRw⟩
    obtain ⟨v, hv, hA⟩ := (hR _).1 hRw
    simp only [List.nil_append] at hA
    have htw : tM q s (w ++ v ++ List.replicate ((qs j).eval (mbM q s) - v.length) false) =
        codeP (decP s).1 ((decP s).2 ++ w) := by
      simp only [tM, List.append_assoc]
      rw [List.take_append_of_le_length (by omega), ← hw, List.take_length]
    have hvb : v.length ≤ (qs j).eval (mbM q s) := by
      rw [hv]; apply poly_eval_mono
      have := tM_len_le q s (w ++ v ++ List.replicate ((qs j).eval (mbM q s) - v.length) false)
      rwa [htw] at this
    refine ⟨w ++ v ++ List.replicate ((qs j).eval (mbM q s) - v.length) false, ?_, ?_⟩
    · rw [hl]; simp; omega
    · have := merge_inner R0 qs q j s (w ++ v ++ List.replicate ((qs j).eval (mbM q s) - v.length) false)
        (by rw [hl]; simp; omega) j le_rfl false []
      simp only [List.append_nil] at this
      rw [this, htw]
      have e1 : (w ++ v ++ List.replicate ((qs j).eval (mbM q s) - v.length) false).drop
          (q.eval (decP s).1.length) = v ++ List.replicate ((qs j).eval (mbM q s) - v.length) false := by
        rw [List.append_assoc, ← hw, List.drop_left]
      rw [e1, ← hv, List.take_append_of_le_length le_rfl, List.take_length]
      exact hA
  · rintro ⟨W, hW, hA⟩
    have hWl : W.length = q.eval (decP s).1.length + (qs j).eval (mbM q s) := by rw [hW, hl]
    have := merge_inner R0 qs q j s W hW j le_rfl false []
    simp only [List.append_nil] at this
    rw [this] at hA
    refine ⟨W.take (q.eval (decP s).1.length), by simp; omega, (hR _).2 ?_⟩
    simp only [altQ_succ_true, List.nil_append]
    have hm := poly_eval_mono (qs j) (tM_len_le q s W)
    refine ⟨_, ?_, hA⟩
    simp only [List.length_take, List.length_drop]
    simp only [tM] at hm ⊢
    omega

end Merge

/-- **Σ_{j+1} is closed under an exact-length existential block.** -/
theorem Rcol_true_Sigma {j : ℕ} {R : Language} (hR : InSigma (j + 1) R) (q : Polynomial ℕ) :
    InSigma (j + 1) (Rcol true R q) := by
  obtain ⟨R0, qs, hR0, hRe⟩ := hR
  have hA : PS (fun c => (decP c).1) := PS.fstP
  -- polytime pieces
  have htM : ∀ {S U : List Bool → List Bool}, PS S → PS U → PS (fun c => tM q (S c) (U c)) :=
    fun hS hU => PS.codePF (PS.comp hS PS.fstP) (PS.append (PS.comp hS PS.sndP)
      (PS.takeU hU (PU.polyOf q (PU.lenX.comp (PS.comp hS PS.fstP)))))
  have hmb : PU (fun c => mbM q (decP c).1) :=
    PU.add (PU.add (PU.mul (PU.const 3) (PU.lenX.comp hA))
      (PU.mul (PU.const 3) (PU.polyOf q (PU.lenX.comp (PS.comp hA PS.fstP))))) (PU.const 1)
  have hlj : PU (fun c => lensM qs q j j (decP c).1 []) :=
    (PU.add (PU.polyOf q (PU.lenX.comp (PS.comp hA PS.fstP))) (PU.polyOf (qs j) hmb)).congr
      (fun c => by simp [lensM])
  have hleaf : InP (leafM R0 qs q j) := by
    have hT := htM PS.fstP PS.sndP
    exact hR0.compPS (PS.codePF hT (PS.append
      (PS.takeU (PS.dropU PS.sndP (PU.polyOf q (PU.lenX.comp (PS.comp hA PS.fstP))))
        (PU.polyOf (qs j) (PU.lenX.comp hT)))
      (PS.dropU PS.sndP hlj)))
  have hl : ∀ i, PU (fun c => lensM qs q j i (decP c).1 (decP c).2) := by
    intro i
    by_cases hi : i = j
    · subst hi; exact hlj.congr (fun c => by simp [lensM])
    · exact (PU.polyOf (qs i) (PU.lenX.comp (htM PS.fstP PS.sndP))).congr
        (fun c => by simp [lensM, hi])
  let P : ℕ → Polynomial ℕ := fun i =>
    q + (qs i).comp (3 * Polynomial.X + 3 * q + 1)
  have hP : ∀ i s U, lensM qs q j i s U ≤ (P i).eval s.length := by
    intro i s U
    have hs := decP_len s.length s le_rfl
    have hq := poly_eval_mono q (show (decP s).1.length ≤ s.length by omega)
    have hmb' : mbM q s ≤ 3 * s.length + 3 * q.eval s.length + 1 := by simp only [mbM]; omega
    have e : (P i).eval s.length = q.eval s.length + (qs i).eval (3 * s.length + 3 * q.eval s.length + 1) := by
      simp [P, Polynomial.eval_comp]
    rw [e]
    by_cases hi : i = j
    · subst hi; simp only [lensM, if_true]
      have := poly_eval_mono (qs i) hmb'; omega
    · simp only [lensM, if_neg hi]
      have := poly_eval_mono (qs i) ((tM_len_le q s U).trans hmb'); omega
  obtain ⟨R', hR', e⟩ := altD_pad hleaf (lensM qs q j) hl P hP (j + 1)
  exact ⟨R', P, hR', fun s => (merge_iff R0 qs q j R hRe s).trans (e s true)⟩

/-! ### The general collapse -/

def Sigma_eq_Pi (k : ℕ) : Prop := ∀ L : Language, InSigma k L ↔ InPi k L

theorem Rcol_Sigma {j : ℕ} (H : Sigma_eq_Pi (j + 1)) {R : Language} (hR : InSigma (j + 1) R)
    (q : Polynomial ℕ) (c : Bool) : InSigma (j + 1) (Rcol c R q) := by
  cases c
  · have hnR : InSigma (j + 1) (fun s => ¬ R s) := (H _).2 ((InSigma_iff_compl _ R).1 hR)
    have h1 : InSigma (j + 1) (fun s => ¬ Rcol false R q s) := (Rcol_true_Sigma hnR q).congr (fun s => by
      simp only [Rcol, if_true, Bool.false_eq_true, if_false, not_forall, exists_prop])
    have h2 : InPi (j + 1) (Rcol false R q) :=
      ((InPi_iff_compl _ _).2 h1)
    exact (H _).2 h2
  · exact Rcol_true_Sigma hR q

theorem SigmaLeaf_collapse {j : ℕ} (H : Sigma_eq_Pi (j + 1)) : ∀ m (L : Language),
    (∃ (R : Language) (qs : ℕ → Polynomial ℕ), InSigma (j + 1) R ∧ ∀ x, L x ↔ altQ R qs x m true []) →
    InSigma (j + 1) L := by
  intro m
  induction m with
  | zero =>
    rintro L ⟨R, qs, hR, hL⟩
    exact InSigma.of_reduces ⟨fun x => codeP x [], PS.codePnil, fun x => hL x⟩ hR
  | succ m ih =>
    rintro L ⟨R, qs, hR, hL⟩
    exact ih L ⟨_, _, Rcol_Sigma H hR (qs 0) (innerT m true),
      fun x => (hL x).trans (altQ_collapse R qs x m true [])⟩

/-- **General collapse**: for `k ≥ 1`, `Σ_k = Π_k → PH = Σ_k`. -/
theorem PH_eq_Sigma_of_Sigma_eq_Pi (k : ℕ) (hk : 1 ≤ k) (H : Sigma_eq_Pi k) (L : Language) :
    InPH L ↔ InSigma k L := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  constructor
  · rintro ⟨m, R, qs, hR, hL⟩
    have hR' : InSigma (j + 1) R := ((Sigma0_iff_P R).2 hR).mono (by omega)
    exact SigmaLeaf_collapse H m L ⟨R, qs, hR', hL⟩
  · intro h; exact ⟨_, h⟩

/-- `Σ_k ⊆ Π_k` already gives `Σ_k = Π_k`. -/
theorem Sigma_eq_Pi_of_subset (k : ℕ) (h : ∀ L, InSigma k L → InPi k L) : Sigma_eq_Pi k := by
  intro L
  refine ⟨h L, fun hL => ?_⟩
  have h2 := h _ ((InPi_iff_compl k L).1 hL)
  exact ((InPi_iff_compl k _).1 h2).congr (fun _ => not_not)

/-- Collapse from `Σ_k ⊆ Π_k`. -/
theorem PH_eq_Sigma_of_Sigma_subset_Pi (k : ℕ) (hk : 1 ≤ k) (h : ∀ L, InSigma k L → InPi k L)
    (L : Language) : InPH L ↔ InSigma k L :=
  PH_eq_Sigma_of_Sigma_eq_Pi k hk (Sigma_eq_Pi_of_subset k h) L

end PvnpReal
