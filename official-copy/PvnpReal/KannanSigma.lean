/-
  PvnpReal.KannanSigma — **Kannan's hard language is in Σ₄** (`KanL_Sigma4`), hence in PH.

  `x ∈ KanL k  ↔  ∃T ∀(w,T') ∃(z,w') ∀(z',ib) KanCore(…)` where the inner predicate checks
  * `fT T z ≠ CEval(z,w)`               (T is hard: `z` refutes circuit code `w`),
  * `¬ (T' <_lex T at position lpN ib) ∨ fT T' z' = CEval(z',w')`  (smaller tables are easy),
  * `fT T x = 1`,
  and is polynomial-time (`InP.KanRP`).  All block lengths are polynomials in `|x|`.
-/
import PvnpReal.KannanHard

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing Computability

/-! ### Polytime building blocks -/

theorem PU.gidxP (r : ℕ) {B : List Bool → ℕ} (hB : PU B) :
    ∀ {Z : List Bool → List Bool}, PS Z → PU (fun s => gidx (B s) r (Z s)) := by
  induction r with
  | zero => intro Z _; exact (PU.const 0).congr (fun _ => rfl)
  | succ r ih =>
    intro Z hZ
    exact (PU.add (PU.fst.comp hZ) (PU.mul hB (ih (PS.comp hZ PS.drop)))).congr (fun _ => rfl)

theorem PU.kidxP (r : ℕ) {Z : List Bool → List Bool} (hZ : PS Z) : PU (fun s => kidx r (Z s)) :=
  PU.gidxP r (PU.add (PU.lenX.comp hZ) (PU.const 1)) hZ

theorem bit_eq_one_iff (T : List Bool) (i : ℕ) : NthTM.bit T i = 1 ↔ T.getD i false = true := by
  unfold NthTM.bit
  rw [List.getD_eq_getElem?_getD]
  cases T[i]? with
  | none => simp
  | some b => cases b <;> simp

theorem PU.bitP {T : List Bool → List Bool} {I : List Bool → ℕ} (hT : PS T) (hI : PU I) :
    PU (fun s => NthTM.bit (T s) (I s)) :=
  (PU.nth.comp (PS.append hI (PS.cons false hT))).congr (fun s => by simp only [lpN_rep, lpX_rep])

theorem InP.getDP {T : List Bool → List Bool} {I : List Bool → ℕ} (hT : PS T) (hI : PU I) :
    InP (fun s => (T s).getD (I s) false = true) :=
  (InP.ofPUeq (PU.bitP hT hI) (PU.const 1)).congr (fun _ => bit_eq_one_iff _ _)

theorem InP.fTP (r : ℕ) {T Z : List Bool → List Bool} (hT : PS T) (hZ : PS Z) :
    InP (fun s => fT r (T s) (Z s) = true) :=
  InP.getDP hT (PU.kidxP r hZ)

theorem InP.CEvalPS {Z W : List Bool → List Bool} (hZ : PS Z) (hW : PS W) :
    InP (fun s => CEval (codeP (Z s) (W s))) :=
  InP.CEvalP.compPS (PS.codePF hZ hW)

theorem InP.iffP {P Q : Language} (hP : InP P) (hQ : InP Q) : InP (fun s => P s ↔ Q s) :=
  (InP.union (InP.inter hP hQ) (InP.inter hP.compl hQ.compl)).congr (fun s => by tauto)

theorem InP.prefEqP {A B : List Bool → List Bool} {I : List Bool → ℕ} (hA : PS A) (hB : PS B)
    (hI : PU I) : InP (fun s => ∀ j < I s, (A s).getD j false = (B s).getD j false) := by
  have hb : PS (fun z => (fun j s => if NthTM.bit (A s) j = NthTM.bit (B s) j then [] else [true])
      (lpN z) (lpX z)) :=
    PS.iteEq (PU.bitP (PS.comp PS.drop hA) PU.fst) (PU.bitP (PS.comp PS.drop hB) PU.fst)
      (PS.const []) (PS.const [true])
  have hF := PS.flatRange hI
    (fun j s => if NthTM.bit (A s) j = NthTM.bit (B s) j then [] else [true]) hb
  refine (InP.ofPUeq (PU.lenX.comp hF) (PU.const 0)).congr (fun s => ?_)
  simp only [List.length_flatMap, List.sum_eq_zero_iff, List.mem_map, List.mem_range,
    forall_exists_index, and_imp]
  constructor
  · intro h j hj
    have := h _ j hj rfl
    have e : NthTM.bit (A s) j = NthTM.bit (B s) j := by
      by_contra hne; simp [hne] at this
    have e1 := bit_eq_one_iff (A s) j
    have e2 := bit_eq_one_iff (B s) j
    cases h1 : (A s).getD j false <;> cases h2 : (B s).getD j false <;> simp_all
  · intro h y j hj hy
    subst hy
    have := h j hj
    have e1 := bit_eq_one_iff (A s) j
    have e2 := bit_eq_one_iff (B s) j
    have e : NthTM.bit (A s) j = NthTM.bit (B s) j := by
      unfold NthTM.bit at e1 e2 ⊢
      split_ifs at e1 e2 ⊢ <;> simp_all
    simp [e]

/-! ### Lexicographic order on equal-length tables -/

theorem bool_lt_iff (a b : Bool) : a < b ↔ a = false ∧ b = true := by
  cases a <;> cases b <;> decide

theorem lex_lt_iff : ∀ (A B : List Bool), A.length = B.length →
    (A < B ↔ ∃ i < A.length, (∀ j < i, A.getD j false = B.getD j false) ∧
      A.getD i false = false ∧ B.getD i false = true)
  | [], [], _ => by simp
  | a :: A, b :: B, h => by
    have ih := lex_lt_iff A B (by simpa using h)
    rw [List.cons_lt_cons_iff, bool_lt_iff, ih]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨rfl, i, hi, h1, h2, h3⟩)
      · exact ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero _), by simpa using ha,
          by simpa using hb⟩
      · refine ⟨i + 1, by simp; omega, fun j hj => ?_, by simpa using h2, by simpa using h3⟩
        cases j with
        | zero => rfl
        | succ j => simpa using h1 j (by omega)
    · rintro ⟨i, hi, h1, h2, h3⟩
      cases i with
      | zero => left; exact ⟨by simpa using h2, by simpa using h3⟩
      | succ i =>
        right
        have h0 := h1 0 (by omega)
        simp only [List.getD_cons_zero] at h0
        refine ⟨h0, i, by simp at hi; omega, fun j hj => ?_, by simpa using h2, by simpa using h3⟩
        simpa using h1 (j + 1) (by omega)

/-! ### The predicate and its polynomial-time check -/

/-- The quantifier-free core. -/
def KanCore (r M : ℕ) (x T w T' z w' z' : List Bool) (i : ℕ) : Prop :=
  (fT r T z = true ↔ ¬ CEval (codeP z w)) ∧
  (¬ (i < M ∧ (∀ j < i, T'.getD j false = T.getD j false) ∧ T'.getD i false = false ∧
      T.getD i false = true) ∨ (fT r T' z' = true ↔ CEval (codeP z' w'))) ∧
  fT r T x = true

/-- The Σ₄ matrix: blocks `T w T' z w' z' ib` read from `u` at polynomial offsets. -/
noncomputable def KanR (k : ℕ) : Language := fun s =>
  let x := (decP s).1
  let u := (decP s).2
  let n := x.length
  let M := (n + 1) ^ kR k
  let ℓ := (ellK (k + 1)).eval n
  KanCore (kR k) M x (subL u 0 M) (subL u M ℓ) (subL u (M + ℓ) M) (subL u (M + ℓ + M) n)
    (subL u (M + ℓ + M + n) ℓ) (subL u (M + ℓ + M + n + ℓ) n)
    (lpN (subL u (M + ℓ + M + n + ℓ + n) M))

theorem InP.KanRP (k : ℕ) : InP (KanR k) := by
  have hn : PU (fun s => (decP s).1.length) := PU.lenX.comp PS.fstP
  have hM : PU (fun s => ((decP s).1.length + 1) ^ kR k) :=
    ((PU.poly ((Polynomial.X + 1) ^ kR k)).comp PS.fstP).congr (fun s => by simp)
  have hl : PU (fun s => (ellK (k + 1)).eval (decP s).1.length) := (PU.poly _).comp PS.fstP
  have hB : ∀ {o l : List Bool → ℕ}, PU o → PU l → PS (fun s => subL (decP s).2 (o s) (l s)) :=
    fun ho hl => PS.subL PS.sndP ho hl
  have bT := hB (PU.const 0) hM
  have bW := hB hM hl
  have bT' := hB (hM.add hl) hM
  have bZ := hB ((hM.add hl).add hM) hn
  have bW' := hB (((hM.add hl).add hM).add hn) hl
  have bZ' := hB ((((hM.add hl).add hM).add hn).add hl) hn
  have bI := PU.fst.comp (hB (((((hM.add hl).add hM).add hn).add hl).add hn) hM)
  have c1 := InP.iffP (InP.fTP (kR k) bT bZ) (InP.CEvalPS bZ bW).compl
  have q1 := InP.ofPUle (bI.add (PU.const 1)) hM
  have q2 := InP.prefEqP bT' bT bI
  have q3 := (InP.getDP bT' bI).compl
  have q4 := InP.getDP bT bI
  have c2 := InP.union (InP.inter q1 (InP.inter q2 (InP.inter q3 q4))).compl
    (InP.iffP (InP.fTP (kR k) bT' bZ') (InP.CEvalPS bZ' bW'))
  have c3 := InP.fTP (kR k) bT PS.fstP
  refine (InP.inter c1 (InP.inter c2 c3)).congr (fun s => ?_)
  simp only [KanR, KanCore, Bool.not_eq_true, Nat.add_one_le_iff]

/-! ### Quantifier bookkeeping -/

theorem forall_split (a b : ℕ) (P : List Bool → Prop) :
    (∀ v : List Bool, v.length = a + b → P v) ↔
      ∀ v1 v2 : List Bool, v1.length = a → v2.length = b → P (v1 ++ v2) := by
  constructor
  · intro h v1 v2 h1 h2; exact h _ (by simp [h1, h2])
  · intro h v hv
    have := h (v.take a) (v.drop a) (by simp; omega) (by simp; omega)
    rwa [List.take_append_drop] at this

theorem exists_split (a b : ℕ) (P : List Bool → Prop) :
    (∃ v : List Bool, v.length = a + b ∧ P v) ↔
      ∃ v1 v2 : List Bool, v1.length = a ∧ v2.length = b ∧ P (v1 ++ v2) := by
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v.take a, v.drop a, by simp; omega, by simp; omega, ?_⟩
    rwa [List.take_append_drop]
  · rintro ⟨v1, v2, h1, h2, h⟩; exact ⟨_, by simp [h1, h2], h⟩

theorem subL_at {u : List Bool} (P X S : List Bool) (hu : u = P ++ X ++ S) {o l : ℕ}
    (ho : o = P.length) (hl : l = X.length) : subL u o l = X := by
  subst hu ho hl
  rw [subL_eq _ _ _ (by simp), List.append_assoc, List.drop_left, List.take_left]

theorem KanR_code (k : ℕ) (x T w T' z w' z' ib : List Bool)
    (hT : T.length = (x.length + 1) ^ kR k) (hw : w.length = (ellK (k + 1)).eval x.length)
    (hT' : T'.length = (x.length + 1) ^ kR k) (hz : z.length = x.length)
    (hw' : w'.length = (ellK (k + 1)).eval x.length) (hz' : z'.length = x.length)
    (hib : ib.length = (x.length + 1) ^ kR k) :
    KanR k (codeP x (T ++ (w ++ T') ++ (z ++ w') ++ (z' ++ ib))) ↔
      KanCore (kR k) ((x.length + 1) ^ kR k) x T w T' z w' z' (lpN ib) := by
  simp only [KanR, decP_codeP]
  set u := T ++ (w ++ T') ++ (z ++ w') ++ (z' ++ ib)
  have e1 : subL u 0 ((x.length + 1) ^ kR k) = T :=
    subL_at [] T (w ++ T' ++ z ++ w' ++ z' ++ ib) (by simp [u]) (by simp) hT.symm
  have e2 : subL u ((x.length + 1) ^ kR k) ((ellK (k + 1)).eval x.length) = w :=
    subL_at T w (T' ++ z ++ w' ++ z' ++ ib) (by simp [u]) hT.symm hw.symm
  rw [e1, e2,
    subL_at (T ++ w) T' (z ++ w' ++ z' ++ ib) (by simp [u]) (by simp only [List.length_append, List.length_nil, hT, hw, hT', hz, hw', hz']) hT'.symm,
    subL_at (T ++ w ++ T') z (w' ++ z' ++ ib) (by simp [u]) (by simp only [List.length_append, List.length_nil, hT, hw, hT', hz, hw', hz']) hz.symm,
    subL_at (T ++ w ++ T' ++ z) w' (z' ++ ib) (by simp [u]) (by simp only [List.length_append, List.length_nil, hT, hw, hT', hz, hw', hz']) hw'.symm,
    subL_at (T ++ w ++ T' ++ z ++ w') z' ib (by simp [u]) (by simp only [List.length_append, List.length_nil, hT, hw, hT', hz, hw', hz']) hz'.symm,
    subL_at (T ++ w ++ T' ++ z ++ w' ++ z') ib [] (by simp [u]) (by simp only [List.length_append, List.length_nil, hT, hw, hT', hz, hw', hz']) hib.symm]

/-- Block lengths (innermost block first). -/
noncomputable def kanQs (k : ℕ) : ℕ → Polynomial ℕ := fun j =>
  if j = 3 then (Polynomial.X + 1) ^ kR k
  else if j = 2 then ellK (k + 1) + (Polynomial.X + 1) ^ kR k
  else if j = 1 then Polynomial.X + ellK (k + 1)
  else Polynomial.X + (Polynomial.X + 1) ^ kR k

theorem KanL_iff_altQ (k : ℕ) (x : List Bool) : KanL k x ↔ altQ (KanR k) (kanQs k) x 4 true [] := by
  set n := x.length with hn
  set M := (n + 1) ^ kR k with hM
  set ℓ := (ellK (k + 1)).eval n with hℓ
  have hq3 : ((kanQs k) 3).eval n = M := by simp [kanQs, hM]
  have hq2 : ((kanQs k) 2).eval n = ℓ + M := by simp [kanQs, hM, hℓ]
  have hq1 : ((kanQs k) 1).eval n = n + ℓ := by simp [kanQs, hℓ]
  have hq0 : ((kanQs k) 0).eval n = n + M := by simp [kanQs, hM]
  show _ ↔ ∃ v1 : List Bool, v1.length = ((kanQs k) 3).eval x.length ∧
    ∀ v2 : List Bool, v2.length = ((kanQs k) 2).eval x.length →
      ∃ v3 : List Bool, v3.length = ((kanQs k) 1).eval x.length ∧
        ∀ v4 : List Bool, v4.length = ((kanQs k) 0).eval x.length →
          KanR k (codeP x ([] ++ v1 ++ v2 ++ v3 ++ v4))
  rw [← hn, hq3, hq2, hq1, hq0]
  simp only [List.nil_append]
  simp only [forall_split, exists_split]
  have key : ∀ T w T' z w' z' ib : List Bool, T.length = M → w.length = ℓ → T'.length = M →
      z.length = n → w'.length = ℓ → z'.length = n → ib.length = M →
      (KanR k (codeP x (T ++ (w ++ T') ++ (z ++ w') ++ (z' ++ ib))) ↔
        KanCore (kR k) M x T w T' z w' z' (lpN ib)) := fun T w T' z w' z' ib a b c d e f g =>
    KanR_code k x T w T' z w' z' ib a b c d e f g
  have hlex : ∀ T' T : List Bool, T'.length = M → T.length = M →
      (T' < T ↔ ∃ i < M, (∀ j < i, T'.getD j false = T.getD j false) ∧
        T'.getD i false = false ∧ T.getD i false = true) := by
    intro T' T h1 h2
    rw [lex_lt_iff T' T (h1.trans h2.symm), h1]
  have hib : ∀ i < M, ∃ ib : List Bool, ib.length = M ∧ lpN ib = i := fun i hi =>
    ⟨List.replicate i true ++ false :: List.replicate (M - i - 1) false, by simp; omega, lpN_rep _ _⟩
  constructor
  · rintro ⟨T, hTL, hTH, hTmin, hfx⟩
    refine ⟨T, hTL, fun w T' hw hT' => ?_⟩
    obtain ⟨z, hz, hzf⟩ := hTH w hw
    have hw' : ∃ w' : List Bool, w'.length = ℓ ∧ (T' < T → ∀ z', z'.length = n →
        (fT (kR k) T' z' = true ↔ CEval (codeP z' w'))) := by
      by_cases hlt : T' < T
      · have hnh := hTmin T' hT' hlt
        unfold KHard at hnh
        by_contra hc
        apply hnh
        intro w' hw'
        by_contra hc2
        apply hc ⟨w', hw', fun _ z' hz' => ?_⟩
        by_contra hc3
        exact hc2 ⟨z', hz', by tauto⟩
      · exact ⟨List.replicate ℓ false, by simp, fun h => absurd h hlt⟩
    obtain ⟨w', hw'L, hw'f⟩ := hw'
    refine ⟨z, w', hz, hw'L, fun z' ib hz' hibL => ?_⟩
    rw [key T w T' z w' z' ib hTL hw hT' hz hw'L hz' hibL]
    refine ⟨hzf, ?_, hfx⟩
    by_cases hlt : T' < T
    · exact Or.inr (hw'f hlt z' hz')
    · left
      rintro ⟨hi, h1, h2, h3⟩
      exact hlt ((hlex T' T hT' hTL).2 ⟨_, hi, h1, h2, h3⟩)
  · rintro ⟨T, hTL, hAll⟩
    have hdef := hAll (List.replicate ℓ false) T (by simp) hTL
    obtain ⟨z0, w0, hz0, hw0, h0⟩ := hdef
    have c0 := (key T _ T z0 w0 (List.replicate n false) (List.replicate M false) hTL (by simp) hTL
      hz0 hw0 (by simp) (by simp)).1 (h0 _ _ (by simp) (by simp))
    refine ⟨T, hTL, fun w hw => ?_, fun T' hT' hlt hH => ?_, c0.2.2⟩
    · obtain ⟨z, w', hz, hw', h⟩ := hAll w T hw hTL
      have c := (key T w T z w' (List.replicate n false) (List.replicate M false) hTL hw hTL hz hw'
        (by simp) (by simp)).1 (h _ _ (by simp) (by simp))
      exact ⟨z, hz, c.1⟩
    · obtain ⟨i, hi, h1, h2, h3⟩ := (hlex T' T hT' hTL).1 hlt
      obtain ⟨ib, hibL, hibN⟩ := hib i hi
      obtain ⟨z, w', hz, hw', h⟩ := hAll (List.replicate ℓ false) T' (by simp) hT'
      have hall : ∀ z' : List Bool, z'.length = n → (fT (kR k) T' z' = true ↔ CEval (codeP z' w')) := by
        intro z' hz'
        have c := (key T _ T' z w' z' ib hTL (by simp) hT' hz hw' hz' hibL).1 (h _ _ hz' hibL)
        rcases c.2.1 with hc | hc
        · exact absurd ⟨hibN ▸ hi, hibN ▸ h1, hibN ▸ h2, hibN ▸ h3⟩ hc
        · exact hc
      obtain ⟨z', hz', hz'f⟩ := hH w' hw'
      have := hall z' hz'
      tauto

/-- **Kannan's language is in Σ₄.** -/
theorem KanL_Sigma4 (k : ℕ) : InSigma 4 (KanL k) :=
  ⟨KanR k, kanQs k, InP.KanRP k, KanL_iff_altQ k⟩

theorem KanL_PH (k : ℕ) : InPH (KanL k) := ⟨4, KanL_Sigma4 k⟩

/-- **Kannan, PH form**: for every `k` there is a language in Σ₄ (⊆ PH) with no circuits of size
`n^k` for all large `n`. -/
theorem kannan_Sigma4 (k : ℕ) : ∃ L, InSigma 4 L ∧ ∃ N, ∀ n ≥ N,
    ¬ HasCircuit n (n ^ k) (fun x : Fin n → Bool => @decide (L (List.ofFn x)) (Classical.dec _)) := by
  obtain ⟨N, hN⟩ := KanL_hard k
  exact ⟨KanL k, KanL_Sigma4 k, N, fun n hn => by convert hN n hn⟩

end PvnpReal
