/-
  PvnpReal.KannanHard — the combinatorial half of **Kannan's theorem**.

  For fixed `k` (with `K = k+1`, `r = 2K+2`) and input length `n`, a *table* `T` of length
  `(n+1)^r` defines the Boolean function `fT r T z = T[idx z]`, where `idx z` reads the first `r`
  unary blocks of `z` as base-`(n+1)` digits.  `KHard r ℓ n T` says that no circuit code `w` of
  length `ℓ = ellK K (n)` (enough to encode every circuit with `≤ n^K` gates, see `encC`) agrees
  with `fT r T` on all `n`-bit inputs.

  * `exists_hard_table`: a counting argument (`2^{A^r} > 2^ℓ` functions on a grid of inputs) gives a
    hard table once `ℓ < (n / r)^r`, which holds for large `n` (`ellK_lt`).
  * `KanL k`: `x` is in iff the **lexicographically first** hard table `T` has `fT r T x = true`.
  * `KanL_hard`: for all large `n`, `KanL k` has no circuit with `≤ n^k` gates.

  The Σ₄ upper bound for `KanL k` is in `KannanSigma.lean`.
-/
import PvnpReal.PpolyUndec
import Mathlib.Data.List.Lex

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing Computability

/-! ### Base-`B` digits read from unary blocks -/

/-- Digit sum `a₀ + B·(a₁ + B·(…))`. -/
def dsum (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + B * dsum B l

/-- The first `r` unary blocks of `z`, read as base-`B` digits. -/
def gidx (B : ℕ) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | r + 1, z => lpN z + B * gidx B r (lpX z)

/-- The table index of an input `z` (base `|z|+1`, `r` digits). -/
def kidx (r : ℕ) (z : List Bool) : ℕ := gidx (z.length + 1) r z

/-- The Boolean function defined by a table. -/
def fT (r : ℕ) (T z : List Bool) : Bool := T.getD (kidx r z) false

theorem gidx_encNs (B : ℕ) (l : List ℕ) (rest : List Bool) :
    gidx B l.length (encNs l ++ rest) = dsum B l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.length_cons, gidx, lpN_encNs, lpX_encNs, ih, dsum]

theorem dsum_lt (B : ℕ) (l : List ℕ) (h : ∀ a ∈ l, a < B) : dsum B l < B ^ l.length := by
  induction l with
  | nil => simp [dsum]
  | cons a l ih =>
    have ha := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    simp only [dsum, List.length_cons, pow_succ]
    calc a + B * dsum B l < B + B * dsum B l := by omega
      _ = B * (dsum B l + 1) := by ring
      _ ≤ B * B ^ l.length := Nat.mul_le_mul_left _ h2
      _ = B ^ l.length * B := by ring

theorem dsum_inj (B : ℕ) : ∀ (l l' : List ℕ), l.length = l'.length → (∀ a ∈ l, a < B) →
    (∀ a ∈ l', a < B) → dsum B l = dsum B l' → l = l'
  | [], [], _, _, _, _ => rfl
  | a :: l, a' :: l', hl, h, h', e => by
    have ha := h a (by simp)
    have ha' := h' a' (by simp)
    have hB : 0 < B := by omega
    simp only [dsum] at e
    have e1 : a = a' := by
      have := congrArg (· % B) e
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
      exact this
    have e2 : dsum B l = dsum B l' := by
      have := congrArg (· / B) e
      simp only [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha',
        zero_add] at this
      exact this
    rw [e1, dsum_inj B l l' (by simpa using hl) (fun b hb => h b (by simp [hb]))
      (fun b hb => h' b (by simp [hb])) e2]

/-! ### The grid of inputs -/

/-- Digits of a grid point. -/
def gLst {r A : ℕ} (a : Fin r → Fin A) : List ℕ := List.ofFn (fun j => (a j : ℕ))

/-- The input of length `n` encoding a grid point. -/
def gInp (n : ℕ) {r A : ℕ} (a : Fin r → Fin A) : List Bool :=
  encNs (gLst a) ++ List.replicate (n - (encNs (gLst a)).length) false

theorem gLst_len {r A : ℕ} (a : Fin r → Fin A) : (encNs (gLst a)).length ≤ r * A := by
  unfold encNs
  rw [List.length_flatMap]
  have := List.sum_le_length_nsmul ((gLst a).map (fun d => (List.replicate d true ++ [false]).length)) A
    (by
      intro y hy
      simp only [gLst, List.map_ofFn, List.mem_ofFn, Function.comp_apply] at hy
      obtain ⟨j, rfl⟩ := hy
      have := (a j).2
      simp)
  simpa [gLst] using this

theorem gInp_length {n r A : ℕ} (hA : r * A ≤ n) (a : Fin r → Fin A) : (gInp n a).length = n := by
  have := gLst_len a
  simp only [gInp, List.length_append, List.length_replicate]; omega

theorem kidx_gInp {n r A : ℕ} (hA : r * A ≤ n) (a : Fin r → Fin A) :
    kidx r (gInp n a) = dsum (n + 1) (gLst a) := by
  unfold kidx
  rw [gInp_length hA]
  have := gidx_encNs (n + 1) (gLst a) (List.replicate (n - (encNs (gLst a)).length) false)
  simp only [gLst, List.length_ofFn] at this
  exact this

theorem gLst_lt {n r A : ℕ} (hA : A ≤ n) (a : Fin r → Fin A) : ∀ d ∈ gLst a, d < n + 1 := by
  intro d hd
  simp only [gLst, List.mem_ofFn] at hd
  obtain ⟨j, rfl⟩ := hd
  have := (a j).2; omega

theorem gval_inj {n r A : ℕ} (hA : A ≤ n) {a a' : Fin r → Fin A}
    (e : dsum (n + 1) (gLst a) = dsum (n + 1) (gLst a')) : a = a' := by
  have := dsum_inj (n + 1) _ _ (by simp [gLst]) (gLst_lt hA a) (gLst_lt hA a') e
  funext j
  apply Fin.ext
  have h2 := congrArg (fun l => l.getD j 0) this
  simpa [gLst] using h2

/-! ### Hard tables -/

/-- Circuit-code length bound for `≤ n^K` gates (as in `InPpoly_of_circ`). -/
noncomputable def ellK (K : ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.X ^ K + 1) + (Polynomial.X ^ K + 1) +
    Polynomial.X ^ K * (2 * (Polynomial.X + Polynomial.X ^ K) + 5)

theorem ellK_eval (K n : ℕ) :
    (ellK K).eval n = (n + n ^ K + 1) + (n ^ K + 1) + n ^ K * (2 * (n + n ^ K) + 5) := by
  simp [ellK]

/-- `T` is hard: no code `w` of length `ℓ` makes `CEval` agree with `fT r T` on all `n`-bit inputs. -/
def KHard (r ℓ n : ℕ) (T : List Bool) : Prop :=
  ∀ w : List Bool, w.length = ℓ → ∃ z : List Bool, z.length = n ∧
    (fT r T z = true ↔ ¬ CEval (codeP z w))

/-- **Counting**: a hard table exists once `ℓ < (n / r)^r`. -/
theorem exists_hard_table {r n ℓ : ℕ} (hℓ : ℓ < (n / r) ^ r) :
    ∃ T : List Bool, T.length = (n + 1) ^ r ∧ KHard r ℓ n T := by
  classical
  by_contra hne
  have key : ∀ T : List Bool, T.length = (n + 1) ^ r → ∃ w : List Bool, w.length = ℓ ∧
      ∀ z : List Bool, z.length = n → (fT r T z = true ↔ CEval (codeP z w)) := by
    intro T hT
    by_contra h
    apply hne ⟨T, hT, fun w hw => ?_⟩
    by_contra h2
    apply h ⟨w, hw, fun z hz => ?_⟩
    by_contra h3
    exact h2 ⟨z, hz, by tauto⟩
  choose W hW hWs using key
  set A := n / r
  have hrA : r * A ≤ n := Nat.mul_div_le n r
  have hAn : A ≤ n := Nat.div_le_self n r
  let Tg : ((Fin r → Fin A) → Bool) → List Bool := fun g =>
    List.ofFn (fun i : Fin ((n + 1) ^ r) => decide (∃ a, dsum (n + 1) (gLst a) = i ∧ g a = true))
  have hTg : ∀ g, (Tg g).length = (n + 1) ^ r := fun g => by simp [Tg]
  have hfT : ∀ g a, fT r (Tg g) (gInp n a) = g a := by
    intro g a
    have hlt : dsum (n + 1) (gLst a) < (n + 1) ^ r := by
      have := dsum_lt (n + 1) (gLst a) (gLst_lt hAn a)
      simpa [gLst] using this
    simp only [fT, kidx_gInp hrA, Tg]
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn]
    by_cases hg : g a = true
    · simp only [hg, decide_eq_true_eq]; exact ⟨a, rfl, hg⟩
    · simp only [hg, decide_eq_false_iff_not, not_exists, not_and]
      intro a' e h'
      exact hg (gval_inj hAn e ▸ h')
  let Φ : ((Fin r → Fin A) → Bool) → List.Vector Bool ℓ := fun g => ⟨W (Tg g) (hTg g), hW _ _⟩
  have hinj : Function.Injective Φ := by
    intro g g' e
    have e' : W (Tg g) (hTg g) = W (Tg g') (hTg g') := congrArg Subtype.val e
    funext a
    have h1 := hWs (Tg g) (hTg g) (gInp n a) (gInp_length hrA a)
    have h2 := hWs (Tg g') (hTg g') (gInp n a) (gInp_length hrA a)
    rw [hfT, e'] at h1
    rw [hfT] at h2
    cases hga : g a <;> cases hga' : g' a <;> simp_all
  have hc := Fintype.card_le_of_injective Φ hinj
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, card_vector] at hc
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hc
  omega

/-- For large `n`, codes of `≤ n^K`-gate circuits are shorter than the grid: `ℓ < (n / r)^r`. -/
theorem ellK_lt (K : ℕ) (hK : 1 ≤ K) : ∃ N, ∀ n ≥ N, (ellK K).eval n < (n / (2 * K + 2)) ^ (2 * K + 2) := by
  set r := 2 * K + 2 with hr
  refine ⟨14 * (2 * r) ^ r + 2 * r + 1, fun n hn => ?_⟩
  rw [ellK_eval]
  set S := n ^ K with hSdef
  have hn1 : 1 ≤ n := by omega
  have hS : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
  have hnS : n ≤ S := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ K := Nat.pow_le_pow_right (by omega) hK
  have h1 : (n + S + 1) + (S + 1) + S * (2 * (n + S) + 5) ≤ 14 * S ^ 2 := by nlinarith
  set A := n / r with hA
  have hr0 : 0 < r := by omega
  have hlt : n < r * (A + 1) := Nat.lt_mul_div_succ n hr0
  have hA2 : n ≤ 2 * r * A := by
    rw [mul_add, mul_one] at hlt
    rw [mul_assoc]
    have h0 : 0 ≤ 14 * (2 * r) ^ r := Nat.zero_le _
    generalize r * A = P at hlt ⊢
    generalize 14 * (2 * r) ^ r = Q at hn
    omega
  have hnr : n ^ r = n ^ 2 * S ^ 2 := by
    rw [hSdef, ← pow_mul, ← pow_add]; congr 1; omega
  have hpow : n ^ r ≤ (2 * r) ^ r * A ^ r := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hA2 r
  have hn2 : 14 * (2 * r) ^ r < n ^ 2 := by nlinarith
  by_contra hcon
  replace hcon := not_lt.1 hcon
  have hP : 0 < (2 * r) ^ r := by positivity
  have e1 : (2 * r) ^ r * A ^ r ≤ (2 * r) ^ r * (14 * S ^ 2) :=
    Nat.mul_le_mul_left _ (hcon.trans' (le_of_eq rfl) |>.trans' (by omega) |> fun h => h.trans h1)
  have e2 : 14 * (2 * r) ^ r * S ^ 2 < n ^ 2 * S ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hn2 (by positivity)
  nlinarith

/-! ### The language -/

/-- Parameters: `K = k+1` gates exponent, `r = 2K+2` digits. -/
def kR (k : ℕ) : ℕ := 2 * (k + 1) + 2

/-- **Kannan's hard language** (for exponent `k`): `x` is in iff the lexicographically first hard
table of length `(|x|+1)^r` has a `1` at position `idx x`. -/
def KanL (k : ℕ) : Language := fun x =>
  ∃ T : List Bool, T.length = (x.length + 1) ^ kR k ∧
    KHard (kR k) ((ellK (k + 1)).eval x.length) x.length T ∧
    (∀ T' : List Bool, T'.length = (x.length + 1) ^ kR k → T' < T →
      ¬ KHard (kR k) ((ellK (k + 1)).eval x.length) x.length T') ∧
    fT (kR k) T x = true

open scoped Classical in
/-- **Circuit lower bound**: for every `k`, for all large `n`, `KanL k` has no circuit with `≤ n^k`
gates on `n`-bit inputs. -/
theorem KanL_hard (k : ℕ) : ∃ N, ∀ n ≥ N,
    ¬ HasCircuit n (n ^ k) (fun x : Fin n → Bool => decide (KanL k (List.ofFn x))) := by
  classical
  obtain ⟨N, hN⟩ := ellK_lt (k + 1) (by omega)
  refine ⟨N + 1, fun n hn => ?_⟩
  set r := kR k with hr
  set ℓ := (ellK (k + 1)).eval n with hℓ
  set M := (n + 1) ^ r with hM
  obtain ⟨T0, hT0, hH0⟩ := exists_hard_table (r := r) (n := n) (ℓ := ℓ)
    (by have := hN n (by omega); simpa [hr, kR] using this)
  obtain ⟨S, hmem⟩ : ∃ S : Finset (List Bool), ∀ T, T ∈ S ↔ T.length = M ∧ KHard r ℓ n T := by
    refine ⟨(Finset.univ.filter (fun v : List.Vector Bool M => KHard r ℓ n v.toList)).image
      List.Vector.toList, fun T => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, h, rfl⟩; exact ⟨v.toList_length, h⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨T, h1⟩, h2, rfl⟩
  have hne : S.Nonempty := ⟨T0, (hmem T0).2 ⟨hT0, hH0⟩⟩
  set Tm := S.min' hne
  obtain ⟨hTmL, hTmH⟩ := (hmem Tm).1 (S.min'_mem hne)
  have hiff : ∀ y : List Bool, y.length = n → (KanL k y ↔ fT r Tm y = true) := by
    intro y hy
    unfold KanL
    rw [hy]
    constructor
    · rintro ⟨T, hTL, hTH, hTmin, hf⟩
      have hle : Tm ≤ T := S.min'_le T ((hmem T).2 ⟨hTL, hTH⟩)
      rcases lt_or_eq_of_le hle with h | h
      · exact absurd hTmH (hTmin Tm hTmL h)
      · rw [h]; exact hf
    · intro hf
      refine ⟨Tm, hTmL, hTmH, fun T' hT' hlt hH => ?_, hf⟩
      have := S.min'_le T' ((hmem T').2 ⟨hT', hH⟩)
      exact absurd hlt (not_lt.2 this)
  rintro ⟨s, hs, C, hC⟩
  have hn1 : 1 ≤ n := by omega
  have hsK : s ≤ n ^ (k + 1) := hs.trans (Nat.pow_le_pow_right hn1 (by omega))
  have hlen : (encC C).length ≤ ℓ := by
    have := encC_length_le C
    rw [hℓ, ellK_eval]
    have : s * (2 * (n + s) + 5) ≤ n ^ (k + 1) * (2 * (n + n ^ (k + 1)) + 5) :=
      Nat.mul_le_mul hsK (by omega)
    omega
  set w := encC C ++ List.replicate (ℓ - (encC C).length) false
  have hw : w.length = ℓ := by simp [w]; omega
  obtain ⟨z, hz, hzf⟩ := hTmH w hw
  subst hz
  have hx : List.ofFn (fun i : Fin z.length => z[i]) = z := List.ofFn_getElem
  have hce := CEval_code C (fun i : Fin z.length => z[i]) (List.replicate (ℓ - (encC C).length) false)
  rw [hx, hC] at hce
  have := hiff z rfl
  simp only [hx, decide_eq_true_eq] at hce
  rw [show codeP z w = codeP z (encC C ++ List.replicate (ℓ - (encC C).length) false) from rfl] at hzf
  tauto

end PvnpReal
