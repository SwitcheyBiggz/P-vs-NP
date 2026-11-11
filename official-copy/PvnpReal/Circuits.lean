/-
  PvnpReal.Circuits — Boolean circuits and the **counting lemma** (Shannon/Muller):
  most Boolean functions on `n` bits need large circuits.

  A circuit with `n` inputs and `s` gates is a straight-line program: gate `i` has an operation
  (`AND`, `OR`, `NOT`) and two wire indices among the `n + s` wires; a gate may only read wires
  with smaller index (a forward reference reads `false`), so every such object is a well-formed
  acyclic circuit. The output is a chosen wire (or the constant `false`).
-/
import PvnpReal.Hierarchy

namespace PvnpReal

open Classical

/-- Boolean functions on `n` bits. -/
abbrev BFun (n : ℕ) := (Fin n → Bool) → Bool

/-- A gate on `w` wires: operation (`0 = AND`, `1 = OR`, `2 = NOT` of the first input) and two inputs. -/
abbrev BGate (w : ℕ) := Fin 3 × Fin w × Fin w

/-- A circuit with `n` inputs and `s` gates (plus the output wire index; `n + s` means `false`). -/
abbrev BCirc (n s : ℕ) := (Fin s → BGate (n + s)) × Fin (n + s + 1)

def opApply : Fin 3 → Bool → Bool → Bool
  | 0, a, b => a && b
  | 1, a, b => a || b
  | _, a, _ => !a

/-- Value of wire `j` (inputs are wires `0..n-1`, gate `i` is wire `n + i`). -/
def wire {n s : ℕ} (C : Fin s → BGate (n + s)) (x : Fin n → Bool) (j : ℕ) : Bool :=
  if hj : j < n then x ⟨j, hj⟩ else
    if hs : j - n < s then
      opApply (C ⟨j - n, hs⟩).1
        (if h : ((C ⟨j - n, hs⟩).2.1 : ℕ) < j then wire C x (C ⟨j - n, hs⟩).2.1 else false)
        (if h : ((C ⟨j - n, hs⟩).2.2 : ℕ) < j then wire C x (C ⟨j - n, hs⟩).2.2 else false)
    else false
termination_by j

/-- The function computed by a circuit. -/
def BCirc.eval {n s : ℕ} (C : BCirc n s) : BFun n := fun x =>
  if (C.2 : ℕ) < n + s then wire C.1 x C.2 else false

/-- `f` has a circuit with at most `s` gates. -/
def HasCircuit (n s : ℕ) (f : BFun n) : Prop := ∃ s' ≤ s, ∃ C : BCirc n s', C.eval = f

theorem HasCircuit.mono {n s s' : ℕ} {f : BFun n} (h : s ≤ s') (hf : HasCircuit n s f) :
    HasCircuit n s' f := by
  obtain ⟨s'', hs, C, hC⟩ := hf
  exact ⟨s'', hs.trans h, C, hC⟩

theorem card_circuit (n s : ℕ) : Fintype.card (BCirc n s) = (3 * (n + s) ^ 2) ^ s * (n + s + 1) := by
  simp [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_two, mul_assoc]

theorem card_bfun (n : ℕ) : Fintype.card (BFun n) = 2 ^ 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Number of circuits of size `s'`, monotone in `s'`. -/
theorem circ_mono {n s' s : ℕ} (h : s' ≤ s) :
    (3 * (n + s') ^ 2) ^ s' * (n + s' + 1) ≤ (3 * (n + s) ^ 2) ^ s * (n + s + 1) := by
  rcases Nat.eq_zero_or_pos (n + s) with h0 | h0
  · have : s' = s := by omega
    subst this; rfl
  apply Nat.mul_le_mul _ (by omega)
  calc (3 * (n + s') ^ 2) ^ s' ≤ (3 * (n + s) ^ 2) ^ s' :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) _
    _ ≤ (3 * (n + s) ^ 2) ^ s := Nat.pow_le_pow_right (by positivity) h

/-- **Counting lemma**: at most `(s+1)·(3(n+s)²)^s·(n+s+1)` functions have circuits of size `≤ s`. -/
theorem card_hasCircuit_le (n s : ℕ) :
    (Finset.univ.filter (HasCircuit n s)).card ≤ (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s + 1)) := by
  have hsub : Finset.univ.filter (HasCircuit n s) ⊆
      (Finset.range (s + 1)).biUnion (fun s' => Finset.univ.image (BCirc.eval (n := n) (s := s'))) := by
    intro f hf
    obtain ⟨s', hs', C, hC⟩ := (Finset.mem_filter.1 hf).2
    exact Finset.mem_biUnion.2 ⟨s', Finset.mem_range.2 (by omega),
      Finset.mem_image.2 ⟨C, Finset.mem_univ _, hC⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ s' ∈ Finset.range (s + 1), (Finset.univ.image (BCirc.eval (n := n) (s := s'))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ s' ∈ Finset.range (s + 1), (3 * (n + s) ^ 2) ^ s * (n + s + 1) := by
        apply Finset.sum_le_sum
        intro s' hs'
        calc _ ≤ (Finset.univ : Finset (BCirc n s')).card := Finset.card_image_le
          _ = _ := by rw [Finset.card_univ, card_circuit]
          _ ≤ _ := circ_mono (by simpa [Nat.lt_succ_iff] using hs')
    _ = _ := by simp

/-- If there are fewer small circuits than functions, some function has no small circuit. -/
theorem exists_hard {n s : ℕ} (h : (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s + 1)) < 2 ^ 2 ^ n) :
    ∃ f : BFun n, ¬ HasCircuit n s f := by
  by_contra hc
  push_neg at hc
  have : (Finset.univ.filter (HasCircuit n s)) = Finset.univ := by
    ext f; simp [hc f]
  have h1 := card_hasCircuit_le n s
  rw [this, Finset.card_univ, card_bfun] at h1
  omega

/-- Clean form of the count: if `n + s + 1 ≤ 2ⁿ`, the count is at most `2^((2n+2)(s+1))`. -/
theorem count_le_pow {n s : ℕ} (hs : n + s + 1 ≤ 2 ^ n) :
    (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s + 1)) ≤ 2 ^ ((2 * n + 2) * (s + 1)) := by
  have h3 : 3 * (n + s) ^ 2 ≤ 2 ^ (2 * n + 2) := by
    have : (n + s) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (by omega) _
    calc 3 * (n + s) ^ 2 ≤ 4 * (2 ^ n) ^ 2 := by omega
      _ = 2 ^ (2 * n + 2) := by rw [← pow_mul, pow_add]; ring
  have h4 : (3 * (n + s) ^ 2) ^ s ≤ 2 ^ ((2 * n + 2) * s) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h3 _
  have h5 : s + 1 ≤ 2 ^ n := by omega
  calc (s + 1) * ((3 * (n + s) ^ 2) ^ s * (n + s + 1))
      ≤ 2 ^ n * (2 ^ ((2 * n + 2) * s) * 2 ^ n) :=
        Nat.mul_le_mul h5 (Nat.mul_le_mul h4 hs)
    _ ≤ 2 ^ ((2 * n + 2) * (s + 1)) := by
        rw [← pow_add, ← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- **Most functions are hard**: if `n + s + 1 ≤ 2ⁿ`, the number of functions with circuits of
size `≤ s` is at most `2^((2n+2)(s+1))` (out of `2^(2ⁿ)`). -/
theorem card_easy_le {n s : ℕ} (hs : n + s + 1 ≤ 2 ^ n) :
    (Finset.univ.filter (HasCircuit n s)).card ≤ 2 ^ ((2 * n + 2) * (s + 1)) :=
  (card_hasCircuit_le n s).trans (count_le_pow hs)

/-- **Shannon-type lower bound**: if `(2n+2)(s+1) < 2ⁿ`, some `n`-bit function needs more than
`s` gates. -/
theorem exists_hard_of_lt {n s : ℕ} (h : (2 * n + 2) * (s + 1) < 2 ^ n) :
    ∃ f : BFun n, ¬ HasCircuit n s f := by
  have hs : n + s + 1 ≤ 2 ^ n := by nlinarith
  apply exists_hard
  calc _ ≤ 2 ^ ((2 * n + 2) * (s + 1)) := count_le_pow hs
    _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by omega) h

/-- `(2n+2)(n^k+1) < 2ⁿ` for all large `n`. -/
theorem poly_lt_two_pow (k : ℕ) : ∃ N, ∀ n ≥ N, (2 * n + 2) * (n ^ k + 1) + 1 ≤ 2 ^ n := by
  obtain ⟨N, hN⟩ := poly_le_two_pow_eventually
    ((Polynomial.C 2 * Polynomial.X + Polynomial.C 2) * (Polynomial.X ^ k + 1) + 1)
  exact ⟨N, fun n hn => by simpa using hN n hn⟩

/-- **Superpolynomial lower bounds exist (non-constructively)**: for every `k`, for all large `n`
some `n`-bit function has no circuit with `≤ nᵏ` gates. -/
theorem exists_superpoly_hard (k : ℕ) : ∃ N, ∀ n ≥ N, ∃ f : BFun n, ¬ HasCircuit n (n ^ k) f := by
  obtain ⟨N, hN⟩ := poly_lt_two_pow k
  exact ⟨N, fun n hn => exists_hard_of_lt (by have := hN n hn; omega)⟩

/-- **Most functions need superpolynomial circuits**: for large `n`, at most half of all `n`-bit
functions have circuits of size `≤ nᵏ` (indeed at most a `2^{-(2ⁿ - (2n+2)(nᵏ+1))}` fraction). -/
theorem easy_le_half (k : ℕ) : ∃ N, ∀ n ≥ N,
    2 * (Finset.univ.filter (HasCircuit n (n ^ k))).card ≤ 2 ^ 2 ^ n := by
  obtain ⟨N, hN⟩ := poly_lt_two_pow k
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  have hs : n + n ^ k + 1 ≤ 2 ^ n := by
    have e : (2 * n + 2) * (n ^ k + 1) = 2 * (n * n ^ k) + 2 * n + 2 * n ^ k + 2 := by ring
    omega
  calc 2 * _ ≤ 2 * 2 ^ ((2 * n + 2) * (n ^ k + 1)) := Nat.mul_le_mul_left _ (card_easy_le hs)
    _ = 2 ^ ((2 * n + 2) * (n ^ k + 1) + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)

end PvnpReal

namespace PvnpReal

/-- Sanity check (the model is not vacuous): each input variable has a circuit with `0` gates. -/
theorem hasCircuit_proj (n : ℕ) (i : Fin n) : HasCircuit n 0 (fun x => x i) := by
  refine ⟨0, le_refl _, (fun j => j.elim0, ⟨i, by omega⟩), ?_⟩
  funext x
  simp only [BCirc.eval, Nat.add_zero, show (i : ℕ) < n from i.2, if_true]
  rw [wire, dif_pos i.2]

/-- Sanity check: `x₀ ∧ x₁` has a circuit with one gate. -/
theorem hasCircuit_and : HasCircuit 2 1 (fun x => x 0 && x 1) := by
  refine ⟨1, le_refl _, (fun _ => (0, 0, 1), 2), ?_⟩
  funext x
  simp only [BCirc.eval]
  rw [if_pos (by decide), wire, dif_neg (by decide), dif_pos (by decide)]
  simp only [opApply]
  rw [dif_pos (by decide), dif_pos (by decide), wire, dif_pos (by decide), wire, dif_pos (by decide)]
  rfl

end PvnpReal
