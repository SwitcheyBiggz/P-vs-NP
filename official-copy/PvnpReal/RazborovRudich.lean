/-
  PvnpReal.RazborovRudich — pseudorandom function families and the **conditional
  Razborov–Rudich theorem**.

  * `PRF`: for every input length `n`, seeds `z : Fin (seedLen n) → Bool` (polynomial seed length)
    and functions `G n z : BFun n`, each computed by a circuit with `≤ nᵏ` gates.
  * `adv F D n`: the distinguishing advantage `|Pr_z[D(G z)] − Pr_f[D f]|` of a test `D` that sees
    the whole truth table (in `ℚ`, by exact counting).
  * `Secure Cls F`: every test in class `Cls` has advantage `< 2^{-cn}` for large `n`, for every `c`.
    Classes used: `Constructive` (truth table decidable in time poly(2ⁿ) = 2^{O(n)}) and
    `ConstructiveC` (truth table decidable by circuits of size 2^{O(n)}).

  Proven (hypothesis, not axiom): **`razborov_rudich`** — if a PRF secure against
  `Constructive` tests exists, no property is `Natural`; **`razborov_rudich_circuit`** — the same
  for `ConstructiveC` tests and `NaturalC` properties. Also **`ttab_injective`**.

  Scope (honest): the PRF here is parameterized directly by the input length `n` of the
  function, with security against 2^{O(n)} tests and advantage 2^{-cn}. The textbook statement
  (PRFs with seed length `m` secure against `2^{m^ε}`-size circuits, rescaled by restricting
  inputs) is not formalized; nor is any keyed-circuit form `G n z x = C_n(z, x)`
  (that would imply our per-seed circuit condition via a restriction lemma, not proven here).
  Existence of secure PRFs is NOT proven or assumed as an axiom; it is an open hypothesis.
  Nothing here bears on P vs NP.
-/
import PvnpReal.NaturalProofs

namespace PvnpReal

open Classical

/-! ### Truth tables are faithful -/

/-- The bits of an index `i < 2ⁿ`, as an input point. -/
def bitsOf (n : ℕ) (i : Fin (2 ^ n)) : Fin n → Bool := fun j => Nat.testBit i j

theorem bitsOf_injective (n : ℕ) : Function.Injective (bitsOf n) := by
  intro i i' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact congrFun h ⟨j, hj⟩
  · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le i.2 hle),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le i'.2 hle)]

theorem bitsOf_bijective (n : ℕ) : Function.Bijective (bitsOf n) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨bitsOf_injective n, by simp⟩

/-- **Truth tables determine functions.** -/
theorem ttab_injective (n : ℕ) : Function.Injective (ttab (n := n)) := by
  intro f g h
  have h' := List.ofFn_injective h
  funext x
  obtain ⟨i, rfl⟩ := (bitsOf_bijective n).2 x
  exact congrFun h' i

/-! ### Pseudorandom function families -/

/-- A family of functions keyed by seeds, each member computable by `nᵏ`-size circuits. -/
structure PRF where
  seedLen : ℕ → ℕ
  seedPoly : Polynomial ℕ
  seed_le : ∀ n, seedLen n ≤ seedPoly.eval n
  k : ℕ
  G : ∀ n, (Fin (seedLen n) → Bool) → BFun n
  small : ∀ n z, HasCircuit n (n ^ k) (G n z)

/-- Distinguishing advantage of the test `D` at input length `n`. -/
noncomputable def adv (F : PRF) (D : CProp) (n : ℕ) : ℚ :=
  |((Finset.univ.filter (fun z => D n (F.G n z))).card : ℚ) / Fintype.card (Fin (F.seedLen n) → Bool)
    - ((Finset.univ.filter (D n)).card : ℚ) / 2 ^ 2 ^ n|

/-- Security against a class of tests: advantage `< 2^{-cn}` eventually, for every `c`. -/
def Secure (Cls : CProp → Prop) (F : PRF) : Prop :=
  ∀ D, Cls D → ∀ c : ℕ, ∃ N, ∀ n ≥ N, adv F D n < 1 / 2 ^ (c * n)

/-- Truth table as a point of `Fin (2ⁿ) → Bool`. -/
def ttF {n : ℕ} (f : BFun n) : Fin (2 ^ n) → Bool := fun i => f (bitsOf n i)

/-- Circuit constructivity: the property is decided on truth tables by `2^{O(n)}`-size circuits. -/
def ConstructiveC (Pr : CProp) : Prop :=
  ∃ d N, ∀ n ≥ N, ∃ D : BFun (2 ^ n), HasCircuit (2 ^ n) (2 ^ (d * n)) D ∧
    ∀ f, D (ttF f) = true ↔ Pr n f

/-- `P/poly`-natural property useful against `P/poly`. -/
def NaturalC (Pr : CProp) : Prop := ConstructiveC Pr ∧ Large Pr ∧ UsefulPpoly Pr

/-- **The attack**: a large property useful against `P/poly` has advantage `≥ 2^{-cn}` against
every PRF, for large `n`. -/
theorem attack {Pr : CProp} (hL : Large Pr) (hU : UsefulPpoly Pr) (F : PRF) :
    ∃ c N, ∀ n ≥ N, 1 / 2 ^ (c * n) ≤ adv F Pr n := by
  obtain ⟨c, N, h⟩ := natural_distinguishes hL hU F.k
  refine ⟨c, N, fun n hn => ?_⟩
  obtain ⟨h0, h2⟩ := h n hn (Fin (F.seedLen n) → Bool) (F.G n) (F.small n)
  have hq : ((2 : ℚ) ^ 2 ^ n) ≤ 2 ^ (c * n) * ((Finset.univ.filter (Pr n)).card : ℚ) := by
    exact_mod_cast h2
  unfold adv
  rw [h0, Nat.cast_zero, zero_div, zero_sub, abs_neg,
    abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Conditional Razborov–Rudich (generic form).** If some PRF is secure against a class of
tests, no property in that class is both large and useful against `P/poly`. -/
theorem no_large_useful_of_secure (Cls : CProp → Prop) (F : PRF) (hF : Secure Cls F)
    (Pr : CProp) (hC : Cls Pr) (hL : Large Pr) (hU : UsefulPpoly Pr) : False := by
  obtain ⟨c, N1, h1⟩ := attack hL hU F
  obtain ⟨N2, h2⟩ := hF Pr hC c
  have a := h1 (max N1 N2) (le_max_left _ _)
  have b := h2 (max N1 N2) (le_max_right _ _)
  linarith

/-- **Razborov–Rudich (conditional).** If a PRF secure against `2^{O(n)}`-time truth-table tests
exists, then no natural property (constructive, large) is useful against `P/poly`. -/
theorem razborov_rudich (h : ∃ F : PRF, Secure Constructive F) : ∀ Pr, ¬ Natural Pr := by
  rintro Pr ⟨hC, hL, hU⟩
  obtain ⟨F, hF⟩ := h
  exact no_large_useful_of_secure Constructive F hF Pr hC hL hU

/-- **Razborov–Rudich, circuit version (conditional).** If a PRF secure against `2^{O(n)}`-size
circuit tests on truth tables exists, no `P/poly`-natural property is useful against `P/poly`. -/
theorem razborov_rudich_circuit (h : ∃ F : PRF, Secure ConstructiveC F) : ∀ Pr, ¬ NaturalC Pr := by
  rintro Pr ⟨hC, hL, hU⟩
  obtain ⟨F, hF⟩ := h
  exact no_large_useful_of_secure ConstructiveC F hF Pr hC hL hU

/-- Consequence: under the PRF hypothesis, the (large, useful) hardness property `Hard` is not
constructive. -/
theorem hard_not_constructive (h : ∃ F : PRF, Secure Constructive F) : ¬ Constructive Hard :=
  fun hC => razborov_rudich h Hard ⟨hC, hard_large, hard_useful⟩

theorem hard_not_constructiveC (h : ∃ F : PRF, Secure ConstructiveC F) : ¬ ConstructiveC Hard :=
  fun hC => razborov_rudich_circuit h Hard ⟨hC, hard_large, hard_useful⟩

end PvnpReal
