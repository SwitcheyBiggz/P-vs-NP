/-
  PvnpReal.NaturalProofs — definitions for the **Razborov–Rudich natural proofs barrier** and the
  pieces of it that are provable without cryptographic assumptions.

  * A *circuit property* `Pr n f` of Boolean functions; its truth-table language `ttLang Pr`.
  * `Constructive Pr`: `ttLang Pr ∈ P` (polynomial in the truth-table length `2ⁿ`).
  * `Large Pr`: density at least `2^{-cn}` for large `n`.
  * `UsefulPpoly Pr`: for every `k`, for large `n`, no `f` with `Pr n f` has a circuit of size `≤ nᵏ`.
  * `Natural Pr := Constructive Pr ∧ Large Pr ∧ UsefulPpoly Pr`.

  Proven: the hardness property `Hard` (no circuit of Shannon size `sM n`) is **large and useful**
  (`hard_large`, `hard_useful`); every large useful property yields superpolynomial lower bounds
  (`lower_bound_of_large_useful`); and the **distinguisher step** of Razborov–Rudich
  (`natural_distinguishes`): a large property useful against size `nᵏ` accepts at least a
  `2^{-cn}` fraction of all functions but *no* member of any family of functions computable by
  `nᵏ`-size circuits (e.g. a pseudorandom function family).

  NOT proven / not formalized: pseudorandom function families and their security definition, and
  the Razborov–Rudich theorem itself ("if PRFs secure against `2^{n^ε}`-size circuits exist, no
  `P/poly`-natural property is useful against `P/poly`"), which needs that cryptographic assumption.
  Whether `Hard` is constructive is open (it is an MCSP-type question). Nothing here bears on P vs NP.
-/
import PvnpReal.Circuits

namespace PvnpReal

open Classical

/-- A property of Boolean functions, for every input length. -/
abbrev CProp := ∀ n, BFun n → Prop

/-- Truth table of `f`: entry `i` is `f` on the binary digits of `i`. -/
def ttab {n : ℕ} (f : BFun n) : List Bool := List.ofFn fun i : Fin (2 ^ n) => f fun j => Nat.testBit i j

theorem ttab_length {n : ℕ} (f : BFun n) : (ttab f).length = 2 ^ n := by simp [ttab]

/-- The language of truth tables of functions with the property. -/
def ttLang (Pr : CProp) : Language := fun y => ∃ n, ∃ f : BFun n, ttab f = y ∧ Pr n f

/-- Constructivity: deciding the property from the truth table is polynomial in `2ⁿ`. -/
def Constructive (Pr : CProp) : Prop := InP (ttLang Pr)

/-- Largeness: for large `n`, at least a `2^{-cn}` fraction of `n`-bit functions have the property. -/
def Large (Pr : CProp) : Prop :=
  ∃ c N, ∀ n ≥ N, 2 ^ 2 ^ n ≤ 2 ^ (c * n) * (Finset.univ.filter (Pr n)).card

/-- Usefulness against `P/poly`: functions with the property have no `nᵏ`-size circuits. -/
def UsefulPpoly (Pr : CProp) : Prop :=
  ∀ k, ∃ N, ∀ n ≥ N, ∀ f, Pr n f → ¬ HasCircuit n (n ^ k) f

/-- A `P`-natural property useful against `P/poly`. -/
def Natural (Pr : CProp) : Prop := Constructive Pr ∧ Large Pr ∧ UsefulPpoly Pr

/-- Shannon size: the largest `s ≤ 2ⁿ` with `(2n+2)(s+1) < 2ⁿ`. -/
def sM (n : ℕ) : ℕ := Nat.findGreatest (fun s => (2 * n + 2) * (s + 1) < 2 ^ n) (2 ^ n)

/-- The hardness property: no circuit with `≤ sM n` gates. -/
def Hard : CProp := fun n f => ¬ HasCircuit n (sM n) f

theorem sM_spec {n : ℕ} (hn : 4 ≤ n) : (2 * n + 2) * (sM n + 1) < 2 ^ n := by
  have h0 : (2 * n + 2) * (0 + 1) < 2 ^ n := by
    have : 2 ^ 4 * 2 ^ (n - 4) = 2 ^ n := by rw [← pow_add]; congr 1; omega
    have h2 : n < 2 ^ n := Nat.lt_two_pow_self
    have h3 : 2 * n + 2 < 2 ^ n := by
      induction n, hn using Nat.le_induction with
      | base => decide
      | succ m hm ih =>
        rw [pow_succ]
        have := ih (by rw [← pow_add]; congr 1; omega) Nat.lt_two_pow_self
        omega
    omega
  exact Nat.findGreatest_spec (P := fun s => (2 * n + 2) * (s + 1) < 2 ^ n) (Nat.zero_le _) h0

/-- **The hardness property is large** (density `≥ 1/2` for `n ≥ 4`). -/
theorem hard_large : Large Hard := by
  refine ⟨1, 4, fun n hn => ?_⟩
  have h := sM_spec hn
  have hs : n + sM n + 1 ≤ 2 ^ n := by
    have e : (2 * n + 2) * (sM n + 1) = 2 * (n * sM n) + 2 * n + 2 * sM n + 2 := by ring
    omega
  have he := card_easy_le hs
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := HasCircuit n (sM n))
  rw [Finset.card_univ, card_bfun] at hsplit
  have hpow : 2 * 2 ^ ((2 * n + 2) * (sM n + 1)) ≤ 2 ^ 2 ^ n := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hH : Finset.univ.filter (Hard n) = Finset.univ.filter (fun f => ¬ HasCircuit n (sM n) f) := by
    ext f; simp [Hard]
  rw [hH, one_mul]
  nlinarith

/-- **The hardness property is useful against `P/poly`.** -/
theorem hard_useful : UsefulPpoly Hard := by
  intro k
  obtain ⟨N, hN⟩ := poly_lt_two_pow k
  refine ⟨N, fun n hn f hf hc => hf (hc.mono ?_)⟩
  have h := hN n hn
  have hle : n ^ k ≤ 2 ^ n := by
    have e : (2 * n + 2) * (n ^ k + 1) = 2 * (n * n ^ k) + 2 * n + 2 * n ^ k + 2 := by ring
    omega
  exact Nat.le_findGreatest (P := fun s => (2 * n + 2) * (s + 1) < 2 ^ n) hle (by omega)

/-- A large property has members for all large `n`. -/
theorem Large.exists_mem {Pr : CProp} (h : Large Pr) : ∃ N, ∀ n ≥ N, ∃ f, Pr n f := by
  obtain ⟨c, N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  by_contra hc
  push_neg at hc
  have h0 : (Finset.univ.filter (Pr n)) = ∅ := by
    ext f; simp [hc f]
  rw [h0, Finset.card_empty, mul_zero] at this
  exact absurd this (Nat.not_le.2 (pow_pos (by norm_num) _))

/-- **A large useful property gives superpolynomial circuit lower bounds.** -/
theorem lower_bound_of_large_useful {Pr : CProp} (hL : Large Pr) (hU : UsefulPpoly Pr) (k : ℕ) :
    ∃ N, ∀ n ≥ N, ∃ f : BFun n, ¬ HasCircuit n (n ^ k) f := by
  obtain ⟨N1, h1⟩ := hL.exists_mem
  obtain ⟨N2, h2⟩ := hU k
  refine ⟨max N1 N2, fun n hn => ?_⟩
  obtain ⟨f, hf⟩ := h1 n (le_of_max_le_left hn)
  exact ⟨f, h2 n (le_of_max_le_right hn) f hf⟩

/-- **Distinguisher step of Razborov–Rudich.** If `Pr` is large and useful against size `nᵏ`, then
for all large `n` and every family `G : Z → BFun n` of functions with `nᵏ`-size circuits (e.g. the
keys of a pseudorandom function family), `Pr` accepts no member of the family but at least a
`2^{-cn}` fraction of all functions. (With `Pr` constructive this is a statistical test; turning it
into a break of a PRF needs the cryptographic definitions, which are not formalized here.) -/
theorem natural_distinguishes {Pr : CProp} (hL : Large Pr) (hU : UsefulPpoly Pr) (k : ℕ) :
    ∃ c N, ∀ n ≥ N, ∀ (Z : Type) [Fintype Z] (G : Z → BFun n), (∀ z, HasCircuit n (n ^ k) (G z)) →
      (Finset.univ.filter (fun z => Pr n (G z))).card = 0 ∧
      2 ^ 2 ^ n ≤ 2 ^ (c * n) * (Finset.univ.filter (Pr n)).card := by
  obtain ⟨c, N1, h1⟩ := hL
  obtain ⟨N2, h2⟩ := hU k
  refine ⟨c, max N1 N2, fun n hn Z _ G hG => ⟨?_, h1 n (le_of_max_le_left hn)⟩⟩
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z _ hz
  exact h2 n (le_of_max_le_right hn) (G z) hz (hG z)

end PvnpReal
