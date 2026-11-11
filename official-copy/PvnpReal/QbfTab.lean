/-
  PvnpReal.QbfTab — the second Cook–Levin tableau as an `R`-chain of row blocks.

  For the one-hot encoding of the tableau CSP (`CSP.lean`, `Tab2.lean`):
  * local decoding/encoding lemmas (`con_of`, `con_hot`): a block of hot bits that satisfies the
    at-least-one clauses and a constraint's forbidden-tuple clauses decodes to values satisfying the
    constraint, and conversely;
  * translation invariance of the row and transition constraints (`csRow_shift`, `csTrans_shift`,
    `csFinal_shift`);
  * **`tab_chain_iff`**: the tableau with `T ≥ 1` rows is satisfiable iff there is an assignment `g`
    of the fixed symbols and two rows (initial and final) satisfying `tabTop` and an `R`-chain of `T`
    steps between those two rows, where `R(u, v)` is the CNF `tabB0` (rows 0, 1 and the transition
    between them) evaluated on `u, v`.
-/
import PvnpReal.QbfSav
import PvnpReal.CookLevin2

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

/-! ### Generic one-hot lemmas -/

section Gen

variable {D : Type*} [DecidableEq D]

def shC (s : ℕ) (c : Constraint D) : Constraint D := ⟨c.scope.map (· + s), c.rel⟩

/-- Decode CSP variable `v` from hot bits (first marked value, else a default). -/
def decB (U : List D) (hU : U ≠ []) (b : ℕ → Bool) (v : ℕ) : D :=
  (U.find? (fun d => b (hotVar U v d))).getD (U.head hU)

/-- The canonical hot bits of a CSP assignment. -/
def hotB (U : List D) (a : ℕ → D) (n : ℕ) : Bool := decide (n % U.length = U.idxOf (a (n / U.length)))

def HC (U : List D) (cs : List (Constraint D)) : CNF := cs.flatMap (conClauses U)

def AL (U : List D) (lo len : ℕ) : CNF := (List.range len).map (fun i => aloClause U (lo + i))

theorem find?_congr {p q : D → Bool} : ∀ (l : List D), (∀ d ∈ l, p d = q d) → l.find? p = l.find? q
  | [], _ => rfl
  | d :: l, h => by
    simp only [List.find?_cons]
    rw [h d (by simp), find?_congr l (fun d' hd' => h d' (by simp [hd']))]

theorem decB_mem (U : List D) (hU : U ≠ []) (b : ℕ → Bool) (v : ℕ) : decB U hU b v ∈ U := by
  unfold decB
  rcases h : U.find? (fun d => b (hotVar U v d)) with _ | d
  · exact List.head_mem hU
  · exact List.mem_of_find?_eq_some h

theorem decB_congr (U : List D) (hU : U ≠ []) {b b' : ℕ → Bool} {v v' : ℕ}
    (h : ∀ d ∈ U, b (hotVar U v d) = b' (hotVar U v' d)) : decB U hU b v = decB U hU b' v' := by
  unfold decB; rw [find?_congr U h]

theorem decB_hot (U : List D) (hU : U ≠ []) (b : ℕ → Bool) (v : ℕ)
    (h : evalClause (aloClause U v) b = true) : b (hotVar U v (decB U hU b v)) = true := by
  simp only [evalClause, aloClause, List.any_map, List.any_eq_true, Function.comp, evalLiteral_pos] at h
  obtain ⟨d, hd, hb⟩ := h
  unfold decB
  rcases e : U.find? (fun d => b (hotVar U v d)) with _ | d'
  · rw [List.find?_eq_none] at e; exact absurd hb (by simpa using e d hd)
  · simpa using List.find?_some e

theorem con_of (U : List D) (hU : U ≠ []) (b : ℕ → Bool) (c : Constraint D)
    (hc : evalCNF (conClauses U c) b = true)
    (halo : ∀ v ∈ c.scope, evalClause (aloClause U v) b = true) :
    c.rel (c.scope.map (decB U hU b)) = true := by
  by_contra hr
  have hmem : forbidClause U c.scope (c.scope.map (decB U hU b)) ∈ conClauses U c := by
    refine List.mem_map.2 ⟨c.scope.map (decB U hU b), ?_, rfl⟩
    rw [List.mem_filter, mem_tuples]
    refine ⟨⟨by simp, ?_⟩, by simpa using hr⟩
    intro d hd
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hd
    exact decB_mem U hU b v
  rw [evalCNF_iff] at hc
  obtain ⟨lit, hlit, hev⟩ := hc _ hmem
  simp only [forbidClause, List.mem_map] at hlit
  obtain ⟨p, hp, rfl⟩ := hlit
  rw [zip_map_self, List.mem_map] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  have := decB_hot U hU b v (halo v hv)
  rw [evalLiteral_neg] at hev
  simp [this] at hev

theorem hotVar_div' (U : List D) (v : ℕ) {d : D} (hd : d ∈ U) : hotVar U v d / U.length = v :=
  hotVar_div U v hd

theorem alo_hot (U : List D) (a : ℕ → D) (v : ℕ) (h : a v ∈ U) :
    evalClause (aloClause U v) (hotB U a) = true := by
  simp only [evalClause, aloClause, List.any_map, List.any_eq_true, Function.comp, evalLiteral_pos]
  exact ⟨a v, h, by simp [hotB, hotVar_div U v h, hotVar_mod U v h]⟩

theorem con_hot (U : List D) (a : ℕ → D) (c : Constraint D) (hU : ∀ v ∈ c.scope, a v ∈ U)
    (hr : c.rel (c.scope.map a) = true) : evalCNF (conClauses U c) (hotB U a) = true := by
  rw [evalCNF_iff]
  intro cl hcl
  obtain ⟨ds, hds, rfl⟩ := List.mem_map.1 hcl
  rw [List.mem_filter, mem_tuples] at hds
  have hne : ds ≠ c.scope.map a := by
    intro e; subst e; simp [hr] at hds
  obtain ⟨p, hp, hne'⟩ := exists_zip_ne a c.scope ds hds.1.1 hne
  have hpU : p.2 ∈ U := hds.1.2 _ (List.of_mem_zip hp).2
  have hp1 : a p.1 ∈ U := hU _ (List.of_mem_zip hp).1
  refine ⟨⟨hotVar U p.1 p.2, true⟩, List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
  rw [evalLiteral_neg]
  simp only [hotB, hotVar_div U _ hpU, hotVar_mod U _ hpU, Bool.not_eq_true', decide_eq_false_iff_not]
  intro e
  exact hne' ((List.idxOf_inj hp1).1 e.symm)

theorem hotVar_bnd (U : List D) (v : ℕ) {d : D} (hd : d ∈ U) :
    v * U.length ≤ hotVar U v d ∧ hotVar U v d < v * U.length + U.length := by
  have := List.idxOf_lt_length_of_mem hd
  unfold hotVar; omega

theorem conCl_vars (U : List D) (c : Constraint D) :
    ∀ cl ∈ conClauses U c, ∀ l ∈ cl, ∃ v ∈ c.scope, ∃ d ∈ U, l.var = hotVar U v d := by
  intro cl hcl l hl
  obtain ⟨ds, hds, rfl⟩ := List.mem_map.1 hcl
  rw [List.mem_filter, mem_tuples] at hds
  simp only [forbidClause, List.mem_map] at hl
  obtain ⟨p, hp, rfl⟩ := hl
  exact ⟨p.1, (List.of_mem_zip hp).1, p.2, hds.1.2 _ (List.of_mem_zip hp).2, rfl⟩

theorem alo_vars (U : List D) (v : ℕ) : ∀ l ∈ aloClause U v, ∃ d ∈ U, l.var = hotVar U v d := by
  intro l hl
  simp only [aloClause, List.mem_map] at hl
  obtain ⟨d, hd, rfl⟩ := hl
  exact ⟨d, hd, rfl⟩

theorem HC_iff (U : List D) (cs : List (Constraint D)) (b : ℕ → Bool) :
    evalCNF (HC U cs) b = true ↔ ∀ c ∈ cs, evalCNF (conClauses U c) b = true :=
  evalCNF_flatMap _ _ _

theorem AL_iff (U : List D) (lo len : ℕ) (b : ℕ → Bool) :
    evalCNF (AL U lo len) b = true ↔ ∀ i < len, evalClause (aloClause U (lo + i)) b = true := by
  simp [AL, evalCNF]

/-- Hot bits after a shift of `s` CSP variables. -/
theorem hotB_shift (U : List D) (hU : U ≠ []) (a : ℕ → D) (s v : ℕ) :
    hotB U a (v + s * U.length) = hotB U (fun w => a (w + s)) v := by
  have hl : 0 < U.length := List.length_pos_iff.2 hU
  simp only [hotB, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hl]

/-- Every variable of a CNF whose clauses come from constraints with scopes in `[lo, hi)` and
from at-least-one clauses of variables in `[lo, hi)` lies in `[lo·|U|, hi·|U|)`. -/
theorem HC_vars (U : List D) (cs : List (Constraint D)) (lo hi : ℕ)
    (hs : ∀ c ∈ cs, ∀ v ∈ c.scope, lo ≤ v ∧ v < hi) :
    ∀ cl ∈ HC U cs, ∀ l ∈ cl, lo * U.length ≤ l.var ∧ l.var < hi * U.length := by
  intro cl hcl l hl
  obtain ⟨c, hc, hcl⟩ := List.mem_flatMap.1 hcl
  obtain ⟨v, hv, d, hd, e⟩ := conCl_vars U c cl hcl l hl
  have := hotVar_bnd U v hd
  have h1 := hs c hc v hv
  have h2 : lo * U.length ≤ v * U.length := Nat.mul_le_mul_right _ h1.1
  have h3 : (v + 1) * U.length ≤ hi * U.length := Nat.mul_le_mul_right _ h1.2
  rw [Nat.add_mul] at h3
  rw [e]; omega

theorem AL_vars (U : List D) (lo len : ℕ) :
    ∀ cl ∈ AL U lo len, ∀ l ∈ cl, lo * U.length ≤ l.var ∧ l.var < (lo + len) * U.length := by
  intro cl hcl l hl
  simp only [AL, List.mem_map, List.mem_range] at hcl
  obtain ⟨i, hi, rfl⟩ := hcl
  obtain ⟨d, hd, e⟩ := alo_vars U _ l hl
  have := hotVar_bnd U (lo + i) hd
  have h2 : lo * U.length ≤ (lo + i) * U.length := Nat.mul_le_mul_right _ (by omega)
  have h3 : (lo + i + 1) * U.length ≤ (lo + len) * U.length := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at h3
  rw [e]; omega

end Gen

/-! ### Translation invariance and scopes of the tableau constraints -/

section Tab

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (S : ℕ) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool)

theorem csRow_shift (a t : ℕ) :
    csRow d Ks S (a + t) = (csRow d Ks S a).map (shC (D := V2 Γ Λ σ) (t * W2 Ks S)) := by
  simp only [csRow, shC, List.map_flatMap, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, sv2, cv2, add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem csTrans_shift (a t : ℕ) :
    csTrans m d P Ks S (a + t) = (csTrans m d P Ks S a).map (shC (t * W2 Ks S)) := by
  simp only [csTrans, shC, List.map_flatMap, List.map_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, sv2, cv2, add_mul, one_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem csFinal_shift (a t : ℕ) :
    csFinal (Λ := Λ) (σ := σ) Ks S (a + t) k₁ gacc =
      (csFinal Ks S a k₁ gacc).map (shC (t * W2 Ks S)) := by
  simp only [csFinal, shC, List.map_cons, List.map_nil, cv2, add_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem sv2_succ (t : ℕ) : sv2 Ks S (t + 1) = sv2 Ks S t + W2 Ks S := by unfold sv2; ring

theorem cv2_bounds (t : ℕ) {k : K} (hk : k ∈ Ks) {p : ℕ} (hp : p < S) :
    sv2 Ks S t < cv2 Ks S t k p ∧ cv2 Ks S t k p < sv2 Ks S (t + 1) := by
  have hi := List.idxOf_lt_length_of_mem hk
  have hr : 1 + Ks.idxOf k * S + p < W2 Ks S := by
    unfold W2
    have : (Ks.idxOf k + 1) * S ≤ Ks.length * S := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul] at this; omega
  rw [sv2_succ]; unfold cv2 sv2; omega

theorem scope_row (hdS : d + 1 ≤ S) (t : ℕ) :
    ∀ c ∈ csRow (Γ := Γ) (Λ := Λ) (σ := σ) d Ks S t, ∀ v ∈ c.scope,
      sv2 Ks S t ≤ v ∧ v < sv2 Ks S (t + 1) := by
  intro c hc v hv
  simp only [csRow, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range] at hc
  obtain ⟨k, hk, (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)⟩ := hc
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · have := cv2_bounds Ks S t hk (p := 0) (by omega); omega
    · have := cv2_bounds Ks S t hk (p := i) (by omega); omega
  · simp only [List.mem_singleton] at hv; subst hv
    have := cv2_bounds Ks S t hk (p := S - (d + 1) + j) (by omega); omega

theorem scope_trans (hS2 : 2 * d + P + 1 ≤ S) (t : ℕ) :
    ∀ c ∈ csTrans m d P Ks S t, ∀ v ∈ c.scope, sv2 Ks S t ≤ v ∧ v < sv2 Ks S (t + 2) := by
  have e2 : sv2 Ks S (t + 2) = sv2 Ks S (t + 1) + W2 Ks S := sv2_succ Ks S (t + 1)
  have e1 := sv2_succ Ks S t
  have e3 : sv2 Ks S (t + 1 + 1) = sv2 Ks S (t + 2) := rfl
  intro c hc v hv
  simp only [csTrans, List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map,
    List.mem_range] at hc
  rcases hc with rfl | ⟨k, hk, (⟨p, hp, rfl⟩ | ⟨j, hj, rfl⟩)⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
    have : 0 < W2 Ks S := by unfold W2; omega
    rcases hv with rfl | rfl <;> omega
  · simp only [List.mem_cons, List.mem_map, List.mem_range] at hv
    rcases hv with rfl | rfl | ⟨i, hi, rfl⟩
    · have : 0 < W2 Ks S := by unfold W2; omega
      omega
    · have := cv2_bounds Ks S (t + 1) hk (p := p) (by omega); omega
    · have := cv2_bounds Ks S t hk (p := i) (by omega); omega
  · simp only [List.mem_cons, List.mem_map, List.mem_range] at hv
    rcases hv with rfl | rfl | ⟨i, hi, rfl⟩
    · have : 0 < W2 Ks S := by unfold W2; omega
      omega
    · have := cv2_bounds Ks S (t + 1) hk (p := d + P + j) (by omega); omega
    · have := cv2_bounds Ks S t hk (p := d + j + i) (by omega); omega

theorem scope_final (hk₁ : k₁ ∈ Ks) (hS : 1 ≤ S) (t : ℕ) :
    ∀ c ∈ csFinal (Λ := Λ) (σ := σ) Ks S t k₁ gacc, ∀ v ∈ c.scope,
      sv2 Ks S t ≤ v ∧ v < sv2 Ks S (t + 1) := by
  intro c hc v hv
  simp only [csFinal, List.mem_singleton] at hc; subst hc
  simp only [List.mem_singleton] at hv; subst hv
  have := cv2_bounds Ks S t hk₁ (p := 0) (by omega); omega

theorem scope_init (hk₀ : k₀ ∈ Ks) (hS1 : xs.length + 2 + Q ≤ S) :
    ∀ c ∈ csZ (Λ := Λ) (σ := σ) k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs, ∀ v ∈ c.scope,
      v < sv2 Ks S 1 := by
  have h0 : ∀ p < S, cv2 Ks S 0 k₀ p < sv2 Ks S 1 := fun p hp =>
    (cv2_bounds Ks S 0 hk₀ hp).2
  have hW : 2 < sv2 Ks S 1 := by unfold sv2 W2; omega
  intro c hc v hv
  simp only [csZ, csInit, List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map,
    List.mem_range, List.mem_flatMap, List.mem_filter, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl) | ((((((rfl | ⟨i, hi, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) |
    ⟨j, hj, rfl⟩) | ⟨k, ⟨hk, -⟩, p, hp, rfl⟩)))
  all_goals simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hv
  · omega
  · omega
  · subst hv
    have : sv2 Ks S 1 = sv2 Ks S 0 + W2 Ks S := sv2_succ Ks S 0
    have : 0 < W2 Ks S := by unfold W2; omega
    omega
  · rcases hv with rfl | rfl
    · exact h0 _ (by omega)
    · have : NthTM.bit xs i ≤ 1 := by unfold NthTM.bit; split <;> omega
      omega
  · subst hv; exact h0 _ (by omega)
  · rcases hv with rfl | rfl <;> exact h0 _ (by omega)
  · subst hv; exact h0 _ (by omega)
  · subst hv; exact (cv2_bounds Ks S 0 hk hp).2

end Tab

/-! ### The tableau as a chain of row blocks -/

section Chain

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [DecidableEq (V2 Γ Λ σ)]
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (S : ℕ) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool) (U : List (V2 Γ Λ σ))

/-- Fixed symbols, initial row (row 0) and final row (row 1). -/
noncomputable def tabTop : CNF :=
  AL U 0 (sv2 Ks S 2) ++
    HC U (csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs ++ csFinal Ks S 1 k₁ gacc)

/-- Rows 0 and 1 and the transition between them. -/
noncomputable def tabB0 : CNF :=
  AL U (sv2 Ks S 0) (2 * W2 Ks S) ++
    HC U (csRow d Ks S 0 ++ csRow d Ks S 1 ++ csTrans m d P Ks S 0)

/-- The one-step relation between two row blocks of hot bits. -/
def tabR (u v : List Bool) : Prop :=
  evalCNF (tabB0 m d P Ks S U) (asg (List.replicate (2 * U.length) false ++ u ++ v)) = true

theorem sv2_mul (t : ℕ) : sv2 Ks S t * U.length = 2 * U.length + t * (W2 Ks S * U.length) := by
  unfold sv2; ring

theorem tabTop_vars (hk₀ : k₀ ∈ Ks) (hk₁ : k₁ ∈ Ks) (hS1 : xs.length + 2 + Q ≤ S) :
    ∀ cl ∈ tabTop Ks S k₀ k₁ main v₀ sb sep Q gacc xs U, ∀ l ∈ cl,
      l.var < 2 * U.length + 2 * (W2 Ks S * U.length) := by
  intro cl hcl l hl
  rw [← sv2_mul]
  rcases List.mem_append.1 hcl with h | h
  · have := AL_vars U 0 (sv2 Ks S 2) cl h l hl; simpa using this.2
  · refine (HC_vars U _ 0 (sv2 Ks S 2) (fun c hc v hv => ?_) cl h l hl).2
    have e1 : sv2 Ks S 2 = sv2 Ks S 1 + W2 Ks S := sv2_succ Ks S 1
    rcases List.mem_append.1 hc with hc | hc
    · have := scope_init (Λ := Λ) (σ := σ) Ks S k₀ main v₀ sb sep Q xs hk₀ hS1 c hc v hv
      omega
    · have := scope_final (Λ := Λ) (σ := σ) Ks S k₁ gacc hk₁ (by omega) 1 c hc v hv
      have r2 : sv2 Ks S (1 + 1) = sv2 Ks S 2 := rfl
      omega

theorem tabB0_vars (hS2 : 2 * d + P + 1 ≤ S) :
    ∀ cl ∈ tabB0 m d P Ks S U, ∀ l ∈ cl,
      2 * U.length ≤ l.var ∧ l.var < 2 * U.length + 2 * (W2 Ks S * U.length) := by
  intro cl hcl l hl
  have e0 : sv2 Ks S 0 * U.length = 2 * U.length := by simpa using sv2_mul Ks S U 0
  rw [← sv2_mul, ← e0]
  have e1 : sv2 Ks S 1 = sv2 Ks S 0 + W2 Ks S := sv2_succ Ks S 0
  have e2 : sv2 Ks S 2 = sv2 Ks S 1 + W2 Ks S := sv2_succ Ks S 1
  rcases List.mem_append.1 hcl with h | h
  · have := AL_vars U (sv2 Ks S 0) (2 * W2 Ks S) cl h l hl
    rw [show sv2 Ks S 0 + 2 * W2 Ks S = sv2 Ks S 2 by omega] at this; exact this
  · refine HC_vars U _ (sv2 Ks S 0) (sv2 Ks S 2) (fun c hc v hv => ?_) cl h l hl
    have r1 : sv2 Ks S (0 + 1) = sv2 Ks S 1 := rfl
    have r2 : sv2 Ks S (1 + 1) = sv2 Ks S 2 := rfl
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have := scope_row (Λ := Λ) (σ := σ) d Ks S (by omega) 0 c hc v hv; omega
    · have := scope_row (Λ := Λ) (σ := σ) d Ks S (by omega) 1 c hc v hv; omega
    · have := scope_trans m d P Ks S hS2 0 c hc v hv; exact this

/-! Membership in the tableau. -/

theorem mt_init {T : ℕ} {c : Constraint (V2 Γ Λ σ)}
    (h : c ∈ csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs) :
    c ∈ tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

theorem mt_row {T t : ℕ} (ht : t ≤ T) {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csRow d Ks S t) :
    c ∈ tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨t, List.mem_range.2 (by omega), h⟩)))

theorem mt_trans {T t : ℕ} (ht : t < T) {c : Constraint (V2 Γ Λ σ)}
    (h : c ∈ csTrans m d P Ks S t) : c ∈ tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, h⟩))

theorem mt_final {T : ℕ} {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csFinal Ks S T k₁ gacc) :
    c ∈ tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs :=
  List.mem_append_right _ h

theorem rdF_getD (a : ℕ → Bool) (p n i : ℕ) (h : i < n) : (rdF a p n).getD i false = a (p + i) := by
  simp [rdF, List.getD_eq_getElem?_getD, h]

theorem shC_rel (s : ℕ) (c : Constraint (V2 Γ Λ σ)) (a : ℕ → V2 Γ Λ σ) :
    (shC s c).rel ((shC s c).scope.map a) = c.rel (c.scope.map (fun v => a (v + s))) := by
  simp [shC, List.map_map, Function.comp_def]

theorem hotVar_add (v s : ℕ) (x : V2 Γ Λ σ) :
    hotVar U (v + s) x = hotVar U v x + s * U.length := by unfold hotVar; ring

/-- **From a chain of row blocks to a solution of the tableau.** -/
theorem tab_of_chain (hU : U ≠ []) (hk₀ : k₀ ∈ Ks) (hk₁ : k₁ ∈ Ks)
    (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S) (T : ℕ) (hT : 1 ≤ T)
    (g : List Bool) (htop : evalCNF (tabTop Ks S k₀ k₁ main v₀ sb sep Q gacc xs U) (asg g) = true)
    (hch : Chain (tabR m d P Ks S U) (W2 Ks S * U.length) T
      (rdF (asg g) (2 * U.length) (W2 Ks S * U.length))
      (rdF (asg g) (2 * U.length + W2 Ks S * U.length) (W2 Ks S * U.length))) :
    CSPSat U (tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs) := by
  obtain ⟨u, hu0, huT, hul, huR⟩ := hch
  set L := U.length with hL
  set n := W2 Ks S * L with hn
  have hLp : 0 < L := List.length_pos_iff.2 hU
  have hW : 0 < W2 Ks S := by unfold W2; omega
  have hnp : 0 < n := Nat.mul_pos hW hLp
  have sm : ∀ t, sv2 Ks S t * L = 2 * L + t * n := fun t => by
    simp only [hn, hL]; exact sv2_mul Ks S U t
  let β : ℕ → Bool := fun v =>
    if v < 2 * L + n then asg g v else (u ((v - 2 * L) / n)).getD ((v - 2 * L) % n) false
  have F1 : ∀ t i, i < n → β (2 * L + t * n + i) = (u t).getD i false := by
    intro t i hi
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [β, Nat.zero_mul, Nat.add_zero, if_pos (show 2 * L + i < 2 * L + n by omega)]
      rw [hu0, rdF_getD _ _ _ _ hi]
    · have : ¬ (2 * L + t * n + i < 2 * L + n) := by
        have : n ≤ t * n := Nat.le_mul_of_pos_left n ht
        omega
      simp only [β, if_neg this]
      rw [show 2 * L + t * n + i - 2 * L = i + t * n by omega, Nat.add_mul_div_right _ _ hnp,
        Nat.add_mul_mod_self_right, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.zero_add]
  have hβg : ∀ v < 2 * L + n, β v = asg g v := fun v hv => if_pos hv
  -- Top, split
  rw [tabTop, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff] at htop
  obtain ⟨hAL, hHC⟩ := htop
  set a := decB U hU β with ha
  refine ⟨a, fun v => decB_mem U hU β v, fun c hc => ?_⟩
  -- one step of the chain gives the constraints between rows `t` and `t + 1`
  have hstep : ∀ t < T, ∀ c0 ∈ csRow d Ks S 0 ++ csRow d Ks S 1 ++ csTrans m d P Ks S 0,
      (shC (t * W2 Ks S) c0).rel ((shC (t * W2 Ks S) c0).scope.map a) = true := by
    intro t ht c0 hc0
    have hR := huR t ht
    unfold tabR at hR
    rw [tabB0, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff] at hR
    obtain ⟨hA, hH⟩ := hR
    set w := List.replicate (2 * L) false ++ u t ++ u (t + 1) with hw
    have hsc : ∀ v ∈ c0.scope, sv2 Ks S 0 ≤ v ∧ v < sv2 Ks S 2 := by
      intro v hv
      have e1 : sv2 Ks S 1 = sv2 Ks S 0 + W2 Ks S := sv2_succ Ks S 0
      have e2 : sv2 Ks S 2 = sv2 Ks S 1 + W2 Ks S := sv2_succ Ks S 1
      have r1 : sv2 Ks S (0 + 1) = sv2 Ks S 1 := rfl
      have r2 : sv2 Ks S (1 + 1) = sv2 Ks S 2 := rfl
      simp only [List.mem_append] at hc0
      rcases hc0 with (h | h) | h
      · have := scope_row (Λ := Λ) (σ := σ) d Ks S (by omega) 0 c0 h v hv; omega
      · have := scope_row (Λ := Λ) (σ := σ) d Ks S (by omega) 1 c0 h v hv; omega
      · exact scope_trans m d P Ks S hS2 0 c0 h v hv
    have hrel := con_of U hU (asg w) c0 (hH c0 hc0) (fun v hv => by
      have := hsc v hv
      have h' := hA (v - sv2 Ks S 0) (by
        have : sv2 Ks S 2 = sv2 Ks S 0 + 2 * W2 Ks S := by unfold sv2; ring
        omega)
      rwa [Nat.add_sub_cancel' this.1] at h')
    rw [shC_rel]
    rw [← hrel]
    congr 1
    apply List.map_congr_left
    intro v hv
    refine decB_congr U hU (fun x hx => ?_)
    obtain ⟨h1, h2⟩ := hotVar_bnd U v hx
    rw [← hL] at h1 h2
    have hv' := hsc v hv
    have b1 : sv2 Ks S 0 * L ≤ v * L := Nat.mul_le_mul_right _ hv'.1
    have b2 : (v + 1) * L ≤ sv2 Ks S 2 * L := Nat.mul_le_mul_right _ hv'.2
    rw [Nat.add_mul, Nat.one_mul] at b2
    rw [sm] at b1 b2
    simp only [Nat.zero_mul, Nat.add_zero] at b1
    obtain ⟨j, hj⟩ : ∃ j, hotVar U v x = 2 * L + j := ⟨hotVar U v x - 2 * L, by omega⟩
    have hj2 : j < 2 * n := by omega
    rw [hotVar_add, hj]
    have hw' : asg w (2 * L + j) = (u t ++ u (t + 1)).getD j false := by
      rw [hw, List.append_assoc]
      have := asg_append_right (List.replicate (2 * L) false) (u t ++ u (t + 1)) j
      simp only [List.length_replicate] at this
      rw [this]; rfl
    rw [hw']
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [List.getD_append _ _ _ _ (by rw [hul]; exact hjn),
        show 2 * L + j + t * W2 Ks S * L = 2 * L + t * n + j by rw [hn]; ring, F1 t j hjn]
    · rw [List.getD_append_right _ _ _ _ (by rw [hul]; exact hjn), hul,
        show 2 * L + j + t * W2 Ks S * L = 2 * L + (t + 1) * n + (j - n) by
          have e1 : t * W2 Ks S * L = t * n := by rw [hn]; ring
          have e2 : (t + 1) * n = t * n + n := by ring
          omega,
        F1 (t + 1) (j - n) (by omega)]
  simp only [tab2CS, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with (((hZI | ⟨t, ht, hrow⟩) | ⟨t, ht, htr⟩) | hfin)
  · -- fixed symbols and the initial row
    have hZI' : c ∈ csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs := List.mem_append.2 hZI
    have hsc := scope_init (Λ := Λ) (σ := σ) Ks S k₀ main v₀ sb sep Q xs hk₀ hS1 c hZI'
    have hrel := con_of U hU (asg g) c (hHC c (List.mem_append_left _ hZI')) (fun v hv => by
      have := hsc v hv
      have e : sv2 Ks S 2 = sv2 Ks S 1 + W2 Ks S := sv2_succ Ks S 1
      simpa using hAL v (by omega))
    rw [← hrel]
    congr 1
    apply List.map_congr_left
    intro v hv
    refine decB_congr U hU (fun x hx => ?_)
    obtain ⟨-, h2⟩ := hotVar_bnd U v hx
    rw [← hL] at h2
    have b2 : (v + 1) * L ≤ sv2 Ks S 1 * L := Nat.mul_le_mul_right _ (hsc v hv)
    rw [Nat.add_mul, Nat.one_mul, sm] at b2
    exact hβg _ (by omega)
  · -- rows
    rcases Nat.lt_or_ge t T with htT | htT
    · rw [show t = 0 + t by omega, csRow_shift] at hrow
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hrow
      exact hstep t htT c0 (by simp [hc0])
    · rw [show t = 1 + (T - 1) by omega, csRow_shift] at hrow
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hrow
      exact hstep (T - 1) (by omega) c0 (by simp [hc0])
  · rw [show t = 0 + t by omega, csTrans_shift] at htr
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 htr
    exact hstep t ht c0 (by simp [hc0])
  · -- the final row
    rw [show T = 1 + (T - 1) by omega, csFinal_shift] at hfin
    obtain ⟨c1, hc1, rfl⟩ := List.mem_map.1 hfin
    have hsc := scope_final (Λ := Λ) (σ := σ) Ks S k₁ gacc hk₁ (by omega) 1 c1 hc1
    have hrel := con_of U hU (asg g) c1 (hHC c1 (List.mem_append_right _ hc1)) (fun v hv => by
      have := hsc v hv
      have e : sv2 Ks S 2 = sv2 Ks S 1 + W2 Ks S := sv2_succ Ks S 1
      have r2 : sv2 Ks S (1 + 1) = sv2 Ks S 2 := rfl
      simpa using hAL v (by omega))
    rw [shC_rel, ← hrel]
    congr 1
    apply List.map_congr_left
    intro v hv
    refine (decB_congr U hU (fun x hx => ?_)).symm
    obtain ⟨h1, h2⟩ := hotVar_bnd U v hx
    rw [← hL] at h1 h2
    have r2 : sv2 Ks S (1 + 1) = sv2 Ks S 2 := rfl
    have b1 : sv2 Ks S 1 * L ≤ v * L := Nat.mul_le_mul_right _ (hsc v hv).1
    have b2 : (v + 1) * L ≤ sv2 Ks S 2 * L := Nat.mul_le_mul_right _ (r2 ▸ (hsc v hv).2)
    rw [Nat.add_mul, Nat.one_mul] at b2
    rw [sm] at b1 b2
    obtain ⟨i, hi⟩ : ∃ i, hotVar U v x = 2 * L + n + i := ⟨hotVar U v x - (2 * L + n), by omega⟩
    have hin : i < n := by omega
    rw [hotVar_add, hi, show 2 * L + n + i + (T - 1) * W2 Ks S * L = 2 * L + T * n + i by
      rw [hn]; rcases T with _ | T; · omega
      · simp only [Nat.add_sub_cancel]; ring, F1 T i hin, huT, rdF_getD _ _ _ _ hin]


/-- **From a solution of the tableau to a chain of row blocks.** -/
theorem chain_of_tab (hU : U ≠ []) (hk₀ : k₀ ∈ Ks) (hk₁ : k₁ ∈ Ks)
    (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S) (T : ℕ) (hT : 1 ≤ T)
    (h : CSPSat U (tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs)) :
    ∃ g : List Bool, g.length = 2 * U.length + 2 * (W2 Ks S * U.length) ∧
      evalCNF (tabTop Ks S k₀ k₁ main v₀ sb sep Q gacc xs U) (asg g) = true ∧
      Chain (tabR m d P Ks S U) (W2 Ks S * U.length) T
        (rdF (asg g) (2 * U.length) (W2 Ks S * U.length))
        (rdF (asg g) (2 * U.length + W2 Ks S * U.length) (W2 Ks S * U.length)) := by
  obtain ⟨a, haU, hc⟩ := h
  set n := W2 Ks S * U.length with hn
  have hLp : 0 < U.length := List.length_pos_iff.2 hU
  have hW : 0 < W2 Ks S := by unfold W2; omega
  have hnp : 0 < n := Nat.mul_pos hW hLp
  have sm : ∀ t, sv2 Ks S t * U.length = 2 * U.length + t * n := fun t => by
    simp only [hn]; exact sv2_mul Ks S U t
  set β := hotB U a with hβ
  set g := rdF β 0 (2 * U.length + n) ++ rdF β (2 * U.length + T * n) n with hg
  have hgl : g.length = 2 * U.length + 2 * n := by simp [hg]; ring
  have G1 : ∀ v < 2 * U.length + n, asg g v = β v := by
    intro v hv
    rw [hg, asg_append_left _ _ (by simpa using hv)]
    simp [asg, rdF, List.getD_eq_getElem?_getD, hv]
  have G2 : ∀ i < n, asg g (2 * U.length + n + i) = β (2 * U.length + T * n + i) := by
    intro i hi
    rw [hg, show 2 * U.length + n + i = (rdF β 0 (2 * U.length + n)).length + i by simp]
    rw [asg_append_right]
    simp [asg, rdF, List.getD_eq_getElem?_getD, hi]
  refine ⟨g, hgl, ?_, ?_⟩
  · -- the top part, through the shifted assignment `a'`
    let s := (T - 1) * W2 Ks S
    let a' : ℕ → V2 Γ Λ σ := fun v => if v < sv2 Ks S 1 then a v else a (v + s)
    have ha' : ∀ v, a' v ∈ U := fun v => by
      simp only [a']; split_ifs <;> exact haU _
    have hA : ∀ v < 2 * U.length + 2 * n, asg g v = hotB U a' v := by
      intro v hv
      have e1 := sm 1
      rcases Nat.lt_or_ge v (2 * U.length + n) with h1 | h1
      · rw [G1 v h1, hβ]
        have : v / U.length < sv2 Ks S 1 := by
          rw [Nat.div_lt_iff_lt_mul hLp]; omega
        simp only [hotB, a', if_pos this]
      · obtain ⟨i, rfl⟩ : ∃ i, v = 2 * U.length + n + i := ⟨v - (2 * U.length + n), by omega⟩
        rw [G2 i (by omega), hβ,
          show 2 * U.length + T * n + i = (2 * U.length + n + i) + (T - 1) * W2 Ks S * U.length by
            have e : T * n = n + (T - 1) * n := by
              rcases T with _ | T; · omega
              · simp only [Nat.add_sub_cancel]; ring
            have e2 : (T - 1) * W2 Ks S * U.length = (T - 1) * n := by rw [hn]; ring
            omega,
          hotB_shift U hU a ((T - 1) * W2 Ks S)]
        have : ¬ ((2 * U.length + n + i) / U.length < sv2 Ks S 1) := by
          rw [Nat.div_lt_iff_lt_mul hLp]; omega
        simp only [hotB, a', if_neg this]
        rfl
    rw [evalCNF_congr _ _ _ (fun cl hcl l hl => hA _ (by
      have := tabTop_vars Ks S k₀ k₁ main v₀ sb sep Q gacc xs U hk₀ hk₁ hS1 cl hcl l hl
      rw [← hn] at this; exact this))]
    rw [tabTop, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff]
    refine ⟨fun i _ => alo_hot U a' _ (ha' _), fun c hc' => ?_⟩
    refine con_hot U a' c (fun v _ => ha' v) ?_
    rcases List.mem_append.1 hc' with hZI | hF
    · have hsc := scope_init (Λ := Λ) (σ := σ) Ks S k₀ main v₀ sb sep Q xs hk₀ hS1 c hZI
      rw [show c.scope.map a' = c.scope.map a from List.map_congr_left (fun v hv => by
        simp only [a', if_pos (hsc v hv)])]
      exact hc c (mt_init m d P Ks S k₀ k₁ main v₀ sb sep Q gacc xs hZI)
    · have hsc := scope_final (Λ := Λ) (σ := σ) Ks S k₁ gacc hk₁ (by omega) 1 c hF
      have hmem : shC s c ∈ csFinal Ks S T k₁ gacc := by
        rw [show T = 1 + (T - 1) by omega, csFinal_shift]
        exact List.mem_map.2 ⟨c, hF, rfl⟩
      have := hc _ (mt_final m d P Ks S k₀ k₁ main v₀ sb sep Q gacc xs hmem)
      rw [shC_rel] at this
      rw [show c.scope.map a' = c.scope.map (fun v => a (v + s)) from List.map_congr_left
        (fun v hv => by simp only [a', if_neg (show ¬ v < sv2 Ks S 1 by have := hsc v hv; omega)])]
      exact this
  · -- the chain of rows
    refine ⟨fun t => rdF β (2 * U.length + t * n) n, ?_, ?_, fun t => by simp, fun t ht => ?_⟩
    · simp only [Nat.zero_mul, Nat.add_zero]
      exact rdF_congr (fun i hi => (G1 _ (by omega)).symm)
    · show rdF β (2 * U.length + T * n) n = rdF (asg g) (2 * U.length + n) n
      unfold rdF; apply List.map_congr_left; intro i hi
      exact (G2 i (List.mem_range.1 hi)).symm
    · let at' : ℕ → V2 Γ Λ σ := fun v => a (v + t * W2 Ks S)
      unfold tabR
      set w := List.replicate (2 * U.length) false ++ rdF β (2 * U.length + t * n) n ++
        rdF β (2 * U.length + (t + 1) * n) n with hw
      have hB : ∀ v, 2 * U.length ≤ v → v < 2 * U.length + 2 * n → asg w v = hotB U at' v := by
        intro v h1 h2
        obtain ⟨j, rfl⟩ : ∃ j, v = 2 * U.length + j := ⟨v - 2 * U.length, by omega⟩
        have hw' : asg w (2 * U.length + j) =
            (rdF β (2 * U.length + t * n) n ++ rdF β (2 * U.length + (t + 1) * n) n).getD j false := by
          rw [hw, List.append_assoc]
          have := asg_append_right (List.replicate (2 * U.length) false)
            (rdF β (2 * U.length + t * n) n ++ rdF β (2 * U.length + (t + 1) * n) n) j
          simp only [List.length_replicate] at this
          rw [this]; rfl
        have e1 : t * W2 Ks S * U.length = t * n := by rw [hn]; ring
        have key : hotB U at' (2 * U.length + j) = β (2 * U.length + t * n + j) := by
          have := hotB_shift U hU a (t * W2 Ks S) (2 * U.length + j)
          rw [hβ, show 2 * U.length + t * n + j = 2 * U.length + j + t * W2 Ks S * U.length by
            rw [e1]; ring, this]
        rw [hw', key]
        rcases Nat.lt_or_ge j n with hjn | hjn
        · rw [List.getD_append _ _ _ _ (by simpa using hjn), rdF_getD _ _ _ _ hjn]
        · rw [List.getD_append_right _ _ _ _ (by simpa using hjn), rdF_length,
            rdF_getD _ _ _ _ (by omega)]
          congr 1
          have e2 : (t + 1) * n = t * n + n := by ring
          omega
      rw [evalCNF_congr _ (asg w) (hotB U at') (fun cl hcl l hl => by
        have := tabB0_vars m d P Ks S U hS2 cl hcl l hl
        rw [← hn] at this
        exact hB _ this.1 this.2)]
      rw [tabB0, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff]
      refine ⟨fun i _ => alo_hot U at' _ (haU _), fun c0 hc0 => ?_⟩
      refine con_hot U at' c0 (fun v _ => haU _) ?_
      have hmem : shC (t * W2 Ks S) c0 ∈ tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs := by
        simp only [List.mem_append] at hc0
        rcases hc0 with (h | h) | h
        · refine mt_row m d P Ks S k₀ k₁ main v₀ sb sep Q gacc xs (t := 0 + t) (by omega) ?_
          rw [csRow_shift]; exact List.mem_map.2 ⟨c0, h, rfl⟩
        · refine mt_row m d P Ks S k₀ k₁ main v₀ sb sep Q gacc xs (t := 1 + t) (by omega) ?_
          rw [csRow_shift]; exact List.mem_map.2 ⟨c0, h, rfl⟩
        · refine mt_trans m d P Ks S k₀ k₁ main v₀ sb sep Q gacc xs (t := 0 + t) (by omega) ?_
          rw [csTrans_shift]; exact List.mem_map.2 ⟨c0, h, rfl⟩
      have := hc _ hmem
      rwa [shC_rel] at this

end Chain

end PvnpReal
