/-
  PvnpReal.CSP — constraint satisfaction problems over an explicit finite list `U` of allowed
  values, and their one-hot CNF encoding, with a correctness proof.

  Each CSP variable `v` gets one CNF variable per value `d ∈ U` ("`v` has value `d`"). The clauses are
  * one at-least-one clause per CSP variable, and
  * for each constraint and each violating value tuple from `U`, the clause forbidding it.
  A constraint of arity `r` therefore costs at most `|U| ^ r` clauses. At-most-one clauses are not
  needed: if several values are marked, any one of them gives a solution.
-/
import PvnpReal.Sat

namespace PvnpReal

/-- A constraint: a scope (list of variable indices) and a relation on the values in it. -/
structure Constraint (D : Type*) where
  scope : List ℕ
  rel : List D → Bool

/-- The CSP with allowed values `U` is satisfiable. -/
def CSPSat {D : Type*} (U : List D) (cs : List (Constraint D)) : Prop :=
  ∃ a : ℕ → D, (∀ v, a v ∈ U) ∧ ∀ c ∈ cs, c.rel (c.scope.map a) = true

/-- All value tuples of length `r` with entries from `U`. -/
def tuples {D : Type*} (U : List D) : ℕ → List (List D)
  | 0 => [[]]
  | r + 1 => U.flatMap (fun d => (tuples U r).map (d :: ·))

theorem mem_tuples {D : Type*} (U : List D) :
    ∀ (r : ℕ) (ds : List D), ds ∈ tuples U r ↔ ds.length = r ∧ ∀ d ∈ ds, d ∈ U
  | 0, ds => by cases ds <;> simp [tuples]
  | r + 1, [] => by simp [tuples]
  | r + 1, d :: ds => by
    simp only [tuples, List.mem_flatMap, List.mem_map, List.cons.injEq, mem_tuples U r,
      List.length_cons, List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨d', hd', ds', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, hd', h2⟩
    · rintro ⟨h1, hd, h2⟩; exact ⟨d, hd, ds, ⟨h1, h2⟩, rfl, rfl⟩

variable {D : Type*} [DecidableEq D]

/-- CNF variable "CSP variable `v` has value `d`". -/
def hotVar (U : List D) (v : ℕ) (d : D) : ℕ := v * U.length + U.idxOf d

theorem hotVar_div (U : List D) (v : ℕ) {d : D} (hd : d ∈ U) : hotVar U v d / U.length = v := by
  have h := List.idxOf_lt_length_of_mem hd
  unfold hotVar
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem hotVar_mod (U : List D) (v : ℕ) {d : D} (hd : d ∈ U) :
    hotVar U v d % U.length = U.idxOf d := by
  unfold hotVar
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (List.idxOf_lt_length_of_mem hd)]

/-- "Variable `v` takes some value". -/
def aloClause (U : List D) (v : ℕ) : Clause := U.map (fun d => ⟨hotVar U v d, false⟩)

/-- The clause forbidding the value tuple `ds` on the scope `vs`. -/
def forbidClause (U : List D) (vs : List ℕ) (ds : List D) : Clause :=
  (vs.zip ds).map (fun p => ⟨hotVar U p.1 p.2, true⟩)

def conClauses (U : List D) (c : Constraint D) : CNF :=
  ((tuples U c.scope.length).filter (fun ds => !c.rel ds)).map (forbidClause U c.scope)

/-- The CNF encoding of a CSP whose variables are `0, …, N-1`. -/
def cspCNF (U : List D) (N : ℕ) (cs : List (Constraint D)) : CNF :=
  (List.range N).map (aloClause U) ++ cs.flatMap (conClauses U)

theorem exists_zip_ne {D : Type*} (a : ℕ → D) :
    ∀ (vs : List ℕ) (ds : List D), ds.length = vs.length → ds ≠ vs.map a →
      ∃ p ∈ vs.zip ds, a p.1 ≠ p.2
  | [], [], _, h => absurd rfl h
  | v :: vs, d :: ds, hl, h => by
    by_cases hd : a v = d
    · obtain ⟨p, hp, hne⟩ := exists_zip_ne a vs ds (by simpa using hl)
        (by intro e; apply h; simp [hd, e])
      exact ⟨p, by simp [hp], hne⟩
    · exact ⟨(v, d), by simp, hd⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem zip_map_self {α β : Type*} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map (fun v => (v, f v))
  | [] => rfl
  | v :: l => by simp [zip_map_self f l]

/-- **Correctness of the CSP → CNF encoding.** -/
theorem cspCNF_correct (U : List D) (hU : U ≠ []) (N : ℕ) (cs : List (Constraint D))
    (hs : ∀ c ∈ cs, ∀ v ∈ c.scope, v < N) :
    SAT (cspCNF U N cs) ↔ CSPSat U cs := by
  constructor
  · rintro ⟨b, hb⟩
    rw [evalCNF_iff] at hb
    classical
    let a : ℕ → D := fun v =>
      if h : ∃ d ∈ U, b (hotVar U v d) = true then h.choose else U.head hU
    have haU : ∀ v, a v ∈ U := by
      intro v
      by_cases hex : ∃ d ∈ U, b (hotVar U v d) = true
      · simp only [a, dite_cond_eq_true (eq_true hex)]; exact hex.choose_spec.1
      · simp only [a, dite_cond_eq_false (eq_false hex)]; exact List.head_mem hU
    have ha : ∀ v < N, b (hotVar U v (a v)) = true := by
      intro v hv
      obtain ⟨lit, hlit, hev⟩ :=
        hb (aloClause U v) (List.mem_append_left _ (List.mem_map.2 ⟨v, by simpa, rfl⟩))
      simp only [aloClause, List.mem_map] at hlit
      obtain ⟨d, hd, rfl⟩ := hlit
      have hex : ∃ d ∈ U, b (hotVar U v d) = true := ⟨d, hd, hev⟩
      simp only [a, dite_cond_eq_true (eq_true hex)]
      exact hex.choose_spec.2
    refine ⟨a, haU, fun c hc => ?_⟩
    by_contra hr
    have hmem : forbidClause U c.scope (c.scope.map a) ∈ cspCNF U N cs := by
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨c, hc, ?_⟩)
      refine List.mem_map.2 ⟨c.scope.map a, ?_, rfl⟩
      rw [List.mem_filter, mem_tuples]
      refine ⟨⟨by simp, ?_⟩, by simpa using hr⟩
      intro d hd
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hd
      exact haU v
    obtain ⟨lit, hlit, hev⟩ := hb _ hmem
    simp only [forbidClause, List.mem_map] at hlit
    obtain ⟨p, hp, rfl⟩ := hlit
    rw [zip_map_self, List.mem_map] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    have := ha v (hs c hc v hv)
    rw [evalLiteral_neg] at hev
    simp [this] at hev
  · rintro ⟨a, haU, ha⟩
    refine ⟨fun n => decide (n % U.length = U.idxOf (a (n / U.length))), ?_⟩
    rw [evalCNF_iff]
    intro cl hcl
    rcases List.mem_append.1 hcl with h | h
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 h
      refine ⟨⟨hotVar U v (a v), false⟩, ?_, ?_⟩
      · simp only [aloClause, List.mem_map]; exact ⟨a v, haU v, rfl⟩
      · simp [evalLiteral_pos, hotVar_div U v (haU v), hotVar_mod U v (haU v)]
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.1 h
      obtain ⟨ds, hds, rfl⟩ := List.mem_map.1 h
      rw [List.mem_filter, mem_tuples] at hds
      have hne : ds ≠ c.scope.map a := by
        intro e; subst e; simp [ha c hc] at hds
      obtain ⟨p, hp, hne'⟩ := exists_zip_ne a c.scope ds hds.1.1 hne
      have hpU : p.2 ∈ U := hds.1.2 _ (List.of_mem_zip hp).2
      refine ⟨⟨hotVar U p.1 p.2, true⟩, List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
      rw [evalLiteral_neg, hotVar_div U _ hpU, hotVar_mod U _ hpU]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      intro e
      exact hne' ((List.idxOf_inj (haU _)).1 e.symm)

end PvnpReal
