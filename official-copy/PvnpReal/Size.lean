/-
  PvnpReal.Size — length bounds: the encoding of a CNF, the one-hot CSP encoding, and (in
  `CookLevinSize.lean`) the Cook–Levin formula `clCNF`, which is polynomial in `|x|`.
-/
import PvnpReal.CSP

namespace PvnpReal

theorem flatMap_len_le {α β : Type*} (l : List α) (f : α → List β) (C : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ C) : (l.flatMap f).length ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.succ_mul]; omega

theorem encList_len_le {α : Type} (e : α → List Bool) (l : List α) (A : ℕ)
    (h : ∀ x ∈ l, (e x).length ≤ A) : (encList e l).length ≤ l.length * (A + 1) + 1 := by
  induction l with
  | nil => simp [encList]
  | cons x l ih =>
    simp only [encList, List.length_cons, List.length_append]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.succ_mul]; omega

theorem encLit_len (l : Literal) : (encLit l).length = l.var + 2 := by
  simp [encLit, encVar]

/-- Length of an encoded formula with `≤ A` literals per clause and variables `≤ B`. -/
theorem encodeCNF_len_le (φ : CNF) (A B : ℕ) (hA : ∀ cl ∈ φ, cl.length ≤ A)
    (hB : ∀ cl ∈ φ, ∀ l ∈ cl, l.var ≤ B) :
    (encodeCNF φ).length ≤ φ.length * (A * (B + 3) + 2) + 1 := by
  unfold encodeCNF
  apply encList_len_le
  intro cl hcl
  have := encList_len_le encLit cl (B + 2) (fun l hl => by rw [encLit_len]; have := hB cl hcl l hl; omega)
  have h2 := Nat.mul_le_mul_right (B + 2 + 1) (hA cl hcl)
  have e : A * (B + 3) = A * (B + 2 + 1) := rfl
  omega

theorem tuples_length {D : Type*} (U : List D) (r : ℕ) : (tuples U r).length = U.length ^ r := by
  induction r with
  | zero => simp [tuples]
  | succ r ih =>
    simp only [tuples]
    have : ∀ l : List D, (l.flatMap (fun d => (tuples U r).map (d :: ·))).length =
        l.length * U.length ^ r := by
      intro l; induction l with
      | nil => simp
      | cons d l ihl => simp [ihl, ih, Nat.succ_mul]; omega
    rw [this, pow_succ, Nat.mul_comm]

variable {D : Type*} [DecidableEq D]

theorem hotVar_lt (U : List D) {v N : ℕ} (hv : v < N) {d : D} (hd : d ∈ U) :
    hotVar U v d < N * U.length := by
  have h1 := List.idxOf_lt_length_of_mem hd
  have : (v + 1) * U.length ≤ N * U.length := Nat.mul_le_mul_right _ hv
  unfold hotVar; rw [Nat.succ_mul] at this; omega

/-- **Size of the CSP encoding** (constraints of arity ≤ 3). -/
theorem cspCNF_size (U : List D) (N : ℕ) (cs : List (Constraint D))
    (hs : ∀ c ∈ cs, ∀ v ∈ c.scope, v < N) (h3 : ∀ c ∈ cs, c.scope.length ≤ 3) :
    (encodeCNF (cspCNF U N cs)).length ≤
      (N + cs.length * (U.length + 1) ^ 3) * ((U.length + 3) * (N * U.length + 3) + 2) + 1 := by
  have hlen : (cspCNF U N cs).length ≤ N + cs.length * (U.length + 1) ^ 3 := by
    unfold cspCNF
    rw [List.length_append, List.length_map, List.length_range]
    have := flatMap_len_le cs (conClauses U) ((U.length + 1) ^ 3) (fun c hc => by
      unfold conClauses
      rw [List.length_map]
      refine le_trans (List.length_filter_le _ _) ?_
      rw [tuples_length]
      calc U.length ^ c.scope.length ≤ (U.length + 1) ^ c.scope.length :=
            Nat.pow_le_pow_left (Nat.le_succ _) _
        _ ≤ (U.length + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (h3 c hc))
    omega
  refine le_trans (encodeCNF_len_le _ (U.length + 3) (N * U.length) ?_ ?_) ?_
  · intro cl hcl
    rcases List.mem_append.1 hcl with h | h
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 h
      simp [aloClause]
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.1 h
      obtain ⟨ds, -, rfl⟩ := List.mem_map.1 h
      simp only [forbidClause, List.length_map, List.length_zip]
      have := h3 c hc; omega
  · intro cl hcl l hl
    rcases List.mem_append.1 hcl with h | h
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hl
      exact le_of_lt (hotVar_lt U (List.mem_range.1 hv) hd)
    · obtain ⟨c, hc, h⟩ := List.mem_flatMap.1 h
      obtain ⟨ds, hds, rfl⟩ := List.mem_map.1 h
      rw [List.mem_filter, mem_tuples] at hds
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      exact le_of_lt (hotVar_lt U (hs c hc _ (List.of_mem_zip hp).1)
        (hds.1.2 _ (List.of_mem_zip hp).2))
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _

end PvnpReal
