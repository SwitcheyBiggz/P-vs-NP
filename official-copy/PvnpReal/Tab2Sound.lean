/-
  PvnpReal.Tab2Sound — soundness of the second tableau: a solution of `tab2CS` yields a witness
  whose run ends with the accepting output cell.
-/
import PvnpReal.Tab2

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

open scoped Classical

section Sound

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (m : Λ → Stmt Γ Λ σ) (d P : ℕ) (Ks : List K) (S T : ℕ) (k₀ k₁ : K) (main : Λ) (v₀ : σ)
  (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool)

/-! ### Reading off relations -/

theorem cellRel1_true {Pr : Option (Sig Γ) → Prop} {x : V2 Γ Λ σ}
    (h : cellRel1 Pr [x] = true) : ∃ c, x = Sum.inr c ∧ Pr c := by
  rcases x with R | c
  · simp [cellRel1] at h
  · exact ⟨c, rfl, by simpa [cellRel1] using h⟩

theorem cellRel2_true {Pr : Option (Sig Γ) → Option (Sig Γ) → Prop} {x y : V2 Γ Λ σ}
    (h : cellRel2 Pr [x, y] = true) : ∃ c c', x = Sum.inr c ∧ y = Sum.inr c' ∧ Pr c c' := by
  rcases x with R | c <;> rcases y with R' | c'
  all_goals simp [cellRel2] at h
  exact ⟨c, c', rfl, rfl, h⟩

theorem ctlRel1_true {Pr : Ctl Γ Λ σ → Prop} {x : V2 Γ Λ σ}
    (h : ctlRel1 Pr [x] = true) : ∃ R, x = Sum.inl R ∧ Pr R := by
  rcases x with R | c
  · exact ⟨R, rfl, by simpa [ctlRel1] using h⟩
  · simp [ctlRel1] at h

theorem ctlRel2_true {Pr : Ctl Γ Λ σ → Ctl Γ Λ σ → Prop} {x y : V2 Γ Λ σ}
    (h : ctlRel2 Pr [x, y] = true) : ∃ R R', x = Sum.inl R ∧ y = Sum.inl R' ∧ Pr R R' := by
  rcases x with R | c <;> rcases y with R' | c'
  all_goals simp [ctlRel2] at h
  exact ⟨R, R', rfl, rfl, h⟩

theorem linkRel_true {k : K} {i : ℕ} {x y : V2 Γ Λ σ}
    (h : linkRel k i [x, y] = true) : ∃ R c, x = Sum.inl R ∧ y = Sum.inr c ∧ (R.win k)[i]? = c := by
  rcases x with R | c <;> rcases y with R' | c'
  all_goals simp [linkRel] at h
  exact ⟨R, c', rfl, rfl, h⟩

theorem tcRel_true {k : K} {rp pcap : ℕ} {R : Ctl Γ Λ σ} {y : V2 Γ Λ σ} {olds : List (V2 Γ Λ σ)}
    (h : tcRel m d k rp pcap (Sum.inl R :: y :: olds) = true) :
    ∃ new, y = Sum.inr new ∧ tcP m d k rp pcap R new olds := by
  rcases y with R' | c
  · simp [tcRel] at h
  · exact ⟨c, rfl, by simpa [tcRel] using h⟩

/-! ### Membership in `tab2CS` -/

section Mem
variable {m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs}
variable (hKs : ∀ k, k ∈ Ks)

local notation "CS" => tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs

include hKs in
theorem m_Z0 : (⟨[0], cellRel1 (· = some ⟨k₀, sb false⟩)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS := by
  simp [tab2CS, csZ]
include hKs in
theorem m_Z1 : (⟨[1], cellRel1 (· = some ⟨k₀, sb true⟩)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS := by
  simp [tab2CS, csZ]

theorem m_init {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csInit Ks S k₀ main v₀ sb sep Q xs) : c ∈ CS :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

theorem m_ctl0 : (⟨[sv2 Ks S 0], ctlRel1 (fun R => R.l = some main ∧ R.var = v₀)⟩ :
    Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_init (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))))))

theorem m_bit {i : ℕ} (hi : i < xs.length) : (⟨[cv2 Ks S 0 k₀ i, NthTM.bit xs i],
    cellRel2 (· = ·)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_init (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))

theorem m_sep : (⟨[cv2 Ks S 0 k₀ xs.length], cellRel1 (· = some ⟨k₀, sep⟩)⟩ :
    Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_init (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _)))))

theorem m_wit {j : ℕ} (hj : j < Q) : (⟨[cv2 Ks S 0 k₀ (xs.length + 1 + j),
    cv2 Ks S 0 k₀ (xs.length + 2 + j)], cellRel2 (witP sb)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_init (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))

theorem m_blank0 {j : ℕ} (hj : j < S - (xs.length + 1 + Q)) :
    (⟨[cv2 Ks S 0 k₀ (xs.length + 1 + Q + j)], cellRel1 (· = none)⟩ :
      Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_init (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))

include hKs in
theorem m_other {k : K} (hk : k ≠ k₀) {p : ℕ} (hp : p < S) :
    (⟨[cv2 Ks S 0 k p], cellRel1 (· = none)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_init (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_filter.2 ⟨hKs k, by simpa⟩,
    List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩⟩))

theorem m_row {t : ℕ} (ht : t ≤ T) {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csRow d Ks S t) : c ∈ CS :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨t, List.mem_range.2 (by omega), h⟩)))

include hKs in
theorem m_link {t : ℕ} (ht : t ≤ T) (k : K) {i : ℕ} (hi : i < d) :
    (⟨[sv2 Ks S t, cv2 Ks S t k i], linkRel k i⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_row ht (List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_left _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)⟩)

include hKs in
theorem m_blankEnd {t : ℕ} (ht : t ≤ T) (k : K) {j : ℕ} (hj : j < d + 1) :
    (⟨[cv2 Ks S t k (S - (d + 1) + j)], cellRel1 (· = none)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_row ht (List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_right _
    (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)⟩)

theorem m_trans {t : ℕ} (ht : t < T) {c : Constraint (V2 Γ Λ σ)} (h : c ∈ csTrans m d P Ks S t) :
    c ∈ CS :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, h⟩))

theorem m_tctl {t : ℕ} (ht : t < T) :
    (⟨[sv2 Ks S t, sv2 Ks S (t + 1)], ctlRel2 (transCP m)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_trans ht (List.mem_cons_self ..)

include hKs in
theorem m_small {t : ℕ} (ht : t < T) (k : K) {p : ℕ} (hp : p < d + P) :
    (⟨sv2 Ks S t :: cv2 Ks S (t + 1) k p :: (List.range (p + d + 1)).map (fun i => cv2 Ks S t k i),
      tcRel m d k p p⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_trans ht (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_left _
    (List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩)⟩))

include hKs in
theorem m_deep {t : ℕ} (ht : t < T) (k : K) {j : ℕ} (hj : j < S - (d + P) - (d + 1)) :
    (⟨sv2 Ks S t :: cv2 Ks S (t + 1) k (d + P + j) ::
        (List.range (P + d + 1)).map (fun i => cv2 Ks S t k (d + j + i)),
      tcRel m d k P (d + P)⟩ : Constraint (V2 Γ Λ σ)) ∈ CS :=
  m_trans ht (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨k, hKs k, List.mem_append_right _
    (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)⟩))

theorem m_final : (⟨[cv2 Ks S T k₁ 0], cellRel1 (· = some ⟨k₁, gacc⟩)⟩ :
    Constraint (V2 Γ Λ σ)) ∈ CS :=
  List.mem_append_right _ (List.mem_singleton_self _)

end Mem

/-! ### Soundness -/

def Rep2 (a : ℕ → V2 Γ Λ σ) (t : ℕ) (c : Cfg Γ Λ σ) : Prop :=
  a (sv2 Ks S t) = Sum.inl (ctlOf d c) ∧ ∀ k, ∀ p < S, a (cv2 Ks S t k p) = Sum.inr (cellOf c k p)

variable {m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs}

local notation "CS" => tab2CS m d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs

theorem rel_of (a : ℕ → V2 Γ Λ σ) (hc : ∀ c ∈ CS, c.rel (c.scope.map a) = true)
    {c : Constraint (V2 Γ Λ σ)} (h : c ∈ CS) : c.rel (c.scope.map a) = true := hc c h

/-- Control of row `t` from its links, once the cells of row `t` are known. -/
theorem ctl_of_links (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (a : ℕ → V2 Γ Λ σ) (hU : ∀ v, a v ∈ U) (hc : ∀ c ∈ CS, c.rel (c.scope.map a) = true)
    (hdS : d ≤ S) {t : ℕ} (ht : t ≤ T) (c : Cfg Γ Λ σ) (R : Ctl Γ Λ σ)
    (hR : a (sv2 Ks S t) = Sum.inl R) (hl : R.l = c.l) (hv : R.var = c.var)
    (hcells : ∀ k, ∀ p < S, a (cv2 Ks S t k p) = Sum.inr (cellOf c k p)) :
    R = ctlOf d c := by
  refine ctl_eq_of d R c hl hv (hUd R (hR ▸ hU _)) (fun k i hi => ?_)
  have h := hc _ (m_link (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs) (k₁ := k₁)
    (main := main) (v₀ := v₀) (m := m) (P := P) hKs ht k hi)
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨R', c', h1, h2, h3⟩ := linkRel_true h
  rw [hR] at h1; cases h1
  rw [hcells k i (by omega)] at h2; cases h2
  exact h3

theorem rep2_step (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (a : ℕ → V2 Γ Λ σ) (hU : ∀ v, a v ∈ U) (hc : ∀ c ∈ CS, c.rel (c.scope.map a) = true)
    (hS2 : 2 * d + P + 1 ≤ S) {t : ℕ} (ht : t < T) (c : Cfg Γ Λ σ) (hrep : Rep2 d Ks S a t c)
    (hlen : ∀ k, ((stepStay m c).stk k).length ≤ S - (d + 1)) :
    Rep2 d Ks S a (t + 1) (stepStay m c) := by
  have hcells : ∀ k, ∀ p < S, a (cv2 Ks S (t + 1) k p) = Sum.inr (cellOf (stepStay m c) k p) := by
    intro k p hp
    by_cases h1 : p < d + P
    · have h := hc _ (m_small (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs)
        (k₁ := k₁) (main := main) (v₀ := v₀) hKs ht k h1)
      simp only [List.map_cons, List.map_map] at h
      rw [hrep.1] at h
      obtain ⟨new, hnew, htc⟩ := tcRel_true m d h
      have eo : List.map (a ∘ fun i => cv2 Ks S t k i) (List.range (p + d + 1)) =
          (List.range (p + d + 1)).map (fun i => Sum.inr (cellOf c k (p - p + i))) := by
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        simp only [Function.comp, Nat.sub_self, Nat.zero_add]
        exact hrep.2 k i (by omega)
      rw [eo] at htc
      rw [hnew, (tcP_iff m d P hd hP c k p p p le_rfl (Or.inl ⟨rfl, rfl⟩) new).1 htc]
    · by_cases h2 : p < S - (d + 1)
      · obtain ⟨j, rfl⟩ : ∃ j, p = d + P + j := ⟨p - (d + P), by omega⟩
        have h := hc _ (m_deep (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs)
          (k₁ := k₁) (main := main) (v₀ := v₀) hKs ht k (j := j) (by omega))
        simp only [List.map_cons, List.map_map] at h
        rw [hrep.1] at h
        obtain ⟨new, hnew, htc⟩ := tcRel_true m d h
        have eo : List.map (a ∘ fun i => cv2 Ks S t k (d + j + i)) (List.range (P + d + 1)) =
            (List.range (P + d + 1)).map (fun i => Sum.inr (cellOf c k (d + P + j - P + i))) := by
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          simp only [Function.comp]
          rw [show d + P + j - P + i = d + j + i by omega]
          exact hrep.2 k _ (by omega)
        rw [eo] at htc
        rw [hnew, (tcP_iff m d P hd hP c k (d + P + j) P (d + P) (by omega)
          (Or.inr ⟨rfl, by omega, rfl⟩) new).1 htc]
      · obtain ⟨j, rfl⟩ : ∃ j, p = S - (d + 1) + j := ⟨p - (S - (d + 1)), by omega⟩
        have h := hc _ (m_blankEnd (m := m) (P := P) (sb := sb) (sep := sep) (Q := Q) (gacc := gacc)
          (xs := xs) (k₁ := k₁) (main := main) (v₀ := v₀) hKs (t := t + 1) (by omega) k (j := j)
          (by omega))
        simp only [List.map_cons, List.map_nil] at h
        obtain ⟨c', h1, h2⟩ := cellRel1_true h
        rw [h1, h2]
        simp only [cellOf]
        rw [List.getElem?_eq_none (by have := hlen k; omega)]
        rfl
  have h := hc _ (m_tctl (sb := sb) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs) (k₁ := k₁)
    (main := main) (v₀ := v₀) (Ks := Ks) (S := S) (m := m) (d := d) (P := P) ht)
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨R, R', h1, h2, h3⟩ := ctlRel2_true h
  rw [hrep.1] at h1; cases h1
  rw [transCP_iff m d hd] at h3
  refine ⟨?_, hcells⟩
  rw [h2, ctl_of_links hKs U hUd a hU hc (by omega) (by omega) _ R' h2 h3.1 h3.2 hcells]

/-- A witness sequence: symbols or blanks, never a symbol after a blank. -/
theorem wit_extract (Q : ℕ) : ∀ (f : ℕ → Option (Sig Γ)), f Q = none →
    (∀ j < Q, witP sb (f j) (f (j + 1))) →
    ∃ w : List Bool, w.length ≤ Q ∧ ∀ j ≤ Q, f j = ((w.map sb)[j]?).map (fun g => ⟨k₀, g⟩) := by
  induction Q with
  | zero => intro f h0 _; exact ⟨[], le_rfl, fun j hj => by
      obtain rfl : j = 0 := by omega
      simpa using h0⟩
  | succ Q ih =>
    intro f hQ hw
    obtain ⟨w', hw'l, hw'⟩ := ih (fun j => f (j + 1)) hQ (fun j hj => hw (j + 1) (by omega))
    rcases (hw 0 (by omega)).1 with h0 | ⟨b, hb⟩
    · have hn : ∀ j ≤ Q + 1, f j = none := by
        intro j hj
        induction j with
        | zero => exact h0
        | succ j ihj => exact (hw j (by omega)).2 (ihj (by omega))
      exact ⟨[], by simp, fun j hj => by simpa using hn j hj⟩
    · refine ⟨b :: w', by simp; omega, fun j hj => ?_⟩
      cases j with
      | zero => simpa using hb
      | succ j => simpa using hw' j (by omega)

theorem rep2_init (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (a : ℕ → V2 Γ Λ σ) (hU : ∀ v, a v ∈ U) (hc : ∀ c ∈ CS, c.rel (c.scope.map a) = true)
    (hS1 : xs.length + 2 + Q ≤ S) (hdS : d ≤ S) :
    ∃ w : List Bool, w.length ≤ Q ∧
      Rep2 d Ks S a 0 (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb)) := by
  -- the fixed symbol variables
  have hZ : ∀ b : Bool, a (if b then 1 else 0) = Sum.inr (some ⟨k₀, sb b⟩) := by
    intro b
    cases b
    · have h := hc _ (m_Z0 (m := m) (d := d) (P := P) (Ks := Ks) (S := S) (T := T) (k₁ := k₁)
        (main := main) (v₀ := v₀) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs) hKs)
      simp only [List.map_cons, List.map_nil] at h
      obtain ⟨c, h1, h2⟩ := cellRel1_true h
      rw [if_neg (by simp), h1, h2]
    · have h := hc _ (m_Z1 (m := m) (d := d) (P := P) (Ks := Ks) (S := S) (T := T) (k₁ := k₁)
        (main := main) (v₀ := v₀) (sep := sep) (Q := Q) (gacc := gacc) (xs := xs) hKs)
      simp only [List.map_cons, List.map_nil] at h
      obtain ⟨c, h1, h2⟩ := cellRel1_true h
      rw [if_pos rfl, h1, h2]
  -- the witness region
  let f : ℕ → Option (Sig Γ) := fun j =>
    match a (cv2 Ks S 0 k₀ (xs.length + 1 + j)) with
    | Sum.inr c => c
    | Sum.inl _ => none
  have hf : ∀ j ≤ Q, a (cv2 Ks S 0 k₀ (xs.length + 1 + j)) = Sum.inr (f j) := by
    intro j hj
    rcases Nat.lt_or_ge j Q with hj' | hj'
    · have h := hc _ (m_wit (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main) (v₀ := v₀)
        (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs) hj')
      simp only [List.map_cons, List.map_nil] at h
      obtain ⟨c, c', h1, -, -⟩ := cellRel2_true h
      simp only [f, h1]
    · rw [show j = Q by omega]
      have h := hc _ (m_blank0 (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main)
        (v₀ := v₀) (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs) (Q := Q)
        (j := 0) (by omega))
      simp only [List.map_cons, List.map_nil, Nat.add_zero] at h
      obtain ⟨c, h1, -⟩ := cellRel1_true h
      simp only [f, h1]
  have hfQ : f Q = none := by
    have h := hc _ (m_blank0 (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main)
      (v₀ := v₀) (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs) (Q := Q)
      (j := 0) (by omega))
    simp only [List.map_cons, List.map_nil, Nat.add_zero] at h
    obtain ⟨c, h1, h2⟩ := cellRel1_true h
    simp only [f, h1, h2]
  have hfw : ∀ j < Q, witP sb (f j) (f (j + 1)) := by
    intro j hj
    have h := hc _ (m_wit (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main) (v₀ := v₀)
      (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs) hj)
    simp only [List.map_cons, List.map_nil] at h
    rw [hf j (by omega), show xs.length + 2 + j = xs.length + 1 + (j + 1) by omega,
      hf (j + 1) (by omega)] at h
    obtain ⟨c, c', h1, h2, h3⟩ := cellRel2_true h
    cases h1; cases h2; exact h3
  obtain ⟨w, hwl, hw⟩ := wit_extract (sb := sb) Q f hfQ hfw
  refine ⟨w, hwl, ?_⟩
  set c0 := initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb) with hc0
  have hcells : ∀ k, ∀ p < S, a (cv2 Ks S 0 k p) = Sum.inr (cellOf c0 k p) := by
    intro k p hp
    by_cases hk : k = k₀
    · subst hk
      have hst : c0.stk k = xs.map sb ++ sep :: w.map sb := by simp [hc0, initCfg]
      simp only [cellOf, hst]
      rcases Nat.lt_trichotomy p xs.length with h1 | h1 | h1
      · have h := hc _ (m_bit (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main)
          (v₀ := v₀) (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (Q := Q) h1)
        simp only [List.map_cons, List.map_nil] at h
        obtain ⟨c, c', e1, e2, e3⟩ := cellRel2_true h
        have hb : NthTM.bit xs p = if xs[p] then 1 else 0 := by
          simp [NthTM.bit, List.getElem?_eq_getElem h1]
        rw [hb, hZ] at e2
        cases e2
        rw [e1, e3, List.getElem?_append_left (by simpa using h1)]
        simp [List.getElem?_eq_getElem h1]
      · subst h1
        have h := hc _ (m_sep (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main)
          (v₀ := v₀) (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (Q := Q) (xs := xs))
        simp only [List.map_cons, List.map_nil] at h
        obtain ⟨c, e1, e2⟩ := cellRel1_true h
        rw [e1, e2, List.getElem?_append_right (by simp)]
        simp
      · by_cases h2 : p ≤ xs.length + 1 + Q
        · obtain ⟨j, rfl⟩ : ∃ j, p = xs.length + 1 + j := ⟨p - (xs.length + 1), by omega⟩
          rw [hf j (by omega), hw j (by omega), List.getElem?_append_right (by simp; omega)]
          simp only [List.length_map, show xs.length + 1 + j - xs.length = j + 1 by omega,
            List.getElem?_cons_succ]
        · obtain ⟨j, rfl⟩ : ∃ j, p = xs.length + 1 + Q + j := ⟨p - (xs.length + 1 + Q), by omega⟩
          have h := hc _ (m_blank0 (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main)
            (v₀ := v₀) (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs)
            (Q := Q) (j := j) (by omega))
          simp only [List.map_cons, List.map_nil] at h
          obtain ⟨c, e1, e2⟩ := cellRel1_true h
          rw [e1, e2, List.getElem?_eq_none (by simp; omega)]
          rfl
    · have h := hc _ (m_other (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (main := main)
        (v₀ := v₀) (sep := sep) (gacc := gacc) (Ks := Ks) (S := S) (sb := sb) (xs := xs)
        (Q := Q) hKs hk hp)
      simp only [List.map_cons, List.map_nil] at h
      obtain ⟨c, e1, e2⟩ := cellRel1_true h
      rw [e1, e2]
      simp [cellOf, hc0, initCfg, hk]
  have h := hc _ (m_ctl0 (m := m) (d := d) (P := P) (T := T) (k₁ := k₁) (sep := sep) (gacc := gacc)
    (Ks := Ks) (S := S) (sb := sb) (xs := xs) (Q := Q) (main := main) (v₀ := v₀))
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨R, e1, e2⟩ := ctlRel1_true h
  refine ⟨?_, hcells⟩
  rw [e1, ctl_of_links hKs U hUd a hU hc hdS (Nat.zero_le _) c0 R e1 (by simp [hc0, initCfg, e2.1])
    (by simp [hc0, initCfg, e2.2]) hcells]

/-- **Soundness of the second tableau.** -/
theorem tab2_sound (hd : ∀ lab, sdepth (m lab) ≤ d) (hP : ∀ lab, pushes (m lab) ≤ P)
    (hKs : ∀ k, k ∈ Ks) (U : List (V2 Γ Λ σ))
    (hUd : ∀ R, (Sum.inl R : V2 Γ Λ σ) ∈ U → ∀ k, (R.win k).length ≤ d)
    (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S)
    (hlen : ∀ w : List Bool, w.length ≤ Q → ∀ t ≤ T, ∀ k,
      (((stepStay m)^[t] (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb))).stk k).length ≤
        S - (d + 1))
    (hsat : CSPSat U CS) :
    ∃ w : List Bool, w.length ≤ Q ∧
      cellOf ((stepStay m)^[T] (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb))) k₁ 0 =
        some ⟨k₁, gacc⟩ := by
  obtain ⟨a, hU, hc⟩ := hsat
  obtain ⟨w, hwl, h0⟩ := rep2_init hKs U hUd a hU hc hS1 (by omega)
  refine ⟨w, hwl, ?_⟩
  have hrep : ∀ t ≤ T, Rep2 d Ks S a t
      ((stepStay m)^[t] (initCfg main v₀ k₀ (xs.map sb ++ sep :: w.map sb))) := by
    intro t ht
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact rep2_step hd hP hKs U hUd a hU hc hS2 (by omega) _ (ih (by omega))
        (fun k => by have := hlen w hwl (t + 1) ht k; rwa [Function.iterate_succ_apply'] at this)
  have h := hc _ (m_final (m := m) (d := d) (P := P) (T := T) (k₀ := k₀) (sep := sep) (gacc := gacc)
    (Ks := Ks) (S := S) (sb := sb) (xs := xs) (Q := Q) (main := main) (v₀ := v₀) (k₁ := k₁))
  simp only [List.map_cons, List.map_nil] at h
  obtain ⟨c, e1, e2⟩ := cellRel1_true h
  rw [(hrep T le_rfl).2 k₁ 0 (by omega)] at e1
  cases e1
  exact e2

end Sound

end PvnpReal
