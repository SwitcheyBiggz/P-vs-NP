/-
  PvnpReal.QbfTabN — the nondeterministic tableau as a chain of row blocks (copy of the
  `QbfTab` chain section with `csTransN`/`csFinalH`): `tab_of_chainN`, `chain_of_tabN`.
-/
import PvnpReal.TabN

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2

section TabNShift

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (d P : ℕ) (Ks : List K) (S : ℕ) (k₀ k₁ : K)
  (gacc : Γ k₁)

theorem csTransN_shift (a t : ℕ) :
    csTransN m alt d P Ks S (a + t) = (csTransN m alt d P Ks S a).map (shC (t * W2 Ks S)) := by
  unfold csTransN
  rw [csTrans_shift]
  simp only [csTrans, List.map_cons, List.tail_cons]
  congr 1
  simp only [shC, List.map_cons, List.map_nil, sv2, add_mul, one_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem csFinalH_shift (a t : ℕ) :
    csFinalH (Λ := Λ) (σ := σ) Ks S (a + t) k₁ gacc =
      (csFinalH Ks S a k₁ gacc).map (shC (t * W2 Ks S)) := by
  unfold csFinalH
  rw [csFinal_shift, List.map_append]
  congr 1
  simp only [shC, List.map_cons, List.map_nil, sv2, add_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem scope_transN (hS2 : 2 * d + P + 1 ≤ S) (t : ℕ) :
    ∀ c ∈ csTransN m alt d P Ks S t, ∀ v ∈ c.scope, sv2 Ks S t ≤ v ∧ v < sv2 Ks S (t + 2) := by
  intro c hc v hv
  rcases List.mem_cons.1 hc with rfl | h
  · exact scope_trans m d P Ks S hS2 t _ (List.mem_cons_self ..) v hv
  · exact scope_trans m d P Ks S hS2 t c (List.mem_of_mem_tail h) v hv

theorem scope_finalH (hk₁ : k₁ ∈ Ks) (hS : 1 ≤ S) (t : ℕ) :
    ∀ c ∈ csFinalH (Λ := Λ) (σ := σ) Ks S t k₁ gacc, ∀ v ∈ c.scope,
      sv2 Ks S t ≤ v ∧ v < sv2 Ks S (t + 1) := by
  intro c hc v hv
  rcases List.mem_append.1 hc with h | h
  · exact scope_final Ks S k₁ gacc hk₁ hS t c h v hv
  · simp only [List.mem_singleton] at h; subst h
    simp only [List.mem_singleton] at hv; subst hv
    have := sv2_succ Ks S t
    have : 0 < W2 Ks S := by unfold W2; omega
    omega

end TabNShift

section ChainN

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} [DecidableEq (V2 Γ Λ σ)]
variable (m : Λ → Stmt Γ Λ σ) (alt : Λ → Λ) (d P : ℕ) (Ks : List K) (S : ℕ) (k₀ k₁ : K)
  (main : Λ) (v₀ : σ) (sb : Bool → Γ k₀) (sep : Γ k₀) (Q : ℕ) (gacc : Γ k₁) (xs : List Bool)
  (U : List (V2 Γ Λ σ))

/-- Fixed symbols, initial row (row 0) and final halted row (row 1). -/
noncomputable def tabTopN : CNF :=
  AL U 0 (sv2 Ks S 2) ++
    HC U (csZ k₀ sb ++ csInit Ks S k₀ main v₀ sb sep Q xs ++ csFinalH Ks S 1 k₁ gacc)

/-- Rows 0 and 1 and the transition between them. -/
noncomputable def tabB0N : CNF :=
  AL U (sv2 Ks S 0) (2 * W2 Ks S) ++
    HC U (csRow d Ks S 0 ++ csRow d Ks S 1 ++ csTransN m alt d P Ks S 0)

/-- The one-step relation between two row blocks of hot bits. -/
def tabRN (u v : List Bool) : Prop :=
  evalCNF (tabB0N m alt d P Ks S U) (asg (List.replicate (2 * U.length) false ++ u ++ v)) = true

theorem tabTopN_vars (hk₀ : k₀ ∈ Ks) (hk₁ : k₁ ∈ Ks) (hS1 : xs.length + 2 + Q ≤ S) :
    ∀ cl ∈ tabTopN Ks S k₀ k₁ main v₀ sb sep Q gacc xs U, ∀ l ∈ cl,
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
    · have := scope_finalH (Λ := Λ) (σ := σ) Ks S k₁ gacc hk₁ (by omega) 1 c hc v hv
      have r2 : sv2 Ks S (1 + 1) = sv2 Ks S 2 := rfl
      omega

theorem tabB0N_vars (hS2 : 2 * d + P + 1 ≤ S) :
    ∀ cl ∈ tabB0N m alt d P Ks S U, ∀ l ∈ cl,
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
    · have := scope_transN m alt d P Ks S hS2 0 c hc v hv; exact this

/-- **From a chain of row blocks to a solution of the tableau.** -/
theorem tab_of_chainN (hU : U ≠ []) (hk₀ : k₀ ∈ Ks) (hk₁ : k₁ ∈ Ks)
    (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S) (T : ℕ) (hT : 1 ≤ T)
    (g : List Bool) (htop : evalCNF (tabTopN Ks S k₀ k₁ main v₀ sb sep Q gacc xs U) (asg g) = true)
    (hch : Chain (tabRN m alt d P Ks S U) (W2 Ks S * U.length) T
      (rdF (asg g) (2 * U.length) (W2 Ks S * U.length))
      (rdF (asg g) (2 * U.length + W2 Ks S * U.length) (W2 Ks S * U.length))) :
    CSPSat U (tabNCS m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs) := by
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
  rw [tabTopN, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff] at htop
  obtain ⟨hAL, hHC⟩ := htop
  set a := decB U hU β with ha
  refine ⟨a, fun v => decB_mem U hU β v, fun c hc => ?_⟩
  -- one step of the chain gives the constraints between rows `t` and `t + 1`
  have hstep : ∀ t < T, ∀ c0 ∈ csRow d Ks S 0 ++ csRow d Ks S 1 ++ csTransN m alt d P Ks S 0,
      (shC (t * W2 Ks S) c0).rel ((shC (t * W2 Ks S) c0).scope.map a) = true := by
    intro t ht c0 hc0
    have hR := huR t ht
    unfold tabRN at hR
    rw [tabB0N, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff] at hR
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
      · exact scope_transN m alt d P Ks S hS2 0 c0 h v hv
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
  simp only [tabNCS, List.mem_append, List.mem_flatMap, List.mem_range] at hc
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
  · rw [show t = 0 + t by omega, csTransN_shift] at htr
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 htr
    exact hstep t ht c0 (by simp [hc0])
  · -- the final row
    rw [show T = 1 + (T - 1) by omega, csFinalH_shift] at hfin
    obtain ⟨c1, hc1, rfl⟩ := List.mem_map.1 hfin
    have hsc := scope_finalH (Λ := Λ) (σ := σ) Ks S k₁ gacc hk₁ (by omega) 1 c1 hc1
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
theorem chain_of_tabN (hU : U ≠ []) (hk₀ : k₀ ∈ Ks) (hk₁ : k₁ ∈ Ks)
    (hS1 : xs.length + 2 + Q ≤ S) (hS2 : 2 * d + P + 1 ≤ S) (T : ℕ) (hT : 1 ≤ T)
    (h : CSPSat U (tabNCS m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs)) :
    ∃ g : List Bool, g.length = 2 * U.length + 2 * (W2 Ks S * U.length) ∧
      evalCNF (tabTopN Ks S k₀ k₁ main v₀ sb sep Q gacc xs U) (asg g) = true ∧
      Chain (tabRN m alt d P Ks S U) (W2 Ks S * U.length) T
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
      have := tabTopN_vars Ks S k₀ k₁ main v₀ sb sep Q gacc xs U hk₀ hk₁ hS1 cl hcl l hl
      rw [← hn] at this; exact this))]
    rw [tabTopN, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff]
    refine ⟨fun i _ => alo_hot U a' _ (ha' _), fun c hc' => ?_⟩
    refine con_hot U a' c (fun v _ => ha' v) ?_
    rcases List.mem_append.1 hc' with hZI | hF
    · have hsc := scope_init (Λ := Λ) (σ := σ) Ks S k₀ main v₀ sb sep Q xs hk₀ hS1 c hZI
      rw [show c.scope.map a' = c.scope.map a from List.map_congr_left (fun v hv => by
        simp only [a', if_pos (hsc v hv)])]
      exact hc c (mN_pre hZI)
    · have hsc := scope_finalH (Λ := Λ) (σ := σ) Ks S k₁ gacc hk₁ (by omega) 1 c hF
      have hmem : shC s c ∈ csFinalH Ks S T k₁ gacc := by
        rw [show T = 1 + (T - 1) by omega, csFinalH_shift]
        exact List.mem_map.2 ⟨c, hF, rfl⟩
      have := hc _ (List.mem_append_right _ hmem)
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
      unfold tabRN
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
        have := tabB0N_vars m alt d P Ks S U hS2 cl hcl l hl
        rw [← hn] at this
        exact hB _ this.1 this.2)]
      rw [tabB0N, evalCNF_app, Bool.and_eq_true, AL_iff, HC_iff]
      refine ⟨fun i _ => alo_hot U at' _ (haU _), fun c0 hc0 => ?_⟩
      refine con_hot U at' c0 (fun v _ => haU _) ?_
      have hmem : shC (t * W2 Ks S) c0 ∈ tabNCS m alt d P Ks S T k₀ k₁ main v₀ sb sep Q gacc xs := by
        simp only [List.mem_append] at hc0
        rcases hc0 with (h | h) | h
        · refine mN_row (t := 0 + t) (by omega) ?_
          rw [csRow_shift]; exact List.mem_map.2 ⟨c0, h, rfl⟩
        · refine mN_row (t := 1 + t) (by omega) ?_
          rw [csRow_shift]; exact List.mem_map.2 ⟨c0, h, rfl⟩
        · refine mN_trans (t := 0 + t) (by omega) ?_
          rw [csTransN_shift]; exact List.mem_map.2 ⟨c0, h, rfl⟩
      have := hc _ hmem
      rwa [shC_rel] at this

end ChainN

end PvnpReal
