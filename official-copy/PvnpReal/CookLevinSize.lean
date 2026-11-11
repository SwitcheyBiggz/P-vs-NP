/-
  PvnpReal.CookLevinSize — the Cook–Levin formula `clCNF q h x` has an encoding whose length is
  bounded by an explicit polynomial in `|x|`.
-/
import PvnpReal.CookLevinTab
import PvnpReal.Size

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

open scoped Classical

section TabSize

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
variable (m : Λ → Stmt Γ Λ σ) (d : ℕ) (Ks : List K) (S : ℕ)
  (main : Λ) (v₀ : σ) (k₀ : K) (pre : List (Γ k₀)) (allowed : Γ k₀ → Prop) (Q T : ℕ)
  (cacc : Cfg Γ Λ σ)

theorem tabCS_length :
    (tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc).length ≤
      2 + S + (2 * T + 1) * (1 + Ks.length * S) + Ks.length * S := by
  have hrow : ∀ (f : K → ℕ → Constraint (TVal Γ Λ σ)),
      (Ks.flatMap (fun k => (List.range S).map (f k))).length ≤ Ks.length * S :=
    fun f => flatMap_len_le _ _ _ (fun k _ => by simp)
  have h1 := flatMap_len_le (List.range (T + 1)) (fun t =>
    (⟨[sv Ks S t], rel1 (rowSummP d S)⟩ : Constraint (TVal Γ Λ σ)) ::
    Ks.flatMap (fun k => (List.range S).map (fun i =>
      ⟨[sv Ks S t, cv Ks S t k i], rel2 (linkP d k i)⟩))) (1 + Ks.length * S)
    (fun t _ => by rw [List.length_cons]; have := hrow (fun k i =>
      ⟨[sv Ks S t, cv Ks S t k i], rel2 (linkP d k i)⟩); omega)
  have h2 := flatMap_len_le (List.range T) (fun t =>
    (⟨[sv Ks S t, sv Ks S (t + 1)], rel2s (transSummP m d)⟩ : Constraint (TVal Γ Λ σ)) ::
    Ks.flatMap (fun k => (List.range S).map (fun i =>
      ⟨[sv Ks S t, cv Ks S t k i, cv Ks S (t + 1) k i], rel3 (transCellP m d k i)⟩)))
    (1 + Ks.length * S)
    (fun t _ => by rw [List.length_cons]; have := hrow (fun k i =>
      ⟨[sv Ks S t, cv Ks S t k i, cv Ks S (t + 1) k i], rel3 (transCellP m d k i)⟩); omega)
  have h3 := hrow (fun k i => ⟨[cv Ks S T k i], relC (finalCellP cacc k i)⟩)
  simp only [List.length_range] at h1 h2
  unfold tabCS
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  have : (2 * T + 1) * (1 + Ks.length * S) = (T + 1) * (1 + Ks.length * S) +
    T * (1 + Ks.length * S) := by ring
  omega

theorem tabCS_scope_len :
    ∀ c ∈ tabCS m d Ks S main v₀ k₀ pre allowed Q T cacc, c.scope.length ≤ 3 := by
  intro c hc
  simp only [tabCS, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | ((((⟨i, hi, rfl⟩ | ⟨t, ht, rfl | ⟨k, -, i, hi, rfl⟩⟩) |
    ⟨t, ht, rfl | ⟨k, -, i, hi, rfl⟩⟩) | rfl) | ⟨k, -, i, hi, rfl⟩) <;> simp

theorem tabValues_length [Fintype K] [Fintype Λ] [Fintype σ] (L : List (Sig Γ))
    (u0 : TVal Γ Λ σ) :
    (tabValues d S L u0).length ≤
      Fintype.card (Option Λ) * Fintype.card σ * (S + 1) ^ Fintype.card K *
        (upTo L d).length ^ Fintype.card K + L.length + 1 := by
  unfold tabValues
  rw [Finset.length_toList]
  refine le_trans (Finset.card_union_le _ _) ?_
  refine Nat.add_le_add (le_trans (Finset.card_union_le _ _) ?_) (by simp)
  refine Nat.add_le_add (le_trans Finset.card_image_le ?_)
    (le_trans (List.toFinset_card_le _) (by simp))
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_piFinset, Finset.card_range,
    Finset.prod_const]
  have h1 := Nat.pow_le_pow_left (List.toFinset_card_le (upTo L d)) (Fintype.card K)
  calc _ = Fintype.card (Option Λ) * Fintype.card σ * (S + 1) ^ Fintype.card K *
        (upTo L d).toFinset.card ^ Fintype.card K := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h1

end TabSize

section VerifierSize

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {V : List Bool × List Bool → Bool} (q : Polynomial ℕ)
  (h : TM2ComputableInPolyTime pairEnc encodeBool V)

/-- Bound on the number of tableau values, as a function of the space bound `S`. -/
noncomputable def clUB (S : ℕ) : ℕ :=
  Fintype.card (Option h.tm.Λ) * Fintype.card h.tm.σ * (S + 1) ^ Fintype.card h.tm.K *
    (upTo (clL h.tm) (clD h.tm)).length ^ Fintype.card h.tm.K + (clL h.tm).length + 1

/-- The size bound as an explicit function of `S` and `T`. -/
noncomputable def clBound (S T : ℕ) : ℕ :=
  let kc := Fintype.card h.tm.K
  let Nv := (T + 1) * (1 + kc * S)
  let cs := 2 + S + (2 * T + 1) * (1 + kc * S) + kc * S
  (Nv + cs * (clUB h S + 1) ^ 3) * ((clUB h S + 3) * (Nv * clUB h S + 3) + 2) + 1

theorem clKs_length : (clKs h.tm).length = Fintype.card h.tm.K := by
  simp [clKs]

theorem clCNF_size_le (x : List Bool) :
    (encodeCNF (clCNF q h x)).length ≤ clBound h (clS q h x) (clT q h x) := by
  unfold clCNF tabCNF
  set S := clS q h x
  set T := clT q h x
  set U := tabValues (clD h.tm) S (clL h.tm) (clU0 h)
  have hU : U.length ≤ clUB h S := tabValues_length _ _ _ _
  have hcs := tabCS_length h.tm.m (clD h.tm) (clKs h.tm) S h.tm.main h.tm.initialState h.tm.k₀
    (clPre h x) (clAllowed h) (q.eval x.length) T (clAcc h)
  refine le_trans (cspCNF_size U _ _ (tabCS_scope_lt _ _ _ _ _ _ _ _ _ _ _ _ (clKs_spec h))
    (tabCS_scope_len _ _ _ _ _ _ _ _ _ _ _ _)) ?_
  rw [clKs_length] at hcs
  unfold clBound rowW
  rw [clKs_length]
  simp only
  gcongr

/-- The polynomial bounding the size of the Cook–Levin formula. -/
noncomputable def clPoly : Polynomial ℕ :=
  let kc := Fintype.card h.tm.K
  let PN : Polynomial ℕ := Polynomial.X + 1 + q
  let PT : Polynomial ℕ := h.time.comp PN
  let PS : Polynomial ℕ := PN + Polynomial.C (pushTotal h.tm) * PT
  let PU : Polynomial ℕ :=
    Polynomial.C (Fintype.card (Option h.tm.Λ) * Fintype.card h.tm.σ) * (PS + 1) ^ kc *
      Polynomial.C ((upTo (clL h.tm) (clD h.tm)).length ^ kc) +
    Polynomial.C ((clL h.tm).length + 1)
  let PNv : Polynomial ℕ := (PT + 1) * (1 + Polynomial.C kc * PS)
  let Pcs : Polynomial ℕ := 2 + PS + (2 * PT + 1) * (1 + Polynomial.C kc * PS) +
    Polynomial.C kc * PS
  (PNv + Pcs * (PU + 1) ^ 3) * ((PU + 3) * (PNv * PU + 3) + 2) + 1

theorem clPoly_eval (x : List Bool) :
    (clPoly q h).eval x.length = clBound h (clS q h x) (clT q h x) := by
  simp only [clPoly, clBound, clUB, clS, clT, clN, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  ring

/-- **The Cook–Levin formula has polynomial size**: its encoding is at most `clPoly(|x|)` long. -/
theorem clMap_size (x : List Bool) : (clMap q h x).length ≤ (clPoly q h).eval x.length := by
  rw [clPoly_eval]; exact clCNF_size_le q h x

end VerifierSize

end PvnpReal
