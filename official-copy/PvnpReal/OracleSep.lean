/-
  PvnpReal.OracleSep — **Baker–Gill–Solovay, part 2**: an oracle `B` with `P^B ≠ NP^B`.

  `L_B x := ∃ y, |y| = |x| ∧ y ∈ B` is in `NP^B` (guess `y`, one query). `B` is built in stages
  against every pair (oracle program `p`, clock `k·(n+1)^k`), enumerated via `Encodable` and
  `Nat.unpair`: at stage `i` pick `n` beyond everything so far with `cQ(p)·k(n+1)^k < 2ⁿ`, run
  `p` on `1ⁿ` against the finite oracle built so far; if it accepts add nothing, otherwise add a
  length-`n` string it never queried. Trace congruence (`orun_congr`) shows the final `B` gives
  the same run, so `p` is wrong on `1ⁿ`.
-/
import PvnpReal.Oracle

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability Classical

namespace BGS

/-- The language `L_B`. -/
def LB (B : Language) : Language := fun x => ∃ y : List Bool, y.length = x.length ∧ B y

/-- The verifier: query the witness, accept iff the answer is yes. -/
def ver : OProg where
  k0 := 0
  kw := 1
  ka := 2
  main := 0
  init := 0
  inT := [0, 1]
  accT := [false, true]
  m := [.query 1 [false, true] (.push 2 [1] .halt) .halt]

theorem ver_run (B : Language) (x w : List Bool) :
    orunFor B ver 1 (OInit ver x w) =
      some (if B w then ⟨none, 0, Function.update (OInit ver x w).stk 2 [1]⟩
        else ⟨none, 0, (OInit ver x w).stk⟩) := by
  have hq : qstr [false, true] ((OInit ver x w).stk 1) = w := by
    simp only [OInit, ver, qstr]
    simp only [show (1 : ℕ) ≠ 0 by omega, if_false, if_true, List.map_map]
    conv_rhs => rw [← List.map_id w]
    congr 1; funext b; cases b <;> rfl
  have h2 : (OInit ver x w).stk 2 = [] := by simp [OInit, ver]
  show orunFor B ver 0 (oAux B (.query 1 [false, true] (.push 2 [1] .halt) .halt) 0
    (OInit ver x w).stk) = _
  simp only [oAux, hq]
  split_ifs
  · simp [oAux, orunFor, h2]
  · simp [orunFor]

theorem LB_in_NP (B : Language) : InNPO B (LB B) := by
  refine ⟨ver, 1, Polynomial.X, fun x => ⟨fun w _ => ?_, ?_⟩⟩
  · rw [show (1 : Polynomial ℕ).eval x.length = 1 by simp, ver_run]; exact ⟨_, rfl⟩
  · simp only [show (1 : Polynomial ℕ).eval x.length = 1 by simp, Polynomial.eval_X, ver_run]
    constructor
    · rintro ⟨y, hy, hB⟩
      refine ⟨y, _, hy, rfl, ?_⟩
      rw [if_pos hB]; simp [OAccepts, ver]
    · rintro ⟨w, h, hw, e, ha⟩
      refine ⟨w, hw, ?_⟩
      by_contra hB
      rw [if_neg hB] at e; cases e
      simp [OAccepts, ver, OInit] at ha

/-! ### The stage construction -/

def clk (k n : ℕ) : ℕ := k * (n + 1) ^ k

theorem exists_stage_n (c k ℓ : ℕ) : ∃ n, ℓ ≤ n ∧ c * clk k n < 2 ^ n := by
  obtain ⟨n0, hn0⟩ := poly_le_two_pow_eventually
    (Polynomial.C (c * k) * (Polynomial.X + 1) ^ k + 1)
  refine ⟨max ℓ n0, le_max_left _ _, ?_⟩
  have := hn0 (max ℓ n0) (le_max_right _ _)
  simp [clk] at this ⊢
  nlinarith

theorem exists_not_mem (Q : List (List Bool)) (n : ℕ) (h : Q.length < 2 ^ n) :
    ∃ y : List Bool, y.length = n ∧ y ∉ Q := by
  by_contra hc
  push_neg at hc
  have h1 : (Finset.univ : Finset (Fin n → Bool)).card ≤ Q.toFinset.card :=
    Finset.card_le_card_of_injOn (fun g => List.ofFn g)
      (fun g _ => by simp only [Finset.mem_coe, List.mem_toFinset]; exact hc _ (by simp))
      (fun a _ b _ e => List.ofFn_injective e)
  have h2 := List.toFinset_card_le Q
  simp at h1
  omega

structure St where
  S : List (List Bool)
  ℓ : ℕ

noncomputable def nOf (c k ℓ : ℕ) : ℕ := Classical.choose (exists_stage_n c k ℓ)

theorem nOf_spec (c k ℓ : ℕ) : ℓ ≤ nOf c k ℓ ∧ c * clk k (nOf c k ℓ) < 2 ^ nOf c k ℓ :=
  Classical.choose_spec (exists_stage_n c k ℓ)

noncomputable def yOf (n : ℕ) (Q : List (List Bool)) : List Bool :=
  if h : ∃ y : List Bool, y.length = n ∧ y ∉ Q then Classical.choose h else List.replicate n true

theorem yOf_len (n : ℕ) (Q : List (List Bool)) : (yOf n Q).length = n := by
  unfold yOf; split
  · next h => exact (Classical.choose_spec h).1
  · simp

/-- Data of stage `i` for program `p` and clock exponent `k`, from state `st`. -/
noncomputable def sn (p : OProg) (k : ℕ) (st : St) : ℕ := nOf p.cQ k st.ℓ
noncomputable def sx (p : OProg) (k : ℕ) (st : St) : List Bool := List.replicate (sn p k st) true
noncomputable def sQ (p : OProg) (k : ℕ) (st : St) : List (List Bool) :=
  orunQ (· ∈ st.S) p (clk k (sn p k st)) (OInit p (sx p k st) [])
def sAcc (p : OProg) (k : ℕ) (st : St) : Prop :=
  ∃ h, orunFor (· ∈ st.S) p (clk k (sn p k st)) (OInit p (sx p k st) []) = some h ∧ OAccepts p h

noncomputable def stepSt (i : ℕ) (st : St) : St :=
  match Encodable.decode (α := OProg) (Nat.unpair i).1 with
  | none => st
  | some p =>
    let k := (Nat.unpair i).2
    ⟨if sAcc p k st then st.S else yOf (sn p k st) (sQ p k st) :: st.S,
      sn p k st + 1 + ((sQ p k st).map List.length).sum⟩

noncomputable def stage : ℕ → St
  | 0 => ⟨[], 0⟩
  | i + 1 => stepSt i (stage i)

/-- **The oracle.** -/
def B : Language := fun s => ∃ i, s ∈ (stage i).S

theorem stage_succ (i : ℕ) : stage (i + 1) = stepSt i (stage i) := rfl

theorem step_mono (i : ℕ) (st : St) : (∀ s ∈ st.S, s ∈ (stepSt i st).S) ∧ st.ℓ ≤ (stepSt i st).ℓ ∧
    ∀ s ∈ (stepSt i st).S, s ∈ st.S ∨ st.ℓ ≤ s.length := by
  unfold stepSt
  split
  · exact ⟨fun s h => h, le_refl _, fun s h => Or.inl h⟩
  · next p _ =>
    have h1 := (nOf_spec p.cQ (Nat.unpair i).2 st.ℓ).1
    refine ⟨fun s h => ?_, ?_, fun s h => ?_⟩
    · dsimp only; split
      · exact h
      · exact List.mem_cons_of_mem _ h
    · dsimp only; unfold sn; omega
    · dsimp only at h; split at h
      · exact Or.inl h
      · rcases List.mem_cons.1 h with rfl | h
        · right; rw [yOf_len]; exact h1
        · exact Or.inl h

theorem stage_len : ∀ i, ∀ s ∈ (stage i).S, s.length < (stage i).ℓ := by
  intro i
  induction i with
  | zero => intro s h; simp [stage] at h
  | succ i ih =>
    intro s h
    rw [stage_succ] at h ⊢
    unfold stepSt at h ⊢
    cases he : Encodable.decode (α := OProg) (Nat.unpair i).1 with
    | none => simp only [he] at h ⊢; exact ih s h
    | some p =>
      simp only [he] at h ⊢
      have h1 := (nOf_spec p.cQ (Nat.unpair i).2 (stage i).ℓ).1
      split at h
      · have := ih s h; unfold sn; omega
      · rcases List.mem_cons.1 h with rfl | h
        · rw [yOf_len]; omega
        · have := ih s h; unfold sn; omega

theorem stage_mono {i j : ℕ} (hij : i ≤ j) :
    (∀ s ∈ (stage i).S, s ∈ (stage j).S) ∧ (stage i).ℓ ≤ (stage j).ℓ ∧
      ∀ s ∈ (stage j).S, s ∈ (stage i).S ∨ (stage i).ℓ ≤ s.length := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨fun s h => h, le_refl _, fun s h => Or.inl h⟩
  | succ j hij ih =>
    obtain ⟨a, b, c⟩ := ih
    obtain ⟨a', b', c'⟩ := step_mono j (stage j)
    rw [stage_succ]
    refine ⟨fun s h => a' s (a s h), le_trans b b', fun s h => ?_⟩
    rcases c' s h with h | h
    · exact c s h
    · right; omega

/-- Membership in `B` is decided at any stage up to length `ℓ`. -/
theorem B_split (m : ℕ) (s : List Bool) (hs : B s) : s ∈ (stage m).S ∨ (stage m).ℓ ≤ s.length := by
  obtain ⟨j, hj⟩ := hs
  rcases le_total j m with h | h
  · exact Or.inl ((stage_mono h).1 s hj)
  · exact (stage_mono h).2.2 s hj

/-- Polynomials are dominated by the clocks. -/
theorem poly_le_clk (T : Polynomial ℕ) : ∃ k, ∀ n, T.eval n ≤ clk k n := by
  refine ⟨T.eval 1 + T.natDegree, fun n => ?_⟩
  have h1 : T.eval n ≤ T.eval 1 * (n + 1) ^ T.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [one_pow, mul_one]
    apply Nat.mul_le_mul_left
    calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + 1) ^ T.natDegree := Nat.pow_le_pow_right (by omega) (by simp at hi; omega)
  unfold clk
  calc T.eval n ≤ T.eval 1 * (n + 1) ^ T.natDegree := h1
    _ ≤ (T.eval 1 + T.natDegree) * (n + 1) ^ (T.eval 1 + T.natDegree) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

/-- **`L_B ∉ P^B`.** -/
theorem LB_not_in_P : ¬ InPO B (LB B) := by
  rintro ⟨p, T, hp⟩
  obtain ⟨k, hk⟩ := poly_le_clk T
  set i := Nat.pair (Encodable.encode p) k
  set st := stage i
  have hdec : Encodable.decode (α := OProg) (Nat.unpair i).1 = some p := by
    simp [i, Nat.unpair_pair, Encodable.encodek]
  have hk' : (Nat.unpair i).2 = k := by simp [i, Nat.unpair_pair]
  have hstep : stage (i + 1) = ⟨if sAcc p k st then st.S else yOf (sn p k st) (sQ p k st) :: st.S,
      sn p k st + 1 + ((sQ p k st).map List.length).sum⟩ := by
    rw [stage_succ]; unfold stepSt; rw [hdec]; simp only [hk']; rfl
  set n := sn p k st
  set x := sx p k st
  have hxl : x.length = n := by simp [x, sx, n]
  obtain ⟨h, e, hL⟩ := hp x
  rw [hxl] at e
  have e' : orunFor B p (clk k n) (OInit p x []) = some h := orun_mono (hk n) e
  -- the stage run agrees with the real one
  have hQ : ∀ s ∈ sQ p k st, (s ∈ st.S ↔ B s) := by
    intro s hs
    constructor
    · intro h; exact ⟨i, h⟩
    · intro hB
      rcases B_split (i + 1) s hB with h1 | h1
      · rw [hstep] at h1
        dsimp only at h1
        split at h1
        · exact h1
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exfalso
            have hlen : (sQ p k st).length < 2 ^ n := by
              have := orunQ_len (· ∈ st.S) p (clk k n) (OInit p x [])
              have := (nOf_spec p.cQ k st.ℓ).2
              unfold sQ at *; exact lt_of_le_of_lt (by simpa [n, x] using ‹_ ≤ _›) this
            have hy : ∃ y : List Bool, y.length = n ∧ y ∉ sQ p k st := exists_not_mem _ _ hlen
            unfold yOf at hs
            rw [dif_pos hy] at hs
            exact (Classical.choose_spec hy).2 hs
          · exact h1
      · exfalso
        rw [hstep] at h1
        dsimp only at h1
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hs)
        omega
  have hrun : orunFor (· ∈ st.S) p (clk k n) (OInit p x []) = some h := by
    rw [orun_congr (· ∈ st.S) B p _ _ hQ]; exact e'
  by_cases ha : OAccepts p h
  · -- p accepts, but no string of length n is in B
    have hacc : sAcc p k st := ⟨h, hrun, ha⟩
    obtain ⟨y, hy, hB⟩ := hL.2 ha
    rw [hxl] at hy
    rcases B_split (i + 1) y hB with h1 | h1
    · rw [hstep] at h1; dsimp only at h1; rw [if_pos hacc] at h1
      have : y.length < st.ℓ := stage_len i y h1
      have := (nOf_spec p.cQ k st.ℓ).1
      simp only [n, sn] at hy; omega
    · rw [hstep] at h1; dsimp only at h1; simp only [n] at hy; omega
  · -- p rejects, but a string of length n was added to B
    have hacc : ¬ sAcc p k st := by
      rintro ⟨h', e2, ha'⟩; rw [hrun] at e2; cases e2; exact ha ha'
    apply ha
    apply hL.1
    refine ⟨yOf n (sQ p k st), by rw [yOf_len, hxl], i + 1, ?_⟩
    rw [hstep]; dsimp only; rw [if_neg hacc]; exact List.mem_cons_self

end BGS

/-- **Baker–Gill–Solovay (2): there is an oracle `B` with `P^B ≠ NP^B`.** -/
theorem exists_oracle_P_ne_NP : ∃ B : Language, ∃ L, InNPO B L ∧ ¬ InPO B L :=
  ⟨BGS.B, BGS.LB BGS.B, BGS.LB_in_NP _, BGS.LB_not_in_P⟩

end PvnpReal
