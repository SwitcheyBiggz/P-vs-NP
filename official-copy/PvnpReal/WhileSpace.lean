/-
  PvnpReal.WhileSpace — the while-loop machine as a **space-bounded decider**.
-/
import PvnpReal.WhileTM

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability WhileTM IterTM

theorem stk_len_le (M : FinTM2) (i c x o : List Bool) (l : List (M.Γ M.k₀)) (B : ℕ)
    (hi : i.length ≤ B) (hc : c.length ≤ B) (hx : x.length ≤ B) (ho : o.length ≤ B) (hl : l.length ≤ B)
    (k : IterTM.K M) :
    (stk M i c x o (Function.update (fun _ => []) M.k₀ l) k).length ≤ B := by
  rcases k with ((_ | _ | _ | _) | k)
  · exact hi
  · exact hc
  · exact hx
  · exact ho
  · show (Function.update (fun _ => []) M.k₀ l k).length ≤ B
    by_cases h : k = M.k₀
    · subst h; rw [Function.update_self]; exact hl
    · rw [Function.update_of_ne h]; simp

/-- **While-loop deciders are space-bounded.** If, from `true :: false :: x`, the polytime map `g`
keeps the state starting with `true` for `j ≤ J(|x|)` rounds, then stops with state tail `[f x]`,
and all states have length `≤ Lb(|x|)`, then `f` is decided in space
`n + Lb(n) + C·(2n + 2Lb(n) + P(Lb(n)) + 6)` (`P` = time polynomial of `g`). -/
theorem whileDecider {g : List Bool → List Bool} (hg : TM2ComputableInPolyTime strEnc strEnc g)
    (f : List Bool → Bool) (J Lb : ℕ → ℕ)
    (hF : ∀ x, ∃ j ≤ J x.length, (∀ i < j, (g^[i] (true :: false :: x)).head? = some true) ∧
      (g^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, (g^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      (g^[j] (true :: false :: x)).tail = [f x]) :
    ∃ h : TM2ComputableInTime strEnc encodeBool f,
      SpaceBounded h (fun n => n + Lb n + pushTotal h.tm *
        (2 * n + 2 * Lb n + hg.time.eval (Lb n) + 6)) := by
  let M := hg.tm
  let e := hg.inputAlphabet
  let eo := hg.outputAlphabet
  let P := hg.time
  let T : ℕ → ℕ := fun n => 2 * n + 5 + J n * (2 * Lb n + P.eval (Lb n) + 3) + (2 * Lb n + 3)
  -- the per-input analysis
  have key : ∀ x : List Bool, ∃ j ≤ J x.length,
      (∀ i < j, ∃ δ, 1 ≤ δ ∧ δ ≤ 2 * Lb x.length + P.eval (Lb x.length) + 3 ∧
        (flip bind (TM2.step (pmW M e eo)))^[δ] (some (Lcfg M (g^[i] (true :: false :: x)) e)) =
          some (Lcfg M (g^[i + 1] (true :: false :: x)) e)) ∧
      (g^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, (g^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      (g^[j] (true :: false :: x)).tail = [f x] := by
    intro x
    obtain ⟨j, hj, hhead, hlast, hlen, hout⟩ := hF x
    refine ⟨j, hj, fun i hi => ?_, hlast, hlen, hout⟩
    set y := g^[i] (true :: false :: x)
    obtain ⟨st, hst, ev⟩ : ∃ st ≤ P.eval (Lb x.length),
        (flip bind (TM2.step M.m))^[st] (some (initList M (y.map e.symm))) =
          some (haltList M ((g y).map eo.symm)) := by
      have hx := hg.outputsFun y
      have ev := hx.evals_in_steps
      simp only [Option.map_some] at ev
      refine ⟨hx.steps, ?_, ev⟩
      have := hx.steps_le_m
      simp only [strEnc] at this
      exact this.trans (poly_eval_mono P (hlen i (by omega)))
    have hr := roundW (e := e) (eo := eo) g y (hhead i hi) st ev
    have hgy : g y = g^[i + 1] (true :: false :: x) := by
      rw [Function.iterate_succ_apply']
    rw [hgy] at hr
    have hl1 := hlen (i + 1) (by omega)
    exact ⟨_, by omega, by omega, hr⟩
  have hreach : ∀ x : List Bool, ∀ j : ℕ, (∀ i < j, ∃ δ, 1 ≤ δ ∧
      δ ≤ 2 * Lb x.length + P.eval (Lb x.length) + 3 ∧
        (flip bind (TM2.step (pmW M e eo)))^[δ] (some (Lcfg M (g^[i] (true :: false :: x)) e)) =
          some (Lcfg M (g^[i + 1] (true :: false :: x)) e)) →
      ∃ s ≤ j * (2 * Lb x.length + P.eval (Lb x.length) + 3),
        (flip bind (TM2.step (pmW M e eo)))^[s] (some (Lcfg M (true :: false :: x) e)) =
          some (Lcfg M (g^[j] (true :: false :: x)) e) := by
    intro x j
    induction j with
    | zero => intro _; exact ⟨0, by omega, rfl⟩
    | succ j ih =>
      intro hr
      obtain ⟨s, hs, h1⟩ := ih (fun i hi => hr i (by omega))
      obtain ⟨δ, -, hδ, h2⟩ := hr j (by omega)
      refine ⟨δ + s, ?_, iter_chain h1 h2⟩
      have : (j + 1) * (2 * Lb x.length + P.eval (Lb x.length) + 3) =
          j * (2 * Lb x.length + P.eval (Lb x.length) + 3) +
            (2 * Lb x.length + P.eval (Lb x.length) + 3) := by ring
      omega
  have hex : ∀ x : List Bool, ∃ s ≤ T x.length,
      (flip bind (TM2.step (pmW M e eo)))^[s] (some (initList (tmW M e eo) x)) =
        some (haltList (tmW M e eo) ([f x] : List Bool)) := by
    intro x
    obtain ⟨j, hj, hr, hlast, hlen, hout⟩ := key x
    obtain ⟨s, hs, h2⟩ := hreach x j hr
    have h1 := startW (e := e) (eo := eo) x
    have h3 := finishW (e := e) (eo := eo) (g^[j] (true :: false :: x)) hlast
    rw [hout] at h3
    rw [initList_eqW, haltList_eqW]
    refine ⟨_, ?_, iter_chain (iter_chain h1 h2) h3⟩
    have : j * (2 * Lb x.length + P.eval (Lb x.length) + 3) ≤
        J x.length * (2 * Lb x.length + P.eval (Lb x.length) + 3) := Nat.mul_le_mul_right _ hj
    have hl := hlen j le_rfl
    have : [f x].length ≤ Lb x.length := by rw [← hout]; simp; omega
    simp only [List.length_cons, List.length_nil, T] at this ⊢
    omega
  let h : TM2ComputableInTime strEnc encodeBool f :=
    { tm := tmW M e eo
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := T
      outputsFun := fun x =>
        { steps := Classical.choose (hex x)
          evals_in_steps := by
            erw [List.map_id, List.map_id, Option.map_some]
            exact (Classical.choose_spec (hex x)).2
          steps_le_m := by
            have := (Classical.choose_spec (hex x)).1
            simpa [strEnc] using this } }
  refine ⟨h, fun x i c _ hc k => ?_⟩
  obtain ⟨j, hj, hr, hlast, hlen, hout⟩ := key x
  set n := x.length
  set L := Lb n
  have hc' : (flip bind (tmW M e eo).step)^[i] (some (initList (tmW M e eo) x)) = some c := by
    have e0 : List.map (Equiv.refl Bool).invFun (strEnc x) = x := by simp [strEnc]
    rw [← e0]; exact hc
  rw [initList_eqW] at hc'
  let Good : (tmW M e eo).Cfg → Prop := fun c =>
    c = (⟨some (.inr .A), (M.initialState, none), stk M x [] [] [] (fun _ => [])⟩ : PC (M := M)) ∨
    (∃ i ≤ j, c = Lcfg M (g^[i] (true :: false :: x)) e) ∨
    c = (⟨none, (M.initialState, none), stk M [] [] [] [f x] (fun _ => [])⟩ : PC (M := M))
  have hsp := space_of_good (tmW M e eo) _ Good (n + L) (2 * n + 2 * L + P.eval L + 6) (by omega)
    (Or.inl rfl)
    (fun c hc => by
      rcases hc with rfl | ⟨i, hi, rfl⟩ | rfl
      · intro k
        have := stk_len_le M x [] [] [] [] (n + L) (by omega) (by simp) (by simp) (by simp)
          (by simp) k
        rw [Function.update_eq_self_iff.2 rfl] at this
        exact this
      · intro k
        exact stk_len_le M [] [] [] [] _ (n + L) (by simp) (by simp) (by simp) (by simp)
          (by simp; have := hlen i hi; omega) k
      · intro k
        have hl := hlen j le_rfl
        have : [f x].length ≤ L := by rw [← hout]; simp; omega
        have := stk_len_le M [] [] [] [f x] [] (n + L) (by simp) (by simp) (by simp)
          (by simp at this ⊢; omega) (by simp) k
        rw [Function.update_eq_self_iff.2 rfl] at this
        exact this)
    (fun c hc => by
      rcases hc with rfl | ⟨i, hi, rfl⟩ | rfl
      · left
        refine ⟨_, by omega, by omega, _, startW (e := e) (eo := eo) x, Or.inr (Or.inl ⟨0, by omega, rfl⟩)⟩
      · rcases Nat.lt_or_ge i j with hij | hij
        · obtain ⟨δ, hδ1, hδ, hrun⟩ := hr i hij
          left
          exact ⟨δ, hδ1, by omega, _, hrun, Or.inr (Or.inl ⟨i + 1, by omega, rfl⟩)⟩
        · have hij' : i = j := by omega
          subst hij'
          left
          have h3 := finishW (e := e) (eo := eo) (g^[i] (true :: false :: x)) hlast
          rw [hout] at h3
          refine ⟨_, by omega, by simp <;> omega, _, h3, Or.inr (Or.inr rfl)⟩
      · right; rfl)
  exact hsp i c hc' k

end PvnpReal
