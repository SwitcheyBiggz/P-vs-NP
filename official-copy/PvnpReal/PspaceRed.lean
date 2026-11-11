/-
  PvnpReal.PspaceRed — PSPACE is closed under polynomial-time many-one reductions.

  `TQBF_comp_in_PSPACE`: for polytime `r`, `x ↦ TQBF (r x)` is decided in polynomial space, by the
  same depth-first evaluator as `TQBF_in_PSPACE` whose first round applies `r`. With
  `TQBF_PSPACE_hard` this gives `InPSPACE.of_reduces`.
-/
import PvnpReal.QbfPrint

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing Computability

/-- The evaluator whose start round first applies `r`. -/
def gQr (r : List Bool → List Bool) (s : List Bool) : List Bool :=
  if NthTM.bit s 1 = 1 then gQ s
  else if NthTM.bit s 0 = 1 then gQ (true :: false :: r s.tail.tail) else gQ s

theorem PS.gQr {r : List Bool → List Bool} (hr : PS r) : PS (gQr r) := by
  have hT2 : PS (fun s => s.tail.tail) := PS.comp PS.tail PS.tail
  exact (PS.iteEq (PU.bitAt 1) (PU.const 1) PS.gQ (PS.iteEq (PU.bitAt 0) (PU.const 1)
    (PS.comp (PS.cons true (PS.cons false (PS.comp hT2 hr))) PS.gQ) PS.gQ)).congr (fun s => rfl)

theorem gQr_start (r : List Bool → List Bool) (x : List Bool) :
    gQr r (true :: false :: x) = St true false (decX (r x)) (decC (r x)) [] := by
  simp [gQr, NthTM.bit, gQ_start]

theorem gQr_good (r : List Bool → List Bool) {qs X s : List Bool} (h : GoodQ qs X s) :
    gQr r s = gQ s := by
  obtain ⟨m, v, p, rfl, -⟩ := h
  simp [gQr]

theorem iter_agree {α : Type*} {g g' : α → α} {P : α → Prop} (hP : ∀ s, P s → g' s = g s) :
    ∀ (j : ℕ) (s : α), (∀ i < j, P (g^[i] s)) → g'^[j] s = g^[j] s := by
  intro j
  induction j with
  | zero => intro s _; rfl
  | succ j ih =>
    intro s h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hP s (h 0 (by omega))]
    exact ih _ (fun i hi => by
      have := h (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this)

/-- The while-loop analysis of `gQr r` (cf. `TQBF_in_PSPACE`). -/
theorem gQr_hF {r : List Bool → List Bool} (hr : PS r) : ∃ (J : ℕ → ℕ) (Lp : Polynomial ℕ),
    ∀ x, ∃ j ≤ J x.length, (∀ i < j, ((gQr r)^[i] (true :: false :: x)).head? = some true) ∧
      ((gQr r)^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, ((gQr r)^[i] (true :: false :: x)).length ≤ Lp.eval x.length) ∧
      ((gQr r)^[j] (true :: false :: x)).tail = [tv (decC (r x)) (decX (r x)) []] := by
  classical
  let hR : TM2ComputableInPolyTime strEnc strEnc r := Classical.choice hr
  let mBp : Polynomial ℕ := Polynomial.X + Polynomial.C (pushTotal hR.tm) * hR.time
  have hm : ∀ x : List Bool, (r x).length ≤ mBp.eval x.length := fun x => by
    have := outLen_boundT hR.toTM2ComputableInTime x
    have e : mBp.eval x.length = x.length + pushTotal hR.tm * hR.time.eval x.length := by
      simp [mBp]
    rw [e]; exact this
  let f : List Bool → Bool := fun x => tv (decC (r x)) (decX (r x)) []
  let Lp : Polynomial ℕ := 21 * mBp + Polynomial.X + 14
  let Lb : ℕ → ℕ := fun n => Lp.eval n
  let J : ℕ → ℕ := fun n => 4 * 2 ^ (mBp.eval n) + 2
  have hF : ∀ x, ∃ j ≤ J x.length, (∀ i < j, ((gQr r)^[i] (true :: false :: x)).head? = some true) ∧
      ((gQr r)^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, ((gQr r)^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      ((gQr r)^[j] (true :: false :: x)).tail = [f x] := by
    intro x
    set y := r x
    set qs := decX y
    set X := decC y
    have hqs : qs.length ≤ y.length := decX_len y
    have hX : X.length ≤ y.length := decC_len y
    have hy : y.length ≤ mBp.eval x.length := hm x
    obtain ⟨j, hj, e, G⟩ := run_down qs X qs.length [] false (by simp) (by simp)
    simp only [List.length_nil, List.drop_zero] at e
    have agree : ∀ i ≤ j, (gQr r)^[i] (St true false qs X []) = gQ^[i] (St true false qs X []) :=
      fun i hi => iter_agree (fun s hs => gQr_good r hs) i _ (fun i' hi' => G i' (by omega))
    have e' : (gQr r)^[j] (St true false qs X []) = St false (tv X qs []) qs X [] := by
      rw [agree j le_rfl, e]
    have eS : (gQr r)^[1] (true :: false :: x) = St true false qs X [] := by
      rw [Function.iterate_one, gQr_start]
    have eF : (gQr r)^[1] (St false (tv X qs []) qs X []) = [false, tv X qs []] := by
      rw [Function.iterate_one, gQr_good r ⟨false, _, [], rfl, by simp⟩, gQ_up_nil]
    have eAll := iter_chain (iter_chain eS e') eF
    have hmid : ∀ i ≤ j, GoodQ qs X ((gQr r)^[i + 1] (true :: false :: x)) := by
      intro i hi
      rw [Function.iterate_succ_apply, gQr_start, agree i hi]; exact G i hi
    have hpow : 2 ^ qs.length ≤ 2 ^ (mBp.eval x.length) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨1 + (j + 1), by show _ ≤ 4 * 2 ^ (mBp.eval x.length) + 2; omega, fun i hi => ?_, ?_,
      fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · rfl
      · obtain ⟨m, v, p, hs, -⟩ := hmid i (by omega)
        rw [hs]; rfl
    · rw [eAll]; simp
    · have hL : Lb x.length = 21 * mBp.eval x.length + x.length + 14 := by
        simp [Lb, Lp]
      rw [hL]
      rcases i with _ | i
      · simp; omega
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · obtain ⟨m, v, p, hs, hp⟩ := hmid i (by omega)
          rw [hs]
          have := St_len m v qs X p hp
          omega
        · rw [show i + 1 = 1 + (j + 1) by omega, eAll]; simp
    · rw [eAll]; rfl
  exact ⟨J, Lp, hF⟩

/-- **Generic while-loop membership in PSPACE**: polytime round map, polynomial state length. -/
theorem InPSPACE.of_while {g : List Bool → List Bool} (hgP : PS g) (f : List Bool → Bool)
    (J : ℕ → ℕ) (Lp : Polynomial ℕ)
    (hF : ∀ x, ∃ j ≤ J x.length, (∀ i < j, (g^[i] (true :: false :: x)).head? = some true) ∧
      (g^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, (g^[i] (true :: false :: x)).length ≤ Lp.eval x.length) ∧
      (g^[j] (true :: false :: x)).tail = [f x]) :
    InPSPACE (fun x => f x = true) := by
  let hg : TM2ComputableInPolyTime strEnc strEnc g := Classical.choice hgP
  obtain ⟨h, hsp⟩ := whileDecider hg f J (fun n => Lp.eval n) hF
  let C := pushTotal h.tm
  let p : Polynomial ℕ := Polynomial.X + Lp + Polynomial.C C *
    (2 * Polynomial.X + 2 * Lp + hg.time.comp Lp + 6)
  refine ⟨p, f, h, fun x i c hi hc k => (hsp x i c hi hc k).trans (le_of_eq ?_), fun x => Iff.rfl⟩
  simp [p, C, Polynomial.eval_comp]

/-- **`x ↦ TQBF (r x)` is in PSPACE** for every polytime `r`. -/
theorem TQBF_comp_in_PSPACE {r : List Bool → List Bool} (hr : PS r) :
    InPSPACE (fun x => TQBF (r x)) := by
  obtain ⟨J, Lp, hF⟩ := gQr_hF hr
  exact InPSPACE.of_while (PS.gQr hr) _ J Lp hF

/-- Negating the final answer of a while-loop map. -/
def gNeg (g : List Bool → List Bool) (s : List Bool) : List Bool :=
  if NthTM.bit (g s) 0 = 1 then g s
  else if NthTM.bit (g s) 1 = 1 then [false, false] else [false, true]

theorem PS.gNeg {g : List Bool → List Bool} (hg : PS g) : PS (gNeg g) :=
  (PS.iteEq ((PU.bitAt 0).comp hg) (PU.const 1) hg (PS.iteEq ((PU.bitAt 1).comp hg) (PU.const 1)
    (PS.const _) (PS.const _))).congr (fun _ => rfl)

theorem gNeg_hF {g : List Bool → List Bool} {f : List Bool → Bool} {J : ℕ → ℕ} {Lb : ℕ → ℕ}
    {x : List Bool}
    (hF : ∃ j ≤ J x.length, (∀ i < j, (g^[i] (true :: false :: x)).head? = some true) ∧
      (g^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, (g^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      (g^[j] (true :: false :: x)).tail = [f x]) :
    ∃ j ≤ J x.length, (∀ i < j, ((gNeg g)^[i] (true :: false :: x)).head? = some true) ∧
      ((gNeg g)^[j] (true :: false :: x)).head? ≠ some true ∧
      (∀ i ≤ j, ((gNeg g)^[i] (true :: false :: x)).length ≤ Lb x.length) ∧
      ((gNeg g)^[j] (true :: false :: x)).tail = [!f x] := by
  obtain ⟨j, hj, hh, hl, hlen, ht⟩ := hF
  set s0 := true :: false :: x
  rcases j with _ | j0
  · exact (hl rfl).elim
  have hP : ∀ s, (g s).head? = some true → gNeg g s = g s := by
    intro s hs
    have : NthTM.bit (g s) 0 = 1 := by
      rcases hq : g s with _ | ⟨b, t⟩ <;> rw [hq] at hs <;> simp at hs
      subst hs; rfl
    simp [gNeg, this]
  have agree : ∀ i ≤ j0, (gNeg g)^[i] s0 = g^[i] s0 := fun i hi =>
    iter_agree hP i s0 (fun i' hi' => by
      rw [← Function.iterate_succ_apply' g]; exact hh _ (by omega))
  have hfin : (gNeg g)^[j0 + 1] s0 = [false, !f x] := by
    rw [Function.iterate_succ_apply', agree j0 le_rfl]
    rw [Function.iterate_succ_apply'] at hl ht
    obtain ⟨b, t, e⟩ : ∃ b t, g (g^[j0] s0) = b :: t := by
      cases hq : g (g^[j0] s0) with
      | nil => rw [hq] at ht; simp at ht
      | cons b t => exact ⟨b, t, rfl⟩
    rw [e] at hl ht
    simp only [List.tail_cons] at ht
    subst ht
    have hb : b = false := by cases b <;> simp_all
    subst hb
    unfold gNeg; rw [e]
    cases f x <;> rfl
  refine ⟨j0 + 1, hj, fun i hi => ?_, by rw [hfin]; simp, fun i hi => ?_, by rw [hfin]; rfl⟩
  · rw [agree i (by omega)]; exact hh i hi
  · rcases Nat.lt_or_ge i (j0 + 1) with h | h
    · rw [agree i (by omega)]; exact hlen i hi
    · rw [show i = j0 + 1 by omega, hfin]
      have := hlen (j0 + 1) le_rfl
      have h2 : (g^[j0 + 1] s0).length = 2 := by
        rcases hq : g^[j0 + 1] s0 with _ | ⟨b, t⟩
        · rw [hq] at ht; simp at ht
        · rw [hq] at ht; simp at ht; subst ht; rfl
      rw [h2] at this; exact this

/-- **`x ↦ ¬ TQBF (r x)` is in PSPACE** for every polytime `r`. -/
theorem TQBF_comp_compl_in_PSPACE {r : List Bool → List Bool} (hr : PS r) :
    InPSPACE (fun x => ¬ TQBF (r x)) := by
  obtain ⟨J, Lp, hF⟩ := gQr_hF hr
  exact (InPSPACE.of_while (PS.gNeg (PS.gQr hr)) _ J Lp (fun x => gNeg_hF (f := fun x => tv (decC (r x)) (decX (r x)) [])
      (Lb := fun n => Lp.eval n) (hF x))).congr
    (fun x => by
      show (!tv (decC (r x)) (decX (r x)) []) = true ↔ ¬ (tv (decC (r x)) (decX (r x)) [] = true)
      cases tv (decC (r x)) (decX (r x)) [] <;> simp)

/-- Every language that reduces to TQBF is in PSPACE. -/
theorem InPSPACE.of_reduces_TQBF {L : Language} (hr : PolyReduces L TQBF) : InPSPACE L := by
  obtain ⟨r, hr, hL⟩ := hr
  exact (TQBF_comp_in_PSPACE hr).congr (fun x => (hL x).symm)

/-- **PSPACE is closed under polynomial-time many-one reductions.** -/
theorem InPSPACE.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InPSPACE L') :
    InPSPACE L :=
  InPSPACE.of_reduces_TQBF (hr.trans (TQBF_PSPACE_hard L' h))

end PvnpReal

namespace PvnpReal

/-- **PSPACE is closed under complement.** -/
theorem InPSPACE.compl {L : Language} (h : InPSPACE L) : InPSPACE (fun x => ¬ L x) := by
  obtain ⟨r, hr, hL⟩ := TQBF_PSPACE_hard L h
  exact (TQBF_comp_compl_in_PSPACE hr).congr (fun x => not_congr (hL x).symm)

end PvnpReal
