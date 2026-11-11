/-
  PvnpReal.Classes — NP is closed under reductions (NP = everything that reduces to SAT);
  EXP, P ⊆ EXP, EXP closed under reductions, and "SAT ∈ EXP ⇒ NP ⊆ EXP".
-/
import PvnpReal.PairMap

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing TM2 Computability

/-! ### NP is closed under polynomial-time reductions -/

/-- Anything that reduces to SAT is in NP: the verifier first maps `x # w ↦ g(x) # w`
(`pairMapComputable`), then runs the SAT verifier. Long witnesses are harmless because the SAT
verifier is sound for every `w` (`verify_sound`). -/
theorem InNP.of_reduces_SAT {L : Language} (hr : PolyReduces L SATLang) : InNP L := by
  obtain ⟨g, ⟨hg⟩, hL⟩ := hr
  refine ⟨fun p => verify (g p.1) p.2,
    Polynomial.X + (pushTotal hg.tm : Polynomial ℕ) * hg.time,
    ⟨composeGen (pairMapComputable hg) satVerifierComputable⟩, fun x => ?_⟩
  rw [hL]
  constructor
  · intro hx
    obtain ⟨w, hw, hv⟩ := (SATLang_iff_verify _).1 hx
    have hlen := outLen_bound hg x
    simp only [strEnc] at hlen
    refine ⟨w, ?_, hv⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_natCast, Nat.cast_id]
    omega
  · rintro ⟨w, -, hv⟩
    obtain ⟨φ, hφe, hφ⟩ := verify_sound _ w hv
    rw [hφe]
    exact (SATLang_encode_iff φ).2 ⟨asg w, hφ⟩

/-- **NP = the languages that reduce to SAT.** -/
theorem InNP_iff_reduces_SAT (L : Language) : InNP L ↔ PolyReduces L SATLang :=
  ⟨fun h => cookLevin.2 L h, InNP.of_reduces_SAT⟩

/-- **NP is closed under polynomial-time reductions.** -/
theorem InNP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InNP L') : InNP L :=
  InNP.of_reduces_SAT (hr.trans (cookLevin.2 L' h))

/-! ### EXP -/

/-- **EXP**: decided by a `FinTM2` within `2^{p(n)}` steps for some polynomial `p`. -/
def InEXP (L : Language) : Prop :=
  ∃ (f : List Bool → Bool) (p : Polynomial ℕ),
    (∃ h : TM2ComputableInTime strEnc encodeBool f, ∀ n, h.time n ≤ 2 ^ p.eval n) ∧
      ∀ x, L x ↔ f x = true

/-- **P ⊆ EXP.** -/
theorem P_subset_EXP (L : Language) (h : InP L) : InEXP L := by
  obtain ⟨f, ⟨hf⟩, hL⟩ := h
  exact ⟨f, hf.time, ⟨hf.toTM2ComputableInTime, fun n => (Nat.lt_two_pow_self).le⟩, hL⟩

/-- Output length of a machine with an arbitrary time bound. -/
theorem outLen_boundT {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + pushTotal h.tm * h.time (ea a).length := by
  have hx := h.outputsFun a
  have e := hx.evals_in_steps
  simp only [Option.map_some] at e
  have hl := iterate_len h.tm hx.steps _ _ e (ea a).length (by
    intro k
    simp only [initList]
    split
    · next hk => subst hk; simp
    · simp)
  have := hl h.tm.k₁
  simp only [haltList, dite_true, List.length_map] at this
  have hs := hx.steps_le_m
  have : pushTotal h.tm * hx.steps ≤ pushTotal h.tm * h.time (ea a).length :=
    Nat.mul_le_mul_left _ hs
  simp only [eq_mpr_eq_cast, cast_eq, List.length_map] at *
  omega

/-- **Composition with arbitrary time bounds**; the second bound is dominated by a monotone `B`. -/
noncomputable def composeInTime {α β γ αΓ βΓ γΓ : Type} [Inhabited βΓ] {ea : α → List αΓ}
    {eb : β → List βΓ} {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInTime ea eb f) (h2 : TM2ComputableInTime eb ec g) (B : ℕ → ℕ)
    (hB : ∀ m, h2.time m ≤ B m) (hBm : Monotone B) :
    TM2ComputableInTime ea ec (g ∘ f) where
  tm := composeTM h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet
  inputAlphabet := h1.inputAlphabet
  outputAlphabet := h2.outputAlphabet
  time n := h1.time n + 2 * (n + pushTotal h1.tm * h1.time n) + 2 +
    B (n + pushTotal h1.tm * h1.time n)
  outputsFun x := by
    let hx1 := h1.outputsFun x
    let hx2 := h2.outputsFun (f x)
    refine
      { steps := hx2.steps + (((List.map h1.outputAlphabet.invFun (eb (f x))).length + 1) +
          (((List.map h1.outputAlphabet.invFun (eb (f x))).length + 1) + hx1.steps))
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have e1 := hx1.evals_in_steps
      simp only [Option.map_some] at e1
      have e2 : (flip bind (TM2.step h2.tm.m))^[hx2.steps] (some (initList h2.tm
          ((List.map h1.outputAlphabet.invFun (eb (f x))).map
            (conv h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet)))) =
          some (haltList h2.tm (List.map h2.outputAlphabet.invFun (ec (g (f x))))) := by
        rw [map_conv]; exact hx2.evals_in_steps
      have := compose_run h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet _ _ _ _ _ e1 e2
      erw [initList_compose]
      exact this.trans (congrArg some (haltList_compose _ _ _ _ _).symm)
    · have hs1 := hx1.steps_le_m
      have hs2 := hx2.steps_le_m
      have hlen := outLen_boundT h1 x
      have hmono := hBm hlen
      have hb := hB (eb (f x)).length
      simp only [List.length_map] at *
      have hC : pushTotal h1.tm * hx1.steps ≤ pushTotal h1.tm * h1.time (ea x).length :=
        Nat.mul_le_mul_left _ hs1
      omega

theorem add_le_two_pow (a b : ℕ) : a + 2 ^ b ≤ 2 ^ (a + b) := by
  have h1 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rw [Nat.pow_add]
  nlinarith

/-- **EXP is closed under polynomial-time reductions.** -/
theorem InEXP.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InEXP L') : InEXP L := by
  obtain ⟨g, ⟨hg⟩, hL⟩ := hr
  obtain ⟨f, p, ⟨hf, hfb⟩, hL'⟩ := h
  set C := pushTotal hg.tm
  let B : ℕ → ℕ := fun m => 2 ^ p.eval m
  have hBm : Monotone B := fun a b hab => Nat.pow_le_pow_right (by norm_num) (poly_eval_mono p hab)
  let hc := composeInTime hg.toTM2ComputableInTime hf B hfb hBm
  refine ⟨f ∘ g, Polynomial.X + (2 * Polynomial.X + (2 + 2 * (C : Polynomial ℕ)) * hg.time + 2) +
      p.comp (Polynomial.X + (C : Polynomial ℕ) * hg.time), ⟨hc, fun n => ?_⟩,
      fun x => (hL x).trans (hL' (g x))⟩
  show hg.time.eval n + 2 * (n + C * hg.time.eval n) + 2 + 2 ^ p.eval (n + C * hg.time.eval n) ≤ _
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
  have := add_le_two_pow (hg.time.eval n + 2 * (n + C * hg.time.eval n) + 2)
    (p.eval (n + C * hg.time.eval n))
  refine this.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  nlinarith

/-- **If SAT ∈ EXP then NP ⊆ EXP.** (Uses Cook–Levin and closure of EXP under reductions.) -/
theorem NP_subset_EXP_of_SAT_in_EXP (h : InEXP SATLang) (L : Language) (hL : InNP L) :
    InEXP L := InEXP.of_reduces (cookLevin.2 L hL) h

/-- **EXP is closed under complement** (compose the decider with the negation machine). -/
theorem InEXP.compl {L : Language} (h : InEXP L) : InEXP (fun x => ¬ L x) := by
  obtain ⟨f, p, ⟨hf, hfb⟩, hL⟩ := h
  let h1 : TM2ComputableInTime strEnc strEnc (fun x => [f x]) :=
    ⟨hf.toTM2ComputableAux, hf.time, hf.outputsFun⟩
  have hBm : Monotone (fun m : ℕ => m + 2) := fun a b hab => by simp only; omega
  let hc := composeInTime h1 notComputable.toTM2ComputableInTime (fun m => m + 2)
    (fun m => by show Polynomial.eval m (Polynomial.X + 2) ≤ m + 2; simp) hBm
  let h2 : TM2ComputableInTime strEnc encodeBool (fun x => !f x) :=
    ⟨hc.toTM2ComputableAux, hc.time, fun x => by
      have := hc.outputsFun x
      have e : (SmallTM.notF ∘ fun x => [f x]) x = encodeBool (!f x) := by
        show SmallTM.notF [f x] = [!f x]
        cases f x <;> rfl
      rw [e] at this
      exact this⟩
  set C := pushTotal hf.tm
  refine ⟨fun x => !f x, p + Polynomial.X + (8 + 3 * (C : Polynomial ℕ)), ⟨h2, fun n => ?_⟩,
    fun x => ?_⟩
  · show hf.time n + 2 * (n + C * hf.time n) + 2 + ((n + C * hf.time n) + 2) ≤ _
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
    have ht := hfb n
    have hK : 8 + 3 * C ≤ 2 ^ (8 + 3 * C) := Nat.lt_two_pow_self.le
    have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have hp : 1 ≤ 2 ^ p.eval n := Nat.one_le_two_pow
    rw [Nat.pow_add, Nat.pow_add]
    generalize 2 ^ p.eval n = A at ht hp ⊢
    generalize 2 ^ n = B at hn ⊢
    generalize 2 ^ (8 + 3 * C) = D at hK ⊢
    generalize hf.time n = t at ht ⊢
    have hAB : A ≤ A * B := Nat.le_mul_of_pos_right _ (by omega)
    have hBA : B ≤ A * B := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : C * t ≤ C * (A * B) := Nat.mul_le_mul_left _ (ht.trans hAB)
    have h4 : (8 + 3 * C) * (A * B) ≤ D * (A * B) := Nat.mul_le_mul_right _ hK
    have e : A * B * D = D * (A * B) := by ring
    rw [e]
    nlinarith
  · show ¬ L x ↔ (!f x) = true
    rw [hL]; cases f x <;> simp

/-- `NP ⊆ EXP` is equivalent to `SAT ∈ EXP` (the unconditional statement is NOT proven here). -/
theorem NP_subset_EXP_iff_SAT_in_EXP : (∀ L, InNP L → InEXP L) ↔ InEXP SATLang :=
  ⟨fun h => h SATLang SAT_in_NP, NP_subset_EXP_of_SAT_in_EXP⟩

end PvnpReal
