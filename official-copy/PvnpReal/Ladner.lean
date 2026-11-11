/-
  PvnpReal.Ladner — pieces of **Ladner's theorem** (conditional on `¬ P_eq_NP`).

  Padded SAT with a padding function `g`:  `LH g = {1ᵐ 0 x | m = g(|x|), x ∈ SAT}`.

  Proven:
  * `PU.indEq`, `PS.iteEq`: polytime equality tests and if-then-else.
  * **`SAT_le_LH`**: if `n ↦ 1^{g(n)}` is polytime, `SAT ≤ₚ LH g`.
  * **`LH_in_NP`**: if `g` is polytime-checkable (`min (g |x|) (m+1)` computable from `1ᵐ0x`), `LH g ∈ NP`.
  * **`SAT_in_P_of_reduces_LH`** ("blown holes" half): if `g` is checkable and grows faster than every
    polynomial, any reduction `SAT ≤ₚ LH g` yields a polytime SAT algorithm (iterated self-reduction
    that shrinks the formula, then brute force on bounded-size formulas).
  * **`ladner_of_padding`**: assuming `¬ P_eq_NP` and a padding function `g` with
    (G1) checkable, (G2) `LH g ∈ P → n ↦ 1^{g(n)}` polytime, (G3) `LH g` NP-complete → `g` superpolynomial,
    the language `LH g` is in NP, not in P, and not NP-complete.

  The padding function itself (`gL m = m ^ H m`, by lazy diagonalization) and the full theorem
  `ladner : ¬ P_eq_NP → ∃ L, InNP L ∧ ¬ InP L ∧ ¬ NPComplete L` are in `LadnerH.lean` /
  `LadnerMachine.lean`. Nothing here bears on P vs NP.
-/
import PvnpReal.PvsNP
import PvnpReal.BruteEXP
import PvnpReal.Flat
import PvnpReal.Stream

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### Combinators -/

theorem PU.indEq {u v : List Bool → ℕ} (hu : PU u) (hv : PU v) :
    PU (fun x => if u x = v x then 1 else 0) :=
  (PU.sub (PU.const 1) (PU.add (PU.sub hu hv) (PU.sub hv hu))).congr (fun x => by
    split_ifs with h <;> omega)

theorem flatMap_range_const (n : ℕ) (l : List Bool) :
    (List.range n).flatMap (fun _ => l) = if n = 0 then [] else if n = 1 then l else
      (List.range n).flatMap (fun _ => l) := by
  rcases n with _ | _ | n <;> simp

/-- **If-then-else on a polytime equality test.** -/
theorem PS.iteEq {u v : List Bool → ℕ} {f g : List Bool → List Bool} (hu : PU u) (hv : PU v)
    (hf : PS f) (hg : PS g) : PS (fun x => if u x = v x then f x else g x) := by
  have he := PU.indEq hu hv
  have hne := PU.sub (PU.const 1) he
  have h1 := PS.flatRange he (fun _ x => f x) (PS.comp PS.drop hf)
  have h2 := PS.flatRange hne (fun _ x => g x) (PS.comp PS.drop hg)
  refine (PS.append h1 h2).congr (fun x => ?_)
  by_cases h : u x = v x <;> simp [h]

/-! ### Padded SAT -/

/-- `LH g = {1ᵐ 0 x | m = g(|x|) ∧ x ∈ SAT}` (read through `lpN`/`lpX`). -/
def LH (g : ℕ → ℕ) : Language := fun y => lpN y = g (lpX y).length ∧ SATLang (lpX y)

/-- Polytime checkability of the padding length. -/
def Checkable (g : ℕ → ℕ) : Prop := PU (fun y => min (g (lpX y).length) (lpN y + 1))

theorem check_iff (g : ℕ → ℕ) (y : List Bool) :
    lpN y = min (g (lpX y).length) (lpN y + 1) ↔ lpN y = g (lpX y).length := by
  constructor
  · intro h; have := min_le_right (g (lpX y).length) (lpN y + 1); omega
  · intro h; rw [← h]; simp

/-- **`SAT ≤ₚ LH g`** when the padding is polytime printable. -/
theorem SAT_le_LH (g : ℕ → ℕ) (hg : PU (fun x => g x.length)) : PolyReduces SATLang (LH g) := by
  obtain ⟨h⟩ := PS.append hg (PS.cons false PS.id)
  refine ⟨_, ⟨h⟩, fun x => ?_⟩
  simp only [LH, lpN_rep, lpX_rep, true_and]

/-- **`LH g ∈ NP`** for checkable `g` (reduction to SAT). -/
theorem LH_in_NP (g : ℕ → ℕ) (hg : Checkable g) : InNP (LH g) := by
  obtain ⟨x0, hx0⟩ := SATLang_not_univ
  obtain ⟨h⟩ := PS.iteEq PU.fst hg PS.drop (PS.const x0)
  refine InNP.of_reduces ⟨_, ⟨h⟩, fun y => ?_⟩ SAT_in_NP
  simp only [LH]
  by_cases hc : lpN y = min (g (lpX y).length) (lpN y + 1)
  · rw [if_pos hc, (check_iff g y).1 hc]; simp
  · rw [if_neg hc]
    have : ¬ lpN y = g (lpX y).length := fun e => hc ((check_iff g y).2 e)
    simp [this, hx0]

/-- Superpolynomial growth. -/
def SuperPoly (g : ℕ → ℕ) : Prop := ∀ P : Polynomial ℕ, ∃ N, ∀ n ≥ N, P.eval n < g n

theorem lpN_le (y : List Bool) : lpN y ≤ y.length := (List.takeWhile_prefix id).length_le

/-- Brute force with a constant padding is correct on short formulas. -/
theorem searchB_const {M : ℕ} {s : List Bool} (hs : 2 ^ s.length ≤ M) :
    searchB (List.replicate M true ++ false :: s) = true ↔ SATLang s := by
  rw [SATLang_iff_exists_bin, searchB, lpN_rep, lpX_rep]
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, -, hi⟩
    obtain ⟨φ, rfl, hφ⟩ := verify_sound _ _ hi
    exact (SATLang_iff_exists_bin _).1 ⟨φ, rfl, _, hφ⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, by omega, hv⟩

/-- **The "blown holes" half of Ladner**: a reduction from SAT to `LH g` with superpolynomial
checkable `g` gives `SAT ∈ P`. -/
theorem SAT_in_P_of_reduces_LH (g : ℕ → ℕ) (hg : Checkable g) (hs : SuperPoly g)
    (hr : PolyReduces SATLang (LH g)) : InP SATLang := by
  obtain ⟨f, ⟨hf⟩, hfL⟩ := hr
  obtain ⟨x0, hx0⟩ := SATLang_not_univ
  -- output length bound
  let Pp : Polynomial ℕ := Polynomial.X + Polynomial.C (pushTotal hf.tm) * hf.time
  have hlen : ∀ x, (f x).length ≤ Pp.eval x.length := by
    intro x
    have : (f x).length ≤ x.length + pushTotal hf.tm * hf.time.eval x.length :=
      outLen_boundT hf.toTM2ComputableInTime x
    simpa [Pp] using this
  obtain ⟨N0, hN0⟩ := hs Pp
  let N' := max N0 (x0.length + 1)
  -- one self-reduction step
  let st : List Bool → List Bool := fun ψ =>
    if lpN (f ψ) = min (g (lpX (f ψ)).length) (lpN (f ψ) + 1) then lpX (f ψ) else x0
  have hstPS : PS st := PS.iteEq (PU.fst.comp ⟨hf⟩) (hg.comp ⟨hf⟩) (PS.comp ⟨hf⟩ PS.drop) (PS.const x0)
  have hinv : ∀ ψ, SATLang (st ψ) ↔ SATLang ψ := by
    intro ψ
    rw [hfL ψ]
    simp only [st, LH]
    by_cases hc : lpN (f ψ) = min (g (lpX (f ψ)).length) (lpN (f ψ) + 1)
    · rw [if_pos hc, (check_iff g _).1 hc]; simp
    · rw [if_neg hc]
      have : ¬ lpN (f ψ) = g (lpX (f ψ)).length := fun e => hc ((check_iff g _).2 e)
      simp [this, hx0]
  have hshr : ∀ ψ, (st ψ).length < N' ∨ (st ψ).length < ψ.length := by
    intro ψ
    simp only [st]
    by_cases hc : lpN (f ψ) = min (g (lpX (f ψ)).length) (lpN (f ψ) + 1)
    · rw [if_pos hc]
      have he := (check_iff g _).1 hc
      have h1 : g (lpX (f ψ)).length ≤ Pp.eval ψ.length := by
        rw [← he]; exact (lpN_le _).trans (hlen ψ)
      by_contra hcon
      push_neg at hcon
      have h2 := hN0 (lpX (f ψ)).length (by omega)
      have h3 := poly_eval_mono Pp hcon.2
      omega
    · rw [if_neg hc]; left; omega
  have hit : ∀ ψ i, (st^[i] ψ).length < N' ∨ (st^[i] ψ).length + i ≤ ψ.length := by
    intro ψ i
    induction i with
    | zero => right; simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases hshr (st^[i] ψ) with h | h
      · left; exact h
      · rcases ih with h' | h'
        · left; omega
        · right; omega
  have hsmall : ∀ ψ, (st^[ψ.length] ψ).length < N' := by
    intro ψ
    rcases hit ψ ψ.length with h | h
    · exact h
    · have : 0 < N' := by omega
      omega
  have hinvI : ∀ ψ i, SATLang (st^[i] ψ) ↔ SATLang ψ := by
    intro ψ i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', hinv, ih]
  have hbound : ∀ y i, (st^[i] y).length ≤ (Polynomial.X + Polynomial.C N').eval (y.length + i) := by
    intro y i
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rcases hit y i with h | h <;> omega
  have hI := PS.iter hstPS _ hbound
  have hA : PS (fun x => List.replicate x.length true ++ false :: x) := PS.append PU.lenX (PS.cons false PS.id)
  have hIt : PS (fun x => st^[x.length] x) := (PS.comp hA hI).congr (fun x => by simp only [lpN_rep, lpX_rep])
  have hP : PS (fun s => List.replicate (2 ^ N') true ++ false :: s) :=
    PS.append (PU.const _) (PS.cons false PS.id)
  obtain ⟨hD⟩ := PS.comp (PS.comp hIt hP) PS.search
  refine ⟨_, ⟨strToDecider hD⟩, fun x => ?_⟩
  rw [searchB_const ((Nat.pow_le_pow_right (by norm_num) (hsmall x).le)), hinvI]

/-- **Ladner's theorem from a padding function** (the construction of `g` is in `LadnerH`). -/
theorem ladner_of_padding (hPNP : ¬ P_eq_NP) (g : ℕ → ℕ) (hg1 : Checkable g)
    (hg2 : InP (LH g) → PU (fun x => g x.length))
    (hg3 : NPComplete (LH g) → SuperPoly g) :
    InNP (LH g) ∧ ¬ InP (LH g) ∧ ¬ NPComplete (LH g) := by
  refine ⟨LH_in_NP g hg1, fun hP => ?_, fun hC => ?_⟩
  · exact hPNP (P_eq_NP_iff_SAT_in_P.2 (InP.of_reduces (SAT_le_LH g (hg2 hP)) hP))
  · exact hPNP (P_eq_NP_iff_SAT_in_P.2
      (SAT_in_P_of_reduces_LH g hg1 (hg3 hC) (hC.2 SATLang SAT_in_NP)))

end PvnpReal
