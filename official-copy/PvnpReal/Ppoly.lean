/-
  PvnpReal.Ppoly — **P/poly** as polynomial-time computation with polynomial advice.

  `InPpoly L`: there are a P language `A`, a polynomial `q` and advice strings `adv n` with
  `|adv n| = q(n)` exactly (Arora–Barak Def. 6.18 style: `DTIME(n^c)/n^d`) such that
  `x ∈ L ↔ codeP x (adv |x|) ∈ A`. The advice depends only on the input length and is arbitrary
  (not computable). The circuit form `InPpolyCirc` (polynomial-size `BCirc` families from
  `Circuits.lean`) is defined too; the equivalence of the two is NOT proven (see NOTES).
-/
import PvnpReal.SigmaRed
import PvnpReal.Circuits

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing Computability

open scoped Classical

/-- **P/poly** (advice form). -/
def InPpoly (L : Language) : Prop :=
  ∃ (A : Language) (q : Polynomial ℕ) (adv : ℕ → List Bool),
    InP A ∧ (∀ n, (adv n).length = q.eval n) ∧ ∀ x, L x ↔ A (codeP x (adv x.length))

/-- **P/poly** (circuit form): polynomial-size circuit families (not proven equivalent). -/
def InPpolyCirc (L : Language) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n, HasCircuit n (q.eval n) (fun x : Fin n → Bool => decide (L (List.ofFn x)))

/-- `NP ⊆ P/poly`. -/
def NP_subset_Ppoly : Prop := ∀ L : Language, InNP L → InPpoly L

/-- **P ⊆ P/poly.** -/
theorem P_subset_Ppoly (L : Language) (h : InP L) : InPpoly L :=
  ⟨fun s => L (decP s).1, 0, fun _ => [], h.compPS PS.fstP, fun n => by simp,
    fun x => by simp [decP_codeP]⟩

theorem PS.ofInP {A : Language} (h : InP A) : PS (fun s => [decide (A s)]) := by
  obtain ⟨f, ⟨hf⟩, hA⟩ := h
  exact PS.congr (⟨deciderToStr hf⟩ : PS (fun s => [f s])) (fun s => by
    have := hA s; by_cases e : A s <;> simp_all)

/-! ### Advice tables: the advice for every length `≤ N`, in slots of width `W` -/

/-- Slot `n` (`n ≤ N`) holds `adv n` padded with `false` to width `W`. -/
def advCat (adv : ℕ → List Bool) (q : Polynomial ℕ) (N W : ℕ) : List Bool :=
  (List.range (N + 1)).flatMap (fun n => adv n ++ List.replicate (W - q.eval n) false)

theorem flatten_drop_mul (W : ℕ) : ∀ (L : List (List Bool)), (∀ b ∈ L, b.length = W) →
    ∀ n, L.flatten.drop (n * W) = (L.drop n).flatten := by
  intro L
  induction L with
  | nil => intro _ n; simp
  | cons b L ih =>
    intro hL n
    cases n with
    | zero => simp
    | succ n =>
      have hb := hL b (by simp)
      rw [List.flatten_cons, List.drop_append, hb, List.drop_eq_nil_of_le (by rw [hb]; nlinarith),
        List.nil_append, show (n + 1) * W - W = n * W by rw [Nat.succ_mul]; omega,
        ih (fun b' hb' => hL b' (by simp [hb'])) n, List.drop_succ_cons]

section Adv

variable {adv : ℕ → List Bool} {q : Polynomial ℕ} {N W : ℕ}

theorem advCat_length (hadv : ∀ n, (adv n).length = q.eval n) (hW : ∀ n ≤ N, q.eval n ≤ W) :
    (advCat adv q N W).length = (N + 1) * W := by
  unfold advCat
  rw [List.length_flatMap]
  have : ∀ n ∈ List.range (N + 1), (adv n ++ List.replicate (W - q.eval n) false).length = W := by
    intro n hn
    have := hW n (by simp at hn; omega)
    simp [hadv]; omega
  rw [List.map_congr_left this]
  simp [Nat.mul_comm]

theorem advCat_slot (hadv : ∀ n, (adv n).length = q.eval n) (hW : ∀ n ≤ N, q.eval n ≤ W)
    {n : ℕ} (hn : n ≤ N) : subL (advCat adv q N W) (n * W) (q.eval n) = adv n := by
  have hlen := advCat_length hadv hW
  have hq := hW n hn
  rw [subL_eq _ _ _ (by rw [hlen]; nlinarith)]
  have hb : ∀ b ∈ (List.range (N + 1)).map (fun n => adv n ++ List.replicate (W - q.eval n) false),
      b.length = W := by
    intro b hb
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
    have := hW m (by simp at hm; omega)
    simp [hadv]; omega
  unfold advCat
  rw [List.flatMap_def, flatten_drop_mul W _ hb n,
    List.drop_eq_getElem_cons (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range, List.flatten_cons, List.append_assoc]
  exact List.take_left' (hadv n)

end Adv

/-- **P/poly is closed under polynomial-time many-one reductions** (the advice of `L` at length `n`
is the table of advice of `L'` for all lengths `≤ |f x|`'s polynomial bound). -/
theorem InPpoly.of_reduces {L L' : Language} (hr : PolyReduces L L') (h : InPpoly L') : InPpoly L := by
  obtain ⟨f, hf, hfL⟩ := hr
  obtain ⟨A, q, adv, hA, hadv, hL'⟩ := h
  obtain ⟨Nf, hNf⟩ := PS.outPoly hf
  set WP := q.comp Nf
  have hW : ∀ n, ∀ m ≤ Nf.eval n, q.eval m ≤ WP.eval n := fun n m hm => by
    simp only [WP, Polynomial.eval_comp]; exact poly_eval_mono q hm
  refine ⟨fun s => A (codeP (f (decP s).1) (subL (decP s).2 ((f (decP s).1).length *
      WP.eval (decP s).1.length) (q.eval (f (decP s).1).length))),
    (Nf + 1) * WP, fun n => advCat adv q (Nf.eval n) (WP.eval n), ?_, fun n => ?_, fun x => ?_⟩
  · have hy : PS (fun s => f (decP s).1) := PS.comp PS.fstP hf
    exact hA.compPS (PS.codePF hy (PS.subL PS.sndP ((PU.lenX.comp hy).mul
      (PU.polyOf WP (PU.lenX.comp PS.fstP))) (PU.polyOf q (PU.lenX.comp hy))))
  · rw [advCat_length hadv (hW n)]; simp
  · simp only [decP_codeP]
    rw [advCat_slot hadv (hW x.length) (hNf x), hfL x, hL']

theorem InPpoly.congr {L L' : Language} (h : InPpoly L) (e : ∀ x, L x ↔ L' x) : InPpoly L' := by
  obtain ⟨A, q, adv, hA, hadv, hL⟩ := h
  exact ⟨A, q, adv, hA, hadv, fun x => (e x).symm.trans (hL x)⟩

/-- `SAT ∈ P/poly ↔ NP ⊆ P/poly`. -/
theorem SAT_Ppoly_iff : InPpoly SATLang ↔ NP_subset_Ppoly :=
  ⟨fun h L hL => InPpoly.of_reduces (SAT_NPHard L hL) h, fun H => H _ SAT_in_NP⟩

end PvnpReal
