/-
  PvnpReal.NSpace — nondeterministic space: **NPSPACE**.

  A nondeterministic machine (`NTM`) is a Mathlib `FinTM2` `tm` together with a relabelling
  `alt : Λ → Λ`. Every step executes the instruction of the current label (a deterministic
  `stepStay tm.m` step) and then chooses a bit `b`: with `b = true` the label `l'` that the step
  jumped to is replaced by `alt l'` (so from each configuration there are two successors; any
  two-choice machine can be put in this form by doubling labels and starting with a no-op).
  (Before checkpoint 57 the choice instead selected the program `tm.m` / `tm.m ∘ alt` of the
  current step; the definition was changed so that the choice is visible in the tableau's control
  cell.)
  Input `x` is placed on stack `k₀` as `x.map sb` followed by an end marker `sep`. A run is fixed
  by a choice sequence `bs : ℕ → Bool`; it **accepts** if it reaches a halted configuration whose
  output stack `k₁` has the symbol `acc` on top. The machine is `S`-space bounded if every stack of
  every configuration on every run stays within `S(|x|)`.

  `InNPSPACE L`: some NTM with a polynomial space bound accepts exactly `L`.
-/
import PvnpReal.QbfHard

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open Turing TM2 Computability

/-- A run that executes program `ms t` at step `t` (halted configurations stay). -/
def nrun {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (ms : ℕ → Λ → Stmt Γ Λ σ)
    (c : Cfg Γ Λ σ) : ℕ → Cfg Γ Λ σ
  | 0 => c
  | t + 1 => stepStay (ms t) (nrun ms c t)

theorem nrun_const {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (m : Λ → Stmt Γ Λ σ)
    (c : Cfg Γ Λ σ) : ∀ t, nrun (fun _ => m) c t = (stepStay m)^[t] c := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem nrun_congr {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (ms ms' : ℕ → Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (h : ∀ t, ms t = ms' t) :
    ∀ t, nrun ms c t = nrun ms' c t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp only [nrun, ih, h]

theorem stepStay_halted {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (m : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (h : c.l = none) : stepStay m c = c := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · cases h

theorem nrun_halted {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (ms : ℕ → Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) (h : (nrun ms c t).l = none) :
    ∀ r, nrun ms c (t + r) = nrun ms c t := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    show stepStay _ (nrun ms c (t + r)) = _
    rw [ih, stepStay_halted _ _ h]

theorem iterate_halted {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (m : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (h : c.l = none) : ∀ r, (stepStay m)^[r] c = c := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih, stepStay_halted _ _ h]

/-- **Nondeterministic two-choice `FinTM2` machines.** -/
structure NTM where
  tm : FinTM2
  alt : tm.Λ → tm.Λ
  sb : Bool → tm.Γ tm.k₀
  sep : tm.Γ tm.k₀
  acc : tm.Γ tm.k₁

namespace NTM

variable (N : NTM)

/-- The program used with choice bit `b`. -/
def prog (b : Bool) : N.tm.Λ → Stmt N.tm.Γ N.tm.Λ N.tm.σ :=
  fun l => N.tm.m (if b then N.alt l else l)

def init (x : List Bool) : Cfg N.tm.Γ N.tm.Λ N.tm.σ :=
  initCfg N.tm.main N.tm.initialState N.tm.k₀ (x.map N.sb ++ [N.sep])

/-- Relabel the next instruction with `alt` when `b = true`. -/
def relab (b : Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) : Cfg N.tm.Γ N.tm.Λ N.tm.σ :=
  ⟨if b then c.l.map N.alt else c.l, c.var, c.stk⟩

/-- One nondeterministic step with choice bit `b`. -/
def nstep (b : Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) : Cfg N.tm.Γ N.tm.Λ N.tm.σ :=
  N.relab b (stepStay N.tm.m c)

/-- The run from `c` with choice sequence `bs`. -/
def runC (bs : ℕ → Bool) (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) : ℕ → Cfg N.tm.Γ N.tm.Λ N.tm.σ
  | 0 => c
  | t + 1 => N.nstep (bs t) (runC bs c t)

/-- The run on `x` with choice sequence `bs`. -/
def run (bs : ℕ → Bool) (x : List Bool) (t : ℕ) : Cfg N.tm.Γ N.tm.Λ N.tm.σ :=
  N.runC bs (N.init x) t

/-- Accepting configurations: halted, with `acc` on top of the output stack. -/
def Acc (c : Cfg N.tm.Γ N.tm.Λ N.tm.σ) : Prop :=
  c.l = none ∧ cellOf c N.tm.k₁ 0 = some ⟨N.tm.k₁, N.acc⟩

/-- `N` accepts `x`: some choice sequence leads to an accepting configuration. -/
def Accepts (x : List Bool) : Prop := ∃ (bs : ℕ → Bool) (t : ℕ), N.Acc (N.run bs x t)

/-- Every stack of every configuration on every run on `x` has length `≤ S |x|`. -/
def SpaceBounded (S : ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (bs : ℕ → Bool) (t : ℕ) (k : N.tm.K), ((N.run bs x t).stk k).length ≤ S x.length

end NTM

/-- **NPSPACE**: languages accepted by a polynomially space-bounded nondeterministic machine. -/
def InNPSPACE (L : Language) : Prop :=
  ∃ (N : NTM) (p : Polynomial ℕ), N.SpaceBounded (fun n => p.eval n) ∧ ∀ x, L x ↔ N.Accepts x

/-- **coNPSPACE**: complements of NPSPACE languages. -/
def InCoNPSPACE (L : Language) : Prop := InNPSPACE (fun x => ¬ L x)

/-! ### PSPACE ⊆ NPSPACE -/

open scoped Classical

section Det

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {f : List Bool → Bool} (h : TM2ComputableInTime strEnc encodeBool f) (p : Polynomial ℕ)

/-- A deterministic decider (wrapped to read `x #`) as a nondeterministic machine. -/
noncomputable def detNTM : NTM := ⟨hV h, id, hsb h, hsep h, hacc h⟩

theorem detNTM_run (bs : ℕ → Bool) (x : List Bool) (t : ℕ) :
    (detNTM h).run bs x t = (stepStay (hV h).m)^[t] (hc0 h x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show (detNTM h).nstep (bs t) ((detNTM h).run bs x t) = _
    rw [ih, Function.iterate_succ_apply']
    unfold NTM.nstep NTM.relab
    cases bs t <;> simp [detNTM] <;> rfl

theorem detNTM_accepts (x : List Bool) :
    (detNTM h).Accepts x ↔ f x = true := by
  have hT := le_refl ((h.outputsFun x).steps + htp x)
  constructor
  · rintro ⟨bs, t, hl, hc⟩
    rw [detNTM_run] at hl hc
    have hstay : (stepStay (hV h).m)^[(h.outputsFun x).steps + htp x + t] (hc0 h x) =
        (stepStay (hV h).m)^[t] (hc0 h x) := by
      rw [Function.iterate_add_apply]
      exact iterate_halted _ _ hl _
    rcases Nat.lt_or_ge t ((h.outputsFun x).steps + htp x) with ht | ht
    · refine (h_acc h x _ (Nat.le_add_right _ t)).1 ?_
      rw [hstay]; exact hc
    · exact (h_acc h x t ht).1 hc
  · intro hf
    refine ⟨fun _ => false, (h.outputsFun x).steps + htp x, ?_, ?_⟩
    · rw [detNTM_run, h_final h x _ hT]; rfl
    · rw [detNTM_run]; exact (h_acc h x _ hT).2 hf

theorem detNTM_space (hsp : SpaceBounded h (fun n => p.eval n)) :
    (detNTM h).SpaceBounded (fun n => (Polynomial.X + 1 + Polynomial.C (pushTotal (hV h)) *
      (2 * Polynomial.X + 3) + p).eval n) := by
  intro x bs t k
  rw [detNTM_run]
  refine (h_len h p hsp x t k).trans (le_of_eq ?_)
  simp only [hB0, htp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat]
  ring

end Det

/-- **PSPACE ⊆ NPSPACE.** -/
theorem PSPACE_subset_NPSPACE (L : Language) (hL : InPSPACE L) : InNPSPACE L := by
  obtain ⟨p, f, h, hsp, hfL⟩ := hL
  exact ⟨detNTM h, _, detNTM_space h p hsp, fun x => (hfL x).trans (detNTM_accepts h x).symm⟩

/-- **NP ⊆ NPSPACE.** -/
theorem NP_subset_NPSPACE (L : Language) (hL : InNP L) : InNPSPACE L :=
  PSPACE_subset_NPSPACE L (NP_subset_PSPACE L hL)

/-- **P ⊆ NPSPACE.** -/
theorem P_subset_NPSPACE (L : Language) (hL : InP L) : InNPSPACE L :=
  PSPACE_subset_NPSPACE L (P_subset_PSPACE L hL)

end PvnpReal
