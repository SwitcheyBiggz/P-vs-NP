/-
  PvnpReal.ExplicitCost2 — length-aware degree calculus.

  `PSl d l f`: time polynomial `≤ K(n+1)^d` AND output length `≤ K(|x|+1)^l`. With a composition
  machine `composeLen` that charges the second machine at the *semantic* length bound of the first
  output (instead of `n + C·time`), compositions cost `max(d₁, l₁·d₂)` instead of `d₁·d₂`. This
  brings the interpreter's explicit exponent down from `8495200` (ExplicitCost) to a small number.
-/
import PvnpReal.ExplicitCost

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-- **Composition charged at a supplied output-length bound `Lp` of the first function.** -/
noncomputable def composeLen {f g : List Bool → List Bool}
    (h1 : TM2ComputableInPolyTime strEnc strEnc f) (h2 : TM2ComputableInPolyTime strEnc strEnc g)
    (Lp : Polynomial ℕ) (hL : ∀ x, (f x).length ≤ Lp.eval x.length) :
    TM2ComputableInPolyTime strEnc strEnc (g ∘ f) where
  tm := composeTM h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet
  inputAlphabet := h1.inputAlphabet
  outputAlphabet := h2.outputAlphabet
  time := h1.time + 2 * (Polynomial.X + (pushTotal h1.tm : Polynomial ℕ) * h1.time) + 2 +
    h2.time.comp Lp
  outputsFun x := by
    let hx1 := h1.outputsFun x
    let hx2 := h2.outputsFun (f x)
    refine
      { steps := hx2.steps + (((List.map h1.outputAlphabet.invFun (strEnc (f x))).length + 1) +
          (((List.map h1.outputAlphabet.invFun (strEnc (f x))).length + 1) + hx1.steps))
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have e1 := hx1.evals_in_steps
      simp only [Option.map_some] at e1
      have e2 : (flip bind (TM2.step h2.tm.m))^[hx2.steps] (some (initList h2.tm
          ((List.map h1.outputAlphabet.invFun (strEnc (f x))).map
            (conv h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet)))) =
          some (haltList h2.tm (List.map h2.outputAlphabet.invFun (strEnc (g (f x))))) := by
        rw [map_conv]; exact hx2.evals_in_steps
      have := compose_run h1.tm h2.tm h1.outputAlphabet h2.inputAlphabet _ _ _ _ _ e1 e2
      erw [initList_compose]
      exact this.trans (congrArg some (haltList_compose _ _ _ _ _).symm)
    · have hs1 := hx1.steps_le_m
      have hs2 := hx2.steps_le_m
      have hlen := outLen_bound h1 x
      have hmono := poly_eval_mono h2.time (hL x)
      simp only [strEnc, List.length_map] at *
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
      have hC : pushTotal h1.tm * hx1.steps ≤ pushTotal h1.tm * h1.time.eval x.length :=
        Nat.mul_le_mul_left _ hs1
      omega

/-- Time degree `d` and output-length degree `l`. -/
def PSl (d l : ℕ) (f : List Bool → List Bool) : Prop :=
  ∃ h : TM2ComputableInPolyTime strEnc strEnc f, ∃ K,
    (∀ n, h.time.eval n ≤ K * (n + 1) ^ d) ∧ ∀ x, (f x).length ≤ K * (x.length + 1) ^ l

/-- Unary quantity with time degree `d` and value degree `l`. -/
def PUl (d l : ℕ) (u : List Bool → ℕ) : Prop := PSl d l (fun x => List.replicate (u x) true)

theorem PSl.mk {d l : ℕ} {f : List Bool → List Bool} (h : TM2ComputableInPolyTime strEnc strEnc f)
    (KT KL : ℕ) (hT : ∀ n, h.time.eval n ≤ KT * (n + 1) ^ d)
    (hL : ∀ x, (f x).length ≤ KL * (x.length + 1) ^ l) : PSl d l f :=
  ⟨h, KT + KL, fun n => (hT n).trans (Nat.mul_le_mul_right _ (by omega)),
    fun x => (hL x).trans (Nat.mul_le_mul_right _ (by omega))⟩

theorem PSl.of {d l : ℕ} {f : List Bool → List Bool} (h : PSd d f) (KL : ℕ)
    (hL : ∀ x, (f x).length ≤ KL * (x.length + 1) ^ l) : PSl d l f :=
  let ⟨h, KT, hT⟩ := h; PSl.mk h KT KL hT hL

theorem PSl.toPSd {d l : ℕ} {f : List Bool → List Bool} (h : PSl d l f) : PSd d f :=
  let ⟨h, K, hT, _⟩ := h; ⟨h, K, hT⟩

theorem PSl.toPS {d l : ℕ} {f : List Bool → List Bool} (h : PSl d l f) : PS f := h.toPSd.toPS

theorem PSl.lenB {d l : ℕ} {f : List Bool → List Bool} (h : PSl d l f) :
    ∃ K, ∀ x, (f x).length ≤ K * (x.length + 1) ^ l :=
  let ⟨_, K, _, hL⟩ := h; ⟨K, hL⟩

theorem PSl.mono {d l d' l' : ℕ} {f : List Bool → List Bool} (h : PSl d l f) (hd : d ≤ d')
    (hl : l ≤ l') : PSl d' l' f := by
  obtain ⟨h, K, hT, hL⟩ := h
  exact ⟨h, K, fun n => (hT n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd)),
    fun x => (hL x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hl))⟩

theorem PSl.congr {d l : ℕ} {f g : List Bool → List Bool} (h : PSl d l f) (e : ∀ x, f x = g x) :
    PSl d l g := by
  have : f = g := funext e
  subst this; exact h

theorem PUl.congr {d l : ℕ} {u v : List Bool → ℕ} (h : PUl d l u) (e : ∀ x, u x = v x) : PUl d l v :=
  PSl.congr h (fun x => by rw [e])

theorem PUl.val {d l : ℕ} {u : List Bool → ℕ} (h : PUl d l u) :
    ∃ K, ∀ x, u x ≤ K * (x.length + 1) ^ l := by
  obtain ⟨K, hK⟩ := PSl.lenB h
  exact ⟨K, fun x => by simpa using hK x⟩

/-! ### Arithmetic -/

theorem pw_bound (K n l e : ℕ) : (K * (n + 1) ^ l + 1) ^ e ≤ (K + 1) ^ e * (n + 1) ^ (l * e) := by
  have h1 : 1 ≤ (n + 1) ^ l := Nat.one_le_pow _ _ (by omega)
  have h2 : K * (n + 1) ^ l + 1 ≤ (K + 1) * (n + 1) ^ l := by
    have e2 : (K + 1) * (n + 1) ^ l = K * (n + 1) ^ l + (n + 1) ^ l := by ring
    omega
  calc (K * (n + 1) ^ l + 1) ^ e ≤ ((K + 1) * (n + 1) ^ l) ^ e := Nat.pow_le_pow_left h2 _
    _ = (K + 1) ^ e * (n + 1) ^ (l * e) := by rw [mul_pow, ← pow_mul]

theorem pow_le_max_left (n a b : ℕ) : (n + 1) ^ a ≤ (n + 1) ^ max a b :=
  Nat.pow_le_pow_right (by omega) (le_max_left _ _)

theorem pow_le_max_right (n a b : ℕ) : (n + 1) ^ b ≤ (n + 1) ^ max a b :=
  Nat.pow_le_pow_right (by omega) (le_max_right _ _)

theorem compT_arith (K1 K2 C d1 d2 l1 n s q : ℕ) (hd1 : 1 ≤ d1)
    (hs : s ≤ K1 * (n + 1) ^ d1) (hq : q ≤ K2 * (K1 * (n + 1) ^ l1 + 1) ^ d2) :
    s + 2 * (n + C * s) + 2 + q ≤
      (K1 + 2 * (C * K1 + 1) + 2 + K2 * (K1 + 1) ^ d2) * (n + 1) ^ (max d1 (l1 * d2)) := by
  set M := (n + 1) ^ (max d1 (l1 * d2))
  have hA : (n + 1) ^ d1 ≤ M := pow_le_max_left _ _ _
  have hB : (n + 1) ^ (l1 * d2) ≤ M := pow_le_max_right _ _ _
  have hn : n + 1 ≤ (n + 1) ^ d1 := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hd1
  have hs' : s ≤ K1 * M := hs.trans (Nat.mul_le_mul_left _ hA)
  have hCs : C * s ≤ C * K1 * M := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hs'
  have hq' : q ≤ K2 * (K1 + 1) ^ d2 * M := by
    refine hq.trans ?_
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ ((pw_bound K1 n l1 d2).trans (Nat.mul_le_mul_left _ hB))
  generalize K2 * (K1 + 1) ^ d2 = E at hq' ⊢
  have e : (K1 + 2 * (C * K1 + 1) + 2 + E) * M = K1 * M + 2 * (C * K1 * M) + 2 * M + 2 * M + E * M := by
    ring
  omega

/-! ### Composition and fan-out -/

/-- **Length-aware composition**: time `max(d₁, l₁·d₂)`; the output length bound is supplied. -/
theorem PSl.compT {d1 l1 d2 l : ℕ} {f g : List Bool → List Bool} (hf : PSl d1 l1 f) (hg : PSd d2 g)
    (hd1 : 1 ≤ d1) (Kl : ℕ) (hl : ∀ x, (g (f x)).length ≤ Kl * (x.length + 1) ^ l) :
    PSl (max d1 (l1 * d2)) l (fun x => g (f x)) := by
  obtain ⟨h1, K1, hT1, hL1⟩ := hf
  obtain ⟨h2, K2, hT2⟩ := hg
  let Lp : Polynomial ℕ := (K1 : Polynomial ℕ) * (Polynomial.X + 1) ^ l1
  have hLp : ∀ x, (f x).length ≤ Lp.eval x.length := fun x => by simpa [Lp] using hL1 x
  refine PSl.mk (composeLen h1 h2 Lp hLp)
    (K1 + 2 * (pushTotal h1.tm * K1 + 1) + 2 + K2 * (K1 + 1) ^ d2) Kl (fun n => ?_) hl
  have := compT_arith K1 K2 (pushTotal h1.tm) d1 d2 l1 n (h1.time.eval n)
    (h2.time.eval (K1 * (n + 1) ^ l1)) hd1 (hT1 n) (hT2 _)
  simpa [composeLen, Lp, Polynomial.eval_comp] using this

theorem PSl.comp {d1 l1 d2 l2 : ℕ} {f g : List Bool → List Bool} (hf : PSl d1 l1 f)
    (hg : PSl d2 l2 g) (hd1 : 1 ≤ d1) : PSl (max d1 (l1 * d2)) (l1 * l2) (fun x => g (f x)) := by
  obtain ⟨K1, hK1⟩ := hf.lenB
  obtain ⟨K2, hK2⟩ := hg.lenB
  refine PSl.compT hf hg.toPSd hd1 (K2 * (K1 + 1) ^ l2) (fun x => ?_)
  refine (hK2 (f x)).trans ?_
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by have := hK1 x; omega) _).trans
    (pw_bound K1 x.length l1 l2))

theorem PSl.append {d1 l1 d2 l2 : ℕ} {f g : List Bool → List Bool} (hf : PSl d1 l1 f)
    (hg : PSl d2 l2 g) (hd : 1 ≤ max d1 d2) :
    PSl (max d1 d2) (max l1 l2) (fun x => f x ++ g x) := by
  obtain ⟨K1, hK1⟩ := hf.lenB
  obtain ⟨K2, hK2⟩ := hg.lenB
  refine PSl.of (PSd.append (hf.toPSd.mono (le_max_left _ _)) (hg.toPSd.mono (le_max_right _ _)) hd)
    (K1 + K2) (fun x => ?_)
  rw [List.length_append, add_mul]
  exact Nat.add_le_add ((hK1 x).trans (Nat.mul_le_mul_left _ (pow_le_max_left _ _ _)))
    ((hK2 x).trans (Nat.mul_le_mul_left _ (pow_le_max_right _ _ _)))

/-! ### Primitives -/

theorem PSl.const (c : List Bool) : PSl 1 0 (fun _ => c) :=
  PSl.of (PSd.const c) c.length (fun x => by simp)

theorem PSl.id : PSl 1 1 (fun x => x) := PSl.of PSd.id 1 (fun x => by simp)

theorem PSl.cons (b : Bool) {d l : ℕ} {f : List Bool → List Bool} (hf : PSl d l f) (hd : 1 ≤ d) :
    PSl d l (fun x => b :: f x) :=
  ((PSl.const [b]).append hf (le_max_of_le_left le_rfl)).mono (max_le hd le_rfl)
    (max_le (Nat.zero_le _) le_rfl)

theorem PUl.const (n : ℕ) : PUl 1 0 (fun _ => n) := PSl.const _

theorem PUl.fst : PUl 1 1 lpN :=
  PSl.of PUd.fst 1 (fun x => by have := LoopTM.lp_len x; simp; omega)

theorem PSl.drop : PSl 1 1 lpX :=
  PSl.of PSd.drop 1 (fun x => by have := LoopTM.lp_len x; simp; omega)

theorem PUl.nth : PUl 1 0 (fun z => NthTM.bit (lpX z) (lpN z)) :=
  PSl.of PUd.nth 1 (fun x => by simp [NthTM.bit]; split <;> simp)

theorem PUl.add {d1 l1 d2 l2 : ℕ} {u v : List Bool → ℕ} (hu : PUl d1 l1 u) (hv : PUl d2 l2 v)
    (hd : 1 ≤ max d1 d2) : PUl (max d1 d2) (max l1 l2) (fun x => u x + v x) :=
  (PSl.append hu hv hd).congr (fun x => by rw [List.replicate_add])

theorem PUl.sub {d1 l1 d2 l2 : ℕ} {u v : List Bool → ℕ} (hu : PUl d1 l1 u) (hv : PUl d2 l2 v)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) :
    PUl (max (max d1 d2) (max l1 l2 * 1)) l1 (fun x => u x - v x) := by
  obtain ⟨K, hK⟩ := hu.val
  have hA := PSl.append hu (PSl.cons false hv hd2) (le_max_of_le_left hd1)
  have := PSl.compT hA (PSd.of_lin monusComputable 4 4 (by simp [monusComputable]))
    (le_max_of_le_left hd1) K (l := l1) (fun x => by
      simp only [monusF, lpN_rep, lpX_rep, lpN_replicate, List.length_replicate]
      exact (Nat.sub_le _ _).trans (hK x))
  exact this.congr (fun x => by simp [monusF, lpN_rep, lpX_rep, lpN_replicate])

/-- `get` on the tail of the input. -/
theorem PUl.getDrop {d l : ℕ} {u : List Bool → ℕ} (hu : PUl d l u) (hd : 1 ≤ d) :
    PUl (max (max d 1) (max l 1 * 1)) 1 (fun z => (numsOf (lpX z)).getD (u z) 0) := by
  have hA := PSl.append hu (PSl.cons false PSl.drop le_rfl) (le_max_of_le_left hd)
  have := PSl.compT hA (PSd.of_lin numAtComputable 6 6 (by simp [numAtComputable]))
    (le_max_of_le_left hd) 1 (l := 1) (fun x => by
      simp only [numAt, lpN_rep, lpX_rep, List.length_replicate]
      have h1 := (Flat.getD_le (numsOf (lpX x)) (u x)).trans (Flat.numsOf_max_le (lpX x))
      have h2 := LoopTM.lp_len x
      rw [one_mul, pow_one]; omega)
  exact this.congr (fun x => by simp [numAt, lpN_rep, lpX_rep])

theorem PUl.mul {d1 l1 d2 l2 : ℕ} {u v : List Bool → ℕ} (hu : PUl d1 l1 u) (hv : PUl d2 l2 v)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) :
    PUl (max (max (max d1 d2) (max l1 l2 * 2)) ((l1 + l2) * 1)) (l1 + l2) (fun x => u x * v x) := by
  obtain ⟨Ku, hKu⟩ := hu.val
  obtain ⟨Kv, hKv⟩ := hv.val
  have hp : PSl (max d1 d2) (max l1 l2) (fun x => pairU (u x) (v x)) :=
    (PSl.append hu (PSl.cons false hv hd2) (le_max_of_le_left hd1)).congr
      (fun x => by simp [pairU])
  have hval : ∀ x, u x * v x ≤ Ku * Kv * (x.length + 1) ^ (l1 + l2) := fun x => by
    rw [pow_add, mul_mul_mul_comm]; exact Nat.mul_le_mul (hKu x) (hKv x)
  have hu2 : ∀ x, u x ≤ Ku * (x.length + 1) ^ (l1 + l2) := fun x =>
    (hKu x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have h1p : ∀ x : List Bool, 1 ≤ (x.length + 1) ^ (l1 + l2) := fun x => Nat.one_le_pow _ _ (by omega)
  have hh := PSl.compT hp (PSd.horner 0) (le_max_of_le_left hd1) (Ku + 1 + Ku * Kv)
    (l := l1 + l2) (fun x => by
      rw [hornerF_pairU]
      simp only [pairU, List.length_append, List.length_replicate, List.length_cons, add_mul,
        mul_zero, add_zero]
      have := hval x; have := hu2 x; have := h1p x
      have e : u x * v x = u x * v x + 0 := rfl
      nlinarith)
  have := PSl.compT hh (PSd.of_lin SmallTM.sndComputable 1 2 (by simp [SmallTM.sndComputable]))
    (le_max_of_le_left (le_max_of_le_left hd1)) (Ku * Kv) (l := l1 + l2) (fun x => by
      simp only [hornerF_pairU, SmallTM.sndF, hM_pairU, List.length_replicate]
      simpa [mul_comm] using hval x)
  exact this.congr (fun x => by simp [hornerF_pairU, SmallTM.sndF, hM_pairU])

/-! ### Expressions with time and value degrees -/

/-- Value degree of an expression. -/
def NE.lv : NE → ℕ
  | .c _ => 0
  | .p => 1
  | .get _ => 1
  | .add a b => max a.lv b.lv
  | .mul a b => a.lv + b.lv
  | .sub a _ => a.lv

/-- Time degree of an expression's evaluator. -/
def NE.dt : NE → ℕ
  | .c _ => 1
  | .p => 1
  | .get e => max (max e.dt 1) (max e.lv 1 * 1)
  | .add a b => max a.dt b.dt
  | .mul a b => max (max (max a.dt b.dt) (max a.lv b.lv * 2)) ((a.lv + b.lv) * 1)
  | .sub a b => max (max a.dt b.dt) (max a.lv b.lv * 1)

theorem NE.dt_pos (e : NE) : 1 ≤ e.dt := by
  induction e with
  | c n => exact le_rfl
  | p => exact le_rfl
  | get e ih => exact le_max_of_le_left (le_max_right _ _)
  | add a b iha ihb => exact le_max_of_le_left iha
  | mul a b iha ihb => exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left iha))
  | sub a b iha ihb => exact le_max_of_le_left (le_max_of_le_left iha)

/-- **Expression evaluation with explicit time and value degrees.** -/
theorem NE.pul (e : NE) : PUl e.dt e.lv (fun z => e.ev (lpN z) (numsOf (lpX z))) := by
  induction e with
  | c n => exact PUl.const n
  | p => exact PUl.fst
  | get e ih => exact PUl.getDrop ih e.dt_pos
  | add a b iha ihb => exact PUl.add iha ihb (le_max_of_le_left a.dt_pos)
  | mul a b iha ihb => exact PUl.mul iha ihb a.dt_pos b.dt_pos
  | sub a b iha ihb => exact PUl.sub iha ihb a.dt_pos b.dt_pos

theorem NE.pul0 (e : NE) : PUl e.dt e.lv (fun y => e.ev 0 (numsOf y)) := by
  have := PSl.comp (PSl.cons false PSl.id le_rfl) (NE.pul e) le_rfl
  refine (this.mono (max_le e.dt_pos (by rw [one_mul])) (by rw [one_mul])).congr (fun y => ?_)
  simp only [LoopTM.lpN_cons_false, LoopTM.lpX_cons_false]

/-! ### Loops, iteration, and the interpreter -/

theorem flatMap_range_len_le (f : ℕ → List Bool) (B : ℕ) :
    ∀ n, (∀ i < n, (f i).length ≤ B) → ((List.range n).flatMap f).length ≤ n * B := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [List.range_succ, List.flatMap_append, List.length_append, add_mul, one_mul]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

/-- **Length-aware concatenation over a range.** -/
theorem PSl.flatRange {dN lN db lb : ℕ} {N : List Bool → ℕ} (hN : PUl dN lN N)
    (b : ℕ → List Bool → List Bool) (hb : PSl db lb (fun z => b (lpN z) (lpX z)))
    (hdN : 1 ≤ dN) (hdb : 1 ≤ db) :
    PSl (max (max dN 1) (max lN 1 * (db + 1))) (lN + max lN 1 * lb)
      (fun x => (List.range (N x)).flatMap fun i => b i x) := by
  obtain ⟨KN, hKN⟩ := hN.val
  obtain ⟨Kb, hKb⟩ := hb.lenB
  have hin : PSl (max dN 1) (max lN 1) (fun x => List.replicate (N x) true ++ false :: x) :=
    PSl.append hN (PSl.cons false PSl.id le_rfl) (le_max_of_le_left hdN)
  have heq : ∀ x, loopF (fun z => b (lpN z) (lpX z)) (List.replicate (N x) true ++ false :: x) =
      (List.range (N x)).flatMap fun i => b i x := fun x => by
    simp only [loopF, lpN_rep, lpX_rep]
  refine (PSl.compT hin (PSd.loop hb.toPSd hdb) (le_max_of_le_left hdN)
    (KN * (Kb * (KN + 1) ^ lb)) (l := lN + max lN 1 * lb) (fun x => ?_)).congr heq
  rw [heq]
  set n := x.length
  set P := (n + 1) ^ max lN 1
  have hP1 : n + 1 ≤ P := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hP2 : (n + 1) ^ lN ≤ P := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hNx : N x ≤ KN * (n + 1) ^ lN := hKN x
  have hbody : ∀ i < N x, (b i x).length ≤ Kb * (KN + 1) ^ lb * (n + 1) ^ (max lN 1 * lb) := by
    intro i hi
    have := hKb (List.replicate i true ++ false :: x)
    simp only [lpN_rep, lpX_rep, List.length_append, List.length_replicate, List.length_cons] at this
    refine this.trans ?_
    rw [mul_assoc, pow_mul, ← mul_pow]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have h3 : KN * (n + 1) ^ lN ≤ KN * P := Nat.mul_le_mul_left _ hP2
    have e : (KN + 1) * P = KN * P + P := by ring
    have hn : x.length = n := rfl
    rw [show (n + 1) ^ max lN 1 = P from rfl]
    omega
  refine (flatMap_range_len_le _ _ _ hbody).trans ?_
  calc N x * (Kb * (KN + 1) ^ lb * (n + 1) ^ (max lN 1 * lb))
      ≤ KN * (n + 1) ^ lN * (Kb * (KN + 1) ^ lb * (n + 1) ^ (max lN 1 * lb)) :=
        Nat.mul_le_mul_right _ hNx
    _ = KN * (Kb * (KN + 1) ^ lb) * (n + 1) ^ (lN + max lN 1 * lb) := by rw [pow_add]; ring

/-- **Length-aware iteration.** -/
theorem PSl.iter {d e : ℕ} {g : List Bool → List Bool} (hg : PSd d g) (q : Polynomial ℕ)
    (hq : ∀ y i, (g^[i] y).length ≤ q.eval (y.length + i)) (Kq : ℕ)
    (hqb : ∀ n, q.eval n ≤ Kq * (n + 1) ^ e) (hd : 1 ≤ d) (he : 1 ≤ e) :
    PSl (e * d + 1) e (fun z => g^[lpN z] (lpX z)) :=
  PSl.of (PSd.iter hg q hq Kq hqb hd he) Kq (fun z => by
    have h1 := hq (lpX z) (lpN z)
    have h2 := LoopTM.lp_len z
    refine h1.trans ((poly_eval_mono q (by omega : (lpX z).length + lpN z ≤ z.length)).trans ?_)
    exact (hqb _))

theorem PUl.lenX : PUl 2 1 (fun x => x.length) := by
  have h1 : PSl 1 1 SmallTM.lenF := PSl.of (PSd.of_lin SmallTM.lenComputable 1 2
    (by simp [SmallTM.lenComputable])) 2 (fun x => by simp [SmallTM.lenF])
  have hl : ∀ x, SmallTM.lenF x = pairU x.length 0 := fun x => by simp [SmallTM.lenF, pairU]
  have h2 := PSl.compT h1 (PSd.horner 1) le_rfl 3 (l := 1) (fun x => by
    rw [hl, hornerF_pairU]; simp [pairU]; omega)
  have h3 := PSl.compT h2 (PSd.horner 0) (by norm_num) 3 (l := 1) (fun x => by
    rw [hl, hornerF_pairU, hornerF_pairU]; simp [pairU]; omega)
  have h4 := PSl.compT h3 (PSd.of_lin SmallTM.sndComputable 1 2 (by simp [SmallTM.sndComputable]))
    (by norm_num) 1 (l := 1) (fun x => by
    rw [hl, hornerF_pairU, hornerF_pairU]; simp [SmallTM.sndF, hM_pairU])
  refine (h4.mono (by norm_num) le_rfl).congr (fun x => ?_)
  rw [hl, hornerF_pairU, hornerF_pairU]
  simp [SmallTM.sndF, hM_pairU]

theorem PSl.drop2 : PSl 1 1 (fun z => lpX (lpX z)) :=
  (PSl.comp PSl.drop PSl.drop le_rfl).mono (by norm_num) (by norm_num)

theorem PSl.bitsEncDrop : PSl 2 1 (fun w => bitsEnc (lpX w)) := by
  have hg : PSl 1 1 (fun z => List.replicate (lpN z) true ++ false :: lpX (lpX z)) :=
    (PSl.append PUl.fst (PSl.cons false PSl.drop2 le_rfl) (by norm_num)).mono (by norm_num)
      (by norm_num)
  have hU : PUl 1 0 (fun z => NthTM.bit (lpX (lpX z)) (lpN z)) :=
    ((PSl.comp hg PUl.nth le_rfl).mono (by norm_num) (by norm_num)).congr
      (fun z => by simp only [lpN_rep, lpX_rep])
  have hN : PUl 2 1 (fun w => (lpX w).length) :=
    (PSl.comp PSl.drop PUl.lenX le_rfl).mono (by norm_num) (by norm_num)
  have hb : PSl 1 0 (fun z => List.replicate (NthTM.bit (lpX (lpX z)) (lpN z)) true ++ [false]) :=
    (PSl.append hU (PSl.const [false]) (by norm_num)).mono (by norm_num) (by norm_num)
  exact ((PSl.flatRange hN (fun j w => List.replicate (NthTM.bit (lpX w) j) true ++ [false]) hb
    (by norm_num) le_rfl).mono (by norm_num) (by norm_num)).congr (fun w => rfl)

theorem PSl.srcBits : PSl 2 1 PvnpReal.srcBits := by
  have hl : PSl 2 1 (fun w => List.replicate (lpX w).length true) :=
    (PSl.comp PSl.drop PUl.lenX le_rfl).mono (by norm_num) (by norm_num)
  have hdd : PSl 2 1 (fun w => lpX (lpX w)) := PSl.drop2.mono (by norm_num) le_rfl
  have h1 := PSl.append PSl.bitsEncDrop hdd (by norm_num)
  have h2 := PSl.append hl (PSl.cons false h1 (by norm_num)) (by norm_num)
  have h3 := PSl.append PUl.fst (PSl.cons false h2 (by norm_num)) (by norm_num)
  exact (h3.mono (by norm_num) (by norm_num)).congr (fun w => rfl)

/-- **Length-aware pointwise maps of number sequences.** -/
theorem PSl.mapNums (N F : NE) :
    PSl (max (max N.dt 1) (max N.lv 1 * (F.dt + 1))) (N.lv + max N.lv 1 * F.lv)
      (fun y => encNums ((List.range (N.ev 0 (numsOf y))).map (fun i => F.ev i (numsOf y)))) := by
  have hb : PSl F.dt F.lv (fun z => List.replicate (F.ev (lpN z) (numsOf (lpX z))) true ++ [false]) :=
    (PSl.append (NE.pul F) (PSl.const [false]) (le_max_of_le_left F.dt_pos)).mono
      (max_le le_rfl F.dt_pos) (max_le le_rfl (Nat.zero_le _))
  exact (PSl.flatRange (NE.pul0 N) (fun i y => List.replicate (F.ev i (numsOf y)) true ++ [false])
    hb N.dt_pos F.dt_pos).congr (fun y => by simp [encNums, List.flatMap_map])

theorem PSl.stepB : PSl 3 2 Flat.stepB :=
  ((PSl.mapNums Flat.nE Flat.stepE).mono (by decide) (by decide)).congr (fun y => rfl)

theorem PSl.stepIter : PSl 7 2 (fun z => Flat.stepB^[lpN z] (lpX z)) :=
  PSl.iter (e := 2) PSl.stepB.toPSd (Polynomial.X * (Polynomial.X + 1) + Polynomial.X)
    (fun y i => by have := Flat.stepB_growth y i; simp; omega) 3
    (fun n => by simp; nlinarith) (by norm_num) (by norm_num)

/-- **The diagonal interpreter `dW` runs in time `O(n^42)`** (explicit degree 42). -/
theorem PSl.dW : PSl 42 0 (fun w => [dW w]) := by
  have hM : PSl 10 6 (fun y => encNums ((List.range (Flat.iN.ev 0 (numsOf y))).map
      (fun i => Flat.initE.ev i (numsOf y)))) :=
    (PSl.mapNums Flat.iN Flat.initE).mono (by decide) (by decide)
  have hI : PSl 10 6 (fun w => encNums (Flat.initL (srcW w))) :=
    ((PSl.comp PSl.srcBits hM (by norm_num)).mono (by norm_num) (by norm_num)).congr (fun w => by
      simp only [numsOf_srcBits]; rfl)
  have hZ : PSl 10 6 (fun w => List.replicate (lpN w) true ++ false :: encNums (Flat.initL (srcW w))) :=
    (PSl.append PUl.fst (PSl.cons false hI (by norm_num)) (by norm_num)).mono (by norm_num)
      (by norm_num)
  have hIt : PSl 42 12 (fun w => Flat.stepB^[lpN w] (encNums (Flat.initL (srcW w)))) :=
    ((PSl.comp hZ PSl.stepIter (by norm_num)).mono (by norm_num) (by norm_num)).congr (fun w => by
      simp only [lpN_rep, lpX_rep])
  have hA : PUl 2 0 (fun y => ansE.ev 0 (numsOf y)) :=
    (NE.pul0 ansE).mono (by decide) (by decide)
  have hR := PSl.comp hIt hA (by norm_num)
  have hO : PSl 1 0 SmallTM.orF :=
    PSl.of (PSd.of_lin orComputable 1 1 (by simp [orComputable])) 1 (fun x => by simp [SmallTM.orF])
  refine ((PSl.comp hR hO (by norm_num)).mono (by norm_num) (by norm_num)).congr (fun w => ?_)
  simp only [ansE, numsOf_stepB_iter, SmallTM.orF, PvnpReal.dW, Flat.tagOf,
    NE.ev_sub, NE.ev_eq, NE.ev_c]
  by_cases h : Flat.tagE.ev 0 (Flat.stepL^[lpN w] (Flat.initL (srcW w))) = 5 <;> simp [h]

/-- **Time hierarchy with explicit exponent 42**: for every `t` whose padding `1^{t(n)}0x` is computed in
time `A·(t(n)+n+1)^a`, `diagT t ∈ DTIME(K·(t(n)+n+1)^{42a})` and `diagT t ∉ DTIME(T)` for all `T = o(t)`. -/
theorem time_hierarchy_42 (t : ℕ → ℕ) (hp : TM2ComputableInTime strEnc strEnc (padWith t))
    (A a : ℕ) (ha : 1 ≤ a) (hA : ∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) :
    ∃ K, InDTIME (fun n => K * (t n + n + 1) ^ (a * 42)) (diagT t) ∧
      ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (diagT t) := by
  obtain ⟨K, hK⟩ := diagT_in_DTIME_of_deg PSl.dW.toPSd (by norm_num) t hp A a ha hA
  exact ⟨K, hK, fun T hT => diagT_not_in_DTIME t T hT⟩

/-- **Exponential instance**: some language is in `DTIME(K·(2ⁿ+n+1)^42)` but not in `DTIME(2ⁿ/(n+1))`. -/
theorem exp_time_hierarchy_42 : ∃ K, ∃ L : Language,
    InDTIME (fun n => K * (2 ^ n + n + 1) ^ 42) L ∧ ¬ InDTIME (fun n => 2 ^ n / (n + 1)) L := by
  obtain ⟨K, h1, h2⟩ := time_hierarchy_42 (fun n => 2 ^ n) padExp 9 1 le_rfl (fun n => by
    show 4 * 2 ^ n + 5 * n + 4 ≤ 9 * (2 ^ n + n + 1) ^ 1
    rw [pow_one]; omega)
  refine ⟨K, _, by simpa using h1, h2 _ (fun D => ⟨D, fun n hn => ?_⟩)⟩
  have h3 : (n + 1) * (2 ^ n / (n + 1)) ≤ 2 ^ n := Nat.mul_div_le _ _
  have h4 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h5 : 1 ≤ 2 ^ n / (n + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h6 : D * (2 ^ n / (n + 1)) ≤ n * (2 ^ n / (n + 1)) := Nat.mul_le_mul_right _ hn
  have e : (n + 1) * (2 ^ n / (n + 1)) = n * (2 ^ n / (n + 1)) + 2 ^ n / (n + 1) := by ring
  omega

end PvnpReal
