/-
  PvnpReal.ExplicitCost — degree-tracked polynomial time.

  `PSd d f`: `f` is computed by a `FinTM2` whose time polynomial is bounded by `K·(n+1)^d` (explicit
  degree `d`, existential constant `K`). We re-derive the closure combinators with explicit degree
  bookkeeping (composition multiplies degrees, fan-out takes the common degree), and the degrees
  of the primitive machines read off their concrete time polynomials.
-/
import PvnpReal.GapHierarchy
import PvnpReal.BruteBits

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-- Degree-`d` polynomial time. -/
def PSd (d : ℕ) (f : List Bool → List Bool) : Prop :=
  ∃ h : TM2ComputableInPolyTime strEnc strEnc f, ∃ K, ∀ n, h.time.eval n ≤ K * (n + 1) ^ d

/-- Degree-`d` unary quantity. -/
def PUd (d : ℕ) (u : List Bool → ℕ) : Prop := PSd d (fun x => List.replicate (u x) true)

theorem PSd.toPS {d : ℕ} {f : List Bool → List Bool} (h : PSd d f) : PS f :=
  let ⟨h, _⟩ := h; ⟨h⟩

theorem PSd.mono {d d' : ℕ} {f : List Bool → List Bool} (h : PSd d f) (hd : d ≤ d') : PSd d' f := by
  obtain ⟨h, K, hK⟩ := h
  exact ⟨h, K, fun n => (hK n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd))⟩

theorem PSd.congr {d : ℕ} {f g : List Bool → List Bool} (h : PSd d f) (e : ∀ x, f x = g x) :
    PSd d g := by
  have : f = g := funext e
  subst this; exact h

theorem PUd.congr {d : ℕ} {u v : List Bool → ℕ} (h : PUd d u) (e : ∀ x, u x = v x) : PUd d v :=
  PSd.congr h (fun x => by rw [e])

/-- A linear-time machine `time = a·X + b` has degree 1. -/
theorem PSd.of_lin {f : List Bool → List Bool} (h : TM2ComputableInPolyTime strEnc strEnc f)
    (a b : ℕ) (ht : h.time = (a : Polynomial ℕ) * Polynomial.X + (b : Polynomial ℕ)) : PSd 1 f := by
  refine ⟨h, a + b, fun n => ?_⟩
  rw [ht]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_X,
    pow_one]
  nlinarith

/-! ### Arithmetic cores -/

theorem comp_arith (K1 K2 C d1 d2 n s q : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hs : s ≤ K1 * (n + 1) ^ d1) (hq : q ≤ K2 * (n + C * s + 1) ^ d2) :
    s + 2 * (n + C * s) + 2 + q ≤
      (K1 + 2 * (C * K1 + 1) + 2 + K2 * (C * K1 + 1) ^ d2) * (n + 1) ^ (d1 * d2) := by
  set N := (n + 1) ^ d1 with hNdef
  have hN : n + 1 ≤ N := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ N := Nat.pow_le_pow_right (by omega) hd1
  have hCs : C * s ≤ C * K1 * N := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hs
  have hx : n + C * s + 1 ≤ (C * K1 + 1) * N := by
    have e : (C * K1 + 1) * N = C * K1 * N + N := by ring
    omega
  have hM : (n + 1) ^ (d1 * d2) = N ^ d2 := by rw [pow_mul]
  have hN1 : 1 ≤ N := by omega
  have hNM : N ≤ N ^ d2 := by
    calc N = N ^ 1 := (pow_one _).symm
      _ ≤ N ^ d2 := Nat.pow_le_pow_right hN1 hd2
  have hq2 : q ≤ K2 * (C * K1 + 1) ^ d2 * N ^ d2 := by
    refine hq.trans ?_
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx _)
  rw [hM]
  generalize N ^ d2 = M at hNM hq2 ⊢
  generalize K2 * (C * K1 + 1) ^ d2 = E at hq2 ⊢
  have a1 : K1 * N ≤ K1 * M := Nat.mul_le_mul_left _ hNM
  have a2 : C * K1 * N ≤ C * K1 * M := Nat.mul_le_mul_left _ hNM
  have e : (K1 + 2 * (C * K1 + 1) + 2 + E) * M = K1 * M + 2 * (C * K1 * M) + 2 * M + 2 * M + E * M := by
    ring
  omega

theorem PSd.comp {d1 d2 : ℕ} {f g : List Bool → List Bool} (hf : PSd d1 f) (hg : PSd d2 g)
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2) : PSd (d1 * d2) (fun x => g (f x)) := by
  obtain ⟨h1, K1, hK1⟩ := hf
  obtain ⟨h2, K2, hK2⟩ := hg
  refine ⟨composeComputable h1 h2, K1 + 2 * (pushTotal h1.tm * K1 + 1) + 2 +
    K2 * (pushTotal h1.tm * K1 + 1) ^ d2, fun n => ?_⟩
  have := comp_arith K1 K2 (pushTotal h1.tm) d1 d2 n (h1.time.eval n)
    (h2.time.eval (n + pushTotal h1.tm * h1.time.eval n)) hd1 hd2 (hK1 n) (hK2 _)
  simpa [composeComputable, Polynomial.eval_comp] using this

theorem fan_arith (K1 K2 C1 C2 d n s1 s2 : ℕ) (hd : 1 ≤ d)
    (h1 : s1 ≤ K1 * (n + 1) ^ d) (h2 : s2 ≤ K2 * (n + 1) ^ d) :
    2 * n + s1 + s2 + 2 * (n + C1 * s1) + 2 * (n + C2 * s2) + 8 ≤
      (6 + K1 + K2 + 2 * C1 * K1 + 2 * C2 * K2 + 8) * (n + 1) ^ d := by
  set N := (n + 1) ^ d
  have hN : n + 1 ≤ N := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ N := Nat.pow_le_pow_right (by omega) hd
  have a1 : C1 * s1 ≤ C1 * K1 * N := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ h1
  have a2 : C2 * s2 ≤ C2 * K2 * N := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ h2
  have e : (6 + K1 + K2 + 2 * C1 * K1 + 2 * C2 * K2 + 8) * N =
      6 * N + K1 * N + K2 * N + 2 * (C1 * K1 * N) + 2 * (C2 * K2 * N) + 8 * N := by ring
  omega

theorem PSd.append {d : ℕ} {f g : List Bool → List Bool} (hf : PSd d f) (hg : PSd d g)
    (hd : 1 ≤ d) : PSd d (fun x => f x ++ g x) := by
  obtain ⟨h1, K1, hK1⟩ := hf
  obtain ⟨h2, K2, hK2⟩ := hg
  refine ⟨fanComputable h1 h2, 6 + K1 + K2 + 2 * pushTotal h1.tm * K1 + 2 * pushTotal h2.tm * K2 + 8,
    fun n => ?_⟩
  have := fan_arith K1 K2 (pushTotal h1.tm) (pushTotal h2.tm) d n _ _ hd (hK1 n) (hK2 n)
  simpa [fanComputable] using this

/-! ### Primitives -/

theorem PSd.const (c : List Bool) : PSd 1 (fun _ => c) :=
  PSd.of_lin (constListComputable c) 1 1 (by simp [constListComputable])

theorem PSd.id : PSd 1 (fun x => x) :=
  ⟨idComputableInPolyTime strEnc, 1, fun n => by simp [idComputableInPolyTime]⟩

theorem PSd.cons (b : Bool) {d : ℕ} {f : List Bool → List Bool} (hf : PSd d f) (hd : 1 ≤ d) :
    PSd d (fun x => b :: f x) :=
  ((PSd.const [b]).mono hd).append hf hd

theorem PUd.const (n : ℕ) : PUd 1 (fun _ => n) := PSd.const _

theorem PUd.fst : PUd 1 lpN := PSd.of_lin SmallTM.fstComputable 1 2 (by simp [SmallTM.fstComputable])

theorem PSd.drop : PSd 1 lpX :=
  ((PSd.comp (PSd.of_lin SmallTM.revDropComputable 1 2 (by simp [SmallTM.revDropComputable]))
    (PSd.of_lin SmallTM.revComputable 1 1 (by simp [SmallTM.revComputable])) le_rfl le_rfl)).congr
    (fun x => by simp [SmallTM.revDropF])

theorem PUd.nth : PUd 1 (fun z => NthTM.bit (lpX z) (lpN z)) :=
  PSd.of_lin NthTM.nthComputable 2 4 (by simp [NthTM.nthComputable])

theorem PUd.comp {d1 d2 : ℕ} {u : List Bool → ℕ} (hu : PUd d2 u) {f : List Bool → List Bool}
    (hf : PSd d1 f) (h1 : 1 ≤ d1) (h2 : 1 ≤ d2) : PUd (d1 * d2) (fun x => u (f x)) :=
  PSd.comp hf hu h1 h2

theorem PUd.add {d : ℕ} {u v : List Bool → ℕ} (hu : PUd d u) (hv : PUd d v) (hd : 1 ≤ d) :
    PUd d (fun x => u x + v x) :=
  (PSd.append hu hv hd).congr (fun x => by rw [List.replicate_add])

theorem PUd.sub {d : ℕ} {u v : List Bool → ℕ} (hu : PUd d u) (hv : PUd d v) (hd : 1 ≤ d) :
    PUd d (fun x => u x - v x) := by
  have := PSd.comp (PSd.append hu (PSd.cons false hv hd) hd)
    (PSd.of_lin monusComputable 4 4 (by simp [monusComputable])) hd le_rfl
  rw [mul_one] at this
  exact this.congr (fun x => by simp [monusF, lpN_rep, lpX_rep, lpN_replicate])

theorem PUd.getNum {d : ℕ} {u : List Bool → ℕ} {s : List Bool → List Bool} (hu : PUd d u)
    (hs : PSd d s) (hd : 1 ≤ d) : PUd d (fun x => (numsOf (s x)).getD (u x) 0) := by
  have := PSd.comp (PSd.append hu (PSd.cons false hs hd) hd)
    (PSd.of_lin numAtComputable 6 6 (by simp [numAtComputable])) hd le_rfl
  rw [mul_one] at this
  exact this.congr (fun x => by simp [numAt, lpN_rep, lpX_rep])

theorem PSd.horner (a : ℕ) : PSd 2 (hornerF a) := by
  refine ⟨hornerComputable a, 10, fun n => ?_⟩
  simp only [hornerComputable, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  nlinarith

theorem PUd.mul {d : ℕ} {u v : List Bool → ℕ} (hu : PUd d u) (hv : PUd d v) (hd : 1 ≤ d) :
    PUd (d * 2) (fun x => u x * v x) := by
  have hp : PSd d (fun x => pairU (u x) (v x)) := (PSd.append hu (PSd.cons false hv hd) hd).congr
    (fun x => by simp [pairU])
  have hh := PSd.comp hp (PSd.horner 0) hd (by norm_num)
  have := PSd.comp hh (PSd.of_lin SmallTM.sndComputable 1 2 (by simp [SmallTM.sndComputable]))
    (by nlinarith) le_rfl
  rw [mul_one] at this
  exact this.congr (fun x => by simp [hornerF_pairU, SmallTM.sndF, hM_pairU])

/-! ### Expressions, loops, iteration -/

/-- Degree of the evaluator of an `NE` expression (doubles at each multiplication). -/
def NE.deg : NE → ℕ
  | .c _ => 1
  | .p => 1
  | .get e => e.deg
  | .add a b => max a.deg b.deg
  | .mul a b => max a.deg b.deg * 2
  | .sub a b => max a.deg b.deg

theorem NE.deg_pos (e : NE) : 1 ≤ e.deg := by
  induction e with
  | c n => exact le_rfl
  | p => exact le_rfl
  | get e ih => exact ih
  | add a b iha ihb => exact le_max_of_le_left iha
  | mul a b iha ihb => simp only [NE.deg]; have := le_max_left a.deg b.deg; omega
  | sub a b iha ihb => exact le_max_of_le_left iha

/-- **Explicit-degree expression evaluation.** -/
theorem NE.pud (e : NE) : PUd e.deg (fun z => e.ev (lpN z) (numsOf (lpX z))) := by
  induction e with
  | c n => exact PUd.const n
  | p => exact PUd.fst
  | get e ih => exact PUd.getNum ih (PSd.drop.mono e.deg_pos) e.deg_pos
  | add a b iha ihb =>
    exact PUd.add (iha.mono (le_max_left _ _)) (ihb.mono (le_max_right _ _))
      (le_max_of_le_left a.deg_pos)
  | mul a b iha ihb =>
    exact PUd.mul (iha.mono (le_max_left _ _)) (ihb.mono (le_max_right _ _))
      (le_max_of_le_left a.deg_pos)
  | sub a b iha ihb =>
    exact PUd.sub (iha.mono (le_max_left _ _)) (ihb.mono (le_max_right _ _))
      (le_max_of_le_left a.deg_pos)

theorem NE.pud0 (e : NE) : PUd e.deg (fun y => e.ev 0 (numsOf y)) := by
  have := PUd.comp (NE.pud e) (PSd.cons false PSd.id le_rfl) le_rfl e.deg_pos
  rw [one_mul] at this
  exact this.congr (fun y => by simp only [LoopTM.lpN_cons_false, LoopTM.lpX_cons_false])

theorem loop_arith (K C d n p : ℕ) (hd : 1 ≤ d) (hp : p ≤ K * (n + 1) ^ d) :
    2 * n + 6 + n * (4 * n + 4 + p + 2 * C * p) ≤ (16 + K + 2 * C * K) * (n + 1) ^ (d + 1) := by
  set N := (n + 1) ^ d
  have hN : n + 1 ≤ N := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ N := Nat.pow_le_pow_right (by omega) hd
  have hM : (n + 1) ^ (d + 1) = (n + 1) * N := by rw [pow_succ]; ring
  rw [hM]
  have a1 : 2 * C * p ≤ 2 * C * K * N := by
    rw [mul_assoc (2 * C)]; exact Nat.mul_le_mul_left _ hp
  have a2 : 4 * n + 4 + p + 2 * C * p ≤ (8 + K + 2 * C * K) * N := by
    have e : (8 + K + 2 * C * K) * N = 8 * N + K * N + 2 * C * K * N := by ring
    omega
  have a3 : n * (4 * n + 4 + p + 2 * C * p) ≤ (n + 1) * ((8 + K + 2 * C * K) * N) :=
    Nat.mul_le_mul (by omega) a2
  have a4 : n + 1 ≤ (n + 1) * N := Nat.le_mul_of_pos_right _ (by omega)
  have e : (16 + K + 2 * C * K) * ((n + 1) * N) = (n + 1) * ((8 + K + 2 * C * K) * N) +
    8 * ((n + 1) * N) := by ring
  omega

theorem PSd.loop {d : ℕ} {g : List Bool → List Bool} (hg : PSd d g) (hd : 1 ≤ d) :
    PSd (d + 1) (loopF g) := by
  obtain ⟨h, K, hK⟩ := hg
  refine ⟨loopComputable h, 16 + K + 2 * pushTotal h.tm * K, fun n => ?_⟩
  have := loop_arith K (pushTotal h.tm) d n _ hd (hK n)
  simpa [loopComputable, mul_assoc] using this

/-- **Explicit-degree concatenation over a range.** -/
theorem PSd.flatRange {dN db : ℕ} {N : List Bool → ℕ} (hN : PUd dN N) (b : ℕ → List Bool → List Bool)
    (hb : PSd db (fun z => b (lpN z) (lpX z))) (hdN : 1 ≤ dN) (hdb : 1 ≤ db) :
    PSd (dN * (db + 1)) (fun x => (List.range (N x)).flatMap fun i => b i x) := by
  have hin : PSd dN (fun x => List.replicate (N x) true ++ false :: x) :=
    PSd.append hN (PSd.cons false (PSd.id.mono hdN) hdN) hdN
  refine (PSd.comp hin (PSd.loop hb hdb) hdN (by omega)).congr (fun x => ?_)
  simp only [loopF, lpN_rep, lpX_rep]

theorem iter_arith (K Kq d e n p Q : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hQ : Q ≤ Kq * (n + 1) ^ e) (hp : p ≤ K * (Q + 1) ^ d) :
    3 * n + 6 + n * (2 * Q + p + 3) + 2 * Q ≤
      (4 * Kq + K * (Kq + 1) ^ d + 12) * (n + 1) ^ (e * d + 1) := by
  set A := (n + 1) ^ e
  have hA : n + 1 ≤ A := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ A := Nat.pow_le_pow_right (by omega) he
  set B := (n + 1) ^ (e * d)
  have hB : B = A ^ d := by simp only [B, A, ← pow_mul]
  have hAB : A ≤ B := by
    rw [hB]
    calc A = A ^ 1 := (pow_one _).symm
      _ ≤ A ^ d := Nat.pow_le_pow_right (by omega) hd
  have hp2 : p ≤ K * (Kq + 1) ^ d * B := by
    refine hp.trans ?_
    rw [hB, mul_assoc, ← mul_pow]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have e2 : (Kq + 1) * A = Kq * A + A := by ring
    omega
  have hM : (n + 1) ^ (e * d + 1) = (n + 1) * B := by rw [pow_succ]; ring
  rw [hM]
  have hQB : Q ≤ Kq * B := hQ.trans (Nat.mul_le_mul_left _ hAB)
  generalize K * (Kq + 1) ^ d = E at hp2 ⊢
  have a2 : 2 * Q + p + 3 ≤ (2 * Kq + E + 3) * B := by
    have e2 : (2 * Kq + E + 3) * B = 2 * (Kq * B) + E * B + 3 * B := by ring
    omega
  have a3 : n * (2 * Q + p + 3) ≤ (n + 1) * ((2 * Kq + E + 3) * B) := Nat.mul_le_mul (by omega) a2
  have a4 : n + 1 ≤ (n + 1) * B := Nat.le_mul_of_pos_right _ (by omega)
  have a5 : Kq * B ≤ Kq * ((n + 1) * B) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have e3 : (4 * Kq + E + 12) * ((n + 1) * B) = (n + 1) * ((2 * Kq + E + 3) * B) +
    2 * (Kq * ((n + 1) * B)) + 9 * ((n + 1) * B) := by ring
  omega

/-- **Explicit-degree iteration.** -/
theorem PSd.iter {d e : ℕ} {g : List Bool → List Bool} (hg : PSd d g) (q : Polynomial ℕ)
    (hq : ∀ y i, (g^[i] y).length ≤ q.eval (y.length + i)) (Kq : ℕ)
    (hqb : ∀ n, q.eval n ≤ Kq * (n + 1) ^ e) (hd : 1 ≤ d) (he : 1 ≤ e) :
    PSd (e * d + 1) (fun z => g^[lpN z] (lpX z)) := by
  obtain ⟨h, K, hK⟩ := hg
  obtain ⟨h', ht⟩ := iter_exists h q hq
  refine ⟨h', 4 * Kq + K * (Kq + 1) ^ d + 12, fun n => ?_⟩
  rw [ht]
  have := iter_arith K Kq d e n _ _ hd he (hqb n) (hK (q.eval n))
  simpa [Polynomial.eval_comp] using this

/-! ### The universal interpreter with an explicit degree -/

theorem PUd.lenX : PUd 4 (fun x => x.length) := by
  have h1 : PSd 1 SmallTM.lenF :=
    PSd.of_lin SmallTM.lenComputable 1 2 (by simp [SmallTM.lenComputable])
  have h2 := PSd.comp h1 (PSd.horner 1) le_rfl (by norm_num)
  have h3 := PSd.comp h2 (PSd.horner 0) (by norm_num) (by norm_num)
  have h4 := PSd.comp h3 (PSd.of_lin SmallTM.sndComputable 1 2 (by simp [SmallTM.sndComputable]))
    (by norm_num) le_rfl
  refine (show PSd 4 _ from h4).congr (fun x => ?_)
  have e : SmallTM.lenF x = pairU x.length 0 := by simp [SmallTM.lenF, pairU]
  rw [e, hornerF_pairU, hornerF_pairU]
  simp [SmallTM.sndF, hM_pairU]

theorem PSd.bitsEnc {ds : ℕ} {s : List Bool → List Bool} (hs : PSd ds s) (hds : 1 ≤ ds) :
    PSd (ds * 4 * (ds + 1)) (fun w => bitsEnc (s w)) := by
  have hd : PSd ds (fun z => s (lpX z)) := by
    have := PSd.comp PSd.drop hs le_rfl hds; rwa [one_mul] at this
  have hg : PSd ds (fun z => List.replicate (lpN z) true ++ false :: s (lpX z)) :=
    PSd.append (PUd.fst.mono hds) (PSd.cons false hd hds) hds
  have hU : PUd ds (fun z => NthTM.bit (s (lpX z)) (lpN z)) := by
    have := PUd.comp PUd.nth hg hds le_rfl
    rw [mul_one] at this
    exact this.congr (fun z => by simp only [lpN_rep, lpX_rep])
  have hN : PUd (ds * 4) (fun w => (s w).length) := PUd.comp PUd.lenX hs hds (by norm_num)
  exact (PSd.flatRange hN (fun j w => List.replicate (NthTM.bit (s w) j) true ++ [false])
    (PSd.append hU ((PSd.const [false]).mono hds) hds) (by omega) hds).congr (fun w => rfl)

theorem PSd.srcBits : PSd 8 PvnpReal.srcBits := by
  have hb : PSd 8 (fun w => PvnpReal.bitsEnc (lpX w)) := PSd.bitsEnc PSd.drop le_rfl
  have hl : PSd 8 (fun w => List.replicate (lpX w).length true) :=
    (PUd.comp PUd.lenX PSd.drop le_rfl (by norm_num)).mono (by norm_num)
  have hdd : PSd 8 (fun w => lpX (lpX w)) := (PSd.comp PSd.drop PSd.drop le_rfl le_rfl).mono (by norm_num)
  exact PSd.append (PUd.fst.mono (by norm_num)) (PSd.cons false (PSd.append hl (PSd.cons false
    (PSd.append hb hdd (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)

/-- **Explicit-degree pointwise maps of number sequences.** -/
theorem PSd.mapNums (N F : NE) : PSd (N.deg * (F.deg + 1))
    (fun y => encNums ((List.range (N.ev 0 (numsOf y))).map (fun i => F.ev i (numsOf y)))) :=
  (PSd.flatRange (NE.pud0 N) (fun i y => List.replicate (F.ev i (numsOf y)) true ++ [false])
    (PSd.append (NE.pud F) ((PSd.const [false]).mono F.deg_pos) F.deg_pos) N.deg_pos
    F.deg_pos).congr (fun y => by simp [encNums, List.flatMap_map])

/-- Degree of one step of the flat machine. -/
def stepDeg : ℕ := Flat.nE.deg * (Flat.stepE.deg + 1)

theorem PSd.stepB : PSd stepDeg Flat.stepB :=
  (PSd.mapNums Flat.nE Flat.stepE).congr (fun y => rfl)

theorem stepDeg_pos : 1 ≤ stepDeg :=
  Nat.mul_pos (Flat.nE.deg_pos) (by omega)

theorem PSd.stepIter : PSd (2 * stepDeg + 1) (fun z => Flat.stepB^[lpN z] (lpX z)) :=
  PSd.iter PSd.stepB (Polynomial.X * (Polynomial.X + 1) + Polynomial.X)
    (fun y i => by have := Flat.stepB_growth y i; simp; omega) 3
    (fun n => by simp; nlinarith) stepDeg_pos (by norm_num)

/-- Degree of the initial-configuration map. -/
def initDeg : ℕ := 8 * (Flat.iN.deg * (Flat.initE.deg + 1))

/-- The expression reading the answer tag. -/
def ansE : NE := NE.sub (NE.c 1) (NE.eq Flat.tagE (NE.c 5))

/-- **The explicit degree of the diagonal interpreter `dW`.** -/
def dWdeg : ℕ := initDeg * (2 * stepDeg + 1) * ansE.deg * 1

theorem initDeg_pos : 1 ≤ initDeg := by
  unfold initDeg
  have := Nat.mul_pos (Flat.iN.deg_pos) (by omega : 0 < Flat.initE.deg + 1)
  omega

theorem PSd.dW : PSd dWdeg (fun w => [dW w]) := by
  have hI : PSd initDeg (fun w => encNums (Flat.initL (srcW w))) :=
    (PSd.comp PSd.srcBits (PSd.mapNums Flat.iN Flat.initE) (by norm_num)
      (Nat.mul_pos Flat.iN.deg_pos (by omega))).congr (fun w => by
      simp only [numsOf_srcBits]; rfl)
  have hZ : PSd initDeg (fun w => List.replicate (lpN w) true ++ false :: encNums (Flat.initL (srcW w))) :=
    PSd.append (PUd.fst.mono initDeg_pos) (PSd.cons false hI initDeg_pos) initDeg_pos
  have hIt : PSd (initDeg * (2 * stepDeg + 1))
      (fun w => Flat.stepB^[lpN w] (encNums (Flat.initL (srcW w)))) :=
    (PSd.comp hZ PSd.stepIter initDeg_pos (by omega)).congr (fun w => by
      simp only [lpN_rep, lpX_rep])
  have hR : PUd (initDeg * (2 * stepDeg + 1) * ansE.deg)
      (fun w => ansE.ev 0 (numsOf (Flat.stepB^[lpN w] (encNums (Flat.initL (srcW w)))))) :=
    PUd.comp (NE.pud0 ansE) hIt (Nat.mul_pos initDeg_pos (by omega)) ansE.deg_pos
  have hpos : 1 ≤ initDeg * (2 * stepDeg + 1) * ansE.deg :=
    Nat.mul_pos (Nat.mul_pos initDeg_pos (by omega)) ansE.deg_pos
  refine (PSd.comp hR (PSd.of_lin orComputable 1 1 (by simp [orComputable])) hpos le_rfl).congr
    (fun w => ?_)
  simp only [ansE, numsOf_stepB_iter, SmallTM.orF, PvnpReal.dW, Flat.tagOf,
    NE.ev_sub, NE.ev_eq, NE.ev_c]
  by_cases h : Flat.tagE.ev 0 (Flat.stepL^[lpN w] (Flat.initL (srcW w))) = 5 <;> simp [h]

/-! ### Time hierarchy with an explicit exponent -/

theorem comp_arithN (K1 K2 C d2 n s q N : ℕ) (hd2 : 1 ≤ d2) (hN : n + 1 ≤ N)
    (hs : s ≤ K1 * N) (hq : q ≤ K2 * (n + C * s + 1) ^ d2) :
    s + 2 * (n + C * s) + 2 + q ≤ (K1 + 2 * (C * K1 + 1) + 2 + K2 * (C * K1 + 1) ^ d2) * N ^ d2 := by
  have hCs : C * s ≤ C * K1 * N := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hs
  have hx : n + C * s + 1 ≤ (C * K1 + 1) * N := by
    have e : (C * K1 + 1) * N = C * K1 * N + N := by ring
    omega
  have hN1 : 1 ≤ N := by omega
  have hNM : N ≤ N ^ d2 := by
    calc N = N ^ 1 := (pow_one _).symm
      _ ≤ N ^ d2 := Nat.pow_le_pow_right hN1 hd2
  have hq2 : q ≤ K2 * (C * K1 + 1) ^ d2 * N ^ d2 := by
    refine hq.trans ?_
    rw [mul_assoc, ← mul_pow]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx _)
  generalize N ^ d2 = M at hNM hq2 ⊢
  generalize K2 * (C * K1 + 1) ^ d2 = E at hq2 ⊢
  have a1 : K1 * N ≤ K1 * M := Nat.mul_le_mul_left _ hNM
  have a2 : C * K1 * N ≤ C * K1 * M := Nat.mul_le_mul_left _ hNM
  have e : (K1 + 2 * (C * K1 + 1) + 2 + E) * M = K1 * M + 2 * (C * K1 * M) + 2 * M + 2 * M + E * M := by
    ring
  omega

/-- Upper bound for `diagT t` from any explicit degree `D` of the interpreter `dW`. -/
theorem diagT_in_DTIME_of_deg {D : ℕ} (hD : PSd D (fun w => [dW w])) (hD1 : 1 ≤ D) (t : ℕ → ℕ)
    (hp : TM2ComputableInTime strEnc strEnc (padWith t)) (A a : ℕ) (ha : 1 ≤ a)
    (hA : ∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) :
    ∃ K, InDTIME (fun n => K * (t n + n + 1) ^ (a * D)) (diagT t) := by
  obtain ⟨hs, K2, hK2⟩ := hD
  let h2 := strToDecider hs
  let hc := composeInTime hp h2.toTM2ComputableInTime (fun m => h2.time.eval m)
    (fun m => le_rfl) (fun a b h => poly_eval_mono h2.time h)
  refine ⟨A + 2 * (pushTotal hp.tm * A + 1) + 2 + K2 * (pushTotal hp.tm * A + 1) ^ D,
    dW ∘ padWith t, hc, fun n => ?_, fun x => diagT_iff t x⟩
  have hm : 1 ≤ t n + n + 1 := by omega
  have hN : n + 1 ≤ (t n + n + 1) ^ a :=
    le_trans (by omega : n + 1 ≤ t n + n + 1) (by
      calc t n + n + 1 = (t n + n + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right hm ha)
  have := comp_arithN A K2 (pushTotal hp.tm) D n (hp.time n)
    (h2.time.eval (n + pushTotal hp.tm * hp.time n)) _ hD1 hN (hA n) (hK2 _)
  rw [← pow_mul] at this
  exact this

theorem dWdeg_pos : 1 ≤ dWdeg := by
  unfold dWdeg
  have h1 := initDeg_pos
  have h2 := ansE.deg_pos
  have := Nat.mul_pos (Nat.mul_pos h1 (by omega : 0 < 2 * stepDeg + 1)) h2
  omega

/-- The explicit degree of the interpreter, evaluated. -/
theorem dWdeg_eq : dWdeg = 8495200 := by decide

/-- **Time hierarchy with an explicit exponent** `D = dWdeg = 8495200`: for every time function `t`
whose padding is computed in time `A·(t(n)+n+1)^a`, `diagT t ∈ DTIME(K·(t(n)+n+1)^{a·D})` and
`diagT t ∉ DTIME(T)` for every `T = o(t)`. -/
theorem time_hierarchy_explicit (t : ℕ → ℕ) (hp : TM2ComputableInTime strEnc strEnc (padWith t))
    (A a : ℕ) (ha : 1 ≤ a) (hA : ∀ n, hp.time n ≤ A * (t n + n + 1) ^ a) :
    ∃ K, InDTIME (fun n => K * (t n + n + 1) ^ (a * 8495200)) (diagT t) ∧
      ∀ T : ℕ → ℕ, (∀ D, ∃ N, ∀ n ≥ N, D * T n + 1 ≤ t n) → ¬ InDTIME T (diagT t) := by
  obtain ⟨K, hK⟩ := diagT_in_DTIME_of_deg PSd.dW dWdeg_pos t hp A a ha hA
  rw [dWdeg_eq] at hK
  exact ⟨K, hK, fun T hT => diagT_not_in_DTIME t T hT⟩

/-- Exponential instance with the explicit exponent. -/
theorem exp_time_hierarchy_explicit : ∃ K, ∃ L : Language,
    InDTIME (fun n => K * (2 ^ n + n + 1) ^ 8495200) L ∧ ¬ InDTIME (fun n => 2 ^ n / (n + 1)) L := by
  obtain ⟨K, h1, h2⟩ := time_hierarchy_explicit (fun n => 2 ^ n) padExp 9 1 le_rfl (fun n => by
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
