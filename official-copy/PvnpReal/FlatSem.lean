/-
  PvnpReal.FlatSem — abstract semantics of the flat machine (`mstep` on a state and
  `ℕ`-indexed stacks) and the **layout lemma** `rep_step`: `stepL` on an array layout `Rep`resenting
  a configuration represents the abstract successor.
-/
import PvnpReal.Diag2

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability NE

namespace Flat

structure MC where
  q : ℕ
  S : ℕ → List ℕ

/-- Field `f` of instruction `q` of a flat program. -/
def pf (Pc : List ℕ) (q f : ℕ) : ℕ := Pc.getD (6 + q * Pc.getD 1 0 + f) 0

/-- One abstract step. -/
def mstep (Pc : List ℕ) (c : MC) : MC :=
  if pf Pc c.q 0 = 1 then
    ⟨pf Pc c.q 3, Function.update c.S (pf Pc c.q 1) (pf Pc c.q 2 :: c.S (pf Pc c.q 1))⟩
  else if pf Pc c.q 0 = 2 then
    ⟨pf Pc c.q (4 + oc (c.S (pf Pc c.q 1)).head?),
      Function.update c.S (pf Pc c.q 1) (c.S (pf Pc c.q 1)).tail⟩
  else if pf Pc c.q 0 = 3 then ⟨pf Pc c.q (4 + oc (c.S (pf Pc c.q 1)).head?), c.S⟩
  else if pf Pc c.q 0 = 4 then ⟨pf Pc c.q 3, c.S⟩
  else c

theorem mstep_push {Pc : List ℕ} {c : MC} (h : pf Pc c.q 0 = 1) : mstep Pc c =
    ⟨pf Pc c.q 3, Function.update c.S (pf Pc c.q 1) (pf Pc c.q 2 :: c.S (pf Pc c.q 1))⟩ := by
  simp [mstep, h]
theorem mstep_pop {Pc : List ℕ} {c : MC} (h : pf Pc c.q 0 = 2) : mstep Pc c =
    ⟨pf Pc c.q (4 + oc (c.S (pf Pc c.q 1)).head?),
      Function.update c.S (pf Pc c.q 1) (c.S (pf Pc c.q 1)).tail⟩ := by
  simp [mstep, h]
theorem mstep_peek {Pc : List ℕ} {c : MC} (h : pf Pc c.q 0 = 3) : mstep Pc c =
    ⟨pf Pc c.q (4 + oc (c.S (pf Pc c.q 1)).head?), c.S⟩ := by
  simp [mstep, h]
theorem mstep_nop {Pc : List ℕ} {c : MC} (h : pf Pc c.q 0 = 4) : mstep Pc c = ⟨pf Pc c.q 3, c.S⟩ := by
  simp [mstep, h]
theorem mstep_other {Pc : List ℕ} {c : MC} (h1 : pf Pc c.q 0 ≠ 1) (h2 : pf Pc c.q 0 ≠ 2)
    (h3 : pf Pc c.q 0 ≠ 3) (h4 : pf Pc c.q 0 ≠ 4) : mstep Pc c = c := by
  simp [mstep, h1, h2, h3, h4]

/-- `L` lays out configuration `c` (capacity `Cap`, `nK` stacks, program `Pc`). -/
def Rep (Cap nK : ℕ) (Pc L : List ℕ) (c : MC) : Prop :=
  5 + nK + nK * Cap + Pc.length ≤ L.length ∧
  L.getD 0 0 = c.q ∧ L.getD 1 0 = Cap ∧ L.getD 2 0 = nK ∧ L.getD 3 0 = Pc.getD 1 0 ∧
  L.getD 4 0 = L.length ∧
  (∀ k < nK, L.getD (5 + k) 0 = (c.S k).length ∧ (c.S k).length ≤ Cap ∧
    ∀ d < (c.S k).length, L.getD (5 + nK + k * Cap + d) 0 = (c.S k).getD ((c.S k).length - 1 - d) 0) ∧
  (∀ m, L.getD (5 + nK + nK * Cap + m) 0 = Pc.getD m 0)

theorem stepL_getD (L : List ℕ) (i : ℕ) :
    (stepL L).getD i 0 = if i < L.getD 4 0 then stepE.ev i L else 0 := by
  simp only [stepL, nE, gt, ev_get, ev_c, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem isPush_ev (i L) : isPush.ev i L = if tagE.ev i L = 1 then 1 else 0 := ev_eq _ _ _ _
theorem isPop_ev (i L) : isPop.ev i L = if tagE.ev i L = 2 then 1 else 0 := ev_eq _ _ _ _
theorem isPeek_ev (i L) : isPeek.ev i L = if tagE.ev i L = 3 then 1 else 0 := ev_eq _ _ _ _
theorem isNop_ev (i L) : isNop.ev i L = if tagE.ev i L = 4 then 1 else 0 := ev_eq _ _ _ _

theorem newLen_ev (i L) : newLen.ev i L = if tagE.ev i L = 1 then lenE.ev i L + 1
    else if tagE.ev i L = 2 then lenE.ev i L - 1 else lenE.ev i L := by
  simp only [newLen, ev_ite, isPush_ev, isPop_ev, ev_add, ev_sub, ev_c]
  split_ifs <;> simp_all

theorem newQ_ev (i L) : newQ.ev i L = if tagE.ev i L = 1 then nxE.ev i L
    else if tagE.ev i L = 4 then nxE.ev i L
    else if tagE.ev i L = 2 ∨ tagE.ev i L = 3 then tnE.ev i L else qE.ev i L := by
  simp only [newQ, ev_ite, isPush_ev, isPop_ev, isPeek_ev, isNop_ev, ev_add]
  split_ifs <;> simp_all <;> omega

theorem ite10_eq0 {P : Prop} [Decidable P] : ((if P then 1 else 0 : ℕ) = 0) ↔ ¬ P := by
  by_cases h : P <;> simp [h]

theorem ite10_mul_eq0 {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : ℕ) * (if Q then 1 else 0) = 0) ↔ ¬ (P ∧ Q) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem stepE_ev (i : ℕ) (L : List ℕ) : stepE.ev i L =
    if i = 0 then newQ.ev i L else if i = 5 + kE.ev i L then newLen.ev i L
    else if tagE.ev i L = 1 ∧ i = (baseE kE).ev i L + lenE.ev i L then aE.ev i L else L.getD i 0 := by
  have c1 : (eq p (c 0)).ev i L = 0 ↔ ¬ i = 0 := by rw [ev_eq]; exact ite10_eq0
  have c2 : (eq p (add (c 5) kE)).ev i L = 0 ↔ ¬ i = 5 + kE.ev i L := by rw [ev_eq]; exact ite10_eq0
  have c3 : (mul isPush (eq p (add (baseE kE) lenE))).ev i L = 0 ↔
      ¬ (tagE.ev i L = 1 ∧ i = (baseE kE).ev i L + lenE.ev i L) := by
    rw [ev_mul, isPush_ev, ev_eq]; exact ite10_mul_eq0
  simp only [stepE, ev_ite, c1, c2, c3, ev_get, ev_p]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem cell_inj {j K d e Cap : ℕ} (hd : d < Cap) (he : e < Cap) (h : j * Cap + d = K * Cap + e) :
    j = K ∧ d = e := by
  have hc : 0 < Cap := by omega
  have h1 : (j * Cap + d) / Cap = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hd, Nat.zero_add]
  have h2 : (K * Cap + e) / Cap = K := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt he, Nat.zero_add]
  have hj : j = K := by rw [← h1, h, h2]
  subst hj; exact ⟨rfl, by omega⟩

theorem kcap_lt {K nK Cap e : ℕ} (hK : K < nK) (he : e < Cap) : K * Cap + e < nK * Cap := by
  have : (K + 1) * Cap ≤ nK * Cap := Nat.mul_le_mul_right _ hK
  nlinarith

/-- **Layout lemma**: one array step represents one abstract step. -/
theorem rep_step {Cap nK : ℕ} {Pc L : List ℕ} {c : MC} (H : Rep Cap nK Pc L c)
    (hk : pf Pc c.q 0 = 1 ∨ pf Pc c.q 0 = 2 ∨ pf Pc c.q 0 = 3 → pf Pc c.q 1 < nK)
    (hcap : pf Pc c.q 0 = 1 → (c.S (pf Pc c.q 1)).length < Cap) :
    Rep Cap nK Pc (stepL L) (mstep Pc c) := by
  obtain ⟨hL, h0, h1, h2, h3, h4, hS, hP⟩ := H
  set W := Pc.getD 1 0
  set T := pf Pc c.q 0 with hT
  set K := pf Pc c.q 1 with hK
  set A := pf Pc c.q 2
  set NX := pf Pc c.q 3
  -- evaluations
  have eq_fld : ∀ (f : NE) (i : ℕ), (fld f).ev i L = pf Pc c.q (f.ev i L) := by
    intro f i
    simp only [fld, pbE, nKE, capE, qE, wE, gt, ev_get, ev_add, ev_mul, ev_c, h0, h2, h1, h3]
    rw [show 5 + (nK + nK * Cap) + (6 + (c.q * W + f.ev i L)) =
      5 + nK + nK * Cap + (6 + c.q * W + f.ev i L) by ring, hP]
    rfl
  have eT : ∀ i, tagE.ev i L = T := fun i => by simp only [tagE, eq_fld, ev_c]; rfl
  have eK : ∀ i, kE.ev i L = K := fun i => by simp only [kE, eq_fld, ev_c]; rfl
  have eA : ∀ i, aE.ev i L = A := fun i => by simp only [aE, eq_fld, ev_c]; rfl
  have eNX : ∀ i, nxE.ev i L = NX := fun i => by simp only [nxE, eq_fld, ev_c]; rfl
  have eLen : ∀ i, lenE.ev i L = L.getD (5 + K) 0 := fun i => by
    simp only [lenE, ev_get, ev_add, ev_c, eK]
  have eBase : ∀ i, (baseE kE).ev i L = 5 + nK + K * Cap := fun i => by
    simp only [baseE, ev_add, ev_mul, ev_c, eK, nKE, capE, gt, ev_get, h1, h2]; ring
  have eO : K < nK → ∀ i, oE.ev i L = oc (c.S K).head? := by
    intro hKn i
    obtain ⟨l1, _, l3⟩ := hS K hKn
    simp only [oE, ev_ite, ev_add, ev_c, eLen, l1]
    split
    · next h => rw [List.length_eq_zero_iff.1 h]; rfl
    · next h =>
      simp only [topE, ev_get, ev_add, ev_sub, ev_c, eBase, eLen, l1]
      rw [show 5 + nK + K * Cap + ((c.S K).length - 1) = 5 + nK + K * Cap + ((c.S K).length - 1)
        from rfl, l3 _ (by omega)]
      rcases hs : c.S K with _ | ⟨b, r⟩
      · simp [hs] at h
      · simp [oc]
  have eQ : ∀ i, newQ.ev i L = (mstep Pc c).q := by
    intro i; rw [newQ_ev, eT, eNX]
    by_cases t1 : T = 1
    · rw [if_pos t1, mstep_push t1]
    by_cases t4 : T = 4
    · rw [if_neg t1, if_pos t4, mstep_nop t4]
    rw [if_neg t1, if_neg t4]
    by_cases t2 : T = 2
    · rw [if_pos (Or.inl t2), mstep_pop t2]
      simp only [tnE, eq_fld, ev_add, ev_c, eO (hk (by omega)) i]; rfl
    by_cases t3 : T = 3
    · rw [if_pos (Or.inr t3), mstep_peek t3]
      simp only [tnE, eq_fld, ev_add, ev_c, eO (hk (by omega)) i]; rfl
    · rw [if_neg (by omega), mstep_other t1 t2 t3 t4]
      simp only [qE, gt, ev_get, ev_c, h0]
  have hlen' : (stepL L).length = L.length := by rw [stepL_len, h4]
  have gD : ∀ i, (stepL L).getD i 0 = if i < L.length then stepE.ev i L else 0 := by
    intro i; rw [stepL_getD, h4]
  -- generic copy
  have copy : ∀ i, i ≠ 0 → (i = 5 + K → T ≠ 1 ∧ T ≠ 2) → (T = 1 → i ≠ 5 + nK + K * Cap +
      L.getD (5 + K) 0) → stepE.ev i L = L.getD i 0 := by
    intro i a1 a2 a3
    rw [stepE_ev, if_neg a1]
    by_cases e5 : i = 5 + kE.ev i L
    · rw [if_pos e5]
      rw [eK] at e5
      obtain ⟨n1, n2⟩ := a2 e5
      rw [newLen_ev, eT, if_neg n1, if_neg n2, eLen, e5]
    · rw [if_neg e5, if_neg]
      rintro ⟨t, e⟩
      rw [eT] at t; rw [eBase, eLen] at e
      exact a3 t e
  have WPlt : T = 1 → 5 + nK + K * Cap + L.getD (5 + K) 0 < 5 + nK + nK * Cap := by
    intro t
    have hKn := hk (Or.inl t)
    obtain ⟨l1, _, _⟩ := hS K hKn
    have := hcap t
    rw [l1]
    have := kcap_lt hKn this
    omega
  refine ⟨by rw [hlen']; exact hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gD, if_pos (by omega), stepE_ev, if_pos rfl, eQ]
  · rw [gD, if_pos (by omega), copy 1 (by omega) (by omega) (fun _ => by omega), h1]
  · rw [gD, if_pos (by omega), copy 2 (by omega) (by omega) (fun _ => by omega), h2]
  · rw [gD, if_pos (by omega), copy 3 (by omega) (by omega) (fun _ => by omega), h3]
  · rw [gD, if_pos (by omega), copy 4 (by omega) (by omega) (fun _ => by omega), h4, hlen']
  · intro j hj
    obtain ⟨l1, l2, l3⟩ := hS j hj
    have hjc : j * Cap + 0 < nK * Cap ∨ Cap = 0 := by
      rcases Nat.eq_zero_or_pos Cap with h | h
      · exact Or.inr h
      · exact Or.inl (kcap_lt hj h)
    have pos_lt : ∀ d, d < Cap → 5 + nK + j * Cap + d < L.length := by
      intro d hd
      have := kcap_lt hj hd
      omega
    -- the new stack j
    by_cases hjK : j = K ∧ (T = 1 ∨ T = 2)
    · obtain ⟨hjk, ht⟩ := hjK
      subst hjk
      have hKn := hk (by omega)
      rcases ht with t | t
      · -- push
        have hc := hcap t
        have ms : (mstep Pc c).S K = A :: c.S K := by
          rw [mstep_push t]; exact Function.update_self _ _ _
        rw [ms]
        refine ⟨?_, by simp; omega, ?_⟩
        · rw [gD, if_pos (by omega), stepE_ev, if_neg (by omega), if_pos (by rw [eK])]
          rw [newLen_ev, eT, if_pos t, eLen, l1]; simp
        · intro d hd
          simp only [List.length_cons] at hd
          rw [gD, if_pos (pos_lt d (by omega))]
          by_cases hdl : d = (c.S K).length
          · rw [stepE_ev, if_neg (by omega), if_neg (by rw [eK]; omega), if_pos ⟨by rw [eT]; exact t,
              by rw [eBase, eLen, l1, hdl]⟩, eA]
            simp [hdl]
          · rw [copy _ (by omega) (fun e => by omega) (fun _ e => by
              rw [l1] at e; exact hdl (by omega)), l3 d (by omega)]
            simp only [List.length_cons]
            rw [show (c.S K).length + 1 - 1 - d = ((c.S K).length - 1 - d) + 1 by omega]
            simp
      · -- pop
        have t1 : T ≠ 1 := by omega
        have ms : (mstep Pc c).S K = (c.S K).tail := by
          rw [mstep_pop t]; exact Function.update_self _ _ _
        rw [ms]
        refine ⟨?_, by simp; omega, ?_⟩
        · rw [gD, if_pos (by omega), stepE_ev, if_neg (by omega), if_pos (by rw [eK])]
          rw [newLen_ev, eT, if_neg t1, if_pos t, eLen, l1]; simp
        · intro d hd
          simp only [List.length_tail] at hd
          rw [gD, if_pos (pos_lt d (by omega)),
            copy _ (by omega) (fun e => by omega) (fun e => absurd e t1), l3 d (by omega)]
          rcases hs : c.S K with _ | ⟨b, r⟩
          · simp [hs] at hd
          · simp only [hs, List.length_cons, List.tail_cons] at hd ⊢
            rw [show r.length + 1 - 1 - d = (r.length - 1 - d) + 1 by omega]
            simp
    · have ms : (mstep Pc c).S j = c.S j := by
        by_cases t1 : T = 1
        · rw [mstep_push t1]; exact Function.update_of_ne (fun e => hjK ⟨e, Or.inl t1⟩) _ _
        by_cases t2 : T = 2
        · rw [mstep_pop t2]; exact Function.update_of_ne (fun e => hjK ⟨e, Or.inr t2⟩) _ _
        by_cases t3 : T = 3
        · rw [mstep_peek t3]
        by_cases t4 : T = 4
        · rw [mstep_nop t4]
        rw [mstep_other t1 t2 t3 t4]
      rw [ms]
      refine ⟨?_, l2, ?_⟩
      · rw [gD, if_pos (by have := pos_lt 0; omega), copy _ (by omega)
          (fun e => by refine ⟨fun t => hjK ⟨by omega, Or.inl t⟩, fun t => hjK ⟨by omega, Or.inr t⟩⟩)
          (fun t e => by have := WPlt t; have := hk (Or.inl t); omega), l1]
      · intro d hd
        rw [gD, if_pos (pos_lt d (by omega)), copy _ (by omega)
          (fun e => by
            constructor
            · intro t; have := hk (Or.inl t); omega
            · intro t; have := hk (Or.inr (Or.inl t)); omega)
          (fun t e => by
            have hKn := hk (Or.inl t)
            obtain ⟨m1, _, _⟩ := hS K hKn
            have hc := hcap t
            rw [m1] at e
            have := cell_inj (show d < Cap by omega) hc (by omega : j * Cap + d = K * Cap + (c.S K).length)
            exact hjK ⟨this.1, Or.inl t⟩), l3 d hd]
  · intro m
    rw [gD]
    split
    · next hm =>
      rw [copy _ (by omega)
        (fun e => by
          constructor
          · intro t; have := hk (Or.inl t); omega
          · intro t; have := hk (Or.inr (Or.inl t)); omega)
        (fun t e => by have := WPlt t; omega), hP]
    · next hm =>
      have := hP m
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at this
      simpa using this

theorem mstep_len (Pc : List ℕ) (c : MC) (k : ℕ) :
    ((mstep Pc c).S k).length ≤ (c.S k).length + 1 := by
  by_cases t1 : pf Pc c.q 0 = 1
  · rw [mstep_push t1]
    by_cases e : k = pf Pc c.q 1
    · subst e; simp
    · simp [Function.update_of_ne e]
  by_cases t2 : pf Pc c.q 0 = 2
  · rw [mstep_pop t2]
    by_cases e : k = pf Pc c.q 1
    · subst e; simp; omega
    · simp [Function.update_of_ne e]
  by_cases t3 : pf Pc c.q 0 = 3
  · rw [mstep_peek t3]; dsimp only; omega
  by_cases t4 : pf Pc c.q 0 = 4
  · rw [mstep_nop t4]; dsimp only; omega
  rw [mstep_other t1 t2 t3 t4]; omega

theorem rep_tag {Cap nK : ℕ} {Pc L : List ℕ} {c : MC} (H : Rep Cap nK Pc L c) :
    tagOf L = pf Pc c.q 0 := by
  obtain ⟨_, h0, h1, h2, h3, _, _, hP⟩ := H
  simp only [tagOf, tagE, fld, pbE, nKE, capE, qE, wE, gt, ev_get, ev_add, ev_mul, ev_c, h0, h2, h1,
    h3]
  rw [show 5 + (nK + nK * Cap) + (6 + (c.q * Pc.getD 1 0 + 0)) =
    5 + nK + nK * Cap + (6 + c.q * Pc.getD 1 0 + 0) by ring, hP]
  rfl

/-- **Iterated layout lemma.** -/
theorem rep_iter {Cap nK : ℕ} {Pc : List ℕ}
    (hk : ∀ q, pf Pc q 0 = 1 ∨ pf Pc q 0 = 2 ∨ pf Pc q 0 = 3 → pf Pc q 1 < nK) :
    ∀ (t : ℕ) (L : List ℕ) (c : MC), Rep Cap nK Pc L c → (∀ k < nK, (c.S k).length + t ≤ Cap) →
      Rep Cap nK Pc (stepL^[t] L) ((mstep Pc)^[t] c) := by
  intro t
  induction t with
  | zero => intro L c H _; exact H
  | succ t ih =>
    intro L c H hc
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih _ _ (rep_step H (hk c.q) (fun t1 => ?_)) (fun k hk' => ?_)
    · have := hc _ (hk c.q (Or.inl t1)); omega
    · have := mstep_len Pc c k; have := hc k hk'; omega

end Flat

end PvnpReal
