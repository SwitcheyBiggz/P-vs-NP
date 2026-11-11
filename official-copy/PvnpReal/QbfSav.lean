/-
  PvnpReal.QbfSav — the Savitch-style reachability QBF, generically.

  Given a CNF `B` describing a relation `R` between two `n`-bit blocks, the prenex QBF
  `∃ g ∃ M_k ∀ z_k ∃ C_k D_k … ∃ M_1 ∀ z_1 ∃ C_1 D_1. Top(g) ∧ ⋀ Sel_j ∧ B(C_1, D_1)`
  (with the one-bit selector trick: `z = 0 → (C,D) = (P,M)`, `z = 1 → (C,D) = (M,Q)`)
  is true iff there are blocks `A, B` with `Top` and an `R`-chain of length `2^k` from `A` to `B`
  (`sav_correct`, `sav_chain`). The matrix is a plain conjunction of CNFs: no Tseitin step is
  needed, because each selector is itself a CNF.
-/
import PvnpReal.Qbf

set_option linter.unusedSimpArgs false

namespace PvnpReal

/-! ### Reading blocks -/

/-- The `n` bits of `a` starting at position `p`. -/
def rdF (a : ℕ → Bool) (p n : ℕ) : List Bool := (List.range n).map (fun i => a (p + i))

@[simp] theorem rdF_length (a : ℕ → Bool) (p n : ℕ) : (rdF a p n).length = n := by simp [rdF]

theorem rdF_congr {a b : ℕ → Bool} {p n : ℕ} (h : ∀ i < n, a (p + i) = b (p + i)) :
    rdF a p n = rdF b p n := by
  unfold rdF; apply List.map_congr_left; intro i hi; exact h i (List.mem_range.1 hi)

theorem rdF_eq_iff (a : ℕ → Bool) (p q n : ℕ) :
    rdF a p n = rdF a q n ↔ ∀ i < n, a (p + i) = a (q + i) := by
  unfold rdF; rw [List.map_inj_left]; simp

theorem asg_append_left (w u : List Bool) {v : ℕ} (h : v < w.length) :
    asg (w ++ u) v = asg w v := by
  simp [asg, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem asg_append_right (w u : List Bool) (v : ℕ) :
    asg (w ++ u) (w.length + v) = asg u v := by
  simp [asg, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem rdF_append_left (w u : List Bool) {p n : ℕ} (h : p + n ≤ w.length) :
    rdF (asg (w ++ u)) p n = rdF (asg w) p n :=
  rdF_congr (fun i hi => asg_append_left w u (by omega))

theorem rdF_append_right (w u : List Bool) (q n : ℕ) :
    rdF (asg (w ++ u)) (w.length + q) n = rdF (asg u) q n := by
  unfold rdF; apply List.map_congr_left; intro i _
  rw [Nat.add_assoc, asg_append_right]

theorem rdF_append_right' (w u : List Bool) {q q' : ℕ} (n : ℕ) (h : q = w.length + q') :
    rdF (asg (w ++ u)) q n = rdF (asg u) q' n := by
  rw [h, rdF_append_right]

theorem rdF_prefix (u r : List Bool) : rdF (asg (u ++ r)) 0 u.length = u := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [rdF, List.getElem_map, List.getElem_range, Nat.zero_add]
  simp only [rdF_length] at h1
  rw [asg_append_left _ _ h1]
  simp [asg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-! ### Evaluation only sees the variables that occur -/

theorem evalCNF_app (φ ψ : CNF) (a : ℕ → Bool) :
    evalCNF (φ ++ ψ) a = (evalCNF φ a && evalCNF ψ a) := by
  simp [evalCNF, List.all_append]

theorem evalCNF_flatMap {α : Type*} (l : List α) (f : α → CNF) (a : ℕ → Bool) :
    evalCNF (l.flatMap f) a = true ↔ ∀ x ∈ l, evalCNF (f x) a = true := by
  simp [evalCNF, List.all_flatMap]

/-! ### Quantifier blocks -/

theorem qval_exists (φ : CNF) : ∀ (k : ℕ) (qs w : List Bool),
    qval φ (List.replicate k false ++ qs) w = true ↔
      ∃ u : List Bool, u.length = k ∧ qval φ qs (w ++ u) = true := by
  intro k
  induction k with
  | zero => intro qs w; simp
  | succ k ih =>
    intro qs w
    simp only [List.replicate_succ, List.cons_append, qval, Bool.false_eq_true, if_false,
      Bool.or_eq_true, ih]
    constructor
    · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩)
      · exact ⟨false :: u, by simp [hu], by simpa using h⟩
      · exact ⟨true :: u, by simp [hu], by simpa using h⟩
    · rintro ⟨u, hu, h⟩
      rcases u with _ | ⟨b, u⟩
      · simp at hu
      · simp only [List.length_cons, Nat.add_right_cancel_iff] at hu
        cases b
        · exact Or.inl ⟨u, hu, by simpa using h⟩
        · exact Or.inr ⟨u, hu, by simpa using h⟩

theorem qval_forall (φ : CNF) (qs w : List Bool) :
    qval φ (true :: qs) w = true ↔
      qval φ qs (w ++ [false]) = true ∧ qval φ qs (w ++ [true]) = true := by
  simp [qval]

/-- Clauses over already-assigned variables factor out of the quantifier prefix. -/
theorem qval_low (φ ψ : CNF) : ∀ (qs w : List Bool), (∀ cl ∈ φ, ∀ l ∈ cl, l.var < w.length) →
    qval (φ ++ ψ) qs w = (evalCNF φ (asg w) && qval ψ qs w) := by
  intro qs
  induction qs with
  | nil => intro w _; simp [qval, evalCNF_app]
  | cons q qs ih =>
    intro w hw
    have hb : ∀ b : Bool, ∀ cl ∈ φ, ∀ l ∈ cl, l.var < (w ++ [b]).length := fun b cl hcl l hl => by
      have := hw cl hcl l hl; simp; omega
    have e : ∀ b : Bool, evalCNF φ (asg (w ++ [b])) = evalCNF φ (asg w) := fun b =>
      evalCNF_congr _ _ _ (fun cl hcl l hl => asg_append_left _ _ (hw cl hcl l hl))
    simp only [qval]
    rw [ih _ (hb false), ih _ (hb true), e, e]
    cases q <;> cases evalCNF φ (asg w) <;> simp

/-! ### The selector -/

/-- Selector clauses for bit `i` of a level whose parent pair starts at `p`: `P = p`, `Q = p+n`,
`M = p+2n`, `z = p+3n`, `C = p+4n`, `D = p+5n`. -/
def selCls (n p i : ℕ) : CNF :=
  [[⟨p + 3 * n, false⟩, ⟨p + 4 * n + i, true⟩, ⟨p + i, false⟩],
   [⟨p + 3 * n, false⟩, ⟨p + 4 * n + i, false⟩, ⟨p + i, true⟩],
   [⟨p + 3 * n, false⟩, ⟨p + 5 * n + i, true⟩, ⟨p + 2 * n + i, false⟩],
   [⟨p + 3 * n, false⟩, ⟨p + 5 * n + i, false⟩, ⟨p + 2 * n + i, true⟩],
   [⟨p + 3 * n, true⟩, ⟨p + 4 * n + i, true⟩, ⟨p + 2 * n + i, false⟩],
   [⟨p + 3 * n, true⟩, ⟨p + 4 * n + i, false⟩, ⟨p + 2 * n + i, true⟩],
   [⟨p + 3 * n, true⟩, ⟨p + 5 * n + i, true⟩, ⟨p + n + i, false⟩],
   [⟨p + 3 * n, true⟩, ⟨p + 5 * n + i, false⟩, ⟨p + n + i, true⟩]]

def selCNF (n p : ℕ) : CNF := (List.range n).flatMap (selCls n p)

theorem selCls_iff (n p i : ℕ) (a : ℕ → Bool) :
    evalCNF (selCls n p i) a = true ↔
      (a (p + 3 * n) = false → a (p + 4 * n + i) = a (p + i) ∧ a (p + 5 * n + i) = a (p + 2 * n + i)) ∧
      (a (p + 3 * n) = true → a (p + 4 * n + i) = a (p + 2 * n + i) ∧ a (p + 5 * n + i) = a (p + n + i)) := by
  simp only [selCls, evalCNF, evalClause, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    evalLiteral_pos, evalLiteral_neg]
  cases a (p + 3 * n) <;> cases a (p + 4 * n + i) <;> cases a (p + i) <;>
    cases a (p + 5 * n + i) <;> cases a (p + 2 * n + i) <;> cases a (p + n + i) <;> simp

theorem selCNF_iff (n p : ℕ) (a : ℕ → Bool) :
    evalCNF (selCNF n p) a = true ↔
      (a (p + 3 * n) = false → rdF a (p + 4 * n) n = rdF a p n ∧ rdF a (p + 5 * n) n = rdF a (p + 2 * n) n) ∧
      (a (p + 3 * n) = true → rdF a (p + 4 * n) n = rdF a (p + 2 * n) n ∧
        rdF a (p + 5 * n) n = rdF a (p + n) n) := by
  rw [selCNF, evalCNF_flatMap]
  simp only [List.mem_range, selCls_iff, rdF_eq_iff]
  constructor
  · intro h
    exact ⟨fun hz => ⟨fun i hi => (h i hi).1 hz |>.1, fun i hi => (h i hi).1 hz |>.2⟩,
      fun hz => ⟨fun i hi => (h i hi).2 hz |>.1, fun i hi => (h i hi).2 hz |>.2⟩⟩
  · rintro ⟨h1, h2⟩ i hi
    refine ⟨fun hz => ⟨?_, ?_⟩, fun hz => ⟨?_, ?_⟩⟩
    · have := (h1 hz).1 i hi; rwa [Nat.add_assoc] at this ⊢
    · have := (h1 hz).2 i hi; rwa [Nat.add_assoc] at this ⊢
    · have := (h2 hz).1 i hi; rwa [Nat.add_assoc] at this ⊢
    · have := (h2 hz).2 i hi; rwa [Nat.add_assoc] at this ⊢

theorem selCNF_vars (n p : ℕ) : ∀ cl ∈ selCNF n p, ∀ l ∈ cl, l.var < p + 6 * n := by
  intro cl hcl l hl
  simp only [selCNF, List.mem_flatMap, List.mem_range] at hcl
  obtain ⟨i, hi, hcl⟩ := hcl
  simp only [selCls, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl | rfl <;> simp <;> omega

/-! ### Levels -/

/-- The relation "reachable in `2^j` `R`-steps through `n`-bit blocks". -/
def Sav (R : List Bool → List Bool → Prop) (n : ℕ) : ℕ → List Bool → List Bool → Prop
  | 0 => R
  | j + 1 => fun a b => ∃ c, c.length = n ∧ Sav R n j a c ∧ Sav R n j c b

/-- Quantifier block of one level: `∃ M (n)`, `∀ z`, `∃ pad (n-1)`, `∃ C D (2n)`. -/
def savBlk (n : ℕ) : List Bool :=
  List.replicate n false ++ true :: (List.replicate (n - 1) false ++ List.replicate (2 * n) false)

def lvlPre (n j : ℕ) : List Bool := (List.range j).flatMap (fun _ => savBlk n)

def lvlCNF (n p j : ℕ) : CNF := (List.range j).flatMap (fun i => selCNF n (p + 4 * n * i))

theorem lvlPre_succ (n j : ℕ) : lvlPre n (j + 1) = savBlk n ++ lvlPre n j := by
  simp [lvlPre, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem lvlCNF_succ (n p j : ℕ) : lvlCNF n p (j + 1) = selCNF n p ++ lvlCNF n (p + 4 * n) j := by
  simp only [lvlCNF, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.mul_zero,
    Nat.add_zero]
  congr 1
  apply List.flatMap_congr
  intro i _
  congr 1
  simp only [Nat.succ_eq_add_one]
  ring

theorem sav_inner (R : List Bool → List Bool → Prop) (n : ℕ) (hn : 1 ≤ n) (B : CNF) :
    ∀ (j p : ℕ) (w : List Bool), w.length = p + 2 * n →
      (∀ a, evalCNF B a = true ↔ R (rdF a (p + 4 * n * j) n) (rdF a (p + 4 * n * j + n) n)) →
      (qval (lvlCNF n p j ++ B) (lvlPre n j) w = true ↔
        Sav R n j (rdF (asg w) p n) (rdF (asg w) (p + n) n)) := by
  intro j
  induction j with
  | zero =>
    intro p w _ hB
    simp only [lvlCNF, lvlPre, List.range_zero, List.flatMap_nil, List.nil_append, qval, Sav]
    simpa using hB (asg w)
  | succ j ih =>
    intro p w hw hB
    have hB' : ∀ a, evalCNF B a = true ↔
        R (rdF a (p + 4 * n + 4 * n * j) n) (rdF a (p + 4 * n + 4 * n * j + n) n) := by
      intro a; rw [hB a]; ring_nf
    rw [lvlCNF_succ, lvlPre_succ, List.append_assoc, savBlk]
    simp only [List.append_assoc, List.cons_append]
    rw [qval_exists]
    simp only [qval_forall, ← List.append_assoc, List.append_assoc]
    -- the generic shape after `∃ M ∀ z`
    have key : ∀ (m : List Bool), m.length = n → ∀ b : Bool,
        (qval (selCNF n p ++ (lvlCNF n (p + 4 * n) j ++ B))
          (List.replicate (n - 1) false ++ (List.replicate (2 * n) false ++ lvlPre n j))
          (w ++ (m ++ [b])) = true ↔
        ∃ c d : List Bool, c.length = n ∧ d.length = n ∧
          (b = false → c = rdF (asg w) p n ∧ d = m) ∧ (b = true → c = m ∧ d = rdF (asg w) (p + n) n) ∧
          Sav R n j c d) := by
      intro m hm b
      rw [qval_exists]
      constructor
      · rintro ⟨u, hu, h⟩
        rw [qval_exists] at h
        obtain ⟨cd, hcd, h⟩ := h
        set W := w ++ (m ++ [b]) ++ u ++ cd with hW
        have hWl : W.length = p + 4 * n + 2 * n := by
          simp [hW, hw, hm, hu, hcd]; omega
        rw [qval_low _ _ _ _ (fun cl hcl l hl => by
          have := selCNF_vars n p cl hcl l hl; omega)] at h
        rw [Bool.and_eq_true, ih (p + 4 * n) W hWl hB', selCNF_iff] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        refine ⟨rdF (asg W) (p + 4 * n) n, rdF (asg W) (p + 4 * n + n) n, by simp, by simp, ?_, ?_, h3⟩
        all_goals
          have eW : W = w ++ (m ++ ([b] ++ (u ++ cd))) := by simp [hW]
          have rP : rdF (asg W) p n = rdF (asg w) p n := by
            rw [eW, rdF_append_left _ _ (by omega)]
          have rQ : rdF (asg W) (p + n) n = rdF (asg w) (p + n) n := by
            rw [eW, rdF_append_left _ _ (by omega)]
          have rM : rdF (asg W) (p + 2 * n) n = m := by
            rw [eW, show p + 2 * n = w.length + 0 by omega, rdF_append_right, ← hm, rdF_prefix]
          have rz : asg W (p + 3 * n) = b := by
            rw [eW, show p + 3 * n = w.length + (m.length + 0) by omega, asg_append_right,
              asg_append_right]
            rfl
          have e5 : p + 4 * n + n = p + 5 * n := by ring
        · intro hb; subst hb
          obtain ⟨c1, c2⟩ := h1 rz
          rw [e5, c1, c2, rP, rM]; exact ⟨rfl, rfl⟩
        · intro hb; subst hb
          obtain ⟨c1, c2⟩ := h2 rz
          rw [e5, c1, c2, rQ, rM]; exact ⟨rfl, rfl⟩
      · rintro ⟨c, d, hc, hd, h1, h2, h3⟩
        refine ⟨List.replicate (n - 1) false, by simp, ?_⟩
        rw [qval_exists]
        refine ⟨c ++ d, by simp [hc, hd]; ring, ?_⟩
        set W := w ++ (m ++ [b]) ++ List.replicate (n - 1) false ++ (c ++ d) with hW
        have hWl : W.length = p + 4 * n + 2 * n := by
          simp [hW, hw, hm, hc, hd]; omega
        have eW : W = w ++ (m ++ ([b] ++ (List.replicate (n - 1) false ++ (c ++ d)))) := by simp [hW]
        have rP : rdF (asg W) p n = rdF (asg w) p n := by
          rw [eW, rdF_append_left _ _ (by omega)]
        have rQ : rdF (asg W) (p + n) n = rdF (asg w) (p + n) n := by
          rw [eW, rdF_append_left _ _ (by omega)]
        have rM : rdF (asg W) (p + 2 * n) n = m := by
          rw [eW, show p + 2 * n = w.length + 0 by omega, rdF_append_right, ← hm, rdF_prefix]
        have rz : asg W (p + 3 * n) = b := by
          rw [eW, show p + 3 * n = w.length + (m.length + 0) by omega, asg_append_right,
            asg_append_right]
          rfl
        have rC : rdF (asg W) (p + 4 * n) n = c := by
          rw [eW, rdF_append_right' w _ (q' := 2 * n) n (by omega),
            rdF_append_right' m _ (q' := n) n (by omega),
            rdF_append_right' [b] _ (q' := n - 1) n (by simp; omega),
            rdF_append_right' (List.replicate (n - 1) false) _ (q' := 0) n (by simp), ← hc,
            rdF_prefix]
        have rD : rdF (asg W) (p + 4 * n + n) n = d := by
          rw [eW, rdF_append_right' w _ (q' := 3 * n) n (by omega),
            rdF_append_right' m _ (q' := 2 * n) n (by omega),
            rdF_append_right' [b] _ (q' := 2 * n - 1) n (by simp; omega),
            rdF_append_right' (List.replicate (n - 1) false) _ (q' := n) n (by simp; omega),
            rdF_append_right' c _ (q' := 0) n (by omega)]
          simpa [hd] using rdF_prefix d []
        rw [qval_low _ _ _ _ (fun cl hcl l hl => by
          have := selCNF_vars n p cl hcl l hl; omega)]
        rw [Bool.and_eq_true, ih (p + 4 * n) W hWl hB', selCNF_iff, rC, rD,
          show p + 5 * n = p + 4 * n + n by ring, rD, rP, rQ, rM, rz]
        refine ⟨⟨fun hb => ?_, fun hb => ?_⟩, h3⟩
        · obtain ⟨e1, e2⟩ := h1 hb; exact ⟨e1, e2⟩
        · obtain ⟨e1, e2⟩ := h2 hb; exact ⟨e1, e2⟩
    constructor
    · rintro ⟨m, hm, hf, ht⟩
      obtain ⟨c, d, -, -, h1, -, h3⟩ := (key m hm false).1 hf
      obtain ⟨c', d', -, -, -, h2', h3'⟩ := (key m hm true).1 ht
      obtain ⟨e1, e2⟩ := h1 rfl
      obtain ⟨e3, e4⟩ := h2' rfl
      rw [e1, e2] at h3; rw [e3, e4] at h3'
      exact ⟨m, hm, h3, h3'⟩
    · rintro ⟨m, hm, h1, h2⟩
      refine ⟨m, hm, ?_, ?_⟩
      · exact (key m hm false).2 ⟨_, m, by simp, hm, fun _ => ⟨rfl, rfl⟩, by simp, h1⟩
      · exact (key m hm true).2 ⟨m, _, hm, by simp, by simp, fun _ => ⟨rfl, rfl⟩, h2⟩

/-- **Correctness of the Savitch QBF.** -/
theorem sav_correct (R : List Bool → List Bool → Prop) (n r0 k : ℕ) (hn : 1 ≤ n) (Top B : CNF)
    (hTop : ∀ cl ∈ Top, ∀ l ∈ cl, l.var < r0 + 2 * n)
    (hB : ∀ a, evalCNF B a = true ↔ R (rdF a (r0 + 4 * n * k) n) (rdF a (r0 + 4 * n * k + n) n)) :
    qval (Top ++ (lvlCNF n r0 k ++ B)) (List.replicate (r0 + 2 * n) false ++ lvlPre n k) [] = true ↔
      ∃ g : List Bool, g.length = r0 + 2 * n ∧ evalCNF Top (asg g) = true ∧
        Sav R n k (rdF (asg g) r0 n) (rdF (asg g) (r0 + n) n) := by
  rw [qval_exists]
  simp only [List.nil_append]
  constructor
  · rintro ⟨g, hg, h⟩
    rw [qval_low _ _ _ _ (fun cl hcl l hl => by rw [hg]; exact hTop cl hcl l hl), Bool.and_eq_true,
      sav_inner R n hn B k r0 g hg hB] at h
    exact ⟨g, hg, h⟩
  · rintro ⟨g, hg, h1, h2⟩
    refine ⟨g, hg, ?_⟩
    rw [qval_low _ _ _ _ (fun cl hcl l hl => by rw [hg]; exact hTop cl hcl l hl), Bool.and_eq_true,
      sav_inner R n hn B k r0 g hg hB]
    exact ⟨h1, h2⟩

/-! ### Chains -/

/-- An `R`-chain of `N` steps through `n`-bit blocks. -/
def Chain (R : List Bool → List Bool → Prop) (n N : ℕ) (a b : List Bool) : Prop :=
  ∃ u : ℕ → List Bool, u 0 = a ∧ u N = b ∧ (∀ i, (u i).length = n) ∧ ∀ i < N, R (u i) (u (i + 1))

theorem chain_one (R : List Bool → List Bool → Prop) (n : ℕ) (a b : List Bool)
    (ha : a.length = n) (hb : b.length = n) : Chain R n 1 a b ↔ R a b := by
  constructor
  · rintro ⟨u, h0, h1, -, hR⟩
    have := hR 0 (by omega); rwa [h0, h1] at this
  · intro h
    refine ⟨fun i => if i = 0 then a else b, by simp, by simp, fun i => ?_, fun i hi => ?_⟩
    · by_cases hi : i = 0 <;> simp [hi, ha, hb]
    · obtain rfl : i = 0 := by omega
      simpa using h

theorem chain_double (R : List Bool → List Bool → Prop) (n N : ℕ) (a b : List Bool) :
    Chain R n (N + N) a b ↔ ∃ c, c.length = n ∧ Chain R n N a c ∧ Chain R n N c b := by
  constructor
  · rintro ⟨u, h0, h1, hl, hR⟩
    refine ⟨u N, hl N, ⟨u, h0, rfl, hl, fun i hi => hR i (by omega)⟩,
      ⟨fun i => u (N + i), by simp, h1, fun i => hl _, fun i hi => ?_⟩⟩
    have := hR (N + i) (by omega)
    rwa [Nat.add_assoc] at this
  · rintro ⟨c, hc, ⟨u, h0, h1, hl, hR⟩, ⟨v, g0, g1, gl, gR⟩⟩
    refine ⟨fun i => if i ≤ N then u i else v (i - N), by simp [h0], ?_, fun i => ?_,
      fun i hi => ?_⟩
    · by_cases hN : N + N ≤ N
      · obtain rfl : N = 0 := by omega
        simp only [Nat.add_zero, le_refl, if_true]
        rw [h0] at h1; rw [g0] at g1; rw [h0, h1, ← g1]
      · simp only [hN, if_false, Nat.add_sub_cancel]; exact g1
    · by_cases h : i ≤ N <;> simp [h, hl, gl]
    · by_cases h1' : i + 1 ≤ N
      · simp only [h1', show i ≤ N by omega, if_true]; exact hR i (by omega)
      · by_cases h2 : i ≤ N
        · have hiN : i = N := by omega
          rw [hiN]; dsimp only
          rw [if_pos le_rfl, if_neg (by omega), show N + 1 - N = 0 + 1 by omega, h1, ← g0]
          exact gR 0 (by omega)
        · simp only [h2, h1', if_false, show i + 1 - N = i - N + 1 by omega]
          exact gR _ (by omega)

theorem sav_chain (R : List Bool → List Bool → Prop) (n : ℕ) :
    ∀ (j : ℕ) (a b : List Bool), a.length = n → b.length = n →
      (Sav R n j a b ↔ Chain R n (2 ^ j) a b) := by
  intro j
  induction j with
  | zero => intro a b ha hb; simp only [Sav, pow_zero]; exact (chain_one R n a b ha hb).symm
  | succ j ih =>
    intro a b ha hb
    rw [pow_succ, Nat.mul_two, chain_double]
    simp only [Sav]
    constructor
    · rintro ⟨c, hc, h1, h2⟩
      exact ⟨c, hc, (ih a c ha hc).1 h1, (ih c b hc hb).1 h2⟩
    · rintro ⟨c, hc, h1, h2⟩
      exact ⟨c, hc, (ih a c ha hc).2 h1, (ih c b hc hb).2 h2⟩

end PvnpReal
