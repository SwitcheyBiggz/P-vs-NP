/-
  PvnpReal.Tseitin — Boolean circuits, CIRCUIT-SAT, and the Tseitin translation to CNF,
  with a full correctness proof:

      SAT (tseitin C) ↔ CircuitSAT C      (for well-formed circuits)

  This is the last step of the circuit-based route to Cook–Levin
  (bounded TM run → circuit → CNF), as used e.g. in Lean's `complexitylib`.
  Only correctness is proved here; the polynomial running time of a *machine* computing
  `tseitin` is not.
-/
import PvnpReal.Sat

namespace PvnpReal

/-- A gate reads earlier wires (by index). -/
inductive Gate
  | and (i j : ℕ)
  | or (i j : ℕ)
  | not (i : ℕ)

def Gate.eval : Gate → (ℕ → Bool) → Bool
  | .and i j, v => v i && v j
  | .or i j, v => v i || v j
  | .not i, v => !v i

/-- Gate `g` at wire `w` only reads wires `< w`. -/
def Gate.WF : Gate → ℕ → Prop
  | .and i j, w => i < w ∧ j < w
  | .or i j, w => i < w ∧ j < w
  | .not i, w => i < w

theorem Gate.eval_congr (g : Gate) (w : ℕ) (hg : g.WF w) (v v' : ℕ → Bool)
    (h : ∀ k < w, v k = v' k) : g.eval v = g.eval v' := by
  cases g with
  | and i j => simp only [Gate.WF] at hg; simp [Gate.eval, h i hg.1, h j hg.2]
  | or i j => simp only [Gate.WF] at hg; simp [Gate.eval, h i hg.1, h j hg.2]
  | not i => simp only [Gate.WF] at hg; simp [Gate.eval, h i hg]

/-- A circuit: wires `0 … nIn-1` are inputs, wire `nIn + p` is the output of `gates[p]`.
The output is the last wire. -/
structure Circuit where
  nIn : ℕ
  gates : List Gate

def Circuit.size (C : Circuit) : ℕ := C.nIn + C.gates.length
def Circuit.out (C : Circuit) : ℕ := C.size - 1

def Circuit.WF (C : Circuit) : Prop :=
  0 < C.size ∧ ∀ p (h : p < C.gates.length), (C.gates[p]).WF (C.nIn + p)

/-- Evaluate gates one after another, appending each result. -/
def goWires : List Bool → List Gate → List Bool
  | ws, [] => ws
  | ws, g :: gs => goWires (ws ++ [g.eval (fun i => ws.getD i false)]) gs

/-- Value of every wire on input `inp` (missing input bits read as `false`). -/
def Circuit.value (C : Circuit) (inp : List Bool) : ℕ → Bool := fun i =>
  (goWires ((List.range C.nIn).map (fun k => inp.getD k false)) C.gates).getD i false

/-- CIRCUIT-SAT: some input makes the output wire true. -/
def CircuitSAT (C : Circuit) : Prop :=
  ∃ inp : List Bool, inp.length = C.nIn ∧ C.value inp C.out = true

/-- A wire valuation consistent with the circuit on input `inp`. -/
def Consistent (C : Circuit) (inp : List Bool) (v : ℕ → Bool) : Prop :=
  (∀ i < C.nIn, v i = inp.getD i false) ∧
    ∀ p (h : p < C.gates.length), v (C.nIn + p) = (C.gates[p]).eval v

/-! ### Uniqueness and existence of the consistent valuation -/

theorem consistent_unique (C : Circuit) (hC : C.WF) (inp : List Bool) (v v' : ℕ → Bool)
    (hv : Consistent C inp v) (hv' : Consistent C inp v') : ∀ i < C.size, v i = v' i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h : i < C.nIn
    · rw [hv.1 i h, hv'.1 i h]
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
      have hp : p < C.gates.length := by simp [Circuit.size] at hi; omega
      rw [hv.2 p hp, hv'.2 p hp]
      apply Gate.eval_congr _ _ (hC.2 p hp)
      intro k hk
      exact ih k hk (by simp [Circuit.size] at hi ⊢; omega)

theorem goWires_length (ws : List Bool) (gs : List Gate) :
    (goWires ws gs).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp [goWires]
  | cons g gs ih => simp [goWires, ih]; omega

theorem goWires_prefix (ws : List Bool) (gs : List Gate) (i : ℕ) (hi : i < ws.length) :
    (goWires ws gs).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [goWires]
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem goWires_spec (ws : List Bool) (gs : List Gate)
    (hwf : ∀ p (h : p < gs.length), (gs[p]).WF (ws.length + p)) :
    ∀ p (h : p < gs.length), (goWires ws gs).getD (ws.length + p) false =
      (gs[p]).eval (fun k => (goWires ws gs).getD k false) := by
  induction gs generalizing ws with
  | nil => intro p h; simp at h
  | cons g gs ih =>
    intro p hp
    have hwf' : ∀ p (h : p < gs.length),
        (gs[p]).WF ((ws ++ [g.eval (fun i => ws.getD i false)]).length + p) := by
      intro p h
      have := hwf (p + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 p] using this
    cases p with
    | zero =>
      have hwf0 : g.WF ws.length := hwf 0 (Nat.succ_pos _)
      have key : (goWires (ws ++ [g.eval (fun i => ws.getD i false)]) gs).getD ws.length false =
          g.eval (fun i => ws.getD i false) := by
        rw [goWires_prefix _ _ _ (by simp)]; simp [List.getD_eq_getElem?_getD]
      have agree : ∀ k < ws.length,
          (goWires (ws ++ [g.eval (fun i => ws.getD i false)]) gs).getD k false = ws.getD k false :=
        fun k hk => by
          rw [goWires_prefix _ _ _ (by simp; omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      show (goWires (ws ++ [g.eval (fun i => ws.getD i false)]) gs).getD (ws.length + 0) false =
        g.eval (fun k => (goWires (ws ++ [g.eval (fun i => ws.getD i false)]) gs).getD k false)
      rw [Nat.add_zero, key]
      apply Gate.eval_congr _ _ hwf0
      intro k hk
      exact (agree k hk).symm
    | succ p =>
      simp only [goWires, List.getElem_cons_succ]
      have := ih _ hwf' p (by simpa using hp)
      simpa [Nat.add_assoc, Nat.add_comm 1 p] using this

theorem value_consistent (C : Circuit) (hC : C.WF) (inp : List Bool) :
    Consistent C inp (C.value inp) := by
  constructor
  · intro i hi
    simp only [Circuit.value]
    rw [goWires_prefix _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · intro p hp
    have := goWires_spec ((List.range C.nIn).map (fun k => inp.getD k false)) C.gates
      (by intro p h; simpa using hC.2 p h) p hp
    rw [List.length_map, List.length_range] at this
    exact this

/-! ### The Tseitin CNF -/

def posL (v : ℕ) : Literal := ⟨v, false⟩
def negL (v : ℕ) : Literal := ⟨v, true⟩

/-- Clauses forcing wire `w` to equal gate `g`. -/
def gateCNF (w : ℕ) : Gate → CNF
  | .and i j => [[negL w, posL i], [negL w, posL j], [posL w, negL i, negL j]]
  | .or i j => [[negL w, posL i, posL j], [posL w, negL i], [posL w, negL j]]
  | .not i => [[posL w, posL i], [negL w, negL i]]

def gatesCNF : ℕ → List Gate → CNF
  | _, [] => []
  | w, g :: gs => gateCNF w g ++ gatesCNF (w + 1) gs

/-- The Tseitin formula: all gate constraints, plus "the output wire is true". -/
def tseitin (C : Circuit) : CNF := gatesCNF C.nIn C.gates ++ [[posL C.out]]

theorem evalCNF_append (φ ψ : CNF) (a : ℕ → Bool) :
    evalCNF (φ ++ ψ) a = (evalCNF φ a && evalCNF ψ a) := by
  simp [evalCNF, List.all_append]

theorem gateCNF_iff (w : ℕ) (g : Gate) (a : ℕ → Bool) :
    evalCNF (gateCNF w g) a = true ↔ a w = g.eval a := by
  cases g with
  | and i j =>
    cases hw : a w <;> cases hi : a i <;> cases hj : a j <;>
      simp [gateCNF, evalCNF, evalClause, evalLiteral, posL, negL, Gate.eval, hw, hi, hj]
  | or i j =>
    cases hw : a w <;> cases hi : a i <;> cases hj : a j <;>
      simp [gateCNF, evalCNF, evalClause, evalLiteral, posL, negL, Gate.eval, hw, hi, hj]
  | not i =>
    cases hw : a w <;> cases hi : a i <;>
      simp [gateCNF, evalCNF, evalClause, evalLiteral, posL, negL, Gate.eval, hw, hi]

theorem gatesCNF_iff (w : ℕ) (gs : List Gate) (a : ℕ → Bool) :
    evalCNF (gatesCNF w gs) a = true ↔ ∀ p (h : p < gs.length), a (w + p) = (gs[p]).eval a := by
  induction gs generalizing w with
  | nil => simp [gatesCNF, evalCNF]
  | cons g gs ih =>
    simp only [gatesCNF, evalCNF_append, Bool.and_eq_true, gateCNF_iff, ih]
    constructor
    · rintro ⟨h0, hs⟩ p hp
      cases p with
      | zero => simpa using h0
      | succ p =>
        have := hs p (by simpa using hp)
        simpa [Nat.add_assoc, Nat.add_comm 1 p] using this
    · intro h
      refine ⟨h 0 (Nat.succ_pos _), fun p hp => ?_⟩
      have := h (p + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 p] using this

/-- **Tseitin correctness.** -/
theorem tseitin_correct (C : Circuit) (hC : C.WF) : SAT (tseitin C) ↔ CircuitSAT C := by
  have hout : C.out < C.size := by simp [Circuit.out]; have := hC.1; omega
  constructor
  · rintro ⟨a, ha⟩
    simp only [tseitin, evalCNF_append, Bool.and_eq_true, gatesCNF_iff] at ha
    obtain ⟨hg, ho⟩ := ha
    have hao : a C.out = true := by simpa [evalCNF, evalClause, evalLiteral, posL] using ho
    let inp := (List.range C.nIn).map a
    have hcons : Consistent C inp a := by
      refine ⟨fun i hi => ?_, hg⟩
      simp [inp, List.getD_eq_getElem?_getD, hi]
    refine ⟨inp, by simp [inp], ?_⟩
    rw [← consistent_unique C hC inp a _ hcons (value_consistent C hC inp) C.out hout]
    exact hao
  · rintro ⟨inp, -, hv⟩
    refine ⟨C.value inp, ?_⟩
    simp only [tseitin, evalCNF_append, Bool.and_eq_true, gatesCNF_iff]
    exact ⟨(value_consistent C hC inp).2, by simpa [evalCNF, evalClause, evalLiteral, posL] using hv⟩

end PvnpReal
