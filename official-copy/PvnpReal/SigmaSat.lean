/-
  PvnpReal.SigmaSat — **Σ_k-SAT** and its membership in Σ_k.

  Instance: block sizes `n₁ … n_k` and a formula `φ` over variables `0, 1, …` numbered block by block;
  encoded as `Rof (encNs [n₁,…,n_k]) (encodeCNF φ)` (`encNs` = `1^{n₁} 0 ⋯ 1^{n_k} 0`).
  Value: `∃ w₁ ∈ {0,1}^{n₁} ∀ w₂ ∈ {0,1}^{n₂} … Q w_k. M(w₁⋯w_k)`, where the matrix `M` is the CNF `φ`
  for odd `k` and the **DNF** `φ` (same syntax, read as an OR of ANDs of literals) for even `k`
  (variables outside the blocks read `false`, as in `asg`).
  On arbitrary strings the decoders `decX`/`decC` are used (as for `TQBF`); a string whose block part is
  malformed (`shapeOK`) is rejected, and for even `k` so is one whose matrix part is not a formula
  code (`codeB`, a finite-state check); for odd `k` the SAT verifier already rejects non-codes.
-/
import PvnpReal.PHGen
import PvnpReal.PHSpace
import PvnpReal.Fst

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

/-! ### Finite-state syntax check and literal flip on formula codes -/

inductive PM | F | C | S | V | D | E
  deriving DecidableEq, Inhabited

instance : Fintype PM := ⟨{.F, .C, .S, .V, .D, .E}, fun k => by cases k <;> simp⟩

def codeδ : PM → Bool → PM × List Bool
  | .F, false => (.D, [])
  | .F, true => (.C, [])
  | .C, false => (.F, [])
  | .C, true => (.S, [])
  | .S, _ => (.V, [])
  | .V, true => (.V, [])
  | .V, false => (.C, [])
  | _, _ => (.E, [])

def codeFin : PM → List Bool
  | .D => [true]
  | _ => [false]

/-- The syntax check, as a Boolean. -/
def codeB : PM → List Bool → Bool
  | q, [] => decide (q = .D)
  | q, b :: r => codeB (codeδ q b).1 r

theorem fstOut_code : ∀ (l : List Bool) (q : PM), fstOut codeδ codeFin q l = [codeB q l] := by
  intro l
  induction l with
  | nil => intro q; cases q <;> rfl
  | cons b l ih => intro q; simp only [fstOut, codeB, ih]; cases q <;> cases b <;> rfl

theorem InP.codeBP : InP (fun X => codeB .F X = true) := by
  obtain ⟨h⟩ := (fstComputable codeδ codeFin PM.F).congr (fun X => fstOut_code X .F)
  exact ⟨_, ⟨strToDecider h⟩, fun _ => Iff.rfl⟩

def flipδ : PM → Bool → PM × List Bool
  | .F, true => (.C, [true])
  | .F, false => (.F, [false])
  | .C, true => (.S, [true])
  | .C, false => (.F, [false])
  | .S, b => (.V, [!b])
  | .V, true => (.V, [true])
  | .V, false => (.C, [false])
  | q, b => (q, [b])

/-- Flip the sign bit of every literal (on formula codes). -/
def flipS (X : List Bool) : List Bool := fstOut flipδ (fun _ => []) .F X

theorem PS.flipS : PS flipS := fstComputable flipδ (fun _ => []) PM.F

def negCNF (φ : CNF) : CNF := φ.map (List.map (fun l => (⟨l.var, !l.neg⟩ : Literal)))

/-- DNF reading of the same syntax. -/
def evalDNF (φ : CNF) (a : ℕ → Bool) : Bool := φ.any (fun t => t.all (fun l => evalLiteral l a))

theorem evalCNF_neg (φ : CNF) (a : ℕ → Bool) : evalCNF (negCNF φ) a = !evalDNF φ a := by
  induction φ with
  | nil => rfl
  | cons t φ ih =>
    simp only [negCNF, List.map_cons, evalCNF, List.all_cons, evalDNF, List.any_cons] at ih ⊢
    rw [ih]
    have : evalClause (t.map (fun l => (⟨l.var, !l.neg⟩ : Literal))) a =
        !t.all (fun l => evalLiteral l a) := by
      induction t with
      | nil => rfl
      | cons l t iht =>
        simp only [evalClause, List.map_cons, List.any_cons, List.all_cons] at iht ⊢
        rw [iht]
        rcases l with ⟨v, n⟩; cases n <;> simp [evalLiteral]
    rw [this, Bool.not_or]

-- parsing lemmas
theorem codeB_var (v : ℕ) (r : List Bool) : codeB .V (encVar v ++ r) = codeB .C r := by
  induction v with
  | zero => simp [encVar, codeB, codeδ]
  | succ v ih => simpa [encVar, List.replicate_succ, codeB, codeδ] using ih

theorem codeB_clause (c : Clause) (r : List Bool) : codeB .C (encList encLit c ++ r) = codeB .F r := by
  induction c with
  | nil => simp [encList, codeB, codeδ]
  | cons l c ih =>
    simp only [encList, encLit, List.cons_append, List.append_assoc, codeB, codeδ]
    rw [codeB_var, ih]

theorem codeB_encode (φ : CNF) : codeB .F (encodeCNF φ) = true := by
  suffices h : ∀ r, codeB .F (encList (encList encLit) φ ++ r) = codeB .D r by
    have := h []; simp only [List.append_nil] at this; rw [encodeCNF, this]; rfl
  induction φ with
  | nil => intro r; simp [encList, codeB, codeδ]
  | cons c φ ih =>
    intro r
    simp only [encList, List.cons_append, List.append_assoc, codeB, codeδ]
    rw [codeB_clause, ih]

theorem flip_var (v : ℕ) (r : List Bool) :
    fstOut flipδ (fun _ => []) .V (encVar v ++ r) = encVar v ++ fstOut flipδ (fun _ => []) .C r := by
  induction v with
  | zero => simp [encVar, fstOut, flipδ]
  | succ v ih => simpa [encVar, List.replicate_succ, fstOut, flipδ] using ih

theorem flip_clause (c : Clause) (r : List Bool) :
    fstOut flipδ (fun _ => []) .C (encList encLit c ++ r) =
      encList encLit (c.map (fun l => (⟨l.var, !l.neg⟩ : Literal))) ++ fstOut flipδ (fun _ => []) .F r := by
  induction c with
  | nil => simp [encList, fstOut, flipδ]
  | cons l c ih =>
    simp only [encList, encLit, List.cons_append, List.append_assoc, fstOut, flipδ, List.map_cons]
    rw [flip_var, ih]; simp

theorem flipS_encode (φ : CNF) : flipS (encodeCNF φ) = encodeCNF (negCNF φ) := by
  suffices h : ∀ r, fstOut flipδ (fun _ => []) .F (encList (encList encLit) φ ++ r) =
      encList (encList encLit) (negCNF φ) ++ fstOut flipδ (fun _ => []) .F r by
    have := h []
    simp only [List.append_nil] at this
    simp only [flipS, encodeCNF, this]
    simp [fstOut]
  induction φ with
  | nil => intro r; simp [encList, fstOut, flipδ, negCNF]
  | cons c φ ih =>
    intro r
    simp only [encList, List.cons_append, List.append_assoc, fstOut, flipδ, negCNF, List.map_cons]
    rw [flip_clause, ih]; simp [negCNF]

/-! ### Block sizes -/

def encNs (l : List ℕ) : List Bool := l.flatMap (fun n => List.replicate n true ++ [false])

def nthN (j : ℕ) (ns : List Bool) : ℕ := lpN (lpX^[j] ns)

def decNs (k : ℕ) (ns : List Bool) : List ℕ := (List.range k).map (fun i => nthN i ns)

def nsum : ℕ → List Bool → ℕ
  | 0, _ => 0
  | k + 1, ns => lpN ns + 1 + nsum k (lpX ns)

/-- The block part is exactly `k` unary numbers. -/
def shapeOK (k : ℕ) (ns : List Bool) : Prop := nsum k ns = ns.length

theorem encNs_cons (n : ℕ) (l : List ℕ) : encNs (n :: l) = List.replicate n true ++ false :: encNs l := by
  simp [encNs]

theorem shapeOK_encNs (l : List ℕ) : shapeOK l.length (encNs l) := by
  unfold shapeOK
  induction l with
  | nil => rfl
  | cons n l ih => simp only [List.length_cons, nsum, encNs_cons, lpN_rep, lpX_rep, ih]; simp; omega

theorem decNs_encNs (l : List ℕ) : decNs l.length (encNs l) = l := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [decNs, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map] at ih ⊢
    simp only [nthN, Function.iterate_zero, id, encNs_cons, lpN_rep, List.cons.injEq, true_and]
    conv_rhs => rw [← ih]
    apply List.map_congr_left; intro i _
    simp [nthN, Function.iterate_succ, lpX_rep]

/-! ### The language -/

/-- Alternating block quantification over a leaf predicate on the concatenated assignment. -/
def sval (leaf : List Bool → Bool) : List ℕ → Bool → List Bool → Prop
  | [], _, p => leaf p = true
  | n :: ns, true, p => ∃ w : List Bool, w.length = n ∧ sval leaf ns false (p ++ w)
  | n :: ns, false, p => ∀ w : List Bool, w.length = n → sval leaf ns true (p ++ w)

/-- Sum of the first `j` block sizes. -/
def psum : ℕ → List Bool → ℕ
  | 0, _ => 0
  | j + 1, ns => lpN ns + psum j (lpX ns)

/-- Variable numbering: the assignment `w₁⋯w_k` (outermost first) is rotated so that the
innermost block `w_k` gets the variables `0 … n_k - 1`, followed by `w₁ ⋯ w_{k-1}`. -/
def rot (n : ℕ) (p : List Bool) : List Bool := p.drop n ++ p.take n

/-- The leaf on string codes: CNF for odd `k`, DNF for even `k`; `n` is the size of the outer
blocks `w₁⋯w_{k-1}`. -/
def leafK (k n : ℕ) (X p : List Bool) : Bool :=
  if k % 2 = 1 then verify X (rot n p) else (codeB .F X && !verify (flipS X) (rot n p))

/-- **Σ_k-SAT.** -/
def SigmaSAT (k : ℕ) : Language := fun y =>
  shapeOK k (decX y) ∧ sval (leafK k (psum (k - 1) (decX y)) (decC y)) (decNs k (decX y)) true []

def encSigma (ns : List ℕ) (φ : CNF) : List Bool := Rof (encNs ns) (encodeCNF φ)

def matVal (k : ℕ) (φ : CNF) (a : ℕ → Bool) : Bool := if k % 2 = 1 then evalCNF φ a else evalDNF φ a

theorem sval_congr {f g : List Bool → Bool} (h : ∀ p, f p = g p) :
    ∀ ns b p, sval f ns b p ↔ sval g ns b p := by
  intro ns
  induction ns with
  | nil => intro b p; simp [sval, h]
  | cons n ns ih => intro b p; cases b <;> simp [sval, ih]

/-- **Σ_k-SAT on codes**: `∃ w₁ ∀ w₂ … M(w₁⋯w_k)` with `|w_i| = nᵢ`. -/
theorem psum_encNs : ∀ (l : List ℕ) (j : ℕ), psum j (encNs l) = (l.take j).sum := by
  intro l
  induction l with
  | nil =>
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simpa [psum, encNs, lpN, lpX] using ih
  | cons n l ih =>
    intro j
    cases j with
    | zero => rfl
    | succ j => simp only [psum, encNs_cons, lpN_rep, lpX_rep, ih, List.take_succ_cons, List.sum_cons]

theorem SigmaSAT_encode (ns : List ℕ) (φ : CNF) :
    SigmaSAT ns.length (encSigma ns φ) ↔
      sval (fun p => matVal ns.length φ (asg (rot (ns.take (ns.length - 1)).sum p))) ns true [] := by
  simp only [SigmaSAT, encSigma, decX_Rof, decC_Rof, decNs_encNs, psum_encNs]
  refine ⟨fun h => (sval_congr (fun p => ?_) _ _ _).1 h.2,
    fun h => ⟨shapeOK_encNs ns, (sval_congr (fun p => ?_) _ _ _).1 h⟩⟩
  · unfold leafK matVal
    split_ifs
    · exact verify_encode φ _
    · rw [codeB_encode, flipS_encode, verify_encode, evalCNF_neg]; simp
  · unfold leafK matVal
    split_ifs
    · exact (verify_encode φ _).symm
    · rw [codeB_encode, flipS_encode, verify_encode, evalCNF_neg]; simp

/-! ### Σ_k-SAT ∈ Σ_k -/

theorem altQ_conj (A R : Language) (qs : ℕ → Polynomial ℕ) (x : List Bool) :
    ∀ k b u, altQ (fun s => A (decP s).1 ∧ R s) qs x k b u ↔ A x ∧ altQ R qs x k b u := by
  intro k
  induction k with
  | zero => intro b u; simp [decP_codeP]
  | succ k ih =>
    intro b u
    cases b
    · simp only [altQ_succ_false, ih]
      constructor
      · intro h
        exact ⟨(h (List.replicate ((qs k).eval x.length) false) (by simp)).1, fun w hw => (h w hw).2⟩
      · rintro ⟨hA, h⟩ w hw; exact ⟨hA, h w hw⟩
    · simp only [altQ_succ_true, ih]
      constructor
      · rintro ⟨w, hw, hA, h⟩; exact ⟨hA, w, hw, h⟩
      · rintro ⟨hA, w, hw, h⟩; exact ⟨w, hw, hA, h⟩

/-- Σ_k is closed under intersection with a P language. -/
theorem InSigma.inter_P {k : ℕ} {A B : Language} (hA : InP A) (hB : InSigma k B) :
    InSigma k (fun x => A x ∧ B x) := by
  obtain ⟨R, qs, hR, hL⟩ := hB
  exact ⟨_, qs, (hA.compPS PS.fstP).inter hR, fun x =>
    (and_congr_right fun _ => hL x).trans (altQ_conj A R qs x k true []).symm⟩

theorem PS.iterDrop (j : ℕ) : PS (fun ns => lpX^[j] ns) := by
  induction j with
  | zero => exact PS.id
  | succ j ih => exact (PS.comp PS.drop ih).congr (fun ns => by rw [Function.iterate_succ_apply])

theorem iterDrop_len (j : ℕ) (ns : List Bool) : (lpX^[j] ns).length ≤ ns.length := by
  induction j generalizing ns with
  | zero => exact le_rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (by have := LoopTM.lp_len ns; omega)

theorem nthN_le (j : ℕ) (ns : List Bool) : nthN j ns ≤ ns.length := by
  have := LoopTM.lp_len (lpX^[j] ns); have := iterDrop_len j ns
  unfold nthN; omega

theorem PU.nsum (k : ℕ) : PU (nsum k) := by
  induction k with
  | zero => exact PU.const 0
  | succ k ih => exact ((PU.fst.add (PU.const 1)).add (ih.comp PS.drop)).congr (fun _ => rfl)

theorem InP.shapeOKP (k : ℕ) : InP (fun y => shapeOK k (decX y)) :=
  InP.ofPUeq ((PU.nsum k).comp PS.decX) (PU.lenX.comp PS.decX)

theorem PU.psum (j : ℕ) : PU (psum j) := by
  induction j with
  | zero => exact PU.const 0
  | succ j ih => exact (PU.fst.add (ih.comp PS.drop)).congr (fun _ => rfl)

theorem PS.rot {n : List Bool → ℕ} {A : List Bool → List Bool} (hn : PU n) (hA : PS A) :
    PS (fun s => rot (n s) (A s)) :=
  ((PS.dropU hA hn).append (PS.takeU hA hn)).congr (fun _ => rfl)

theorem InP.leafKP (k : ℕ) :
    InP (fun s => leafK k (psum (k - 1) (decX (decP s).1)) (decC (decP s).1) (decP s).2 = true) := by
  have hver : InP (fun t => verify (decP t).1 (decP t).2 = true) :=
    InP.ofPair (V := fun p => verify p.1 p.2) ⟨satVerifierComputable⟩
  have hX : PS (fun s => decC (decP s).1) := PS.comp PS.fstP PS.decC
  have hn : PU (fun s => psum (k - 1) (decX (decP s).1)) :=
    (PU.psum (k - 1)).comp (PS.comp PS.fstP PS.decX)
  have hr : PS (fun s => rot (psum (k - 1) (decX (decP s).1)) (decP s).2) := PS.rot hn PS.sndP
  by_cases hk : k % 2 = 1
  · exact (hver.compPS (PS.codePF hX hr)).congr (fun s => by simp [leafK, hk, decP_codeP])
  · have h1 := InP.codeBP.compPS hX
    have h2 := (hver.compPS (PS.codePF (PS.comp hX PS.flipS) hr)).compl
    exact (h1.inter h2).congr (fun s => by simp [leafK, hk, decP_codeP])

theorem drop_decNs (k j : ℕ) (ns : List Bool) (hj : j < k) :
    (decNs k ns).drop (k - (j + 1)) = nthN (k - (j + 1)) ns :: (decNs k ns).drop (k - j) := by
  have hl : k - (j + 1) < (decNs k ns).length := by simp [decNs]; omega
  rw [List.drop_eq_getElem_cons hl]
  simp only [decNs, List.getElem_map, List.getElem_range]
  congr 2; omega

/-- **Σ_k-SAT ∈ Σ_k.** -/
theorem SigmaSAT_in_Sigma (k : ℕ) : InSigma k (SigmaSAT k) := by
  refine InSigma.inter_P (InP.shapeOKP k) ?_
  let lens : ℕ → List Bool → List Bool → ℕ := fun j y _ => nthN (k - 1 - j) (decX y)
  obtain ⟨R', hR', e⟩ := altD_pad (InP.leafKP k) lens
    (fun j => ((PU.fst.comp (PS.iterDrop (k - 1 - j))).comp (PS.comp PS.fstP PS.decX)).congr
      (fun s => rfl))
    (fun _ => Polynomial.X)
    (fun j y _ => by
      simp only [Polynomial.eval_X, lens]
      exact (nthN_le _ _).trans (decX_len y)) k
  refine ⟨R', fun _ => Polynomial.X, hR', fun y => ?_⟩
  refine Iff.trans ?_ (e y true)
  have key : ∀ j ≤ k, ∀ b u, altD (fun s => leafK k (psum (k - 1) (decX (decP s).1)) (decC (decP s).1) (decP s).2 = true)
      lens y j b u ↔ sval (leafK k (psum (k - 1) (decX y)) (decC y)) ((decNs k (decX y)).drop (k - j)) b u := by
    intro j
    induction j with
    | zero =>
      intro _ b u
      rw [show k - 0 = k by omega, List.drop_eq_nil_of_le (by simp [decNs])]
      simp [sval, decP_codeP]
    | succ j ih =>
      intro hj b u
      rw [drop_decNs k j _ (by omega)]
      have hlen : lens j y u = nthN (k - (j + 1)) (decX y) := by
        simp only [lens]; congr 1; omega
      cases b
      · simp only [altD_succ_false, sval, hlen, ih (by omega)]
      · simp only [altD_succ_true, sval, hlen, ih (by omega)]
  have := key k le_rfl true []
  rw [Nat.sub_self, List.drop_zero] at this
  exact this.symm

end PvnpReal
