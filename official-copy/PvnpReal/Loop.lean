/-
  PvnpReal.Loop — a bounded-loop combinator with a unary counter.

  For a polynomial-time `g`, the function
    `loopF g (1ⁿ 0 x) = g (0 x) ++ g (1 0 x) ++ … ++ g (1ⁿ⁻¹ 0 x)`
  is polynomial-time (`loopComputable`).  The machine keeps the remaining count, the current
  index `i` (unary), and a reversed copy of `x`; in each round it builds `1ⁱ 0 x` on the body's
  input stack, runs the body, and appends the body's output to an accumulator.
-/
import PvnpReal.FanOut

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability StateTransition Turing.TM2.Stmt

/-- Leading ones / the part after the first zero (all of it if there is no zero). -/
def lpN (y : List Bool) : ℕ := (y.takeWhile id).length
def lpX (y : List Bool) : List Bool := y.drop (lpN y + 1)

def loopF (g : List Bool → List Bool) (y : List Bool) : List Bool :=
  (List.range (lpN y)).flatMap fun i => g (List.replicate i true ++ false :: lpX y)

namespace LoopTM

inductive LK | inp | A | I | X | O | T | out
  deriving DecidableEq

inductive LP | rd | rx | loop | cx | bx | ci | bi | mo | fo | cI | cX
  deriving DecidableEq

instance : Fintype LK := ⟨{.inp, .A, .I, .X, .O, .T, .out}, fun k => by cases k <;> simp⟩
instance : Fintype LP :=
  ⟨{.rd, .rx, .loop, .cx, .bx, .ci, .bi, .mo, .fo, .cI, .cX}, fun k => by cases k <;> simp⟩

variable (M : FinTM2) (ei : M.Γ M.k₀ ≃ Bool) (eo : M.Γ M.k₁ ≃ Bool)

abbrev K := LK ⊕ M.K
abbrev Γ : K M → Type
  | .inl _ => Bool
  | .inr k => M.Γ k
abbrev Λ := M.Λ ⊕ LP
abbrev σ := M.σ × Option Bool
abbrev St := TM2.Stmt (Γ M) (Λ M) (σ M)
abbrev Cfg := TM2.Cfg (Γ M) (Λ M) (σ M)

def liftM : TM2.Stmt M.Γ M.Λ M.σ → St M
  | .push k f q => push (.inr k) (fun s => f s.1) (liftM q)
  | .peek k f q => peek (.inr k) (fun s o => (f s.1 o, s.2)) (liftM q)
  | .pop k f q => pop (.inr k) (fun s o => (f s.1 o, s.2)) (liftM q)
  | .load a q => load (fun s => (a s.1, s.2)) (liftM q)
  | .branch f q₁ q₂ => branch (fun s => f s.1) (liftM q₁) (liftM q₂)
  | .goto f => goto (fun s => .inl (f s.1))
  | .halt => goto (fun _ => .inr .mo)

def mv (a b : K M) (ea : Γ M a → Bool) (eb : Bool → Γ M b) (self : LP) (fin : St M) : St M :=
  pop a (fun s o => (s.1, o.map ea))
    (branch (fun s => s.2.isSome) (push b (fun s => eb (s.2.getD false)) (goto fun _ => .inr self))
      fin)

def cp (a b c : K M) (ea : Γ M a → Bool) (eb : Bool → Γ M b) (ec : Bool → Γ M c) (self : LP)
    (fin : St M) : St M :=
  pop a (fun s o => (s.1, o.map ea))
    (branch (fun s => s.2.isSome)
      (push b (fun s => eb (s.2.getD false)) (push c (fun s => ec (s.2.getD false))
        (goto fun _ => .inr self)))
      fin)

def clr (a : K M) (self : LP) (fin : St M) : St M :=
  pop a (fun s o => (s.1, o.map fun _ => false))
    (branch (fun s => s.2.isSome) (goto fun _ => .inr self) fin)

def Lm : Λ M → St M
  | .inl l => liftM M (M.m l)
  | .inr .rd => pop (.inl .inp) (fun s o => (s.1, o))
      (branch (fun s => decide (s.2 = some true))
        (push (.inl .A) (fun _ => true) (goto fun _ => .inr .rd))
        (branch (fun s => decide (s.2 = some false)) (goto fun _ => .inr .rx)
          (goto fun _ => .inr .loop)))
  | .inr .rx => mv M (.inl .inp) (.inl .X) (fun b => b) (fun b => b) .rx (goto fun _ => .inr .loop)
  | .inr .loop => pop (.inl .A) (fun s o => (s.1, o))
      (branch (fun s => s.2.isSome) (goto fun _ => .inr .cx) (goto fun _ => .inr .fo))
  | .inr .cx => cp M (.inl .X) (.inr M.k₀) (.inl .T) (fun b => b) ei.symm (fun b => b) .cx
      (goto fun _ => .inr .bx)
  | .inr .bx => mv M (.inl .T) (.inl .X) (fun b => b) (fun b => b) .bx
      (push (.inr M.k₀) (fun _ => ei.symm false) (goto fun _ => .inr .ci))
  | .inr .ci => cp M (.inl .I) (.inr M.k₀) (.inl .T) (fun b => b) ei.symm (fun b => b) .ci
      (goto fun _ => .inr .bi)
  | .inr .bi => mv M (.inl .T) (.inl .I) (fun b => b) (fun b => b) .bi
      (push (.inl .I) (fun _ => true)
        (load (fun _ => (M.initialState, none)) (goto fun _ => .inl M.main)))
  | .inr .mo => mv M (.inr M.k₁) (.inl .O) eo (fun b => b) .mo (goto fun _ => .inr .loop)
  | .inr .fo => mv M (.inl .O) (.inl .out) (fun b => b) (fun b => b) .fo
      (goto fun _ => .inr .cI)
  | .inr .cI => clr M (.inl .I) .cI (goto fun _ => .inr .cX)
  | .inr .cX => clr M (.inl .X) .cX halt

def loopTM : FinTM2 where
  K := K M
  kDecidableEq := inferInstance
  kFin := @instFintypeSum _ _ inferInstance M.kFin
  k₀ := .inl .inp
  k₁ := .inl .out
  Γ := Γ M
  Λ := Λ M
  main := .inr .rd
  ΛFin := @instFintypeSum _ _ M.ΛFin inferInstance
  σ := σ M
  initialState := (M.initialState, none)
  σFin := @instFintypeProd _ _ M.σFin inferInstance
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := Lm M ei eo

abbrev F : Option (Cfg M) → Option (Cfg M) := flip bind (TM2.step (Lm M ei eo))

/-! ### Stack builder -/

def L (inp A I X O T out : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k : K M, List (Γ M k)
  | .inl .inp => inp
  | .inl .A => A
  | .inl .I => I
  | .inl .X => X
  | .inl .O => O
  | .inl .T => T
  | .inl .out => out
  | .inr k => S k

section upd
variable (inp A I X O T out v : List Bool) (S : ∀ k, List (M.Γ k))

macro "lupd_tac" : tactic => `(tactic| (
  funext j
  rcases j with ((_ | _ | _ | _ | _ | _ | _) | j) <;>
    first
    | (rw [Function.update_self]; rfl)
    | (rw [Function.update_of_ne (by simp)]; rfl)))

theorem u_inp : Function.update (L M inp A I X O T out S) (.inl .inp) v =
    L M v A I X O T out S := by lupd_tac
theorem u_A : Function.update (L M inp A I X O T out S) (.inl .A) v =
    L M inp v I X O T out S := by lupd_tac
theorem u_I : Function.update (L M inp A I X O T out S) (.inl .I) v =
    L M inp A v X O T out S := by lupd_tac
theorem u_X : Function.update (L M inp A I X O T out S) (.inl .X) v =
    L M inp A I v O T out S := by lupd_tac
theorem u_O : Function.update (L M inp A I X O T out S) (.inl .O) v =
    L M inp A I X v T out S := by lupd_tac
theorem u_T : Function.update (L M inp A I X O T out S) (.inl .T) v =
    L M inp A I X O v out S := by lupd_tac
theorem u_out : Function.update (L M inp A I X O T out S) (.inl .out) v =
    L M inp A I X O T v S := by lupd_tac

theorem u_M (k : M.K) (w : List (M.Γ k)) :
    Function.update (L M inp A I X O T out S) (.inr k) w =
      L M inp A I X O T out (Function.update S k w) := by
  funext j
  rcases j with ((_ | _ | _ | _ | _ | _ | _) | j)
  all_goals try (rw [Function.update_of_ne (by simp)]; rfl)
  by_cases h : j = k
  · subst h; rw [Function.update_self]
    show w = Function.update S j w j
    rw [Function.update_self]
  · rw [Function.update_of_ne (by simpa using h)]
    show S j = Function.update S k w j
    rw [Function.update_of_ne h]

end upd

theorem nil_updM (k : M.K) :
    (Function.update (fun _ => []) k [] : ∀ j, List (M.Γ j)) = fun _ => [] := by
  funext j; by_cases h : j = k
  · subst h; simp
  · simp [h]

/-! ### Generic loops -/

section gen
variable {M ei eo}

theorem mv_run (a b : K M) (hab : a ≠ b) (ea : Γ M a → Bool) (eb : Bool → Γ M b) (self : LP)
    (fin : St M) (hm : Lm M ei eo (.inr self) = mv M a b ea eb self fin) (l : List (Γ M a)) :
    ∀ (v : M.σ) (o : Option Bool) (S : ∀ k, List (Γ M k)), S a = l →
    (F M ei eo)^[l.length + 1] (some ⟨some (.inr self), (v, o), S⟩) =
      some (TM2.stepAux fin (v, none)
        (Function.update (Function.update S a []) b ((l.map (eb ∘ ea)).reverse ++ S b))) := by
  induction l with
  | nil =>
    intro v o S hS
    show some (TM2.stepAux (Lm M ei eo (.inr self)) (v, o) S) = _
    rw [hm]
    simp only [mv, TM2.stepAux, hS, List.head?_nil, List.tail_nil, Option.map_none,
      Option.isSome_none, Bool.cond_false, List.map_nil, List.reverse_nil, List.nil_append]
    congr 2
    funext k
    by_cases hk : k = b
    · subst hk; rw [Function.update_self, Function.update_of_ne (Ne.symm hab)]
    · rw [Function.update_of_ne hk]
  | cons x l ih =>
    intro v o S hS
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F M ei eo (some ⟨some (.inr self), (v, o), S⟩) =
        some ⟨some (.inr self), (v, some (ea x)),
          Function.update (Function.update S a l) b (eb (ea x) :: S b)⟩ := by
      show some (TM2.stepAux (Lm M ei eo (.inr self)) (v, o) S) = _
      rw [hm]
      simp only [mv, TM2.stepAux, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      congr 3
      rw [Function.update_of_ne (Ne.symm hab)]
    rw [e, ih v _ _ (by rw [Function.update_of_ne hab, Function.update_self])]
    congr 2
    funext k
    by_cases hk : k = b
    · subst hk
      rw [Function.update_self, Function.update_self, Function.update_self]
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      by_cases ha : k = a
      · subst ha; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne hk,
          Function.update_of_ne ha]

theorem cp_run (a b c : K M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ea : Γ M a → Bool)
    (eb : Bool → Γ M b) (ec : Bool → Γ M c) (self : LP) (fin : St M)
    (hm : Lm M ei eo (.inr self) = cp M a b c ea eb ec self fin) (l : List (Γ M a)) :
    ∀ (v : M.σ) (o : Option Bool) (S : ∀ k, List (Γ M k)), S a = l →
    (F M ei eo)^[l.length + 1] (some ⟨some (.inr self), (v, o), S⟩) =
      some (TM2.stepAux fin (v, none)
        (Function.update (Function.update (Function.update S a []) b
          ((l.map (eb ∘ ea)).reverse ++ S b)) c ((l.map (ec ∘ ea)).reverse ++ S c))) := by
  induction l with
  | nil =>
    intro v o S hS
    show some (TM2.stepAux (Lm M ei eo (.inr self)) (v, o) S) = _
    rw [hm]
    simp only [cp, TM2.stepAux, hS, List.head?_nil, List.tail_nil, Option.map_none,
      Option.isSome_none, Bool.cond_false, List.map_nil, List.reverse_nil, List.nil_append]
    congr 2
    funext k
    by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> (try subst_vars) <;>
      simp_all [Function.update_of_ne]
  | cons x l ih =>
    intro v o S hS
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F M ei eo (some ⟨some (.inr self), (v, o), S⟩) =
        some ⟨some (.inr self), (v, some (ea x)),
          Function.update (Function.update (Function.update S a l) b (eb (ea x) :: S b)) c
            (ec (ea x) :: S c)⟩ := by
      show some (TM2.stepAux (Lm M ei eo (.inr self)) (v, o) S) = _
      rw [hm]
      simp only [cp, TM2.stepAux, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [Function.update_of_ne (Ne.symm hbc), Function.update_of_ne (Ne.symm hac),
        Function.update_of_ne (Ne.symm hab)]
    rw [e, ih v _ _ (by rw [Function.update_of_ne hac, Function.update_of_ne hab,
      Function.update_self])]
    congr 2
    funext k
    by_cases h1 : k = a <;> by_cases h2 : k = b <;> by_cases h3 : k = c <;> (try subst_vars) <;>
      simp_all [Function.update_of_ne]

theorem clr_run (a : K M) (self : LP) (fin : St M)
    (hm : Lm M ei eo (.inr self) = clr M a self fin) (l : List (Γ M a)) :
    ∀ (v : M.σ) (o : Option Bool) (S : ∀ k, List (Γ M k)), S a = l →
    (F M ei eo)^[l.length + 1] (some ⟨some (.inr self), (v, o), S⟩) =
      some (TM2.stepAux fin (v, none) (Function.update S a [])) := by
  induction l with
  | nil =>
    intro v o S hS
    show some (TM2.stepAux (Lm M ei eo (.inr self)) (v, o) S) = _
    rw [hm]
    simp only [clr, TM2.stepAux, hS, List.head?_nil, List.tail_nil, Option.map_none,
      Option.isSome_none, Bool.cond_false]
  | cons x l ih =>
    intro v o S hS
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : F M ei eo (some ⟨some (.inr self), (v, o), S⟩) =
        some ⟨some (.inr self), (v, some false), Function.update S a l⟩ := by
      show some (TM2.stepAux (Lm M ei eo (.inr self)) (v, o) S) = _
      rw [hm]
      simp only [clr, TM2.stepAux, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, Bool.cond_true]
    rw [e, ih v _ _ (by rw [Function.update_self]), Function.update_idem]

end gen

/-! ### The phases, on the stack builder -/

section phases
variable (inp A I X O T out : List Bool) (S : ∀ k, List (M.Γ k)) (v : M.σ) (o : Option Bool)

theorem mapid (l : List Bool) : List.map ((fun b : Bool => b) ∘ fun b => b) l = l := List.map_id l

theorem Pcx : (F M ei eo)^[X.length + 1]
    (some ⟨some (.inr .cx), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .bx), (v, none), L M inp A I [] O (X.reverse ++ T) out
      (Function.update S M.k₀ ((X.map ei.symm).reverse ++ S M.k₀))⟩ := by
  refine (cp_run (.inl .X) (.inr M.k₀) (.inl .T) (by simp) (by simp) (by simp) (fun b => b)
    ei.symm (fun b => b) .cx _ rfl X v o _ rfl).trans ?_
  rw [u_X, u_M, u_T, mapid]; rfl

theorem Pci : (F M ei eo)^[I.length + 1]
    (some ⟨some (.inr .ci), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .bi), (v, none), L M inp A [] X O (I.reverse ++ T) out
      (Function.update S M.k₀ ((I.map ei.symm).reverse ++ S M.k₀))⟩ := by
  refine (cp_run (.inl .I) (.inr M.k₀) (.inl .T) (by simp) (by simp) (by simp) (fun b => b)
    ei.symm (fun b => b) .ci _ rfl I v o _ rfl).trans ?_
  rw [u_I, u_M, u_T, mapid]; rfl

theorem Pbx : (F M ei eo)^[T.length + 1]
    (some ⟨some (.inr .bx), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .ci), (v, none), L M inp A I (T.reverse ++ X) O [] out
      (Function.update S M.k₀ (ei.symm false :: S M.k₀))⟩ := by
  refine (mv_run (.inl .T) (.inl .X) (by simp) (fun b => b) (fun b => b) .bx _ rfl T v o _
    rfl).trans ?_
  rw [u_T, u_X, mapid]
  show some (TM2.stepAux (goto fun _ => Sum.inr LP.ci) (v, none)
    (Function.update (L M inp A I (T.reverse ++ X) O [] out S) (.inr M.k₀)
      (ei.symm false :: S M.k₀))) = _
  rw [u_M]; rfl

theorem Pbi : (F M ei eo)^[T.length + 1]
    (some ⟨some (.inr .bi), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inl M.main), (M.initialState, none),
      L M inp A (true :: (T.reverse ++ I)) X O [] out S⟩ := by
  refine (mv_run (.inl .T) (.inl .I) (by simp) (fun b => b) (fun b => b) .bi _ rfl T v o _
    rfl).trans ?_
  rw [u_T, u_I, mapid]
  show some (TM2.stepAux (goto fun _ => Sum.inl M.main) (M.initialState, none)
    (Function.update (L M inp A (T.reverse ++ I) X O [] out S) (.inl .I)
      (true :: (T.reverse ++ I)))) = _
  rw [u_I]; rfl

theorem Pmo : (F M ei eo)^[(S M.k₁).length + 1]
    (some ⟨some (.inr .mo), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .loop), (v, none), L M inp A I X (((S M.k₁).map eo).reverse ++ O) T out
      (Function.update S M.k₁ [])⟩ := by
  refine (mv_run (.inr M.k₁) (.inl .O) (by simp) eo (fun b => b) .mo _ rfl (S M.k₁) v o _
    rfl).trans ?_
  rw [u_M, u_O]; rfl

theorem Pfo : (F M ei eo)^[O.length + 1]
    (some ⟨some (.inr .fo), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .cI), (v, none), L M inp A I X [] T (O.reverse ++ out) S⟩ := by
  refine (mv_run (.inl .O) (.inl .out) (by simp) (fun b => b) (fun b => b) .fo _ rfl O v o _
    rfl).trans ?_
  rw [u_O, u_out, mapid]; rfl

theorem Prx : (F M ei eo)^[inp.length + 1]
    (some ⟨some (.inr .rx), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .loop), (v, none), L M [] A I (inp.reverse ++ X) O T out S⟩ := by
  refine (mv_run (.inl .inp) (.inl .X) (by simp) (fun b => b) (fun b => b) .rx _ rfl inp v o _
    rfl).trans ?_
  rw [u_inp, u_X, mapid]; rfl

theorem PcI : (F M ei eo)^[I.length + 1]
    (some ⟨some (.inr .cI), (v, o), L M inp A I X O T out S⟩) =
    some ⟨some (.inr .cX), (v, none), L M inp A [] X O T out S⟩ := by
  refine (clr_run (.inl .I) .cI _ rfl I v o _ rfl).trans ?_
  rw [u_I]; rfl

theorem PcX : (F M ei eo)^[X.length + 1]
    (some ⟨some (.inr .cX), (v, o), L M inp A I X O T out S⟩) =
    some ⟨none, (v, none), L M inp A I [] O T out S⟩ := by
  refine (clr_run (.inl .X) .cX _ rfl X v o _ rfl).trans ?_
  rw [u_X]; rfl

theorem Ploop_s (a : Bool) : (F M ei eo)^[1]
    (some ⟨some (.inr .loop), (v, o), L M inp (a :: A) I X O T out S⟩) =
    some ⟨some (.inr .cx), (v, some a), L M inp A I X O T out S⟩ := by
  show some (TM2.stepAux (Lm M ei eo (.inr .loop)) (v, o) (L M inp (a :: A) I X O T out S)) = _
  simp only [Lm, TM2.stepAux]
  show some (TM2.stepAux (goto fun _ => Sum.inr LP.cx) (v, some a)
    (Function.update (L M inp (a :: A) I X O T out S) (.inl .A) A)) = _
  rw [u_A]; rfl

theorem Ploop_n : (F M ei eo)^[1]
    (some ⟨some (.inr .loop), (v, o), L M inp [] I X O T out S⟩) =
    some ⟨some (.inr .fo), (v, none), L M inp [] I X O T out S⟩ := by
  show some (TM2.stepAux (Lm M ei eo (.inr .loop)) (v, o) (L M inp [] I X O T out S)) = _
  simp only [Lm, TM2.stepAux]
  show some (TM2.stepAux (goto fun _ => Sum.inr LP.fo) (v, none)
    (Function.update (L M inp [] I X O T out S) (.inl .A) [])) = _
  rw [u_A]; rfl

end phases

theorem lpN_cons_true (y : List Bool) : lpN (true :: y) = lpN y + 1 := by
  simp [lpN]
theorem lpX_cons_true (y : List Bool) : lpX (true :: y) = lpX y := by
  simp [lpX, lpN_cons_true]
theorem lpN_cons_false (y : List Bool) : lpN (false :: y) = 0 := by simp [lpN]
theorem lpX_cons_false (y : List Bool) : lpX (false :: y) = y := by simp [lpX, lpN_cons_false]

theorem Prd (y : List Bool) : ∀ (A I X O T out : List Bool) (S : ∀ k, List (M.Γ k))
    (v : M.σ) (o : Option Bool), ∃ n ≤ y.length + 2, (F M ei eo)^[n]
    (some ⟨some (.inr .rd), (v, o), L M y A I X O T out S⟩) =
    some ⟨some (.inr .loop), (v, none), L M [] (List.replicate (lpN y) true ++ A) I
      ((lpX y).reverse ++ X) O T out S⟩ := by
  induction y with
  | nil =>
    intro A I X O T out S v o
    refine ⟨1, by simp, ?_⟩
    show some (TM2.stepAux (Lm M ei eo (.inr .rd)) (v, o) (L M [] A I X O T out S)) = _
    simp only [Lm, TM2.stepAux]
    show some (TM2.stepAux (goto fun _ => Sum.inr LP.loop) (v, none)
      (Function.update (L M [] A I X O T out S) (.inl .inp) [])) = _
    rw [u_inp]; rfl
  | cons b y ih =>
    intro A I X O T out S v o
    cases b with
    | true =>
      obtain ⟨n, hn, h⟩ := ih (true :: A) I X O T out S v (some true)
      refine ⟨n + 1, by simp; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      have e : F M ei eo (some ⟨some (.inr .rd), (v, o), L M (true :: y) A I X O T out S⟩) =
          some ⟨some (.inr .rd), (v, some true), L M y (true :: A) I X O T out S⟩ := by
        show some (TM2.stepAux (Lm M ei eo (.inr .rd)) (v, o)
          (L M (true :: y) A I X O T out S)) = _
        simp only [Lm, TM2.stepAux]
        show some (TM2.stepAux (goto fun _ => Sum.inr LP.rd) (v, some true)
          (Function.update (Function.update (L M (true :: y) A I X O T out S) (.inl .inp) y)
            (.inl .A) (true :: A))) = _
        rw [u_inp, u_A]; rfl
      rw [e, h, lpN_cons_true, lpX_cons_true, List.replicate_succ', List.append_assoc]
      rfl
    | false =>
      refine ⟨(y.length + 1) + 1, by simp, ?_⟩
      rw [Function.iterate_add_apply]
      have e : (F M ei eo)^[1]
          (some ⟨some (.inr .rd), (v, o), L M (false :: y) A I X O T out S⟩) =
          some ⟨some (.inr .rx), (v, some false), L M y A I X O T out S⟩ := by
        show some (TM2.stepAux (Lm M ei eo (.inr .rd)) (v, o)
          (L M (false :: y) A I X O T out S)) = _
        simp only [Lm, TM2.stepAux]
        show some (TM2.stepAux (goto fun _ => Sum.inr LP.rx) (v, some false)
          (Function.update (L M (false :: y) A I X O T out S) (.inl .inp) y)) = _
        rw [u_inp]; rfl
      rw [e, Prx, lpN_cons_false, lpX_cons_false]
      rfl

/-! ### Lifting the body machine -/

def liftCM (c : M.Cfg) (o : Option Bool) (inp A I X O T out : List Bool) : Cfg M :=
  ⟨some (match c.l with | none => .inr .mo | some l => .inl l), (c.var, o),
    L M inp A I X O T out c.stk⟩

theorem stepAux_liftM (o : Option Bool) (inp A I X O T out : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (liftM M q) (v, o) (L M inp A I X O T out S) =
      liftCM M (TM2.stepAux q v S) o inp A I X O T out := by
  induction q generalizing v S with
  | push k f q ih =>
    show TM2.stepAux (liftM M q) (v, o)
      (Function.update (L M inp A I X O T out S) (.inr k) (f v :: S k)) = _
    rw [u_M]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    show TM2.stepAux (liftM M q) (f v (S k).head?, o)
      (Function.update (L M inp A I X O T out S) (.inr k) (S k).tail) = _
    rw [u_M]; exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    show cond (f v) _ _ = liftCM M (cond (f v) _ _) o inp A I X O T out
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl

theorem iterate_liftM (o : Option Bool) (inp A I X O T out : List Bool)
    (n : ℕ) (c d : M.Cfg) (h : (flip bind (TM2.step M.m))^[n] (some c) = some d) :
    (F M ei eo)^[n] (some (liftCM M c o inp A I X O T out)) =
      some (liftCM M d o inp A I X O T out) := by
  induction n generalizing c with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · change (flip bind (TM2.step M.m))^[n] none = some d at h
      rw [flip_bind_iterate_none] at h; cases h
    · change (flip bind (TM2.step M.m))^[n] (some (TM2.stepAux (M.m l) v S)) = some d at h
      change (F M ei eo)^[n]
        (some (TM2.stepAux (liftM M (M.m l)) (v, o) (L M inp A I X O T out S))) = _
      rw [stepAux_liftM]
      exact ih _ h

/-! ### One round and the whole loop -/

section run
variable (g : List Bool → List Bool) (Tp : Polynomial ℕ) (C : ℕ)
  (hM : ∀ z : List Bool, ∃ n ≤ Tp.eval z.length, (flip bind (TM2.step M.m))^[n]
    (some (initList M (z.map ei.symm))) = some (haltList M ((g z).map eo.symm)))
  (hlen : ∀ z : List Bool, (g z).length ≤ z.length + C * Tp.eval z.length)

theorem runM (z : List Bool) (Ar I4 X2 O : List Bool) (S : ∀ k, List (M.Γ k))
    (hS : S = Function.update (fun _ => []) M.k₀ (z.map ei.symm)) (nM : ℕ)
    (hrun : (flip bind (TM2.step M.m))^[nM] (some (initList M (z.map ei.symm))) =
      some (haltList M ((g z).map eo.symm))) :
    (F M ei eo)^[nM] (some ⟨some (.inl M.main), (M.initialState, none),
      L M [] Ar I4 X2 O [] [] S⟩) =
      some (liftCM M (haltList M ((g z).map eo.symm)) none [] Ar I4 X2 O [] []) := by
  subst hS
  have h := iterate_liftM M ei eo none [] Ar I4 X2 O [] [] nM _ _ hrun
  have e : liftCM M (initList M (z.map ei.symm)) none [] Ar I4 X2 O [] [] =
      ⟨some (.inl M.main), (M.initialState, none),
        L M [] Ar I4 X2 O [] [] (Function.update (fun _ => []) M.k₀ (z.map ei.symm))⟩ := by
    simp only [liftCM, initList_stk]; rfl
  rw [e] at h
  exact h

include hM hlen in
theorem iter1 (i : ℕ) (x Ar O : List Bool) (a : Bool) (v : M.σ) (o : Option Bool) :
    ∃ n ≤ 3 * (i + 1 + x.length) + 4 + Tp.eval (i + 1 + x.length) +
        C * Tp.eval (i + 1 + x.length),
      (F M ei eo)^[n] (some ⟨some (.inr .loop), (v, o),
        L M [] (a :: Ar) (List.replicate i true) x.reverse O [] [] (fun _ => [])⟩) =
      some ⟨some (.inr .loop), (M.initialState, none),
        L M [] Ar (List.replicate (i + 1) true) x.reverse
          ((g (List.replicate i true ++ false :: x)).reverse ++ O) [] [] (fun _ => [])⟩ := by
  set z := List.replicate i true ++ false :: x with hz
  have hzl : z.length = i + 1 + x.length := by simp [hz]; omega
  obtain ⟨nM, hnM, hrun⟩ := hM z
  have hl := hlen z
  rw [hzl] at hnM hl
  have h0 := Ploop_s M ei eo [] Ar (List.replicate i true) x.reverse O [] [] (fun _ => []) v o a
  have h1 := Pcx M ei eo [] Ar (List.replicate i true) x.reverse O [] [] (fun _ => []) v (some a)
  refine ⟨_, ?_, (iter_chain h0 (iter_chain h1 (iter_chain (Pbx M ei eo _ _ _ _ _ _ _ _ _ _)
    (iter_chain (Pci M ei eo _ _ _ _ _ _ _ _ _ _) (iter_chain (Pbi M ei eo _ _ _ _ _ _ _ _ _ _)
      (iter_chain (runM M ei eo g z _ _ _ _ _ ?_ nM hrun)
        (Pmo M ei eo _ _ _ _ _ _ _ _ _ _))))))).trans ?_⟩
  · simp only [haltList_stk, Function.update_self, List.length_map, List.length_append,
      List.length_reverse, List.length_nil, List.length_replicate, Nat.add_zero]
    omega
  · funext k
    by_cases h : k = M.k₀
    · subst h; simp [hz, List.map_reverse]
    · simp [h]
  · simp only [liftCM, haltList_stk, Function.update_idem, nil_updM, Function.update_self,
      List.map_map, Equiv.self_comp_symm, List.map_id, List.append_nil, List.reverse_reverse,
      List.reverse_replicate, List.replicate_succ]
    rfl

include hM hlen in
theorem iter_run (x : List Bool) (Lb : ℕ) (k : ℕ) : ∀ (i : ℕ) (O : List Bool),
    i + k + x.length ≤ Lb →
    ∃ n ≤ k * (3 * Lb + 4 + Tp.eval Lb + C * Tp.eval Lb),
      (F M ei eo)^[n] (some ⟨some (.inr .loop), (M.initialState, none),
        L M [] (List.replicate k true) (List.replicate i true) x.reverse O [] [] (fun _ => [])⟩) =
      some ⟨some (.inr .loop), (M.initialState, none),
        L M [] [] (List.replicate (i + k) true) x.reverse
          (((List.range' i k).flatMap fun j => g (List.replicate j true ++ false :: x)).reverse
            ++ O) [] [] (fun _ => [])⟩ ∧
      ((List.range' i k).flatMap fun j => g (List.replicate j true ++ false :: x)).length ≤
        k * (Lb + C * Tp.eval Lb) := by
  induction k with
  | zero => intro i O _; exact ⟨0, by simp, by simp, by simp⟩
  | succ k ih =>
    intro i O hb
    obtain ⟨n1, hn1, h1⟩ := iter1 M ei eo g Tp C hM hlen i x (List.replicate k true) O true
      M.initialState none
    obtain ⟨n2, hn2, h2, hl2⟩ := ih (i + 1) ((g (List.replicate i true ++ false :: x)).reverse ++ O)
      (by omega)
    have hT : Tp.eval (i + 1 + x.length) ≤ Tp.eval Lb := poly_eval_mono _ (by omega)
    have hCT : C * Tp.eval (i + 1 + x.length) ≤ C * Tp.eval Lb := Nat.mul_le_mul_left _ hT
    have hg := hlen (List.replicate i true ++ false :: x)
    simp only [List.length_append, List.length_replicate, List.length_cons] at hg
    have hg' : (g (List.replicate i true ++ false :: x)).length ≤ Lb + C * Tp.eval Lb := by
      have : i + (x.length + 1) = i + 1 + x.length := by omega
      rw [this] at hg; omega
    refine ⟨n2 + n1, ?_, ?_, ?_⟩
    · rw [Nat.succ_mul]; omega
    · rw [List.replicate_succ, Function.iterate_add_apply, h1, h2, List.range'_succ,
        List.flatMap_cons, List.reverse_append, List.append_assoc,
        show i + 1 + k = i + (k + 1) by omega]
    · rw [List.range'_succ, List.flatMap_cons, List.length_append, Nat.succ_mul]; omega

theorem lp_len (y : List Bool) : lpN y + (lpX y).length ≤ y.length := by
  induction y with
  | nil => simp [lpN, lpX]
  | cons b y ih =>
    cases b
    · rw [lpN_cons_false, lpX_cons_false]; simp
    · rw [lpN_cons_true, lpX_cons_true]; simp; omega

theorem initList_loop (y : List Bool) :
    initList (loopTM M ei eo) y =
      ⟨some (.inr .rd), (M.initialState, none), L M y [] [] [] [] [] [] (fun _ => [])⟩ := by
  simp only [initList]
  congr 1
  funext j
  rcases j with ((_ | _ | _ | _ | _ | _ | _) | j) <;> rfl

theorem haltList_loop (y : List Bool) :
    haltList (loopTM M ei eo) y =
      ⟨none, (M.initialState, none), L M [] [] [] [] [] [] y (fun _ => [])⟩ := by
  simp only [haltList]
  congr 1
  funext j
  rcases j with ((_ | _ | _ | _ | _ | _ | _) | j) <;> rfl

include hM hlen in
theorem loop_run (y : List Bool) :
    ∃ n ≤ 2 * y.length + 6 + y.length * (4 * y.length + 4 + Tp.eval y.length +
        2 * C * Tp.eval y.length),
      (F M ei eo)^[n] (some (initList (loopTM M ei eo) y)) =
        some (haltList (loopTM M ei eo) (loopF g y)) := by
  rw [initList_loop, haltList_loop]
  have hlp := lp_len y
  obtain ⟨n0, hn0, h0⟩ := Prd M ei eo y [] [] [] [] [] [] (fun _ => []) M.initialState none
  simp only [List.append_nil] at h0
  obtain ⟨n1, hn1, h1, hl1⟩ := iter_run M ei eo g Tp C hM hlen (lpX y) y.length (lpN y) 0 []
    (by omega)
  simp only [List.append_nil, Nat.zero_add] at h1
  have h2 := Ploop_n M ei eo [] (List.replicate (lpN y) true) (lpX y).reverse
    ((List.range' 0 (lpN y)).flatMap fun j => g (List.replicate j true ++ false :: lpX y)).reverse
    [] [] (fun _ => []) M.initialState none
  have h3 := Pfo M ei eo [] [] (List.replicate (lpN y) true) (lpX y).reverse
    ((List.range' 0 (lpN y)).flatMap fun j => g (List.replicate j true ++ false :: lpX y)).reverse
    [] [] (fun _ => []) M.initialState none
  have h4 := PcI M ei eo [] [] (List.replicate (lpN y) true) (lpX y).reverse [] []
    (((List.range' 0 (lpN y)).flatMap
      fun j => g (List.replicate j true ++ false :: lpX y)).reverse.reverse ++ [])
    (fun _ => []) M.initialState none
  have h5 := PcX M ei eo [] [] [] (lpX y).reverse [] []
    (((List.range' 0 (lpN y)).flatMap
      fun j => g (List.replicate j true ++ false :: lpX y)).reverse.reverse ++ [])
    (fun _ => []) M.initialState none
  refine ⟨_, ?_, (iter_chain h0 (iter_chain h1 (iter_chain h2 (iter_chain h3
    (iter_chain h4 h5))))).trans ?_⟩
  · simp only [List.length_reverse, List.length_replicate]
    have hm : lpN y * (3 * y.length + 4 + Tp.eval y.length + C * Tp.eval y.length) ≤
        y.length * (3 * y.length + 4 + Tp.eval y.length + C * Tp.eval y.length) :=
      Nat.mul_le_mul_right _ (by omega)
    have hm2 : lpN y * (y.length + C * Tp.eval y.length) ≤
        y.length * (y.length + C * Tp.eval y.length) :=
      Nat.mul_le_mul_right _ (by omega)
    have e : y.length * (4 * y.length + 4 + Tp.eval y.length + 2 * C * Tp.eval y.length) =
        y.length * (3 * y.length + 4 + Tp.eval y.length + C * Tp.eval y.length) +
          y.length * (y.length + C * Tp.eval y.length) := by ring
    rw [e]
    omega
  · simp only [List.reverse_reverse, List.append_nil, loopF, List.range_eq_range']
    rfl

end run

end LoopTM


/-- **Bounded loop**: if `g` is polynomial-time computable, so is
`loopF g (1ⁿ 0 x) = g (0 x) ++ g (1 0 x) ++ … ++ g (1ⁿ⁻¹ 0 x)`. -/
noncomputable def loopComputable {g : List Bool → List Bool}
    (h : TM2ComputableInPolyTime strEnc strEnc g) :
    TM2ComputableInPolyTime strEnc strEnc (loopF g) where
  tm := LoopTM.loopTM h.tm h.inputAlphabet h.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 6 + Polynomial.X * (4 * Polynomial.X + 4 + h.time +
    2 * (pushTotal h.tm : Polynomial ℕ) * h.time)
  outputsFun y := by
    have hM : ∀ z : List Bool, ∃ n ≤ h.time.eval z.length, (flip bind (TM2.step h.tm.m))^[n]
        (some (initList h.tm (z.map h.inputAlphabet.symm))) =
          some (haltList h.tm ((g z).map h.outputAlphabet.symm)) := by
      intro z
      have hz := h.outputsFun z
      have e := hz.evals_in_steps
      simp only [Option.map_some] at e
      exact ⟨hz.steps, hz.steps_le_m, e⟩
    have hlen : ∀ z : List Bool, (g z).length ≤ z.length + pushTotal h.tm * h.time.eval z.length :=
      fun z => outLen_bound h z
    have H := LoopTM.loop_run h.tm h.inputAlphabet h.outputAlphabet g h.time (pushTotal h.tm)
      hM hlen y
    refine
      { steps := Classical.choose H
        evals_in_steps := ?_
        steps_le_m := ?_ }
    · have hr := (Classical.choose_spec H).2
      erw [List.map_id, List.map_id, Option.map_some]
      exact hr
    · have hn := (Classical.choose_spec H).1
      simp only [strEnc, List.length_map]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_natCast, Polynomial.eval_ofNat, Nat.cast_id]
      exact hn

end PvnpReal
