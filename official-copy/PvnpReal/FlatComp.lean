/-
  PvnpReal.FlatComp — compiling a normal-form program `NProg` into a flat program `Pc`
  (one flat instruction per (statement node, variable value) pair), and the **micro-simulation**:
  every `nrunFor` run of the `NProg` is mirrored by iterating the abstract flat step `mstep`,
  with at most `D` micro-steps per macro-step.
-/
import PvnpReal.FlatSem
import PvnpReal.NormalForm

set_option linter.unusedSimpArgs false

namespace PvnpReal

open Turing Computability

deriving instance DecidableEq for NStmt

namespace Flat

def subs : NStmt → List NStmt
  | .push k f q => .push k f q :: subs q
  | .peek k f q => .peek k f q :: subs q
  | .pop k f q => .pop k f q :: subs q
  | .load f q => .load f q :: subs q
  | .branch f q₁ q₂ => .branch f q₁ q₂ :: (subs q₁ ++ subs q₂)
  | .goto f => [.goto f]
  | .halt => [.halt]

def depth : NStmt → ℕ
  | .push _ _ q => depth q + 1
  | .peek _ _ q => depth q + 1
  | .pop _ _ q => depth q + 1
  | .load _ q => depth q + 1
  | .branch _ q₁ q₂ => max (depth q₁) (depth q₂) + 1
  | .goto _ => 1
  | .halt => 1

theorem self_mem_subs (q : NStmt) : q ∈ subs q := by cases q <;> simp [subs]

theorem getD_flatMap_uniform {W : ℕ} (g : ℕ → List ℕ) (hg : ∀ s, (g s).length = W) {f : ℕ}
    (hf : f < W) : ∀ (n s : ℕ), ((List.range n).flatMap g).getD (s * W + f) 0 =
      if s < n then (g s).getD f 0 else 0 := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    have hlen : ((List.range n).flatMap g).length = n * W := by
      simp [List.length_flatMap, hg]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp only [List.getD_eq_getElem?_getD]
    by_cases hs : s < n
    · have hlt : s * W + f < n * W := by
        have : (s + 1) * W ≤ n * W := Nat.mul_le_mul_right _ hs
        nlinarith
      rw [List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, ih, if_pos hs,
        if_pos (by omega), List.getD_eq_getElem?_getD]
    · have hnW : n * W ≤ s * W := Nat.mul_le_mul_right _ (by omega)
      rw [List.getElem?_append_right (by omega), hlen]
      by_cases he : s = n
      · subst he
        rw [if_pos (by omega), show s * W + f - s * W = f by omega]
      · have : (n + 1) * W ≤ s * W := Nat.mul_le_mul_right _ (by omega)
        have e : (n + 1) * W = n * W + W := by ring
        rw [if_neg (by omega), List.getElem?_eq_none (by rw [hg]; omega)]
        rfl

def SGood (B : ℕ) (S : ℕ → List ℕ) : Prop := ∀ k, ∀ a ∈ S k, a < B

/-- Compilation parameters: the program, a bound `V` on variable values, a bound `B` on stack
symbols, and the number `nK` of stacks. -/
structure Prm where
  p : NProg
  V : ℕ
  B : ℕ
  nK : ℕ

namespace Prm

variable (P : Prm)

def nodes : List NStmt := P.p.m.flatMap subs ++ [.halt]
def st (q : NStmt) (v : ℕ) : ℕ := P.nodes.idxOf q * P.V + v
def CHK : ℕ := P.nodes.length * P.V
def Wd : ℕ := P.B + 5
def root (l : ℕ) : NStmt := P.p.m.getD l .halt
def tbl (g : ℕ → ℕ) : List ℕ := (List.range (P.B + 1)).map g

def instr (v : ℕ) : NStmt → List ℕ
  | .push k f q => [1, k, f.getD v 0, P.st q v]
  | .peek k f q => [3, k, 0, 0] ++ P.tbl (fun o => P.st q ((f.getD v []).getD o 0))
  | .pop k f q => [2, k, 0, 0] ++ P.tbl (fun o => P.st q ((f.getD v []).getD o 0))
  | .load f q => [4, 0, 0, P.st q (f.getD v 0)]
  | .branch f q₁ q₂ => [4, 0, 0, P.st (cond (f.getD v false) q₁ q₂) v]
  | .goto f => [4, 0, 0, P.st (P.root (f.getD v 0)) v]
  | .halt => [4, 0, 0, P.CHK]

def chkI : List ℕ := [3, P.p.k1, 0, 0] ++
  P.tbl (fun o => if o ≠ 0 ∧ P.p.outT.getD (o - 1) false = true then P.CHK + 1 else P.CHK + 2)

def blk (s : ℕ) : List ℕ :=
  if s < P.CHK then P.instr (s % P.V) (P.nodes.getD (s / P.V) .halt)
  else if s = P.CHK then P.chkI else if s = P.CHK + 1 then [5] else [0]

def pad (l : List ℕ) : List ℕ := (List.range P.Wd).map (fun i => l.getD i 0)

def start : ℕ := P.st (P.root P.p.main) P.p.init

/-- **The compiled flat program.** -/
def Pc : List ℕ := [P.nK, P.Wd, P.p.k0, P.p.inT.getD 0 0, P.p.inT.getD 1 0, P.start] ++
  (List.range (P.CHK + 3)).flatMap (fun s => P.pad (P.blk s))

def fcfg (c : NCfg) : MC :=
  ⟨match c.l with | some l => P.st (P.root l) c.var | none => P.CHK, c.stk⟩

/-- Local well-formedness of a node. -/
def NWF : NStmt → Prop
  | .push k f _ => k < P.nK ∧ ∀ v, f.getD v 0 < P.B
  | .peek k f _ => k < P.nK ∧ ∀ v o, (f.getD v []).getD o 0 < P.V
  | .pop k f _ => k < P.nK ∧ ∀ v o, (f.getD v []).getD o 0 < P.V
  | .load f _ => ∀ v, f.getD v 0 < P.V
  | _ => True

theorem pad_len (l : List ℕ) : (P.pad l).length = P.Wd := by simp [pad]

theorem pad_getD (l : List ℕ) {f : ℕ} (hf : f < P.Wd) : (P.pad l).getD f 0 = l.getD f 0 := by
  simp [pad, List.getD_eq_getElem?_getD, hf]

theorem Pc_W : P.Pc.getD 1 0 = P.Wd := rfl

theorem pf_eq (s : ℕ) {f : ℕ} (hf : f < P.Wd) :
    pf P.Pc s f = if s < P.CHK + 3 then (P.blk s).getD f 0 else 0 := by
  unfold pf
  rw [Pc_W]
  have : P.Pc.getD (6 + s * P.Wd + f) 0 =
      ((List.range (P.CHK + 3)).flatMap (fun s => P.pad (P.blk s))).getD (s * P.Wd + f) 0 := by
    unfold Pc
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp; omega)]
    congr 2; simp; omega
  rw [this, getD_flatMap_uniform _ (fun s => P.pad_len _) hf]
  split
  · rw [P.pad_getD _ hf]
  · rfl

theorem nodes_getD_idx {q : NStmt} (hq : q ∈ P.nodes) : P.nodes.getD (P.nodes.idxOf q) .halt = q := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hq)]
  exact List.getElem_idxOf _

theorem st_lt {q : NStmt} (hq : q ∈ P.nodes) {v : ℕ} (hv : v < P.V) : P.st q v < P.CHK := by
  have h1 := List.idxOf_lt_length_of_mem hq
  unfold st CHK
  have : (P.nodes.idxOf q + 1) * P.V ≤ P.nodes.length * P.V := Nat.mul_le_mul_right _ h1
  nlinarith

theorem blk_st {q : NStmt} (hq : q ∈ P.nodes) {v : ℕ} (hv : v < P.V) :
    P.blk (P.st q v) = P.instr v q := by
  unfold blk
  rw [if_pos (P.st_lt hq hv)]
  have hV : 0 < P.V := by omega
  have e1 : P.st q v % P.V = v := by
    unfold st; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  have e2 : P.st q v / P.V = P.nodes.idxOf q := by
    unfold st; rw [Nat.add_comm, Nat.add_mul_div_right _ _ hV, Nat.div_eq_of_lt hv, Nat.zero_add]
  rw [e1, e2, P.nodes_getD_idx hq]

theorem pf_st {q : NStmt} (hq : q ∈ P.nodes) {v : ℕ} (hv : v < P.V) {f : ℕ} (hf : f < P.Wd) :
    pf P.Pc (P.st q v) f = (P.instr v q).getD f 0 := by
  rw [P.pf_eq _ hf, if_pos (by have := P.st_lt hq hv; omega), P.blk_st hq hv]

theorem tbl_getD (g : ℕ → ℕ) {o : ℕ} (ho : o ≤ P.B) : (P.tbl g).getD o 0 = g o := by
  simp [tbl, List.getD_eq_getElem?_getD, show o < P.B + 1 by omega]

theorem oc_le {B : ℕ} {l : List ℕ} (h : ∀ a ∈ l, a < B) : oc l.head? ≤ B := by
  cases l with
  | nil => simp [oc]
  | cons a r => simp [oc]; exact h a (by simp)

theorem getD_four (a b c d : ℕ) (l : List ℕ) (o : ℕ) : ([a, b, c, d] ++ l).getD (4 + o) 0 = l.getD o 0 := by
  simp [List.getD_eq_getElem?_getD, show 4 + o = o + 4 by omega]

theorem mem_nodes_root (l : ℕ) : ∀ q ∈ subs (P.root l), q ∈ P.nodes := by
  intro q hq
  unfold root at hq
  unfold nodes
  by_cases hl : l < P.p.m.length
  · rw [List.getD_eq_getElem _ _ hl] at hq
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hl, hq⟩)
  · rw [List.getD_eq_default _ _ (by omega)] at hq
    simp [subs] at hq; subst hq; simp

theorem sgood_update_tail {B : ℕ} {S : ℕ → List ℕ} (hS : SGood B S) (k : ℕ) :
    SGood B (Function.update S k (S k).tail) := by
  intro j a ha
  by_cases e : j = k
  · subst e; rw [Function.update_self] at ha; exact hS _ _ (List.mem_of_mem_tail ha)
  · rw [Function.update_of_ne e] at ha; exact hS _ _ ha

/-- **Micro-simulation of one statement tree.** -/
theorem micro (hN : ∀ q ∈ P.nodes, P.NWF q) (q : NStmt) (hq : ∀ q' ∈ subs q, q' ∈ P.nodes) :
    ∀ v < P.V, ∀ S, SGood P.B S → ∃ n ≤ depth q, (mstep P.Pc)^[n] ⟨P.st q v, S⟩ =
      P.fcfg (nAux q v S) ∧ (nAux q v S).var < P.V ∧ SGood P.B (nAux q v S).stk := by
  have hm : q ∈ P.nodes := hq _ (self_mem_subs _)
  induction q with
  | push k f q ih =>
    intro v hv S hS
    obtain ⟨hk, hf⟩ := hN _ hm
    have pfi : ∀ i, i < 4 → pf P.Pc (P.st (.push k f q) v) i =
        (P.instr v (.push k f q)).getD i 0 := fun i hi => P.pf_st hm hv (by simp [Wd]; omega)
    have t : pf P.Pc (P.st (.push k f q) v) 0 = 1 := by rw [pfi 0 (by omega)]; rfl
    have p1 : pf P.Pc (P.st (.push k f q) v) 1 = k := by rw [pfi 1 (by omega)]; rfl
    have p2 : pf P.Pc (P.st (.push k f q) v) 2 = f.getD v 0 := by rw [pfi 2 (by omega)]; rfl
    have p3 : pf P.Pc (P.st (.push k f q) v) 3 = P.st q v := by rw [pfi 3 (by omega)]; rfl
    have hS' : SGood P.B (Function.update S k (f.getD v 0 :: S k)) := by
      intro j a ha
      by_cases e : j = k
      · subst e; rw [Function.update_self] at ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hf v
        · exact hS _ _ ha
      · rw [Function.update_of_ne e] at ha; exact hS _ _ ha
    have hq' : ∀ q' ∈ subs q, q' ∈ P.nodes := fun q' h' => hq q' (by simp [subs, h'])
    obtain ⟨n, hn, e, r⟩ := ih hq' (hq' _ (self_mem_subs _)) v hv _ hS'
    refine ⟨n + 1, by simp [depth]; omega, ?_, r⟩
    rw [Function.iterate_succ_apply, mstep_push (c := ⟨P.st (.push k f q) v, S⟩) t]
    dsimp only
    rw [p1, p2, p3, e]; rfl
  | peek k f q ih =>
    intro v hv S hS
    obtain ⟨hk, hf⟩ := hN _ hm
    have ho := oc_le (hS k)
    have t : pf P.Pc (P.st (.peek k f q) v) 0 = 3 := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p1 : pf P.Pc (P.st (.peek k f q) v) 1 = k := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p4 : pf P.Pc (P.st (.peek k f q) v) (4 + oc (S k).head?) =
        P.st q ((f.getD v []).getD (oc (S k).head?) 0) := by
      rw [P.pf_st hm hv (by simp [Wd]; omega)]
      show ([3, k, 0, 0] ++ P.tbl _).getD _ 0 = _
      rw [getD_four, P.tbl_getD _ ho]
    have hq' : ∀ q' ∈ subs q, q' ∈ P.nodes := fun q' h' => hq q' (by simp [subs, h'])
    obtain ⟨n, hn, e, r⟩ := ih hq' (hq' _ (self_mem_subs _)) _ (hf v _) S hS
    refine ⟨n + 1, by simp [depth]; omega, ?_, r⟩
    rw [Function.iterate_succ_apply, mstep_peek (c := ⟨P.st (.peek k f q) v, S⟩) t]
    dsimp only
    rw [p1, p4, e]; rfl
  | pop k f q ih =>
    intro v hv S hS
    obtain ⟨hk, hf⟩ := hN _ hm
    have ho := oc_le (hS k)
    have t : pf P.Pc (P.st (.pop k f q) v) 0 = 2 := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p1 : pf P.Pc (P.st (.pop k f q) v) 1 = k := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p4 : pf P.Pc (P.st (.pop k f q) v) (4 + oc (S k).head?) =
        P.st q ((f.getD v []).getD (oc (S k).head?) 0) := by
      rw [P.pf_st hm hv (by simp [Wd]; omega)]
      show ([2, k, 0, 0] ++ P.tbl _).getD _ 0 = _
      rw [getD_four, P.tbl_getD _ ho]
    have hq' : ∀ q' ∈ subs q, q' ∈ P.nodes := fun q' h' => hq q' (by simp [subs, h'])
    obtain ⟨n, hn, e, r⟩ := ih hq' (hq' _ (self_mem_subs _)) _ (hf v _) _ (sgood_update_tail hS k)
    refine ⟨n + 1, by simp [depth]; omega, ?_, r⟩
    rw [Function.iterate_succ_apply, mstep_pop (c := ⟨P.st (.pop k f q) v, S⟩) t]
    dsimp only
    rw [p1, p4, e]; rfl
  | load f q ih =>
    intro v hv S hS
    have hf : ∀ v, f.getD v 0 < P.V := hN _ hm
    have t : pf P.Pc (P.st (.load f q) v) 0 = 4 := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p3 : pf P.Pc (P.st (.load f q) v) 3 = P.st q (f.getD v 0) := by
      rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have hq' : ∀ q' ∈ subs q, q' ∈ P.nodes := fun q' h' => hq q' (by simp [subs, h'])
    obtain ⟨n, hn, e, r⟩ := ih hq' (hq' _ (self_mem_subs _)) _ (hf v) S hS
    refine ⟨n + 1, by simp [depth]; omega, ?_, r⟩
    rw [Function.iterate_succ_apply, mstep_nop (c := ⟨P.st (.load f q) v, S⟩) t]
    dsimp only
    rw [p3, e]; rfl
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v hv S hS
    have t : pf P.Pc (P.st (.branch f q₁ q₂) v) 0 = 4 := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p3 : pf P.Pc (P.st (.branch f q₁ q₂) v) 3 = P.st (cond (f.getD v false) q₁ q₂) v := by
      rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have h1 : ∀ q' ∈ subs q₁, q' ∈ P.nodes := fun q' h' => hq q' (by simp [subs, h'])
    have h2 : ∀ q' ∈ subs q₂, q' ∈ P.nodes := fun q' h' => hq q' (by simp [subs, h'])
    cases hb : f.getD v false with
    | true =>
      obtain ⟨n, hn, e, r⟩ := ih₁ h1 (h1 _ (self_mem_subs _)) v hv S hS
      have hnb : nAux (.branch f q₁ q₂) v S = nAux q₁ v S := by simp only [nAux, hb, cond_true]
      rw [hnb]
      refine ⟨n + 1, by simp [depth]; omega, ?_, r⟩
      rw [Function.iterate_succ_apply, mstep_nop (c := ⟨P.st (.branch f q₁ q₂) v, S⟩) t]
      dsimp only
      rw [p3, hb]; exact e
    | false =>
      obtain ⟨n, hn, e, r⟩ := ih₂ h2 (h2 _ (self_mem_subs _)) v hv S hS
      have hnb : nAux (.branch f q₁ q₂) v S = nAux q₂ v S := by simp only [nAux, hb, cond_false]
      rw [hnb]
      refine ⟨n + 1, by simp [depth]; omega, ?_, r⟩
      rw [Function.iterate_succ_apply, mstep_nop (c := ⟨P.st (.branch f q₁ q₂) v, S⟩) t]
      dsimp only
      rw [p3, hb]; exact e
  | goto f =>
    intro v hv S hS
    have t : pf P.Pc (P.st (.goto f) v) 0 = 4 := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p3 : pf P.Pc (P.st (.goto f) v) 3 = P.st (P.root (f.getD v 0)) v := by
      rw [P.pf_st hm hv (by simp [Wd])]; rfl
    refine ⟨1, by simp [depth], ?_, hv, hS⟩
    rw [Function.iterate_one, mstep_nop (c := ⟨P.st (.goto f) v, S⟩) t]
    dsimp only
    rw [p3]; rfl
  | halt =>
    intro v hv S hS
    have t : pf P.Pc (P.st .halt v) 0 = 4 := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    have p3 : pf P.Pc (P.st .halt v) 3 = P.CHK := by rw [P.pf_st hm hv (by simp [Wd])]; rfl
    refine ⟨1, by simp [depth], ?_, hv, hS⟩
    rw [Function.iterate_one, mstep_nop (c := ⟨P.st .halt v, S⟩) t]
    dsimp only
    rw [p3]; rfl

def D : ℕ := (P.nodes.map depth).sum

theorem depth_le {q : NStmt} (hq : q ∈ P.nodes) : depth q ≤ P.D :=
  List.le_sum_of_mem (List.mem_map_of_mem hq)

/-- **Macro-simulation**: a halting clocked run of `T` steps costs at most `D·T` micro-steps. -/
theorem macroSim (hN : ∀ q ∈ P.nodes, P.NWF q) : ∀ (T : ℕ) (c h : NCfg), c.var < P.V →
    SGood P.B c.stk → nrunFor P.p T c = some h →
    ∃ n ≤ P.D * T, (mstep P.Pc)^[n] (P.fcfg c) = P.fcfg h ∧ h.l = none ∧ SGood P.B h.stk := by
  intro T
  induction T with
  | zero =>
    rintro ⟨l, v, S⟩ h hv hS e
    simp only [nrunFor] at e
    split at e
    · next hl =>
      injection e with e; subst e; exact ⟨0, by simp, rfl, hl, hS⟩
    · simp at e
  | succ T ih =>
    rintro ⟨l, v, S⟩ h hv hS e
    cases l with
    | none => simp [nrunFor] at e; subst e; exact ⟨0, by simp, rfl, rfl, hS⟩
    | some l =>
      simp only [nrunFor] at e
      obtain ⟨n1, hn1, e1, r1, r2⟩ := P.micro hN (P.root l) (P.mem_nodes_root l) v hv S hS
      obtain ⟨n2, hn2, e2, r3, r4⟩ := ih _ h r1 r2 e
      refine ⟨n2 + n1, ?_, ?_, r3, r4⟩
      · have := P.depth_le (P.mem_nodes_root l _ (self_mem_subs _)); rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply]
        show (mstep P.Pc)^[n2] ((mstep P.Pc)^[n1] ⟨P.st (P.root l) v, S⟩) = _
        rw [e1, e2]

theorem blk_chk : P.blk P.CHK = P.chkI := by simp [blk]
theorem blk_acc : P.blk (P.CHK + 1) = [5] := by simp [blk]
theorem blk_rej : P.blk (P.CHK + 2) = [0] := by simp [blk]

theorem chk_step (S : ℕ → List ℕ) (hS : SGood P.B S) : mstep P.Pc ⟨P.CHK, S⟩ =
    ⟨if oc (S P.p.k1).head? ≠ 0 ∧ P.p.outT.getD (oc (S P.p.k1).head? - 1) false = true then
      P.CHK + 1 else P.CHK + 2, S⟩ := by
  have ho := oc_le (hS P.p.k1)
  have t : pf P.Pc P.CHK 0 = 3 := by
    rw [P.pf_eq _ (by simp [Wd]), if_pos (by omega), blk_chk]; rfl
  have p1 : pf P.Pc P.CHK 1 = P.p.k1 := by
    rw [P.pf_eq _ (by simp [Wd]), if_pos (by omega), blk_chk]; rfl
  rw [mstep_peek (c := ⟨P.CHK, S⟩) t]
  dsimp only
  rw [p1, P.pf_eq _ (by simp [Wd]; omega), if_pos (by omega), blk_chk]
  unfold chkI
  rw [getD_four, P.tbl_getD _ ho]

theorem acc_fix (S : ℕ → List ℕ) : mstep P.Pc ⟨P.CHK + 1, S⟩ = ⟨P.CHK + 1, S⟩ := by
  have t : pf P.Pc (P.CHK + 1) 0 = 5 := by
    rw [P.pf_eq _ (by simp [Wd]), if_pos (by omega), blk_acc]; rfl
  exact mstep_other (c := ⟨P.CHK + 1, S⟩) (by rw [t]; omega) (by rw [t]; omega) (by rw [t]; omega)
    (by rw [t]; omega)

theorem rej_fix (S : ℕ → List ℕ) : mstep P.Pc ⟨P.CHK + 2, S⟩ = ⟨P.CHK + 2, S⟩ := by
  have t : pf P.Pc (P.CHK + 2) 0 = 0 := by
    rw [P.pf_eq _ (by simp [Wd]), if_pos (by omega), blk_rej]; rfl
  exact mstep_other (c := ⟨P.CHK + 2, S⟩) (by rw [t]; omega) (by rw [t]; omega) (by rw [t]; omega)
    (by rw [t]; omega)

theorem tag_acc : pf P.Pc (P.CHK + 1) 0 = 5 := by
  rw [P.pf_eq _ (by simp [Wd]), if_pos (by omega), blk_acc]; rfl
theorem tag_rej : pf P.Pc (P.CHK + 2) 0 = 0 := by
  rw [P.pf_eq _ (by simp [Wd]), if_pos (by omega), blk_rej]; rfl

/-- Static well-formedness: every push/pop/peek instruction names a stack `< nK`. -/
theorem stk_ok (hN : ∀ q ∈ P.nodes, P.NWF q) (hk1 : P.p.k1 < P.nK) :
    ∀ s, pf P.Pc s 0 = 1 ∨ pf P.Pc s 0 = 2 ∨ pf P.Pc s 0 = 3 → pf P.Pc s 1 < P.nK := by
  intro s hs
  rw [P.pf_eq _ (by simp [Wd])] at hs ⊢
  by_cases h3 : s < P.CHK + 3
  · rw [if_pos h3] at hs ⊢
    by_cases hc : s < P.CHK
    · have hV : 0 < P.V := by
        rcases Nat.eq_zero_or_pos P.V with h | h
        · simp [CHK, h] at hc
        · exact h
      have hi : s / P.V < P.nodes.length := (Nat.div_lt_iff_lt_mul hV).2 hc
      have hmem : P.nodes.getD (s / P.V) .halt ∈ P.nodes := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      have hw := hN _ hmem
      unfold blk at hs ⊢
      rw [if_pos hc] at hs ⊢
      generalize P.nodes.getD (s / P.V) .halt = q at hs hw
      cases q <;> simp_all [instr, NWF, getD_four]
    · by_cases e : s = P.CHK
      · subst e; rw [blk_chk]; exact hk1
      · by_cases e1 : s = P.CHK + 1
        · subst e1; rw [blk_acc] at hs; simp at hs
        · have e2 : s = P.CHK + 2 := by omega
          subst e2; rw [blk_rej] at hs; simp at hs
  · rw [if_neg h3] at hs; omega

end Prm

end Flat

end PvnpReal
