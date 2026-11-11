/-
  PvnpReal.CircOneHot — straight-line programs over a finite value list `U` (one-hot encoded),
  compiled to bit programs and hence to circuits. Each node is either an input-bit node
  (`val j = f (x i)`) or a function node (`val j = F (vals of ≤ c earlier nodes)`).
  `hasCircuit_aprog`: a program with `N` nodes gives, for any output node `o` and predicate `Pr`,
  a circuit for `x ↦ Pr (val x o)` with at most `2 + (N·|U| + 1)·4·2^(c·|U|)` gates.
-/
import PvnpReal.CircShannon

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

theorem getD_range_map (N : ℕ) (f : ℕ → Bool) {i : ℕ} (hi : i < N) :
    ((List.range N).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem nStep_eq (v : List Bool) (nd : BNode) :
    nStep v nd = v ++ [nd.2 (nd.1.map (fun d => v.getD d false))] := rfl

/-- Evaluation of a bit program given in `range`/`map` form, against a closed-form value function. -/
theorem nval_range (x : List Bool) (nodeAt : ℕ → BNode) (bv : ℕ → Bool)
    (hx : ∀ i < x.length, bv i = x.getD i false) :
    ∀ N : ℕ, (∀ p < N, (∀ d ∈ (nodeAt p).1, d < x.length + p) ∧
      bv (x.length + p) = (nodeAt p).2 ((nodeAt p).1.map bv)) →
    nval x ((List.range N).map nodeAt) = (List.range (x.length + N)).map bv
  | 0, _ => by
    apply List.ext_getElem (by simp [nval])
    intro i h1 h2
    simp only [nval, List.map_nil, List.foldl_nil, List.getElem_map, List.getElem_range]
    have hi : i < x.length := by simpa [nval] using h1
    rw [hx i hi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  | N + 1, h => by
    have ih := nval_range x nodeAt bv hx N (fun p hp => h p (by omega))
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      show nval x ((List.range N).map nodeAt ++ [nodeAt N]) =
        nStep (nval x ((List.range N).map nodeAt)) (nodeAt N) by simp [nval, List.foldl_append],
      ih, nStep_eq]
    rw [show x.length + (N + 1) = (x.length + N) + 1 by omega, List.range_succ, List.map_append]
    obtain ⟨hd, he⟩ := h N (by omega)
    simp only [List.map_cons, List.map_nil, he]
    congr 2
    apply congrArg
    apply List.map_congr_left
    intro d hdd
    rw [getD_range_map _ _ (hd d hdd)]

/-! ### Programs over a finite value list -/

inductive ANode (α : Type) where
  | inp (i : ℕ) (f : Bool → α)
  | fn (ds : List ℕ) (F : List α → α)

section OneHot

variable {α : Type} (U : List α) (dflt : α)

noncomputable def oh (a : α) : List Bool := U.map (fun b => decide (a = b))

noncomputable def ohDec (bs : List Bool) : α := U.getD (bs.idxOf true) dflt

noncomputable def ohDecs (k : ℕ) (bs : List Bool) : List α :=
  (List.range k).map (fun i => ohDec U dflt ((bs.drop (i * U.length)).take U.length))

def ohBlk (n d : ℕ) : List ℕ := (List.range U.length).map (fun u => n + d * U.length + u)

noncomputable def bnodeOf (n : ℕ) (a : ANode α) (u : ℕ) : BNode :=
  match a with
  | .inp i f => ([i], fun bs => decide (f (bs.getD 0 false) = U.getD u dflt))
  | .fn ds F => (ds.flatMap (ohBlk U n), fun bs => decide (F (ohDecs U dflt ds.length bs) = U.getD u dflt))

noncomputable def anodeAt (n : ℕ) (as : List (ANode α)) (o : ℕ) (Pr : α → Prop) (p : ℕ) : BNode :=
  if p < as.length * U.length then
    match as[p / U.length]? with
    | some a => bnodeOf U dflt n a (p % U.length)
    | none => ([], fun _ => false)
  else (ohBlk U n o, fun bs => decide (Pr (ohDec U dflt bs)))

theorem oh_length (a : α) : (oh U a).length = U.length := by simp [oh]

theorem idxOf_oh (a : α) : ∀ U : List α, (oh U a).idxOf true = U.idxOf a
  | [] => rfl
  | b :: U => by
    have ih := idxOf_oh a U
    simp only [oh, List.map_cons] at ih ⊢
    by_cases h : a = b
    · subst h; simp [List.idxOf_cons]
    · simp [List.idxOf_cons, h, Ne.symm h, ih]

theorem ohDec_oh {a : α} (ha : a ∈ U) : ohDec U dflt (oh U a) = a := by
  rw [ohDec, idxOf_oh, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem ha)]
  simp [List.getElem_idxOf]

theorem oh_getD (a : α) {u : ℕ} (hu : u < U.length) :
    (oh U a).getD u false = decide (a = U.getD u dflt) := by
  simp [oh, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]

theorem flatMap_block {β : Type} (g : β → List Bool) (W : ℕ) (hg : ∀ b, (g b).length = W) :
    ∀ (L : List β) (i : ℕ) (hi : i < L.length), ((L.flatMap g).drop (i * W)).take W = g L[i]
  | [], i, hi => by simp at hi
  | b :: L, 0, _ => by
    simp only [List.flatMap_cons, Nat.zero_mul, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by rw [hg]), List.take_of_length_le (by rw [hg])]
  | b :: L, i + 1, hi => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show (i + 1) * W = (g b).length + i * W by rw [hg]; ring, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
    exact flatMap_block g W hg L i (by simpa using hi)

theorem ohDecs_flat (ds : List ℕ) (val : ℕ → α) (hU : ∀ d ∈ ds, val d ∈ U) :
    ohDecs U dflt ds.length (ds.flatMap (fun d => oh U (val d))) = ds.map val := by
  apply List.ext_getElem (by simp [ohDecs])
  intro i h1 h2
  simp only [ohDecs, List.getElem_map, List.getElem_range]
  rw [flatMap_block (fun d => oh U (val d)) U.length (fun b => oh_length U _) ds i (by simpa using h2),
    ohDec_oh U dflt (hU _ (List.getElem_mem _))]

include dflt in
/-- **One-hot programs are circuits.** `val x` is the value list of the program on input `x`,
characterised by the node equations. -/
theorem hasCircuit_aprog (n c : ℕ) (as : List (ANode α)) (hc1 : 1 ≤ c)
    (hinp : ∀ j (hj : j < as.length) i f, as[j] = .inp i f → i < n)
    (hfn : ∀ j (hj : j < as.length) ds F, as[j] = .fn ds F → (∀ d ∈ ds, d < j) ∧ ds.length ≤ c)
    (val : (Fin n → Bool) → ℕ → α)
    (hU : ∀ x, ∀ j < as.length, val x j ∈ U)
    (hvi : ∀ x j (hj : j < as.length) i f, as[j] = .inp i f →
      val x j = f ((List.ofFn x).getD i false))
    (hvf : ∀ x j (hj : j < as.length) ds F, as[j] = .fn ds F → val x j = F (ds.map (val x)))
    (o : ℕ) (ho : o < as.length) (Pr : α → Prop) :
    HasCircuit n (2 + (as.length * U.length + 1) * (4 * 2 ^ (c * U.length)))
      (fun x => decide (Pr (val x o))) := by
  have hW : 0 < U.length := List.length_pos_of_mem (hU (fun _ => false) o ho)
  set ns := (List.range (as.length * U.length + 1)).map (anodeAt U dflt n as o Pr) with hns
  have hlen : ns.length = as.length * U.length + 1 := by simp [hns]
  -- structural facts about node `p`
  have hdiv : ∀ d u, u < U.length → (d * U.length + u) / U.length = d ∧ (d * U.length + u) % U.length = u := by
    intro d u hu
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hu, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  have hblk : ∀ d e, d < e → ∀ v ∈ ohBlk U n d, v < n + e * U.length := by
    intro d e hde v hv
    simp only [ohBlk, List.mem_map, List.mem_range] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have : (d + 1) * U.length ≤ e * U.length := Nat.mul_le_mul_right _ hde
    simp only [Nat.add_mul, Nat.one_mul] at this; omega
  have hpj : ∀ p < as.length * U.length, p / U.length < as.length ∧ p / U.length * U.length ≤ p ∧ p % U.length < U.length := by
    intro p hp
    refine ⟨Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]), Nat.div_mul_le_self p U.length,
      Nat.mod_lt _ hW⟩
  -- structural facts: dependencies point backwards, fan-in ≤ c·U.length
  have hnodeEq : ∀ p (hpa : p < as.length * U.length), anodeAt U dflt n as o Pr p =
      bnodeOf U dflt n (as[p / U.length]'(hpj p hpa).1) (p % U.length) := by
    intro p hpa
    simp only [anodeAt, if_pos hpa, List.getElem?_eq_getElem (hpj p hpa).1]
  have hdeps : ∀ p < as.length * U.length + 1, ∀ d ∈ (anodeAt U dflt n as o Pr p).1, d < n + p := by
    intro p hp v hv
    by_cases hpa : p < as.length * U.length
    · obtain ⟨hj, hjp, hu⟩ := hpj p hpa
      rw [hnodeEq p hpa] at hv
      rcases ha : as[p / U.length] with ⟨i, f⟩ | ⟨ds, F⟩
      · rw [ha] at hv
        have hi := hinp _ hj i f ha
        simp only [bnodeOf, List.mem_singleton] at hv; omega
      · rw [ha] at hv
        obtain ⟨hds, -⟩ := hfn _ hj ds F ha
        simp only [bnodeOf, List.mem_flatMap] at hv
        obtain ⟨d, hd, hv⟩ := hv
        have := hblk d (p / U.length) (hds d hd) v hv; omega
    · simp only [anodeAt, if_neg hpa] at hv
      have := hblk o as.length ho v hv; omega
  have hblkl : ∀ d, (ohBlk U n d).length = U.length := fun d => by simp [ohBlk]
  have hcW : ∀ p, (anodeAt U dflt n as o Pr p).1.length ≤ c * U.length := by
    intro p
    have h1 : 1 ≤ c * U.length := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : U.length ≤ c * U.length := Nat.le_mul_of_pos_left _ (by omega)
    by_cases hpa : p < as.length * U.length
    · obtain ⟨hj, hjp, hu⟩ := hpj p hpa
      rw [hnodeEq p hpa]
      rcases ha : as[p / U.length] with ⟨i, f⟩ | ⟨ds, F⟩
      · simp [bnodeOf]; omega
      · obtain ⟨-, hdl⟩ := hfn _ hj ds F ha
        simp only [bnodeOf, List.length_flatMap, hblkl, List.map_const', List.sum_replicate,
          smul_eq_mul]
        exact Nat.mul_le_mul_right _ hdl
    · simp only [anodeAt, if_neg hpa, hblkl]; exact h2
  -- the closed-form bit values
  have key : ∀ x : Fin n → Bool,
      (nval (List.ofFn x) ns).getD (n + as.length * U.length) false = decide (Pr (val x o)) := by
    intro x
    let bv : ℕ → Bool := fun i =>
      if i < n then (List.ofFn x).getD i false
      else if i - n < as.length * U.length then (oh U (val x ((i - n) / U.length))).getD ((i - n) % U.length) false
      else decide (Pr (val x o))
    have hxl : (List.ofFn x).length = n := by simp
    have hbvb : ∀ d < as.length, (ohBlk U n d).map bv = oh U (val x d) := by
      intro d hd
      apply List.ext_getElem (by simp [ohBlk, oh_length])
      intro u h1 h2
      simp only [ohBlk, List.length_map, List.length_range] at h1
      simp only [ohBlk, List.getElem_map, List.getElem_range, bv]
      have : d * U.length + u < as.length * U.length := by
        have : (d + 1) * U.length ≤ as.length * U.length := Nat.mul_le_mul_right _ hd
        simp only [Nat.add_mul, Nat.one_mul] at this; omega
      rw [if_neg (by omega), if_pos (by omega), show n + d * U.length + u - n = d * U.length + u by omega,
        (hdiv d u h1).1, (hdiv d u h1).2]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    have hnv := nval_range (List.ofFn x) (anodeAt U dflt n as o Pr) bv
      (fun i hi => by simp only [bv]; rw [if_pos (by omega)]) (as.length * U.length + 1) (by
        intro p hp
        rw [hxl]
        refine ⟨hdeps p hp, ?_⟩
        by_cases hpa : p < as.length * U.length
        · obtain ⟨hj, hjp, hu⟩ := hpj p hpa
          have hbvp : bv (n + p) = decide (val x (p / U.length) = U.getD (p % U.length) dflt) := by
            simp only [bv]
            rw [if_neg (by omega), if_pos (by omega), show n + p - n = p by omega, oh_getD U dflt _ hu]
          rw [hnodeEq p hpa, hbvp]
          rcases ha : as[p / U.length] with ⟨i, f⟩ | ⟨ds, F⟩
          · have hi := hinp _ hj i f ha
            simp only [bnodeOf, List.map_cons, List.map_nil, List.getD_cons_zero, bv, if_pos hi]
            rw [hvi x _ hj i f ha]
          · obtain ⟨hds, -⟩ := hfn _ hj ds F ha
            have hm : (ds.flatMap (ohBlk U n)).map bv = ds.flatMap (fun d => oh U (val x d)) := by
              rw [List.map_flatMap]
              apply List.flatMap_congr
              intro d hd; exact hbvb d (by have := hds d hd; omega)
            simp only [bnodeOf]
            rw [hm, ohDecs_flat U dflt ds (val x) (fun d hd => hU x d (by have := hds d hd; omega)),
              ← hvf x _ hj ds F ha]
        · have hpe : p = as.length * U.length := by omega
          simp only [anodeAt, if_neg hpa]
          rw [hbvb o ho, ohDec_oh U dflt (hU x o ho)]
          simp only [bv]
          rw [if_neg (by omega), if_neg (by omega)])
    rw [hnv, getD_range_map _ _ (by omega)]
    simp only [bv]
    rw [if_neg (by omega), if_neg (by omega)]
  have hC := hasCircuit_nval n (c * U.length) ns
    (fun p hp d hd => by
      rw [hlen] at hp
      simp only [hns, List.getElem_map, List.getElem_range] at hd
      exact hdeps p hp d hd)
    (fun nd hnd => by
      simp only [hns, List.mem_map] at hnd
      obtain ⟨p, -, rfl⟩ := hnd
      exact hcW p)
    (n + as.length * U.length) (by omega)
  rw [hlen] at hC
  have hf : (fun x : Fin n → Bool => (nval (List.ofFn x) ns).getD (n + as.length * U.length) false) =
      (fun x => decide (Pr (val x o))) := funext key
  rw [hf] at hC
  exact hC

end OneHot

end PvnpReal
