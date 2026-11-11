/-
  PvnpReal.CircShannon — size-bounded circuits for arbitrary Boolean functions (Shannon expansion),
  placed at an absolute offset inside a larger gate list, and *bit programs*: straight-line programs
  whose nodes are arbitrary Boolean functions of `≤ c` earlier bits. A bit program with `N` nodes
  is a circuit with at most `2 + N · 4 · 2^c` gates (`hasCircuit_nval`).
-/
import PvnpReal.CircBuild

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PvnpReal

open scoped Classical

theorem pStep_length (v : List Bool) (g : CGate) : (pStep v g).length = v.length + 1 := by
  simp [pStep]

theorem pStep_getD_old (v : List Bool) (g : CGate) {j : ℕ} (hj : j < v.length) :
    (pStep v g).getD j false = v.getD j false := by
  simp [pStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem pStep_getD_new (v : List Bool) (g : CGate) {j : ℕ} (hj : j = v.length) :
    (pStep v g).getD j false = opN g.1 (v.getD g.2.1 false) (v.getD g.2.2 false) := by
  subst hj; simp [pStep, List.getD_eq_getElem?_getD]

theorem shan_tail (v0 : List Bool) (w o1 o0 : ℕ) (hw : w < v0.length) (h1 : o1 < v0.length)
    (h0 : o0 < v0.length) :
    (pRun v0 [(2, w, w), (0, w, o1), (0, v0.length, o0), (1, v0.length + 1, v0.length + 2)]).getD
      (v0.length + 3) false =
      ((v0.getD w false && v0.getD o1 false) || (!v0.getD w false && v0.getD o0 false)) := by
  simp only [pRun_cons, pRun_nil]
  set a := v0.length with ha
  set u1 := pStep v0 (2, w, w)
  set u2 := pStep u1 (0, w, o1)
  set u3 := pStep u2 (0, a, o0)
  have l1 : u1.length = a + 1 := pStep_length _ _
  have l2 : u2.length = a + 2 := by rw [pStep_length, l1]
  have l3 : u3.length = a + 3 := by rw [pStep_length, l2]
  rw [pStep_getD_new _ _ l3.symm]
  dsimp only
  have e3a : u3.getD (a + 1) false = u2.getD (a + 1) false := pStep_getD_old _ _ (by omega)
  have e3b : u3.getD (a + 2) false = opN 0 (u2.getD a false) (u2.getD o0 false) :=
    pStep_getD_new _ _ l2.symm
  have e2a : u2.getD (a + 1) false = opN 0 (u1.getD w false) (u1.getD o1 false) :=
    pStep_getD_new _ _ l1.symm
  have e2b : u2.getD a false = u1.getD a false := pStep_getD_old _ _ (by omega)
  have e2o : u2.getD o0 false = u1.getD o0 false := pStep_getD_old _ _ (by omega)
  have e1a : u1.getD a false = opN 2 (v0.getD w false) (v0.getD w false) := pStep_getD_new _ _ ha
  have e1w : u1.getD w false = v0.getD w false := pStep_getD_old _ _ (by omega)
  have e1o : u1.getD o1 false = v0.getD o1 false := pStep_getD_old _ _ (by omega)
  have e1z : u1.getD o0 false = v0.getD o0 false := pStep_getD_old _ _ (by omega)
  rw [e3a, e3b, e2a, e2b, e2o, e1a, e1w, e1o, e1z]
  cases v0.getD w false <;> simp [opN]

/-! ### Shannon expansion at an absolute offset -/

/-- `shan cF cT ws f ℓ`: gates (to be placed at positions `ℓ, ℓ+1, …`) and the output wire of a
circuit computing `f` on the wires `ws`; `cF`/`cT` are wires holding the constants. -/
def shan (cF cT : ℕ) : List ℕ → (List Bool → Bool) → ℕ → List CGate × ℕ
  | [], f, _ => ([], if f [] then cT else cF)
  | w :: ws, f, ℓ =>
    let r1 := shan cF cT ws (fun bs => f (true :: bs)) ℓ
    let r0 := shan cF cT ws (fun bs => f (false :: bs)) (ℓ + r1.1.length)
    let l' := ℓ + r1.1.length + r0.1.length
    (r1.1 ++ r0.1 ++ [(2, w, w), (0, w, r1.2), (0, l', r0.2), (1, l' + 1, l' + 2)], l' + 3)

theorem shan_length (cF cT : ℕ) : ∀ (ws : List ℕ) (f : List Bool → Bool) (ℓ : ℕ),
    (shan cF cT ws f ℓ).1.length + 4 = 4 * 2 ^ ws.length
  | [], f, ℓ => by simp [shan]
  | w :: ws, f, ℓ => by
    have h1 := shan_length cF cT ws (fun bs => f (true :: bs)) ℓ
    have h0 := shan_length cF cT ws (fun bs => f (false :: bs))
      (ℓ + (shan cF cT ws (fun bs => f (true :: bs)) ℓ).1.length)
    simp only [shan, List.length_append, List.length_cons, List.length_nil, pow_succ]
    omega

theorem shan_spec (cF cT : ℕ) : ∀ (ws : List ℕ) (f : List Bool → Bool) (ℓ : ℕ) (v : List Bool),
    v.length = ℓ → cF < ℓ → cT < ℓ → v.getD cF false = false → v.getD cT false = true →
    (∀ w ∈ ws, w < ℓ) →
    (pRun v (shan cF cT ws f ℓ).1).getD (shan cF cT ws f ℓ).2 false =
        f (ws.map (fun w => v.getD w false)) ∧
      (shan cF cT ws f ℓ).2 < ℓ + (shan cF cT ws f ℓ).1.length ∧
      ∀ g ∈ (shan cF cT ws f ℓ).1, g.2.1 < ℓ + (shan cF cT ws f ℓ).1.length ∧
        g.2.2 < ℓ + (shan cF cT ws f ℓ).1.length
  | [], f, ℓ, v, hv, hF, hT, hvF, hvT, _ => by
    refine ⟨?_, ?_, by simp [shan]⟩
    · simp only [shan, pRun_nil, List.map_nil]
      cases hf : f [] <;> simp only [hf, if_true, Bool.false_eq_true, if_false] <;> assumption
    · simp only [shan]; split_ifs <;> simp <;> omega
  | w :: ws, f, ℓ, v, hv, hF, hT, hvF, hvT, hws => by
    simp only [List.mem_cons, forall_eq_or_imp] at hws
    obtain ⟨hw, hws⟩ := hws
    simp only [shan]
    set r1 := shan cF cT ws (fun bs => f (true :: bs)) ℓ with hr1
    set v1 := pRun v r1.1 with hv1d
    have hv1 : v1.length = ℓ + r1.1.length := by rw [hv1d, pRun_length, hv]
    obtain ⟨e1, o1lt, b1⟩ := shan_spec cF cT ws (fun bs => f (true :: bs)) ℓ v hv hF hT hvF hvT hws
    rw [← hr1, ← hv1d] at e1
    rw [← hr1] at o1lt b1
    have keep1 : ∀ j < ℓ, v1.getD j false = v.getD j false := fun j hj =>
      pRun_getD _ _ (by omega)
    set r0 := shan cF cT ws (fun bs => f (false :: bs)) (ℓ + r1.1.length) with hr0
    obtain ⟨e0, o0lt, b0⟩ := shan_spec cF cT ws (fun bs => f (false :: bs)) (ℓ + r1.1.length) v1
      hv1 (by omega) (by omega) (by rw [keep1 _ hF]; exact hvF) (by rw [keep1 _ hT]; exact hvT)
      (fun w hw => by have := hws w hw; omega)
    rw [← hr0] at e0 o0lt b0
    set v0 := pRun v1 r0.1 with hv0d
    have hv0 : v0.length = ℓ + r1.1.length + r0.1.length := by rw [hv0d, pRun_length, hv1]
    have keep0 : ∀ j < ℓ + r1.1.length, v0.getD j false = v1.getD j false := fun j hj =>
      pRun_getD _ _ (by omega)
    have hmap : ws.map (fun w => v1.getD w false) = ws.map (fun w => v.getD w false) :=
      List.map_congr_left (fun w hw => keep1 w (hws w hw))
    rw [hmap] at e0
    have hvw0 : v0.getD w false = v.getD w false := by rw [keep0 _ (by omega), keep1 _ hw]
    have ho1 : v0.getD r1.2 false = f (true :: ws.map (fun w => v.getD w false)) := by
      rw [keep0 _ o1lt, e1]
    refine ⟨?_, ?_, ?_⟩
    · rw [pRun_append, pRun_append, ← hv1d, ← hv0d]
      have := shan_tail v0 w r1.2 r0.2 (by omega) (by omega) (by omega)
      rw [hv0] at this
      rw [show ℓ + r1.1.length + r0.1.length + 3 = ℓ + r1.1.length + r0.1.length + 3 from rfl, this,
        hvw0, ho1, e0]
      simp only [List.map_cons]
      cases v.getD w false <;> simp
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro g hg
      simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hg
      rcases hg with (hg | hg) | rfl | rfl | rfl | rfl
      · have := b1 g hg; omega
      · have := b0 g hg; omega
      all_goals simp only; omega

/-! ### Bit programs -/

/-- A node: dependency list (bit indices) and the Boolean function applied to their values. -/
abbrev BNode := List ℕ × (List Bool → Bool)

def nStep (vals : List Bool) (nd : BNode) : List Bool :=
  vals ++ [nd.2 (nd.1.map (fun d => vals.getD d false))]

/-- Values of all bits: the inputs, then one bit per node. -/
def nval (x : List Bool) (ns : List BNode) : List Bool := ns.foldl nStep x

theorem nval_length (x : List Bool) (ns : List BNode) : (nval x ns).length = x.length + ns.length := by
  induction ns using List.reverseRecOn with
  | nil => rfl
  | append_singleton ns nd ih =>
    simp only [nval, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    simp [nStep, ih]; omega

def constG (n : ℕ) : List CGate := [(0, n, n), (2, n, n)]

def bStep (n : ℕ) (st : List CGate × List ℕ) (nd : BNode) : List CGate × List ℕ :=
  let r := shan n (n + 1) (nd.1.map (fun d => st.2.getD d 0)) nd.2 (n + 2 + st.1.length)
  (st.1 ++ r.1, st.2 ++ [r.2])

def bBuild (n : ℕ) (ns : List BNode) : List CGate × List ℕ := ns.foldl (bStep n) ([], List.range n)

theorem constG_vals (x : List Bool) (gs : List CGate) :
    (pRun x (constG x.length ++ gs)).getD x.length false = false ∧
      (pRun x (constG x.length ++ gs)).getD (x.length + 1) false = true ∧
      ∀ j < x.length, (pRun x (constG x.length ++ gs)).getD j false = x.getD j false := by
  rw [pRun_append]
  have hl : (pRun x (constG x.length)).length = x.length + 2 := by
    rw [pRun_length]; simp [constG]
  refine ⟨?_, ?_, ?_⟩
  · rw [pRun_getD _ _ (by omega)]
    simp only [constG, pRun_cons, pRun_nil]
    rw [pStep_getD_old _ _ (by simp [pStep_length]), pStep_getD_new _ _ rfl]
    simp [opN, List.getD_eq_getElem?_getD]
  · rw [pRun_getD _ _ (by omega)]
    simp only [constG, pRun_cons, pRun_nil]
    rw [pStep_getD_new _ _ (by simp [pStep_length]), pStep_getD_new _ _ rfl]
    simp [opN, List.getD_eq_getElem?_getD]
  · intro j hj
    rw [pRun_getD _ _ (by omega)]
    simp only [constG, pRun_cons, pRun_nil]
    rw [pStep_getD_old _ _ (by simp [pStep_length]; omega), pStep_getD_old _ _ hj]

theorem bBuild_inv (x : List Bool) (c : ℕ) (ns : List BNode)
    (hdep : ∀ j (hj : j < ns.length), ∀ d ∈ (ns[j]).1, d < x.length + j)
    (hc : ∀ nd ∈ ns, nd.1.length ≤ c) :
    (bBuild x.length ns).2.length = x.length + ns.length ∧
      (∀ b < x.length + ns.length,
        (bBuild x.length ns).2.getD b 0 < x.length + 2 + (bBuild x.length ns).1.length ∧
        (pRun x (constG x.length ++ (bBuild x.length ns).1)).getD ((bBuild x.length ns).2.getD b 0)
          false = (nval x ns).getD b false) ∧
      (∀ g ∈ constG x.length ++ (bBuild x.length ns).1,
        g.2.1 < x.length + 2 + (bBuild x.length ns).1.length ∧
        g.2.2 < x.length + 2 + (bBuild x.length ns).1.length) ∧
      (bBuild x.length ns).1.length ≤ ns.length * (4 * 2 ^ c) := by
  induction ns using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [bBuild], ?_, ?_, by simp [bBuild]⟩
    · intro b hb
      simp only [List.length_nil, Nat.add_zero] at hb
      have := (constG_vals x []).2.2 b hb
      have hr : (List.range x.length).getD b 0 = b := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hb]
      simp only [bBuild, List.foldl_nil, List.append_nil, nval] at this ⊢
      rw [hr]; exact ⟨by omega, this⟩
    · intro g hg
      simp [constG, bBuild] at hg ⊢
      rcases hg with rfl | rfl <;> simp
  | append_singleton ns nd ih =>
    have hdep' : ∀ j (hj : j < ns.length), ∀ d ∈ (ns[j]).1, d < x.length + j := by
      intro j hj d hd
      exact hdep j (by simp; omega) d (by rw [List.getElem_append_left hj]; exact hd)
    have hnd : ∀ d ∈ nd.1, d < x.length + ns.length := by
      intro d hd
      have := hdep ns.length (by simp) d (by simp [hd])
      exact this
    obtain ⟨i1, i2, i3, i4⟩ := ih hdep' (fun nd' h => hc nd' (by simp [h]))
    set st := bBuild x.length ns with hst
    set Pv := pRun x (constG x.length ++ st.1) with hPv
    have hPl : Pv.length = x.length + 2 + st.1.length := by
      rw [hPv, pRun_length]; simp [constG]; omega
    have hcv := constG_vals x st.1
    rw [← hPv] at hcv
    set ws := nd.1.map (fun d => st.2.getD d 0) with hws
    have hwsl : ∀ w ∈ ws, w < x.length + 2 + st.1.length := by
      intro w hw
      rw [hws, List.mem_map] at hw
      obtain ⟨d, hd, rfl⟩ := hw
      exact (i2 d (hnd d hd)).1
    set r := shan x.length (x.length + 1) ws nd.2 (x.length + 2 + st.1.length) with hr
    obtain ⟨e, olt, bnd⟩ := shan_spec x.length (x.length + 1) ws nd.2 _ Pv hPl (by omega) (by omega)
      hcv.1 hcv.2.1 hwsl
    rw [← hr] at e olt bnd
    have hb : bBuild x.length (ns ++ [nd]) = (st.1 ++ r.1, st.2 ++ [r.2]) := by
      simp only [bBuild, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    have hnv : nval x (ns ++ [nd]) = nStep (nval x ns) nd := by
      simp [nval, List.foldl_append]
    have hnl := nval_length x ns
    have hPr : pRun x (constG x.length ++ (st.1 ++ r.1)) = pRun Pv r.1 := by
      rw [← List.append_assoc, pRun_append]
    have hlen := shan_length x.length (x.length + 1) ws nd.2 (x.length + 2 + st.1.length)
    rw [← hr] at hlen
    rw [hb, hnv, hPr]
    refine ⟨by simp only [List.length_append, List.length_singleton, i1]; omega, ?_, ?_, ?_⟩
    · intro b hb'
      simp only [List.length_append, List.length_singleton] at hb' ⊢
      by_cases hbl : b < x.length + ns.length
      · have := i2 b hbl
        rw [List.getD_append _ _ _ _ (by omega)]
        refine ⟨by omega, ?_⟩
        rw [pRun_getD _ _ (by omega), this.2, nStep,
          List.getD_append _ _ _ _ (by omega)]
      · have hbe : b = x.length + ns.length := by omega
        subst hbe
        rw [List.getD_append_right _ _ _ _ (by omega), i1, Nat.sub_self]
        simp only [List.getD_cons_zero]
        refine ⟨by omega, ?_⟩
        rw [e, nStep, List.getD_append_right _ _ _ _ (by omega), hnl, Nat.sub_self]
        simp only [List.getD_cons_zero, hws, List.map_map]
        apply congrArg
        apply List.map_congr_left
        intro d hd
        simp only [Function.comp]
        rw [(i2 d (hnd d hd)).2]
    · intro g hg
      simp only [List.length_append]
      rw [← List.append_assoc, List.mem_append] at hg
      rcases hg with hg | hg
      · have := i3 g hg; omega
      · have := bnd g hg; omega
    · simp only [List.length_append, List.length_singleton]
      have := hc nd (by simp)
      have : 2 ^ ws.length ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by simp [hws]; omega)
      rw [Nat.add_mul, Nat.one_mul]; omega

/-- **Bit programs are circuits.** -/
theorem hasCircuit_nval (n c : ℕ) (ns : List BNode)
    (hdep : ∀ j (hj : j < ns.length), ∀ d ∈ (ns[j]).1, d < n + j)
    (hc : ∀ nd ∈ ns, nd.1.length ≤ c) (o : ℕ) (ho : o < n + ns.length) :
    HasCircuit n (2 + ns.length * (4 * 2 ^ c)) (fun x => (nval (List.ofFn x) ns).getD o false) := by
  have hx0 : (List.replicate n false).length = n := by simp
  obtain ⟨_, j2, j3, j4⟩ := bBuild_inv (List.replicate n false) c ns (by rw [hx0]; exact hdep) hc
  rw [hx0] at j2 j3 j4
  set st := bBuild n ns
  have hgl : (constG n ++ st.1).length = 2 + st.1.length := by simp [constG]; omega
  have hC := hasCircuit_of_gates (n := n) (fun x => (nval (List.ofFn x) ns).getD o false)
    (constG n ++ st.1) (fun g hg => by rw [hgl]; have := j3 g hg; omega)
    (st.2.getD o 0) (by rw [hgl]; have := (j2 o ho).1; omega) (fun x => by
      have hx : (List.ofFn x).length = n := by simp
      obtain ⟨_, k2, _, _⟩ := bBuild_inv (List.ofFn x) c ns (by rw [hx]; exact hdep) hc
      rw [hx] at k2
      exact ((k2 o ho).2).symm)
  refine hC.mono ?_
  rw [hgl]; omega

end PvnpReal
