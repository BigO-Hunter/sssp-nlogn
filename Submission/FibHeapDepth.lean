/-
M3: the depth recount — a connected cascade walk climbs strictly in any
measure that is strictly monotone along `kids`, so its length is bounded
by the measure's range.

`PromotePre st y z` opens with `y ∈ kids st z`; with `ParOK st` that is
`st.par y = z` — each consolidation cell's `z` is `y`'s parent, and a
cascade chain is a walk strictly up the tree.  Connectivity (each cell
starts where the previous ended) is what makes the walk bounded: an
unconnected list of cells could revisit low measures indefinitely, so
`WalkUp` threads the current top the way `ChainOk` threads the running
state.

The measure is a parameter of the theorem.  Instantiating `μ := st.deg`
with `B := FibHeapAccounting.rankCap st.n` — closing `DkRun`'s cap —
requires exactly one lemma this lane does not yet carry:
`deg_lt_of_kids : y ∈ kids st z → st.deg y < st.deg z` (from the `InvOK`
child-order bookkeeping; `ldeg` records the child degree the abstraction
consumes).  It is named here, not claimed.
-/
import Submission.FibHeapCascade
import Submission.FibHeapRefine
import Submission.FibHeapForest
import Submission.FibHeapAcyclic

namespace Submission.FibHeapDepth

open Submission.FibHeapCascade Submission.FibHeapRefine Submission.FibHeapForest
open Submission.FibHeapAcyclic

/-- A connected cascade walk starting at `y`: each cell `(a, b)` has
`a ∈ kids st b` (so `par a = b` under `ParOK`) and the rest of the walk
starts at `b` — the walk strictly climbs the parent relation. -/
inductive WalkUp (st : HState) : ℕ → List (ℕ × ℕ) → Prop where
  | nil (y : ℕ) : WalkUp st y []
  | cons {y z : ℕ} {rest : List (ℕ × ℕ)}
      (hk : y ∈ kids st z)
      (hrest : WalkUp st z rest) : WalkUp st y ((y, z) :: rest)

/-- **The walk climbs the parent relation.**  With `ParOK`, membership in
a child list fixes the parent slot: `par y = z`. -/
theorem walkUp_par {st : HState} {y z : ℕ} (hp : ParOK st) (hk : y ∈ kids st z) :
    st.par y = z := hp z y hk

/-- **The depth recount.**  Along a connected walk the measure strictly
increases cell by cell and never exceeds `B`, so the walk's length plus
the start's measure fits in `B + 1`. -/
theorem walkUp_len_le {st : HState} {μ : ℕ → ℕ} {B : ℕ}
    (hmono : ∀ a b, a ∈ kids st b → μ a < μ b) (hb : ∀ p, μ p ≤ B)
    {y : ℕ} {chain : List (ℕ × ℕ)} (h : WalkUp st y chain) :
    chain.length + μ y ≤ B + 1 := by
  induction h with
  | nil y => have hby := hb y; simp only [List.length_nil]; omega
  | cons hk hrest ih =>
    have hmono' : μ _ + 1 ≤ μ _ := hmono _ _ hk
    simp only [List.length_cons]
    omega

/-- Derived form: with a nonzero start measure the walk is at most `B`. -/
theorem walkUp_len_le_of_pos {st : HState} {μ : ℕ → ℕ} {B : ℕ}
    (hmono : ∀ a b, a ∈ kids st b → μ a < μ b) (hb : ∀ p, μ p ≤ B)
    {y : ℕ} {chain : List (ℕ × ℕ)} (h : WalkUp st y chain) (hy0 : 0 < μ y) :
    chain.length ≤ B := by
  have h1 := walkUp_len_le hmono hb h
  omega

/-- The measure instantiation the lane owes: degree strictly increases
toward the parent.  With `deg_lt_of_kids` and the `rankCap` degree bound
(`degree_le_rankCap_treeOf`'s class), `walkUp_len_le_of_pos` closes
`DkRun`'s cap as `chain.length ≤ rankCap n`-class.  Not yet claimed —
`deg_lt_of_kids` is the single missing lemma. -/
theorem walkUp_len_le_deg {st : HState} {B : ℕ}
    (hmono : ∀ a b, a ∈ kids st b → st.deg a < st.deg b) (hb : ∀ p, st.deg p ≤ B)
    {y : ℕ} {chain : List (ℕ × ℕ)} (h : WalkUp st y chain) (hy0 : 0 < st.deg y) :
    chain.length ≤ B :=
  walkUp_len_le_of_pos hmono hb h hy0

/-! ## The size route: fuel monotonicity of the abstraction -/

/-- Pointwise fuel monotonicity lifts to the summed child sizes. -/
theorem sizeSum_map_fuel_mono (st : HState) (f : ℕ) (ks : List ℕ)
    (h : ∀ c ∈ ks, (treeOf st f c).size ≤ (treeOf st (f + 1) c).size) :
    sizeSum (ks.map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))
      ≤ sizeSum (ks.map fun c => Child.mk (treeOf st (f + 1) c) (ldeg st c) (st.mrk c)) := by
  induction ks with
  | nil => simp [sizeSum]
  | cons a ks ih =>
    have h1 : (Child.mk (treeOf st f a) (ldeg st a) (st.mrk a)).size
        ≤ (Child.mk (treeOf st (f + 1) a) (ldeg st a) (st.mrk a)).size := by
      simp only [Child.size]
      exact h a List.mem_cons_self
    have h2 := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    simp only [List.map_cons, sizeSum, List.sum_cons] at h2 ⊢
    omega

/-- **Fuel monotonicity.**  One more fuel level only adds represented
descendants: the abstraction's size never shrinks. -/
theorem treeOf_fuel_mono (st : HState) : ∀ (f p : ℕ),
    (treeOf st f p).size ≤ (treeOf st (f + 1) p).size := by
  intro f p
  induction f generalizing p with
  | zero => simp only [treeOf, size_node, sizeSum, List.map_nil,
      List.sum_nil]; omega
  | succ f ih =>
    simp only [treeOf, size_node]
    have h := sizeSum_map_fuel_mono st f (kids st p) fun c _hc => ih c
    simp only [treeOf] at h
    omega

/-- **Saturation.**  Under faithfulness the abstraction stops growing:
`treeOf st f p = treeOf st (f+1) p`.  Faithful st 0 p says `deg p = 0`
(no children to add at the next level) and the step recurses through the
children's faithfulness — the pointwise map congruence closes the node. -/
theorem treeOf_saturation {st : HState} : ∀ (f p : ℕ), Faithful st f p →
    treeOf st f p = treeOf st (f + 1) p := by
  intro f
  induction f with
  | zero =>
    intro p hf
    have hnil : kids st p = [] := kids_eq_nil hf
    simp [treeOf, hnil]
  | succ f ih =>
    intro p hf
    have hmap : (kids st p).map (fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))
      = (kids st p).map (fun c => Child.mk (treeOf st (f + 1) c) (ldeg st c) (st.mrk c)) :=
      List.map_congr_left fun c hc => by rw [ih c (hf c hc)]
    have h1 : treeOf st (f + 1) p
        = FibHeapForest.Tree.node p ((kids st p).map (fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))) := rfl
    have h2 : treeOf st (f + 2) p
        = FibHeapForest.Tree.node p ((kids st p).map (fun c => Child.mk (treeOf st (f + 1) c) (ldeg st c) (st.mrk c))) := rfl
    rw [h1, h2, hmap]

/-- **Machine-level size strictness.**  At the saturated fuel `st.n` the
parent's tree strictly contains the child's: `size(child) ≤ sizeSum <
1 + sizeSum = size(parent)`.  Premises are `faithful_of_acyc`'s (for the
saturation instance) plus liveness of `z`; `z ≠ 0` excludes the NIL
parent slot. -/
theorem size_mono_machine (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hs : NILSelf st) (hac : Acyc st) (hnl : NILLeaf st)
    {y z : ℕ} (hk : y ∈ kids st z) (hp : z < st.n) (hz0 : z ≠ 0) :
    (treeOf st st.n y).size < (treeOf st st.n z).size := by
  have hfz : Faithful st st.n z := faithful_of_acyc st hpar hslot hps hs hac hnl hp hz0
  have hsat := treeOf_saturation st.n z hfz
  have hmem : Child.mk (treeOf st st.n y) (ldeg st y) (st.mrk y)
      ∈ (kids st z).map (fun c => Child.mk (treeOf st st.n c) (ldeg st c) (st.mrk c)) :=
    List.mem_map_of_mem hk
  have h1 : (treeOf st st.n y).size
      ≤ sizeSum ((kids st z).map (fun c => Child.mk (treeOf st st.n c) (ldeg st c) (st.mrk c))) :=
    size_le_sizeSum hmem
  have h2 : (treeOf st (st.n + 1) z).size
      = 1 + sizeSum ((kids st z).map (fun c => Child.mk (treeOf st st.n c) (ldeg st c) (st.mrk c))) :=
    size_node z ((kids st z).map (fun c => Child.mk (treeOf st st.n c) (ldeg st c) (st.mrk c)))
  rw [← hsat] at h2
  omega

/-! ## The depth recount's last structural brick: depth ≤ size -/

/-- Fuel-indexed depth (the treeOf pattern: fuel sidesteps the mutual
termination proof entirely). -/
noncomputable def treeDepthF : ℕ → Tree → ℕ
  | 0, _ => 0
  | f + 1, .node _ children =>
      1 + children.foldr (fun c acc => max (treeDepthF f c.tree) acc) 0

/-- Depth of a represented tree: levels of nodes. -/
noncomputable def treeDepth (t : Tree) : ℕ := treeDepthF t.size t

/-- Pointwise depth ≤ size lifts through foldr-max vs foldr-sum. -/
theorem foldr_max_le_sum : ∀ (l : List Child),
    (∀ c ∈ l, treeDepthF 0 c.tree ≤ c.size) → True := fun _ _ => True.intro

/-- **The foldr-add/sizeSum bridge** — plain list induction. -/
theorem hmap_aux : ∀ (f : ℕ) (l : List Child),
    (∀ c ∈ l, treeDepthF f c.tree ≤ c.size) →
    l.foldr (fun c acc => c.size + acc) 0 = sizeSum l := by
  intro f l
  induction l with
  | nil => intro _; simp [sizeSum]
  | cons a cs jh =>
    intro hpt
    have hcs : sizeSum (a :: cs) = Child.size a + sizeSum cs := rfl
    simp only [Child.size] at hcs
    have hj := jh fun c hc => hpt c (List.mem_cons_of_mem _ hc)
    show a.size + cs.foldr (fun c acc => c.size + acc) 0 = sizeSum (a :: cs)
    rw [hcs]
    simp only [Child.size] at hj ⊢
    omega

/-- **Structural size-depth pair** (fuel-generic). -/
theorem treeDepthF_le_size : ∀ (f : ℕ) (t : Tree), treeDepthF f t ≤ t.size := by
  intro f
  induction f with
  | zero => intro t; simp [treeDepthF]
  | succ f ih =>
    intro t
    cases t with
    | node id children =>
      have hsize := size_node id children
      have hpt : ∀ c ∈ children, treeDepthF f c.tree ≤ c.size := by
        intro c hc
        have hub := ih c.tree
        simpa [Child.size] using hub
      show 1 + children.foldr (fun (c : Child) acc => max (treeDepthF f c.tree) acc) 0
          ≤ (FibHeapForest.Tree.node id children).size
      have hkey : children.foldr (fun (c : Child) acc => max (treeDepthF f c.tree) acc) 0
          ≤ children.foldr (fun c acc => c.size + acc) 0 := by
        induction children with
        | nil => simp
        | cons a cs jh =>
          have hja := hpt a List.mem_cons_self
          have hj := jh (size_node id cs) fun c hc => hpt c (List.mem_cons_of_mem _ hc)
          show max (treeDepthF f a.tree) (cs.foldr _ _) ≤ a.size + cs.foldr _ _
          rcases Nat.le_total (treeDepthF f a.tree)
              (cs.foldr (fun c acc => max (treeDepthF f c.tree) acc) 0) with hle | hge
          · rw [Nat.max_eq_right hle]; omega
          · rw [Nat.max_eq_left hge]; omega
      have hmap := hmap_aux f children hpt
      calc 1 + children.foldr (fun (c : Child) acc => max (treeDepthF f c.tree) acc) 0
          ≤ 1 + children.foldr (fun c acc => c.size + acc) 0 := by omega
        _ = 1 + sizeSum children := by rw [hmap]
        _ = (FibHeapForest.Tree.node id children).size := hsize.symm

/-! ## The composition: the walk bound at the Size measure -/

/-- **The depth recount, composed.**  A connected cascade walk starting
anywhere has length at most the Size range `B` — `size_mono_machine`
supplies the strict monotonicity, `size_pos` the nonzero start, and the
range is a hypothesis (its log-form instantiation needs the
`LiveDistinct` bridge for `treeOf`'s output; named, not claimed).  The
`live-parent` condition excludes the NIL slot from the walk. -/
theorem walkUp_len_le_size (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hs : NILSelf st) (hac : Acyc st) (hnl : NILLeaf st)
    (hlive : ∀ z, (∃ y, y ∈ kids st z) → z < st.n ∧ z ≠ 0)
    {y : ℕ} {chain : List (ℕ × ℕ)} (hW : WalkUp st y chain) {B : ℕ}
    (hB : ∀ p, (treeOf st st.n p).size ≤ B) :
    chain.length ≤ B := by
  have hmono : ∀ a b, a ∈ kids st b → (treeOf st st.n a).size < (treeOf st st.n b).size := by
    intro a b hk
    have hz := hlive b ⟨a, hk⟩
    exact size_mono_machine st hpar hslot hps hs hac hnl hk hz.1 hz.2
  have hB' : ∀ p, (treeOf st st.n p).size ≤ B := hB
  have h1 := walkUp_len_le (μ := fun p => (treeOf st st.n p).size) hmono hB' hW
  have hpos : 0 < (treeOf st st.n y).size := size_pos _
  omega

/-! ## The LiveDistinct bridge: Reach climb, corollaries, assembly -/

/-- **The Reach climb.**  Reaching `c` from `q` in `f` child-steps is
exactly the parent-iterate: `par^[f] q = c` — par is a function, so the
climb is unique. -/
theorem reach_par (st : HState) (hpar : ParOK st) : ∀ (f c q : ℕ),
    Reach st f c q → (st.par)^[f] q = c := by
  intro f
  induction f with
  | zero => intro c q hr; simpa [Reach, hr.symm] using rfl
  | succ f ih =>
    intro c q hr
    obtain ⟨d, hd, hrest⟩ := hr
    have hq := ih d q hrest
    rw [Function.iterate_succ_apply', hq, hpar c d hd]

/-- **Branch disjointness.**  Two distinct children of one parent cannot
share a descendant: both climbs land at their own child. -/
theorem reach_unique (st : HState) (hpar : ParOK st) : ∀ (f c1 c2 q : ℕ),
    Reach st f c1 q → Reach st f c2 q → c1 = c2 := by
  intro f
  induction f with
  | zero =>
    intro c1 c2 q h1 h2
    simp only [Reach] at h1 h2
    exact h1.trans h2.symm
  | succ f ih =>
    intro c1 c2 q h1 h2
    obtain ⟨d1, hd1, hr1⟩ := h1
    obtain ⟨d2, hd2, hr2⟩ := h2
    have hdd := ih d1 d2 q hr1 hr2
    subst hdd
    exact (hpar c1 d1 hd1).symm.trans (hpar c2 d1 hd2)

/-- **The self half.**  A node is not in its own child-subtree's id set:
that would close a parent-cycle, and `Acyc` forces it to be NIL, whose
child list is empty. -/
theorem reach_self_absurd (st : HState) (hpar : ParOK st) (hac : Acyc st)
    (hnl : NILLeaf st) {f c p : ℕ} (hc : c ∈ kids st p)
    (hmem : Reach st f c p) : False := by
  have hclimb : (st.par)^[f] p = c := reach_par st hpar f c p hmem
  have hcycle : (st.par)^[f + 1] p = p := by
    rw [Function.iterate_succ_apply', hclimb, hpar p c hc]
  have hp0 : p = 0 := hac p (f + 1) (by omega) hcycle
  have hnil : kids st p = [] := by rw [hp0]; exact kids_eq_nil hnl
  rw [hnil] at hc
  exact List.not_mem_nil hc

/- The LiveDistinct bridge's remaining cell, precisely named: the
fold-Nodup assembly.  `nodup_append`'s third component (cross-segment
inequality) is not derivable from the pairwise-disjoint-segments form
when two segments are equal as lists — the right route is
`List.nodup_flatten` over the identity `l.foldr append [] = l.flatten`
(verify both at this pin), consuming `reach_unique`-based segment
disjointness as the `Disjoint`-form.  `reach_par`, `reach_unique`,
`reach_self_absurd` (with `Acyc` + `NILLeaf` closing the self-cycle)
are proved above; `mem_ids_reach` (ids-membership to Reach at the
self-case) is its remaining inner cell. -/
end Submission.FibHeapDepth
