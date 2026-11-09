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
import Submission.FibHeapSupport

namespace Submission.FibHeapDepth

open Submission.FibHeapCascade Submission.FibHeapRefine Submission.FibHeapForest
open Submission.FibHeapAcyclic
open Submission.FibHeapSupport

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

/- The LiveDistinct bridge: the `ids` fold's machine decomposition.  Landed
2026-11-09, the recursor cell included: `ids_node_eq` unrolls `ids` along
`treeOf` through the aux recursor `Tree.rec_1` (the pin generates no equation
lemmas for it; the working recipe is `simp only [List.map_cons, List.foldr_cons]`
for the cons iota plus plain delta on the head — never a `show` against
`rec_1`-on-cons, whose elaborated motives mismatch).  On top of it:
`mem_foldr_append` (the climb), `mem_ids_reach` (ids-membership to `Reach`),
the two disjointness combos (`ids_not_self`, `ids_disjoint_cross` —
`reach_self_absurd` and `reach_unique_depth`+`reach_unique`), and
`liveDistinct_treeOf` via `List.nodup_flatten` (per-segment Nodup from the fuel
IH, `Pairwise Disjoint` from `KidsNodup` + `List.disjoint_iff_ne`). -/
section LiveDistinctBridge

/-- **The `ids` fold unrolls along `treeOf`.**  The aux-recursor cell: the
`Tree.rec_1` fold over the spliced child list equals the appended fold of the
children's id lists.  The cons case's head recursion value is
`ids (treeOf st f a)` by pure unfolding (`Child.mk` projections and the child
recursor's identity case), which is why the map is over machine ids. -/
theorem ids_node_eq (st : HState) (f p : ℕ) :
    ids (treeOf st (f + 1) p)
      = p :: List.foldr (fun xs ys : List ℕ => xs ++ ys) []
          ((kids st p).map fun c => ids (treeOf st f c)) := by
  have hnode : treeOf st (f + 1) p
      = FibHeapForest.Tree.node p
          ((kids st p).map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c)) := rfl
  rw [hnode]
  have hunroll : ids (FibHeapForest.Tree.node p
        ((kids st p).map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c)))
      = p :: Tree.rec_1 (motive_1 := fun _ => List ℕ) (motive_2 := fun _ => List ℕ)
        (motive_3 := fun _ => List ℕ)
        (fun id _ childIds => id :: childIds) (fun _ _ _ treeIds => treeIds) []
        (fun _ _ headIds tailIds => headIds ++ tailIds)
        ((kids st p).map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c)) := by
    simp [ids]
  rw [hunroll]
  have aux : ∀ ks : List ℕ,
      Tree.rec_1 (motive_1 := fun _ => List ℕ) (motive_2 := fun _ => List ℕ)
        (motive_3 := fun _ => List ℕ)
        (fun id _ childIds => id :: childIds) (fun _ _ _ treeIds => treeIds) []
        (fun _ _ headIds tailIds => headIds ++ tailIds)
        (ks.map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))
      = List.foldr (fun xs ys : List ℕ => xs ++ ys) []
          (ks.map fun c => ids (treeOf st f c)) := by
    intro ks
    induction ks with
    | nil => rfl
    | cons a ks ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [ih]
      rfl
  rw [aux]

/-- The foldr-append membership decomposition. -/
theorem mem_foldr_append {x : ℕ} : ∀ (L : List (List ℕ)),
    x ∈ L.foldr (fun xs ys : List ℕ => xs ++ ys) [] ↔ ∃ xs ∈ L, x ∈ xs := by
  intro L
  induction L with
  | nil => simp
  | cons a L ih => simp [List.mem_append, ih]

/-- The `foldr (++) []` form is the flatten. -/
theorem foldr_append_eq_flatten (L : List (List ℕ)) :
    L.foldr (fun xs ys : List ℕ => xs ++ ys) [] = L.flatten := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

/-- **The ids→Reach climb** (the `mem_ids_reach` cell named in
`FibHeapSupport`): every id collected in the abstraction sits below its root
in the parent relation.  Fuel induction through `ids_node_eq`. -/
theorem mem_ids_reach (st : HState) : ∀ (f c x : ℕ),
    x ∈ ids (treeOf st f c) → ∃ g, Reach st g c x := by
  intro f
  induction f with
  | zero =>
    intro c x hx
    simp only [treeOf] at hx
    simp [ids] at hx
    exact ⟨0, hx.symm⟩
  | succ f ih =>
    intro c x hx
    rw [ids_node_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨0, rfl⟩
    · obtain ⟨xs, hxsm, hxs⟩ := Iff.mp (mem_foldr_append _) hx
      simp only [List.mem_map] at hxsm
      obtain ⟨d, hdmem, rfl⟩ := hxsm
      obtain ⟨g, hg⟩ := ih d x hxs
      exact ⟨g + 1, ⟨d, hdmem, hg⟩⟩

/-- **Disjointness combo, self half.**  A parent's own id is not in a child's
subtree: that closes a `par` cycle, and `Acyc` only tolerates the NIL loop. -/
theorem ids_not_self (st : HState) (hpar : ParOK st) (hac : Acyc st) (hnl : NILLeaf st)
    {f c p : ℕ} (hc : c ∈ kids st p) : p ∉ ids (treeOf st f c) := by
  intro hmem
  obtain ⟨g, hg⟩ := mem_ids_reach st f c p hmem
  exact reach_self_absurd st hpar hac hnl hc hg

/-- **Disjointness combo, cross half.**  Two distinct children's subtrees share
no id: a shared id climbs to both children, `reach_unique_depth` equalizes the
climb lengths from the common (non-NIL, live) parent and `reach_unique` lands
the children equal. -/
theorem ids_disjoint_cross (st : HState) (hpar : ParOK st) (hac : Acyc st) (hnl : NILLeaf st)
    {f c1 c2 p : ℕ} (h1 : c1 ∈ kids st p) (h2 : c2 ∈ kids st p) (hne : c1 ≠ c2) :
    List.Disjoint (ids (treeOf st f c1)) (ids (treeOf st f c2)) := by
  rw [List.disjoint_iff_ne]
  intro a ha b hb hab
  subst hab
  obtain ⟨g1, hg1⟩ := mem_ids_reach st f c1 a ha
  obtain ⟨g2, hg2⟩ := mem_ids_reach st f c2 a hb
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0] at h1
    rw [kids_eq_nil hnl] at h1
    simp at h1
  have hp1 : Reach st (g1 + 1) p a := ⟨c1, h1, hg1⟩
  have hp2 : Reach st (g2 + 1) p a := ⟨c2, h2, hg2⟩
  have hgd := reach_unique_depth st hpar hac hp0 hp1 hp2
  have hgg : g1 = g2 := by omega
  exact hne (reach_unique st hpar g1 c1 c2 a hg1 (hgg ▸ hg2))

/-- Index-Nodup form is list Nodup (generic, over `getD` with default `0`). -/
theorem nodup_of_getD_ne : ∀ (l : List ℕ),
    (∀ j k, j < k → k < l.length → l.getD j 0 ≠ l.getD k 0) → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a t ih =>
    intro h
    refine List.pairwise_cons.mpr ⟨?_, ih (fun j k hj hk => h (j + 1) (k + 1) (by omega)
      (by simp only [List.length_cons]; omega))⟩
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨hilt, hid⟩ := List.getElem?_eq_some_iff.mp hi
    have hne : a ≠ t.getD i 0 := by
      have h0 := h 0 (i + 1) (by omega) (by simp only [List.length_cons]; omega)
      simpa using h0
    rw [List.getD_eq_getElem t 0 hilt, hid] at hne
    exact hne

/-- `KidsNodup`'s index form is list Nodup. -/
theorem kids_nodup_list {st : HState} {p : ℕ} (h : KidsNodup st p) : (kids st p).Nodup := by
  refine nodup_of_getD_ne (kids st p) (fun j k hj hk => ?_)
  rw [kids_length] at hk
  exact h j k hj hk

/-- Pairwise disjointness of the id segments over a Nodup child list. -/
theorem ids_segments_pairwise (st : HState) (hpar : ParOK st) (hac : Acyc st) (hnl : NILLeaf st)
    (f p : ℕ) : ∀ ks : List ℕ, (∀ c ∈ ks, c ∈ kids st p) → ks.Nodup →
    (ks.map fun c => ids (treeOf st f c)).Pairwise List.Disjoint := by
  intro ks
  induction ks with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons a ks ih =>
    intro hmem hnod
    obtain ⟨hanot, htail⟩ := List.nodup_cons.mp hnod
    refine List.pairwise_cons.mpr ⟨?_, ih (fun c hc => hmem c (List.mem_cons_of_mem _ hc)) htail⟩
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    have hac2 : a ≠ c := by
      intro h
      exact hanot (by rw [h]; exact hc)
    exact ids_disjoint_cross st hpar hac hnl (hmem a List.mem_cons_self)
      (hmem c (List.mem_cons_of_mem _ hc)) hac2

/-- **LiveDistinct over the machine state.**  The abstraction's id list has no
repeats: per-segment Nodup is the fuel induction, cross-segment disjointness is
`ids_disjoint_cross` gated by `KidsNodup`. -/
theorem liveDistinct_treeOf (st : HState) (hpar : ParOK st) (hac : Acyc st) (hnl : NILLeaf st)
    (hnd : ∀ q, KidsNodup st q) : ∀ (f p : ℕ), LiveDistinct (treeOf st f p) := by
  intro f
  induction f with
  | zero =>
    intro p
    simp [treeOf, ids, LiveDistinct]
  | succ f ih =>
    intro p
    simp only [LiveDistinct]
    rw [ids_node_eq, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨xs, hxsm, hxs⟩ := Iff.mp (mem_foldr_append _) hmem
      simp only [List.mem_map] at hxsm
      obtain ⟨c, hc, rfl⟩ := hxsm
      exact ids_not_self st hpar hac hnl hc hxs
    · rw [foldr_append_eq_flatten, List.nodup_flatten]
      refine ⟨fun xs hxsm => ?_, ?_⟩
      · simp only [List.mem_map] at hxsm
        obtain ⟨c, -, rfl⟩ := hxsm
        exact ih c
      · exact ids_segments_pairwise st hpar hac hnl f p (kids st p) (fun _ hc => hc)
          (kids_nodup_list (hnd p))

/-- Every id in an in-range node's abstraction is a live slot: the climb
descends only through `kids` (which `SlotOK` bounds) or stops at the root. -/
theorem mem_ids_lt {st : HState} (hslot : SlotOK st)
    {f p x : ℕ} (hp : p < st.n) (hx : x ∈ ids (treeOf st f p)) : x < st.n := by
  obtain ⟨g, hg⟩ := mem_ids_reach st f p x hx
  cases g with
  | zero =>
    simp only [Reach] at hg
    rw [hg] at hp
    exact hp
  | succ g' => exact reach_lt st hslot (g' + 1) p x hp (by omega) hg

/-- The machine abstraction at fuel `st.n` fits the live slots: `Size ≤ st.n`
for every in-range node. -/
theorem treeOf_size_le_n (st : HState) (hpar : ParOK st) (hac : Acyc st) (hnl : NILLeaf st)
    (hnd : ∀ q, KidsNodup st q) (hslot : SlotOK st) {p : ℕ} (hp : p < st.n) :
    (treeOf st st.n p).size ≤ st.n := by
  have hld := liveDistinct_treeOf st hpar hac hnl hnd st.n p
  have hcard : (ids (treeOf st st.n p)).toFinset.card = (treeOf st st.n p).size :=
    live_card hld
  have hsub : (ids (treeOf st st.n p)).toFinset ⊆ Finset.range st.n := fun x hx => by
    simpa [Finset.mem_range] using mem_ids_lt hslot hp (by simpa using hx)
  calc (treeOf st st.n p).size = (ids (treeOf st st.n p)).toFinset.card := hcard.symm
    _ ≤ st.n := by simpa using Finset.card_le_card hsub

/-- **The walk bound at the live size `B := st.n`.**  Every node of an
in-range walk is in range: the bottom by hypothesis, each parent by
`ParSlot`, the NIL parent excluded by `NILLeaf`.  So the Size measure's
strict climb (`size_mono_machine`) lives inside `range st.n` and the walk
is at most `st.n` long. -/
theorem walkUp_len_le_n (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hs : NILSelf st) (hac : Acyc st) (hnl : NILLeaf st)
    (hnd : ∀ q, KidsNodup st q)
    {y : ℕ} {chain : List (ℕ × ℕ)} (hW : WalkUp st y chain) (hy : y < st.n) :
    chain.length ≤ st.n := by
  have hclimb : ∀ (a b : ℕ), a ∈ kids st b → a < st.n → b < st.n ∧ b ≠ 0 ∧
      (treeOf st st.n a).size < (treeOf st st.n b).size := by
    intro a b hk han
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0] at hk
      rw [kids_eq_nil hnl] at hk
      simp at hk
    have hbn : b < st.n := by rw [← walkUp_par hpar hk]; exact hps a han
    exact ⟨hbn, hb0, size_mono_machine st hpar hslot hps hs hac hnl hk hbn hb0⟩
  have main : ∀ (chain : List (ℕ × ℕ)) (y : ℕ),
      WalkUp st y chain → y < st.n →
      chain.length + (treeOf st st.n y).size ≤ st.n + 1 := by
    intro chain
    induction chain with
    | nil =>
      intro y hW hy
      have hsz := treeOf_size_le_n st hpar hac hnl hnd hslot hy
      simp only [List.length_nil]
      omega
    | cons cell rest ih =>
      intro y hW hy
      cases hW with
      | @cons _ z _ hk hW' =>
        obtain ⟨hz1, hz2, hz3⟩ := hclimb y z hk hy
        have hz : rest.length + (treeOf st st.n z).size ≤ st.n + 1 := ih z hW' hz1
        have hsz := treeOf_size_le_n st hpar hac hnl hnd hslot hy
        simp only [List.length_cons]
        omega
  have hm := main chain y hW hy
  have hpos : 0 < (treeOf st st.n y).size := size_pos _
  omega

end LiveDistinctBridge

/- The bridge's remaining cells, precisely named: (1) the `ChainOk → WalkUp`
lift — the cascade's cells read the *evolving* kids, and the lift is that cut
and promote only remove edges, so each cell's membership lifts to the original
state's `kids` (`kids_promote_unchanged` class); (2) the walk bound at
`B := st.n` for in-range walks, feeding `DkRun`'s per-step `chain.length ≤ L`
with `L := st.n`; (3) the row's sequential total over matched states.  The
ids side (`ids_node_eq` through `liveDistinct_treeOf`) is landed above. -/
end Submission.FibHeapDepth
