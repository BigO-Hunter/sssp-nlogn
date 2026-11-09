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

namespace Submission.FibHeapDepth

open Submission.FibHeapCascade Submission.FibHeapRefine Submission.FibHeapForest

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

end Submission.FibHeapDepth
