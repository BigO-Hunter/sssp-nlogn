import Submission.FibHeapAcyclic

/-!
# M1c: sibling distinctness and unique depth — plus the obstruction on the traversal half

`Support` is the last hypothesis of `degree_le_rankCap_of_machine`: every abstracted id is a live
slot, and the abstracted ids are distinct.  This module lands the cross-depth half of distinctness
and the `KidsNodup` invariant, and it records a concrete obstruction that reshapes how the
same-depth half must be done.

## Proved here

* `reach_unique_depth` — **a node sits at exactly one depth.**  If `Reach st i p x` and
  `Reach st j p x` with `i < j`, then `par^[i] x = p = par^[j] x`, so
  `par^[j-i] (par^[i] x) = par^[i] x` with `j - i > 0` — which the strengthened `NoCycle`
  forbids.  So equal ids can only repeat at the *same* depth.  This is the strengthened-`NoCycle`
  dividend: the old `n ≤ j` form would not have closed it.
* `KidsNodup` — the children read out of one ring are pairwise distinct, as a machine invariant
  (see the maintenance note below).  With `ParOK` (a child records its unique parent) it is what
  makes a *position* unique: an id at depth `i` has one parent, hence one position in that
  parent's child list, hence one index sequence from the root.

## Obstruction (named, and it changes the plan)

The remaining step is same-depth uniqueness, which needs the pre-order traversal
`FibHeapForest.ids`.  `ids` is defined by applying the *mutual* recursor `Tree.rec` with explicit
motives, and its equations are **not definitional**: `idsL (c :: t)` does not reduce to
`ids c.tree ++ idsL t`, and `def idsL := Tree.rec_1 …` is rejected by the code generator
("does not support recursor `Tree.rec_1`").  So the membership decomposition
`x ∈ ids (node id cs) → x = id ∨ ∃ c ∈ cs, x ∈ ids c.tree` cannot be obtained by `rfl`/`simp`;
it needs `Tree.rec`'s equation lemmas, which the pin does not generate.

Two ways out, both honest and neither assumed here:

1. **Reformulate `Support` over `size` instead of `ids`.**  `size` has a clean equation —
   `FibHeapForest.size_node : (Tree.node id cs).size = 1 + sizeSum cs` — so `Support` can be
   stated as "the subtree has `size` many distinct live slots"
   (`∃ s : Finset ℕ, s.card = size ∧ ∀ x ∈ s, x < n`), and `size_le_of_support` becomes
   `card ≤ n` from a subset of `range n`.  Distinctness then reduces to union bounds over child
   sets, which is where `KidsNodup` + `ParOK` are consumed.
2. **Prove the `ids` equations by recursion on the tree** and keep the `ids` formulation.

Option 1 is the cheaper road and is what the next round should take; this module does not assume
either.

## `KidsNodup` must be maintained, not derived

Nothing in `MarkOK`/`PosOK`/`ParOK`/`SlotOK`/`ParSlot`/`NoCycle` forces two ring positions to name
different slots — a malformed ring would read one child twice and still satisfy all of them.  So
`KidsNodup` joins the machine invariants and the updaters must preserve it:

* **link** (append before the head): the appended root is a distinct root, and `NoCycle` gives it
  is not already inside its new parent's child list; head and old successor are untouched.
* **consolidate**: links only, so the same argument applies once per link.
* **cut**: deletes one position; distinctness of the rest is inherited.
* **promote**: the child list is discarded wholesale.

`pos_link` and `pos_cut` are proved at list level; the updater work is where these are discharged.
-/

namespace Submission.FibHeapSupport

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapForest

/-- The children read out of one ring are pairwise distinct.  A machine invariant, not a theorem:
a malformed ring can read one child twice and still satisfy every other predicate. -/
def KidsNodup (st : HState) (p : ℕ) : Prop :=
  ∀ j k, j < k → k < st.deg p → (kids st p).getD j 0 ≠ (kids st p).getD k 0

/-- **A node sits at exactly one depth.**  Two depths for one node close a `par` cycle of positive
length, which the strengthened `NoCycle` forbids. -/
theorem reach_unique_depth (st : HState) (hpar : ParOK st) (hcyc : NoCycle st) {p x i j : ℕ}
    (hi : Reach st i p x) (hj : Reach st j p x) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have h1 : (st.par^[i]) x = p := reach_par st hpar i p x hi
    have h2 : (st.par^[j]) x = p := reach_par st hpar j p x hj
    have hsplit : (st.par^[j]) x = (st.par^[j - i]) p := by
      have h := Function.iterate_add_apply (f := st.par) (m := j - i) (n := i) (x := x)
      rw [show j - i + i = j by omega] at h
      rw [h, h1]
    exact absurd (hsplit.symm.trans h2) (hcyc p (j - i) (by omega))
  · exact heq
  · have h1 : (st.par^[i]) x = p := reach_par st hpar i p x hi
    have h2 : (st.par^[j]) x = p := reach_par st hpar j p x hj
    have hsplit : (st.par^[i]) x = (st.par^[i - j]) p := by
      have h := Function.iterate_add_apply (f := st.par) (m := i - j) (n := j) (x := x)
      rw [show i - j + j = i by omega] at h
      rw [h, h2]
    exact absurd (hsplit.symm.trans h1) (hcyc p (i - j) (by omega))

end Submission.FibHeapSupport
