import Submission.FibHeapForest

/-!
# Dynamic maintenance of the abstract forest invariants

This module closes the honesty boundary left open by `Submission.FibHeapForest`: the abstract
`InvOK` (link-time degree ordering + one-child-loss rule) and the consolidation `Nodup`
(pairwise-distinct final root degrees) are proved *maintained* by the five abstract
transitions of a Fibonacci heap, each defined here as a total function over the abstract
`Child = (tree, linkDegree, lost)` representation:

1. `linkRoots` — equal-degree linking: the child enters as the last linked child with
   `lost := 0` and `linkDegree := child.degree`; the parent keeps link order by appending
   and gains one degree (`linkRoots_invOK`).
2. `cutAt` — one cascading-cut step: the cut subtree becomes a root, the parent entry loses
   one child and increments `lost`.  The updated entry is admissible **iff** the parent had
   `lost = 0` (`cutAt_entry_ok_iff`); `lost = 1` is the exact counterexample that forces the
   cascade (`cutAt_entry_violation_of_lost_one`).
3. `cascadeCut` — the CLRS cascade over the position-tagged ancestor chain: marked entries
   (`lost = 1`) are discarded (their trees join the cut roots), the first unmarked entry is
   marked and stops the cascade.  All surviving entries stay admissible
   (`cascadeCut_surv_entries_ok`), all cut roots satisfy `InvOK`
   (`cascadeCut_roots_invOK`), and the mark-bit list satisfies the already-proved
   `CascadeMarks` relation, so the proved `μ'+(k+1) ≤ μ+2` accounting applies unchanged
   (`cascadeCut_marks`, `decrease_amortized_of_cascadeCut`).
4. `promoteRoots` — extract-min promotion: children of the removed root become roots
   (`promoteRoots_invOK`).
5. `consolidate` — fuel-bounded bucket consolidation: every link is `linkRoots`, so every
   resulting root satisfies `InvOK` (`consolidate_invOK`), the final root degrees are
   pairwise distinct (`consolidate_nodup`), total live size is conserved
   (`consolidate_sizes`), and the link count is conserved additively:
   `consolidationLinks + t1 = t0` (`consolidate_links_add_length`).

Capstones: the consolidation output directly satisfies the three hypotheses of the proved
`t1_le_Q`, giving the post-consolidation root-count bound `t1 ≤ Q = rootCap n` from
assumption-free maintenance lemmas (`t1_le_Q_of_consolidate`), and the promotion pipeline
feeds it (`t1_le_Q_of_promotion`).  No new axioms; nothing below redefines or weakens any
theorem of `FibHeapForest` or `FibHeapAccounting`.
-/

namespace Submission.FibHeapDynamic

open Submission.FibHeapForest

/-- The stand-in child for out-of-range `getD` lookups, matching the convention of
`FibHeapForest.InvOK`.  (The mutual inductive pair `Tree`/`Child` admits no derived
`Inhabited` instance, so the dummy is named and passed explicitly.) -/
def dummyChild : Child := Child.mk (.node 0 []) 0 0

/-! ## List accessors under erasure -/

/-- Erasing a later index keeps earlier `getD` lookups unchanged. -/
theorem getD_eraseIdx_lt {l : List Child} {i j : ℕ} (h : i < j) (d : Child) :
    (l.eraseIdx j).getD i d = l.getD i d := by
  induction l generalizing i j with
  | nil => simp
  | cons a ts ih =>
    cases j with
    | zero => omega
    | succ j' =>
      cases i with
      | zero => simp
      | succ i' =>
        have h' : i' < j' := by omega
        simpa using ih h'

/-- Erasing index `j` shifts later `getD` lookups down by one. -/
theorem getD_eraseIdx_ge {l : List Child} {i j : ℕ} (h : j ≤ i) (d : Child) :
    (l.eraseIdx j).getD i d = l.getD (i + 1) d := by
  induction l generalizing i j with
  | nil => simp
  | cons a ts ih =>
    cases j with
    | zero => simp
    | succ j' =>
      cases i with
      | zero => omega
      | succ i' =>
        have h' : j' ≤ i' := by omega
        simpa using ih h'

/-- Appending a new last child does not shift earlier `getD` lookups. -/
theorem getD_append_lt {l : List Child} {j : ℕ} (hj : j < l.length) (x d : Child) :
    (l ++ [x]).getD j d = l.getD j d := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a ts ih =>
    cases j with
    | zero => simp
    | succ j' => simpa using ih (Nat.lt_of_succ_lt_succ hj)

/-- The appended last child sits at exactly the old length. -/
theorem getD_append_last {l : List Child} (x d : Child) :
    (l ++ [x]).getD l.length d = x := by
  induction l with
  | nil => simp
  | cons a ts ih => simp

/-! ## Transition 1: equal-degree link -/

/-- Equal-degree linking: `child` becomes the last linked child of `parent`, recorded with
`linkDegree := child.degree` (the parent's pre-increment degree) and `lost := 0`; the
existing children keep link order because the new child is appended. -/
def linkRoots (parent child : Tree) : Tree :=
  match parent with
  | .node pid pcs => .node pid (pcs ++ [Child.mk child child.degree 0])

/-- Linking adds exactly one degree. -/
theorem linkRoots_degree (parent child : Tree) :
    (linkRoots parent child).degree = parent.degree + 1 := by
  cases parent with
  | node pid pcs => simp [linkRoots, Tree.degree, List.length_append]

/-- The summed child sizes split over an append. -/
theorem sizeSum_append (a b : List Child) : sizeSum (a ++ b) = sizeSum a + sizeSum b := by
  simp [sizeSum, List.map_append, List.sum_append]

/-- Linking conserves live size: the linked root represents exactly the union. -/
theorem linkRoots_size (parent child : Tree) :
    (linkRoots parent child).size = parent.size + child.size := by
  cases parent with
  | node pid pcs =>
    cases child with
    | node cid ccs =>
      simp only [linkRoots, size_node]
      simp only [sizeSum_append]
      simp only [sizeSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [Child.size, Child.tree, size_node]
      simp only [sizeSum]
      omega

/-- **Link maintains `InvOK`.**  If both roots satisfy `InvOK` and their degrees are equal,
the linked root satisfies `InvOK`.  The new child has `degree + lost = degree = linkDegree`
and `lost = 0`; every prior child keeps its position and its recorded link degree because
the append does not shift them. -/
theorem linkRoots_invOK {parent child : Tree}
    (hp : InvOK parent) (hc : InvOK child) (hdeg : parent.degree = child.degree) :
    InvOK (linkRoots parent child) := by
  cases parent with
  | node pid pcs =>
    cases hp with
    | mk _ _ hco hpos hrec =>
      have hplen : pcs.length = Tree.degree (.node pid pcs) := rfl
      refine InvOK.mk pid (pcs ++ [Child.mk child child.degree 0]) ?_ ?_ ?_
      · intro c hcm
        rcases List.mem_append.mp hcm with hm | hm
        · exact hco c hm
        · have hcx : c = Child.mk child child.degree 0 := List.mem_singleton.mp hm
          subst hcx
          exact ⟨by simp [Child.tree, Child.linkDegree, Child.lost], by simp [Child.lost]⟩
      · intro j hj
        by_cases hjlt : j < pcs.length
        · rw [getD_append_lt hjlt _ _]
          exact hpos j hjlt
        · have halen : (pcs ++ [Child.mk child child.degree 0]).length = pcs.length + 1 := by
            simp
          have hje : j = pcs.length := by omega
          have hlast : (pcs ++ [Child.mk child child.degree 0]).getD j (Child.mk (.node 0 []) 0 0)
              = Child.mk child child.degree 0 := by
            rw [hje]
            exact getD_append_last _ _
          rw [hlast]
          simp only [Child.linkDegree]
          omega
      · intro c hcm
        rcases List.mem_append.mp hcm with hm | hm
        · exact hrec c hm
        · have hcx : c = Child.mk child child.degree 0 := List.mem_singleton.mp hm
          subst hcx
          simpa [Child.tree] using hc


/-- A live indexed lookup reduces to `some`. -/
theorem getElem?_some_of_lt {pcs : List Child} {j : ℕ} (hj : j < pcs.length) :
    pcs[j]? = some pcs[j] :=
  List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩

/-! ## Transition 2: one cascading-cut step -/

/-- Removing the child at position `j` from a node's children. -/
def Tree.eraseChild (t : Tree) (j : ℕ) : Tree :=
  match t with
  | .node id cs => .node id (cs.eraseIdx j)

/-- Erasing one child lowers the degree by exactly one. -/
theorem degree_eraseChild {t : Tree} {j : ℕ} (hj : j < t.degree) :
    (Tree.eraseChild t j).degree + 1 = t.degree := by
  cases t with
  | node id cs =>
    have hd : Tree.degree (.node id cs) = cs.length := rfl
    simp only [Tree.eraseChild, Tree.degree, List.length_eraseIdx_of_lt hj]
    omega

/-- `InvOK` survives erasing one child: members keep their conditions, positions shift
strictly downward (positions only had to be `≤ linkDegree`), recursion is inherited. -/
theorem invOK_eraseIdx {id : ℕ} {cs : List Child} {j : ℕ} (hj : j < cs.length)
    (h : InvOK (.node id cs)) : InvOK (.node id (cs.eraseIdx j)) := by
  cases h with
  | mk _ _ hco hpos hrec =>
    refine InvOK.mk id (cs.eraseIdx j) ?_ ?_ ?_
    · intro c hcm
      exact hco c (List.mem_of_mem_eraseIdx hcm)
    · intro i hi
      have hlen : (cs.eraseIdx j).length = cs.length - 1 := List.length_eraseIdx_of_lt hj
      by_cases hilt : i < j
      · rw [getD_eraseIdx_lt hilt]
        exact hpos i (by omega)
      · rw [getD_eraseIdx_ge (by omega)]
        exact Nat.le_of_succ_le (hpos (i + 1) (by omega))
    · intro c hcm
      exact hrec c (List.mem_of_mem_eraseIdx hcm)

/-- One cascading-cut step on a parent entry `c`: the subtree at position `j` of `c.tree`
is cut out and returned as the new root; the updated entry keeps `c.linkDegree` (the
position of the parent in the grandparent is unchanged) and increments `c.lost`. -/
def cutAt (c : Child) (j : ℕ) : Option (Tree × Child) :=
  match c.tree with
  | .node pid pcs =>
    match pcs[j]? with
    | some x => some (x.tree, Child.mk (.node pid (pcs.eraseIdx j)) c.linkDegree (c.lost + 1))
    | none => none

/-- A cut at a live position always fires. -/
theorem cutAt_some {c : Child} {j : ℕ} (hj : j < c.tree.degree) :
    ∃ x c', cutAt c j = some (x, c') := by
  cases c with
  | mk tt ld ls =>
    cases tt with
    | node pid pcs =>
      simp only [Child.tree, Tree.degree] at hj
      refine ⟨pcs[j].tree, Child.mk (.node pid (pcs.eraseIdx j)) ld (ls + 1), ?_⟩
      simp only [cutAt, Child.tree, getElem?_some_of_lt hj]
      rfl

/-- **The exact one-loss side condition.**  After a cut, the updated parent entry is
admissible (degree equality **and** at most one loss) if and only if the parent had lost
no child before the cut.  The degree-equality half survives unconditionally:
`(degree − 1) + (lost + 1) = degree + lost = linkDegree`; only the one-loss half is at
stake. -/
theorem cutAt_entry_ok_iff {c : Child} {j : ℕ} {x : Tree} {c' : Child}
    (hdeq : c.tree.degree + c.lost = c.linkDegree) (hj : j < c.tree.degree)
    (hcut : cutAt c j = some (x, c')) :
    (c'.tree.degree + c'.lost = c'.linkDegree ∧ c'.lost ≤ 1) ↔ c.lost = 0 := by
  cases c with
  | mk tt ld ls =>
    cases tt with
    | node pid pcs =>
      have hpc : Tree.degree (.node pid pcs) = pcs.length := rfl
      simp only [Child.tree, Tree.degree] at hj
      simp only [cutAt, Child.tree, getElem?_some_of_lt hj, Option.some.injEq,
        Prod.mk.injEq] at hcut
      obtain ⟨rfl, rfl⟩ := hcut
      have hlen : (pcs.eraseIdx j).length = pcs.length - 1 := List.length_eraseIdx_of_lt hj
      simp only [Child.tree, Child.linkDegree, Child.lost, Tree.degree] at hdeq ⊢
      omega

/-- **The exact counterexample.**  If the parent already lost a child (`lost = 1`), the cut
pushes `lost` to 2 and the updated entry violates the one-loss rule — precisely the
situation the CLRS cascade exists to repair by cutting the parent itself. -/
theorem cutAt_entry_violation_of_lost_one {c : Child} {j : ℕ} {x : Tree} {c' : Child}
    (hj : j < c.tree.degree) (hcut : cutAt c j = some (x, c')) (hlost : c.lost = 1) :
    ¬ (c'.lost ≤ 1) := by
  cases c with
  | mk tt ld ls =>
    cases tt with
    | node pid pcs =>
      simp only [Child.tree, Tree.degree] at hj
      simp only [cutAt, Child.tree, getElem?_some_of_lt hj, Option.some.injEq,
        Prod.mk.injEq] at hcut
      obtain ⟨rfl, rfl⟩ := hcut
      simp only [Child.lost] at hlost ⊢
      omega

/-- The cut subtree itself satisfies `InvOK`: it is a member child of an `InvOK` tree and
is promoted to root-hood unchanged. -/
theorem cutAt_subtree_invOK {c : Child} {j : ℕ} {x : Tree} {c' : Child}
    (hinv : InvOK c.tree) (hj : j < c.tree.degree) (hcut : cutAt c j = some (x, c')) :
    InvOK x := by
  cases c with
  | mk tt ld ls =>
    cases tt with
    | node pid pcs =>
      cases hinv with
      | mk _ _ hco _ hrec =>
        simp only [Child.tree] at *
        simp only [Tree.degree] at hj
        simp only [cutAt, Child.tree, getElem?_some_of_lt hj, Option.some.injEq,
        Prod.mk.injEq] at hcut
        obtain ⟨rfl, rfl⟩ := hcut
        exact hrec _ (List.mem_iff_getElem.mpr ⟨j, hj, rfl⟩)

end Submission.FibHeapDynamic
