import Submission.FibHeapAccounting
import Mathlib.Data.List.Enum

/-!
# Abstract link-order and one-child-loss accounting for Fibonacci trees

A `Child` records its degree at link time and the number of children subsequently lost.  The
abstract invariant says `currentDegree + lost = linkDegree`, `lost ≤ 1`, and the zero-based link
position is at most `linkDegree`.  This is the precise interface supplied by equal-degree linking
and CLRS cascading cuts; no mutable forest or RAM semantics is asserted here.
-/

namespace Submission.FibHeapForest

mutual
inductive Tree where
  | node (id : ℕ) (children : List Child)
inductive Child where
  | mk (tree : Tree) (linkDegree lost : ℕ)
end

/-- Current degree is the current number of children. -/
def Tree.degree (t : Tree) : ℕ :=
  match t with
  | .node _ children => children.length

/-- Access the subtree carried by a linked child. -/
def Child.tree (c : Child) : Tree :=
  match c with
  | .mk tree _ _ => tree

/-- Access the degree recorded at link time. -/
def Child.linkDegree (c : Child) : ℕ :=
  match c with
  | .mk _ linkDegree _ => linkDegree

/-- Access the number of children lost after linking. -/
def Child.lost (c : Child) : ℕ :=
  match c with
  | .mk _ _ lost => lost

/-- Pre-order identifiers of every represented live node, including every sibling subtree. -/
noncomputable def ids (t : Tree) : List ℕ :=
  Tree.rec (motive_1 := fun _ => List ℕ) (motive_2 := fun _ => List ℕ)
    (motive_3 := fun _ => List ℕ)
    (fun id _ childIds => id :: childIds)
    (fun _ _ _ treeIds => treeIds)
    []
    (fun _ _ headIds tailIds => headIds ++ tailIds)
    t

/-- Abstract live-node count before a distinctness assertion is applied. -/
noncomputable def Tree.size (t : Tree) : ℕ := (ids t).length

/-- The represented size of a linked child. -/
noncomputable def Child.size (c : Child) : ℕ := c.tree.size

/-- Sum of represented child sizes. -/
noncomputable def sizeSum (children : List Child) : ℕ := (children.map Child.size).sum

/-- Every represented tree has positive size. -/
theorem size_pos (t : Tree) : 0 < t.size := by
  cases t with
  | node id children => simp [Tree.size, ids]

/-- Length of the recursively collected child identifiers is the sum of child sizes. -/
theorem ids_list_length (children : List Child) :
    (Tree.rec_1 (fun id _ childIds => id :: childIds) (fun _ _ _ treeIds => treeIds) []
      (fun _ _ headIds tailIds => headIds ++ tailIds) children : List ℕ).length = sizeSum children := by
  refine Tree.rec_1
    (motive_1 := fun (t : Tree) => (ids t).length = t.size)
    (motive_2 := fun (c : Child) => (ids c.tree).length = c.tree.size)
    (motive_3 := fun (cs : List Child) => (Tree.rec_1 (fun id _ childIds => id :: childIds)
      (fun _ _ _ treeIds => treeIds) [] (fun _ _ headIds tailIds => headIds ++ tailIds) cs : List ℕ).length
      = sizeSum cs)
    ?_ ?_ ?_ ?_ children
  · intro id cs ih
    rfl
  · intro tree link lost ih
    rfl
  · simp [sizeSum]
  · intro head tail ihh iht
    simp [sizeSum, List.length_append, iht]
    cases head with
    | mk tree link lost =>
      simpa [Child.size, Child.tree, ids] using ihh

/-- The represented size of a node is one plus the sum of its child sizes. -/
theorem size_node (id : ℕ) (children : List Child) :
    (Tree.node id children).size = 1 + sizeSum children := by
  simp [Tree.size, ids, sizeSum, ids_list_length]
  omega

/-- Child count is at most the sum of positive child sizes. -/
theorem degree_le_sizeSum (children : List Child) : children.length ≤ sizeSum children := by
  induction children with
  | nil => simp [sizeSum]
  | cons c tail ih =>
    have hp : 0 < c.size := by simpa [Child.size] using size_pos c.tree
    simp only [sizeSum] at ih
    simp only [sizeSum, List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- A represented tree has fewer children than live nodes. -/
theorem degree_lt_size (t : Tree) : t.degree < t.size := by
  cases t with
  | node id children =>
    rw [size_node]
    have h := degree_le_sizeSum children
    simp only [Tree.degree]
    omega

/-- Slot safety follows from live size alone, including every tiny `n`. -/
theorem degree_slot_of_live {t : Tree} {n : ℕ} (hs : t.size ≤ n) : t.degree < n + 1 := by
  have h := degree_lt_size t
  omega

/-- All represented live IDs are distinct, including IDs in different sibling subtrees. -/
def LiveDistinct (t : Tree) : Prop := (ids t).Nodup

/-- Under child/live distinctness, represented size is exactly the finite live-set cardinality. -/
theorem live_card {t : Tree} (h : LiveDistinct t) : (ids t).toFinset.card = t.size := by
  exact List.toFinset_card_of_nodup h

/-- The full abstract link-order and one-loss invariant, as an inductive predicate over the
tree.  For every linked child of a node: its current degree plus its lost count equals its
recorded link degree (link-time degree equality), at most one child was lost since linking
(the CLRS one-loss rule), the zero-based link position is at most the link degree (children
are stored in link order), and the child subtree itself satisfies `InvOK`.  This is exactly
the static interface supplied by equal-degree linking and cascading cuts; no mutable
semantics is asserted here. -/
inductive InvOK : Tree → Prop
  | mk : (id : ℕ) → (children : List Child) →
      (∀ c ∈ children, c.tree.degree + c.lost = c.linkDegree ∧ c.lost ≤ 1) →
      (∀ j, j < children.length → j ≤ (children.getD j (Child.mk (.node 0 []) 0 0)).linkDegree) →
      (∀ c ∈ children, InvOK c.tree) →
      InvOK (.node id children)

/-- The represented size of a member child is at most the summed child sizes. -/
theorem size_le_sizeSum {c : Child} {children : List Child} (h : c ∈ children) :
    c.size ≤ sizeSum children := by
  induction children with
  | nil => cases h
  | cons a tail ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [sizeSum]
    · have hih := ih h'
      simp only [sizeSum, List.map_cons, List.sum_cons] at hih ⊢
      omega

end Submission.FibHeapForest
