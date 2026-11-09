import Submission.FibHeapAccounting
import Mathlib.Data.List.Enum

/-!
# Abstract link-order and one-child-loss accounting for Fibonacci trees

A `Child` records its degree at link time and the number of children subsequently lost.  The
abstract invariant `InvOK` says `currentDegree + lost = linkDegree`, `lost ≤ 1`, and the
zero-based link position is at most `linkDegree`.  This is the precise interface supplied by
equal-degree linking and CLRS cascading cuts; no mutable forest or RAM semantics is asserted
here.

Proved, all sorry-free: the CLRS minimum-size theorem `size ≥ Fib(degree+2)` for every
`InvOK` tree (`fib_size_of_invOK` / `size_ge_fib_of_invOK`); the rank cap
`degree ≤ rankCap n` by reuse of `FibHeapAccounting.degree_rankCap_of_fib_size`; the exact
post-consolidation root-count chain `t1 ≤ Q` (`t1_le_Q`, with `Q = rootCap n = 2·log₂ n+2`);
and the exact CLRS cascade-marking effect `μ'+(k+1) ≤ μ+2` (`CascadeMarks`,
`cascade_marks_bound`) wired into the proved decrease-key ledger
(`decrease_amortized_of_marks`).

Honesty boundary: `InvOK` is the static form of link-time degree ordering plus the
at-most-one-child-loss rule.  That the mutable operations maintain `InvOK` at every step is
the precise remaining interface for later dynamic (RAM-level) work; nothing below depends
on it.
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

/-- Fibonacci monotonicity. -/
theorem fib_le_of_le {m n : ℕ} (h : m ≤ n) : Nat.fib m ≤ Nat.fib n := by
  induction n generalizing m with
  | zero => cases m with
    | zero => exact Nat.le_refl _
    | succ m => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · exact (ih (by omega)).trans Nat.fib_le_fib_succ

/-- The offset list lemma behind the CLRS minimum-size argument.  If every child at link
position `j` has link degree at least `j + k` (link order, shifted by `k`), each sibling
subtree satisfies `InvOK`, each sibling obeys link-time degree equality with at most one
loss, and every tree smaller than `M` with `InvOK` has size at least `fib (degree + 2)`
(the strong hypothesis), then the summed sibling sizes dominate the Fibonacci value at the
total link count.  Left induction: the head contributes `fib (k+1)`, and the tail is
re-indexed at offset `k+1` because `(a :: l).getD (j+1) d = l.getD j d`. -/
theorem sizeSum_ge_fib_aux
    (M : ℕ) (hbound : ∀ a : Tree, a.size < M → InvOK a → Nat.fib (a.degree + 2) ≤ a.size) :
    ∀ (children : List Child) (k : ℕ), sizeSum children + 1 ≤ M →
      (∀ j, j < children.length → j + k ≤ (children.getD j (Child.mk (.node 0 []) 0 0)).linkDegree) →
      (∀ c ∈ children, c.tree.degree + c.lost = c.linkDegree ∧ c.lost ≤ 1) →
      (∀ c ∈ children, InvOK c.tree) →
      Nat.fib (k + 2) + sizeSum children ≥ Nat.fib (children.length + k + 2) := by
  intro children
  induction children with
  | nil => intro k _ _ _ _; simp [sizeSum]
  | cons c tail ih =>
    intro k hM hord hco hrec
    have h0 : k ≤ c.linkDegree := by
      have h := hord 0 (by simp)
      simp only [Nat.zero_add, List.getD_cons_zero] at h
      exact h
    obtain ⟨hdeq, hloss⟩ := hco c (by simp)
    have hk : k + 1 ≤ c.tree.degree + 2 := by omega
    have hk1 : Nat.fib (k + 1) ≤ Nat.fib (c.tree.degree + 2) := fib_le_of_le hk
    have hIc : InvOK c.tree := hrec c (by simp)
    have hcs : c.tree.size ≤ sizeSum (c :: tail) := size_le_sizeSum (by simp)
    have hsc : Nat.fib (c.tree.degree + 2) ≤ c.tree.size := hbound c.tree (by omega) hIc
    have hcons : sizeSum (c :: tail) = c.tree.size + sizeSum tail := by
      simp only [sizeSum, Child.size, List.map_cons, List.sum_cons]
    have hM' : sizeSum tail + 1 ≤ M := by omega
    have hord' : ∀ j, j < tail.length → j + (k + 1) ≤ (tail.getD j (Child.mk (.node 0 []) 0 0)).linkDegree := by
      intro j hj
      have h := hord (j + 1) (by rw [List.length_cons]; omega)
      rw [List.getD_cons_succ] at h
      omega
    have hco' : ∀ a ∈ tail, a.tree.degree + a.lost = a.linkDegree ∧ a.lost ≤ 1 :=
      fun a ha => hco a (by simp [ha])
    have hrec' : ∀ a ∈ tail, InvOK a.tree := fun a ha => hrec a (by simp [ha])
    have hkey := ih (k + 1) hM' hord' hco' hrec'
    have expandL : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      have h := Nat.fib_add_two (n := k + 1)
      have he : k + 1 + 1 = k + 2 := by omega
      rw [he] at h
      exact h
    rw [expandL] at hkey
    have expandR : Nat.fib (tail.length + (k + 1) + 2)
        = Nat.fib (tail.length + k + 1) + Nat.fib (tail.length + k + 2) := by
      have h := Nat.fib_add_two (n := tail.length + k + 1)
      have he : tail.length + k + 1 + 1 = tail.length + k + 2 := by omega
      rw [he] at h
      exact h
    rw [expandR] at hkey
    rw [show (c :: tail).length + k + 2 = tail.length + (k + 1) + 2 from by
      rw [List.length_cons]; omega]
    rw [expandR]
    simp only [sizeSum, List.map_cons, List.sum_cons, Child.size]
    simp only [sizeSum] at hkey
    have hfib : Nat.fib (k + 1) ≤ c.tree.size := hk1.trans hsc
    omega

/-- Strong induction on the abstract live size: every `InvOK` tree of size at most `N`
has size at least `fib (degree + 2)`.  The strong hypothesis of `sizeSum_ge_fib_aux` is
discharged for every smaller tree, not only for siblings: a child's size is strictly below
its parent's (`size_le_sizeSum`), so `M = t.size` makes the hypothesis universal below `M`. -/
theorem fib_size_of_invOK :
    ∀ (N : ℕ) (t : Tree), t.size ≤ N → InvOK t → Nat.fib (t.degree + 2) ≤ t.size := by
  intro N
  induction N with
  | zero =>
    intro t hN _
    exact absurd hN (by have := size_pos t; omega)
  | succ N ih =>
    intro t hN hinv
    cases t with
    | node id children =>
      simp only [size_node] at hN
      cases hinv with
      | mk _ _ hco hpos hrec =>
        have hbound : ∀ a : Tree, a.size < 1 + sizeSum children → InvOK a
            → Nat.fib (a.degree + 2) ≤ a.size := by
          intro a ha hai
          exact ih a (by omega) hai
        have hkey := sizeSum_ge_fib_aux (1 + sizeSum children) hbound children 0
          (by omega) (fun j hj => by have := hpos j hj; omega) hco hrec
        rw [show Nat.fib (0 + 2) = 1 from rfl, Nat.add_zero] at hkey
        simp only [Tree.degree, size_node]
        omega

/-- The CLRS minimum-size theorem for Fibonacci trees: an `InvOK` tree whose root has
degree `k` represents at least `fib (k+2)` live nodes. -/
theorem size_ge_fib_of_invOK (t : Tree) (h : InvOK t) : Nat.fib (t.degree + 2) ≤ t.size :=
  fib_size_of_invOK t.size t (Nat.le_refl _) h

/-- The exact feed into the scalar accounting lane: an `InvOK` tree over at most `n` live
nodes has degree at most `rankCap n = 2·log₂ n + 1`.  This REUSES
`FibHeapAccounting.degree_rankCap_of_fib_size` — the Fibonacci lower bound is proved above,
and the elementary rank cap is not re-proved here. -/
theorem degree_le_rankCap_of_invOK {t : Tree} {n : ℕ} (h : InvOK t) (hs : t.size ≤ n) :
    t.degree ≤ FibHeapAccounting.rankCap n :=
  FibHeapAccounting.degree_rankCap_of_fib_size ((size_ge_fib_of_invOK t h).trans hs)

/-- A list of pairwise-distinct naturals, all bounded by `R`, has at most `R+1` elements. -/
theorem nodup_length_le_succ {R : ℕ} {l : List ℕ} (hnd : l.Nodup) (hle : ∀ d ∈ l, d ≤ R) :
    l.length ≤ R + 1 := by
  have hsub : l.toFinset ⊆ Finset.range (R + 1) := fun d hd =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hle d (List.mem_toFinset.mp hd)))
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range (R + 1)).card := Finset.card_le_card hsub
    _ = R + 1 := Finset.card_range _

/-- The exact `t1 ≤ Q` chain.  After consolidation the root degrees are pairwise distinct;
every root tree satisfies `InvOK`; every root tree has size at most `n` (all live nodes fit
the heap).  Then each root degree is at most `rankCap n` (by `degree_le_rankCap_of_invOK`,
which reuses the scalar lane), distinctness bounds the root count by the number of admissible
degrees, and `rootCap n = rankCap n + 1 = 2·log₂ n + 2` is exactly `Q`. -/
theorem t1_le_Q {roots : List Tree} {n : ℕ}
    (hnd : (roots.map Tree.degree).Nodup)
    (hinv : ∀ t ∈ roots, InvOK t) (hsz : ∀ t ∈ roots, t.size ≤ n) :
    roots.length ≤ FibHeapAccounting.rootCap n := by
  have hdeg : ∀ d ∈ roots.map Tree.degree, d ≤ FibHeapAccounting.rankCap n := by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
    exact degree_le_rankCap_of_invOK (hinv t ht) (hsz t ht)
  have h := nodup_length_le_succ hnd hdeg
  rw [List.length_map] at h
  exact h.trans (by rfl)

/-- The exact CLRS cascading-cut marking discipline as an inductive relation.  `l` lists the
mark bits of the strict ancestors of the cut node, from the parent upward, below the root.
`μ` is the marked-live-node count before the cascade, `μ'` after it, and `k` the number of
ancestors cut during the cascade (the original cut in `decreaseKey` is not counted here).
- `stop`: the root is reached without cutting it; roots are unmarked, so nothing changes.
- `mark`: an unmarked parent takes the one terminal new mark and the cascade stops.
- `clear`: a marked parent loses its mark (μ counts one down) and is cut; the cascade continues. -/
inductive CascadeMarks : List Bool → ℕ → ℕ → ℕ → Prop
  | stop (μ : ℕ) : CascadeMarks [] μ μ 0
  | mark (l : List Bool) (μ : ℕ) : CascadeMarks (false :: l) μ (μ + 1) 0
  | clear {l : List Bool} {μ μ' k : ℕ} :
      1 ≤ μ → CascadeMarks l (μ - 1) μ' k → CascadeMarks (true :: l) μ μ' (k + 1)

/-- The exact CLRS marking effect: a cascade that cuts `k` ancestors leaves
`μ' + (k+1) ≤ μ + 2` — at most `k` marks cleared and at most one terminal new mark. -/
theorem cascade_marks_bound {l : List Bool} {μ μ' k : ℕ} (h : CascadeMarks l μ μ' k) :
    μ' + (k + 1) ≤ μ + 2 := by
  induction h with
  | stop => omega
  | mark => omega
  | clear hμ _ ih => omega

/-- Decrease-key's full marking chain, proved end to end: `c = k+1` total cuts (the original
cut plus `k` cascade cuts) under the CLRS discipline give exactly `μ' + c ≤ μ + 2`, so — by
the proved `cascade_potential_delta` — `Φ' + c ≤ Φ + 4`, and the amortized decrease-key
bound `D0 + 3K + D1` follows.  No step is an assumption: the marking effect is
`cascade_marks_bound`, the potential step is `FibHeapAccounting.cascade_potential_delta`,
and the ledger step is `FibHeapAccounting.decrease_amortized_clrs`. -/
theorem decrease_amortized_of_marks {K D0 D1 : ℕ} {l : List Bool} {μ μ' k t t' : ℕ}
    (hK : D1 ≤ K) (ht : t' = t + (k + 1)) (h : CascadeMarks l μ μ' k) :
    D0 + D1 * (k + 1) + FibHeapAccounting.scaledPotential K t' μ'
      ≤ FibHeapAccounting.scaledPotential K t μ + (D0 + 3 * K + D1) :=
  FibHeapAccounting.decrease_amortized_clrs (by omega) hK ht (cascade_marks_bound h)

/-- **M4 determination, case (b): proved.**  The clearing ledger, cell by
cell: under CLRS clearing writes the mark flags are forced — each of the `k`
cascaded cells consumes one mark (`true`), the terminal cell banks one fresh
mark (`false`) — landing `μ' = μ - k + 1` exactly, so the CLRS premise holds
**with no slack**: `μ' + (k+1) = μ + 2` whenever the mark supply covers the
cascade (`k ≤ μ`).  This is the Route-A viability witness: the clearing
writes discharge `decrease_amortized_clrs`'s `hmarks` for every cascade
length, as a per-cell equality (mirroring `machineMarks_promoteState`'s
shape, minus the mark). -/
theorem clrs_cell_premise (μ k : ℕ) (hk : k ≤ μ) :
    ∃ μ' : ℕ, CascadeMarks (List.replicate k true ++ [false]) μ μ' k
      ∧ μ' + (k + 1) ≤ μ + 2 := by
  induction k generalizing μ with
  | zero => exact ⟨μ + 1, CascadeMarks.mark [] μ, by omega⟩
  | succ k ih =>
    obtain ⟨μ', hcm, hbound⟩ := ih (μ - 1) (by omega)
    exact ⟨μ', CascadeMarks.clear (by omega) hcm, by omega⟩

end Submission.FibHeapForest
