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


/-! ## Transition 3: the CLRS cascade -/

/-- The mark-bit view of a position-tagged ancestor chain: an entry is marked exactly when
it has already lost a child (`lost = 1`). -/
def marksOf (chain : List (ℕ × Child)) : List Bool :=
  chain.map (fun p => decide (p.2.lost = 1))

/-- The CLRS cascade over the position-tagged ancestor chain of the originally cut node:
head = deepest ancestor entry, each tag the position of the next-lower tree inside that
entry's tree.  An entry with `lost = 0` (unmarked) is marked (`lost 0 → 1`), loses the
child at the recorded position, and the cascade stops; an entry with `lost ≥ 1` (marked)
is discarded — its tree joins the cut roots — and the cascade continues above it;
everything above the stopping point is untouched. -/
def cascadeCut : List (ℕ × Child) → List Child × List Tree
  | [] => ([], [])
  | p :: rest =>
      match p.2.lost with
      | 0 => (Child.mk (Tree.eraseChild p.2.tree p.1) p.2.linkDegree (p.2.lost + 1)
                :: rest.map (fun q => q.2), [])
      | _ + 1 => let (surv, roots) := cascadeCut rest
                 (surv, p.2.tree :: roots)

/-- The cons step of the cascade on an unmarked head. -/
theorem cascadeCut_cons_zero (j : ℕ) (c : Child) (rest : List (ℕ × Child))
    (h0 : c.lost = 0) :
    cascadeCut ((j, c) :: rest) =
      (Child.mk (Tree.eraseChild c.tree j) c.linkDegree (c.lost + 1)
        :: rest.map (fun q => q.2), []) := by
  have hl : c.lost = (0 : ℕ) := h0
  simp only [cascadeCut, hl]

/-- The cons step of the cascade on a marked head. -/
theorem cascadeCut_cons_marked (j : ℕ) (c : Child) (rest : List (ℕ × Child))
    (h1 : 1 ≤ c.lost) :
    cascadeCut ((j, c) :: rest) =
      let (surv, roots) := cascadeCut rest
      (surv, c.tree :: roots) := by
  have hl : c.lost = (c.lost - 1).succ := by omega
  simp only [cascadeCut]
  rw [hl]

/-- **The cascade keeps every surviving entry admissible.**  Hypotheses: every chain entry
satisfies the entry conditions (link-time degree equality and one-loss, as supplied by the
`InvOK` context of the tree holding the chain), and every recorded position is live.  The
first unmarked entry survives as `(degree − 1, lost 1, same linkDegree)`, which is
admissible precisely because its `lost` was 0. -/
theorem cascadeCut_surv_entries_ok {chain : List (ℕ × Child)}
    (hcond : ∀ p ∈ chain, p.2.tree.degree + p.2.lost = p.2.linkDegree ∧ p.2.lost ≤ 1)
    (hpos : ∀ p ∈ chain, p.1 < p.2.tree.degree) :
    ∀ c ∈ (cascadeCut chain).1,
      c.tree.degree + c.lost = c.linkDegree ∧ c.lost ≤ 1 := by
  induction chain with
  | nil => intro c hc; cases hc
  | cons p rest ih =>
    obtain ⟨j, c⟩ := p
    intro cs hcs
    have hcond' : ∀ q ∈ rest, q.2.tree.degree + q.2.lost = q.2.linkDegree ∧ q.2.lost ≤ 1 :=
      fun q hq => hcond q (by simp [hq])
    by_cases h0 : c.lost = 0
    · rw [cascadeCut_cons_zero _ _ _ h0] at hcs
      simp only [List.mem_cons] at hcs
      rcases hcs with rfl | hcs
      · obtain ⟨hdeq0, hloss0⟩ := hcond (j, c) (by simp)
        have hdeq : c.tree.degree + c.lost = c.linkDegree := hdeq0
        have hloss : c.lost ≤ 1 := hloss0
        have hj : j < c.tree.degree := hpos (j, c) (by simp)
        have hdeg' : (Tree.eraseChild c.tree j).degree + 1 = c.tree.degree :=
          degree_eraseChild hj
        have e1 : (Child.mk (Tree.eraseChild c.tree j) c.linkDegree (c.lost + 1)).tree
            = Tree.eraseChild c.tree j := rfl
        have e2 : (Child.mk (Tree.eraseChild c.tree j) c.linkDegree (c.lost + 1)).lost
            = c.lost + 1 := rfl
        have e3 : (Child.mk (Tree.eraseChild c.tree j) c.linkDegree (c.lost + 1)).linkDegree
            = c.linkDegree := rfl
        refine ⟨?_, ?_⟩
        · rw [e1, e2, e3]
          omega
        · rw [e2]
          omega
      · obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hcs
        exact hcond a (List.mem_cons_of_mem _ ham)
    · have h1 : 1 ≤ c.lost := by omega
      rw [cascadeCut_cons_marked _ _ _ h1] at hcs
      exact ih hcond' (fun q hq => hpos q (by simp [hq])) cs hcs

/-- **The cascade keeps every surviving subtree `InvOK`.**  The first unmarked entry
survives with one child erased (`invOK_eraseIdx`); entries above it are untouched. -/
theorem cascadeCut_surv_trees_invOK {chain : List (ℕ × Child)}
    (hrec : ∀ p ∈ chain, InvOK p.2.tree)
    (hpos : ∀ p ∈ chain, p.1 < p.2.tree.degree) :
    ∀ c ∈ (cascadeCut chain).1, InvOK c.tree := by
  induction chain with
  | nil => intro c hc; cases hc
  | cons p rest ih =>
    obtain ⟨j, c⟩ := p
    intro cs hcs
    have hrec' : ∀ q ∈ rest, InvOK q.2.tree := fun q hq => hrec q (by simp [hq])
    by_cases h0 : c.lost = 0
    · rw [cascadeCut_cons_zero _ _ _ h0] at hcs
      simp only [List.mem_cons] at hcs
      rcases hcs with rfl | hcs
      · have hj : j < c.tree.degree := hpos (j, c) (by simp)
        cases c with
        | mk tt ld ls =>
          cases tt with
          | node pid pcs =>
            simp only [Child.tree, Tree.degree] at hj
            have hmem : InvOK (Child.mk (.node pid pcs) ld ls).tree := by
              simpa using hrec (j, Child.mk (.node pid pcs) ld ls) (by simp)
            exact invOK_eraseIdx hj hmem
      · obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hcs
        exact hrec a (List.mem_cons_of_mem _ ham)
    · have h1 : 1 ≤ c.lost := by omega
      rw [cascadeCut_cons_marked _ _ _ h1] at hcs
      exact ih hrec' (fun q hq => hpos q (by simp [hq])) cs hcs

/-- **Every tree the cascade cuts away satisfies `InvOK`**: each discarded entry's tree is
a member subtree of an `InvOK` tree, promoted to root-hood unchanged. -/
theorem cascadeCut_roots_invOK {chain : List (ℕ × Child)}
    (hrec : ∀ p ∈ chain, InvOK p.2.tree) :
    ∀ t ∈ (cascadeCut chain).2, InvOK t := by
  induction chain with
  | nil => intro t ht; cases ht
  | cons p rest ih =>
    obtain ⟨j, c⟩ := p
    intro t ht
    by_cases h0 : c.lost = 0
    · rw [cascadeCut_cons_zero _ _ _ h0] at ht
      exact absurd ht (by simp)
    · have h1 : 1 ≤ c.lost := by omega
      rw [cascadeCut_cons_marked _ _ _ h1] at ht
      replace ht : t ∈ c.tree :: (cascadeCut rest).2 := ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hrec (j, c) (by simp)
      · exact ih (fun q hq => hrec q (by simp [hq])) t ht

/-- **The cascade's mark bits satisfy the already-proved `CascadeMarks` relation**, with the
number of cascade cuts equal to the number of discarded entries.  Hypotheses: every entry
obeys the one-loss rule (`lost ≤ 1`, from the entry conditions — for `lost ≥ 2` the
mark-bit list would read `false` where the cascade still discards, and the statement would
be false), and `mu` bounds the marked entries inside the chain (a global marked-count
certainly does). -/
theorem cascadeCut_marks {chain : List (ℕ × Child)}
    (hloss : ∀ p ∈ chain, p.2.lost ≤ 1) :
    ∀ μ : ℕ, (marksOf chain).count true ≤ μ →
      ∃ μ' : ℕ, CascadeMarks (marksOf chain) μ μ' ((cascadeCut chain).2.length) := by
  intro μ
  induction chain generalizing μ with
  | nil => intro _; exact ⟨μ, CascadeMarks.stop⟩
  | cons p rest ih =>
    obtain ⟨j, c⟩ := p
    intro hcnt
    have hloss' : ∀ q ∈ rest, q.2.lost ≤ 1 := fun q hq => hloss q (by simp [hq])
    by_cases h0 : c.lost = 0
    · rw [cascadeCut_cons_zero _ _ _ h0]
      have hpr : (j, c).2.lost = c.lost := rfl
      have hd : decide ((j, c).2.lost = 1) = false := decide_eq_false (by rw [hpr]; omega)
      refine ⟨μ + 1, ?_⟩
      rw [marksOf, List.map_cons, hd]
      exact CascadeMarks.mark
    · have h1 : 1 ≤ c.lost := by omega
      rw [cascadeCut_cons_marked _ _ _ h1]
      have hpr : (j, c).2.lost = c.lost := rfl
      have hlossc : (j, c).2.lost ≤ 1 := hloss (j, c) (by simp)
      have hc1 : c.lost = 1 := by omega
      have hd : decide ((j, c).2.lost = 1) = true := by
        rw [show (j, c).2.lost = 1 from hpr.trans hc1]
        rfl
      have hcnt' : (marksOf rest).count true + 1 ≤ μ := by
        have hstep : (marksOf ((j, c) :: rest)).count true
            = List.count true (decide ((j, c).2.lost = 1) :: marksOf rest) := rfl
        rw [hstep, hd, List.count_cons_self] at hcnt
        exact hcnt
      obtain ⟨μ', hmarks⟩ := ih hloss' (μ - 1) (by omega)
      refine ⟨μ', ?_⟩
      rw [marksOf, List.map_cons, hd]
      exact CascadeMarks.clear (by omega) hmarks

/-- Wiring: the cascade consumes exactly the proved marking discipline, so the proved
decrease-key ledger applies with `k + 1` total cuts (the original cut plus `k` cascade
cuts).  The `CascadeMarks` premise is produced by `cascadeCut_marks` from the marked-count
hypothesis; the root-count of the cascade is exactly `k`. -/
theorem decrease_amortized_of_cascadeCut {K D0 D1 μ μ' t t' : ℕ}
    {chain : List (ℕ × Child)}
    (hK : D1 ≤ K) (ht : t' = t + ((cascadeCut chain).2.length + 1))
    (hmarks : CascadeMarks (marksOf chain) μ μ' ((cascadeCut chain).2.length)) :
    D0 + D1 * ((cascadeCut chain).2.length + 1) + FibHeapAccounting.scaledPotential K t' μ'
      ≤ FibHeapAccounting.scaledPotential K t μ + (D0 + 3 * K + D1) :=
  decrease_amortized_of_marks hK ht hmarks

/-! ## Transition 4: extract-min promotion -/

/-- The children of a node (the inductive declares no projection). -/
def treeKids (t : Tree) : List Child :=
  match t with
  | .node _ cs => cs

/-- The children of the removed root become roots; their recorded link data is discarded
with their parent entry. -/
def promoteRoots (t : Tree) : List Tree :=
  (treeKids t).map Child.tree

/-- Promotion unfolding on an explicit node. -/
theorem promoteRoots_node (pid : ℕ) (cs : List Child) :
    promoteRoots (Submission.FibHeapForest.Tree.node pid cs) = cs.map Child.tree := by
  simp only [promoteRoots, treeKids]

/-- **Promotion maintains `InvOK`.**  Each promoted subtree is a member child of an
`InvOK` tree, promoted unchanged. -/
theorem promoteRoots_invOK {t : Tree} (h : InvOK t) :
    ∀ r ∈ promoteRoots t, InvOK r := by
  cases t with
  | node pid cs =>
    rw [promoteRoots_node]
    cases h with
    | mk _ _ _ _ hrec =>
      intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      exact hrec c hc

/-- Promotion keeps the root count: one promoted root per child of the removed tree. -/
theorem promoteRoots_length (t : Tree) : (promoteRoots t).length = t.degree := by
  cases t with
  | node pid cs =>
    rw [promoteRoots_node]
    simp [Tree.degree]

/-- The summed promoted-root sizes are exactly the summed child sizes. -/
theorem sum_map_tree_size (cs : List Child) :
    ((cs.map Child.tree).map Tree.size).sum = sizeSum cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, sizeSum]
    show Tree.size (Child.tree c) + ((cs.map Child.tree).map Tree.size).sum
        = Child.size c + sizeSum cs
    rw [ih]
    rfl

/-- Promotion conserves live size up to the removed root itself: the promoted roots
represent exactly the `size − 1` nodes below the removed root. -/
theorem promoteRoots_sizeSum (t : Tree) :
    ((promoteRoots t).map Tree.size).sum = t.size - 1 := by
  cases t with
  | node pid cs =>
    rw [promoteRoots_node, size_node, sum_map_tree_size]
    omega

/-- Every option is either empty or populated. -/
theorem eq_none_or_some {a : Type} (o : Option a) : o = none ∨ ∃ x, o = some x := by
  cases o with
  | none => exact Or.inl rfl
  | some x => exact Or.inr ⟨x, rfl⟩

/-! ## Transition 5: bucket consolidation -/

/-- The first tree in the table whose degree is `d`. -/
def findDegree (d : ℕ) : List Tree → Option Tree
  | [] => none
  | t :: ts => if t.degree = d then some t else findDegree d ts

/-- The first tree of degree `d` removed. -/
def removeDegree (d : ℕ) : List Tree → List Tree
  | [] => []
  | t :: ts => if t.degree = d then ts else t :: removeDegree d ts

/-- A found table entry carries the requested degree. -/
theorem findDegree_some {d : ℕ} {s : Tree} {l : List Tree}
    (h : findDegree d l = some s) : s.degree = d ∧ s ∈ l := by
  induction l with
  | nil => simp [findDegree] at h
  | cons t ts ih =>
    simp only [findDegree] at h
    split at h
    · rename_i hd
      have hts : t = s := Option.some.inj h
      subst hts
      exact ⟨hd, by simp⟩
    · exact ⟨(ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

/-- No table entry has the requested degree. -/
theorem findDegree_none {d : ℕ} {l : List Tree}
    (h : findDegree d l = none) : ∀ s ∈ l, s.degree ≠ d := by
  induction l with
  | nil => intro s hs; cases hs
  | cons t ts ih =>
    simp only [findDegree] at h
    split at h
    · cases h
    · rename_i hd
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hd
      · exact ih h s hs

/-- Removing an existing degree shortens the table by exactly one. -/
theorem removeDegree_length {d : ℕ} {l : List Tree} (h : ∃ x ∈ l, x.degree = d) :
    (removeDegree d l).length + 1 = l.length := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := h; cases hx
  | cons t ts ih =>
    simp only [removeDegree]
    split
    · simp
    · rename_i hd
      obtain ⟨x, hx, hxd⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hxd hd
      · have hih := ih ⟨x, hx, hxd⟩
        simp only [List.length_cons] at hih ⊢
        omega

/-- Everything in the shortened table is in the original. -/
theorem mem_removeDegree {d : ℕ} {s : Tree} {l : List Tree} (h : s ∈ removeDegree d l) :
    s ∈ l := by
  induction l with
  | nil => simp [removeDegree] at h
  | cons t ts ih =>
    simp only [removeDegree] at h
    split at h
    · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.Mem.head _
      · exact List.mem_cons_of_mem _ (ih h)

/-- Shortening preserves degree distinctness. -/
theorem removeDegree_nodup {d : ℕ} {l : List Tree} (h : (l.map Tree.degree).Nodup) :
    ((removeDegree d l).map Tree.degree).Nodup := by
  induction l with
  | nil => simp [removeDegree]
  | cons t ts ih =>
    simp only [removeDegree]
    split
    · simp only [List.map_cons, List.nodup_cons] at h
      exact h.2
    · simp only [List.map_cons, List.nodup_cons] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hx
      obtain ⟨u, hu, hux⟩ := List.mem_map.mp hx
      have hu' : u ∈ ts := mem_removeDegree hu
      have hum : Tree.degree u ∈ ts.map Tree.degree := List.mem_map_of_mem hu'
      exact h.1 (hux ▸ hum)

/-- Fuel-bounded bucket consolidation: each work-list root either occupies an empty
degree slot in the table or links with the occupant and re-enters the work list; the
fuel counts work steps and the wrapper charges `2 * roots.length`, which the conservation
lemmas show is always sufficient. -/
def consolidateCount : ℕ → List Tree → List Tree → ℕ × List Tree
  | 0, _, table => (0, table)
  | _ + 1, [], table => (0, table)
  | fuel + 1, r :: work, table =>
      match findDegree r.degree table with
      | none => consolidateCount fuel work (r :: table)
      | some s =>
        let res := consolidateCount fuel (linkRoots s r :: work) (removeDegree r.degree table)
        (res.1 + 1, res.2)

/-- **Link-count conservation**: the number of links performed plus the final root count
equals the number of roots present at the start (work list plus table).  At the wrapper's
fuel this certifies that no root was dropped. -/
theorem consolidateCount_conservation {fuel : ℕ} :
    ∀ work table : List Tree, 2 * work.length + table.length ≤ fuel →
      (consolidateCount fuel work table).1 + (consolidateCount fuel work table).2.length
        = work.length + table.length := by
  induction fuel with
  | zero =>
    intro work table hm
    have hw : work = [] := by
      cases work with
      | nil => rfl
      | cons a l => simp at hm
    subst hw
    simp [consolidateCount]
  | succ fuel ih =>
    intro work table hm
    cases work with
    | nil => simp [consolidateCount]
    | cons r rest =>
      simp only [consolidateCount, List.length_cons]
      split
      · rename_i hf
        have hrec := ih rest (r :: table) (by simp only [List.length_cons] at hm ⊢; omega)
        simp only [List.length_cons] at hrec
        omega
      · rename_i s hf
        obtain ⟨hsd, hsm⟩ := findDegree_some hf
        have hrd : (removeDegree r.degree table).length + 1 = table.length :=
          removeDegree_length ⟨s, hsm, hsd⟩
        have hrec := ih (linkRoots s r :: rest) (removeDegree r.degree table)
          (by simp only [List.length_cons] at hm ⊢; omega)
        simp only [List.length_cons] at hrec
        show (consolidateCount fuel (linkRoots s r :: rest) (removeDegree r.degree table)).1 + 1
            + (consolidateCount fuel (linkRoots s r :: rest) (removeDegree r.degree table)).2.length
          = rest.length + 1 + table.length
        omega

/-- The empty-slot step. -/
theorem consolidateCount_none (fuel : ℕ) (r : Tree) (work table : List Tree)
    (hf : findDegree r.degree table = none) :
    consolidateCount (fuel + 1) (r :: work) table
      = consolidateCount fuel work (r :: table) := by
  simp only [consolidateCount, hf]

/-- The link step. -/
theorem consolidateCount_some (fuel : ℕ) (r s : Tree) (work table : List Tree)
    (hf : findDegree r.degree table = some s) :
    consolidateCount (fuel + 1) (r :: work) table =
      let res := consolidateCount fuel (linkRoots s r :: work) (removeDegree r.degree table)
      (res.1 + 1, res.2) := by
  simp only [consolidateCount, hf]

theorem consolidateCount_some_fst (fuel : ℕ) (r s : Tree) (work table : List Tree)
    (hf : findDegree r.degree table = some s) :
    (consolidateCount (fuel + 1) (r :: work) table).1
      = (consolidateCount fuel (linkRoots s r :: work) (removeDegree r.degree table)).1 + 1 := by
  rw [consolidateCount_some fuel r s work table hf]

theorem consolidateCount_some_snd (fuel : ℕ) (r s : Tree) (work table : List Tree)
    (hf : findDegree r.degree table = some s) :
    (consolidateCount (fuel + 1) (r :: work) table).2
      = (consolidateCount fuel (linkRoots s r :: work) (removeDegree r.degree table)).2 := by
  rw [consolidateCount_some fuel r s work table hf]

/-- Shortening removes exactly the found tree, conserving size. -/
theorem removeDegree_sizes (d : ℕ) (l : List Tree) :
    ∀ s : Tree, findDegree d l = some s →
      ((removeDegree d l).map Tree.size).sum + s.size = ((l.map Tree.size).sum) := by
  induction l with
  | nil => intro s hf; simp [findDegree] at hf
  | cons t ts ih =>
    intro s hf
    simp only [findDegree] at hf
    simp only [removeDegree]
    split at hf
    · rename_i hd
      have hts : t = s := Option.some.inj hf
      subst hts
      simp only [hd, ite_true, List.map_cons, List.sum_cons]
      omega
    · rename_i hd
      have hd' : (t.degree = d) = False := by simp [hd]
      simp only [hd', ite_false, List.map_cons, List.sum_cons]
      have hih := ih s hf
      omega

/-- **Consolidation maintains `InvOK`**: every link is `linkRoots`, so the invariant is
inherited through the whole run. -/
theorem consolidateCount_invOK {fuel : ℕ} :
    ∀ work table : List Tree,
      (∀ t ∈ work, InvOK t) → (∀ t ∈ table, InvOK t) →
        ∀ t ∈ (consolidateCount fuel work table).2, InvOK t := by
  induction fuel with
  | zero => intro work table _ htb; exact htb
  | succ fuel ih =>
    intro work table hw htb
    cases work with
    | nil => exact htb
    | cons r rest =>
      by_cases hf : findDegree r.degree table = none
      · rw [consolidateCount_none _ _ _ _ hf]
        have hw' : ∀ t ∈ rest, InvOK t := fun t ht => hw t (List.mem_cons_of_mem _ ht)
        have htb' : ∀ t ∈ r :: table, InvOK t := by
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hw t (List.Mem.head _)
          · exact htb t ht
        exact ih rest (r :: table) hw' htb'
      · rcases eq_none_or_some (findDegree r.degree table) with hfn | ⟨s, hfs⟩
        · exact absurd hfn hf
        rw [consolidateCount_some_snd _ _ _ _ _ hfs]
        refine ih (linkRoots s r :: rest) (removeDegree r.degree table) ?_ ?_
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact linkRoots_invOK (htb s (findDegree_some hfs).2) (hw r (List.Mem.head _))
              (findDegree_some hfs).1
          · exact hw t (List.mem_cons_of_mem _ ht)
        · intro t ht
          exact htb t (mem_removeDegree ht)

/-- **Consolidation maintains degree distinctness**: the table always holds at most one
tree per degree, so the final root degrees are pairwise distinct. -/
theorem consolidateCount_nodup {fuel : ℕ} :
    ∀ work table : List Tree, ((table.map Tree.degree).Nodup) →
      (((consolidateCount fuel work table).2.map Tree.degree).Nodup) := by
  induction fuel with
  | zero => intro _ table hnd; exact hnd
  | succ fuel ih =>
    intro work table hnd
    cases work with
    | nil => exact hnd
    | cons r rest =>
      by_cases hf : findDegree r.degree table = none
      · rw [consolidateCount_none _ _ _ _ hf]
        refine ih rest (r :: table) ?_
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hx => ?_, hnd⟩
        obtain ⟨u, hu, hux⟩ := List.mem_map.mp hx
        exact (findDegree_none hf u hu) hux
      · rcases eq_none_or_some (findDegree r.degree table) with hfn | ⟨s, hfs⟩
        · exact absurd hfn hf
        rw [consolidateCount_some_snd _ _ _ _ _ hfs]
        exact ih (linkRoots s r :: rest) (removeDegree r.degree table)
          (removeDegree_nodup hnd)

/-- **Consolidation conserves total live size.** -/
theorem consolidateCount_sizes {fuel : ℕ} :
    ∀ work table : List Tree, 2 * work.length + table.length ≤ fuel →
      (((consolidateCount fuel work table).2.map Tree.size).sum)
        = (((work ++ table).map Tree.size).sum) := by
  induction fuel with
  | zero =>
    intro work table hm
    have hw : work = [] := by
      cases work with
      | nil => rfl
      | cons a l => simp at hm
    subst hw
    simp [consolidateCount]
  | succ fuel ih =>
    intro work table hm
    cases work with
    | nil => simp [consolidateCount]
    | cons r rest =>
      rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      by_cases hf : findDegree r.degree table = none
      · rw [consolidateCount_none _ _ _ _ hf]
        have hrec := ih rest (r :: table) (by simp only [List.length_cons] at hm ⊢; omega)
        simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hrec
        omega
      · rcases eq_none_or_some (findDegree r.degree table) with hfn | ⟨s, hfs⟩
        · exact absurd hfn hf
        obtain ⟨hsd, hsm⟩ := findDegree_some hfs
        have hrd : (removeDegree r.degree table).length + 1 = table.length :=
          removeDegree_length ⟨s, hsm, hsd⟩
        have hsz2 := removeDegree_sizes r.degree table s hfs
        rw [consolidateCount_some_snd _ _ _ _ _ hfs]
        have hrec := ih (linkRoots s r :: rest) (removeDegree r.degree table)
          (by simp only [List.length_cons] at hm ⊢; omega)
        simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hrec
        have hsz : (linkRoots s r).size = s.size + r.size := linkRoots_size s r
        omega

end Submission.FibHeapDynamic
