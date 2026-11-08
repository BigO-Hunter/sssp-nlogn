import Submission.FibHeapDynamic

/-!
# M1: the machine-array refinement of the Fibonacci forest

`FibHeapForest` left one honesty boundary open: `InvOK` is asserted of an abstract `Tree`, and
nothing connected it to a heap whose children live in arrays.  This module pins that connection
and narrows the boundary to two exactly stated goals.

## The array layer

`HState` holds the forest the way M2 will hold it in the word RAM: `par`, `chd`, `rgt`, `lft`,
`deg`, `mrk`, a root list, a slot count.  A node's children are `deg p` successor steps of `rgt`
from `chd p`; `kids` reads exactly that, so `(kids st p).length = deg p` holds by construction —
no fuel and no acyclicity are needed just to *read* the forest.

## What carries `InvOK`

Two machine predicates carry its whole content, both statements about the arrays alone:

* `MarkOK` — every mark bit is 0 or 1.
* `PosOK` — the child at position `j` of `p` has `deg + mrk ≥ j`.

The link degree `Child.linkDegree` is *derived* on the machine, not stored, as `ldeg = deg + mrk`:
a node is linked with `mrk = 0`, so at link time `deg + mrk` is its degree; every child it later
loses sets its mark, so `deg + mrk` is invariant across a loss.  That is the CLRS one-loss rule,
which is why the record field `c.tree.degree + c.lost = c.linkDegree` of `InvOK` is `rfl` here —
the ghost field is not an assumption, it is a definition.

`PosOK` is what `sizeSum_ge_fib_aux` consumes.  Only two transitions move a child position, and
both are proved here: `pos_link` (an append lands at position `deg` with link degree exactly `deg`,
from equal-degree linking) and `pos_cut` (an erase shifts every later position down, link degrees
untouched — the monotone direction).  Promotion and consolidation only link roots, which is
`pos_link`.

## The closure, and the two remaining goals

`invOK_treeOf` closes the boundary in the honest form: an abstraction at fuel `f+1` is `InvOK`
whenever it is `Faithful` at fuel `f`, where

  `Faithful st f p` — no node of `p`'s subtree sits at depth `f` with children, i.e. the fuel does
  not truncate anything.

Truncation is exactly what a fuel-free abstraction cannot avoid: a truncated node reports degree
`0`, which breaks `InvOK`'s `deg + lost = linkDegree`.  So faithfulness, not dry induction, is the
real interface — and it is what `NoCycle` plus the slot count supplies: a chain of `n+1` distinct
children cannot live in `n` slots, so no node sits at depth `n`.

Two goals remain, both stated exactly, neither assumed away:

1. `faithful_of_noCycle` — discharge `Faithful st st.n p` from `NoCycle st`.
2. `support_of_noCycle` — discharge `Support st f p` (distinct ids inside the slots) from
   `NoCycle st`.

With those two, `degree_le_rankCap_treeOf` gives `deg ≤ rankCap st.n` for every machine node, which
is the exact feed the amortized ledger needs.
-/

namespace Submission.FibHeapRefine

open Submission.FibHeapForest Submission.FibHeapDynamic

/-! ## Generic `getD` plumbing for the two position transitions -/

/-- Appending does not disturb an earlier lookup. -/
theorem getD_append_lt {cs : List ℕ} {j : ℕ} (hj : j < cs.length) (x d : ℕ) :
    (cs ++ [x]).getD j d = cs.getD j d := by
  induction cs generalizing j with
  | nil => simp at hj
  | cons a ts ih =>
    cases j with
    | zero => simp
    | succ j' => simpa using ih (Nat.lt_of_succ_lt_succ hj)

/-- The appended element sits at the old length. -/
theorem getD_append_last {cs : List ℕ} (x d : ℕ) : (cs ++ [x]).getD cs.length d = x := by
  induction cs with
  | nil => simp
  | cons a ts ih => simp

/-- Erasing a later index keeps earlier lookups. -/
theorem getD_eraseIdx_lt {cs : List ℕ} {i j : ℕ} (h : i < j) :
    (cs.eraseIdx j).getD i 0 = cs.getD i 0 := by
  induction cs generalizing i j with
  | nil => simp
  | cons a ts ih =>
    cases j with
    | zero => omega
    | succ j' =>
      cases i with
      | zero => simp
      | succ i' => exact ih (by omega)

/-- Erasing index `j` shifts later lookups down by one. -/
theorem getD_eraseIdx_ge {cs : List ℕ} {i j : ℕ} (h : j ≤ i) :
    (cs.eraseIdx j).getD i 0 = cs.getD (i + 1) 0 := by
  induction cs generalizing i j with
  | nil => simp
  | cons a ts ih =>
    cases j with
    | zero => simp
    | succ j' =>
      cases i with
      | zero => omega
      | succ i' => exact ih (by omega)

/-- `getD` through a `map`, at an in-range index. -/
theorem getD_map_lt {α β : Type} (g : α → β) (dβ : β) (dα : α) :
    ∀ (l : List α) (j : ℕ), j < l.length → (l.map g).getD j dβ = g (l.getD j dα)
  | [], j, hj => by simp at hj
  | a :: t, 0, _ => by simp
  | a :: t, j + 1, hj => by
      have h := getD_map_lt g dβ dα t j (Nat.lt_of_succ_lt_succ hj)
      simpa using h

/-! ## The machine state -/

/-- The machine state: the Fibonacci forest exactly as M2 will hold it in the word RAM. -/
structure HState where
  /-- parent of each slot -/
  par : ℕ → ℕ
  /-- some child of each slot (the head of its circular child list) -/
  chd : ℕ → ℕ
  /-- next sibling, circular within a parent's child list -/
  rgt : ℕ → ℕ
  /-- previous sibling, circular within a parent's child list -/
  lft : ℕ → ℕ
  /-- current child count -/
  deg : ℕ → ℕ
  /-- mark bit -/
  mrk : ℕ → ℕ
  /-- the root list, in order -/
  roots : List ℕ
  /-- number of live slots -/
  n : ℕ

/-- The children of `p`: `deg p` steps of `rgt` from `chd p`.  Total and length-exact. -/
def kids (st : HState) (p : ℕ) : List ℕ :=
  List.ofFn fun j : Fin (st.deg p) => (st.rgt)^[j.val] (st.chd p)

@[simp] theorem kids_length (st : HState) (p : ℕ) : (kids st p).length = st.deg p := by
  simp [kids]

/-- The link degree of a slot, derived rather than stored. -/
def ldeg (st : HState) (p : ℕ) : ℕ := st.deg p + st.mrk p

/-- The one-loss rule on the machine: `mrk` is a bit. -/
def MarkOK (st : HState) : Prop := ∀ p, st.mrk p ≤ 1

/-- Link order on the machine: the child at position `j` of `p` has link degree at least `j`. -/
def PosOK (st : HState) : Prop :=
  ∀ p, ∀ j, j < (kids st p).length → j ≤ ldeg st ((kids st p).getD j 0)

/-- No descendant chain of `n` steps returns to its start: the structure is a forest. -/
def NoCycle (st : HState) : Prop :=
  ∀ (p : ℕ) (j : ℕ), st.n ≤ j → (st.par^[j]) p ≠ p

/-! ## The two transitions that move child positions -/

/-- **Append.**  A child appended at the end of `p`'s list lands at position `deg p`; equal-degree
linking puts a root of degree `deg p` there, so its link degree equals its position exactly, and
every earlier position is untouched. -/
theorem pos_link {cs : List ℕ} {c : ℕ} {dg : ℕ → ℕ}
    (hpos : ∀ j, j < cs.length → j ≤ dg (cs.getD j 0)) (hc : dg c = cs.length) :
    ∀ j, j < (cs ++ [c]).length → j ≤ dg ((cs ++ [c]).getD j 0) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < cs.length
  · rw [getD_append_lt hlt]; exact hpos j hlt
  · have hje : j = cs.length := by omega
    subst hje; rw [getD_append_last]; exact hc.ge

/-- Erasing an in-range index shortens the list by exactly one. -/
theorem length_eraseIdx_lt {cs : List ℕ} {k : ℕ} (hk : k < cs.length) :
    (cs.eraseIdx k).length = cs.length - 1 := by
  have h := List.length_eraseIdx_add_one hk
  omega

/-- **Erase.**  Cutting the child at position `k` shifts every later position down by one and
leaves earlier ones fixed; link degrees are untouched, so `PosOK` survives. -/
theorem pos_cut {cs : List ℕ} {k : ℕ} {dg : ℕ → ℕ} (hk : k < cs.length)
    (hpos : ∀ j, j < cs.length → j ≤ dg (cs.getD j 0)) :
    ∀ j, j < (cs.eraseIdx k).length → j ≤ dg ((cs.eraseIdx k).getD j 0) := by
  intro j hj
  have hlen := length_eraseIdx_lt hk
  have hjlen : j < cs.length := by omega
  by_cases hlt : j < k
  · rw [getD_eraseIdx_lt (by omega : j < k)]; exact hpos j hjlen
  · rw [getD_eraseIdx_ge (by omega : k ≤ j)]
    exact le_trans (Nat.le_succ j) (hpos (j + 1) (by omega))

/-! ## The abstraction -/

/-- The fuel-built abstraction of one node: children in link order, each carrying its derived link
degree and its mark. -/
def treeOf (st : HState) : ℕ → ℕ → Tree
  | 0, p => .node p []
  | f + 1, p =>
      .node p ((kids st p).map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))

/-- The abstraction is not truncated: no node of `p`'s subtree sits at depth `f` with children. -/
def Faithful (st : HState) : ℕ → ℕ → Prop
  | 0, p => st.deg p = 0
  | f + 1, p => ∀ c ∈ kids st p, Faithful st f c

/-- The abstraction of the whole root list. -/
def abstRoots (st : HState) (f : ℕ) : List Tree := st.roots.map (treeOf st f)

/-- The degree of an abstracted node is the stored degree, at every positive fuel. -/
theorem treeOf_degree (st : HState) (f p : ℕ) : (treeOf st (f + 1) p).degree = st.deg p := by
  simp [treeOf, Tree.degree, kids_length]

/-- A node with no children reads out as the empty child list. -/
theorem kids_eq_nil {st : HState} {p : ℕ} (h : st.deg p = 0) : kids st p = [] := by
  have : (kids st p).length = 0 := by simp [h]
  exact List.eq_nil_of_length_eq_zero this

/-- **The boundary is closed.**  A non-truncated abstraction of any state with a mark bit and link
order is an `InvOK` tree.  The record field `deg + lost = linkDegree` is `rfl` because the link
degree is derived as `deg + mrk`; the position field is `PosOK`. -/
theorem invOK_treeOf (st : HState) (hm : MarkOK st) (hp : PosOK st) :
    ∀ (f p : ℕ), Faithful st f p → InvOK (treeOf st (f + 1) p) := by
  intro f
  induction f with
  | zero =>
    intro p hf
    have hnil : kids st p = [] := kids_eq_nil hf
    rw [show treeOf st (0 + 1) p =
      FibHeapForest.Tree.node p ((kids st p).map
        fun c => Child.mk (treeOf st 0 c) (ldeg st c) (st.mrk c)) from rfl, hnil]
    simp only [List.map_nil]
    refine InvOK.mk p [] ?_ ?_ ?_
    · intro c hc; cases hc
    · intro j hj; simp at hj
    · intro c hc; cases hc
  | succ f ih =>
    intro p hf
    rw [show treeOf st (f + 1 + 1) p =
        FibHeapForest.Tree.node p (List.map
          (fun c => Child.mk (treeOf st (f + 1) c) (ldeg st c) (st.mrk c)) (kids st p)) from rfl]
    refine InvOK.mk p _ ?_ ?_ ?_
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨v, -, rfl⟩ := hc
      refine ⟨?_, hm v⟩
      show (treeOf st (f + 1) v).degree + st.mrk v = st.deg v + st.mrk v
      rw [treeOf_degree]
    · intro j hj
      rw [List.length_map] at hj
      have hpos := hp p j hj
      rw [getD_map_lt (fun c => Child.mk (treeOf st (f + 1) c) (ldeg st c) (st.mrk c))
        (Child.mk (FibHeapForest.Tree.node 0 []) 0 0) 0 (kids st p) j hj]
      exact hpos
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨v, hv, rfl⟩ := hc
      exact ih v (hf v hv)

/-- Distinct identifiers inside the live slots.  This is the single hypothesis that turns
`fib(deg+2) ≤ size` into `deg ≤ rankCap st.n`. -/
def Support (st : HState) (f p : ℕ) : Prop :=
  (ids (treeOf st f p)).Nodup ∧ ∀ i ∈ ids (treeOf st f p), i < st.n

/-- Under `Support` the abstracted subtree fits the slots. -/
theorem size_le_of_support {st : HState} {f p : ℕ} (h : Support st f p) :
    (treeOf st f p).size ≤ st.n := by
  obtain ⟨hnd, hlt⟩ := h
  have hcard : (ids (treeOf st f p)).toFinset.card = (treeOf st f p).size :=
    FibHeapForest.live_card hnd
  have hsub : (ids (treeOf st f p)).toFinset ⊆ Finset.range st.n := fun i hi =>
    Finset.mem_range.mpr (hlt i (List.mem_toFinset.mp hi))
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at this
  exact this

/-- The rank cap for a machine node: `InvOK` gives `fib(deg+2) ≤ size`, `Support` gives
`size ≤ n`, and the proved scalar cap finishes. -/
theorem degree_le_rankCap_treeOf (st : HState) (hm : MarkOK st) (hp : PosOK st) (f p : ℕ)
    (hfaith : Faithful st f p) (hs : Support st (f + 1) p) :
    st.deg p ≤ FibHeapAccounting.rankCap st.n := by
  have hinv := invOK_treeOf st hm hp f p hfaith
  have hsize := size_le_of_support hs
  rw [← treeOf_degree st f p]
  exact FibHeapForest.degree_le_rankCap_of_invOK hinv hsize

end Submission.FibHeapRefine
