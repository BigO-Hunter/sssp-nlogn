import Submission.FibHeapSupportSet

/-!
# M2a: the link updater — splice, ledger, and the first two invariants

`linkState st p c` is the exact array splice of an equal-degree link: child `c` (a root) is
appended at the tail of `p`'s circular child list, `deg p` grows by one, `par c := p`, `mrk c := 0`,
and `c` leaves the root list.  Two splices, one per shape of the target list:

* `deg p = 0` — `c` becomes a one-element ring: `chd p := c`, `lft c = rgt c = c`.
* `deg p > 0` — append before the head: with `h = chd p` and `t = lft h` (the tail), set
  `rgt c := h`, `lft c := t`, `rgt t := c`, `lft h := c`.  The head is untouched, so the walk from
  the head still reads the old children in link order and reaches `c` last — exactly
  `kids st p ++ [c]`, which is what `pos_link` consumes (the appended child sits at position
  `deg p` with link degree `deg p` — equality, because equal-degree linking links a root whose
  degree is `deg p`).

## The ledger: 2 of 7 discharged, 5 named

Seven invariants must survive every updater.  Discharged here:

* `MarkOK` — pointwise: the mark of a freshly linked root is 0, every other mark untouched.
* `ParSlot` — pointwise: every `par` value is either unchanged or the live root `p`.

Deliberately not stated (they reduce to the walk lemma
`kids (linkState st p c) p = kids st p ++ [c]`):

* `SlotOK`, `NoCycle`, `ParOK`, `KidsNodup`, `PosOK`.

`SlotOK` is the instructive one: it looks pointwise but is not, because the walk from a *different*
node's head could pass through `c` or the old tail `t`, whose `rgt` entries changed.  Keeping it
out requires `c ∉ kids q` for `q ≠ p` — which holds (`c` was a root, so with `ParOK` + `RootsPar`
a child of `q` has `par = q ≠ c`) — but proving it needs the walk-invariance machinery, same as
the other four.  That machinery is the next module; nothing here claims it.
-/

namespace Submission.FibHeapLink

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport

/-- Roots are self-parents.  With `ParOK` this makes the root set disjoint from every child list:
a root `c` with `c ∈ kids p` would have `par c = p` and `par c = c`. -/
def RootsPar (st : HState) : Prop := ∀ r ∈ st.roots, st.par r = r

/-- Circular child lists.  For every node with children: the walk of length `deg p` closes, it is
injective within one period, and `lft` of the head is exactly the tail (walk position
`deg p - 1`).  This is what makes `kids` read the children in link order and what makes the link
splice's walk provably unchanged on the old prefix. -/
def RingOK (st : HState) : Prop :=
  ∀ p, st.deg p = 0 ∨
    ((st.rgt)^[st.deg p] (st.chd p) = st.chd p ∧
      (∀ j k, j < st.deg p → k < st.deg p →
        (st.rgt)^[j] (st.chd p) = (st.rgt)^[k] (st.chd p) → j = k) ∧
      st.lft (st.chd p) = (st.rgt)^[st.deg p - 1] (st.chd p))

/-- Preconditions of a link: distinct roots of equal degree. -/
def LinkPre (st : HState) (p c : ℕ) : Prop :=
  p ∈ st.roots ∧ c ∈ st.roots ∧ p ≠ c ∧ st.deg p = st.deg c

/-- The link splice.  Both branches write only to already-live slots.  (The field values are
parenthesised: an unpunctuated `fun i => if …` value inside a structure instance swallows the
field separator — measured, not stylistic.) -/
def linkState (st : HState) (p c : ℕ) : HState :=
  if st.deg p = 0 then
    { st with
      par := (fun i => if i = c then p else st.par i)
      mrk := (fun i => if i = c then 0 else st.mrk i)
      deg := (fun i => if i = p then st.deg i + 1 else st.deg i)
      chd := (fun i => if i = p then c else st.chd i)
      rgt := (fun i => if i = c then c else st.rgt i)
      lft := (fun i => if i = c then c else st.lft i)
      roots := st.roots.erase c }
  else
    { st with
      par := (fun i => if i = c then p else st.par i)
      mrk := (fun i => if i = c then 0 else st.mrk i)
      deg := (fun i => if i = p then st.deg i + 1 else st.deg i)
      rgt := (fun i => if i = c then st.chd p else if i = st.lft (st.chd p) then c else st.rgt i)
      lft := (fun i => if i = st.chd p then c else if i = c then st.lft (st.chd p) else st.lft i)
      roots := st.roots.erase c }

/-! ## Pointwise behaviour of the splice -/

theorem linkState_deg (st : HState) (p c q : ℕ) :
    (linkState st p c).deg q = if q = p then st.deg q + 1 else st.deg q := by
  unfold linkState
  by_cases h : st.deg p = 0
  · rw [if_pos h]
  · rw [if_neg h]

theorem linkState_mrk (st : HState) (p c q : ℕ) :
    (linkState st p c).mrk q = if q = c then 0 else st.mrk q := by
  unfold linkState
  by_cases h : st.deg p = 0
  · rw [if_pos h]
  · rw [if_neg h]

theorem linkState_par (st : HState) (p c q : ℕ) :
    (linkState st p c).par q = if q = c then p else st.par q := by
  unfold linkState
  by_cases h : st.deg p = 0
  · rw [if_pos h]
  · rw [if_neg h]

/-- The slot count is untouched by the splice. -/
theorem linkState_n (st : HState) (p c : ℕ) : (linkState st p c).n = st.n := by
  unfold linkState
  by_cases h : st.deg p = 0
  · rw [if_pos h]
  · rw [if_neg h]

theorem linkState_par_c (st : HState) (p c : ℕ) : (linkState st p c).par c = p := by
  rw [linkState_par, if_pos rfl]

theorem linkState_mrk_c (st : HState) (p c : ℕ) : (linkState st p c).mrk c = 0 := by
  rw [linkState_mrk, if_pos rfl]

theorem linkState_par_ne (st : HState) (p c q : ℕ) (hne : q ≠ c) :
    (linkState st p c).par q = st.par q := by
  rw [linkState_par, if_neg hne]

theorem linkState_mrk_ne (st : HState) (p c q : ℕ) (hne : q ≠ c) :
    (linkState st p c).mrk q = st.mrk q := by
  rw [linkState_mrk, if_neg hne]

/-! ## The ledger: 2 of 7 -/

/-- **MarkOK survives the link.** -/
theorem link_markOK (st : HState) (p c : ℕ) (hm : MarkOK st) :
    MarkOK (linkState st p c) := by
  intro q
  rw [linkState_mrk]
  by_cases h : q = c
  · rw [if_pos h]; exact Nat.zero_le 1
  · rw [if_neg h]; exact hm q

/-- **ParSlot survives the link**: every `par` value is either unchanged or the live root `p`. -/
theorem link_parSlot (st : HState) (p c : ℕ) (hps : ParSlot st) (hpv : p < st.n) :
    ParSlot (linkState st p c) := by
  have hn : (linkState st p c).n = st.n := linkState_n st p c
  intro q hq
  rw [hn] at hq ⊢
  by_cases hqc : q = c
  · subst hqc
    rw [linkState_par_c]
    exact hpv
  · rw [linkState_par_ne st p c q hqc]
    exact hps q hq

end Submission.FibHeapLink
