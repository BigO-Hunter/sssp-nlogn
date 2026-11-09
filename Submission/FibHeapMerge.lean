import Submission.FibHeapCut

/-!
# M3b: the consolidation merge — re-pointing an entire root under a smaller-degree root

`mergeState st r p` is the machine-array splice of one consolidation step: the entire root
`r` (subtree included — only `par r` changes, the moved subtree's internal pointers are
untouched) is re-pointed under the root `p`, `deg p` grows by one, `r` leaves the root list,
and the moved root's mark is cleared (`mrk r := 0`).  The splice is *the link splice with the
roles swapped* — every pointwise behaviour lemma mirrors the link's.

## Two splice-design facts the next updater must know

1. **The root list is filtered, not `erase`d.**  The BEq-era `List.erase` removes only the
   *first* occurrence (`List.erase_cons`'s then-branch is `l`), so `st.roots.erase r` can
   still contain `r` when the root list carries duplicates — which the invariant bundle does
   not exclude — and `NILRoots`/`RootNotChild` would be false after the merge.  The splice
   therefore removes *all* occurrences: `roots := st.roots.filter (fun x => x != r)`.
   (The link's `roots := erase c` has the same first-occurrence semantics; its claimed
   theorems never need `c ∉ roots'`, so the link bank is unaffected.)
2. **No equal-degree clause.**  `LinkPre` required `deg p = deg c`; a consolidation step
   re-points `r` under the *smaller-or-equal-degree* root (`MergePre`'s fourth component:
   `st.deg p ≤ st.deg r`), so the appended child satisfies its position *by inequality* —
   position `deg p ≤ ldeg r = deg r` (the mark clears).  That single inequality is the whole
   difference: `merge_posOK` is proved fresh with it, and the remaining discharges mirror
   the link's, with the same-shape `MergePre` components in place of the `LinkPre`
   components.

## What lands here

The walk lemma over `p`'s list (`merge_kids_link`, the `List.ext_get`-pointwise pattern),
the untouched-list lemma for every `q ≠ p`, and the full invariant bundle: MarkOK, ParSlot,
ParOK, KidsNodup, PosOK, SlotOK, Acyc, NILRoots, NILSelf, NILNotRoot, NILLeaf, NILNotChild,
RootNotChild, RootsLive, and RingOK.  The moved subtree's membership is discharged exactly
by `RootNotChild` (the moved root `r` is in no `q ≠ 0` child list, so re-pointing it cannot
disturb any other list) and `NILRoots` (every *remaining* root still has `par = 0`).

The merge-output witness (`merged`: two bare roots merged into one degree-1 root) proves the
invariant bundle directly, and the capstone applies to the post-merge state.

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapMerge

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink Submission.FibHeapLinkWalk

/-! ## The merge splice -/

/-- Preconditions of a consolidation merge: distinct roots `r`, `p`, with `p` of
smaller-or-equal degree — the appended child's link degree (`deg r`, its mark clears)
must cover its new position (`deg p`). -/
def MergePre (st : HState) (r p : ℕ) : Prop :=
  r ∈ st.roots ∧ p ∈ st.roots ∧ r ≠ p ∧ st.deg p ≤ st.deg r

/-- The merge splice: re-point the entire root `r` under `p` (the link splice with the roles
swapped), with the root list filtered — *all* occurrences of `r` leave, duplicates included
(the BEq-era `List.erase` removes only the first). -/
def mergeState (st : HState) (r p : ℕ) : HState :=
  if st.deg p = 0 then
    { st with
      par := (fun i => if i = r then p else st.par i)
      mrk := (fun i => if i = r then 0 else st.mrk i)
      deg := (fun i => if i = p then st.deg i + 1 else st.deg i)
      chd := (fun i => if i = p then r else st.chd i)
      rgt := (fun i => if i = r then r else st.rgt i)
      lft := (fun i => if i = r then r else st.lft i)
      roots := st.roots.filter (fun x => x != r) }
  else
    { st with
      par := (fun i => if i = r then p else st.par i)
      mrk := (fun i => if i = r then 0 else st.mrk i)
      deg := (fun i => if i = p then st.deg i + 1 else st.deg i)
      rgt := (fun i => if i = r then st.chd p else if i = st.lft (st.chd p) then r else st.rgt i)
      lft := (fun i => if i = st.chd p then r else if i = r then st.lft (st.chd p) else st.lft i)
      roots := st.roots.filter (fun x => x != r) }

/-- A root is in no child list of a non-NIL node (transferred). -/
theorem root_notin_kids_merge (st : HState) (hrnc : RootNotChild st) {r q : ℕ} (hr : r ∈ st.roots)
    (hq0 : q ≠ 0) : r ∉ kids st q := hrnc r hr q hq0

/-! ## Pointwise behaviour of the splice -/

theorem mergeState_deg (st : HState) (r p q : ℕ) :
    (mergeState st r p).deg q = if q = p then st.deg q + 1 else st.deg q := by
  unfold mergeState
  by_cases h2 : st.deg p = 0
  · rw [if_pos h2]
  · rw [if_neg h2]

theorem mergeState_mrk (st : HState) (r p q : ℕ) :
    (mergeState st r p).mrk q = if q = r then 0 else st.mrk q := by
  unfold mergeState
  by_cases h2 : st.deg p = 0
  · rw [if_pos h2]
  · rw [if_neg h2]

theorem mergeState_par (st : HState) (r p q : ℕ) :
    (mergeState st r p).par q = if q = r then p else st.par q := by
  unfold mergeState
  by_cases h2 : st.deg p = 0
  · rw [if_pos h2]
  · rw [if_neg h2]

theorem mergeState_n (st : HState) (r p : ℕ) : (mergeState st r p).n = st.n := by
  unfold mergeState
  by_cases h2 : st.deg p = 0
  · rw [if_pos h2]
  · rw [if_neg h2]

theorem mergeState_roots (st : HState) (r p : ℕ) :
    (mergeState st r p).roots = st.roots.filter (fun x => x != r) := by
  unfold mergeState
  by_cases h2 : st.deg p = 0
  · rw [if_pos h2]
  · rw [if_neg h2]

theorem mergeState_par_r (st : HState) (r p : ℕ) : (mergeState st r p).par r = p := by
  rw [mergeState_par, if_pos rfl]

theorem mergeState_mrk_r (st : HState) (r p : ℕ) : (mergeState st r p).mrk r = 0 := by
  rw [mergeState_mrk, if_pos rfl]

theorem mergeState_par_ne (st : HState) (r p q : ℕ) (hne : q ≠ r) :
    (mergeState st r p).par q = st.par q := by
  rw [mergeState_par, if_neg hne]

theorem mergeState_mrk_ne (st : HState) (r p q : ℕ) (hne : q ≠ r) :
    (mergeState st r p).mrk q = st.mrk q := by
  rw [mergeState_mrk, if_neg hne]

theorem mergeState_chd_of_ne (st : HState) (r p q : ℕ) (hqp : q ≠ p) :
    (mergeState st r p).chd q = st.chd q := by
  by_cases h2 : st.deg p = 0
  · simp only [mergeState, linkState, if_pos h2, if_neg hqp]
  · simp only [mergeState, linkState, if_neg h2, if_neg hqp]

theorem mergeState_rgt_zero (st : HState) (r p x : ℕ) (h : st.deg p = 0) :
    (mergeState st r p).rgt x = if x = r then r else st.rgt x := by
  unfold mergeState
  rw [if_pos h]

theorem mergeState_rgt_pos (st : HState) (r p x : ℕ) (h : st.deg p ≠ 0) :
    (mergeState st r p).rgt x =
      if x = r then st.chd p else if x = st.lft (st.chd p) then r else st.rgt x := by
  unfold mergeState
  rw [if_neg h]

theorem mergeState_lft_zero (st : HState) (r p x : ℕ) (h : st.deg p = 0) :
    (mergeState st r p).lft x = if x = r then r else st.lft x := by
  unfold mergeState
  rw [if_pos h]

theorem mergeState_lft_pos (st : HState) (r p x : ℕ) (h : st.deg p ≠ 0) :
    (mergeState st r p).lft x =
      if x = st.chd p then r else if x = r then st.lft (st.chd p) else st.lft x := by
  unfold mergeState
  rw [if_neg h]

theorem rgt_merge_other (st : HState) (r p x : ℕ) (h : st.deg p ≠ 0) (h1 : x ≠ r)
    (h2 : x ≠ st.lft (st.chd p)) : (mergeState st r p).rgt x = st.rgt x := by
  rw [mergeState_rgt_pos st r p x h, if_neg h1, if_neg h2]

theorem rgt_merge_r (st : HState) (r p : ℕ) (h : st.deg p ≠ 0) :
    (mergeState st r p).rgt r = st.chd p := by
  rw [mergeState_rgt_pos st r p r h, if_pos rfl]

theorem rgt_merge_tail (st : HState) (r p : ℕ) (h : st.deg p ≠ 0)
    (h3 : st.lft (st.chd p) ≠ r) : (mergeState st r p).rgt (st.lft (st.chd p)) = r := by
  rw [mergeState_rgt_pos st r p (st.lft (st.chd p)) h, if_neg h3, if_pos rfl]

theorem chd_merge_pos (st : HState) (r p : ℕ) (h : st.deg p ≠ 0) :
    (mergeState st r p).chd p = st.chd p := by
  simp only [mergeState, if_neg h]

theorem deg_merge_pos (st : HState) (r p : ℕ) (h : st.deg p ≠ 0) :
    (mergeState st r p).deg p = st.deg p + 1 := by
  rw [mergeState_deg]
  simp

theorem chd_merge_zero (st : HState) (r p : ℕ) (h : st.deg p = 0) :
    (mergeState st r p).chd p = r := by
  unfold mergeState
  simp [h]

theorem deg_merge_zero (st : HState) (r p : ℕ) (h : st.deg p = 0) :
    (mergeState st r p).deg p = 1 := by
  rw [mergeState_deg]
  simp [h]

theorem rgt_merge_r_zero (st : HState) (r p : ℕ) (h : st.deg p = 0) :
    (mergeState st r p).rgt r = r := by
  rw [mergeState_rgt_zero st r p r h]
  simp

theorem lft_merge_head (st : HState) (r p : ℕ) (hac : Acyc st) (hnrs : NILRoots st)
    (hpar : ParOK st) (hr : r ∈ st.roots) (hp0 : p ≠ 0) (h : st.deg p ≠ 0) :
    (mergeState st r p).lft (st.chd p) = r := by
  have hcp : st.chd p ≠ p := by
    intro hc
    have hmem : p ∈ kids st p := by
      rw [kids]
      exact List.mem_ofFn.mpr ⟨⟨0, by omega⟩, hc⟩
    exact hp0 (hac p 1 (by omega) (hpar p p hmem))
  have hcr : st.chd p ≠ r := by
    intro hc
    have hmem : r ∈ kids st p := by
      rw [kids]
      exact List.mem_ofFn.mpr ⟨⟨0, by omega⟩, hc⟩
    exact hp0 ((hpar p r hmem).symm.trans (hnrs r hr))
  rw [mergeState_lft_pos st r p (st.chd p) h, if_pos rfl]

theorem lft_merge_r_zero (st : HState) (r p : ℕ) (h : st.deg p = 0) :
    (mergeState st r p).lft r = r := by
  rw [mergeState_lft_zero st r p r h, if_pos rfl]

theorem lft_merge_other (st : HState) (r p x : ℕ) (h : st.deg p ≠ 0) (h1 : x ≠ st.chd p)
    (h2 : x ≠ r) : (mergeState st r p).lft x = st.lft x := by
  by_cases hdp : st.deg p = 0
  · rw [mergeState_lft_zero st r p x hdp, if_neg h2]
  · rw [mergeState_lft_pos st r p x hdp, if_neg h1, if_neg h2]

theorem merge_walk_pos (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hdeg : st.deg p ≠ 0) :
    ∀ j, j ≤ st.deg p →
      (mergeState st r p).rgt^[j] (st.chd p) =
        if j = st.deg p then r else (st.rgt)^[j] (st.chd p) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hmem : ∀ j, j < st.deg p → (st.rgt)^[j] (st.chd p) ∈ kids st p := by
    intro j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  have hcnot : ∀ x ∈ kids st p, x ≠ r := by
    intro x hx hc
    subst hc
    exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hp0)
  have htmem : st.lft (st.chd p) ∈ kids st p := by
    rw [((hrk p).resolve_left hdeg).2.2]
    exact hmem (st.deg p - 1) (by omega)
  have hrt : r ≠ st.lft (st.chd p) := fun hc => hcnot _ htmem hc.symm
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : (0 : ℕ) ≠ st.deg p := by omega
    rw [if_neg h0]
    rfl
  | succ j ih =>
    intro hj
    have hj' : j ≤ st.deg p := by omega
    rw [Function.iterate_succ_apply', ih hj']
    have hx : (st.rgt)^[j] (st.chd p) ≠ r := hcnot _ (hmem j (by omega))
    by_cases hlast : j + 1 = st.deg p
    · have hje : j = st.deg p - 1 := by omega
      have hxt : (st.rgt)^[j] (st.chd p) = st.lft (st.chd p) := by
        rw [hje]
        exact ((hrk p).resolve_left hdeg).2.2.symm
      have htail : (mergeState st r p).rgt ((st.rgt)^[j] (st.chd p)) = r := by
        rw [hxt]
        exact rgt_merge_tail st r p hdeg (Ne.symm hrt)
      rw [if_neg (show ¬(j:ℕ) = st.deg p from by omega),
        if_pos (show (j:ℕ) + 1 = st.deg p from hlast), htail]
    · have hxt : (st.rgt)^[j] (st.chd p) ≠ st.lft (st.chd p) := by
        intro hc
        rw [((hrk p).resolve_left hdeg).2.2] at hc
        have hrep := ((hrk p).resolve_left hdeg).2.1 j (st.deg p - 1) (by omega) (by omega) hc
        omega
      rw [if_neg (show ¬(j:ℕ) = st.deg p from by omega),
        if_neg (show ¬((j:ℕ) + 1 = st.deg p) from by omega),
        Function.iterate_succ_apply', rgt_merge_other st r p _ hdeg hx hxt]

/-- **The walk lemma, positive-degree branch, as a list equation.** -/
theorem merge_kids_link_pos (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hdeg : st.deg p ≠ 0) :
    kids (mergeState st r p) p = kids st p ++ [r] := by
  have hwalk := merge_walk_pos st r p hpar hrnc hnr hrk hpre hdeg
  unfold kids
  rw [deg_merge_pos st r p hdeg, chd_merge_pos st r p hdeg]
  refine List.ext_get (by simp) (fun n h1 h2 => ?_)
  simp only [List.get_eq_getElem]
  by_cases hlast : n = st.deg p
  · subst hlast
    rw [List.getElem_append_right (by simp)]
    simp only [List.getElem_ofFn]
    rw [hwalk (st.deg p) (le_refl (st.deg p)), if_pos rfl]
    simp
  · have hn : n < st.deg p := by
      have h2' : n < st.deg p + 1 := by simpa using h2
      omega
    rw [List.getElem_append_left (by simpa using hn)]
    simp only [List.getElem_ofFn]
    rw [hwalk n (Nat.le_of_lt hn), if_neg (Nat.ne_of_lt hn)]

/-- **The walk lemma, empty branch.** -/
theorem merge_kids_link_zero (st : HState) (r p : ℕ) (h : st.deg p = 0) :
    kids (mergeState st r p) p = kids st p ++ [r] := by
  unfold kids
  rw [deg_merge_zero st r p h, chd_merge_zero st r p h, h]
  have hrc : ∀ j : ℕ, (mergeState st r p).rgt^[j] r = r := by
    intro j
    induction j with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, rgt_merge_r_zero st r p h]
  simp [hrc]

/-- **The walk lemma.** -/
theorem merge_kids_link (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) :
    kids (mergeState st r p) p = kids st p ++ [r] := by
  by_cases h : st.deg p = 0
  · exact merge_kids_link_zero st r p h
  · exact merge_kids_link_pos st r p hpar hrnc hnr hrk hpre h

/-- **Every other child list is untouched.** -/
theorem merge_kids_unchanged (st : HState) (r p q : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : MergePre st r p) (hq : q ≠ p) (hq0 : q ≠ 0) :
    kids (mergeState st r p) q = kids st q := by
  have hcnot : ∀ x ∈ kids st q, x ≠ r := by
    intro x hx hc
    subst hc
    exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hq0)
  have h1 : (mergeState st r p).deg q = st.deg q := by
    rw [mergeState_deg, if_neg (by omega : ¬ q = p)]
  have h2 : (mergeState st r p).chd q = st.chd q :=
    mergeState_chd_of_ne st r p q hq
  have hrgt : ∀ x, x ≠ r → (st.deg p = 0 ∨ x ≠ st.lft (st.chd p)) →
      (mergeState st r p).rgt x = st.rgt x := by
    intro x hx hsplit
    by_cases h : st.deg p = 0
    · rw [mergeState_rgt_zero st r p x h, if_neg hx]
    · rw [mergeState_rgt_pos st r p x h, if_neg hx,
        if_neg (hsplit.resolve_left h)]
  have hmem : ∀ z j, j < st.deg z → (st.rgt)^[j] (st.chd z) ∈ kids st z := by
    intro z j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  -- With `deg p ≠ 0`, the old tail `t = lft (chd p)` is a child of `p` (`RingOK`), hence of
  -- no other node (`ParOK`, `q ≠ p`); with `deg p = 0` the splice's second `rgt` write is
  -- absent.
  have hq'' : st.deg p ≠ 0 → st.lft (st.chd p) ∉ kids st q := by
    intro hdp hx
    have htp : st.lft (st.chd p) ∈ kids st p := by
      rw [(Or.resolve_left (hrk p) hdp).2.2]
      exact hmem p (st.deg p - 1) (by omega)
    exfalso
    exact hq ((hpar q _ hx).symm.trans (hpar p _ htp))
  have hw : ∀ j : ℕ, j < st.deg q →
      (mergeState st r p).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
    intro j hj
    induction j with
    | zero => simp
    | succ k ih =>
      have hik : k < st.deg q := by omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hik]
      have hx : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem q k hik
      by_cases hdp : st.deg p = 0
      · exact hrgt _ (hcnot _ hx) (Or.inl hdp)
      · exact hrgt _ (hcnot _ hx) (Or.inr (fun hc => hq'' hdp (hc ▸ hx)))
  unfold kids
  rw [h1, h2]
  refine List.ext_get (by simp) (fun n h1 h2 => ?_)
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact hw n (by simpa using h2)

/-! ## The invariant discharges -/

/-- `MarkOK` survives the merge: the only mark written is the moved root's, and it clears. -/
theorem merge_markOK (st : HState) (r p : ℕ) (hm : MarkOK st) : MarkOK (mergeState st r p) := by
  intro q
  rw [mergeState_mrk]
  by_cases h : q = r
  · rw [if_pos h]; exact Nat.zero_le 1
  · rw [if_neg h]; exact hm q

/-- `ParSlot` survives the merge: every `par` value is either unchanged or the live root `p`. -/
theorem merge_parSlot (st : HState) (r p : ℕ) (hpre : MergePre st r p) (hps : ParSlot st)
    (hrl : RootsLive st) : ParSlot (mergeState st r p) := by
  have hpv : p < st.n := hrl p hpre.2.1
  have hn : (mergeState st r p).n = st.n := mergeState_n st r p
  intro q hq
  rw [hn] at hq ⊢
  by_cases hqr : q = r
  · subst hqr
    rw [mergeState_par_r]
    exact hpv
  · rw [mergeState_par_ne st r p q hqr]
    exact hps q hq

/-- `ParOK` survives the merge: `p`'s old children keep their parent (the moved root `r` is on
no old list — `RootNotChild`), and the moved root records `p`. -/
theorem merge_parOK (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hnl : NILLeaf st) :
    ParOK (mergeState st r p) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hrnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ r := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hq0)
  intro q v hv
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    rw [merge_kids_link st r p hpar hrnc hnr hrk hpre] at hv
    rcases List.mem_append.mp hv with hv | hv
    · rw [mergeState_par_ne st r p v (hrnot p hp0 v hv)]
      exact hpar p v hv
    · have hvc : r = v := (List.mem_singleton.mp hv).symm
      subst hvc
      exact mergeState_par_r st r p
  · by_cases hq0 : q = 0
    · subst hq0
      have hdg : (mergeState st r p).deg 0 = 0 := by
        rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hp0 hc.symm)]
        exact hnl
      rw [kids_eq_nil hdg] at hv
      simp at hv
    · rw [merge_kids_unchanged st r p q hpar hrnc hrk hpre hqp hq0] at hv
      rw [mergeState_par_ne st r p v (hrnot q hq0 v hv)]
      exact hpar q v hv

/-- `KidsNodup` survives the merge: other lists are untouched, `p`'s old prefix keeps its
distinctness, and the moved root `r` is new to `p`'s list (`RootNotChild`). -/
theorem merge_kidsNodup (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hnl : NILLeaf st)
    (hnd : ∀ q, KidsNodup st q) : ∀ q, KidsNodup (mergeState st r p) q := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hrnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ r := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hq0)
  have hmemD : ∀ q j, j < (kids st q).length → (kids st q).getD j 0 ∈ kids st q := by
    intro q j hj
    have hs : (List.ofFn fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q))[j]?
        = some ((st.rgt)^[j] (st.chd q)) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨by simpa using hj, List.getElem_ofFn (by simpa using hj)⟩
    rw [kids, List.getD_eq_getElem?_getD, hs]
    exact List.mem_ofFn.mpr ⟨⟨j, by simpa using hj⟩, rfl⟩
  intro q j k hjk hk
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    by_cases hdeg : st.deg p = 0
    · rw [deg_merge_zero st r p hdeg] at hk
      rw [merge_kids_link_zero st r p hdeg, kids_eq_nil hdeg]
      have hk0 : k = 0 := by omega
      subst hk0
      exact absurd hjk (by omega)
    · rw [deg_merge_pos st r p hdeg] at hk
      rw [merge_kids_link_pos st r p hpar hrnc hnr hrk hpre hdeg]
      have hkl : (kids st p).length = st.deg p := kids_length st p
      by_cases hklt : k < st.deg p
      · rw [getD_append_lt (by rw [hkl]; omega : j < (kids st p).length),
          getD_append_lt (by rw [hkl]; omega : k < (kids st p).length)]
        exact hnd p j k hjk hklt
      · have hk0 : k = st.deg p := by omega
        subst hk0
        rw [getD_append_lt (by rw [kids_length]; omega : j < (kids st p).length),
          ← kids_length, getD_append_last]
        exact hrnot p hp0 _ (hmemD p j (by rw [kids_length]; omega))
  · by_cases hq0 : q = 0
    · subst hq0
      rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hp0 hc.symm), hnl] at hk
      exact absurd hk (by omega)
    · rw [mergeState_deg, if_neg hqp] at hk
      rw [merge_kids_unchanged st r p q hpar hrnc hrk hpre hqp hq0]
      exact hnd q j k hjk hk

/-- `PosOK` survives the merge.  This is the one discharge where the merge's premise
replaces the link's: the moved root `r` is appended at position `deg p` with link degree
`deg r` (its mark clears), and the premise gives exactly `deg p ≤ deg r`.  Old positions
keep their link degrees (the only mark written is on `r`, which sits on no old list), and
`p`'s own entry only grows. -/
theorem merge_posOK (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hnl : NILLeaf st)
    (hpos : PosOK st) : PosOK (mergeState st r p) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hrp : r ≠ p := hpre.2.2.1
  have hle : st.deg p ≤ st.deg r := hpre.2.2.2
  have hrnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ r := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hq0)
  have hmemD : ∀ q j, j < (kids st q).length → (kids st q).getD j 0 ∈ kids st q := by
    intro q j hj
    have hs : (List.ofFn fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q))[j]?
        = some ((st.rgt)^[j] (st.chd q)) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨by simpa using hj, List.getElem_ofFn (by simpa using hj)⟩
    rw [kids, List.getD_eq_getElem?_getD, hs]
    exact List.mem_ofFn.mpr ⟨⟨j, by simpa using hj⟩, rfl⟩
  intro q j hj
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    by_cases hdeg : st.deg p = 0
    · rw [merge_kids_link_zero st r p hdeg, kids_eq_nil hdeg] at hj ⊢
      simp only [List.nil_append, List.length_cons, List.length_nil, Nat.lt_one_iff] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      have hget : (([] : List ℕ) ++ [r]).getD 0 0 = r := rfl
      rw [hget]
      unfold ldeg
      rw [mergeState_deg, if_neg (fun h2 => hrp h2), mergeState_mrk, if_pos rfl]
      omega
    · rw [merge_kids_link_pos st r p hpar hrnc hnr hrk hpre hdeg] at hj ⊢
      have hj1 : j < st.deg p + 1 := by
        simp only [List.length_append, kids_length] at hj
        exact hj
      by_cases hjl : j < st.deg p
      · rw [getD_append_lt (by rw [kids_length]; omega : j < (kids st p).length)]
        have hxne : (kids st p).getD j 0 ≠ r :=
          hrnot p hp0 _ (hmemD p j (by rw [kids_length]; omega))
        have hl : ldeg st ((kids st p).getD j 0)
            ≤ ldeg (mergeState st r p) ((kids st p).getD j 0) := by
          unfold ldeg
          rw [mergeState_deg, mergeState_mrk]
          by_cases hxp : (kids st p).getD j 0 = p
          · rw [hxp, if_pos rfl, if_neg (show (p:ℕ) ≠ r from fun hc => hxne (hxp.trans hc))]
            omega
          · rw [if_neg hxp, if_neg hxne]
        calc j ≤ ldeg st ((kids st p).getD j 0) := hpos p j (by rw [kids_length]; omega)
          _ ≤ ldeg (mergeState st r p) ((kids st p).getD j 0) := hl
      · have hj0 : j = st.deg p := by omega
        subst hj0
        rw [← kids_length, getD_append_last]
        unfold ldeg
        rw [mergeState_deg, if_neg (fun h2 => hrp h2), mergeState_mrk_r, kids_length]
        omega
  · by_cases hq0 : q = 0
    · subst hq0
      rw [kids_eq_nil (by
        rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hp0 hc.symm)]
        exact hnl)] at hj
      simp at hj
    · rw [merge_kids_unchanged st r p q hpar hrnc hrk hpre hqp hq0] at hj ⊢
      have hxne : (kids st q).getD j 0 ≠ r := hrnot q hq0 _ (hmemD q j hj)
      have hl : ldeg st ((kids st q).getD j 0)
          ≤ ldeg (mergeState st r p) ((kids st q).getD j 0) := by
        unfold ldeg
        rw [mergeState_deg, mergeState_mrk]
        by_cases hxp : (kids st q).getD j 0 = p
        · rw [hxp, if_pos rfl, if_neg (show (p:ℕ) ≠ r from fun hc => hxne (hxp.trans hc))]
          omega
        · rw [if_neg hxp, if_neg hxne]
      calc j ≤ ldeg st ((kids st q).getD j 0) := hpos q j hj
        _ ≤ ldeg (mergeState st r p) ((kids st q).getD j 0) := hl

/-- `SlotOK` survives the merge: other lists are untouched, and the moved root `r` is live
(`RootsLive`). -/
theorem merge_slotOK (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hrl : RootsLive st)
    (hnl : NILLeaf st) (hslot : SlotOK st) : SlotOK (mergeState st r p) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hn : (mergeState st r p).n = st.n := mergeState_n st r p
  intro q hq x hx
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    by_cases hdeg : st.deg p = 0
    · rw [merge_kids_link_zero st r p hdeg] at hx
      rw [hn] at hq ⊢
      rcases List.mem_append.mp hx with hx | hx
      · exact hslot p hq x hx
      · have hxc : r = x := (List.mem_singleton.mp hx).symm
        subst hxc
        exact hrl r hpre.1
    · rw [merge_kids_link_pos st r p hpar hrnc hnr hrk hpre hdeg] at hx
      rw [hn] at hq ⊢
      rcases List.mem_append.mp hx with hx | hx
      · exact hslot p hq x hx
      · have hxc : r = x := (List.mem_singleton.mp hx).symm
        subst hxc
        exact hrl r hpre.1
  · by_cases hq0 : q = 0
    · subst hq0
      have hdg : (mergeState st r p).deg 0 = 0 := by
        rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hp0 hc.symm)]
        exact hnl
      rw [kids_eq_nil hdg] at hx
      simp at hx
    · rw [merge_kids_unchanged st r p q hpar hrnc hrk hpre hqp hq0] at hx
      rw [hn] at hq ⊢
      exact hslot q hq x hx

/-- `Acyc` survives the merge (NIL discharge).  The splice's only `par` change is
`par r := p`; a chain that hits `r` moves to `p` and dies at NIL (every root's `par` is 0,
`NILSelf`), one that misses `r` is an old chain, and either way a closure forces the node
to be 0. -/
theorem merge_acyc (st : HState) (r p : ℕ) (hnr : NILNotRoot st) (hpre : MergePre st r p)
    (hnrs : NILRoots st) (hns : NILSelf st) (hac : Acyc st) : Acyc (mergeState st r p) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hr0 : (0:ℕ) ≠ r := fun hc => hnr (hc ▸ hpre.1)
  have hrp : r ≠ p := hpre.2.2.1
  have f0 : (mergeState st r p).par 0 = 0 := by
    rw [mergeState_par_ne st r p 0 hr0]; exact hns
  have fp0 : (mergeState st r p).par p = 0 := by
    rw [mergeState_par_ne st r p p (fun hc => hrp hc.symm)]; exact hnrs p hpre.2.1
  have fzero : ∀ k : ℕ, (mergeState st r p).par^[k] 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, f0]
  intro x j hj heq
  by_cases hhit : ∃ m, m < j ∧ (mergeState st r p).par^[m] x = r
  · obtain ⟨m, hmj, hmc⟩ := hhit
    have hstep : (mergeState st r p).par^[m + 2] x = 0 := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hmc,
        mergeState_par_r st r p, fp0]
    by_cases hjm : j = m + 1
    · subst hjm
      have hfx : (mergeState st r p).par^[m + 1] x = p := by
        rw [Function.iterate_succ_apply', hmc, mergeState_par_r st r p]
      have hpx : p = x := hfx.symm.trans heq
      have h0 : (mergeState st r p).par^[m + 1] x = 0 := by
        rw [Function.iterate_succ_apply, ← hpx, fp0, fzero]
      rw [h0] at heq
      exact heq.symm
    · have hj2 : m + 2 ≤ j := by omega
      rw [show j = j - (m + 2) + (m + 2) from by omega, Function.iterate_add_apply, hstep,
        fzero] at heq
      exact heq.symm
  · -- the chain never visits r: it is an old chain
    have hall : ∀ i, i ≤ j → (mergeState st r p).par^[i] x = (st.par)^[i] x := by
      intro i hi
      induction i with
      | zero => rfl
      | succ k ih =>
        have hlt : k < j := by omega
        have hikj : k ≤ j := by omega
        have hkne : (st.par)^[k] x ≠ r := by
          intro hc
          rw [← ih hikj] at hc
          exact hhit ⟨k, hlt, hc⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hikj,
          mergeState_par_ne st r p _ hkne]
    rw [hall j (le_refl j)] at heq
    exact hac x j hj heq

/-! ## The NIL family, RootNotChild, RootsLive, RingOK -/

/-- `NILRoots` survives the merge: the moved root `r` is filtered out (all occurrences), so
every remaining root keeps `par = 0`. -/
theorem merge_NILRoots (st : HState) (r p : ℕ) (hnrs : NILRoots st) :
    NILRoots (mergeState st r p) := by
  have hr : (mergeState st r p).roots = st.roots.filter (fun x => x != r) :=
    mergeState_roots st r p
  intro r' hr'
  rw [hr, List.mem_filter] at hr'
  obtain ⟨hmem, hne⟩ := hr'
  have hner : r' ≠ r := by
    intro hc
    rw [hc] at hne
    simp at hne
  rw [mergeState_par_ne st r p r' hner]
  exact hnrs r' hmem

/-- `NILSelf` survives the merge: NIL is never the moved root. -/
theorem merge_NILSelf (st : HState) (r p : ℕ) (hpre : MergePre st r p) (hnr : NILNotRoot st)
    (hns : NILSelf st) : NILSelf (mergeState st r p) := by
  show (mergeState st r p).par 0 = 0
  rw [mergeState_par, if_neg (show (0:ℕ) ≠ r from fun hc => hnr (hc ▸ hpre.1))]
  exact hns

/-- `NILNotRoot` survives the merge: filtering a root list cannot add one. -/
theorem merge_NILNotRoot (st : HState) (r p : ℕ) (hnn : NILNotRoot st) :
    NILNotRoot (mergeState st r p) := by
  have hr : (mergeState st r p).roots = st.roots.filter (fun x => x != r) :=
    mergeState_roots st r p
  intro h
  rw [hr, List.mem_filter] at h
  exact hnn h.1

/-- `NILLeaf` survives the merge: the degree write hits `p ≠ 0`, never NIL. -/
theorem merge_NILLeaf (st : HState) (r p : ℕ) (hpre : MergePre st r p) (hnr : NILNotRoot st)
    (hnl : NILLeaf st) : NILLeaf (mergeState st r p) := by
  show (mergeState st r p).deg 0 = 0
  rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hnr (hc ▸ hpre.2.1)), hnl]

/-- `NILNotChild` survives the merge: `p`'s list gains the moved root `r ≠ 0`, every other
list is untouched, and NIL sits on no list. -/
theorem merge_NILNotChild (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hnl : NILLeaf st)
    (hnc : NILNotChild st) : NILNotChild (mergeState st r p) := by
  have hr0 : (0:ℕ) ≠ r := fun hc => hnr (hc ▸ hpre.1)
  intro q hv
  by_cases hqp : q = p
  · rw [hqp] at hv
    rw [merge_kids_link st r p hpar hrnc hnr hrk hpre] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hnc p hv
    · exact hr0 (List.mem_singleton.mp hv)
  · by_cases hq0 : q = 0
    · subst hq0
      have hdg : (mergeState st r p).deg 0 = 0 := by
        rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hnr (hc ▸ hpre.2.1))]
        exact hnl
      rw [kids_eq_nil hdg] at hv
      simp at hv
    · rw [merge_kids_unchanged st r p q hpar hrnc hrk hpre hqp hq0] at hv
      exact hnc q hv

/-- `RootNotChild` survives the merge: the moved root `r` left the root list (so it is no
longer a root at all), every remaining root is on no `q ≠ 0` list — `p`'s list gained `r`
only, and every other list is untouched. -/
theorem merge_RootNotChild (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : MergePre st r p) (hnl : NILLeaf st) :
    RootNotChild (mergeState st r p) := by
  have hr0 : (0:ℕ) ≠ r := fun hc => hnr (hc ▸ hpre.1)
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hr : (mergeState st r p).roots = st.roots.filter (fun x => x != r) :=
    mergeState_roots st r p
  intro r' hr' q hq0 hv
  rw [hr, List.mem_filter] at hr'
  obtain ⟨hmem, hne⟩ := hr'
  have hner : r' ≠ r := by
    intro hc
    rw [hc] at hne
    simp at hne
  by_cases hqp : q = p
  · rw [hqp] at hv
    rw [merge_kids_link st r p hpar hrnc hnr hrk hpre] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hrnc r' hmem p hp0 hv
    · exact hner (List.mem_singleton.mp hv)
  · rw [merge_kids_unchanged st r p q hpar hrnc hrk hpre hqp hq0] at hv
    exact hrnc r' hmem q hq0 hv

/-- `RootsLive` survives the merge: filtering a root list keeps the remaining roots. -/
theorem merge_RootsLive (st : HState) (r p : ℕ) (hpre : MergePre st r p)
    (hrl : RootsLive st) : RootsLive (mergeState st r p) := by
  have hr : (mergeState st r p).roots = st.roots.filter (fun x => x != r) :=
    mergeState_roots st r p
  intro r' hr'
  rw [hr, List.mem_filter] at hr'
  obtain ⟨hmem, -⟩ := hr'
  rw [mergeState_n]
  exact hrl r' hmem

/-- `RingOK` survives the merge.  For `p` itself: appending `r` at the tail gives a ring of
period `deg p + 1` that closes (`r`'s own `rgt` is re-pointed at the head), is injective
(`r` is on no old list — `RootNotChild`), and whose head's `lft` is exactly `r` — the
splice's `lft (chd p) := r` write.  For `q ≠ p`: the q-walk visits only nodes recording
`q`, and every write-target records `p` or is off-list, so `q`'s ring is untouched.  For
`r` itself: its children record `r` and the write-targets record `p`, so `r`'s own ring is
untouched too. -/
theorem merge_RingOK (st : HState) (r p : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hpre : MergePre st r p)
    (hnl : NILLeaf st) (hac : Acyc st) : RingOK (mergeState st r p) := by
  have hrp : r ≠ p := hpre.2.2.1
  have hr0 : (0:ℕ) ≠ r := fun hc => hnr (hc ▸ hpre.1)
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.2.1)
  have hmem : ∀ z j, j < st.deg z → (st.rgt)^[j] (st.chd z) ∈ kids st z := by
    intro z j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  have hcnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ r := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hq0)
  intro q
  by_cases hqp : q = p
  · rw [hqp]
    by_cases hdp : st.deg p = 0
    · -- deg p = 0: the moved root becomes a singleton ring
      rw [deg_merge_zero st r p hdp, chd_merge_zero st r p hdp]
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [Function.iterate_one]
        exact rgt_merge_r_zero st r p hdp
      · intro j k hj hk heq
        have hj0 : j = 0 := by omega
        have hk0 : k = 0 := by omega
        subst hj0
        subst hk0
        rfl
      · rw [Function.iterate_zero_apply]
        exact lft_merge_r_zero st r p hdp
    · -- deg p ≥ 1: the appended ring
      rw [deg_merge_pos st r p hdp, chd_merge_pos st r p hdp]
      have hwalk := merge_walk_pos st r p hpar hrnc hnr hrk hpre hdp
      have hpc : p ≠ r := fun hc => hrp hc.symm
      have hcnotp : ∀ x ∈ kids st p, x ≠ r := by
        intro x hx hc
        subst hc
        exact absurd hx (root_notin_kids_merge st hrnc hpre.1 hp0)
      refine Or.inr ⟨?_, ?_, ?_⟩
      · -- closure: the walk runs the old ring, steps to `r`, then back to the head
        rw [Function.iterate_succ_apply', hwalk (st.deg p) (le_refl (st.deg p)), if_pos rfl,
          rgt_merge_r st r p hdp]
      · -- injectivity: the new element is on no old list
        intro j k hj hk heq
        by_cases hjd : j = st.deg p
        · subst hjd
          by_cases hkd : k = st.deg p
          · exact hkd.symm
          · rw [hwalk (st.deg p) (le_refl (st.deg p)), if_pos rfl, hwalk k (by omega),
              if_neg hkd] at heq
            exact absurd heq.symm (hcnotp _ (hmem p k (by omega)))
        · by_cases hkd : k = st.deg p
          · subst hkd
            rw [hwalk (st.deg p) (le_refl (st.deg p)), if_pos rfl, hwalk j (by omega),
              if_neg hjd] at heq
            exact absurd heq (hcnotp _ (hmem p j (by omega)))
          · rw [hwalk j (by omega), if_neg hjd, hwalk k (by omega), if_neg hkd] at heq
            exact ((hrk p).resolve_left hdp).2.1 j k (by omega) (by omega) heq
      · -- the head's `lft` is the appended root, which is walk position `deg p`
        rw [show st.deg p + 1 - 1 = st.deg p from by omega]
        rw [lft_merge_head st r p hac hnrs hpar hpre.1 hp0 hdp,
          hwalk (st.deg p) (le_refl (st.deg p)), if_pos rfl]
  · -- q ≠ p: the ring is untouched
    by_cases hq0 : q = 0
    · subst hq0
      have hdg : (mergeState st r p).deg 0 = 0 := by
        rw [mergeState_deg, if_neg (show (0:ℕ) ≠ p from fun hc => hp0 hc.symm)]
        exact hnl
      exact Or.inl hdg
    · by_cases hdq0 : (mergeState st r p).deg q = 0
      · exact Or.inl hdq0
      · right
        have hdq : st.deg q ≠ 0 := by
          rw [mergeState_deg, if_neg hqp] at hdq0
          exact hdq0
        have hchdq : (mergeState st r p).chd q = st.chd q := by
          by_cases h : st.deg p = 0
          · simp [mergeState, linkState, h, hqp]
          · simp [mergeState, linkState, h, hqp]
        have hchdqr : st.chd q ≠ r := by
          intro hc
          have hm : st.chd q ∈ kids st q := hmem q 0 (by omega)
          rw [hc] at hm
          have hpar' : st.par r = q := hpar q _ hm
          exact hq0 (hpar'.symm.trans (hnrs r hpre.1))
        have hvne : ∀ k < st.deg q, (st.rgt)^[k] (st.chd q) ≠ r := by
          intro k hk hc
          have hm : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem q k hk
          rw [hc] at hm
          exact hq0 ((hpar q _ hm).symm.trans (hnrs r hpre.1))
        have hle1 : st.deg q - 1 ≤ st.deg q := by omega
        have hvlftp : ∀ k, k < st.deg q → st.deg p ≠ 0 →
            (st.rgt)^[k] (st.chd q) ≠ st.lft (st.chd p) := by
          intro k hk hdp hc
          have htin : st.lft (st.chd p) ∈ kids st p := by
            rw [((hrk p).resolve_left hdp).2.2]
            exact hmem p (st.deg p - 1) (by omega)
          have hm : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem q k hk
          rw [hc] at hm
          exact hqp ((hpar q (st.lft (st.chd p)) hm).symm.trans
            (hpar p (st.lft (st.chd p)) htin))
        have hw : ∀ j, j ≤ st.deg q →
            (mergeState st r p).rgt^[j] ((mergeState st r p).chd q)
              = (st.rgt)^[j] (st.chd q) := by
          intro j
          induction j with
          | zero => simp [hchdq]
          | succ k ih =>
              intro hik
              have hkq : k < st.deg q := by omega
              have hik' : k ≤ st.deg q := by omega
              rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hik']
              by_cases hdp : st.deg p = 0
              · rw [mergeState_rgt_zero st r p _ hdp, if_neg (hvne k hkq)]
              · rw [mergeState_rgt_pos st r p _ hdp, if_neg (hvne k hkq),
                  if_neg (hvlftp k hkq hdp)]
        refine ⟨?_, ?_, ?_⟩
        · rw [mergeState_deg, if_neg hqp, hw (st.deg q) (le_refl (st.deg q)), hchdq]
          exact ((hrk q).resolve_left hdq).1
        · intro j k hj hk heq
          rw [mergeState_deg, if_neg hqp] at hj hk
          rw [hw j (by omega), hw k (by omega)] at heq
          exact ((hrk q).resolve_left hdq).2.1 j k hj hk heq
        · by_cases hdp : st.deg p = 0
          · rw [mergeState_deg, if_neg hqp, hw (st.deg q - 1) hle1, hchdq,
              mergeState_lft_zero st r p (st.chd q) hdp, if_neg hchdqr,
              ((hrk q).resolve_left hdq).2.2]
          · have hchdqp : st.chd q ≠ st.chd p := by
              intro hc
              have hm : st.chd q ∈ kids st q := hmem q 0 (by omega)
              have hm2 : st.chd p ∈ kids st p := hmem p 0 (by omega)
              rw [hc] at hm
              exact hqp ((hpar q (st.chd p) hm).symm.trans (hpar p (st.chd p) hm2))
            rw [mergeState_deg, if_neg hqp, hw (st.deg q - 1) hle1, hchdq,
              lft_merge_other st r p (st.chd q) hdp hchdqp hchdqr,
              ((hrk q).resolve_left hdq).2.2]

/-! ## The merge-output witness -/

/-- The merge witness's pre-state: NIL at slot 0, two bare roots at slots 1, 2. -/
def mergePreSt : HState where
  par := fun _ => 0
  chd := fun _ => 0
  rgt := fun _ => 0
  lft := fun _ => 0
  deg := fun _ => 0
  mrk := fun _ => 0
  roots := [1, 2]
  n := 3

/-- The merge output: slot 1 absorbs slot 2 (both of degree 0). -/
def merged : HState := mergeState mergePreSt 2 1

theorem mergePreSt_ok : MergePre mergePreSt 2 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mergePreSt] <;> omega

@[simp] theorem merged_par (v : ℕ) : merged.par v = if v = 2 then 1 else 0 := by
  by_cases h : v = 2 <;> simp [merged, mergeState, mergePreSt, h]
@[simp] theorem merged_mrk (v : ℕ) : merged.mrk v = 0 := by
  by_cases h : v = 2 <;> simp [merged, mergeState, mergePreSt, h]
@[simp] theorem merged_deg (v : ℕ) : merged.deg v = if v = 1 then 1 else 0 := by
  by_cases h : v = 1 <;> simp [merged, mergeState, mergePreSt, h]
@[simp] theorem merged_chd (v : ℕ) : merged.chd v = if v = 1 then 2 else 0 := by
  by_cases h : v = 1 <;> simp [merged, mergeState, mergePreSt, h]
@[simp] theorem merged_rgt (v : ℕ) : merged.rgt v = if v = 2 then 2 else 0 := by
  simp [merged, mergeState, mergePreSt]
@[simp] theorem merged_lft (v : ℕ) : merged.lft v = if v = 2 then 2 else 0 := by
  simp [merged, mergeState, mergePreSt]
@[simp] theorem merged_roots : merged.roots = [1] := by simp [merged, mergeState, mergePreSt]
@[simp] theorem merged_n : merged.n = 3 := rfl
@[simp] theorem kids_merged (q : ℕ) : kids merged q = if q = 1 then [2] else [] := by
  unfold kids
  by_cases hq : q = 1
  · subst hq
    simp [merged, mergeState, mergePreSt, Function.iterate_one]
  · simp [merged, mergeState, mergePreSt, hq]

theorem merged_ParOK : ParOK merged := by
  intro q v hv
  by_cases hq : q = 1
  · subst hq
    simp at hv
    subst hv
    simp
  · rw [kids_merged, if_neg hq] at hv
    simp at hv

theorem merged_SlotOK : SlotOK merged := by
  intro q hq v hv
  by_cases hq1 : q = 1
  · subst hq1
    simp at hv
    subst hv
    simp
  · rw [kids_merged, if_neg hq1] at hv
    simp at hv

theorem merged_ParSlot : ParSlot merged := by
  intro q _
  by_cases hq : q = 2
  · subst hq; simp
  · simp [hq]

theorem merged_KidsNodup : ∀ q, KidsNodup merged q := by
  intro q j k hjk hk
  by_cases hq : q = 1
  · subst hq
    rw [merged_deg, if_pos rfl] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [kids_merged, if_pos rfl]
    by_cases hj0 : j = 0
    · subst hj0; exact absurd hjk (by omega)
    · simp [hj0]
  · rw [merged_deg, if_neg hq] at hk
    simp at hk

theorem merged_NILRoots : NILRoots merged := by
  intro r hr
  rw [merged_roots] at hr
  simp at hr
  subst hr
  simp

theorem merged_NILSelf : NILSelf merged := rfl

theorem merged_NILNotChild : NILNotChild merged := by
  intro q hv
  by_cases hq : q = 1
  · subst hq
    simp at hv
  · rw [kids_merged, if_neg hq] at hv
    simp at hv

theorem merged_RootNotChild : RootNotChild merged := by
  intro r hr q _ hv
  by_cases hq : q = 1
  · subst hq
    rw [merged_roots] at hr
    simp at hv
    subst hv
    simp at hr
  · rw [kids_merged, if_neg hq] at hv
    simp at hv

theorem merged_RootsLive : RootsLive merged := by
  intro r hr
  rw [merged_roots] at hr
  simp at hr
  subst hr
  simp

theorem merged_NILNotRoot : NILNotRoot merged := by
  intro h
  simp [merged, mergeState, mergePreSt] at h

theorem merged_NILLeaf : NILLeaf merged := rfl

theorem merged_Acyc : Acyc merged := by
  have hp2 : merged.par 2 = 1 := by simp
  have hp1 : merged.par 1 = 0 := by simp
  have hp0z : merged.par 0 = 0 := by simp
  have hzero : ∀ m : ℕ, (merged.par)^[m] 0 = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, hp0z]
  have hz1 : ∀ m : ℕ, (merged.par)^[m + 1] 1 = 0 := by
    intro m
    induction m with
    | zero => exact hp1
    | succ m ih => rw [Function.iterate_succ_apply', ih, hp0z]
  intro x j hj heq
  by_cases hx2 : x = 2
  · subst hx2
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1 : j = 1 := by omega
      subst hj1
      rw [Function.iterate_one, hp2] at heq
      simp at heq
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have hstep : (merged.par)^[m + 2] 2 = 0 := by
        rw [show (m:ℕ) + 2 = (m + 1) + 1 from rfl, Function.iterate_add_apply,
          Function.iterate_one, hp2]
        exact hz1 m
      rw [hstep] at heq
      simp at heq
  · cases j with
    | zero => omega
    | succ k =>
      have hx0 : merged.par x = 0 := by simp [hx2]
      have hall : ∀ m : ℕ, (merged.par)^[m + 1] x = 0 := by
        intro m
        induction m with
        | zero => exact hx0
        | succ m ih => rw [Function.iterate_succ_apply', ih, hp0z]
      rw [hall k] at heq
      exact heq.symm

theorem merged_MarkOK : MarkOK merged := by
  intro q
  simp

theorem merged_PosOK : PosOK merged := by
  intro q j hj
  by_cases hq : q = 1
  · subst hq
    rw [kids_merged, if_pos rfl] at hj ⊢
    simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [ldeg]
  · rw [kids_merged, if_neg hq] at hj
    simp at hj

/-- The merged witness satisfies the support condition at the absorbing root: its
abstraction is the two-node tree over slots 1, 2. -/
theorem merged_Support : Support merged (merged.n + 1) 1 := by
  refine ⟨{1, 2}, ?_, ?_⟩
  · have hshape : treeOf merged (merged.n + 1) 1
        = FibHeapForest.Tree.node 1
            [FibHeapForest.Child.mk (treeOf merged 3 2) (ldeg merged 2) (merged.mrk 2)] := by
      simp [treeOf, kids_merged]
    rw [hshape, FibHeapForest.size_node, FibHeapForest.sizeSum]
    simp [FibHeapForest.Child.size, FibHeapForest.Child.tree, FibHeapForest.size_node,
      FibHeapForest.sizeSum, treeOf, kids_merged]
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp

/-- **The capstone applied to a post-merge state.**  The merge transition keeps the machine
inside the invariant set, so the rank cap applies to the absorbing root. -/
theorem merged_capstone : merged.deg 1 ≤ FibHeapAccounting.rankCap merged.n := by
  have hsup := merged_Support
  have hpn : merged.n + 1 = 4 := by rw [merged_n]
  rw [merged_n] at hsup ⊢
  exact degree_le_rankCap_zero merged merged_ParOK merged_SlotOK merged_ParSlot
    merged_KidsNodup merged_Acyc merged_NILSelf merged_NILLeaf merged_NILNotChild
    merged_MarkOK merged_PosOK (by simp) (by simp [merged]) hsup

end Submission.FibHeapMerge
