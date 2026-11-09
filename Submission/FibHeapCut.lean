import Submission.FibHeapLinkWalk

/-!
# M3a: the cut updater — decrease-key's re-rooting step

`cutState st x y` is the exact array splice of one CLRS cascading-cut step: the child `x` is
removed from `y`'s circular child list, re-rooted (`par x := 0`, prepended to the root list),
and the parent is marked (`mrk y := 1`, `deg y := deg y - 1`).  Two splices, one per shape of
the target list:

* `deg y = 1` — `x` was the only child: `chd y := 0`, `deg y := 0`; no ring writes.
* `deg y ≥ 2` — the standard removal: `rgt (lft x) := rgt x`, `lft (rgt x) := lft x`,
  `chd y := rgt x` when `x` was the head.  The walk from the head then reads the old children
  in link order with exactly the position-`k` element skipped — `(kids st y).eraseIdx k` —
  which is what `pos_cut` (proved at list level in `FibHeapRefine`) consumes.

## The one honest extra premise

`RingOK` pins `lft` only at the *head* of a ring (`lft (chd p) = walk position deg p - 1`);
at an interior node `lft` is unconstrained, so the splice's neighbour write cannot be proved
correct from `RingOK` alone.  `CutPre` therefore carries the two facts the splice needs, both
true of every real ring: `st.rgt (st.lft x) = x` (`lft x` is a predecessor of `x`) and, when
`deg y ≥ 2`, `st.lft x ∈ kids st y` (so ring injectivity pins the predecessor position).

## The marked-parent boundary

`CutPre` also carries `st.mrk y = 0`.  The cut keeps `ldeg y = deg y + mrk y` invariant
(`(deg y - 1) + 1 = deg y + 0`) — but only because the parent was unmarked.  Cutting from a
*marked* parent drops `ldeg y` to `deg y - 1`, which breaks `PosOK` at the grandparent; that
case is precisely what the CLRS cascade exists to repair, and it belongs to the promote/cascade
updater, not to this step.

## What lands here

The re-root walk (`kids_cut` — the `List.ext_get`-pointwise treatment, `kids_length`
pre-normalised before `omega`), the untouched-list lemma for every `q ≠ y`
(`kids_cut_unchanged`, the `kids_unchanged` machinery consumed the way the link discharges
consumed it), and the invariant bundle: `MarkOK`, `ParSlot`, `ParOK`, `KidsNodup`, `PosOK`,
`SlotOK`, `Acyc`, `NILRoots`, `NILSelf`, `NILNotRoot`, `NILLeaf`, `NILNotChild`,
`RootNotChild`, `RootsLive`, and `RingOK` — the walk machinery the *next* updater in the arc
will consume.  The cut-output witness (`cutted`, the link witness's child cut back off)
re-proves the whole bundle, so the capstone applies to a post-cut state: the invariant set has
a model after the transition, and the arc's next `CutPre`/`LinkPre` is satisfiable.

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapCut

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink Submission.FibHeapLinkWalk

/-! ## The cut splice -/

/-- Preconditions of a cut: `x` is a child of the live unmarked node `y`, and `lft x` is a
predecessor of `x` (true of every real ring; `RingOK` pins `lft` only at ring heads, so the
splice's neighbour write needs this stated). -/
def CutPre (st : HState) (x y : ℕ) : Prop :=
  x ∈ kids st y ∧ y < st.n ∧ st.mrk y = 0
    ∧ st.rgt (st.lft x) = x ∧ (2 ≤ st.deg y → st.lft x ∈ kids st y)

/-- The cut splice.  Both branches write only to already-live slots. -/
def cutState (st : HState) (x y : ℕ) : HState :=
  if st.deg y = 1 then
    { st with
      par := (fun i => if i = x then 0 else st.par i)
      mrk := (fun i => if i = y then 1 else st.mrk i)
      deg := (fun i => if i = y then st.deg i - 1 else st.deg i)
      chd := (fun i => if i = y then 0 else st.chd i)
      roots := x :: st.roots }
  else
    { st with
      par := (fun i => if i = x then 0 else st.par i)
      mrk := (fun i => if i = y then 1 else st.mrk i)
      deg := (fun i => if i = y then st.deg i - 1 else st.deg i)
      chd := (fun i => if i = y then if st.chd y = x then st.rgt x else st.chd i else st.chd i)
      rgt := (fun i => if i = st.lft x then st.rgt x else st.rgt i)
      lft := (fun i => if i = st.rgt x then st.lft x else st.lft i)
      roots := x :: st.roots }

/-! ## Pointwise behaviour of the splice -/

theorem cutState_deg (st : HState) (x y q : ℕ) :
    (cutState st x y).deg q = if q = y then st.deg q - 1 else st.deg q := by
  unfold cutState
  by_cases h : st.deg y = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem cutState_mrk (st : HState) (x y q : ℕ) :
    (cutState st x y).mrk q = if q = y then 1 else st.mrk q := by
  unfold cutState
  by_cases h : st.deg y = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem cutState_par (st : HState) (x y q : ℕ) :
    (cutState st x y).par q = if q = x then 0 else st.par q := by
  unfold cutState
  by_cases h : st.deg y = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem cutState_roots (st : HState) (x y : ℕ) :
    (cutState st x y).roots = x :: st.roots := by
  unfold cutState
  by_cases h : st.deg y = 1
  · simp [h]
  · simp [h]

theorem cutState_n (st : HState) (x y : ℕ) : (cutState st x y).n = st.n := by
  unfold cutState
  by_cases h : st.deg y = 1
  · simp [h]
  · simp [h]

theorem cutState_par_x (st : HState) (x y : ℕ) : (cutState st x y).par x = 0 := by
  rw [cutState_par, if_pos rfl]

theorem cutState_par_ne (st : HState) (x y q : ℕ) (hne : q ≠ x) :
    (cutState st x y).par q = st.par q := by
  rw [cutState_par, if_neg hne]

theorem cutState_mrk_y (st : HState) (x y : ℕ) : (cutState st x y).mrk y = 1 := by
  rw [cutState_mrk, if_pos rfl]

theorem cutState_mrk_ne (st : HState) (x y q : ℕ) (hne : q ≠ y) :
    (cutState st x y).mrk q = st.mrk q := by
  rw [cutState_mrk, if_neg hne]

theorem cutState_chd_zero (st : HState) (x y : ℕ) (h : st.deg y = 1) :
    (cutState st x y).chd y = 0 := by
  simp [cutState, h]

theorem cutState_rgt_eq (st : HState) (x y v : ℕ) (h : st.deg y = 1) :
    (cutState st x y).rgt v = st.rgt v := by
  simp [cutState, h]

theorem cutState_lft_eq (st : HState) (x y v : ℕ) (h : st.deg y = 1) :
    (cutState st x y).lft v = st.lft v := by
  simp [cutState, h]

theorem cutState_chd_ne (st : HState) (x y q : ℕ) (h : st.deg y ≠ 1) :
    (cutState st x y).chd q =
      if q = y then (if st.chd y = x then st.rgt x else st.chd y) else st.chd q := by
  by_cases hq : q = y
  · simp [cutState, h, hq]
  · simp [cutState, h, hq]

theorem cutState_rgt_ne (st : HState) (x y v : ℕ) (h : st.deg y ≠ 1) (hv : v ≠ st.lft x) :
    (cutState st x y).rgt v = st.rgt v := by
  simp [cutState, h, hv]

theorem cutState_rgt_pred (st : HState) (x y : ℕ) (h : st.deg y ≠ 1) :
    (cutState st x y).rgt (st.lft x) = st.rgt x := by
  simp [cutState, h]

theorem cutState_lft_ne (st : HState) (x y v : ℕ) (h : st.deg y ≠ 1) (hv : v ≠ st.rgt x) :
    (cutState st x y).lft v = st.lft v := by
  simp [cutState, h, hv]

theorem cutState_lft_succ (st : HState) (x y : ℕ) (h : st.deg y ≠ 1) :
    (cutState st x y).lft (st.rgt x) = st.lft x := by
  simp [cutState, h]

/-! ## Positions in the ring -/

/-- A child sits at some walk position. -/
theorem exists_pos_of_mem {st : HState} {x y : ℕ} (hx : x ∈ kids st y) :
    ∃ k, k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x := by
  rw [kids, List.mem_ofFn] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨j.val, j.isLt, hj⟩

/-- `getD` into a child list is the walk value. -/
theorem kids_getD (st : HState) (y m : ℕ) (hm : m < st.deg y) :
    (kids st y).getD m 0 = (st.rgt)^[m] (st.chd y) := by
  have hs : (List.ofFn fun i : Fin (st.deg y) => (st.rgt)^[i.val] (st.chd y))[m]?
      = some ((st.rgt)^[m] (st.chd y)) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨by simpa using hm, List.getElem_ofFn (by simpa using hm)⟩
  rw [kids, List.getD_eq_getElem?_getD, hs]
  simp

/-- A `getD` value of a child list is a member of it. -/
theorem kids_getD_mem (st : HState) (q j : ℕ) (hj : j < (kids st q).length) :
    (kids st q).getD j 0 ∈ kids st q := by
  have hs : (List.ofFn fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q))[j]?
      = some ((st.rgt)^[j] (st.chd q)) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨by simpa using hj, List.getElem_ofFn (by simpa using hj)⟩
  rw [kids, List.getD_eq_getElem?_getD, hs]
  exact List.mem_ofFn.mpr ⟨⟨j, by simpa using hj⟩, rfl⟩

/-- `k = 0` and `chd y = x` are interchangeable for the cut child at position `k`. -/
theorem chdx_iff (st : HState) (x y : ℕ) (hrk : RingOK st) (k : ℕ)
    (hk : k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x) :
    (st.chd y = x ↔ k = 0) := by
  obtain ⟨hclose, hinj, htail⟩ := (hrk y).resolve_left (by omega)
  constructor
  · intro hc
    have h0 : (st.rgt)^[0] (st.chd y) = (st.rgt)^[k] (st.chd y) := by
      rw [Function.iterate_zero, hk.2]; exact hc
    exact (hinj 0 k (by omega) hk.1 h0).symm
  · intro h
    rw [← hk.2, h, Function.iterate_zero_apply]

/-! ## The re-root walk -/

/-- The predecessor position: `lft x` sits immediately before `x` in the ring — position
`deg y - 1` when `x` is the head, `k - 1` at interior position `k`.  (`RingOK` alone pins
`lft` only at the head; the premise `st.rgt (st.lft x) = x` from `CutPre` plus ring
injectivity pins it everywhere.) -/
theorem pred_pos (st : HState) (x y : ℕ) (hrk : RingOK st) (hpre : CutPre st x y)
    (hd2 : 2 ≤ st.deg y) (k : ℕ) (hk : k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x) :
    st.lft x = (st.rgt)^[if k = 0 then st.deg y - 1 else k - 1] (st.chd y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨hclose, hinj, htail⟩ := (hrk y).resolve_left (by omega)
  have hxchd : k = 0 → st.chd y = x := by
    intro h
    rw [← hk.2, h, Function.iterate_zero_apply]
  by_cases hkz : k = 0
  · have hxc : st.chd y = x := hxchd hkz
    have hlx : st.lft x = st.lft (st.chd y) := by rw [hxc]
    rw [if_pos hkz, hlx]
    exact htail
  · obtain ⟨j, hjd, hjval⟩ := exists_pos_of_mem (hlftmem hd2)
    have hstep : (st.rgt)^[j + 1] (st.chd y) = (st.rgt)^[k] (st.chd y) := by
      rw [Function.iterate_succ_apply', hjval, hpred, hk.2]
    rcases Nat.lt_or_ge (j + 1) (st.deg y) with hlt | hge
    · have hje : j + 1 = k := hinj (j + 1) k hlt hk.1 hstep
      rw [if_neg hkz, ← hjval, show k - 1 = j from by omega]
    · have hjd' : j + 1 = st.deg y := by omega
      rw [hjd'] at hstep
      rw [hclose] at hstep
      have h0 : (st.rgt)^[0] (st.chd y) = (st.rgt)^[k] (st.chd y) := by
        rw [Function.iterate_zero]; exact hstep
      exact absurd (hinj 0 k (by omega) hk.1 h0) (by omega)

/-- **The re-root walk, positive-degree branch.**  After the cut, position `j` of `y`'s child
walk reads old position `j` for `j < k` and old position `j + 1` for `j ≥ k` — the child at
position `k` (the cut child `x`) is skipped. -/
theorem walk_cut_pos (st : HState) (x y : ℕ) (hrk : RingOK st) (hpre : CutPre st x y)
    (hd2 : 2 ≤ st.deg y) (k : ℕ) (hk : k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x) :
    ∀ j : ℕ, j < st.deg y - 1 →
      (cutState st x y).rgt^[j] ((cutState st x y).chd y) =
        (st.rgt)^[if j < k then j else j + 1] (st.chd y) := by
  have hpredpos := pred_pos st x y hrk hpre hd2 k hk
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  have hd1 : st.deg y ≠ 1 := by omega
  obtain ⟨hclose, hinj, htail⟩ := (hrk y).resolve_left (by omega)
  have hxchd : k = 0 → st.chd y = x := by
    intro h
    rw [← hk.2, h, Function.iterate_zero_apply]
  have hchdx : st.chd y = x → k = 0 := by
    intro hc
    have h0 : (st.rgt)^[0] (st.chd y) = (st.rgt)^[k] (st.chd y) := by
      rw [Function.iterate_zero, hk.2]; exact hc
    exact (hinj 0 k (by omega) hk.1 h0).symm
  -- The new head.
  have hchd : (cutState st x y).chd y = if k = 0 then st.rgt x else st.chd y := by
    rw [cutState_chd_ne st x y y hd1, if_pos rfl]
    by_cases hkz : k = 0
    · rw [if_pos (hxchd hkz), if_pos hkz]
    · rw [if_neg (fun hc => hkz (hchdx hc)), if_neg hkz]
  -- The splice's `rgt` behaviour.
  have hstep : ∀ v : ℕ, v ≠ st.lft x → (cutState st x y).rgt v = st.rgt v :=
    fun v hv => cutState_rgt_ne st x y v hd1 hv
  have hstepp : (cutState st x y).rgt (st.lft x) = st.rgt x := cutState_rgt_pred st x y hd1
  have hrgtx : st.rgt x = (st.rgt)^[k + 1] (st.chd y) := by
    rw [Function.iterate_succ_apply', hk.2]
  intro j
  induction j with
  | zero =>
    intro _
    rw [Function.iterate_zero_apply, hchd]
    rcases Nat.eq_zero_or_pos k with hkz | hkz
    · rw [hkz, if_pos rfl, if_neg (show ¬(0:ℕ) < 0 from by omega),
        Function.iterate_one, hxchd (by omega)]
    · rw [if_neg (show ¬(k:ℕ) = 0 from by omega),
        if_pos (show (0:ℕ) < k from by omega), Function.iterate_zero_apply]
  | succ j ih =>
    intro hj
    have hjlt : j < st.deg y - 1 := by omega
    rw [Function.iterate_succ_apply', ih hjlt]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [if_pos hjk]
      by_cases hjk1 : j + 1 = k
      · -- the transition: position `j = k - 1` is `lft x`
        have hk1 : 0 < k := by omega
        have hposj : (st.rgt)^[j] (st.chd y) = st.lft x := by
          rw [hpredpos, if_neg (show ¬(k:ℕ) = 0 from by omega), show k - 1 = j from by omega]
        rw [hposj, hstepp, hrgtx, if_neg (show ¬((j:ℕ) + 1) < k from by omega), hjk1]
      · -- strictly before the predecessor: the walk is untouched
        have hne : (st.rgt)^[j] (st.chd y) ≠ st.lft x := by
          intro hc
          rw [hpredpos, if_neg (show ¬(k:ℕ) = 0 from by omega)] at hc
          exact absurd (hinj j (k - 1) (by omega) (by omega) hc) (by omega)
        rw [hstep _ hne, if_pos (show (j:ℕ) + 1 < k from by omega)]
        exact (Function.iterate_succ_apply' st.rgt j (st.chd y)).symm
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]
      -- position `j + 1 ≤ deg y - 2` is neither the predecessor nor the tail
      have hne : (st.rgt)^[j + 1] (st.chd y) ≠ st.lft x := by
        intro hc
        rw [hpredpos] at hc
        by_cases hkz : k = 0
        · rw [if_pos hkz] at hc
          exact absurd (hinj (j + 1) (st.deg y - 1) (by omega) (by omega) hc) (by omega)
        · rw [if_neg hkz] at hc
          exact absurd (hinj (j + 1) (k - 1) (by omega) (by omega) hc) (by omega)
      rw [hstep _ hne, if_neg (show ¬((j:ℕ) + 1) < k from by omega)]
      exact (Function.iterate_succ_apply' st.rgt (j + 1) (st.chd y)).symm

/-- **The re-root walk, empty branch.**  Cutting the only child empties the list. -/
theorem kids_cut_zero (st : HState) (x y k : ℕ) (hpre : CutPre st x y)
    (hd : st.deg y = 1) (hk : k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x) :
    kids (cutState st x y) y = (kids st y).eraseIdx k := by
  have hk0 : k = 0 := by omega
  subst hk0
  unfold kids
  have hx : st.chd y = x := by rw [← hk.2, Function.iterate_zero_apply]
  rw [cutState_deg st x y y, if_pos rfl, hd, cutState_chd_zero st x y hd]
  simp [hx]

/-- **The re-root walk, positive-degree branch, as a list equation.** -/
theorem kids_cut_pos (st : HState) (x y k : ℕ) (hrk : RingOK st) (hpre : CutPre st x y)
    (hd2 : 2 ≤ st.deg y) (hk : k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x) :
    kids (cutState st x y) y = (kids st y).eraseIdx k := by
  have hd1 : st.deg y ≠ 1 := by omega
  have hw := walk_cut_pos st x y hrk hpre hd2 k hk
  -- the new head, in `hw`'s exact form
  have hxchd : k = 0 → st.chd y = x := by
    intro h
    rw [← hk.2, h, Function.iterate_zero_apply]
  have hchdx : st.chd y = x → k = 0 := (chdx_iff st x y hrk k hk).mp
  have hchd : (cutState st x y).chd y = if k = 0 then st.rgt x else st.chd y := by
    rw [cutState_chd_ne st x y y hd1, if_pos rfl]
    by_cases hkz : k = 0
    · rw [if_pos (hxchd hkz), if_pos hkz]
    · rw [if_neg (fun hc => hkz (hchdx hc)), if_neg hkz]
  unfold kids
  rw [cutState_deg st x y y, if_pos rfl]
  have hlen : ((List.ofFn fun j : Fin (st.deg y) => st.rgt^[j.val] (st.chd y)).eraseIdx k).length
      = st.deg y - 1 := by
    rw [length_eraseIdx_lt (cs := List.ofFn fun j : Fin (st.deg y) => st.rgt^[j.val] (st.chd y))
      (by simpa using hk.1)]
    simp
  rw [hchd] at hw
  refine List.ext_get ?_ (fun n h1 h2 => ?_)
  · rw [hlen]
    simp
  · simp only [List.get_eq_getElem, List.getElem_ofFn]
    rw [hchd]
    have hn : n < st.deg y - 1 := by
      have h3 := h2
      rw [hlen] at h3
      omega
    rw [hw n hn]
    have hd0 : ((List.ofFn fun j : Fin (st.deg y) => st.rgt^[j.val] (st.chd y)).eraseIdx k)[n]
        = ((List.ofFn fun j : Fin (st.deg y) => st.rgt^[j.val] (st.chd y)).eraseIdx k).getD n 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h2, rfl⟩]
      simp
    rw [hd0]
    rcases Nat.lt_or_ge n k with hnk | hnk
    · rw [getD_eraseIdx_lt hnk,
        show (List.ofFn fun j : Fin (st.deg y) => st.rgt^[j.val] (st.chd y)).getD n 0
            = (st.rgt)^[n] (st.chd y) from kids_getD st y n (by omega), if_pos hnk]
    · rw [getD_eraseIdx_ge hnk,
        show (List.ofFn fun j : Fin (st.deg y) => st.rgt^[j.val] (st.chd y)).getD (n + 1) 0
            = (st.rgt)^[n + 1] (st.chd y) from kids_getD st y (n + 1) (by omega),
        if_neg (show ¬((n:ℕ) < k) from by omega)]

/-- **The re-root walk.**  The cut child `x` sits at some position `k`; after the cut, `y`'s
child list is the old list with position `k` erased. -/
theorem kids_cut (st : HState) (x y : ℕ) (hrk : RingOK st) (hpre : CutPre st x y) :
    ∃ k, k < st.deg y ∧ (st.rgt)^[k] (st.chd y) = x ∧
      kids (cutState st x y) y = (kids st y).eraseIdx k := by
  have hd0 : 0 < st.deg y := by
    have h1 := kids_length st y
    have h2 := List.length_pos_of_mem hpre.1
    omega
  obtain ⟨k, hk1, hk2⟩ := exists_pos_of_mem hpre.1
  refine ⟨k, hk1, hk2, ?_⟩
  by_cases hd : st.deg y = 1
  · exact kids_cut_zero st x y k hpre hd ⟨hk1, hk2⟩
  · exact kids_cut_pos st x y k hrk hpre (by omega) ⟨hk1, hk2⟩

/-- The cut child no longer appears in `y`'s child list. -/
theorem cutchild_notin_kids (st : HState) (x y : ℕ) (hrk : RingOK st) (hpre : CutPre st x y)
    (hnd : KidsNodup st y) : x ∉ kids (cutState st x y) y := by
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_cut st x y hrk hpre
  obtain ⟨hclose, hinj, htail⟩ := (hrk y).resolve_left (by have := kids_length st y; omega)
  have hlen : ((kids st y).eraseIdx k).length = st.deg y - 1 := by
    rw [kids, length_eraseIdx_lt (by simpa using hk1)]
    simp
  intro hx
  rw [hkeq] at hx
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hx
  have hjlen : j < ((kids st y).eraseIdx k).length := hj
  have hjd : j < st.deg y := by omega
  have hje' : ((kids st y).eraseIdx k).getD j 0 = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨hjlen, hje⟩]
    simp
  -- position `j` of the erased list reads old position `if j < k then j else j + 1 ≠ k`
  rcases Nat.lt_or_ge j k with a | a
  · rw [getD_eraseIdx_lt a, kids_getD st y j (by omega)] at hje'
    exact absurd (hinj j k (by omega) hk1 (hje'.trans hkx.symm)) (by omega)
  · rw [getD_eraseIdx_ge a, kids_getD st y (j + 1) (by omega)] at hje'
    exact absurd (hinj (j + 1) k (by omega) hk1 (hje'.trans hkx.symm)) (by omega)

/-- **Every other child list is untouched by the cut.** -/
theorem kids_cut_unchanged (st : HState) (x y q : ℕ) (hpar : ParOK st) (hpre : CutPre st x y)
    (hq : q ≠ y) : kids (cutState st x y) q = kids st q := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  have hd0 : 0 < st.deg y := by
    have h1 := kids_length st y
    have h3 := List.length_pos_of_mem hx
    omega
  have h1 : (cutState st x y).deg q = st.deg q := by
    rw [cutState_deg, if_neg hq]
  have h2 : (cutState st x y).chd q = st.chd q := by
    by_cases hd : st.deg y = 1
    · simp [cutState, hd, hq]
    · rw [cutState_chd_ne st x y q hd, if_neg hq]
  have hmem : ∀ z j, j < st.deg z → (st.rgt)^[j] (st.chd z) ∈ kids st z := by
    intro z j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  have hw : ∀ j : ℕ, j < st.deg q →
      (cutState st x y).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
    intro j hj
    induction j with
    | zero => simp
    | succ k ih =>
      have hik : k < st.deg q := by omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hik]
      rcases Nat.lt_or_ge (st.deg y) 2 with hlt | hd2
      · exact cutState_rgt_eq st x y _ (by omega)
      · -- the walk visits only children of `q`; `lft x` is a child of `y`
        have hly : st.lft x ∈ kids st y := hlftmem (by omega)
        have hne : (st.rgt)^[k] (st.chd q) ≠ st.lft x := by
          intro hc
          have hm : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem q k hik
          rw [hc] at hm
          exact hq ((hpar q _ hm).symm.trans (hpar y _ hly))
        exact cutState_rgt_ne st x y _ (by omega) hne
  unfold kids
  rw [h1, h2]
  refine List.ext_get (by simp) (fun n hn1 hn2 => ?_)
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact hw n (by simpa using hn2)

/-! ## The invariant discharges -/

/-- `MarkOK` survives the cut: the only mark written is `mrk y := 1`. -/
theorem cut_MarkOK (st : HState) (x y : ℕ) (hm : MarkOK st) : MarkOK (cutState st x y) := by
  intro q
  rw [cutState_mrk]
  by_cases h : q = y
  · rw [if_pos h]
  · rw [if_neg h]; exact hm q

/-- `ParSlot` survives the cut: every `par` value is either unchanged or the NIL slot `0`. -/
theorem cut_ParSlot (st : HState) (x y : ℕ) (hpre : CutPre st x y) (hps : ParSlot st) :
    ParSlot (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  have hn : (cutState st x y).n = st.n := cutState_n st x y
  have hpos : 0 < st.n := by omega
  intro q hq
  rw [hn] at hq ⊢
  by_cases hqx : q = x
  · rw [hqx, cutState_par_x]
    exact hpos
  · rw [cutState_par_ne st x y q hqx]
    exact hps q hq

/-- `ParOK` survives the cut: `y`'s remaining children keep their parent, every other list is
untouched, and the only `par` write is `par x := 0`. -/
theorem cut_ParOK (st : HState) (x y : ℕ) (hpar : ParOK st) (hrk : RingOK st)
    (hpre : CutPre st x y) (hnd : KidsNodup st y) : ParOK (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_cut st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩
  intro q v hv
  by_cases hqy : q = y
  · rw [hqy] at hv ⊢
    rw [hkeq] at hv
    have hvm : v ∈ kids st y := List.mem_of_mem_eraseIdx hv
    have hvx : v ≠ x := by
      intro hc
      rw [hc] at hv
      apply cutchild_notin_kids st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩ hnd
      rw [hkeq]; exact hv
    rw [cutState_par_ne st x y v hvx]
    exact hpar y v hvm
  · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy] at hv
    have hvx : v ≠ x := by
      intro hc
      rw [hc] at hv
      exact hqy ((hpar q x hv).symm.trans (hpar y x hx))
    rw [cutState_par_ne st x y v hvx]
    exact hpar q v hv

/-- `KidsNodup` survives the cut: `y`'s list loses one element (the erased list is strictly
order-preserving on positions), every other list is untouched. -/
theorem cut_KidsNodup (st : HState) (x y : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : CutPre st x y) (hnd : ∀ q, KidsNodup st q) : ∀ q, KidsNodup (cutState st x y) q := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_cut st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩
  have hlen := length_eraseIdx_lt (by rw [kids_length]; exact hk1)
  have hmono : ∀ j j' : ℕ, j < j' → j' < st.deg y - 1 →
      (if j < k then j else j + 1) < (if j' < k then j' else j' + 1) := by
    intro j j' h hlt
    rcases Nat.lt_or_ge j k with a | a <;> rcases Nat.lt_or_ge j' k with b | b
    · rw [if_pos a, if_pos b]; exact h
    · rw [if_pos a, if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega), if_pos b]; omega
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega),
        if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
  have hget : ∀ j : ℕ, j < st.deg y - 1 →
      ((kids st y).eraseIdx k).getD j 0 = (kids st y).getD (if j < k then j else j + 1) 0 := by
    intro j hj
    rcases Nat.lt_or_ge j k with a | a
    · rw [getD_eraseIdx_lt a, if_pos a]
    · rw [getD_eraseIdx_ge a, if_neg (show ¬((j:ℕ) < k) from by omega)]
  intro q j j' hjk hk
  by_cases hqy : q = y
  · rw [hqy] at hk ⊢
    rw [cutState_deg st x y y, if_pos rfl] at hk
    rw [hkeq] at ⊢
    rw [hget j (by omega), hget j' (by omega)]
    have hbd : (if j' < k then j' else j' + 1) < st.deg y := by
      rcases Nat.lt_or_ge j' k with b | b
      · rw [if_pos b]; omega
      · rw [if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
    exact hnd y _ _ (hmono j j' hjk hk) hbd
  · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy]
    rw [cutState_deg st x y q, if_neg hqy] at hk
    exact hnd q j j' hjk hk

/-- `PosOK` survives the cut.  The one-loss rule does the work: `ldeg y` is invariant
(`(deg y - 1) + 1 = deg y + 0`, which needs the parent unmarked), the cut child is off every
list, and every other `ldeg` is untouched. -/
theorem cut_PosOK (st : HState) (x y : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : CutPre st x y) (hpos : PosOK st) : PosOK (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hk2⟩ := kids_cut st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩
  have hlen := length_eraseIdx_lt (by rw [kids_length]; exact hk1)
  have hne : ∀ j : ℕ, j < st.deg y - 1 → (if j < k then j else j + 1) ≠ k := by
    intro j hj
    rcases Nat.lt_or_ge j k with a | a
    · rw [if_pos a]; omega
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
  have hldegy : ldeg (cutState st x y) y = st.deg y := by
    unfold ldeg
    rw [cutState_deg st x y y, if_pos rfl, cutState_mrk_y]
    omega
  intro q j hj
  by_cases hqy : q = y
  · rw [hqy, hk2] at hj ⊢
    rw [length_eraseIdx_lt (by rw [kids_length]; exact hk1), kids_length] at hj
    have hf : ((kids st y).eraseIdx k).getD j 0
        = (st.rgt)^[if j < k then j else j + 1] (st.chd y) := by
      rcases Nat.lt_or_ge j k with a | a
      · rw [getD_eraseIdx_lt a, if_pos a, kids_getD st y j (by omega)]
      · rw [getD_eraseIdx_ge a, if_neg (show ¬((j:ℕ) < k) from by omega),
          kids_getD st y (j + 1) (by omega)]
    rw [hf]
    have hjd2 : (if j < k then j else j + 1) < st.deg y := by
      rcases Nat.lt_or_ge j k with a | a
      · rw [if_pos a]; omega
      · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
    have hold := hpos y _ (by rw [kids_length]; exact hjd2)
    rw [kids_getD st y _ hjd2] at hold
    have hjle : j ≤ (if j < k then j else j + 1) := by
      rcases Nat.lt_or_ge j k with a | a
      · rw [if_pos a]
      · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
    by_cases hvy : (st.rgt)^[if j < k then j else j + 1] (st.chd y) = y
    · rw [hvy, hldegy]; omega
    · by_cases hvx : (st.rgt)^[if j < k then j else j + 1] (st.chd y) = x
      · exfalso
        obtain ⟨hc0, hinj, ht2⟩ := (hrk y).resolve_left (by omega)
        exact hne j hj (hinj _ k hjd2 hk1 (hvx.trans hkx.symm))
      · have hl : ldeg (cutState st x y) ((st.rgt)^[if j < k then j else j + 1] (st.chd y))
            = ldeg st ((st.rgt)^[if j < k then j else j + 1] (st.chd y)) := by
          unfold ldeg
          rw [cutState_deg st x y _, if_neg hvy, cutState_mrk_ne st x y _ hvy]
        rw [hl]
        exact le_trans hjle hold
  · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy] at hj ⊢
    have hvx : (kids st q).getD j 0 ≠ x := by
      intro hc
      have h1 : (kids st q).getD j 0 ∈ kids st q := kids_getD_mem st q j hj
      rw [hc] at h1
      exact hqy ((hpar q _ h1).symm.trans (hpar y x hx))
    by_cases hvy : (kids st q).getD j 0 = y
    · rw [hvy, hldegy]
      have hold := hpos q j hj
      rw [show ldeg st ((kids st q).getD j 0) = st.deg y from by
        rw [hvy]; unfold ldeg; omega] at hold
      exact hold
    · have hl : ldeg (cutState st x y) ((kids st q).getD j 0)
          = ldeg st ((kids st q).getD j 0) := by
        unfold ldeg
        rw [cutState_deg st x y _, if_neg hvy, cutState_mrk_ne st x y _ hvy]
      rw [hl]
      exact hpos q j hj

/-- `SlotOK` survives the cut: `y`'s list only shrinks, every other list is untouched. -/
theorem cut_SlotOK (st : HState) (x y : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : CutPre st x y) (hslot : SlotOK st) : SlotOK (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_cut st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩
  have hn : (cutState st x y).n = st.n := cutState_n st x y
  intro q hq v hv
  rw [hn] at hq ⊢
  by_cases hqy : q = y
  · rw [hqy] at hv
    rw [hkeq] at hv
    exact hslot y hyv v (List.mem_of_mem_eraseIdx hv)
  · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy] at hv
    exact hslot q hq v hv

/-- `Acyc` survives the cut.  The splice's only `par` change is `par x := 0`; a chain that hits
`x` is absorbed at NIL (`NILSelf`), one that misses `x` is an old chain, and either way a
closure forces the node to be `0`. -/
theorem cut_Acyc (st : HState) (x y : ℕ) (hpre : CutPre st x y) (hns : NILSelf st)
    (hac : Acyc st) : Acyc (cutState st x y) := by
  have f0 : (cutState st x y).par 0 = 0 := by
    by_cases h0x : (0:ℕ) = x
    · rw [cutState_par, if_pos h0x]
    · rw [cutState_par, if_neg h0x]
      exact hns
  have fzero : ∀ k : ℕ, (cutState st x y).par^[k] 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, f0]
  intro v j hj heq
  by_cases hhit : ∃ m, m < j ∧ (cutState st x y).par^[m] v = x
  · obtain ⟨m, hmj, hmc⟩ := hhit
    have hstep : (cutState st x y).par^[m + 1] v = 0 := by
      rw [Function.iterate_succ_apply', hmc, cutState_par_x]
    by_cases hjm : j = m + 1
    · rw [hjm] at heq
      rw [hstep] at heq
      exact heq.symm
    · have hj2 : m + 1 ≤ j := by omega
      rw [show j = j - (m + 1) + (m + 1) from by omega, Function.iterate_add_apply, hstep,
        fzero] at heq
      exact heq.symm
  · have hall : ∀ i, i ≤ j → (cutState st x y).par^[i] v = (st.par)^[i] v := by
      intro i hi
      induction i with
      | zero => rfl
      | succ k ih =>
        have hlt : k < j := by omega
        have hikj : k ≤ j := by omega
        have hkne : (st.par)^[k] v ≠ x := by
          intro hc
          rw [← ih hikj] at hc
          exact hhit ⟨k, hlt, hc⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hikj,
          cutState_par_ne st x y _ hkne]
    rw [hall j (le_refl j)] at heq
    exact hac v j hj heq

/-- `NILRoots` survives the cut: the new root `x` has `par x = 0` by the splice, every old
root keeps its `par`. -/
theorem cut_NILRoots (st : HState) (x y : ℕ) (hnrs : NILRoots st) :
    NILRoots (cutState st x y) := by
  intro r hr
  rw [cutState_roots, List.mem_cons] at hr
  rcases hr with hrx | hr
  · rw [hrx, cutState_par_x]
  · by_cases hx2 : x = r
    · rw [← hx2, cutState_par_x]
    · rw [cutState_par_ne st x y r (fun hc => hx2 hc.symm)]
      exact hnrs r hr

/-- `NILSelf` survives the cut: slot 0 is never the cut child written to. -/
theorem cut_NILSelf (st : HState) (x y : ℕ) (hpre : CutPre st x y) (hnc : NILNotChild st)
    (hns : NILSelf st) : NILSelf (cutState st x y) := by
  have hx0 : x ≠ 0 := fun hc => hnc y (hc ▸ hpre.1)
  show (cutState st x y).par 0 = 0
  by_cases h0x : (0:ℕ) = x
  · rw [cutState_par, if_pos h0x]
  · rw [cutState_par, if_neg (show (0:ℕ) ≠ x from fun hc => hx0 hc.symm)]
    exact hns

/-- `NILNotRoot` survives the cut: the new root is `x ≠ 0` (`NILNotChild`), and `0` was not an
old root. -/
theorem cut_NILNotRoot (st : HState) (x y : ℕ) (hpre : CutPre st x y) (hnc : NILNotChild st)
    (hnn : NILNotRoot st) : NILNotRoot (cutState st x y) := by
  have hx0 : x ≠ 0 := fun hc => hnc y (hc ▸ hpre.1)
  intro h
  rw [cutState_roots, List.mem_cons] at h
  rcases h with h | h
  · exact hx0 h.symm
  · exact hnn h

/-- `NILLeaf` survives the cut: `y ≠ 0` (a live node with children cannot be NIL), so slot 0's
degree is untouched. -/
theorem cut_NILLeaf (st : HState) (x y : ℕ) (hpre : CutPre st x y) (hnl : NILLeaf st) :
    NILLeaf (cutState st x y) := by
  have hy0 : y ≠ 0 := by
    intro hc
    rw [hc] at hpre
    have h1 : 0 < (kids st 0).length := List.length_pos_of_mem hpre.1
    have h2 : (kids st 0).length = 0 := by rw [kids_length, hnl]
    omega
  show (cutState st x y).deg 0 = 0
  rw [cutState_deg st x y 0, if_neg (show (0:ℕ) ≠ y from fun hc => hy0 hc.symm), hnl]

/-- `NILNotChild` survives the cut: `y`'s shrunk list is a sublist of the old one, every other
list is untouched, and the cut child is not NIL anyway. -/
theorem cut_NILNotChild (st : HState) (x y : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : CutPre st x y) (hnc : NILNotChild st) : NILNotChild (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_cut st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩
  intro q hv
  by_cases hqy : q = y
  · rw [hqy] at hv
    rw [hkeq] at hv
    exact hnc y (List.mem_of_mem_eraseIdx hv)
  · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy] at hv
    exact hnc q hv

/-- `RootNotChild` survives the cut: the new root `x` sits on no list (`y`'s list lost it, no
other list ever had it), and old roots are children only of NIL. -/
theorem cut_RootNotChild (st : HState) (x y : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : CutPre st x y) (hnd : KidsNodup st y) (hnc : NILNotChild st) (hnl : NILLeaf st)
    (hrnc : RootNotChild st) : RootNotChild (cutState st x y) := by
  have hy0 : y ≠ 0 := by
    intro hc
    rw [hc] at hpre
    have h1 : 0 < (kids st 0).length := List.length_pos_of_mem hpre.1
    have h2 : (kids st 0).length = 0 := by rw [kids_length, hnl]
    omega
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_cut st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩
  intro r hr q hq0 hv
  rw [cutState_roots, List.mem_cons] at hr
  rcases hr with hrx | hr
  · -- the new root `x`
    by_cases hqy : q = y
    · rw [hqy] at hv
      rw [hrx] at hv
      exact cutchild_notin_kids st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩ hnd hv
    · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy] at hv
      rw [hrx] at hv
      exact hqy ((hpar q x hv).symm.trans (hpar y x hx))
  · -- an old root
    by_cases hqy : q = y
    · rw [hqy] at hv
      rw [hkeq] at hv
      exact hrnc r hr y hy0 (List.mem_of_mem_eraseIdx hv)
    · rw [kids_cut_unchanged st x y q hpar ⟨hx, hyv, hm0, hpred, hlftmem⟩ hqy] at hv
      exact hrnc r hr q hq0 hv

/-- `RootsLive` survives the cut: the new root `x` is live (`SlotOK` downwards from the live
parent `y`), and old roots stay live. -/
theorem cut_RootsLive (st : HState) (x y : ℕ) (hrk : RingOK st) (hpre : CutPre st x y)
    (hslot : SlotOK st) (hrl : RootsLive st) : RootsLive (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  have hxv : x < st.n := hslot y hyv x hx
  have hn : (cutState st x y).n = st.n := cutState_n st x y
  intro r hr
  rw [cutState_roots, List.mem_cons] at hr
  rcases hr with hrx | hr
  · rw [hrx, hn]
    exact hxv
  · rw [hn]
    exact hrl r hr

/-- `RingOK` survives the cut.  For `q ≠ y` the walk never touches a rewritten slot (the
rewritten slots — `lft x`, `rgt x` — are children of `y`, and every visited node is a child of
`q`).  For `y` itself the new ring is the old one with position `k` removed: it closes at
period `deg y - 1`, is injective there, and its head's `lft` is its last position. -/
theorem cut_RingOK (st : HState) (x y : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : CutPre st x y) (hnl : NILLeaf st) : RingOK (cutState st x y) := by
  obtain ⟨hx, hyv, hm0, hpred, hlftmem⟩ := hpre
  have hd0 : 0 < st.deg y := by
    have h1 := kids_length st y
    have h2 := List.length_pos_of_mem hx
    omega
  -- stepwise congruence for walks that avoid the one rewritten slot
  have congr : ∀ (f g : ℕ → ℕ) (c s j : ℕ), (∀ v, v ≠ c → f v = g v) →
      (∀ i, i < j → g^[i] s ≠ c) → f^[j] s = g^[j] s := by
    intro f g c s j hstep
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hvs
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih (fun i hi => hvs i (by omega)), hstep _ (hvs j (by omega))]
  intro q
  by_cases hqy : q = y
  · rw [hqy] at ⊢
    by_cases hd1 : st.deg y = 1
    · rw [cutState_deg st x y y, if_pos rfl, hd1]
      exact Or.inl (by omega)
    · have hd2 : 2 ≤ st.deg y := by omega
      obtain ⟨k, hk1, hk2⟩ := exists_pos_of_mem hx
      obtain ⟨hclose, hinj, htail⟩ := (hrk y).resolve_left (by omega)
      have hxchd : k = 0 → st.chd y = x := by
        intro h
        rw [← hk2, h, Function.iterate_zero_apply]
      have hchdx : st.chd y = x → k = 0 := (chdx_iff st x y hrk k ⟨hk1, hk2⟩).mp
      have hchd : (cutState st x y).chd y = if k = 0 then st.rgt x else st.chd y := by
        rw [cutState_chd_ne st x y y hd1, if_pos rfl]
        by_cases hkz : k = 0
        · rw [if_pos (hxchd hkz), if_pos hkz]
        · rw [if_neg (fun hc => hkz (hchdx hc)), if_neg hkz]
      have hd1' : (cutState st x y).deg y ≠ 0 := by
        rw [cutState_deg st x y y, if_pos rfl]; omega
      have hw := walk_cut_pos st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩ hd2 k ⟨hk1, hk2⟩
      have hstep : ∀ v : ℕ, v ≠ st.lft x → (cutState st x y).rgt v = st.rgt v :=
        fun v hv => cutState_rgt_ne st x y v hd1 hv
      have hstepp : (cutState st x y).rgt (st.lft x) = st.rgt x := cutState_rgt_pred st x y hd1
      have hrgtx : st.rgt x = (st.rgt)^[k + 1] (st.chd y) := by
        rw [Function.iterate_succ_apply', hk2]
      have hpp := pred_pos st x y hrk ⟨hx, hyv, hm0, hpred, hlftmem⟩ hd2 k ⟨hk1, hk2⟩
      -- the new walk's jump: at the predecessor, `rgt'` moves to the cut child's successor
      have hjump : k ≠ 0 →
          (cutState st x y).rgt^[k] (st.chd y) = (st.rgt)^[k + 1] (st.chd y) := by
        intro hkz
        have hpre_eq2 : (cutState st x y).rgt^[k - 1] (st.chd y) = st.lft x := by
          have h1 := hw (k - 1) (by omega)
          rw [hchd, if_neg hkz] at h1
          rw [h1, if_pos (show (k:ℕ) - 1 < k from by omega), hpp, if_neg hkz]
        rw [show (k:ℕ) = (k - 1) + 1 from by omega, Function.iterate_succ_apply',
          hpre_eq2, hstepp, hrgtx,
          show (k:ℕ) + 1 = (k - 1) + 1 + 1 from by omega]
      -- the new ring closes at the new period `deg y - 1`
      have hclos : (cutState st x y).rgt^[(st.deg y - 1)] ((cutState st x y).chd y)
          = (cutState st x y).chd y := by
        by_cases hkz : k = 0
        · -- k = 0: the new walk runs unchanged to the old tail, then jumps back to the new head
          have hxh : st.chd y = x := hxchd hkz
          have hrx1 : st.rgt x = (st.rgt)^[1] (st.chd y) := by
            rw [hrgtx, hkz, show (0:ℕ) + 1 = 1 from by omega]
          have hstep1 : (cutState st x y).rgt^[(st.deg y - 1 - 1)] (st.rgt x) = st.lft x := by
            have hc2 : (cutState st x y).rgt^[(st.deg y - 1 - 1)] (st.rgt x)
                = (st.rgt)^[(st.deg y - 1 - 1)] (st.rgt x) := by
              refine congr _ _ _ _ _ hstep (fun m hm hc => ?_)
              rw [hrx1, ← Function.iterate_add_apply] at hc
              rw [hpp, if_pos hkz] at hc
              have h5 := hinj (m + 1) (st.deg y - 1)
                (by have := kids_length st y; omega) (by omega) hc
              omega
            rw [hc2, hrx1, ← Function.iterate_add_apply,
              show (st.deg y - 1 - 1) + 1 = st.deg y - 1 from by omega, ← htail, hxh]
          rw [hchd, if_pos hkz,
            show (st.deg y - 1) = (st.deg y - 1 - 1) + 1 from by omega,
            Function.iterate_succ_apply', hstep1, hstepp]
        · rcases Nat.lt_or_ge k (st.deg y - 1) with hki | hkd
          · -- 1 ≤ k ≤ deg y - 2: jump at the predecessor (step `k`), then unchanged to the head
            rw [hchd, if_neg (show ¬(k:ℕ) = 0 from by omega),
              show (st.deg y - 1) = (st.deg y - 1 - k) + k from by omega,
              Function.iterate_add_apply, hjump (by omega)]
            have hc3 : (cutState st x y).rgt^[(st.deg y - 1 - k)] ((st.rgt)^[k + 1] (st.chd y))
                = (st.rgt)^[(st.deg y - 1 - k)] ((st.rgt)^[k + 1] (st.chd y)) := by
              refine congr _ _ _ _ _ hstep (fun m hm hc => ?_)
              rw [hpp, if_neg (show ¬(k:ℕ) = 0 from by omega),
                ← Function.iterate_add_apply] at hc
              have h5 := hinj (m + (k + 1)) (k - 1)
                (by have := kids_length st y; omega) (by omega) hc
              omega
            rw [hc3, ← Function.iterate_add_apply,
              show (st.deg y - 1 - k) + (k + 1) = st.deg y from by omega]
            exact hclose
          · -- k = deg y - 1: the walk reaches the old tail (the cut child) and jumps to the head
            have hkde : k = st.deg y - 1 := by omega
            have hpre_eq2 : (cutState st x y).rgt^[k - 1] (st.chd y) = st.lft x := by
              have h1 := hw (k - 1) (by omega)
              rw [hchd, if_neg (show ¬(k:ℕ) = 0 from by omega)] at h1
              rw [h1, if_pos (show (k:ℕ) - 1 < k from by omega), hpp,
                if_neg (show ¬(k:ℕ) = 0 from by omega)]
            rw [hchd, if_neg (show ¬(k:ℕ) = 0 from by omega),
              show (st.deg y - 1) = (k - 1) + 1 from by omega,
              Function.iterate_succ_apply', hpre_eq2, hstepp, hrgtx,
              show (k:ℕ) + 1 = st.deg y from by omega, hclose]
      have hclos' : (cutState st x y).rgt^[(cutState st x y).deg y]
          ((cutState st x y).chd y) = (cutState st x y).chd y := by
        rw [cutState_deg st x y y, if_pos rfl]
        exact hclos
      refine Or.inr ⟨hclos', ?_, ?_⟩
      -- injectivity of the new walk: the position map is strictly increasing
      · intro j j' hj hj' heq
        rw [cutState_deg st x y y, if_pos rfl] at hj hj'
        rw [hw j hj, hw j' hj'] at heq
        have hfinj : ∀ a b : ℕ, a < st.deg y - 1 → b < st.deg y - 1 →
            (if a < k then a else a + 1) = (if b < k then b else b + 1) → a = b := by
          intro a b ha hb heq2
          rcases Nat.lt_or_ge a k with a1 | a1 <;> rcases Nat.lt_or_ge b k with b1 | b1
          · rw [if_pos a1, if_pos b1] at heq2; exact heq2
          · rw [if_pos a1, if_neg (show ¬((b:ℕ) < k) from by omega)] at heq2; omega
          · rw [if_neg (show ¬((a:ℕ) < k) from by omega), if_pos b1] at heq2; omega
          · rw [if_neg (show ¬((a:ℕ) < k) from by omega),
              if_neg (show ¬((b:ℕ) < k) from by omega)] at heq2; omega
        have hf1 : (if j < k then j else j + 1) < st.deg y := by
          rcases Nat.lt_or_ge j k with a | a
          · rw [if_pos a]; omega
          · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
        have hf2 : (if j' < k then j' else j' + 1) < st.deg y := by
          rcases Nat.lt_or_ge j' k with a | a
          · rw [if_pos a]; omega
          · rw [if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
        have hf := hinj _ _ hf1 hf2 heq
        exact hfinj j j' hj hj' hf
      -- `lft` of the new head is the last position of the new walk
      · have hwb : st.deg y - 1 - 1 < st.deg y - 1 := by omega
        rw [cutState_deg st x y y, if_pos rfl, hw (st.deg y - 1 - 1) hwb, hchd]
        by_cases hkz : k = 0
        · -- k = 0: the new head is the cut child's successor; the splice set its `lft`
          rw [if_pos hkz, cutState_lft_succ st x y hd1,
            if_neg (show ¬((st.deg y - 1 - 1:ℕ) < k) from by omega),
            show (st.deg y - 1 - 1) + 1 = st.deg y - 1 from by omega,
            hpp, if_pos hkz]
        · rcases Nat.lt_or_ge k (st.deg y - 1) with hkl | hkd
          · -- 1 ≤ k ≤ deg y - 2: the new head is the old head; its `lft` is untouched
            have hk1d : k + 1 < st.deg y := by omega
            have hchd_ne : st.chd y ≠ st.rgt x := by
              intro hc
              have hz : (st.rgt)^[0] (st.chd y) = (st.rgt)^[k + 1] (st.chd y) := by
                rw [Function.iterate_zero_apply, ← hrgtx]; exact hc
              have h5 := hinj (k + 1) 0 hk1d hd0 hz.symm
              have h6 : ¬((k:ℕ) + 1 = 0) := by simp
              exact absurd h5 h6
            rw [if_neg hkz, if_neg (show ¬((st.deg y - 1 - 1:ℕ) < k) from by omega),
              cutState_lft_ne st x y (st.chd y) hd1 hchd_ne, htail,
              show (st.deg y - 1 - 1) + 1 = st.deg y - 1 from by omega]
          · -- k = deg y - 1: the cut child was the tail; the new head is its successor
            have hkde : k = st.deg y - 1 := by omega
            have heq : st.chd y = st.rgt x := by
              rw [hrgtx, hkde, show (st.deg y - 1) + 1 = st.deg y from by omega, hclose]
            rw [if_neg (show ¬(k:ℕ) = 0 from by omega),
              if_pos (show (st.deg y - 1 - 1:ℕ) < k from by omega), heq,
              cutState_lft_succ st x y hd1, hpp, if_neg (show ¬(k:ℕ) = 0 from by omega),
              hkde, ← heq]
  · by_cases hdq : (cutState st x y).deg q = 0
    · exact Or.inl hdq
    · right
      have hdq' : st.deg q ≠ 0 := by
        rw [cutState_deg st x y q, if_neg hqy] at hdq; exact hdq
      have hmem : ∀ j, j < st.deg q → (st.rgt)^[j] (st.chd q) ∈ kids st q := by
        intro j hj
        rw [kids]
        exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
      by_cases hdy1 : st.deg y = 1
      · -- the degree-1 splice does not touch `q`'s fields at all
        have hchdq : (cutState st x y).chd q = st.chd q := by
          simp [cutState, hdy1, hqy]
        have hf : (cutState st x y).rgt = st.rgt := by
          funext v; exact cutState_rgt_eq st x y v hdy1
        have hff : (cutState st x y).lft = st.lft := by
          funext v; exact cutState_lft_eq st x y v hdy1
        refine ⟨?_, ?_, ?_⟩
        · rw [cutState_deg st x y q, if_neg hqy, hchdq, hf]
          exact ((hrk q).resolve_left hdq').1
        · intro j j' hj hj' heq
          rw [cutState_deg st x y q, if_neg hqy] at hj hj'
          rw [hchdq, hf] at heq
          exact ((hrk q).resolve_left hdq').2.1 j j' hj hj' heq
        · rw [cutState_deg st x y q, if_neg hqy, hchdq, hf, hff]
          exact ((hrk q).resolve_left hdq').2.2
      · have hd2 : 2 ≤ st.deg y := by omega
        have hd1 : st.deg y ≠ 1 := by omega
        obtain ⟨k, hk1, hk2⟩ := exists_pos_of_mem hx
        obtain ⟨hclose, hinj, htail⟩ := (hrk y).resolve_left (by omega)
        have hmemY : ∀ j, j < st.deg y → (st.rgt)^[j] (st.chd y) ∈ kids st y := by
          intro j hj
          rw [kids]
          exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
        have hly : st.lft x ∈ kids st y := hlftmem hd2
        have hrgtx : st.rgt x = (st.rgt)^[k + 1] (st.chd y) := by
          rw [Function.iterate_succ_apply', hk2]
        have hrgxy : st.rgt x ∈ kids st y := by
          rw [hrgtx]
          rcases Nat.lt_or_ge (k + 1) (st.deg y) with hlt | hge
          · exact hmemY (k + 1) hlt
          · have hk1' : (k + 1 : ℕ) = st.deg y := by omega
            rw [hk1', hclose]
            exact hmemY 0 (by omega)
        have hchdq : (cutState st x y).chd q = st.chd q := by
          rw [cutState_chd_ne st x y q hd1, if_neg hqy]
        have hvs : ∀ i, i < st.deg q →
            (st.rgt)^[i] ((cutState st x y).chd q) ≠ st.lft x := by
          intro i hi hc
          rw [hchdq] at hc
          have hm : (st.rgt)^[i] (st.chd q) ∈ kids st q := hmem i hi
          rw [hc] at hm
          exact hqy ((hpar q _ hm).symm.trans (hpar y _ hly))
        have hw2 : ∀ j, j < st.deg q →
            (cutState st x y).rgt^[j] ((cutState st x y).chd q) = (st.rgt)^[j] (st.chd q) := by
          intro j hj
          rw [hchdq]
          refine congr (cutState st x y).rgt st.rgt (st.lft x) (st.chd q) j
            (fun v hv => cutState_rgt_ne st x y v hd1 hv) ?_
          intro i hi
          rw [← hchdq]
          exact hvs i (by omega)
        refine ⟨?_, ?_, ?_⟩
        · have hdq1 : (cutState st x y).deg q = (st.deg q - 1) + 1 := by
            rw [cutState_deg st x y q, if_neg hqy]
            omega
          rw [hdq1, Function.iterate_succ_apply', hw2 (st.deg q - 1) (by omega), hchdq]
          have hvne : (st.rgt)^[st.deg q - 1] (st.chd q) ≠ st.lft x := by
            intro hc
            rw [← hchdq] at hc
            exact hvs _ (by omega) hc
          have hfin_eq : (st.rgt)^[st.deg q] (st.chd q)
              = (st.rgt)^[st.deg q - 1 + 1] (st.chd q) := by
            rw [show st.deg q - 1 + 1 = st.deg q from by omega]
          rw [cutState_rgt_ne st x y _ hd1 hvne]
          have hfin : st.rgt ((st.rgt)^[st.deg q - 1] (st.chd q))
              = (st.rgt)^[st.deg q] (st.chd q) := by
            rw [hfin_eq]
            exact (Function.iterate_succ_apply' st.rgt (st.deg q - 1) (st.chd q)).symm
          rw [hfin]
          exact ((hrk q).resolve_left hdq').1
        · intro j j' hj hj' heq
          rw [cutState_deg st x y q, if_neg hqy] at hj hj'
          rw [hw2 j hj, hw2 j' hj'] at heq
          obtain ⟨hc2, hij2, ht3⟩ := (hrk q).resolve_left hdq'
          exact hij2 j j' hj hj' heq
        · rw [cutState_deg st x y q, if_neg hqy]
          rw [hw2 (st.deg q - 1) (by omega)]
          -- `chd q ≠ rgt x` (their parents differ), so `lft` is untouched at the new head
          have hchdq' : (cutState st x y).chd q ≠ st.rgt x := by
            intro hc
            have h0m : st.chd q ∈ kids st q := by
              have hm0' := hmem 0 (by have := kids_length st q; omega)
              rwa [Function.iterate_zero_apply] at hm0'
            have hp1 : st.par (st.chd q) = q := hpar q _ h0m
            have hp2 : st.par (st.rgt x) = y := hpar y _ hrgxy
            rw [← hchdq, hc] at hp1
            exact hqy (hp1.symm.trans hp2)
          rw [cutState_lft_ne st x y _ hd1 hchdq', hchdq]
          exact (hrk q).resolve_left hdq' |>.2.2

/-! ## The cut-output witness -/

/-- The cut-output witness's pre-state: the link witness's output `linked` — slot 1 a root of
degree 1 whose single child is slot 2. -/
def cutPreSt : HState := linked

/-- The cut output: the child `2` is cut back off slot `1` and re-rooted; slot `1` is marked. -/
def cutted : HState := cutState linked 2 1

/-- The witness pre-state really is a legal cut pre-state. -/
theorem cutPreSt_ok : CutPre linked 2 1 := by
  have hn : 1 < linked.n := by simp
  have hm : linked.mrk 1 = 0 := by simp
  have hlf : linked.rgt (linked.lft 2) = 2 := by simp
  refine ⟨?_, hn, hm, hlf, ?_⟩
  · rw [kids_linked, if_pos rfl]; simp
  · intro h
    simp [linked_deg] at h

@[simp] theorem cutted_par (v : ℕ) : cutted.par v = 0 := by
  by_cases h : v = 2 <;> simp [cutted, cutState, h]

@[simp] theorem cutted_mrk (v : ℕ) : cutted.mrk v = if v = 1 then 1 else 0 := by
  by_cases h : v = 1 <;> simp [cutted, cutState, h]

@[simp] theorem cutted_deg (v : ℕ) : cutted.deg v = 0 := by
  by_cases h : v = 1 <;> simp [cutted, cutState, h]

@[simp] theorem cutted_chd (v : ℕ) : cutted.chd v = 0 := by
  by_cases h : v = 1 <;> simp [cutted, cutState, h]

@[simp] theorem cutted_rgt (v : ℕ) : cutted.rgt v = if v = 2 then 2 else 0 := by
  simp [cutted, cutState]

@[simp] theorem cutted_lft (v : ℕ) : cutted.lft v = if v = 2 then 2 else 0 := by
  simp [cutted, cutState]

@[simp] theorem cutted_roots : cutted.roots = [2, 1] := rfl

@[simp] theorem cutted_n : cutted.n = 3 := rfl

@[simp] theorem kids_cutted (q : ℕ) : kids cutted q = [] := by
  unfold kids
  simp

theorem cutted_ParOK : ParOK cutted := by
  intro q v hv
  rw [kids_cutted] at hv
  exact absurd hv (by simp)

theorem cutted_SlotOK : SlotOK cutted := by
  intro q hq v hv
  rw [kids_cutted] at hv
  exact absurd hv (by simp)

theorem cutted_ParSlot : ParSlot cutted := by
  intro q _
  simp

theorem cutted_KidsNodup : ∀ q, KidsNodup cutted q := by
  intro q j k _ hk
  rw [cutted_deg] at hk
  omega

theorem cutted_NILRoots : NILRoots cutted := by
  intro r hr
  rw [cutted_roots, List.mem_cons] at hr
  rcases hr with h2 | hr
  · rw [h2]; simp
  · simp only [List.mem_singleton] at hr
    rw [hr]; simp

theorem cutted_NILSelf : NILSelf cutted := by
  show cutted.par 0 = 0
  simp

theorem cutted_NILNotChild : NILNotChild cutted := by
  intro q hv
  rw [kids_cutted] at hv
  exact absurd hv (by simp)

theorem cutted_RootNotChild : RootNotChild cutted := by
  intro r hr q _ hv
  rw [cutted_roots, List.mem_cons] at hr
  rw [kids_cutted] at hv
  simp at hr hv

theorem cutted_RootsLive : RootsLive cutted := by
  intro r hr
  rw [cutted_roots, List.mem_cons] at hr
  rcases hr with h2 | hr
  · rw [h2, cutted_n]; omega
  · simp only [List.mem_singleton] at hr
    rw [hr, cutted_n]; omega

theorem cutted_NILNotRoot : NILNotRoot cutted := by
  intro h
  rw [cutted_roots, List.mem_cons] at h
  rcases h with h | h
  · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem cutted_NILLeaf : NILLeaf cutted := by
  show cutted.deg 0 = 0
  simp

theorem cutted_MarkOK : MarkOK cutted := by
  intro q
  rw [cutted_mrk]
  by_cases h : q = 1 <;> simp [h]

theorem cutted_PosOK : PosOK cutted := by
  intro q j hj
  rw [kids_cutted] at hj
  simp at hj

theorem cutted_Acyc : Acyc cutted := by
  intro v j hj heq
  have hall : ∀ m : ℕ, (cutted.par)^[m + 1] v = 0 := by
    intro m
    rw [Function.iterate_succ_apply', cutted_par]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · omega
  · rw [show j = (j - 1) + 1 from by omega, hall (j - 1)] at heq
    exact heq.symm

theorem cutted_RingOK : RingOK cutted := by
  intro q
  rw [cutted_deg]
  exact Or.inl rfl

/-- The cut witness satisfies the support condition at every slot (all its child lists are
empty, so every abstraction is a single bare node). -/
theorem cutted_Support (p : ℕ) (hp3 : p < cutted.n) : Support cutted (cutted.n + 1) p := by
  refine ⟨{p}, ?_, ?_⟩
  · have hshape : treeOf cutted (cutted.n + 1) p = FibHeapForest.Tree.node p [] := by
      simp [treeOf, kids_cutted]
    rw [hshape, FibHeapForest.size_node]
    simp [FibHeapForest.sizeSum]
  · intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    rw [cutted_n]
    exact hp3

/-- **The capstone applied to the post-cut state.**  The cut transition keeps the machine
inside the invariant set, so the rank cap applies to a freshly cut root: the arc's next step is
not vacuous. -/
theorem cutted_capstone (p : ℕ) (hpv : p < cutted.n) (hp0 : p ≠ 0) :
    cutted.deg p ≤ FibHeapAccounting.rankCap cutted.n :=
  degree_le_rankCap_zero cutted cutted_ParOK cutted_SlotOK cutted_ParSlot cutted_KidsNodup
    cutted_Acyc cutted_NILSelf cutted_NILLeaf cutted_NILNotChild cutted_MarkOK cutted_PosOK
    hpv hp0 (cutted_Support p hpv)

end Submission.FibHeapCut
