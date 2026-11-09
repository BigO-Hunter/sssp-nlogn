import Submission.FibHeapCut

/-!
# M3c: the promote updater — the cascade's marked-parent cut

`promoteState st y z` is the exact array splice of the CLRS cascading-cut step that M3a's
`cutState` cannot express: the child `y` is *marked* (`mrk y = 1` — it already lost a child
once), so instead of marking `z` again, `y` itself is cut from `z`'s circular child list and
re-rooted (`par y := 0`, prepended to the root list), `y`'s mark is *cleared* (`mrk y := 0` —
the one loss is spent), and the unmarked parent is marked (`mrk z := 1`, `deg z := deg z - 1`).
Two splices, one per shape of the target list:

* `deg z = 1` — `y` was the only child: `chd z := 0`, `deg z := 0`; no ring writes.
* `deg z ≥ 2` — the standard removal: `rgt (lft y) := rgt y`, `lft (rgt y) := lft y`,
  `chd z := rgt y` when `y` was the head.  The walk from the head then reads the old children
  in link order with exactly the position-`k` element skipped — `(kids st z).eraseIdx k` —
  which is what `pos_cut` (proved at list level in `FibHeapRefine`) consumes.

The two mark writes together keep `ldeg z = deg z + mrk z` invariant (`(deg z - 1) + 1 =
deg z + 0`) — the one-loss rule paying for the cut, exactly as in `cutState`; the promoted
child `y` sits on no list afterwards (`RootNotChild`), so its own link-degree drop is
unconstrained.  This is the machine counterpart of the abstract cascade's marked-head case
(`cascadeCut` in `FibHeapDynamic`: a marked entry is discarded to the cut roots and the
cascade continues above it); the unmarked-stop case is `cutState` itself.

## The honest extra premises

`RingOK` pins `lft` only at the *head* of a ring (`lft (chd p) = walk position deg p - 1`);
at an interior node `lft` is unconstrained, so the splice's neighbour write cannot be proved
correct from `RingOK` alone.  `PromotePre` therefore carries the two facts the splice needs, both
true of every real ring: `st.rgt (st.lft y) = y` (`lft y` is a predecessor of `y`) and, when
`deg z ≥ 2`, `st.lft y ∈ kids st z` (so ring injectivity pins the predecessor position).
It also carries both mark facts — `st.mrk y = 1` (there is a loss to spend; without it the
splice would be inventing a second loss, violating `MarkOK`) and `st.mrk z = 0` (the
degree decrement has a mark to collect; without it `ldeg z` would drop and break `PosOK`
at `z`'s own position, which is the case the cascade's *next* promote handles).

## What lands here

The re-root walk (`kids_promote` — the `List.ext_get`-pointwise treatment, `kids_length`
pre-normalised before `omega`), the untouched-list lemma for every `q ≠ z`
(`kids_promote_unchanged`, the `kids_unchanged` machinery consumed the way the link discharges
consumed it), and the invariant bundle: `MarkOK`, `ParSlot`, `ParOK`, `KidsNodup`, `PosOK`,
`SlotOK`, `Acyc`, `NILRoots`, `NILSelf`, `NILNotRoot`, `NILLeaf`, `NILNotChild`,
`RootNotChild`, `RootsLive`, and `RingOK` — the walk machinery the *next* updater in the arc
will consume.  The promote-output witness (`promoted`: the marked child of a one-child root,
cut back off and unmarked) re-proves the whole bundle, so the capstone applies to a
post-promote state: the invariant set has a model after the transition.

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapPromote

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink Submission.FibHeapLinkWalk

/-! ## The cut splice -/

/-- Preconditions of a promote: `y` is a *marked* child of the live *unmarked* node `z`,
and `lft y` is a predecessor of `y` (true of every real ring; `RingOK` pins `lft` only at
ring heads, so the splice's neighbour write needs this stated).  The two mark premises are
the CLRS cascade in machine arithmetic: `y`'s mark is *spent* (`mrk y := 0` — this step
exists precisely because `y` already lost a child once), and `z`'s is set (`mrk z := 1`),
which keeps `ldeg z = deg z + mrk z` invariant across the degree decrement — the one-loss
rule paying for the cut, as in `cutState`. -/
def PromotePre (st : HState) (y z : ℕ) : Prop :=
  y ∈ kids st z ∧ z < st.n ∧ st.mrk y = 1 ∧ st.mrk z = 0
    ∧ st.rgt (st.lft y) = y ∧ (2 ≤ st.deg z → st.lft y ∈ kids st z)

/-- The promote splice.  Both branches write only to already-live slots.  The mark write
checks `z` first: `mrk z := 1` is unconditional in the pointwise reading (`z ≠ z` is
false), and the promoted child's cleared mark needs `y ≠ z` — true of any real state
(`Acyc` forbids a self-parent). -/
def promoteState (st : HState) (y z : ℕ) : HState :=
  if st.deg z = 1 then
    { st with
      par := (fun i => if i = y then 0 else st.par i)
      mrk := (fun i => if i = z then 1 else if i = y then 0 else st.mrk i)
      deg := (fun i => if i = z then st.deg i - 1 else st.deg i)
      chd := (fun i => if i = z then 0 else st.chd i)
      roots := y :: st.roots }
  else
    { st with
      par := (fun i => if i = y then 0 else st.par i)
      mrk := (fun i => if i = z then 1 else if i = y then 0 else st.mrk i)
      deg := (fun i => if i = z then st.deg i - 1 else st.deg i)
      chd := (fun i => if i = z then if st.chd z = y then st.rgt y else st.chd i else st.chd i)
      rgt := (fun i => if i = st.lft y then st.rgt y else st.rgt i)
      lft := (fun i => if i = st.rgt y then st.lft y else st.lft i)
      roots := y :: st.roots }

/-! ## Pointwise behaviour of the splice -/

theorem promoteState_deg (st : HState) (y z q : ℕ) :
    (promoteState st y z).deg q = if q = z then st.deg q - 1 else st.deg q := by
  unfold promoteState
  by_cases h : st.deg z = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem promoteState_mrk (st : HState) (y z q : ℕ) :
    (promoteState st y z).mrk q =
      if q = z then 1 else if q = y then 0 else st.mrk q := by
  unfold promoteState
  by_cases h : st.deg z = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem promoteState_par (st : HState) (y z q : ℕ) :
    (promoteState st y z).par q = if q = y then 0 else st.par q := by
  unfold promoteState
  by_cases h : st.deg z = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem promoteState_roots (st : HState) (y z : ℕ) :
    (promoteState st y z).roots = y :: st.roots := by
  unfold promoteState
  by_cases h : st.deg z = 1
  · simp [h]
  · simp [h]

theorem promoteState_n (st : HState) (y z : ℕ) : (promoteState st y z).n = st.n := by
  unfold promoteState
  by_cases h : st.deg z = 1
  · simp [h]
  · simp [h]

theorem promoteState_par_y (st : HState) (y z : ℕ) : (promoteState st y z).par y = 0 := by
  rw [promoteState_par, if_pos rfl]

theorem promoteState_par_ne (st : HState) (y z q : ℕ) (hne : q ≠ y) :
    (promoteState st y z).par q = st.par q := by
  rw [promoteState_par, if_neg hne]

theorem promoteState_mrk_z (st : HState) (y z : ℕ) : (promoteState st y z).mrk z = 1 := by
  rw [promoteState_mrk, if_pos rfl]

theorem promoteState_mrk_y (st : HState) (y z : ℕ) (hyz : y ≠ z) :
    (promoteState st y z).mrk y = 0 := by
  rw [promoteState_mrk, if_neg hyz, if_pos rfl]

theorem promoteState_mrk_ne (st : HState) (y z q : ℕ) (hqz : q ≠ z) (hqy : q ≠ y) :
    (promoteState st y z).mrk q = st.mrk q := by
  rw [promoteState_mrk, if_neg hqz, if_neg hqy]

theorem promoteState_chd_zero (st : HState) (y z : ℕ) (h : st.deg z = 1) :
    (promoteState st y z).chd z = 0 := by
  simp [promoteState, h]

theorem promoteState_rgt_eq (st : HState) (y z v : ℕ) (h : st.deg z = 1) :
    (promoteState st y z).rgt v = st.rgt v := by
  simp [promoteState, h]

theorem promoteState_lft_eq (st : HState) (y z v : ℕ) (h : st.deg z = 1) :
    (promoteState st y z).lft v = st.lft v := by
  simp [promoteState, h]

theorem promoteState_chd_ne (st : HState) (y z q : ℕ) (h : st.deg z ≠ 1) :
    (promoteState st y z).chd q =
      if q = z then (if st.chd z = y then st.rgt y else st.chd z) else st.chd q := by
  by_cases hq : q = z
  · simp [promoteState, h, hq]
  · simp [promoteState, h, hq]

theorem promoteState_rgt_ne (st : HState) (y z v : ℕ) (h : st.deg z ≠ 1) (hv : v ≠ st.lft y) :
    (promoteState st y z).rgt v = st.rgt v := by
  simp [promoteState, h, hv]

theorem promoteState_rgt_pred (st : HState) (y z : ℕ) (h : st.deg z ≠ 1) :
    (promoteState st y z).rgt (st.lft y) = st.rgt y := by
  simp [promoteState, h]

theorem promoteState_lft_ne (st : HState) (y z v : ℕ) (h : st.deg z ≠ 1) (hv : v ≠ st.rgt y) :
    (promoteState st y z).lft v = st.lft v := by
  simp [promoteState, h, hv]

theorem promoteState_lft_succ (st : HState) (y z : ℕ) (h : st.deg z ≠ 1) :
    (promoteState st y z).lft (st.rgt y) = st.lft y := by
  simp [promoteState, h]

/-! ## Positions in the ring -/

/-- A child sits at some walk position. -/
theorem exists_pos_of_mem {st : HState} {y z : ℕ} (hx : y ∈ kids st z) :
    ∃ k, k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y := by
  rw [kids, List.mem_ofFn] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨j.val, j.isLt, hj⟩

/-- `getD` into a child list is the walk value. -/
theorem kids_getD (st : HState) (z m : ℕ) (hm : m < st.deg z) :
    (kids st z).getD m 0 = (st.rgt)^[m] (st.chd z) := by
  have hs : (List.ofFn fun i : Fin (st.deg z) => (st.rgt)^[i.val] (st.chd z))[m]?
      = some ((st.rgt)^[m] (st.chd z)) := by
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

/-- `k = 0` and `chd z = y` are interchangeable for the cut child at position `k`. -/
theorem chdy_iff (st : HState) (y z : ℕ) (hrk : RingOK st) (k : ℕ)
    (hk : k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y) :
    (st.chd z = y ↔ k = 0) := by
  obtain ⟨hclose, hinj, htail⟩ := (hrk z).resolve_left (by omega)
  constructor
  · intro hc
    have h0 : (st.rgt)^[0] (st.chd z) = (st.rgt)^[k] (st.chd z) := by
      rw [Function.iterate_zero, hk.2]; exact hc
    exact (hinj 0 k (by omega) hk.1 h0).symm
  · intro h
    rw [← hk.2, h, Function.iterate_zero_apply]

/-! ## The re-root walk -/

/-- The predecessor position: `lft y` sits immediately before `y` in the ring — position
`deg z - 1` when `y` is the head, `k - 1` at interior position `k`.  (`RingOK` alone pins
`lft` only at the head; the premise `st.rgt (st.lft y) = y` from `PromotePre` plus ring
injectivity pins it everywhere.) -/
theorem pred_pos (st : HState) (y z : ℕ) (hrk : RingOK st) (hpre : PromotePre st y z)
    (hd2 : 2 ≤ st.deg z) (k : ℕ) (hk : k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y) :
    st.lft y = (st.rgt)^[if k = 0 then st.deg z - 1 else k - 1] (st.chd z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨hclose, hinj, htail⟩ := (hrk z).resolve_left (by omega)
  have hxchd : k = 0 → st.chd z = y := by
    intro h
    rw [← hk.2, h, Function.iterate_zero_apply]
  by_cases hkz : k = 0
  · have hxc : st.chd z = y := hxchd hkz
    have hlx : st.lft y = st.lft (st.chd z) := by rw [hxc]
    rw [if_pos hkz, hlx]
    exact htail
  · obtain ⟨j, hjd, hjval⟩ := exists_pos_of_mem (hlftmem hd2)
    have hstep : (st.rgt)^[j + 1] (st.chd z) = (st.rgt)^[k] (st.chd z) := by
      rw [Function.iterate_succ_apply', hjval, hpred, hk.2]
    rcases Nat.lt_or_ge (j + 1) (st.deg z) with hlt | hge
    · have hje : j + 1 = k := hinj (j + 1) k hlt hk.1 hstep
      rw [if_neg hkz, ← hjval, show k - 1 = j from by omega]
    · have hjd' : j + 1 = st.deg z := by omega
      rw [hjd'] at hstep
      rw [hclose] at hstep
      have h0 : (st.rgt)^[0] (st.chd z) = (st.rgt)^[k] (st.chd z) := by
        rw [Function.iterate_zero]; exact hstep
      exact absurd (hinj 0 k (by omega) hk.1 h0) (by omega)

/-- **The re-root walk, positive-degree branch.**  After the cut, position `j` of `z`'s child
walk reads old position `j` for `j < k` and old position `j + 1` for `j ≥ k` — the child at
position `k` (the cut child `y`) is skipped. -/
theorem walk_promote_pos (st : HState) (y z : ℕ) (hrk : RingOK st) (hpre : PromotePre st y z)
    (hd2 : 2 ≤ st.deg z) (k : ℕ) (hk : k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y) :
    ∀ j : ℕ, j < st.deg z - 1 →
      (promoteState st y z).rgt^[j] ((promoteState st y z).chd z) =
        (st.rgt)^[if j < k then j else j + 1] (st.chd z) := by
  have hpredpos := pred_pos st y z hrk hpre hd2 k hk
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  have hd1 : st.deg z ≠ 1 := by omega
  obtain ⟨hclose, hinj, htail⟩ := (hrk z).resolve_left (by omega)
  have hxchd : k = 0 → st.chd z = y := by
    intro h
    rw [← hk.2, h, Function.iterate_zero_apply]
  have hchdx : st.chd z = y → k = 0 := by
    intro hc
    have h0 : (st.rgt)^[0] (st.chd z) = (st.rgt)^[k] (st.chd z) := by
      rw [Function.iterate_zero, hk.2]; exact hc
    exact (hinj 0 k (by omega) hk.1 h0).symm
  -- The new head.
  have hchd : (promoteState st y z).chd z = if k = 0 then st.rgt y else st.chd z := by
    rw [promoteState_chd_ne st y z z hd1, if_pos rfl]
    by_cases hkz : k = 0
    · rw [if_pos (hxchd hkz), if_pos hkz]
    · rw [if_neg (fun hc => hkz (hchdx hc)), if_neg hkz]
  -- The splice's `rgt` behaviour.
  have hstep : ∀ v : ℕ, v ≠ st.lft y → (promoteState st y z).rgt v = st.rgt v :=
    fun v hv => promoteState_rgt_ne st y z v hd1 hv
  have hstepp : (promoteState st y z).rgt (st.lft y) = st.rgt y := promoteState_rgt_pred st y z hd1
  have hrgtx : st.rgt y = (st.rgt)^[k + 1] (st.chd z) := by
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
    have hjlt : j < st.deg z - 1 := by omega
    rw [Function.iterate_succ_apply', ih hjlt]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [if_pos hjk]
      by_cases hjk1 : j + 1 = k
      · -- the transition: position `j = k - 1` is `lft y`
        have hk1 : 0 < k := by omega
        have hposj : (st.rgt)^[j] (st.chd z) = st.lft y := by
          rw [hpredpos, if_neg (show ¬(k:ℕ) = 0 from by omega), show k - 1 = j from by omega]
        rw [hposj, hstepp, hrgtx, if_neg (show ¬((j:ℕ) + 1) < k from by omega), hjk1]
      · -- strictly before the predecessor: the walk is untouched
        have hne : (st.rgt)^[j] (st.chd z) ≠ st.lft y := by
          intro hc
          rw [hpredpos, if_neg (show ¬(k:ℕ) = 0 from by omega)] at hc
          exact absurd (hinj j (k - 1) (by omega) (by omega) hc) (by omega)
        rw [hstep _ hne, if_pos (show (j:ℕ) + 1 < k from by omega)]
        exact (Function.iterate_succ_apply' st.rgt j (st.chd z)).symm
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]
      -- position `j + 1 ≤ deg z - 2` is neither the predecessor nor the tail
      have hne : (st.rgt)^[j + 1] (st.chd z) ≠ st.lft y := by
        intro hc
        rw [hpredpos] at hc
        by_cases hkz : k = 0
        · rw [if_pos hkz] at hc
          exact absurd (hinj (j + 1) (st.deg z - 1) (by omega) (by omega) hc) (by omega)
        · rw [if_neg hkz] at hc
          exact absurd (hinj (j + 1) (k - 1) (by omega) (by omega) hc) (by omega)
      rw [hstep _ hne, if_neg (show ¬((j:ℕ) + 1) < k from by omega)]
      exact (Function.iterate_succ_apply' st.rgt (j + 1) (st.chd z)).symm

/-- **The re-root walk, empty branch.**  Cutting the only child empties the list. -/
theorem kids_promote_zero (st : HState) (y z k : ℕ) (hpre : PromotePre st y z)
    (hd : st.deg z = 1) (hk : k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y) :
    kids (promoteState st y z) z = (kids st z).eraseIdx k := by
  have hk0 : k = 0 := by omega
  subst hk0
  unfold kids
  have hx : st.chd z = y := by rw [← hk.2, Function.iterate_zero_apply]
  rw [promoteState_deg st y z z, if_pos rfl, hd, promoteState_chd_zero st y z hd]
  simp [hx]

/-- **The re-root walk, positive-degree branch, as a list equation.** -/
theorem kids_promote_pos (st : HState) (y z k : ℕ) (hrk : RingOK st) (hpre : PromotePre st y z)
    (hd2 : 2 ≤ st.deg z) (hk : k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y) :
    kids (promoteState st y z) z = (kids st z).eraseIdx k := by
  have hd1 : st.deg z ≠ 1 := by omega
  have hw := walk_promote_pos st y z hrk hpre hd2 k hk
  -- the new head, in `hw`'s exact form
  have hxchd : k = 0 → st.chd z = y := by
    intro h
    rw [← hk.2, h, Function.iterate_zero_apply]
  have hchdx : st.chd z = y → k = 0 := (chdy_iff st y z hrk k hk).mp
  have hchd : (promoteState st y z).chd z = if k = 0 then st.rgt y else st.chd z := by
    rw [promoteState_chd_ne st y z z hd1, if_pos rfl]
    by_cases hkz : k = 0
    · rw [if_pos (hxchd hkz), if_pos hkz]
    · rw [if_neg (fun hc => hkz (hchdx hc)), if_neg hkz]
  unfold kids
  rw [promoteState_deg st y z z, if_pos rfl]
  have hlen : ((List.ofFn fun j : Fin (st.deg z) => st.rgt^[j.val] (st.chd z)).eraseIdx k).length
      = st.deg z - 1 := by
    rw [length_eraseIdx_lt (cs := List.ofFn fun j : Fin (st.deg z) => st.rgt^[j.val] (st.chd z))
      (by simpa using hk.1)]
    simp
  rw [hchd] at hw
  refine List.ext_get ?_ (fun n h1 h2 => ?_)
  · rw [hlen]
    simp
  · simp only [List.get_eq_getElem, List.getElem_ofFn]
    rw [hchd]
    have hn : n < st.deg z - 1 := by
      have h3 := h2
      rw [hlen] at h3
      omega
    rw [hw n hn]
    have hd0 : ((List.ofFn fun j : Fin (st.deg z) => st.rgt^[j.val] (st.chd z)).eraseIdx k)[n]
        = ((List.ofFn fun j : Fin (st.deg z) => st.rgt^[j.val] (st.chd z)).eraseIdx k).getD n 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h2, rfl⟩]
      simp
    rw [hd0]
    rcases Nat.lt_or_ge n k with hnk | hnk
    · rw [getD_eraseIdx_lt hnk,
        show (List.ofFn fun j : Fin (st.deg z) => st.rgt^[j.val] (st.chd z)).getD n 0
            = (st.rgt)^[n] (st.chd z) from kids_getD st z n (by omega), if_pos hnk]
    · rw [getD_eraseIdx_ge hnk,
        show (List.ofFn fun j : Fin (st.deg z) => st.rgt^[j.val] (st.chd z)).getD (n + 1) 0
            = (st.rgt)^[n + 1] (st.chd z) from kids_getD st z (n + 1) (by omega),
        if_neg (show ¬((n:ℕ) < k) from by omega)]

/-- **The re-root walk.**  The cut child `y` sits at some position `k`; after the cut, `z`'s
child list is the old list with position `k` erased. -/
theorem kids_promote (st : HState) (y z : ℕ) (hrk : RingOK st) (hpre : PromotePre st y z) :
    ∃ k, k < st.deg z ∧ (st.rgt)^[k] (st.chd z) = y ∧
      kids (promoteState st y z) z = (kids st z).eraseIdx k := by
  have hd0 : 0 < st.deg z := by
    have h1 := kids_length st z
    have h2 := List.length_pos_of_mem hpre.1
    omega
  obtain ⟨k, hk1, hk2⟩ := exists_pos_of_mem hpre.1
  refine ⟨k, hk1, hk2, ?_⟩
  by_cases hd : st.deg z = 1
  · exact kids_promote_zero st y z k hpre hd ⟨hk1, hk2⟩
  · exact kids_promote_pos st y z k hrk hpre (by omega) ⟨hk1, hk2⟩

/-- The cut child no longer appears in `z`'s child list. -/
theorem promotechild_notin_kids (st : HState) (y z : ℕ) (hrk : RingOK st) (hpre : PromotePre st y z)
    (hnd : KidsNodup st z) : y ∉ kids (promoteState st y z) z := by
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_promote st y z hrk hpre
  obtain ⟨hclose, hinj, htail⟩ := (hrk z).resolve_left (by have := kids_length st z; omega)
  have hlen : ((kids st z).eraseIdx k).length = st.deg z - 1 := by
    rw [kids, length_eraseIdx_lt (by simpa using hk1)]
    simp
  intro hx
  rw [hkeq] at hx
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hx
  have hjlen : j < ((kids st z).eraseIdx k).length := hj
  have hjd : j < st.deg z := by omega
  have hje' : ((kids st z).eraseIdx k).getD j 0 = y := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨hjlen, hje⟩]
    simp
  -- position `j` of the erased list reads old position `if j < k then j else j + 1 ≠ k`
  rcases Nat.lt_or_ge j k with a | a
  · rw [getD_eraseIdx_lt a, kids_getD st z j (by omega)] at hje'
    exact absurd (hinj j k (by omega) hk1 (hje'.trans hkx.symm)) (by omega)
  · rw [getD_eraseIdx_ge a, kids_getD st z (j + 1) (by omega)] at hje'
    exact absurd (hinj (j + 1) k (by omega) hk1 (hje'.trans hkx.symm)) (by omega)

/-- **Every other child list is untouched by the cut.** -/
theorem kids_promote_unchanged (st : HState) (y z q : ℕ) (hpar : ParOK st) (hpre : PromotePre st y z)
    (hq : q ≠ z) : kids (promoteState st y z) q = kids st q := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  have hd0 : 0 < st.deg z := by
    have h1 := kids_length st z
    have h3 := List.length_pos_of_mem hx
    omega
  have h1 : (promoteState st y z).deg q = st.deg q := by
    rw [promoteState_deg, if_neg hq]
  have h2 : (promoteState st y z).chd q = st.chd q := by
    by_cases hd : st.deg z = 1
    · simp [promoteState, hd, hq]
    · rw [promoteState_chd_ne st y z q hd, if_neg hq]
  have hmem : ∀ z j, j < st.deg z → (st.rgt)^[j] (st.chd z) ∈ kids st z := by
    intro z j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  have hw : ∀ j : ℕ, j < st.deg q →
      (promoteState st y z).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
    intro j hj
    induction j with
    | zero => simp
    | succ k ih =>
      have hik : k < st.deg q := by omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hik]
      rcases Nat.lt_or_ge (st.deg z) 2 with hlt | hd2
      · exact promoteState_rgt_eq st y z _ (by omega)
      · -- the walk visits only children of `q`; `lft y` is a child of `z`
        have hly : st.lft y ∈ kids st z := hlftmem (by omega)
        have hne : (st.rgt)^[k] (st.chd q) ≠ st.lft y := by
          intro hc
          have hm : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem q k hik
          rw [hc] at hm
          exact hq ((hpar q _ hm).symm.trans (hpar z _ hly))
        exact promoteState_rgt_ne st y z _ (by omega) hne
  unfold kids
  rw [h1, h2]
  refine List.ext_get (by simp) (fun n hn1 hn2 => ?_)
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact hw n (by simpa using hn2)

/-! ## The invariant discharges -/

/-- `MarkOK` survives the promote: the only mark writes are `mrk z := 1` (the unmarked
parent spends its one loss) and `mrk y := 0` (the promoted child's mark is cleared) —
both constants are trivially `≤ 1`. -/
theorem promote_MarkOK (st : HState) (y z : ℕ) (hm : MarkOK st) :
    MarkOK (promoteState st y z) := by
  intro q
  rw [promoteState_mrk]
  by_cases hqz : q = z
  · rw [if_pos hqz]
  · by_cases hqy : q = y
    · rw [if_neg hqz, if_pos hqy]; exact Nat.zero_le 1
    · rw [if_neg hqz, if_neg hqy]; exact hm q

/-- `ParSlot` survives the cut: every `par` value is either unchanged or the NIL slot `0`. -/
theorem promote_ParSlot (st : HState) (y z : ℕ) (hpre : PromotePre st y z) (hps : ParSlot st) :
    ParSlot (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  have hn : (promoteState st y z).n = st.n := promoteState_n st y z
  have hpos : 0 < st.n := by omega
  intro q hq
  rw [hn] at hq ⊢
  by_cases hqx : q = y
  · rw [hqx, promoteState_par_y]
    exact hpos
  · rw [promoteState_par_ne st y z q hqx]
    exact hps q hq

/-- `ParOK` survives the cut: `z`'s remaining children keep their parent, every other list is
untouched, and the only `par` write is `par y := 0`. -/
theorem promote_ParOK (st : HState) (y z : ℕ) (hpar : ParOK st) (hrk : RingOK st)
    (hpre : PromotePre st y z) (hnd : KidsNodup st z) : ParOK (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_promote st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩
  intro q v hv
  by_cases hqy : q = z
  · rw [hqy] at hv ⊢
    rw [hkeq] at hv
    have hvm : v ∈ kids st z := List.mem_of_mem_eraseIdx hv
    have hvx : v ≠ y := by
      intro hc
      rw [hc] at hv
      apply promotechild_notin_kids st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hnd
      rw [hkeq]; exact hv
    rw [promoteState_par_ne st y z v hvx]
    exact hpar z v hvm
  · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy] at hv
    have hvx : v ≠ y := by
      intro hc
      rw [hc] at hv
      exact hqy ((hpar q y hv).symm.trans (hpar z y hx))
    rw [promoteState_par_ne st y z v hvx]
    exact hpar q v hv

/-- `KidsNodup` survives the cut: `z`'s list loses one element (the erased list is strictly
order-preserving on positions), every other list is untouched. -/
theorem promote_KidsNodup (st : HState) (y z : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hnd : ∀ q, KidsNodup st q) : ∀ q, KidsNodup (promoteState st y z) q := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_promote st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩
  have hlen := length_eraseIdx_lt (by rw [kids_length]; exact hk1)
  have hmono : ∀ j j' : ℕ, j < j' → j' < st.deg z - 1 →
      (if j < k then j else j + 1) < (if j' < k then j' else j' + 1) := by
    intro j j' h hlt
    rcases Nat.lt_or_ge j k with a | a <;> rcases Nat.lt_or_ge j' k with b | b
    · rw [if_pos a, if_pos b]; exact h
    · rw [if_pos a, if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega), if_pos b]; omega
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega),
        if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
  have hget : ∀ j : ℕ, j < st.deg z - 1 →
      ((kids st z).eraseIdx k).getD j 0 = (kids st z).getD (if j < k then j else j + 1) 0 := by
    intro j hj
    rcases Nat.lt_or_ge j k with a | a
    · rw [getD_eraseIdx_lt a, if_pos a]
    · rw [getD_eraseIdx_ge a, if_neg (show ¬((j:ℕ) < k) from by omega)]
  intro q j j' hjk hk
  by_cases hqy : q = z
  · rw [hqy] at hk ⊢
    rw [promoteState_deg st y z z, if_pos rfl] at hk
    rw [hkeq] at ⊢
    rw [hget j (by omega), hget j' (by omega)]
    have hbd : (if j' < k then j' else j' + 1) < st.deg z := by
      rcases Nat.lt_or_ge j' k with b | b
      · rw [if_pos b]; omega
      · rw [if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
    exact hnd z _ _ (hmono j j' hjk hk) hbd
  · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy]
    rw [promoteState_deg st y z q, if_neg hqy] at hk
    exact hnd q j j' hjk hk

/-- `PosOK` survives the cut.  The one-loss rule does the work: `ldeg z` is invariant
(`(deg z - 1) + 1 = deg z + 0`, which needs the parent unmarked), the cut child is off every
list, and every other `ldeg` is untouched. -/
theorem promote_PosOK (st : HState) (y z : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hpos : PosOK st) : PosOK (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hk2⟩ := kids_promote st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩
  have hlen := length_eraseIdx_lt (by rw [kids_length]; exact hk1)
  have hne : ∀ j : ℕ, j < st.deg z - 1 → (if j < k then j else j + 1) ≠ k := by
    intro j hj
    rcases Nat.lt_or_ge j k with a | a
    · rw [if_pos a]; omega
    · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
  have hldegy : ldeg (promoteState st y z) z = st.deg z := by
    unfold ldeg
    rw [promoteState_deg st y z z, if_pos rfl, promoteState_mrk_z]
    omega
  intro q j hj
  by_cases hqy : q = z
  · rw [hqy, hk2] at hj ⊢
    rw [length_eraseIdx_lt (by rw [kids_length]; exact hk1), kids_length] at hj
    have hf : ((kids st z).eraseIdx k).getD j 0
        = (st.rgt)^[if j < k then j else j + 1] (st.chd z) := by
      rcases Nat.lt_or_ge j k with a | a
      · rw [getD_eraseIdx_lt a, if_pos a, kids_getD st z j (by omega)]
      · rw [getD_eraseIdx_ge a, if_neg (show ¬((j:ℕ) < k) from by omega),
          kids_getD st z (j + 1) (by omega)]
    rw [hf]
    have hjd2 : (if j < k then j else j + 1) < st.deg z := by
      rcases Nat.lt_or_ge j k with a | a
      · rw [if_pos a]; omega
      · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
    have hold := hpos z _ (by rw [kids_length]; exact hjd2)
    rw [kids_getD st z _ hjd2] at hold
    have hjle : j ≤ (if j < k then j else j + 1) := by
      rcases Nat.lt_or_ge j k with a | a
      · rw [if_pos a]
      · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
    by_cases hvy : (st.rgt)^[if j < k then j else j + 1] (st.chd z) = z
    · rw [hvy, hldegy]; omega
    · by_cases hvx : (st.rgt)^[if j < k then j else j + 1] (st.chd z) = y
      · exfalso
        obtain ⟨hc0, hinj, ht2⟩ := (hrk z).resolve_left (by omega)
        exact hne j hj (hinj _ k hjd2 hk1 (hvx.trans hkx.symm))
      · have hl : ldeg (promoteState st y z) ((st.rgt)^[if j < k then j else j + 1] (st.chd z))
            = ldeg st ((st.rgt)^[if j < k then j else j + 1] (st.chd z)) := by
          unfold ldeg
          rw [promoteState_deg st y z _, if_neg hvy, promoteState_mrk_ne st y z _ hvy hvx]
        rw [hl]
        exact le_trans hjle hold
  · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy] at hj ⊢
    have hvx : (kids st q).getD j 0 ≠ y := by
      intro hc
      have h1 : (kids st q).getD j 0 ∈ kids st q := kids_getD_mem st q j hj
      rw [hc] at h1
      exact hqy ((hpar q _ h1).symm.trans (hpar z y hx))
    by_cases hvy : (kids st q).getD j 0 = z
    · rw [hvy, hldegy]
      have hold := hpos q j hj
      rw [show ldeg st ((kids st q).getD j 0) = st.deg z from by
        rw [hvy]; unfold ldeg; omega] at hold
      exact hold
    · have hl : ldeg (promoteState st y z) ((kids st q).getD j 0)
          = ldeg st ((kids st q).getD j 0) := by
        unfold ldeg
        rw [promoteState_deg st y z _, if_neg hvy, promoteState_mrk_ne st y z _ hvy hvx]
      rw [hl]
      exact hpos q j hj

/-- `SlotOK` survives the cut: `z`'s list only shrinks, every other list is untouched. -/
theorem promote_SlotOK (st : HState) (y z : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hslot : SlotOK st) : SlotOK (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_promote st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩
  have hn : (promoteState st y z).n = st.n := promoteState_n st y z
  intro q hq v hv
  rw [hn] at hq ⊢
  by_cases hqy : q = z
  · rw [hqy] at hv
    rw [hkeq] at hv
    exact hslot z hyv v (List.mem_of_mem_eraseIdx hv)
  · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy] at hv
    exact hslot q hq v hv

/-- `Acyc` survives the cut.  The splice's only `par` change is `par y := 0`; a chain that hits
`y` is absorbed at NIL (`NILSelf`), one that misses `y` is an old chain, and either way a
closure forces the node to be `0`. -/
theorem promote_Acyc (st : HState) (y z : ℕ) (hpre : PromotePre st y z) (hns : NILSelf st)
    (hac : Acyc st) : Acyc (promoteState st y z) := by
  have f0 : (promoteState st y z).par 0 = 0 := by
    by_cases h0x : (0:ℕ) = y
    · rw [promoteState_par, if_pos h0x]
    · rw [promoteState_par, if_neg h0x]
      exact hns
  have fzero : ∀ k : ℕ, (promoteState st y z).par^[k] 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, f0]
  intro v j hj heq
  by_cases hhit : ∃ m, m < j ∧ (promoteState st y z).par^[m] v = y
  · obtain ⟨m, hmj, hmc⟩ := hhit
    have hstep : (promoteState st y z).par^[m + 1] v = 0 := by
      rw [Function.iterate_succ_apply', hmc, promoteState_par_y]
    by_cases hjm : j = m + 1
    · rw [hjm] at heq
      rw [hstep] at heq
      exact heq.symm
    · have hj2 : m + 1 ≤ j := by omega
      rw [show j = j - (m + 1) + (m + 1) from by omega, Function.iterate_add_apply, hstep,
        fzero] at heq
      exact heq.symm
  · have hall : ∀ i, i ≤ j → (promoteState st y z).par^[i] v = (st.par)^[i] v := by
      intro i hi
      induction i with
      | zero => rfl
      | succ k ih =>
        have hlt : k < j := by omega
        have hikj : k ≤ j := by omega
        have hkne : (st.par)^[k] v ≠ y := by
          intro hc
          rw [← ih hikj] at hc
          exact hhit ⟨k, hlt, hc⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hikj,
          promoteState_par_ne st y z _ hkne]
    rw [hall j (le_refl j)] at heq
    exact hac v j hj heq

/-- `NILRoots` survives the cut: the new root `y` has `par y = 0` by the splice, every old
root keeps its `par`. -/
theorem promote_NILRoots (st : HState) (y z : ℕ) (hnrs : NILRoots st) :
    NILRoots (promoteState st y z) := by
  intro r hr
  rw [promoteState_roots, List.mem_cons] at hr
  rcases hr with hrx | hr
  · rw [hrx, promoteState_par_y]
  · by_cases hx2 : y = r
    · rw [← hx2, promoteState_par_y]
    · rw [promoteState_par_ne st y z r (fun hc => hx2 hc.symm)]
      exact hnrs r hr

/-- `NILSelf` survives the cut: slot 0 is never the cut child written to. -/
theorem promote_NILSelf (st : HState) (y z : ℕ) (hpre : PromotePre st y z) (hnc : NILNotChild st)
    (hns : NILSelf st) : NILSelf (promoteState st y z) := by
  have hx0 : y ≠ 0 := fun hc => hnc z (hc ▸ hpre.1)
  show (promoteState st y z).par 0 = 0
  by_cases h0x : (0:ℕ) = y
  · rw [promoteState_par, if_pos h0x]
  · rw [promoteState_par, if_neg (show (0:ℕ) ≠ y from fun hc => hx0 hc.symm)]
    exact hns

/-- `NILNotRoot` survives the cut: the new root is `y ≠ 0` (`NILNotChild`), and `0` was not an
old root. -/
theorem promote_NILNotRoot (st : HState) (y z : ℕ) (hpre : PromotePre st y z) (hnc : NILNotChild st)
    (hnn : NILNotRoot st) : NILNotRoot (promoteState st y z) := by
  have hx0 : y ≠ 0 := fun hc => hnc z (hc ▸ hpre.1)
  intro h
  rw [promoteState_roots, List.mem_cons] at h
  rcases h with h | h
  · exact hx0 h.symm
  · exact hnn h

/-- `NILLeaf` survives the cut: `z ≠ 0` (a live node with children cannot be NIL), so slot 0's
degree is untouched. -/
theorem promote_NILLeaf (st : HState) (y z : ℕ) (hpre : PromotePre st y z) (hnl : NILLeaf st) :
    NILLeaf (promoteState st y z) := by
  have hy0 : z ≠ 0 := by
    intro hc
    rw [hc] at hpre
    have h1 : 0 < (kids st 0).length := List.length_pos_of_mem hpre.1
    have h2 : (kids st 0).length = 0 := by rw [kids_length, hnl]
    omega
  show (promoteState st y z).deg 0 = 0
  rw [promoteState_deg st y z 0, if_neg (show (0:ℕ) ≠ z from fun hc => hy0 hc.symm), hnl]

/-- `NILNotChild` survives the cut: `z`'s shrunk list is a sublist of the old one, every other
list is untouched, and the cut child is not NIL anyway. -/
theorem promote_NILNotChild (st : HState) (y z : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hnc : NILNotChild st) : NILNotChild (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_promote st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩
  intro q hv
  by_cases hqy : q = z
  · rw [hqy] at hv
    rw [hkeq] at hv
    exact hnc z (List.mem_of_mem_eraseIdx hv)
  · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy] at hv
    exact hnc q hv

/-- `RootNotChild` survives the cut: the new root `y` sits on no list (`z`'s list lost it, no
other list ever had it), and old roots are children only of NIL. -/
theorem promote_RootNotChild (st : HState) (y z : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hnd : KidsNodup st z) (hnc : NILNotChild st) (hnl : NILLeaf st)
    (hrnc : RootNotChild st) : RootNotChild (promoteState st y z) := by
  have hy0 : z ≠ 0 := by
    intro hc
    rw [hc] at hpre
    have h1 : 0 < (kids st 0).length := List.length_pos_of_mem hpre.1
    have h2 : (kids st 0).length = 0 := by rw [kids_length, hnl]
    omega
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  obtain ⟨k, hk1, hkx, hkeq⟩ := kids_promote st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩
  intro r hr q hq0 hv
  rw [promoteState_roots, List.mem_cons] at hr
  rcases hr with hrx | hr
  · -- the new root `y`
    by_cases hqy : q = z
    · rw [hqy] at hv
      rw [hrx] at hv
      exact promotechild_notin_kids st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hnd hv
    · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy] at hv
      rw [hrx] at hv
      exact hqy ((hpar q y hv).symm.trans (hpar z y hx))
  · -- an old root
    by_cases hqy : q = z
    · rw [hqy] at hv
      rw [hkeq] at hv
      exact hrnc r hr z hy0 (List.mem_of_mem_eraseIdx hv)
    · rw [kids_promote_unchanged st y z q hpar ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hqy] at hv
      exact hrnc r hr q hq0 hv

/-- `RootsLive` survives the cut: the new root `y` is live (`SlotOK` downwards from the live
parent `z`), and old roots stay live. -/
theorem promote_RootsLive (st : HState) (y z : ℕ) (hrk : RingOK st) (hpre : PromotePre st y z)
    (hslot : SlotOK st) (hrl : RootsLive st) : RootsLive (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  have hxv : y < st.n := hslot z hyv y hx
  have hn : (promoteState st y z).n = st.n := promoteState_n st y z
  intro r hr
  rw [promoteState_roots, List.mem_cons] at hr
  rcases hr with hrx | hr
  · rw [hrx, hn]
    exact hxv
  · rw [hn]
    exact hrl r hr

/-- `RingOK` survives the cut.  For `q ≠ z` the walk never touches a rewritten slot (the
rewritten slots — `lft y`, `rgt y` — are children of `z`, and every visited node is a child of
`q`).  For `z` itself the new ring is the old one with position `k` removed: it closes at
period `deg z - 1`, is injective there, and its head's `lft` is its last position. -/
theorem promote_RingOK (st : HState) (y z : ℕ) (hrk : RingOK st) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hnl : NILLeaf st) : RingOK (promoteState st y z) := by
  obtain ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ := hpre
  have hd0 : 0 < st.deg z := by
    have h1 := kids_length st z
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
  by_cases hqy : q = z
  · rw [hqy] at ⊢
    by_cases hd1 : st.deg z = 1
    · rw [promoteState_deg st y z z, if_pos rfl, hd1]
      exact Or.inl (by omega)
    · have hd2 : 2 ≤ st.deg z := by omega
      obtain ⟨k, hk1, hk2⟩ := exists_pos_of_mem hx
      obtain ⟨hclose, hinj, htail⟩ := (hrk z).resolve_left (by omega)
      have hxchd : k = 0 → st.chd z = y := by
        intro h
        rw [← hk2, h, Function.iterate_zero_apply]
      have hchdx : st.chd z = y → k = 0 := (chdy_iff st y z hrk k ⟨hk1, hk2⟩).mp
      have hchd : (promoteState st y z).chd z = if k = 0 then st.rgt y else st.chd z := by
        rw [promoteState_chd_ne st y z z hd1, if_pos rfl]
        by_cases hkz : k = 0
        · rw [if_pos (hxchd hkz), if_pos hkz]
        · rw [if_neg (fun hc => hkz (hchdx hc)), if_neg hkz]
      have hd1' : (promoteState st y z).deg z ≠ 0 := by
        rw [promoteState_deg st y z z, if_pos rfl]; omega
      have hw := walk_promote_pos st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hd2 k ⟨hk1, hk2⟩
      have hstep : ∀ v : ℕ, v ≠ st.lft y → (promoteState st y z).rgt v = st.rgt v :=
        fun v hv => promoteState_rgt_ne st y z v hd1 hv
      have hstepp : (promoteState st y z).rgt (st.lft y) = st.rgt y := promoteState_rgt_pred st y z hd1
      have hrgtx : st.rgt y = (st.rgt)^[k + 1] (st.chd z) := by
        rw [Function.iterate_succ_apply', hk2]
      have hpp := pred_pos st y z hrk ⟨hx, hyv, hmy1, hmz0, hpred, hlftmem⟩ hd2 k ⟨hk1, hk2⟩
      -- the new walk's jump: at the predecessor, `rgt'` moves to the cut child's successor
      have hjump : k ≠ 0 →
          (promoteState st y z).rgt^[k] (st.chd z) = (st.rgt)^[k + 1] (st.chd z) := by
        intro hkz
        have hpre_eq2 : (promoteState st y z).rgt^[k - 1] (st.chd z) = st.lft y := by
          have h1 := hw (k - 1) (by omega)
          rw [hchd, if_neg hkz] at h1
          rw [h1, if_pos (show (k:ℕ) - 1 < k from by omega), hpp, if_neg hkz]
        rw [show (k:ℕ) = (k - 1) + 1 from by omega, Function.iterate_succ_apply',
          hpre_eq2, hstepp, hrgtx,
          show (k:ℕ) + 1 = (k - 1) + 1 + 1 from by omega]
      -- the new ring closes at the new period `deg z - 1`
      have hclos : (promoteState st y z).rgt^[(st.deg z - 1)] ((promoteState st y z).chd z)
          = (promoteState st y z).chd z := by
        by_cases hkz : k = 0
        · -- k = 0: the new walk runs unchanged to the old tail, then jumps back to the new head
          have hxh : st.chd z = y := hxchd hkz
          have hrx1 : st.rgt y = (st.rgt)^[1] (st.chd z) := by
            rw [hrgtx, hkz, show (0:ℕ) + 1 = 1 from by omega]
          have hstep1 : (promoteState st y z).rgt^[(st.deg z - 1 - 1)] (st.rgt y) = st.lft y := by
            have hc2 : (promoteState st y z).rgt^[(st.deg z - 1 - 1)] (st.rgt y)
                = (st.rgt)^[(st.deg z - 1 - 1)] (st.rgt y) := by
              refine congr _ _ _ _ _ hstep (fun m hm hc => ?_)
              rw [hrx1, ← Function.iterate_add_apply] at hc
              rw [hpp, if_pos hkz] at hc
              have h5 := hinj (m + 1) (st.deg z - 1)
                (by have := kids_length st z; omega) (by omega) hc
              omega
            rw [hc2, hrx1, ← Function.iterate_add_apply,
              show (st.deg z - 1 - 1) + 1 = st.deg z - 1 from by omega, ← htail, hxh]
          rw [hchd, if_pos hkz,
            show (st.deg z - 1) = (st.deg z - 1 - 1) + 1 from by omega,
            Function.iterate_succ_apply', hstep1, hstepp]
        · rcases Nat.lt_or_ge k (st.deg z - 1) with hki | hkd
          · -- 1 ≤ k ≤ deg z - 2: jump at the predecessor (step `k`), then unchanged to the head
            rw [hchd, if_neg (show ¬(k:ℕ) = 0 from by omega),
              show (st.deg z - 1) = (st.deg z - 1 - k) + k from by omega,
              Function.iterate_add_apply, hjump (by omega)]
            have hc3 : (promoteState st y z).rgt^[(st.deg z - 1 - k)] ((st.rgt)^[k + 1] (st.chd z))
                = (st.rgt)^[(st.deg z - 1 - k)] ((st.rgt)^[k + 1] (st.chd z)) := by
              refine congr _ _ _ _ _ hstep (fun m hm hc => ?_)
              rw [hpp, if_neg (show ¬(k:ℕ) = 0 from by omega),
                ← Function.iterate_add_apply] at hc
              have h5 := hinj (m + (k + 1)) (k - 1)
                (by have := kids_length st z; omega) (by omega) hc
              omega
            rw [hc3, ← Function.iterate_add_apply,
              show (st.deg z - 1 - k) + (k + 1) = st.deg z from by omega]
            exact hclose
          · -- k = deg z - 1: the walk reaches the old tail (the cut child) and jumps to the head
            have hkde : k = st.deg z - 1 := by omega
            have hpre_eq2 : (promoteState st y z).rgt^[k - 1] (st.chd z) = st.lft y := by
              have h1 := hw (k - 1) (by omega)
              rw [hchd, if_neg (show ¬(k:ℕ) = 0 from by omega)] at h1
              rw [h1, if_pos (show (k:ℕ) - 1 < k from by omega), hpp,
                if_neg (show ¬(k:ℕ) = 0 from by omega)]
            rw [hchd, if_neg (show ¬(k:ℕ) = 0 from by omega),
              show (st.deg z - 1) = (k - 1) + 1 from by omega,
              Function.iterate_succ_apply', hpre_eq2, hstepp, hrgtx,
              show (k:ℕ) + 1 = st.deg z from by omega, hclose]
      have hclos' : (promoteState st y z).rgt^[(promoteState st y z).deg z]
          ((promoteState st y z).chd z) = (promoteState st y z).chd z := by
        rw [promoteState_deg st y z z, if_pos rfl]
        exact hclos
      refine Or.inr ⟨hclos', ?_, ?_⟩
      -- injectivity of the new walk: the position map is strictly increasing
      · intro j j' hj hj' heq
        rw [promoteState_deg st y z z, if_pos rfl] at hj hj'
        rw [hw j hj, hw j' hj'] at heq
        have hfinj : ∀ a b : ℕ, a < st.deg z - 1 → b < st.deg z - 1 →
            (if a < k then a else a + 1) = (if b < k then b else b + 1) → a = b := by
          intro a b ha hb heq2
          rcases Nat.lt_or_ge a k with a1 | a1 <;> rcases Nat.lt_or_ge b k with b1 | b1
          · rw [if_pos a1, if_pos b1] at heq2; exact heq2
          · rw [if_pos a1, if_neg (show ¬((b:ℕ) < k) from by omega)] at heq2; omega
          · rw [if_neg (show ¬((a:ℕ) < k) from by omega), if_pos b1] at heq2; omega
          · rw [if_neg (show ¬((a:ℕ) < k) from by omega),
              if_neg (show ¬((b:ℕ) < k) from by omega)] at heq2; omega
        have hf1 : (if j < k then j else j + 1) < st.deg z := by
          rcases Nat.lt_or_ge j k with a | a
          · rw [if_pos a]; omega
          · rw [if_neg (show ¬((j:ℕ) < k) from by omega)]; omega
        have hf2 : (if j' < k then j' else j' + 1) < st.deg z := by
          rcases Nat.lt_or_ge j' k with a | a
          · rw [if_pos a]; omega
          · rw [if_neg (show ¬((j':ℕ) < k) from by omega)]; omega
        have hf := hinj _ _ hf1 hf2 heq
        exact hfinj j j' hj hj' hf
      -- `lft` of the new head is the last position of the new walk
      · have hwb : st.deg z - 1 - 1 < st.deg z - 1 := by omega
        rw [promoteState_deg st y z z, if_pos rfl, hw (st.deg z - 1 - 1) hwb, hchd]
        by_cases hkz : k = 0
        · -- k = 0: the new head is the cut child's successor; the splice set its `lft`
          rw [if_pos hkz, promoteState_lft_succ st y z hd1,
            if_neg (show ¬((st.deg z - 1 - 1:ℕ) < k) from by omega),
            show (st.deg z - 1 - 1) + 1 = st.deg z - 1 from by omega,
            hpp, if_pos hkz]
        · rcases Nat.lt_or_ge k (st.deg z - 1) with hkl | hkd
          · -- 1 ≤ k ≤ deg z - 2: the new head is the old head; its `lft` is untouched
            have hk1d : k + 1 < st.deg z := by omega
            have hchd_ne : st.chd z ≠ st.rgt y := by
              intro hc
              have hz : (st.rgt)^[0] (st.chd z) = (st.rgt)^[k + 1] (st.chd z) := by
                rw [Function.iterate_zero_apply, ← hrgtx]; exact hc
              have h5 := hinj (k + 1) 0 hk1d hd0 hz.symm
              have h6 : ¬((k:ℕ) + 1 = 0) := by simp
              exact absurd h5 h6
            rw [if_neg hkz, if_neg (show ¬((st.deg z - 1 - 1:ℕ) < k) from by omega),
              promoteState_lft_ne st y z (st.chd z) hd1 hchd_ne, htail,
              show (st.deg z - 1 - 1) + 1 = st.deg z - 1 from by omega]
          · -- k = deg z - 1: the cut child was the tail; the new head is its successor
            have hkde : k = st.deg z - 1 := by omega
            have heq : st.chd z = st.rgt y := by
              rw [hrgtx, hkde, show (st.deg z - 1) + 1 = st.deg z from by omega, hclose]
            rw [if_neg (show ¬(k:ℕ) = 0 from by omega),
              if_pos (show (st.deg z - 1 - 1:ℕ) < k from by omega), heq,
              promoteState_lft_succ st y z hd1, hpp, if_neg (show ¬(k:ℕ) = 0 from by omega),
              hkde, ← heq]
  · by_cases hdq : (promoteState st y z).deg q = 0
    · exact Or.inl hdq
    · right
      have hdq' : st.deg q ≠ 0 := by
        rw [promoteState_deg st y z q, if_neg hqy] at hdq; exact hdq
      have hmem : ∀ j, j < st.deg q → (st.rgt)^[j] (st.chd q) ∈ kids st q := by
        intro j hj
        rw [kids]
        exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
      by_cases hdy1 : st.deg z = 1
      · -- the degree-1 splice does not touch `q`'s fields at all
        have hchdq : (promoteState st y z).chd q = st.chd q := by
          simp [promoteState, hdy1, hqy]
        have hf : (promoteState st y z).rgt = st.rgt := by
          funext v; exact promoteState_rgt_eq st y z v hdy1
        have hff : (promoteState st y z).lft = st.lft := by
          funext v; exact promoteState_lft_eq st y z v hdy1
        refine ⟨?_, ?_, ?_⟩
        · rw [promoteState_deg st y z q, if_neg hqy, hchdq, hf]
          exact ((hrk q).resolve_left hdq').1
        · intro j j' hj hj' heq
          rw [promoteState_deg st y z q, if_neg hqy] at hj hj'
          rw [hchdq, hf] at heq
          exact ((hrk q).resolve_left hdq').2.1 j j' hj hj' heq
        · rw [promoteState_deg st y z q, if_neg hqy, hchdq, hf, hff]
          exact ((hrk q).resolve_left hdq').2.2
      · have hd2 : 2 ≤ st.deg z := by omega
        have hd1 : st.deg z ≠ 1 := by omega
        obtain ⟨k, hk1, hk2⟩ := exists_pos_of_mem hx
        obtain ⟨hclose, hinj, htail⟩ := (hrk z).resolve_left (by omega)
        have hmemY : ∀ j, j < st.deg z → (st.rgt)^[j] (st.chd z) ∈ kids st z := by
          intro j hj
          rw [kids]
          exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
        have hly : st.lft y ∈ kids st z := hlftmem hd2
        have hrgtx : st.rgt y = (st.rgt)^[k + 1] (st.chd z) := by
          rw [Function.iterate_succ_apply', hk2]
        have hrgxy : st.rgt y ∈ kids st z := by
          rw [hrgtx]
          rcases Nat.lt_or_ge (k + 1) (st.deg z) with hlt | hge
          · exact hmemY (k + 1) hlt
          · have hk1' : (k + 1 : ℕ) = st.deg z := by omega
            rw [hk1', hclose]
            exact hmemY 0 (by omega)
        have hchdq : (promoteState st y z).chd q = st.chd q := by
          rw [promoteState_chd_ne st y z q hd1, if_neg hqy]
        have hvs : ∀ i, i < st.deg q →
            (st.rgt)^[i] ((promoteState st y z).chd q) ≠ st.lft y := by
          intro i hi hc
          rw [hchdq] at hc
          have hm : (st.rgt)^[i] (st.chd q) ∈ kids st q := hmem i hi
          rw [hc] at hm
          exact hqy ((hpar q _ hm).symm.trans (hpar z _ hly))
        have hw2 : ∀ j, j < st.deg q →
            (promoteState st y z).rgt^[j] ((promoteState st y z).chd q) = (st.rgt)^[j] (st.chd q) := by
          intro j hj
          rw [hchdq]
          refine congr (promoteState st y z).rgt st.rgt (st.lft y) (st.chd q) j
            (fun v hv => promoteState_rgt_ne st y z v hd1 hv) ?_
          intro i hi
          rw [← hchdq]
          exact hvs i (by omega)
        refine ⟨?_, ?_, ?_⟩
        · have hdq1 : (promoteState st y z).deg q = (st.deg q - 1) + 1 := by
            rw [promoteState_deg st y z q, if_neg hqy]
            omega
          rw [hdq1, Function.iterate_succ_apply', hw2 (st.deg q - 1) (by omega), hchdq]
          have hvne : (st.rgt)^[st.deg q - 1] (st.chd q) ≠ st.lft y := by
            intro hc
            rw [← hchdq] at hc
            exact hvs _ (by omega) hc
          have hfin_eq : (st.rgt)^[st.deg q] (st.chd q)
              = (st.rgt)^[st.deg q - 1 + 1] (st.chd q) := by
            rw [show st.deg q - 1 + 1 = st.deg q from by omega]
          rw [promoteState_rgt_ne st y z _ hd1 hvne]
          have hfin : st.rgt ((st.rgt)^[st.deg q - 1] (st.chd q))
              = (st.rgt)^[st.deg q] (st.chd q) := by
            rw [hfin_eq]
            exact (Function.iterate_succ_apply' st.rgt (st.deg q - 1) (st.chd q)).symm
          rw [hfin]
          exact ((hrk q).resolve_left hdq').1
        · intro j j' hj hj' heq
          rw [promoteState_deg st y z q, if_neg hqy] at hj hj'
          rw [hw2 j hj, hw2 j' hj'] at heq
          obtain ⟨hc2, hij2, ht3⟩ := (hrk q).resolve_left hdq'
          exact hij2 j j' hj hj' heq
        · rw [promoteState_deg st y z q, if_neg hqy]
          rw [hw2 (st.deg q - 1) (by omega)]
          -- `chd q ≠ rgt y` (their parents differ), so `lft` is untouched at the new head
          have hchdq' : (promoteState st y z).chd q ≠ st.rgt y := by
            intro hc
            have h0m : st.chd q ∈ kids st q := by
              have hmz0' := hmem 0 (by have := kids_length st q; omega)
              rwa [Function.iterate_zero_apply] at hmz0'
            have hp1 : st.par (st.chd q) = q := hpar q _ h0m
            have hp2 : st.par (st.rgt y) = z := hpar z _ hrgxy
            rw [← hchdq, hc] at hp1
            exact hqy (hp1.symm.trans hp2)
          rw [promoteState_lft_ne st y z _ hd1 hchdq', hchdq]
          exact (hrk q).resolve_left hdq' |>.2.2

/-! ## The promote-output witness -/

/-- The promote witness's pre-state: slot 1 an unmarked root holding one marked child
(slot 2), which in turn holds one child (slot 3). -/
def promotePreSt : HState where
  par := fun i => if i = 2 then 1 else if i = 3 then 2 else 0
  chd := fun i => if i = 1 then 2 else if i = 2 then 3 else 0
  rgt := fun i => if i = 2 then 2 else if i = 3 then 3 else 0
  lft := fun i => if i = 2 then 2 else if i = 3 then 3 else 0
  deg := fun i => if i = 1 then 1 else if i = 2 then 1 else 0
  mrk := fun i => if i = 2 then 1 else 0
  roots := [1]
  n := 4

/-- The promote output: the marked child `2` is cut off slot `1` and re-rooted, its mark
clears, and slot `1` is marked. -/
def promoted : HState := promoteState promotePreSt 2 1

/-- The witness pre-state really is a legal promote pre-state. -/
theorem promotePreSt_ok : PromotePre promotePreSt 2 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kids
    exact List.mem_ofFn.mpr ⟨⟨0, by simp [promotePreSt]⟩, rfl⟩
  · simp [promotePreSt]
  · simp [promotePreSt]
  · simp [promotePreSt]
  · simp [promotePreSt]
  · intro h
    exact absurd h (by simp [promotePreSt])

@[simp] theorem promoted_par (v : ℕ) : promoted.par v = if v = 3 then 2 else 0 := by
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;>
    simp [promoted, promoteState, promotePreSt, h1, h2, h3]
@[simp] theorem promoted_mrk (v : ℕ) : promoted.mrk v = if v = 1 then 1 else 0 := by
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> simp [promoted, promoteState, promotePreSt, h1, h2]
@[simp] theorem promoted_deg (v : ℕ) : promoted.deg v = if v = 2 then 1 else 0 := by
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> simp [promoted, promoteState, promotePreSt, h1, h2]
@[simp] theorem promoted_chd (v : ℕ) : promoted.chd v = if v = 2 then 3 else 0 := by
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> simp [promoted, promoteState, promotePreSt, h1, h2]
@[simp] theorem promoted_rgt (v : ℕ) :
    promoted.rgt v = if v = 2 then 2 else if v = 3 then 3 else 0 := by
  by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> simp [promoted, promoteState, promotePreSt, h2, h3]
@[simp] theorem promoted_lft (v : ℕ) :
    promoted.lft v = if v = 2 then 2 else if v = 3 then 3 else 0 := by
  by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> simp [promoted, promoteState, promotePreSt, h2, h3]
@[simp] theorem promoted_roots : promoted.roots = [2, 1] := by
  simp [promoted, promoteState, promotePreSt]
@[simp] theorem promoted_n : promoted.n = 4 := rfl
@[simp] theorem kids_promoted (q : ℕ) : kids promoted q = if q = 2 then [3] else [] := by
  unfold kids
  by_cases hq : q = 2
  · subst hq
    simp [promoted, promoteState, promotePreSt]
  · by_cases hq1 : q = 1 <;> simp [promoted, promoteState, promotePreSt, hq, hq1]

theorem promoted_ParOK : ParOK promoted := by
  intro q v hv
  by_cases hq : q = 2
  · subst hq
    rw [kids_promoted, if_pos rfl] at hv
    simp at hv
    subst hv
    simp
  · rw [kids_promoted, if_neg hq] at hv
    simp at hv

theorem promoted_SlotOK : SlotOK promoted := by
  intro q hq v hv
  by_cases hq2 : q = 2
  · subst hq2
    rw [kids_promoted, if_pos rfl] at hv
    simp at hv
    subst hv
    simp
  · rw [kids_promoted, if_neg hq2] at hv
    simp at hv

theorem promoted_ParSlot : ParSlot promoted := by
  intro q hq
  by_cases hq3 : q = 3
  · subst hq3; simp
  · rw [promoted_par, if_neg hq3]; simp

theorem promoted_KidsNodup : ∀ q, KidsNodup promoted q := by
  intro q j k hjk hk
  by_cases hq : q = 2
  · subst hq
    rw [promoted_deg, if_pos rfl] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [kids_promoted, if_pos rfl]
    by_cases hj0 : j = 0
    · subst hj0; exact absurd hjk (by omega)
    · simp [hj0]
  · rw [promoted_deg, if_neg hq] at hk
    simp at hk

theorem promoted_NILRoots : NILRoots promoted := by
  intro r hr
  rw [promoted_roots] at hr
  simp at hr
  rcases hr with rfl | rfl <;> simp

theorem promoted_NILSelf : NILSelf promoted := rfl

theorem promoted_NILNotChild : NILNotChild promoted := by
  intro q hv
  by_cases hq : q = 2
  · subst hq
    rw [kids_promoted, if_pos rfl] at hv
    simp at hv
  · rw [kids_promoted, if_neg hq] at hv
    simp at hv

theorem promoted_RootNotChild : RootNotChild promoted := by
  intro r hr q _ hv
  by_cases hq : q = 2
  · subst hq
    rw [promoted_roots] at hr
    rw [kids_promoted, if_pos rfl] at hv
    simp at hv
    subst hv
    simp at hr
  · rw [kids_promoted, if_neg hq] at hv
    simp at hv

theorem promoted_RootsLive : RootsLive promoted := by
  intro r hr
  rw [promoted_roots] at hr
  simp at hr
  rcases hr with rfl | rfl <;> simp

theorem promoted_NILNotRoot : NILNotRoot promoted := by
  intro h
  simp [promoted, promoteState, promotePreSt] at h

theorem promoted_NILLeaf : NILLeaf promoted := rfl

theorem promoted_Acyc : Acyc promoted := by
  have hp3 : promoted.par 3 = 2 := by simp
  have hp2 : promoted.par 2 = 0 := by simp
  have hp0z : promoted.par 0 = 0 := by simp
  intro x j hj heq
  by_cases hx3 : x = 3
  · subst hx3
    have h1 : (promoted.par)^[1] 3 = 2 := by rw [Function.iterate_one]; exact hp3
    have h2 : ∀ m : ℕ, (promoted.par)^[m + 1] 2 = 0 := by
      intro m
      induction m with
      | zero => exact hp2
      | succ m ih => rw [Function.iterate_succ_apply', ih, hp0z]
    have hchain : ∀ m : ℕ, (promoted.par)^[m + 2] 3 = 0 := by
      intro m
      rw [show (m:ℕ) + 2 = (m + 1) + 1 from rfl, Function.iterate_add_apply, h1]
      exact h2 m
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1 : j = 1 := by omega
      subst hj1
      rw [Function.iterate_one, hp3] at heq
      simp at heq
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      rw [hchain m] at heq
      simp at heq
  · have hx0 : promoted.par x = 0 := by
      by_cases hx2 : x = 2
      · subst hx2; simp
      · simp [hx3, hx2]
    cases j with
    | zero => omega
    | succ k =>
      have hall : ∀ m : ℕ, (promoted.par)^[m + 1] x = 0 := by
        intro m
        induction m with
        | zero => exact hx0
        | succ m ih => rw [Function.iterate_succ_apply', ih, hp0z]
      rw [hall k] at heq
      exact heq.symm

theorem promoted_MarkOK : MarkOK promoted := by
  intro q
  by_cases hq : q = 1
  · subst hq; simp
  · rw [promoted_mrk, if_neg hq]; exact Nat.zero_le 1

theorem promoted_PosOK : PosOK promoted := by
  intro q j hj
  by_cases hq : q = 2
  · subst hq
    rw [kids_promoted, if_pos rfl] at hj ⊢
    simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [ldeg]
  · rw [kids_promoted, if_neg hq] at hj
    simp at hj

/-- The promoted witness satisfies the support condition at the promoted root: its
abstraction is the two-node tree over slots 2, 3. -/
theorem promoted_Support : Support promoted (promoted.n + 1) 2 := by
  refine ⟨{2, 3}, ?_, ?_⟩
  · have hshape : treeOf promoted (promoted.n + 1) 2
        = FibHeapForest.Tree.node 2
            [FibHeapForest.Child.mk (treeOf promoted 4 3) (ldeg promoted 3) (promoted.mrk 3)] := by
      simp [treeOf, kids_promoted]
    rw [hshape, FibHeapForest.size_node, FibHeapForest.sizeSum]
    simp [FibHeapForest.Child.size, FibHeapForest.Child.tree, FibHeapForest.size_node,
      FibHeapForest.sizeSum, treeOf, kids_promoted]
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp

/-- **The capstone applied to the post-promote state.**  The promote transition keeps the
machine inside the invariant set, so the rank cap applies to the freshly promoted root. -/
theorem promoted_capstone : promoted.deg 2 ≤ FibHeapAccounting.rankCap promoted.n := by
  have hsup := promoted_Support
  have hpn : promoted.n + 1 = 5 := by rw [promoted_n]
  rw [promoted_n] at hsup ⊢
  exact degree_le_rankCap_zero promoted promoted_ParOK promoted_SlotOK promoted_ParSlot
    promoted_KidsNodup promoted_Acyc promoted_NILSelf promoted_NILLeaf promoted_NILNotChild
    promoted_MarkOK promoted_PosOK (by simp) (by simp) hsup

/-! ## The clearing variant: CLRS mark writes (Route A's anchors)

The transfer `promoteState` banks-or-moves one mark (`y → 0`, `z → 1`).
`clearPromoteState` is the same splice with the CLRS clearing writes: BOTH
`y` and `z` are cleared (`y → 0`, `z → 0`).  On an intermediate cell (both
marked) that consumes two marks; on the terminal cell (only `y` marked) it
consumes one and the stop's `markState` re-banks — the `CascadeMarks`
ledger's `k` clears plus one fresh mark.  It is a separate constructor by
design: the transfer suite stays green while the clearing surface re-runs;
the def-swap into `promoteState` is the surface's last step. -/

def clearPromoteState (st : HState) (y z : ℕ) : HState :=
  if st.deg z = 1 then
    { st with
      par := (fun i => if i = y then 0 else st.par i)
      mrk := (fun i => if i = y then 0 else if i = z then 0 else st.mrk i)
      deg := (fun i => if i = z then st.deg i - 1 else st.deg i)
      chd := (fun i => if i = z then 0 else st.chd i)
      roots := y :: st.roots }
  else
    { st with
      par := (fun i => if i = y then 0 else st.par i)
      mrk := (fun i => if i = y then 0 else if i = z then 0 else st.mrk i)
      deg := (fun i => if i = z then st.deg i - 1 else st.deg i)
      chd := (fun i => if i = z then if st.chd z = y then st.rgt y else st.chd i else st.chd i)
      rgt := (fun i => if i = st.lft y then st.rgt y else st.rgt i)
      lft := (fun i => if i = st.rgt y then st.lft y else st.lft i)
      roots := y :: st.roots }

theorem clearPromoteState_mrk (st : HState) (y z q : ℕ) :
    (clearPromoteState st y z).mrk q =
      if q = y then 0 else if q = z then 0 else st.mrk q := by
  unfold clearPromoteState
  by_cases h : st.deg z = 1
  · rw [if_pos h]
  · rw [if_neg h]

theorem clearPromoteState_n (st : HState) (y z : ℕ) :
    (clearPromoteState st y z).n = st.n := by
  unfold clearPromoteState
  by_cases h : st.deg z = 1
  · rw [if_pos h]
  · rw [if_neg h]

/-- **Anchor one.**  `MarkOK` survives the clearing writes trivially: they
only write zeros. -/
theorem promoteClear_MarkOK (st : HState) (y z : ℕ) (hm : MarkOK st) :
    MarkOK (clearPromoteState st y z) := by
  intro q
  rw [clearPromoteState_mrk]
  by_cases hqy : q = y
  · simp [hqy]
  by_cases hqz : q = z
  · simp [hqz]
  · rw [if_neg hqy, if_neg hqz]
    exact hm q

end Submission.FibHeapPromote

