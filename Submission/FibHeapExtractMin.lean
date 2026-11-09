import Submission.FibHeapMerge

/-!
# M4a: extract-min — the array-level step

`extractState st r` is the machine-array splice of one extract-min: the root `r` is
removed from the root list (filtered — *all* occurrences, the merge lesson), its
children are promoted to the root list with their marks cleared and their parents
re-pointed to NIL, and `r`'s child list is emptied (`deg r := 0`, `chd r := 0`; no
`rgt`/`lft` writes — `deg r = 0` makes `RingOK` vacuous at `r`, as in every deg-0
case before).  Keys live outside `HState`: the caller supplies *which* root is the
minimum, exactly as the cut/promote/merge splices supply which nodes they act on.

The consolidation pass that follows — repeated equal-degree melding of the promoted
children against the remaining roots — is the *next* module's fold (`extractRun` over
`mergeState` cells, mirroring `cascadeRun`); this module lands the splice, its
pointwise behaviour, and the invariant bundle on the extracted state.

## What the bundle needs (and what it does not)

`ExtractPre st r` is just `r ∈ st.roots`.  Everything else is carried by the bundle
itself: `ParOK st` supplies the child-list disjointness (a node in two child lists
would have two parents), which is what keeps every *other* list untouched by the
`par`-clearing of `r`'s children — no `kids_unchanged`-style premise bridge is needed
because `deg q`/`chd q` for `q ≠ r` are untouched outright.  `Acyc` follows the
cut's dichotomy (walk either reaches `r`'s promoted children and dies at NIL, or is
unchanged all the way and is handled by the old `Acyc`).

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapExtractMin

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink Submission.FibHeapLinkWalk Submission.FibHeapCut
  Submission.FibHeapMerge

/-! ## The extract splice -/

/-- Preconditions of an extract: `r` is a root.  (The minimum-selection itself is
keyless — the caller names the root; the bundle does the rest.) -/
def ExtractPre (st : HState) (r : ℕ) : Prop :=
  r ∈ st.roots

/-- The extract splice: `r` leaves the root list, its children become unmarked roots,
`r`'s child list empties.  No `rgt`/`lft` writes (`deg r = 0` makes the ring vacuous). -/
def extractState (st : HState) (r : ℕ) : HState :=
  { st with
    par := (fun i => if i ∈ kids st r then 0 else st.par i)
    mrk := (fun i => if i ∈ kids st r then 0 else st.mrk i)
    deg := (fun i => if i = r then 0 else st.deg i)
    chd := (fun i => if i = r then 0 else st.chd i)
    roots := st.roots.filter (fun x => x != r) ++ kids st r }

/-! ## Pointwise behaviour of the splice -/

theorem extractState_deg (st : HState) (r q : ℕ) :
    (extractState st r).deg q = if q = r then 0 else st.deg q := by
  simp [extractState]

theorem extractState_chd (st : HState) (r q : ℕ) :
    (extractState st r).chd q = if q = r then 0 else st.chd q := by
  simp [extractState]

theorem extractState_mrk (st : HState) (r q : ℕ) :
    (extractState st r).mrk q = if q ∈ kids st r then 0 else st.mrk q := by
  simp [extractState]

theorem extractState_par (st : HState) (r q : ℕ) :
    (extractState st r).par q = if q ∈ kids st r then 0 else st.par q := by
  simp [extractState]

theorem extractState_n (st : HState) (r : ℕ) : (extractState st r).n = st.n := by
  simp [extractState]

theorem extractState_roots (st : HState) (r : ℕ) :
    (extractState st r).roots = st.roots.filter (fun x => x != r) ++ kids st r := by
  simp [extractState]

/-- A promoted child's parent is NIL. -/
theorem extractState_par_child (st : HState) (r c : ℕ) (hc : c ∈ kids st r) :
    (extractState st r).par c = 0 := by
  rw [extractState_par, if_pos hc]

/-- An un-promoted slot's parent is untouched. -/
theorem extractState_par_ne (st : HState) (r c : ℕ) (hc : c ∉ kids st r) :
    (extractState st r).par c = st.par c := by
  rw [extractState_par, if_neg hc]

/-- A promoted child's mark is cleared. -/
theorem extractState_mrk_child (st : HState) (r c : ℕ) (hc : c ∈ kids st r) :
    (extractState st r).mrk c = 0 := by
  rw [extractState_mrk, if_pos hc]

/-- An un-promoted slot's mark is untouched. -/
theorem extractState_mrk_ne (st : HState) (r c : ℕ) (hc : c ∉ kids st r) :
    (extractState st r).mrk c = st.mrk c := by
  rw [extractState_mrk, if_neg hc]

/-! ## The child lists after the extract -/

/-- The extracted root's child list is empty. -/
theorem kids_extract_r (st : HState) (r : ℕ) : kids (extractState st r) r = [] := by
  simp [kids, extractState]

/-- Every other child list is untouched: `deg q` and `chd q` are, so the walk is. -/
theorem kids_extract_of_ne (st : HState) (r q : ℕ) (hqr : q ≠ r) :
    kids (extractState st r) q = kids st q := by
  unfold kids
  rw [extractState_deg, if_neg hqr, extractState_chd, if_neg hqr]
  rfl

/-- Child-list disjointness out of `ParOK`: a node in two child lists would have two
parents.  This is why the `par`-clearing of `r`'s children cannot disturb any other
list's read-out. -/
theorem notin_kids_extract (st : HState) (hpar : ParOK st) {r q v : ℕ} (hqr : q ≠ r)
    (hv : v ∈ kids st q) : v ∉ kids st r := by
  intro hv2
  have h1 : st.par v = q := hpar q v hv
  have h2 : st.par v = r := hpar r v hv2
  omega

/-! ## The invariant bundle on the extracted state -/

/-- `MarkOK` survives: promoted children are unmarked, everyone else is untouched. -/
theorem extract_MarkOK (st : HState) (r : ℕ) (hm : MarkOK st) :
    MarkOK (extractState st r) := by
  intro q
  by_cases h : q ∈ kids st r
  · rw [extractState_mrk_child st r q h]
    omega
  · rw [extractState_mrk_ne st r q h]
    exact hm q

/-- `ParSlot` survives: NIL is a live slot. -/
theorem extract_ParSlot (st : HState) (r : ℕ) (hps : ParSlot st) :
    ParSlot (extractState st r) := by
  intro q hq
  by_cases h : q ∈ kids st r
  · rw [extractState_par_child st r q h]
    exact Nat.zero_lt_of_lt hq
  · rw [extractState_par_ne st r q h]
    exact hps q hq

/-- `ParOK` survives: the extracted root's list is empty, every other list is untouched,
and the promoted children read out NIL. -/
theorem extract_ParOK (st : HState) (r : ℕ) (hpar : ParOK st) :
    ParOK (extractState st r) := by
  intro q v hv
  by_cases hqr : q = r
  · subst hqr
    rw [kids_extract_r] at hv
    simp at hv
  · rw [kids_extract_of_ne st r q hqr] at hv
    have hv2 : v ∉ kids st r := notin_kids_extract st hpar hqr hv
    rw [extractState_par_ne st r v hv2]
    exact hpar q v hv

/-- `KidsNodup` survives: the extracted root's list is empty (vacuous), every other
list is the old list with the old degree. -/
theorem extract_KidsNodup (st : HState) (r : ℕ) (hnd : ∀ q, KidsNodup st q) :
    ∀ q, KidsNodup (extractState st r) q := by
  intro q j k hjk hk
  by_cases hqr : q = r
  · subst hqr
    rw [extractState_deg, if_pos rfl] at hk
    omega
  · rw [kids_extract_of_ne st r q hqr]
    rw [extractState_deg, if_neg hqr] at hk
    exact hnd q j k hjk hk

/-- `PosOK` survives: the positions and link degrees of untouched lists are untouched,
and the extracted root's list is empty.  The read-out value of an untouched list is
neither `r` (it is a root in no non-NIL list, and NIL has no children) nor one of `r`'s
children (two parents), so both link-degree summands are the old ones. -/
theorem extract_PosOK (st : HState) (r : ℕ) (hpre : ExtractPre st r) (hpar : ParOK st)
    (hrnc : RootNotChild st) (hnl : NILLeaf st) (hpos : PosOK st) :
    PosOK (extractState st r) := by
  intro q j hj
  by_cases hqr : q = r
  · subst hqr
    rw [kids_extract_r] at hj
    simp at hj
  · rw [kids_extract_of_ne st r q hqr] at hj ⊢
    have hmem : (kids st q).getD j 0 ∈ kids st q := by
      rw [List.getD_eq_getElem (kids st q) 0 hj]
      exact List.getElem_mem hj
    have hv2 : (kids st q).getD j 0 ∉ kids st r :=
      notin_kids_extract st hpar hqr hmem
    have hyr : (kids st q).getD j 0 ≠ r := by
      intro hc
      rw [hc] at hmem
      rcases Nat.eq_zero_or_pos q with hq0 | hqp
      · subst hq0
        rw [kids_eq_nil hnl] at hmem
        simp at hmem
      · exact hrnc r hpre q (by omega) hmem
    show j ≤ (extractState st r).deg ((kids st q).getD j 0) +
      (extractState st r).mrk ((kids st q).getD j 0)
    rw [extractState_deg, if_neg hyr, extractState_mrk, if_neg hv2]
    exact hpos q j hj

/-- `SlotOK` survives: promoted children were `r`'s children, hence live. -/
theorem extract_SlotOK (st : HState) (r : ℕ) (hpre : ExtractPre st r)
    (hrl : RootsLive st) (hslot : SlotOK st) : SlotOK (extractState st r) := by
  intro q hq v hv
  by_cases hqr : q = r
  · subst hqr
    rw [kids_extract_r] at hv
    simp at hv
  · rw [kids_extract_of_ne st r q hqr] at hv
    by_cases hvk : v ∈ kids st r
    · exact hslot r (hrl r hpre) v hvk
    · exact hslot q hq v hv

/-- `NILRoots` survives: remaining old roots keep `par = 0` (a root that was also `r`'s
child would have two parents), promoted children read out NIL. -/
theorem extract_NILRoots (st : HState) (r : ℕ) (hpre : ExtractPre st r)
    (hnrs : NILRoots st) (hnr : NILNotRoot st) (hpar : ParOK st) :
    NILRoots (extractState st r) := by
  intro s hs
  rw [extractState_roots] at hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨hsr, hsrne⟩ := List.mem_filter.mp hs
    have hv2 : s ∉ kids st r := by
      intro hv
      have h1 : st.par s = r := hpar r s hv
      have h2 : st.par s = 0 := hnrs s hsr
      exact hnr (h2 ▸ h1 ▸ hpre)
    rw [extractState_par_ne st r s hv2]
    exact hnrs s hsr
  · rw [extractState_par_child st r s hs]

/-- `NILSelf` survives: NIL is nobody's child. -/
theorem extract_NILSelf (st : HState) (r : ℕ) (hns : NILSelf st) (hnc : NILNotChild st) :
    NILSelf (extractState st r) := by
  show (extractState st r).par 0 = 0
  rw [extractState_par_ne st r 0 (hnc r)]
  exact hns

/-- `NILLeaf` survives: the splice never writes `deg 0` (`0 ≠ r`, `r` is a root). -/
theorem extract_NILLeaf (st : HState) (r : ℕ) (hpre : ExtractPre st r)
    (hnl : NILLeaf st) (hnr : NILNotRoot st) : NILLeaf (extractState st r) := by
  show (extractState st r).deg 0 = 0
  rw [extractState_deg, if_neg (show (0:ℕ) ≠ r from fun hc => hnr (hc ▸ hpre))]
  exact hnl

/-- `NILNotRoot` survives: the filtered list drops `r` only, and NIL is nobody's child. -/
theorem extract_NILNotRoot (st : HState) (r : ℕ) (hnn : NILNotRoot st)
    (hnc : NILNotChild st) : NILNotRoot (extractState st r) := by
  intro hc
  rw [extractState_roots] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hnn (List.mem_filter.mp hc).1
  · exact hnc r hc

/-- `NILNotChild` survives: every list is either emptied or untouched, and NIL was in
none of them. -/
theorem extract_NILNotChild (st : HState) (r : ℕ) (hnc : NILNotChild st) :
    NILNotChild (extractState st r) := by
  intro q hv
  by_cases hqr : q = r
  · subst hqr
    rw [kids_extract_r] at hv
    simp at hv
  · rw [kids_extract_of_ne st r q hqr] at hv
    exact hnc q hv

/-- `RootNotChild` survives: old roots are in no non-NIL list (the old fact), promoted
children are only in `r`'s emptied list. -/
theorem extract_RootNotChild (st : HState) (r : ℕ) (hpar : ParOK st)
    (hrnc : RootNotChild st) (hnc : NILNotChild st) : RootNotChild (extractState st r) := by
  intro s hs q hq0 hv
  rw [extractState_roots] at hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨hsr, _⟩ := List.mem_filter.mp hs
    by_cases hqr : q = r
    · subst hqr
      rw [kids_extract_r] at hv
      simp at hv
    · rw [kids_extract_of_ne st r q hqr] at hv
      exact hrnc s hsr q hq0 hv
  · have hs0 : s ≠ 0 := by
      intro hc
      subst hc
      exact hnc r hs
    by_cases hqr : q = r
    · subst hqr
      rw [kids_extract_r] at hv
      simp at hv
    · have hv2 : s ∈ kids (extractState st r) q := hv
      rw [kids_extract_of_ne st r q hqr] at hv
      have hparOK := extract_ParOK st r hpar
      have h1 : (extractState st r).par s = q := hparOK q s hv2
      have h2 : (extractState st r).par s = 0 := extractState_par_child st r s hs
      have hqreq : q = 0 := by
        rw [← h1]
        exact h2
      exact hq0 hqreq

/-- `RootsLive` survives: remaining roots are live, promoted children were `r`'s
children, hence live. -/
theorem extract_RootsLive (st : HState) (r : ℕ) (hpre : ExtractPre st r)
    (hrl : RootsLive st) (hslot : SlotOK st) : RootsLive (extractState st r) := by
  intro s hs
  rw [extractState_roots] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hrl s (List.mem_filter.mp hs).1
  · exact hslot r (hrl r hpre) s hs

/-- `Acyc` survives, by the cut's dichotomy: a `par'`-walk either reaches one of `r`'s
promoted children (and dies at NIL), or is an old walk all the way (handled by the old
`Acyc`). -/
theorem extract_Acyc (st : HState) (r : ℕ) (hpre : ExtractPre st r)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st) :
    Acyc (extractState st r) := by
  have f0 : (extractState st r).par 0 = 0 := by
    rw [extractState_par_ne st r 0 (hnc r)]
    exact hns
  have fzero : ∀ k : ℕ, (extractState st r).par^[k] 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, f0]
  intro v j hj heq
  by_cases hhit : ∃ m, m < j ∧ (extractState st r).par^[m] v ∈ kids st r
  · obtain ⟨m, hmj, hmc⟩ := hhit
    have hstep : (extractState st r).par^[m + 1] v = 0 := by
      rw [Function.iterate_succ_apply', extractState_par_child st r _ hmc]
    by_cases hjm : j = m + 1
    · rw [hjm] at heq
      rw [hstep] at heq
      exact heq.symm
    · have hj2 : m + 1 ≤ j := by omega
      rw [show j = j - (m + 1) + (m + 1) from by omega, Function.iterate_add_apply, hstep,
        fzero] at heq
      exact heq.symm
  · have hall : ∀ i, i ≤ j → (extractState st r).par^[i] v = (st.par)^[i] v := by
      intro i hi
      induction i with
      | zero => rfl
      | succ k ih =>
        have hlt : k < j := by omega
        have hikj : k ≤ j := by omega
        have hkne : (st.par)^[k] v ∉ kids st r := by
          intro hc
          rw [← ih hikj] at hc
          exact hhit ⟨k, hlt, hc⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hikj,
          extractState_par_ne st r _ hkne]
    rw [hall j (le_refl j)] at heq
    exact hac v j hj heq

/-- `RingOK` survives: the extracted root's ring is vacuous (`deg r = 0`), every other
ring is untouched (`rgt`/`lft` are never written). -/
theorem extract_RingOK (st : HState) (r : ℕ) (hrk : RingOK st) :
    RingOK (extractState st r) := by
  intro q
  by_cases hqr : q = r
  · subst hqr
    left
    simp [extractState]
  · rcases hrk q with h0 | hring
    · left
      rw [extractState_deg, if_neg hqr]
      exact h0
    · right
      have h1 : (extractState st r).deg q = st.deg q := by
        rw [extractState_deg, if_neg hqr]
      have h2 : (extractState st r).chd q = st.chd q := by
        rw [extractState_chd, if_neg hqr]
      have h3 : (extractState st r).rgt = st.rgt := rfl
      have h4 : (extractState st r).lft = st.lft := rfl
      rw [h1, h2, h3, h4]
      exact hring

end Submission.FibHeapExtractMin
