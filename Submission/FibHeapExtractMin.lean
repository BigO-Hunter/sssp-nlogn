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

/-! ## The consolidation fold -/

/-- The consolidation pass: each head pair `(c, p)` melds the promoted child `c`
under the root `p` (the merge splice), until the caller-supplied pairing is
exhausted.  The fold runs on the *running* state, exactly as `cascadeRun` does. -/
def extractRun (st : HState) : List (ℕ × ℕ) → HState
  | [] => st
  | (c, p) :: rest => extractRun (mergeState st c p) rest

/-- One cell's premises: the merge's own preconditions on the state that cell
actually runs in, and the rest of the chain on the state *after* that merge. -/
def ExtractOk (st : HState) : List (ℕ × ℕ) → Prop
  | [] => True
  | (c, p) :: rest => MergePre st c p ∧ ExtractOk (mergeState st c p) rest

/-- **The extract-min program**: promote the minimum root's children to the root
list, then consolidate. -/
def extractMin (st : HState) (r : ℕ) (chain : List (ℕ × ℕ)) : HState :=
  extractRun (extractState st r) chain

/-! ## The fold lemmas: the bundle climbs the consolidation pass -/

theorem extractRun_MarkOK (st : HState) (chain : List (ℕ × ℕ))
    (hm : MarkOK st) (hok : ExtractOk st chain) : MarkOK (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hm
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_markOK st c p hm) hrest

theorem extractRun_ParSlot (st : HState) (chain : List (ℕ × ℕ))
    (hps : ParSlot st) (hrl : RootsLive st) (hok : ExtractOk st chain) :
    ParSlot (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hps
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_parSlot st c p hpre hps hrl)
      (merge_RootsLive st c p hpre hrl) hrest

theorem extractRun_ParOK (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hac : Acyc st)
    (hns : NILSelf st) (hok : ExtractOk st chain) :
    ParOK (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hpar
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns) hrest

theorem extractRun_KidsNodup (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st) (hnr : NILNotRoot st)
    (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st) (hac : Acyc st)
    (hns : NILSelf st) (hnd : ∀ q, KidsNodup st q) (hok : ExtractOk st chain) :
    ∀ q, KidsNodup (extractRun st chain) q := by
  induction chain generalizing st with
  | nil => exact hnd
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns)
      (merge_kidsNodup st c p hpar hrnc hnr hrk hpre hnl hnd) hrest

theorem extractRun_PosOK (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st) (hnr : NILNotRoot st)
    (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st) (hac : Acyc st)
    (hns : NILSelf st) (hpos : PosOK st) (hok : ExtractOk st chain) :
    PosOK (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hpos
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns)
      (merge_posOK st c p hpar hrnc hnr hrk hpre hnl hpos) hrest

theorem extractRun_SlotOK (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st) (hnr : NILNotRoot st)
    (hnrs : NILRoots st) (hrk : RingOK st) (hrl : RootsLive st) (hnl : NILLeaf st)
    (hac : Acyc st) (hns : NILSelf st) (hslot : SlotOK st) (hok : ExtractOk st chain) :
    SlotOK (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hslot
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_RootsLive st c p hpre hrl)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns)
      (merge_slotOK st c p hpar hrnc hnr hrk hpre hrl hnl hslot) hrest

theorem extractRun_Acyc (st : HState) (chain : List (ℕ × ℕ))
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hns : NILSelf st) (hac : Acyc st)
    (hok : ExtractOk st chain) : Acyc (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hac
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs) (merge_NILSelf st c p hpre hnr hns)
      (merge_acyc st c p hnr hpre hnrs hns hac) hrest

theorem extractRun_NILRoots (st : HState) (chain : List (ℕ × ℕ))
    (hnrs : NILRoots st) (hok : ExtractOk st chain) :
    NILRoots (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hnrs
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_NILRoots st c p hnrs) hrest

theorem extractRun_NILSelf (st : HState) (chain : List (ℕ × ℕ))
    (hnr : NILNotRoot st) (hns : NILSelf st) (hok : ExtractOk st chain) :
    NILSelf (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hns
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_NILNotRoot st c p hnr)
      (merge_NILSelf st c p hpre hnr hns) hrest

theorem extractRun_NILNotRoot (st : HState) (chain : List (ℕ × ℕ))
    (hnn : NILNotRoot st) (hok : ExtractOk st chain) :
    NILNotRoot (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hnn
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_NILNotRoot st c p hnn) hrest

theorem extractRun_NILLeaf (st : HState) (chain : List (ℕ × ℕ))
    (hnr : NILNotRoot st) (hnl : NILLeaf st) (hok : ExtractOk st chain) :
    NILLeaf (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hnl
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_NILNotRoot st c p hnr)
      (merge_NILLeaf st c p hpre hnr hnl) hrest

theorem extractRun_NILNotChild (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st) (hnr : NILNotRoot st)
    (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st) (hac : Acyc st)
    (hns : NILSelf st) (hnc : NILNotChild st) (hok : ExtractOk st chain) :
    NILNotChild (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hnc
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns)
      (merge_NILNotChild st c p hpar hrnc hnr hrk hpre hnl hnc) hrest

theorem extractRun_RootNotChild (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st) (hnr : NILNotRoot st)
    (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st) (hac : Acyc st)
    (hns : NILSelf st) (hok : ExtractOk st chain) :
    RootNotChild (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hrnc
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns) hrest

theorem extractRun_RootsLive (st : HState) (chain : List (ℕ × ℕ))
    (hrl : RootsLive st) (hok : ExtractOk st chain) :
    RootsLive (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hrl
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p) (merge_RootsLive st c p hpre hrl) hrest

theorem extractRun_RingOK (st : HState) (chain : List (ℕ × ℕ))
    (hpar : ParOK st) (hrnc : RootNotChild st) (hnr : NILNotRoot st)
    (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st) (hac : Acyc st)
    (hns : NILSelf st)
    (hok : ExtractOk st chain) : RingOK (extractRun st chain) := by
  induction chain generalizing st with
  | nil => exact hrk
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    obtain ⟨hpre, hrest⟩ := hok
    exact ih (mergeState st c p)
      (merge_parOK st c p hpar hrnc hnr hrk hpre hnl)
      (merge_RootNotChild st c p hpar hrnc hnr hrk hpre hnl)
      (merge_NILNotRoot st c p hnr)
      (merge_NILRoots st c p hnrs)
      (merge_RingOK st c p hpar hrnc hnr hnrs hrk hpre hnl hac)
      (merge_NILLeaf st c p hpre hnr hnl)
      (merge_acyc st c p hnr hpre hnrs hns hac)
      (merge_NILSelf st c p hpre hnr hns) hrest

/-! ## The program bridges: the bundle survives the whole extract-min -/

/-- Every premise the fold needs on the running state is produced by the extract
bundle; the bridges assemble them once. -/

theorem extractMin_MarkOK (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hm : MarkOK st) (hok : ExtractOk (extractState st r) chain) :
    MarkOK (extractMin st r chain) :=
  extractRun_MarkOK _ _ (extract_MarkOK st r hm) hok

theorem extractMin_ParSlot (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hps : ParSlot st) (hrl : RootsLive st)
    (hslot : SlotOK st) (hok : ExtractOk (extractState st r) chain) :
    ParSlot (extractMin st r chain) :=
  extractRun_ParSlot _ _ (extract_ParSlot st r hps)
    (extract_RootsLive st r hpre hrl hslot) hok

theorem extractMin_ParOK (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hok : ExtractOk (extractState st r) chain) :
    ParOK (extractMin st r chain) :=
  extractRun_ParOK _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc) hok

theorem extractMin_KidsNodup (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hnd : ∀ q, KidsNodup st q) (hok : ExtractOk (extractState st r) chain) :
    ∀ q, KidsNodup (extractMin st r chain) q :=
  extractRun_KidsNodup _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc)
    (extract_KidsNodup st r hnd) hok

theorem extractMin_PosOK (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st) (hpos : PosOK st)
    (hok : ExtractOk (extractState st r) chain) :
    PosOK (extractMin st r chain) :=
  extractRun_PosOK _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc)
    (extract_PosOK st r hpre hpar hrnc hnl hpos) hok

theorem extractMin_SlotOK (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hrl : RootsLive st)
    (hnl : NILLeaf st) (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hslot : SlotOK st) (hok : ExtractOk (extractState st r) chain) :
    SlotOK (extractMin st r chain) :=
  extractRun_SlotOK _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_RootsLive st r hpre hrl hslot)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc)
    (extract_SlotOK st r hpre hrl hslot) hok

theorem extractMin_Acyc (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hnr : NILNotRoot st) (hnrs : NILRoots st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hok : ExtractOk (extractState st r) chain) :
    Acyc (extractMin st r chain) :=
  extractRun_Acyc _ _ (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_NILSelf st r hns hnc)
    (extract_Acyc st r hpre hnc hns hac) hok

theorem extractMin_NILRoots (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hnrs : NILRoots st) (hnr : NILNotRoot st)
    (hpar : ParOK st) (hok : ExtractOk (extractState st r) chain) :
    NILRoots (extractMin st r chain) :=
  extractRun_NILRoots _ _ (extract_NILRoots st r hpre hnrs hnr hpar) hok

theorem extractMin_NILSelf (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hnn : NILNotRoot st) (hnc : NILNotChild st) (hns : NILSelf st)
    (hok : ExtractOk (extractState st r) chain) :
    NILSelf (extractMin st r chain) :=
  extractRun_NILSelf _ _ (extract_NILNotRoot st r hnn hnc)
    (extract_NILSelf st r hns hnc) hok

theorem extractMin_NILNotRoot (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hnn : NILNotRoot st) (hnc : NILNotChild st)
    (hok : ExtractOk (extractState st r) chain) :
    NILNotRoot (extractMin st r chain) :=
  extractRun_NILNotRoot _ _ (extract_NILNotRoot st r hnn hnc) hok

theorem extractMin_NILLeaf (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hnl : NILLeaf st) (hnr : NILNotRoot st)
    (hnc : NILNotChild st) (hok : ExtractOk (extractState st r) chain) :
    NILLeaf (extractMin st r chain) :=
  extractRun_NILLeaf _ _ (extract_NILNotRoot st r hnr hnc)
    (extract_NILLeaf st r hpre hnl hnr) hok

theorem extractMin_NILNotChild (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hok : ExtractOk (extractState st r) chain) :
    NILNotChild (extractMin st r chain) :=
  extractRun_NILNotChild _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc)
    (extract_NILNotChild st r hnc) hok

theorem extractMin_RootNotChild (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hok : ExtractOk (extractState st r) chain) :
    RootNotChild (extractMin st r chain) :=
  extractRun_RootNotChild _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc) hok

theorem extractMin_RootsLive (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hrl : RootsLive st) (hslot : SlotOK st)
    (hok : ExtractOk (extractState st r) chain) :
    RootsLive (extractMin st r chain) :=
  extractRun_RootsLive _ _ (extract_RootsLive st r hpre hrl hslot) hok

theorem extractMin_RingOK (st : HState) (r : ℕ) (chain : List (ℕ × ℕ))
    (hpre : ExtractPre st r) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hnrs : NILRoots st) (hrk : RingOK st) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hns : NILSelf st) (hac : Acyc st)
    (hok : ExtractOk (extractState st r) chain) :
    RingOK (extractMin st r chain) :=
  extractRun_RingOK _ _ (extract_ParOK st r hpar)
    (extract_RootNotChild st r hpar hrnc hnc)
    (extract_NILNotRoot st r hnr hnc)
    (extract_NILRoots st r hpre hnrs hnr hpar)
    (extract_RingOK st r hrk)
    (extract_NILLeaf st r hpre hnl hnr)
    (extract_Acyc st r hpre hnc hns hac)
    (extract_NILSelf st r hns hnc) hok

/-! ## The extract-min output witness -/

/-- The witness's pre-state: NIL at slot 0; the root slot 3 (the minimum to extract)
holds the two-child ring `[1, 2]`, where `2` carries child `5`; slot `4` is a bystander
root.  No marks anywhere. -/
def extractPreSt : HState where
  par := fun i => if i = 1 then 3 else if i = 2 then 3 else if i = 5 then 2 else 0
  chd := fun i => if i = 3 then 1 else if i = 2 then 5 else 0
  rgt := fun i => if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 0
  lft := fun i => if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 0
  deg := fun i => if i = 3 then 2 else if i = 2 then 1 else 0
  mrk := fun _ => 0
  roots := [4, 3]
  n := 6

/-- The intermediate state after the extraction of root `3` (before consolidation),
spelled out: promoted children are unmarked NIL-parented roots, the extracted slot is
dead, `2` keeps child `5`, the bystander root `4` is untouched. -/
def extracted : HState where
  par := fun i => if i = 5 then 2 else 0
  chd := fun i => if i = 2 then 5 else 0
  rgt := fun i => if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 0
  lft := fun i => if i = 1 then 2 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 0
  deg := fun i => if i = 2 then 1 else 0
  mrk := fun _ => 0
  roots := [4, 1, 2]
  n := 6

/-- Field bridges from the splice application to the literal state.  Eight small
equalities instead of one structure equality — the machine reads fields.  The
`kids`-membership is discharged by `kids_extractPreSt`, which must fire before
`extractPreSt` itself unfolds — the witness-lemma ordering rule this module keeps
re-learning. -/
@[simp] theorem kids_extractPreSt (q : ℕ) :
    kids extractPreSt q = if q = 3 then [1, 2] else if q = 2 then [5] else [] := by
  unfold kids
  by_cases hq3 : q = 3
  · subst hq3
    rfl
  · by_cases hq2 : q = 2
    · subst hq2
      rfl
    · simp [extractPreSt, hq3, hq2]

@[simp] theorem extracted_state_par (v : ℕ) :
    (extractState extractPreSt 3).par v = extracted.par v := by
  have hk : kids extractPreSt 3 = [1, 2] := kids_extractPreSt 3
  simp only [extractState, hk]
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> by_cases h5 : v = 5 <;>
    simp [extractPreSt, extracted, h1, h2, h3, h5]

@[simp] theorem extracted_state_chd (v : ℕ) :
    (extractState extractPreSt 3).chd v = extracted.chd v := by
  simp only [extractState]
  by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> simp [extractPreSt, extracted, h2, h3]

@[simp] theorem extracted_state_rgt (v : ℕ) :
    (extractState extractPreSt 3).rgt v = extracted.rgt v := by
  simp only [extractState]
  simp [extractPreSt, extracted]

@[simp] theorem extracted_state_lft (v : ℕ) :
    (extractState extractPreSt 3).lft v = extracted.lft v := by
  simp only [extractState]
  simp [extractPreSt, extracted]

@[simp] theorem extracted_state_deg (v : ℕ) :
    (extractState extractPreSt 3).deg v = extracted.deg v := by
  simp only [extractState]
  by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> simp [extractPreSt, extracted, h2, h3]

@[simp] theorem extracted_state_mrk (v : ℕ) :
    (extractState extractPreSt 3).mrk v = extracted.mrk v := by
  have hk : kids extractPreSt 3 = [1, 2] := kids_extractPreSt 3
  simp only [extractState, hk]
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> by_cases h3 : v = 3 <;> by_cases h5 : v = 5 <;>
    simp [extractPreSt, extracted, h1, h2, h3, h5]

@[simp] theorem extracted_state_roots :
    (extractState extractPreSt 3).roots = extracted.roots := by
  have hk : kids extractPreSt 3 = [1, 2] := kids_extractPreSt 3
  simp only [extractState, hk]
  simp [extractPreSt, extracted]

@[simp] theorem extracted_state_n : (extractState extractPreSt 3).n = extracted.n := rfl

@[simp] theorem extracted_roots : extracted.roots = [4, 1, 2] := rfl

@[simp] theorem extracted_deg (v : ℕ) :
    extracted.deg v = if v = 2 then 1 else 0 := rfl

@[simp] theorem extracted_mrk (v : ℕ) : extracted.mrk v = 0 := rfl

@[simp] theorem extracted_par (v : ℕ) :
    extracted.par v = if v = 5 then 2 else 0 := rfl

@[simp] theorem extracted_chd (v : ℕ) :
    extracted.chd v = if v = 2 then 5 else 0 := rfl

@[simp] theorem extracted_n : extracted.n = 6 := rfl

@[simp] theorem kids_extracted (q : ℕ) : kids extracted q = if q = 2 then [5] else [] := by
  unfold kids
  by_cases hq2 : q = 2
  · subst hq2
    simp [extracted, Function.iterate_one]
  · simp [extracted, hq2]

/-- The pre-state satisfies the bundle (direct, per the merge/cascade witnesses). -/
theorem w_MarkOK : MarkOK extractPreSt := by
  intro p
  simp [extractPreSt]

theorem w_ParSlot : ParSlot extractPreSt := by
  intro p hp
  by_cases h1 : p = 1 <;> by_cases h2 : p = 2 <;> by_cases h5 : p = 5 <;>
    simp [extractPreSt, h1, h2, h5] <;> omega

theorem w_ParOK : ParOK extractPreSt := by
  intro p v hv
  by_cases hp3 : p = 3
  · subst hp3
    rw [kids_extractPreSt] at hv
    simp at hv
    rcases hv with rfl | rfl <;> simp [extractPreSt]
  · by_cases hp2 : p = 2
    · subst hp2
      rw [kids_extractPreSt] at hv
      simp at hv
      rcases hv with rfl
      simp [extractPreSt]
    · rw [kids_extractPreSt] at hv
      simp [hp3, hp2] at hv

theorem w_KidsNodup : ∀ q, KidsNodup extractPreSt q := by
  intro q j k hjk hk
  by_cases hq3 : q = 3
  · subst hq3
    simp [extractPreSt] at hk
    rw [kids_extractPreSt] at ⊢
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · have hk0 : k = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hk0
      subst hj0
      omega
    · have hk1 : k = 1 := by omega
      have hj0 : j = 0 := by omega
      subst hk1
      subst hj0
      simp
  · by_cases hq2 : q = 2
    · subst hq2
      simp [extractPreSt] at hk
      rw [kids_extractPreSt] at ⊢
      exact absurd hjk (by omega)
    · simp [extractPreSt, hq3, hq2] at hk

theorem w_PosOK : PosOK extractPreSt := by
  intro q j hj
  by_cases hq3 : q = 3
  · subst hq3
    simp [extractPreSt] at hj
    rw [kids_extractPreSt] at ⊢
    simp at hj ⊢
    rcases Nat.lt_or_ge j 1 with hj0 | hj0
    · have hj00 : j = 0 := by omega
      subst hj00
      simp [ldeg, extractPreSt]
    · have hj1 : j = 1 := by omega
      subst hj1
      simp [ldeg, extractPreSt]
  · by_cases hq2 : q = 2
    · subst hq2
      simp [extractPreSt] at hj
      rw [kids_extractPreSt] at ⊢
      simp at hj ⊢
      have hj0 : j = 0 := by omega
      subst hj0
      simp [ldeg, extractPreSt]
    · simp [extractPreSt, hq3, hq2] at hj

theorem w_SlotOK : SlotOK extractPreSt := by
  intro p hp v hv
  by_cases hp3 : p = 3
  · subst hp3
    rw [kids_extractPreSt] at hv
    simp at hv
    rcases hv with rfl | rfl <;> simp [extractPreSt]
  · by_cases hp2 : p = 2
    · subst hp2
      rw [kids_extractPreSt] at hv
      simp at hv
      rcases hv with rfl
      simp [extractPreSt]
    · rw [kids_extractPreSt] at hv
      simp [hp3, hp2] at hv

theorem w_NILRoots : NILRoots extractPreSt := by
  intro r hr
  simp [extractPreSt] at hr
  rcases hr with rfl | rfl <;> simp [extractPreSt]

theorem w_NILSelf : NILSelf extractPreSt := rfl

theorem w_NILLeaf : NILLeaf extractPreSt := rfl

theorem w_NILNotRoot : NILNotRoot extractPreSt := by
  intro hc
  simp [extractPreSt] at hc

theorem w_NILNotChild : NILNotChild extractPreSt := by
  intro q hv
  rw [kids_extractPreSt] at hv
  by_cases hq3 : q = 3
  · subst hq3
    simp at hv
  · by_cases hq2 : q = 2
    · subst hq2
      simp at hv
    · simp [hq3, hq2] at hv

theorem w_RootNotChild : RootNotChild extractPreSt := by
  intro r hr q _ hv
  simp [extractPreSt] at hr
  rcases hr with rfl | rfl
  · rw [kids_extractPreSt] at hv
    by_cases hq3 : q = 3
    · subst hq3
      simp at hv
    · by_cases hq2 : q = 2
      · subst hq2
        simp at hv
      · simp [hq3, hq2] at hv
  · rw [kids_extractPreSt] at hv
    by_cases hq3 : q = 3
    · subst hq3
      simp at hv
    · by_cases hq2 : q = 2
      · subst hq2
        simp at hv
      · simp [hq3, hq2] at hv

theorem w_RootsLive : RootsLive extractPreSt := by
  intro r hr
  simp [extractPreSt] at hr
  rcases hr with rfl | rfl <;> simp [extractPreSt]

/-- Every walk dies at NIL within three steps: the orbits are `1→3→0`, `2→3→0`,
`5→2→3→0`, and NIL absorbs everything. -/
theorem w_death : ∀ v : ℕ, (extractPreSt.par)^[3] v = 0 := by
  intro v
  by_cases h0 : v = 0 <;> by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;>
    by_cases h3 : v = 3 <;> by_cases h4 : v = 4 <;> by_cases h5 : v = 5 <;>
    simp [extractPreSt, h0, h1, h2, h3, h4, h5, Function.iterate_succ_apply',
      Function.iterate_one, Function.iterate_zero_apply]

theorem w_Acyc : Acyc extractPreSt := by
  have f0 : extractPreSt.par 0 = 0 := rfl
  have fzero : ∀ k : ℕ, (extractPreSt.par)^[k] 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, f0]
  have hdead : ∀ v k : ℕ, 3 ≤ k → (extractPreSt.par)^[k] v = 0 := by
    intro v k hk
    have h3 := w_death v
    have he : (extractPreSt.par)^[k] v = (extractPreSt.par)^[3 + (k - 3)] v := by
      congr 1
      omega
    rw [he, Function.iterate_add_apply, w_death]
  -- no walk of positive length returns to its start unless the start is NIL
  have hnor : ∀ v k : ℕ, 0 < k → (extractPreSt.par)^[k] v = v → v = 0 := by
    intro v k hk hv
    rcases Nat.lt_or_ge k 3 with hk3 | hkge
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        by_cases hv0 : v = 0
        · exact hv0
        · by_cases hv1 : v = 1
          · subst hv1; simp [extractPreSt] at hv
          · by_cases hv2 : v = 2
            · subst hv2; simp [extractPreSt] at hv
            · by_cases hv3 : v = 3
              · subst hv3; simp [extractPreSt] at hv
              · by_cases hv4 : v = 4
                · subst hv4; simp [extractPreSt] at hv
                · by_cases hv5 : v = 5
                  · subst hv5; simp [extractPreSt] at hv
                  · simp [extractPreSt, hv0, hv1, hv2, hv3, hv4, hv5] at hv
                    exact hv.symm
      · have hk2 : k = 2 := by omega
        subst hk2
        by_cases hv0 : v = 0
        · exact hv0
        · by_cases hv1 : v = 1
          · subst hv1
            simp [extractPreSt, Function.iterate_succ_apply', Function.iterate_one] at hv
          · by_cases hv2 : v = 2
            · subst hv2
              simp [extractPreSt, Function.iterate_succ_apply', Function.iterate_one] at hv
            · by_cases hv3 : v = 3
              · subst hv3
                simp [extractPreSt, Function.iterate_succ_apply', Function.iterate_one] at hv
              · by_cases hv4 : v = 4
                · subst hv4
                  simp [extractPreSt, Function.iterate_succ_apply', Function.iterate_one] at hv
                · by_cases hv5 : v = 5
                  · subst hv5
                    simp [extractPreSt, Function.iterate_succ_apply', Function.iterate_one] at hv
                  · simp [extractPreSt, hv0, hv1, hv2, hv3, hv4, hv5,
                      Function.iterate_succ_apply', Function.iterate_one] at hv
                    exact hv.symm
    · have hd := hdead v k hkge
      omega
  intro x j hj heq
  have hv := hnor x j hj heq
  omega

theorem w_RingOK : RingOK extractPreSt := by
  intro q
  by_cases hq3 : q = 3
  · subst hq3
    right
    have hrgt1 : extractPreSt.rgt 1 = 2 := rfl
    have hrgt2 : extractPreSt.rgt 2 = 1 := rfl
    refine ⟨by simp [extractPreSt, Function.iterate_succ_apply', Function.iterate_one], ?_,
      by simp [extractPreSt]⟩
    have hchd3 : extractPreSt.chd 3 = 1 := rfl
    intro j k hj hk heq
    simp [extractPreSt] at hj hk
    have hj01 : j = 0 ∨ j = 1 := by omega
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hj01 with rfl | rfl <;> rcases hk01 with rfl | rfl <;>
      simp [Function.iterate_one, Function.iterate_zero_apply, hrgt1, hchd3] at heq <;>
      first | omega | exact absurd heq (by omega)
  · by_cases hq2 : q = 2
    · subst hq2
      right
      refine ⟨by simp [extractPreSt], ?_, by simp [extractPreSt]⟩
      have hchd2 : extractPreSt.chd 2 = 5 := rfl
      intro j k hj hk heq
      simp [extractPreSt] at hj hk
      have hj0 : j = 0 := by omega
      subst hj0
      have hk0 : k = 0 := by omega
      subst hk0
      simp [hchd2]
    · left
      show extractPreSt.deg q = 0
      simp [extractPreSt, hq3, hq2]

/-- The extraction's own preconditions. -/
theorem extractPreSt_pre : ExtractPre extractPreSt 3 := by
  show 3 ∈ extractPreSt.roots
  simp [extractPreSt]

/-- The consolidation cell: promoted child `2` (degree 1) melds under promoted
child `1` (degree 0), in the state the cell actually runs in. -/
theorem extractPreSt_ok : ExtractOk (extractState extractPreSt 3) [(2, 1)] := by
  refine ⟨?_, trivial⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · decide
  · simp

/-- The extraction of the minimum root `3`, followed by one consolidation cell:
promoted child `2` (degree 1) melds under promoted child `1` (degree 0). -/
def extractedMinState : HState := extractMin extractPreSt 3 [(2, 1)]

@[simp] theorem extractedMinState_par (v : ℕ) :
    extractedMinState.par v = if v = 2 then 1 else if v = 5 then 2 else 0 := by
  simp [extractedMinState, extractMin, extractRun, mergeState, extracted_par, extracted_mrk]

@[simp] theorem extractedMinState_deg (v : ℕ) :
    extractedMinState.deg v = if v = 1 then 1 else if v = 2 then 1 else 0 := by
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;> by_cases h5 : v = 5 <;>
    simp [extractedMinState, extractMin, extractRun, mergeState, extracted_deg,
      extracted_mrk, h1, h2, h5]

@[simp] theorem extractedMinState_chd (v : ℕ) :
    extractedMinState.chd v = if v = 1 then 2 else if v = 2 then 5 else 0 := by
  simp [extractedMinState, extractMin, extractRun, mergeState, extracted_chd]

@[simp] theorem extractedMinState_mrk (v : ℕ) : extractedMinState.mrk v = 0 := by
  simp [extractedMinState, extractMin, extractRun, mergeState, extracted_mrk]

@[simp] theorem extractedMinState_roots : extractedMinState.roots = [4, 1] := by
  simp [extractedMinState, extractMin, extractRun, mergeState, extracted_roots]

@[simp] theorem extractedMinState_n : extractedMinState.n = 6 := rfl

@[simp] theorem kids_extractedMinState (q : ℕ) :
    kids extractedMinState q = if q = 1 then [2] else if q = 2 then [5] else [] := by
  by_cases hq1 : q = 1
  · subst hq1
    have hd1 : extractedMinState.deg 1 = 1 := by simp
    unfold kids
    rw [hd1]
    simp [extracted_chd]
  · by_cases hq2 : q = 2
    · subst hq2
      have hd2 : extractedMinState.deg 2 = 1 := by simp
      unfold kids
      rw [hd2]
      simp [extracted_chd]
    · have hdq : extractedMinState.deg q = 0 := by simp [hq1, hq2]
      unfold kids
      rw [hdq]
      simp [hq1, hq2]

/-- The invariant bundle on the output — every predicate via the program bridges,
against the pre-state's directly-proven bundle.  The bridges are the discharge:
no per-predicate splice reasoning happens here. -/

theorem extractedMinState_MarkOK : MarkOK extractedMinState :=
  extractMin_MarkOK _ _ _ w_MarkOK extractPreSt_ok

theorem extractedMinState_ParSlot : ParSlot extractedMinState :=
  extractMin_ParSlot _ _ _ extractPreSt_pre w_ParSlot w_RootsLive w_SlotOK extractPreSt_ok

theorem extractedMinState_ParOK : ParOK extractedMinState :=
  extractMin_ParOK _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_NILLeaf w_NILNotChild w_NILSelf w_Acyc extractPreSt_ok

theorem extractedMinState_KidsNodup : ∀ q, KidsNodup extractedMinState q :=
  extractMin_KidsNodup _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_NILLeaf w_NILNotChild w_NILSelf w_Acyc w_KidsNodup extractPreSt_ok

theorem extractedMinState_PosOK : PosOK extractedMinState :=
  extractMin_PosOK _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_NILLeaf w_NILNotChild w_NILSelf w_Acyc w_PosOK extractPreSt_ok

theorem extractedMinState_SlotOK : SlotOK extractedMinState :=
  extractMin_SlotOK _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_RootsLive w_NILLeaf w_NILNotChild w_NILSelf w_Acyc w_SlotOK extractPreSt_ok

theorem extractedMinState_Acyc : Acyc extractedMinState :=
  extractMin_Acyc _ _ _ extractPreSt_pre w_ParOK w_NILNotRoot w_NILRoots w_NILNotChild
    w_NILSelf w_Acyc extractPreSt_ok

theorem extractedMinState_NILRoots : NILRoots extractedMinState :=
  extractMin_NILRoots _ _ _ extractPreSt_pre w_NILRoots w_NILNotRoot w_ParOK extractPreSt_ok

theorem extractedMinState_NILSelf : NILSelf extractedMinState :=
  extractMin_NILSelf _ _ _ w_NILNotRoot w_NILNotChild w_NILSelf extractPreSt_ok

theorem extractedMinState_NILNotRoot : NILNotRoot extractedMinState :=
  extractMin_NILNotRoot _ _ _ w_NILNotRoot w_NILNotChild extractPreSt_ok

theorem extractedMinState_NILLeaf : NILLeaf extractedMinState :=
  extractMin_NILLeaf _ _ _ extractPreSt_pre w_NILLeaf w_NILNotRoot w_NILNotChild extractPreSt_ok

theorem extractedMinState_NILNotChild : NILNotChild extractedMinState :=
  extractMin_NILNotChild _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_NILLeaf w_NILNotChild w_NILSelf w_Acyc extractPreSt_ok

theorem extractedMinState_RootNotChild : RootNotChild extractedMinState :=
  extractMin_RootNotChild _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_NILLeaf w_NILNotChild w_NILSelf w_Acyc extractPreSt_ok

theorem extractedMinState_RootsLive : RootsLive extractedMinState :=
  extractMin_RootsLive _ _ _ extractPreSt_pre w_RootsLive w_SlotOK extractPreSt_ok

theorem extractedMinState_RingOK : RingOK extractedMinState :=
  extractMin_RingOK _ _ _ extractPreSt_pre w_ParOK w_RootNotChild w_NILNotRoot w_NILRoots
    w_RingOK w_NILLeaf w_NILNotChild w_NILSelf w_Acyc extractPreSt_ok

/-- The output's abstraction is the three-node tree over slots `1`, `2`, `5`. -/
theorem extractedMinState_Support : Support extractedMinState (extractedMinState.n + 1) 1 := by
  refine ⟨{1, 2, 5}, ?_, ?_⟩
  · have hshape : treeOf extractedMinState (extractedMinState.n + 1) 1
        = FibHeapForest.Tree.node 1
            [FibHeapForest.Child.mk (treeOf extractedMinState 6 2) (ldeg extractedMinState 2)
              (extractedMinState.mrk 2)] := by
      simp [treeOf, kids_extractedMinState]
    rw [hshape, FibHeapForest.size_node, FibHeapForest.sizeSum]
    simp [FibHeapForest.Child.size, FibHeapForest.Child.tree, FibHeapForest.size_node,
      FibHeapForest.sizeSum, treeOf, kids_extractedMinState]
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp

/-- **The capstone applied to the post-extract state.**  Extract-min keeps the machine
inside the invariant set, so the rank cap applies to the consolidation winner. -/
theorem extractedMinState_capstone :
    extractedMinState.deg 1 ≤ FibHeapAccounting.rankCap extractedMinState.n := by
  have hsup := extractedMinState_Support
  have hpn : extractedMinState.n + 1 = 7 := by rw [extractedMinState_n]
  rw [extractedMinState_n] at hsup ⊢
  exact degree_le_rankCap_zero extractedMinState extractedMinState_ParOK
    extractedMinState_SlotOK extractedMinState_ParSlot extractedMinState_KidsNodup
    extractedMinState_Acyc extractedMinState_NILSelf extractedMinState_NILLeaf
    extractedMinState_NILNotChild extractedMinState_MarkOK extractedMinState_PosOK
    (by simp) (by simp) hsup

end Submission.FibHeapExtractMin
