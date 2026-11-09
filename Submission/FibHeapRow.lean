/-
THE ROW: the decrease-key and extract-min aggregates, assembled.

**Fredman–Tarjan 1987.  Bound theirs; formalization ours.**

Accounting boundary (stated, not papered — the FibHeapMeasure /
FibHeapAmortized headers' language carried to the row): the row's
decrease-key half is the *clearing* discipline (`DkRunClear` — the
CLRS-write cascade landed in the Measure lane), whose per-op bound is
constant (`count * 5` potential; `count * (D0 + 6K + D1)` scaled — the
honest-6K note in `DkRunClear.potential_scaled_ft`: the fresh-parent
run re-banks a mark at every cut, so the unit carries the cut's rise).
The transfer-discipline run (`DkRun`, `count * (st.n + 5)`) is kept
alongside as the seam's other side.  The transfer lane's `CascadeMarks`
ledger remains the accounting boundary between them.  The extract-min
half runs at the rank-cap class (the splice + the consolidation walk
both `rankCap st.n`-bounded — the recount below; the machine
degree-strictness is the named link-time clause `DegOK`
(`FibHeapRefine`, wound 2125609385), pushed to the extract state by the
unconditional `extract_DegOK`).
-/
import Submission.FibHeapAmortized
import Submission.FibHeapMeasure
import Submission.FibHeapDepth
import Submission.FibHeapCascade
import Submission.FibHeapPop

namespace Submission.FibHeapRow

open Submission.FibHeapAmortized Submission.FibHeapMeasure Submission.FibHeapDepth
open Submission.FibHeapExtractMin
open Submission.FibHeapRefine
open Submission.FibHeapCascade Submission.FibHeapPop
open Submission.FibHeapLink Submission.FibHeapSupport

/-- **The row, decrease-key half.**  A capped run of `m = s.count`
decrease-keys raises the potential by at most `m · (L + 5)` — the
per-op bounds telescope (M5), the cap `L` is the walk bound's output
(M3: `walkUp_len_le_size`, `L ≤ st.n`-class once the LiveDistinct
bridge lands). -/
theorem row_decreaseKey {L : ℕ} {st : HState} (s : DkRun L st) :
    machinePotential s.last ≤ machinePotential st + s.count * (L + 5) :=
  DkRun.potential_cap s

/-- **The row, clearing decrease-key half.**  The per-op bound is CONSTANT
(`+5`: the cut's `+3` plus the cascade's stop `+2`) — independent of the
cascade lengths and the live size.  This is the `n log` form's decrease-key
half: the transfer `DkRun`'s `count * (L + 5)` grows with the live size
through `L`; the clearing `DkRunClear` does not.  The scaled
`D0 + 3K + D1` form (via `decrease_amortized_clrs`'s ledger) needs the
`FibHeapDynamic` `CascadeMarks` bridge re-point — the named tail item. -/
theorem row_decreaseKeyClear {L : ℕ} {st : HState} (s : DkRunClear L st) :
    machinePotential s.last ≤ machinePotential st + s.count * 5 :=
  DkRunClear.potential_clrs s

/-- **The row, extract-min half (witness level).**  The extract-min
witness raises the potential by exactly one (M4b's `extract_potential`).
The generalization to an arbitrary extract-min operation — the per-op
`+1` as a lemma over a general state — is the named next step; it is
not claimed here. -/
theorem row_extractMin_witness :
    machinePotential (extractState extractPreSt 3) = machinePotential extractPreSt + 1 :=
  extract_potential

/- **The row's sequential total over matched states.**  Landed 2026-11-09:
the decrease-key half runs at `L := st.n` (`DkRun st.n` — the per-step
`chain.length ≤ L` witnesses are the walk bound's output,
`FibHeapDepth.walkUp_len_le_n`'s class) and telescopes to
`m · (st.n + 5)`; the extract-min half runs on the run's final state
(matched by construction) and adds its own additive seam — the splice
`(kids r).length` plus the consolidation walk `chain.length` plus two.
The seam is left explicit: folding `(kids r).length` into `st.n`-class
needs the rank-cap lane (`degree_le_rankCap_of_machine`), which is the
stated accounting boundary.  The `ChainOk → WalkUp` lift that turns a
cascade witness into the capped walk (cut/promote only remove edges:
`kids_promote_unchanged` for `q ≠ z`, `kids_promote` +
`List.eraseIdx_sublist` at the promoted parent) is the remaining cell. -/
theorem row_sequential {st : HState} (s : DkRun st.n st) (r : ℕ)
    (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain (extractState s.last r) (extractState s.last r).n chain) :
    machinePotential (cascadeRun (extractState s.last r) chain stop)
      ≤ machinePotential st + s.count * (st.n + 5)
        + ((kids s.last r).length + chain.length + 2) := by
  have h1 : machinePotential s.last ≤ machinePotential st + s.count * (st.n + 5) :=
    DkRun.potential_cap s
  have h2 := extractMin_pop_potential s.last r chain stop hmc
  simp only [machinePotential] at *
  omega

/-- **The row's sequential total, caps machine-derived.**  The extract seam's
consolidation walk is a `Cascade` witness: `cascade_walkUp` lifts it to a
`WalkUp` over the extract state and `walkUp_len_le_n` folds `chain.length`
into the `st.n` class.  The extract state's invariant bundle is discharged
by the `extract_*` preservation suite (`extract_ParOK`, `extract_RingOK`,
`extract_SlotOK`, `extract_ParSlot`, `extract_NILSelf`, `extract_Acyc`,
`extract_NILLeaf`, `extract_KidsNodup`) from the start state's own bundle;
the `(kids r).length` term stays the stated rank-cap boundary. -/
theorem row_sequential_capped {st : HState} (s : DkRun st.n st) (r : ℕ)
    (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain (extractState s.last r) (extractState s.last r).n chain)
    {y : ℕ}
    (hC : Cascade (extractState s.last r) y chain)
    (hpar : ParOK (extractState s.last r)) (hrk : RingOK (extractState s.last r))
    (hslot : SlotOK (extractState s.last r)) (hps : ParSlot (extractState s.last r))
    (hs : NILSelf (extractState s.last r)) (hac : Acyc (extractState s.last r))
    (hnl : NILLeaf (extractState s.last r)) (hnd : ∀ q, KidsNodup (extractState s.last r) q) :
    machinePotential (cascadeRun (extractState s.last r) chain stop)
      ≤ machinePotential st + s.count * (st.n + 5)
        + ((kids s.last r).length + st.n + 2) := by
  have h1 := row_sequential s r chain stop hmc
  have hsn : (extractState s.last r).n = st.n := by
    rw [extractState_n, DkRun.last_n]
  have h2 := cascade_len_le_n st hsn hpar hrk hslot hps hs hac hnl hnd hC
  simp only [machinePotential] at *
  omega

/-- **The rank-cap plug.**  `degree_le_rankCap_of_machine` instantiated at the
run's final state — where `r` still carries its children — bounds the splice
by the log form: its `Support` premise is `support_of_machine` (the
LiveDistinct bridge), the live-size premise rides `DkRun.last_n`, and the
extract-state bundle in `row_sequential_rankCap` is this same machine bundle
pushed through the `extract_*` preservation suite. -/
theorem extract_kids_le_rankCap {st : HState} (s : DkRun st.n st) (r : ℕ)
    (hpre : ExtractPre s.last r) (hrl : RootsLive s.last) (hnn : NILNotRoot s.last)
    (hpar : ParOK s.last) (hslot : SlotOK s.last) (hps : ParSlot s.last)
    (hs : NILSelf s.last) (hac : Acyc s.last) (hnl : NILLeaf s.last) (hm : MarkOK s.last)
    (hpos : PosOK s.last) (hnd : ∀ q, KidsNodup s.last q) :
    (kids s.last r).length ≤ FibHeapAccounting.rankCap st.n := by
  have hrn : r < s.last.n := hrl r hpre
  have hr0 : r ≠ 0 := fun hc => hnn (by rw [← hc]; exact hpre)
  have hcap := FibHeapAcyclic.degree_le_rankCap_of_machine s.last hpar hslot hps hs hac hnl hm
    hpos hrn hr0 (support_of_machine s.last hpar hac hnl hnd hslot hrn)
  rw [DkRun.last_n] at hcap
  rwa [kids_length]

/-- **The row's sequential total at the log-splice form.**  The seam's splice
term is the rank cap (`extract_kids_le_rankCap`): the CLRS log bound on the
extracted root's child count, machine-derived end to end.  The extract-state
bundle is the `s.last` bundle pushed through `extract_*`. -/
theorem row_sequential_rankCap {st : HState} (s : DkRun st.n st) (r : ℕ)
    (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain (extractState s.last r) (extractState s.last r).n chain)
    {y : ℕ} (hC : Cascade (extractState s.last r) y chain)
    (hpar : ParOK s.last) (hrk : RingOK s.last) (hslot : SlotOK s.last)
    (hps : ParSlot s.last) (hs : NILSelf s.last) (hac : Acyc s.last) (hnl : NILLeaf s.last)
    (hm : MarkOK s.last) (hpos : PosOK s.last) (hnd : ∀ q, KidsNodup s.last q)
    (hnc : NILNotChild s.last) (hrnc : RootNotChild s.last)
    (hrl : RootsLive s.last) (hnn : NILNotRoot s.last)
    (hpre : ExtractPre s.last r) :
    machinePotential (cascadeRun (extractState s.last r) chain stop)
      ≤ machinePotential st + s.count * (st.n + 5)
        + (FibHeapAccounting.rankCap st.n + st.n + 2) := by
  have hsn : (extractState s.last r).n = st.n := by rw [extractState_n, DkRun.last_n]
  have hr0 : r ≠ 0 := fun hc => hnn (by rw [← hc]; exact hpre)
  have hcap := extract_kids_le_rankCap s r hpre hrl hnn hpar hslot hps hs hac hnl hm hpos hnd
  -- the extract-state bundle
  have hpar' := extract_ParOK s.last r hpar
  have hrk' := extract_RingOK s.last r hrk
  have hslot' := extract_SlotOK s.last r hpre hrl hslot
  have hps' := extract_ParSlot s.last r hps
  have hs' := extract_NILSelf s.last r hs hnc
  have hac' := extract_Acyc s.last r hpre hnc hs hac
  have hnl' := extract_NILLeaf s.last r hpre hnl hnn
  have hnd' := extract_KidsNodup s.last r hnd
  have h1 := row_sequential s r chain stop hmc
  have h2 := cascade_len_le_n st hsn hpar' hrk' hslot' hps' hs' hac' hnl' hnd' hC
  simp only [machinePotential] at *
  omega

/- Fredman–Tarjan 1987.  Bound theirs; formalization ours.  The CLRS
transfer seam above is the stated accounting boundary. -/

/-! ## The recount: cascade walks are rankCap-bounded -/

/-- **The recount.**  A `WalkUp` cascade over a state with the machine
rank-cap bundle is rankCap-bounded: the walk climbs (degree-strict edges),
so its length plus the start's degree fits under the cap — per-node
`degree_le_rankCap_of_machine` (Support via `support_of_machine`; NIL slot
0's degree is zero, `NILLeaf`).  `hmono` is the walk climb, supplied from
the machine's link-time clause `DegOK` (wound 2125609385: PosOK's ldeg
ordering lower-bounds child degrees by position and gives no
parent-strictness; the strictness is the link-time clause itself, the
machine `InvOK` carry — a modeled discipline constraint, named in
`FibHeapRefine.DegOK`, not a reachable-state theorem). -/
theorem recount_len_le {st : HState} {y : ℕ} {chain : List (ℕ × ℕ)}
    (hmono : ∀ a b : ℕ, a ∈ kids st b → st.deg a < st.deg b)
    (hpar : ParOK st) (hslot : SlotOK st) (hps : ParSlot st) (hs : NILSelf st)
    (hac : Acyc st) (hnl : NILLeaf st) (hm : MarkOK st) (hpos : PosOK st)
    (hnd : ∀ q, KidsNodup st q)
    (hW : WalkUp st y chain) (hy : y < st.n) :
    chain.length + st.deg y ≤ FibHeapAccounting.rankCap st.n + 1 := by
  have hcap : ∀ p, p < st.n → st.deg p ≤ FibHeapAccounting.rankCap st.n + 1 := by
    intro p hpv
    by_cases hp0 : p = 0
    · subst hp0
      have h0 : st.deg 0 = 0 := hnl
      omega
    · exact Nat.le_succ_of_le
        (FibHeapAcyclic.degree_le_rankCap_of_machine st hpar hslot hps hs hac hnl hm
          hpos hpv hp0 (support_of_machine st hpar hac hnl hnd hslot hpv))
  revert hy
  induction hW with
  | nil y =>
    intro hy
    have := hcap y hy
    simp only [List.length_nil]
    omega
  | @cons y z rest hk hrest ih =>
    intro hy
    have hpar' : st.par y = z := walkUp_par hpar hk
    have hz : z < st.n := by rw [← hpar']; exact hps y hy
    have hmono' : st.deg y + 1 ≤ st.deg z := Nat.succ_le_of_lt (hmono y z hk)
    have hih := ih hz
    simp only [List.length_cons]
    omega

/-- The recount, cap form: with a non-leaf start (a cascading-cut's cut node
has a parent, so its degree is positive) the walk's length is at most the
rank cap — the decrease-key half's log cap, `L := rankCap st.n`. -/
theorem recount_len_le_rankCap {st : HState} {y : ℕ} {chain : List (ℕ × ℕ)}
    (hmono : ∀ a b : ℕ, a ∈ kids st b → st.deg a < st.deg b)
    (hpar : ParOK st) (hslot : SlotOK st) (hps : ParSlot st) (hs : NILSelf st)
    (hac : Acyc st) (hnl : NILLeaf st) (hm : MarkOK st) (hpos : PosOK st)
    (hnd : ∀ q, KidsNodup st q)
    (hW : WalkUp st y chain) (hy : y < st.n) (hy0 : 0 < st.deg y) :
    chain.length ≤ FibHeapAccounting.rankCap st.n := by
  have h := recount_len_le hmono hpar hslot hps hs hac hnl hm hpos hnd hW hy
  omega

/-! ## The row: the `n log ; n log` form -/

/-- **The row, clearing decrease-key half (scaled).**  The machine's FT
per-op charge `D0 + 6K + D1` — the lift's fold-segment charge
`D0 + 3K + D1` plus the cut's `+3K` rise — telescoped over the capped run
(`DkRunClear.potential_scaled_ft`).  The honest-6K note is carried there. -/
theorem row_decreaseKeyClear_scaled {K D0 D1 : ℕ} (hK : D1 ≤ K) {L : ℕ} {st : HState}
    (s : DkRunClear L st) :
    FibHeapAccounting.scaledPotential K s.last.roots.length (machineMarks s.last)
      ≤ FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
        + s.count * (D0 + 6 * K + D1) :=
  DkRunClear.potential_scaled_ft hK s

/-- **The row: `n log ; n log`.**  `m = s.count` decrease-keys (the clearing
discipline, cascade cap `rankCap st.n` — `L` instantiated at the recount's
output) then one extract-min with its consolidation walk: the potential rise
is `m · 5` — constant per op, the `n log` decrease-key half — plus the
extract seam with BOTH walk terms at the rank cap: the splice
(`(kids r).length`, the machine rank cap at the run's final state) and the
consolidation walk (`recount_len_le_rankCap` discharged internally over the
extract-state bundle — `extract_PosOK` supplies its `PosOK` piece;
`hy0` is the program fact that the cascade starts at the cut node's
parent, which retains a child, so the recount's non-leaf premise holds).
The walk climb enters as `hdeg : DegOK s.last` — the machine's named
link-time clause (wound 2125609385), pushed to the extract state by
`extract_DegOK` *inside the row* (unconditional: the splice deletes edges
only).  The clause is a modeled discipline constraint named in
`FibHeapRefine.DegOK`, the static form of the link-time discipline exactly
as `FibHeapDynamic.InvOK` is on the abstract forest; its inductive step is
the link (`link_DegOK`), its documented break is the two-loss cascade.
FT-1987: bound theirs, formalization ours.  The CLRS/transfer seam is the
stated accounting boundary (the transfer run keeps its `count * (st.n + 5)`
form; the honest 6K charge note lives in `DkRunClear.potential_scaled_ft`). -/
theorem row_nlog {st : HState} (s : DkRunClear (FibHeapAccounting.rankCap st.n) st)
    (r : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain (extractState s.last r) (extractState s.last r).n chain)
    (hpre : ExtractPre s.last r) (hrl : RootsLive s.last) (hnn : NILNotRoot s.last)
    (hpar : ParOK s.last) (hslot : SlotOK s.last) (hps : ParSlot s.last)
    (hs : NILSelf s.last) (hac : Acyc s.last) (hnl : NILLeaf s.last)
    (hm : MarkOK s.last) (hpos : PosOK s.last) (hnd : ∀ q, KidsNodup s.last q)
    (hnc : NILNotChild s.last) (hrnc : RootNotChild s.last)
    {y : ℕ} (hW : WalkUp (extractState s.last r) y chain)
    (hyw : y < (extractState s.last r).n)
    (hy0 : 0 < (extractState s.last r).deg y)
    (hdeg : DegOK s.last) :
    machinePotential (cascadeRun (extractState s.last r) chain stop)
      ≤ machinePotential st + s.count * 5
        + (2 * FibHeapAccounting.rankCap st.n + 2) := by
  have hlastn : s.last.n = st.n := DkRunClear.last_n s
  -- the decrease-key half
  have h1 : machinePotential s.last ≤ machinePotential st + s.count * 5 :=
    DkRunClear.potential_clrs s
  -- the extract seam
  have h2 := extractMin_pop_potential s.last r chain stop hmc
  -- the splice at the cap (the s.last bundle, `s.last.n = st.n`)
  have hrn : r < s.last.n := hrl r hpre
  have hr0 : r ≠ 0 := fun hc => hnn (by rw [← hc]; exact hpre)
  have hcap := FibHeapAcyclic.degree_le_rankCap_of_machine s.last hpar hslot hps hs hac
    hnl hm hpos hrn hr0 (support_of_machine s.last hpar hac hnl hnd hslot hrn)
  rw [hlastn] at hcap
  have hkids : (kids s.last r).length ≤ FibHeapAccounting.rankCap st.n := by
    rw [kids_length]; exact hcap
  -- the consolidation walk at the cap: the recount over the extract-state bundle
  have hpar' := extract_ParOK s.last r hpar
  have hslot' := extract_SlotOK s.last r hpre hrl hslot
  have hps' := extract_ParSlot s.last r hps
  have hs' := extract_NILSelf s.last r hs hnc
  have hac' := extract_Acyc s.last r hpre hnc hs hac
  have hnl' := extract_NILLeaf s.last r hpre hnl hnn
  have hnd' := extract_KidsNodup s.last r hnd
  have hm' := extract_MarkOK s.last r hm
  have hpos' := extract_PosOK s.last r hpre hpar hrnc hnl hpos
  have hmono := extract_DegOK s.last r hdeg
  have hchain : chain.length ≤ FibHeapAccounting.rankCap st.n := by
    have h := recount_len_le_rankCap hmono hpar' hslot' hps' hs' hac' hnl' hm' hpos'
      hnd' hW hyw hy0
    rw [extractState_n, hlastn] at h
    exact h
  simp only [machinePotential] at *
  omega

end Submission.FibHeapRow
