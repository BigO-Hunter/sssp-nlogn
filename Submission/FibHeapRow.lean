/-
THE ROW: the decrease-key and extract-min aggregates, assembled.

**Fredman–Tarjan 1987.  Bound theirs; formalization ours.**

Accounting boundary (stated, not papered — the FibHeapMeasure /
FibHeapAmortized headers' language carried to the row): this lane's
cascade is the *transfer* mark discipline, so the decrease-key per-op
bound is len-linear and the row's cap is the Size-range `B` (≤ `st.n`
once the `LiveDistinct (treeOf …)` bridge lands — the `ids` fold's
child-subtree disjointness is the one unproven link).  The CLRS
clear-per-step discipline would give the *c-independent* corollary
(`Φ' + c ≤ Φ + 4`) and with it the true `n log ; n log` form; reaching
it needs a clear-semantics cascade here or a transfer-semantics ledger
in the accounting lane.  The `n log` form is therefore the cross-lane
todo; the honest row below is the `st.n`-form.
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

/- Fredman–Tarjan 1987.  Bound theirs; formalization ours.  The CLRS /
transfer seam above is the stated accounting boundary. -/

end Submission.FibHeapRow
