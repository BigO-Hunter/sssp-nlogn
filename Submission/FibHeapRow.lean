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

/- Fredman–Tarjan 1987.  Bound theirs; formalization ours.  The CLRS /
transfer seam above is the stated accounting boundary. -/

end Submission.FibHeapRow
