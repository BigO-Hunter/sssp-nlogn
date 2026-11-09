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

namespace Submission.FibHeapRow

open Submission.FibHeapAmortized Submission.FibHeapMeasure Submission.FibHeapDepth
open Submission.FibHeapExtractMin
open Submission.FibHeapRefine

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

/- **The row's sequential composition — named, not yet claimed.**  The
decrease-key half is fully general in its start state; the extract-min
half is at witness level (`extractPreSt`).  Their sequential product —
extract-mins over the *post-run* state — needs the general extract-min
lemma (`machinePotential (extractState st r) ≤ machinePotential st + 1`
for arbitrary live `st`, `r`), which is the named next step.  No total
theorem is stated over mismatched states.  With the general lemma and
the LiveDistinct bridge (`L ≤ st.n`-class) the row reads
`m · (st.n + 5)`-form, and the CLRS cross-lane corollary upgrades it to
the `n log` form.

Fredman–Tarjan 1987.  Bound theirs; formalization ours.  The CLRS /
transfer seam above is the stated accounting boundary. -/

end Submission.FibHeapRow
