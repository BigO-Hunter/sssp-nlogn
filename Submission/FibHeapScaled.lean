/-
The scaled-potential bridge between the consolidation-measure lane and the
accounting lane.

The measure module's machine potential is exactly the accounting lane's
`FibHeapAccounting.potential t μ = t + 2 * μ` with `t` the root count and `μ`
the mark count — the identification is definitional.  Scaling by `K` and
applying `Nat.mul_le_mul_left` (the same step the accounting lane's own
`decrease_amortized` uses on its potential hypothesis) restates the
decrease-key path bound in the scaled ledger's units.

Note on scope: the accounting lane's `decrease_amortized_clrs` consumes the
CLRS clear-per-step mark discipline (`μ' + c ≤ μ + 2`).  This lane's cascade
is the transfer discipline — the cut banks one fresh mark and each
consolidation cell moves it one link up (y cleared, z marked, net zero), so
the post-state mark count is `μ + 1` exactly and `μ'' + c = μ + k + 2`.  The
c-independent form is therefore *not* derivable here; the scaled bridge below
carries the `K * (len + 5)` term, which the decrease-key's own `O(len)` work
covers.  Reaching `D0 + 3K + D1` requires a clear-semantics cascade in this
lane (or a transfer-semantics ledger in the accounting lane).
-/
import Submission.FibHeapMeasure
import Submission.FibHeapAccounting

namespace Submission.FibHeapScaled

open Submission.FibHeapMeasure Submission.FibHeapRefine Submission.FibHeapCut
open Submission.FibHeapPromote Submission.FibHeapCascade

/-- The machine potential *is* the accounting lane's `Φ = t + 2μ`. -/
theorem machinePotential_eq_potential (st : HState) :
    machinePotential st
      = FibHeapAccounting.potential st.roots.length (machineMarks st) :=
  rfl

/-- Scaled decrease-key path bound: the `K`-scaled potential of the
post-state is at most the `K`-scaled potential of the pre-state plus
`K * (chain.length + 5)` — the amortization's ledger form, with the
c-linear term carried explicitly. -/
theorem decreaseKeyPath_scaled {K : ℕ} (st : HState) (x y : ℕ)
    (chain : List (ℕ × ℕ)) (stop : ℕ) (hyn : y < st.n) (hy0 : st.mrk y = 0)
    (hmc : MarkChain (cutState st x y) st.n chain) :
    FibHeapAccounting.scaledPotential K
        (decreaseKeyPath st x y chain stop).roots.length
        (machineMarks (decreaseKeyPath st x y chain stop))
      ≤ FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
        + K * (chain.length + 5) := by
  have h := decreaseKeyPath_potential st x y chain stop hyn hy0 hmc
  simp only [machinePotential] at h
  calc FibHeapAccounting.scaledPotential K
        (decreaseKeyPath st x y chain stop).roots.length
        (machineMarks (decreaseKeyPath st x y chain stop))
      = K * ((decreaseKeyPath st x y chain stop).roots.length
          + 2 * machineMarks (decreaseKeyPath st x y chain stop)) := rfl
    _ ≤ K * (st.roots.length + 2 * machineMarks st + (chain.length + 5)) :=
        Nat.mul_le_mul_left K h
    _ = FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
        + K * (chain.length + 5) := by rw [Nat.mul_add]; rfl

end Submission.FibHeapScaled
