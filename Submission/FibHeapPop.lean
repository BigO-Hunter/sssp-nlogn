/-
THE POP MODULE: the CLRS extract-min's actual shape — splice plus
consolidation — bounded for arbitrary live states.

The witness-level `extract_potential` (M4b) leaned on two unmarked
children.  The general splice arithmetic: `extractState` clears every
spliced child's mark (`extractState_mrk_child`) and moves the whole
child list to the roots, so the splice raises the potential by at most
`|kids st r|` — and the consolidation walk over those children is
covered by the landed `cascadeRun_potential` (`≤ len + 2`).  The
per-op extract bound at the row form follows, with the cap `k ≤
deg r ≤ rankCap n`-class (the log form) where the degree bound applies.

Fredman–Tarjan 1987.  Bound theirs; formalization ours.
-/
import Submission.FibHeapExtractMin
import Submission.FibHeapMeasure
import Submission.FibHeapCascade

namespace Submission.FibHeapPop

open Submission.FibHeapExtractMin Submission.FibHeapMeasure Submission.FibHeapRefine
open Submission.FibHeapCascade Submission.FibHeapCut Submission.FibHeapPromote

/-- **The splice's potential bound.**  Roots move up by at most the
child count (the filter only removes `r`), marks only move down (every
spliced child's mark is cleared, all other marks kept). -/
theorem extractState_potential_le (st : HState) (r : ℕ) :
    machinePotential (extractState st r) ≤ machinePotential st + (kids st r).length := by
  have hroots : (extractState st r).roots.length ≤ st.roots.length + (kids st r).length := by
    rw [extractState_roots]
    simp only [List.length_append]
    have hflt : (st.roots.filter (fun x => x != r)).length ≤ st.roots.length :=
      List.length_filter_le _ _
    omega
  have hmarks : machineMarks (extractState st r) ≤ machineMarks st := by
    have hsub : markSet (extractState st r) ⊆ markSet st := by
      intro i hi
      rw [mem_markSet] at hi ⊢
      have hn : i < st.n := by
        have := hi.1
        simp [extractState] at this
        exact this
      rw [extractState_mrk] at hi
      by_cases hk : i ∈ kids st r
      · rw [if_pos hk] at hi
        exact absurd hi (by omega)
      · rw [if_neg hk] at hi
        exact ⟨hn, hi.2⟩
    have : machineMarks (extractState st r) ≤ machineMarks st :=
      Finset.card_le_card hsub
    exact this
  simp only [machinePotential] at *
  omega

/-- **The general per-op extract bound at the row form.**  Splice plus
consolidation: the splice costs at most `k` (`k = |kids st r|`), the
consolidation walk over the spliced children costs at most its length
plus two — with `k ≤ deg r ≤ rankCap n`-class this is the log form. -/
theorem extractMin_pop_potential (st : HState) (r : ℕ)
    (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain (extractState st r) (extractState st r).n chain) :
    machinePotential (cascadeRun (extractState st r) chain stop)
      ≤ machinePotential st + (kids st r).length + chain.length + 2 := by
  have hsplice := extractState_potential_le st r
  have hwalk := cascadeRun_potential (extractState st r) chain stop hmc
  simp only [machinePotential] at *
  omega

end Submission.FibHeapPop
