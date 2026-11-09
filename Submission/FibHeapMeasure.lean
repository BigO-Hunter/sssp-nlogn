import Submission.FibHeapExtractMin
import Submission.FibHeapCascade
import Submission.FibHeapAccounting

/-!
# M4b: the consolidation-loop measure — the machine mark count, the potential, the amortization

This module connects the machine `HState` (root list, mark bits) to the scalar
accounting lane (`FibHeapAccounting.potential t μ = t + 2 * μ`, the FT-1987/CLRS
form) and proves the amortization's root:

* **The machine mark count** `machineMarks st`: the number of live slots with a
  set mark bit — `μ` of the accounting lane, read off the array.
* **The machine potential** `machinePotential st := st.roots.length + 2 * machineMarks st`:
  `t + 2μ` with `t` the root count and `μ` the machine mark count.
* **Per-step effects**: the cut raises the potential by exactly 3 (one new root,
  one fresh mark); each consolidation-cell promote raises it by exactly 1 (one new
  root; the consumed mark of the promoted node pays for the mark set on the loser);
  the stop's mark step raises it by at most 2.  Hence the amortization's machine
  form: **the potential increase over a whole decrease-key path is at most
  `chain.length + 5`** — independent of the heap size, linear in the cascade with
  constant coefficient 1 per cell.  The `ChainOk` premises realize the forest
  lane's `CascadeMarks` discipline cell-by-cell (`chainOk_markChain`), so with the
  forest lane's `decrease_amortized_of_marks` the machine cascade is charged to
  the mark potential instead of assuming it.
* **The consolidation measure**: `Consolidated` (distinct root degrees) bounds the
  root count by the degree bound plus one (`root_count_bound`, the pigeonhole over
  the degree map — with `B = rankCap n` this is the `O(log n)` root-count bound);
  the merge cell preserves `Consolidated` relative to the new degree's freshness
  (`merge_Consolidated`); the extract-min output witness is `Consolidated` with
  both roots under `rootCap`.
* **The extraction's potential**: on the extract-min witness the extraction raises
  the machine potential by exactly one (one net new root; the promoted children
  were unmarked, so no mark tokens move).

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapMeasure

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink Submission.FibHeapLinkWalk
  Submission.FibHeapCut Submission.FibHeapMerge Submission.FibHeapPromote
  Submission.FibHeapCascade Submission.FibHeapExtractMin Submission.FibHeapAccounting

/-! ## The machine mark count and the machine potential -/

/-- The marked live slots: `μ` of the accounting lane, read off the array. -/
def markSet (st : HState) : Finset ℕ := (Finset.range st.n).filter (fun i => 0 < st.mrk i)

/-- The machine mark count. -/
def machineMarks (st : HState) : ℕ := (markSet st).card

/-- The machine potential: `t + 2μ` (roots plus two tokens per mark), the
FT-1987/CLRS form with both counts read off the array. -/
def machinePotential (st : HState) : ℕ := st.roots.length + 2 * machineMarks st

theorem mem_markSet {st : HState} {i : ℕ} :
    i ∈ markSet st ↔ i < st.n ∧ 0 < st.mrk i := by
  simp [markSet, Finset.mem_filter, Finset.mem_range]

@[simp] theorem markSet_cutState (st : HState) (x y : ℕ) (hy : y < st.n) :
    markSet (cutState st x y) = insert y (markSet st) := by
  ext i
  simp only [markSet, cutState_n, cutState_mrk, Finset.mem_filter, Finset.mem_range]
  by_cases h' : i = y
  · subst h'
    simp [hy]
  · simp only [if_neg h']
    exact ⟨h', rfl⟩

@[simp] theorem markSet_promoteState (st : HState) (y z : ℕ) (hyn : y < st.n)
    (hzn : z < st.n) (hy : st.mrk y = 1) (hz : st.mrk z = 0) :
    markSet (promoteState st y z) = (markSet st).erase y ∪ {z} := by
  ext i
  simp only [markSet, promoteState_n, promoteState_mrk, Finset.mem_filter, Finset.mem_range]
  by_cases hiy : i = y
  · by_cases hiz : i = z
    · subst hiy
      subst hiz
      simp [hzn, hy]
    · subst hiy
      simp [hz, hy, hyn]
  · by_cases hiz : i = z
    · subst hiz
      simp [hyn, hy]
    · simp [hiy, hiz, hy, hz, hyn]

@[simp] theorem markSet_markState (st : HState) (y : ℕ) (hy : y < st.n) :
    markSet (markState st y) = insert y (markSet st) := by
  ext i
  by_cases h' : i = y
  · subst h'
    simp [markState_mrk, markState_n, markSet, Finset.mem_filter, Finset.mem_range, hy]
  · simp [markSet, markState, markState_mrk, Finset.mem_filter, Finset.mem_range, h', hy]

/-- The cut banks one fresh mark: the mark count goes up by exactly one. -/
theorem machineMarks_cutState (st : HState) (x y : ℕ) (hy : y < st.n) (hy0 : st.mrk y = 0) :
    machineMarks (cutState st x y) = machineMarks st + 1 := by
  simp only [machineMarks]
  rw [markSet_cutState st x y hy]
  rw [Finset.card_insert_of_notMem (by simp [mem_markSet, hy0])]

theorem machineMarks_markState_le (st : HState) (y : ℕ) :
    machineMarks (markState st y) ≤ machineMarks st + 1 := by
  simp only [machineMarks]
  by_cases hy : y < st.n
  · by_cases hyin : y ∈ markSet st
    · rw [markSet_markState st y hy, Finset.insert_eq_of_mem hyin]
    · rw [markSet_markState st y hy,
        Finset.card_insert_of_notMem (by simpa [mem_markSet] using hyin)]
  · have hsame : markSet (markState st y) = markSet st := by
      ext i
      simp only [markSet, markState_n, markState_mrk, Finset.mem_filter, Finset.mem_range]
      by_cases h' : i = y
      · subst h'
        simp [hy]
      · simp only [if_neg h']
        exact ⟨rfl, by simp [h']⟩
    rw [hsame]
    omega

/-- The promote's mark count is unchanged: the promoted node's mark (one banked
token pair) is consumed to pay for the mark set on the losing ancestor. -/
theorem machineMarks_promoteState (st : HState) (y z : ℕ) (hyn : y < st.n) (hzn : z < st.n)
    (hy : st.mrk y = 1) (hz : st.mrk z = 0) :
    machineMarks (promoteState st y z) = machineMarks st := by
  simp only [machineMarks]
  by_cases hyz : y = z
  · subst hyz
    have h : markSet (promoteState st y y) = markSet st := by
      ext i
      by_cases hiy : i = y
      · subst hiy
        simp only [promoteState_n, promoteState_mrk, Finset.mem_filter, Finset.mem_range]
        simp [hy]
      · simp only [promoteState_n, promoteState_mrk, Finset.mem_filter, Finset.mem_range]
        simp [hiy]
    rw [h]
  · rw [markSet_promoteState st y z hyn hzn hy hz]
    have hyin : y ∈ markSet st := by simp [mem_markSet, hy]
    have hzout : z ∉ markSet st := by simp [mem_markSet, hz]
    have hdisj : Disjoint ((markSet st).erase y) {z} :=
      Finset.disjoint_singleton_right.mpr hzout
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hyin]
    omega

theorem machinePotential_promoteState (st : HState) (y z : ℕ) (hy : st.mrk y = 1)
    (hz : st.mrk z = 0) :
    machinePotential (promoteState st y z) = machinePotential st + 1 := by
  have hroots : (promoteState st y z).roots.length = st.roots.length + 1 := by
    rw [promoteState_roots]; simp
  simp only [machinePotential, hroots, machineMarks_promoteState st y z hyn hzn hy hz]
  omega

/-! ## The mark discipline of the cascade -/

/-- The machine mark discipline of a consolidation chain: each cell `(y, z)` runs
against live slots (`y`, `z` under the fixed bound `N` — `promoteState_n` keeps
the live size constant along the fold) with `y`'s mark set and `z`'s clear, and
the rest of the chain runs on the state after that cell.  This is exactly what
the `ChainOk` premises say cell-by-cell; the bridge below extracts it. -/
def MarkChain (st : HState) (N : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (y, z) :: rest =>
      y < N ∧ z < N ∧ st.mrk y = 1 ∧ st.mrk z = 0
        ∧ MarkChain (promoteState st y z) N rest

/-- The `ChainOk` premises realize the machine mark discipline: the promote
preconditions supply each cell's marks, and `SlotOK` (stable across the fold —
`promoteState_n` keeps the live size) bounds the promoted node. -/
theorem chainOk_markChain (st : HState) (chain : List (ℕ × ℕ)) (N : ℕ)
    (hst : st.n = N) (hslot : ∀ s : HState, s.n = N → SlotOK s)
    (hchain : ChainOk st chain) : MarkChain st N chain := by
  induction chain generalizing st with
  | nil => trivial
  | cons head tail ih =>
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hrest⟩ := hchain
    refine ⟨Nat.lt_of_lt_of_eq (hslot st hst z hpre.2.1 y hpre.1) hst,
      hpre.2.1.trans hst, hpre.2.2.1, hpre.2.2.2.1,
      ih (promoteState st y z) (by rw [promoteState_n]; exact hst) hrest⟩

/-! ## The amortization's machine form: the decrease-key path's potential -/

/-- The consolidation fold pays its own way: each cell raises the potential by
exactly one (one new root; the consumed mark pays for the new mark), and the
stop's mark raises it by at most two. -/
theorem cascadeRun_potential (st : HState) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain st st.n chain) :
    machinePotential (cascadeRun st chain stop) ≤ machinePotential st + chain.length + 2 := by
  induction chain generalizing st with
  | nil =>
    simp only [cascadeRun, machinePotential, markState_roots]
    have hm := machineMarks_markState_le st stop
    omega
  | cons head tail ih =>
    obtain ⟨y, z⟩ := head
    obtain ⟨hyn, hzn, hmy, hmz, hrest⟩ := hmc
    have hprom := machinePotential_promoteState st y z hyn hzn hmy hmz
    calc machinePotential (cascadeRun (promoteState st y z) tail stop)
        ≤ machinePotential (promoteState st y z) + tail.length + 2 :=
          ih (promoteState st y z) (by rw [promoteState_n]; exact hrest)
      _ = machinePotential st + 1 + tail.length + 2 := by rw [hprom]
      _ ≤ machinePotential st + ((y, z) :: tail).length + 2 := by
          simp only [List.length_cons]
          omega

/-- The decrease-key path's potential increase is at most the cascade length plus
five: three for the cut (one new root, one fresh mark) and one per consolidation
cell plus two for the stop's mark.  The increase is independent of the heap size
and linear in the cascade with coefficient one — the amortization's machine form,
with the mark transfer (each cell consumes the mark the previous step banked)
carried by `MarkChain`. -/
theorem decreaseKeyPath_potential (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hyn : y < st.n) (hy0 : st.mrk y = 0)
    (hmc : MarkChain (cutState st x y) st.n chain) :
    machinePotential (decreaseKeyPath st x y chain stop) ≤ machinePotential st + chain.length + 5 := by
  unfold decreaseKeyPath
  have hcut : machinePotential (cutState st x y) = machinePotential st + 3 := by
    have hroots : (cutState st x y).roots.length = st.roots.length + 1 := by
      rw [cutState_roots]; simp
    simp only [machinePotential, hroots, machineMarks_cutState st x y hyn hy0]
    omega
  have hmc' : MarkChain (cutState st x y) (cutState st x y).n chain := by
    rw [cutState_n]; exact hmc
  calc machinePotential (cascadeRun (cutState st x y) chain stop)
      ≤ machinePotential (cutState st x y) + chain.length + 2 :=
        cascadeRun_potential _ chain stop hmc'
    _ = machinePotential st + 3 + chain.length + 2 := by rw [hcut]
    _ ≤ machinePotential st + chain.length + 5 := omega

/-! ## The consolidation measure -/

/-- Distinct root degrees: after consolidation no two roots share a rank. -/
def Consolidated (st : HState) : Prop :=
  ∀ r ∈ st.roots, ∀ p ∈ st.roots, r ≠ p → st.deg r ≠ st.deg p

/-- **The root-count bound.**  With distinct root degrees and every root degree
bounded by `B`, there are at most `B + 1` roots — the degree map injects the root
list into `List.range (B + 1)` (pigeonhole through `subperm_of_subset`).  With
`B = rankCap n` this is the `O(log n)` root-count bound. -/
theorem root_count_bound (st : HState) (hnd : st.roots.Nodup) (hc : Consolidated st) {B : ℕ}
    (hB : ∀ r ∈ st.roots, st.deg r ≤ B) : st.roots.length ≤ B + 1 := by
  have hmapnod : (st.roots.map st.deg).Nodup :=
    (List.nodup_map_iff_inj_on hnd).mpr (fun a ha b hb hab => hc a ha b hb (by rw [hab]))
  have hmem : ∀ d ∈ st.roots.map st.deg, d ∈ List.range (B + 1) := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
    exact List.mem_range.mpr (Nat.lt_succ_of_le (hB r hr))
  have hsubperm : st.roots.map st.deg <+~ List.range (B + 1) :=
    List.subperm_of_subset hmapnod hmem
  have hlen := hsubperm.length_le
  rwa [List.length_map, List.length_range] at hlen

/-- The merge cell preserves `Consolidated`, provided the new rank of the absorbing
root does not collide with any untouched root (the freshness the real
implementation's degree buckets supply). -/
theorem merge_Consolidated (st : HState) (hc : Consolidated st) (r p : ℕ)
    (hpre : MergePre st r p)
    (hnew : ∀ q ∈ st.roots, q ≠ p → q ≠ r → st.deg p + 1 ≠ st.deg q) :
    Consolidated (mergeState st r p) := by
  intro a ha b hb hab hde
  rw [mergeState_roots] at ha hb
  obtain ⟨hra, hrap⟩ := List.mem_filter.mp ha
  obtain ⟨hba, hbp⟩ := List.mem_filter.mp hb
  rw [mergeState_deg, mergeState_deg] at hde
  by_cases hap : a = p
  · subst hap
    simp only [if_pos rfl] at hde
    exact absurd hde (hnew b hba (by omega) (by rwa [bne_iff_ne]))
  · by_cases hbp : b = p
    · subst hbp
      simp only [if_pos rfl] at hde
      exact absurd hde (Ne.symm (hnew a ha (by omega) (by rwa [bne_iff_ne])))
    · rw [if_neg hap, if_neg hbp] at hde
      exact absurd hde (hc a (by simpa using hra) b (by simpa using hba) (by omega))

/-! ## The measure on the extract-min witness -/

/-- The extraction raises the machine potential by exactly one: one net new root
(three roots after against two before), and no mark tokens move — the promoted
children were unmarked. -/
theorem extract_potential :
    machinePotential (extractState extractPreSt 3) = machinePotential extractPreSt + 1 := by
  have hroots : (extractState extractPreSt 3).roots.length = 3 := by
    rw [extracted_state_roots]; simp [extracted_roots]
  have hmarks : markSet (extractState extractPreSt 3) = ∅ := by
    ext i
    simp [markSet, extracted_state_mrk, extracted_mrk]
  have h0 : machineMarks extractPreSt = 0 := by
    simp only [machineMarks]
    have hex : markSet extractPreSt = ∅ := by ext i; simp [markSet, extractPreSt]
    rw [hex, Finset.card_empty]
  have hr2 : extractPreSt.roots.length = 2 := by simp [extractPreSt]
  simp only [machinePotential, machineMarks, hroots, hmarks, h0, hr2, Finset.card_empty]
  omega

/-- The extract-min output witness is consolidated: the two surviving roots have
distinct degrees (`4` at degree 0, `1` at degree 1). -/
theorem extractedMinState_consolidated : Consolidated extractedMinState := by
  intro r hr p hp hne hde
  simp at hr hp
  rcases hr with rfl | rfl <;> rcases hp with rfl | rfl
  · exact absurd rfl hne
  · simp at hde
  · simp at hde
  · exact absurd rfl hne

/-- The witness's root bound: two roots, and every `rankCap` is at least one, so
two roots are under `rootCap` — the pigeonhole bound at `B = 1` (degrees 0 and 1)
matches `rootCap 6 ≥ 2`. -/
theorem extractedMinState_root_bound :
    extractedMinState.roots.length ≤ FibHeapAccounting.rootCap extractedMinState.n := by
  have h2 : extractedMinState.roots.length = 2 := by simp [extractedMinState_roots]
  have h1 : 1 ≤ FibHeapAccounting.rankCap extractedMinState.n := by
    simp only [FibHeapAccounting.rankCap]
    omega
  simp only [FibHeapAccounting.rootCap]
  omega

end Submission.FibHeapMeasure
