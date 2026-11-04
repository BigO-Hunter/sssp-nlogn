import Submission.DijkstraSim

/-!
# Submission.DijkstraHeap — heap-ops simulation (siftUp/siftDown/push/pop)

Mid-sift states do not satisfy `Inv.heapOK`, so the loop invariants run on
`SoftInv` (everything but heap order) plus a structural clause (pairs are
originals shifted along the sift path) and a single-violation heap clause.
`SoftInv.swap` transfers the entry fields through one transposition; the
structural clause feeds the heap-order restoration.
-/

namespace Submission.DijkstraHeap

open Frontier Frontier.RAM WExpr Stmt NNReal ENNReal
open Submission.DijkstraProg Submission.DijkstraModel Submission.DijkstraDecode
open Submission.DijkstraSim

variable {G : Graph} {s : Fin G.n}

/-- `Inv` without the heap-order field (mid-sift states). -/
structure SoftInv (s : Fin G.n) (distA : Fin G.n → ℝ≥0) (reachA doneA : Fin G.n → ℕ)
    (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h ins : ℕ) : Prop where
  ghost : ∀ v, reachA v ≠ 0 → ∃ p, G.IsWalk s v p ∧ G.len p = distA v
  relax_hold : ∀ e : Fin G.m, doneA (G.src e) ≠ 0 →
    reachA (G.dst e) ≠ 0 ∧
    ((distA (G.dst e) : ℝ≥0) : ℝ≥0∞) ≤ ((distA (G.src e) : ℝ≥0) : ℝ≥0∞) + G.w e
  entry_cur : ∀ v, reachA v ≠ 0 → doneA v = 0 → ∃ i, i < h ∧ hv i = v ∧ hd i = distA v
  entry_mono : ∀ i, i < h → distA (hv i) ≤ hd i
  entry_reach : ∀ i, i < h → reachA (hv i) ≠ 0
  source0 : distA s = 0 ∧ reachA s ≠ 0
  done_reach : ∀ u, doneA u ≠ 0 → reachA u ≠ 0

theorem SoftInv.toInv {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
    {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}
    (S : SoftInv s distA reachA doneA hv hd h ins) (H : HeapOK hv hd h) :
    Inv G s distA reachA doneA hv hd h ins :=
  ⟨S.ghost, S.relax_hold, H, S.entry_cur, S.entry_mono, S.entry_reach, S.source0, S.done_reach⟩

theorem Inv.toSoft {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
    {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}
    (I : Inv G s distA reachA doneA hv hd h ins) :
    SoftInv s distA reachA doneA hv hd h ins :=
  ⟨I.ghost, I.relax_hold, I.entry_cur, I.entry_mono, I.entry_reach, I.source0, I.done_reach⟩

/-- The entry fields survive a transposition of two heap positions (`a`, `b` below `h`):
the swap moves pairs atomically. -/
theorem SoftInv.swap {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
    {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}
    (S : SoftInv s distA reachA doneA hv hd h ins) {a b : ℕ}
    (hab : a ≠ b) (ha : a < h) (hb : b < h) {hv' : ℕ → Fin G.n} {hd' : ℕ → ℝ≥0}
    (heqv : ∀ i, hv' i = if i = a then hv b else if i = b then hv a else hv i)
    (heqd : ∀ i, hd' i = if i = a then hd b else if i = b then hd a else hd i) :
    SoftInv s distA reachA doneA hv' hd' h ins := by
  have hmono : ∀ i, i < h → distA (hv' i) ≤ hd' i := by
    intro i hi
    have hvi : hv' i = if i = a then hv b else if i = b then hv a else hv i := heqv i
    have hdi : hd' i = if i = a then hd b else if i = b then hd a else hd i := heqd i
    by_cases hia : i = a
    · have e1 : (if i = a then hv b else if i = b then hv a else hv i) = hv b := if_pos hia
      have e2 : (if i = a then hd b else if i = b then hd a else hd i) = hd b := if_pos hia
      rw [hvi, hdi, e1, e2]; exact S.entry_mono b hb
    · by_cases hib : i = b
      · have e1 : (if i = a then hv b else if i = b then hv a else hv i) = hv a :=
          by rw [if_neg hia, if_pos hib]
        have e2 : (if i = a then hd b else if i = b then hd a else hd i) = hd a :=
          by rw [if_neg hia, if_pos hib]
        rw [hvi, hdi, e1, e2]; exact S.entry_mono a ha
      · have e1 : (if i = a then hv b else if i = b then hv a else hv i) = hv i :=
          by rw [if_neg hia, if_neg hib]
        have e2 : (if i = a then hd b else if i = b then hd a else hd i) = hd i :=
          by rw [if_neg hia, if_neg hib]
        rw [hvi, hdi, e1, e2]; exact S.entry_mono i hi
  have hreachE : ∀ i, i < h → reachA (hv' i) ≠ 0 := by
    intro i hi
    have hvi : hv' i = if i = a then hv b else if i = b then hv a else hv i := heqv i
    by_cases hia : i = a
    · have e1 : (if i = a then hv b else if i = b then hv a else hv i) = hv b := if_pos hia
      rw [hvi, e1]; exact S.entry_reach b hb
    · by_cases hib : i = b
      · have e1 : (if i = a then hv b else if i = b then hv a else hv i) = hv a :=
          by rw [if_neg hia, if_pos hib]
        rw [hvi, e1]; exact S.entry_reach a ha
      · have e1 : (if i = a then hv b else if i = b then hv a else hv i) = hv i :=
          by rw [if_neg hia, if_neg hib]
        rw [hvi, e1]; exact S.entry_reach i hi
  refine ⟨S.ghost, S.relax_hold, ?_, hmono, hreachE, S.source0, S.done_reach⟩
  intro v hr hd0
  obtain ⟨j, hj, hjv, hjd⟩ := S.entry_cur v hr hd0
  by_cases hja : j = a
  · refine ⟨b, hb, ?_, ?_⟩
    · have e1 : (if b = a then hv b else if b = b then hv a else hv b) = hv a :=
        by rw [if_neg (Ne.symm hab), if_pos rfl]
      rw [heqv b, e1]; rw [hja] at hjv; exact hjv
    · have e2 : (if b = a then hd b else if b = b then hd a else hd b) = hd a :=
        by rw [if_neg (Ne.symm hab), if_pos rfl]
      rw [heqd b, e2]; rw [hja] at hjd; exact hjd

  · by_cases hjb : j = b
    · refine ⟨a, ha, ?_, ?_⟩
      · have e1 : (if a = a then hv b else if a = b then hv a else hv a) = hv b := if_pos rfl
        rw [heqv a, e1]; rw [hjb] at hjv; exact hjv
      · have e2 : (if a = a then hd b else if a = b then hd a else hd a) = hd b := if_pos rfl
        rw [heqd a, e2]; rw [hjb] at hjd; exact hjd
    · refine ⟨j, hj, ?_, ?_⟩
      · have e1 : (if j = a then hv b else if j = b then hv a else hv j) = hv j :=
          by rw [if_neg hja, if_neg hjb]
        rw [heqv j, e1]; exact hjv
      · have e2 : (if j = a then hd b else if j = b then hd a else hd j) = hd j :=
          by rw [if_neg hja, if_neg hjb]
        rw [heqd j, e2]; exact hjd

end Submission.DijkstraHeap
