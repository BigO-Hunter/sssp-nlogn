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

/-- The entry fields of `SoftInv` — the only fields heap-entry transpositions touch.
Frame fields (`ghost`, `relax_hold`, `source0`, `done_reach`) ride alongside unchanged,
so sift/sweep code can transport entry state without the full `SoftInv`. -/
structure EntrySoft (s : Fin G.n) (distA : Fin G.n → ℝ≥0)
    (reachA doneA : Fin G.n → ℕ) (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h ins : ℕ) : Prop where
  entry_cur : ∀ v, reachA v ≠ 0 → doneA v = 0 → ∃ i, i < h ∧ hv i = v ∧ hd i = distA v
  entry_mono : ∀ i, i < h → distA (hv i) ≤ hd i
  entry_reach : ∀ i, i < h → reachA (hv i) ≠ 0

theorem EntrySoft.swap {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
    {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}
    (S : EntrySoft s distA reachA doneA hv hd h ins) {a b : ℕ}
    (hab : a ≠ b) (ha : a < h) (hb : b < h) {hv' : ℕ → Fin G.n} {hd' : ℕ → ℝ≥0}
    (heqv : ∀ i, hv' i = if i = a then hv b else if i = b then hv a else hv i)
    (heqd : ∀ i, hd' i = if i = a then hd b else if i = b then hd a else hd i) :
    EntrySoft s distA reachA doneA hv' hd' h ins := by
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
  refine ⟨?_, hmono, hreachE⟩
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

/-- The entry fields with one waived entry: the vertex `holev` being pushed by the caller has
not been inserted into the heap yet (`pushBody` inserts it itself), so no entry is demanded. -/
structure EntrySoftH (holev : Fin G.n) (s : Fin G.n) (distA : Fin G.n → ℝ≥0)
    (reachA doneA : Fin G.n → ℕ) (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h ins : ℕ) : Prop where
  entry_hole : ∀ v, v ≠ holev → reachA v ≠ 0 → doneA v = 0 →
    ∃ i, i < h ∧ hv i = v ∧ hd i = distA v
  entry_mono : ∀ i, i < h → distA (hv i) ≤ hd i
  entry_reach : ∀ i, i < h → reachA (hv i) ≠ 0

theorem EntrySoftH.ofSoft {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
    {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ} {holev : Fin G.n}
    (S : EntrySoft s distA reachA doneA hv hd h ins) :
    EntrySoftH holev s distA reachA doneA hv hd h ins :=
  ⟨fun v _ => S.entry_cur v, S.entry_mono, S.entry_reach⟩

/-- `SoftInv` with one waived `entry_cur` hole: the freshly popped vertex `holev`
has no heap entry between `popBody` and `settleBody`'s done-store. -/
structure SoftInvH (holev : Fin G.n) (s : Fin G.n) (distA : Fin G.n → ℝ≥0)
    (reachA doneA : Fin G.n → ℕ) (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h ins : ℕ) : Prop where
  ghost : ∀ v, reachA v ≠ 0 → ∃ p, G.IsWalk s v p ∧ G.len p = distA v
  relax_hold : ∀ e : Fin G.m, doneA (G.src e) ≠ 0 →
    reachA (G.dst e) ≠ 0 ∧
    ((distA (G.dst e) : ℝ≥0) : ℝ≥0∞) ≤ ((distA (G.src e) : ℝ≥0) : ℝ≥0∞) + G.w e
  entry_hole : ∀ v, v ≠ holev → reachA v ≠ 0 → doneA v = 0 →
    ∃ i, i < h ∧ hv i = v ∧ hd i = distA v
  entry_mono : ∀ i, i < h → distA (hv i) ≤ hd i
  entry_reach : ∀ i, i < h → reachA (hv i) ≠ 0
  source0 : distA s = 0 ∧ reachA s ≠ 0
  done_reach : ∀ u, doneA u ≠ 0 → reachA u ≠ 0

theorem SoftInvH.swap {holev : Fin G.n} {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
    {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}
    (S : SoftInvH holev s distA reachA doneA hv hd h ins) {a b : ℕ}
    (hab : a ≠ b) (ha : a < h) (hb : b < h) {hv' : ℕ → Fin G.n} {hd' : ℕ → ℝ≥0}
    (heqv : ∀ i, hv' i = if i = a then hv b else if i = b then hv a else hv i)
    (heqd : ∀ i, hd' i = if i = a then hd b else if i = b then hd a else hd i) :
    SoftInvH holev s distA reachA doneA hv' hd' h ins := by
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
  intro v hvne hr hd0
  obtain ⟨j, hj, hjv, hjd⟩ := S.entry_hole v hvne hr hd0
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

/-- Heap-entry validity: every in-range `hv` slot holds a real vertex word. -/
def HeapV (st : State ℝ≥0) (h : ℕ) : Prop := ∀ i, i < h → st.wa "hv" i < G.n

theorem HeapV.congr {st st' : State ℝ≥0} {h : ℕ} (V : HeapV (G := G) st h)
    (e : ∀ i, st'.wa "hv" i = st.wa "hv" i) : HeapV (G := G) st' h := by
  intro i hi; rw [e i]; exact V i hi

theorem HeapV.storeW {st : State ℝ≥0} {h : ℕ} (V : HeapV (G := G) st h)
    {i a : ℕ} (ha : a < G.n) : HeapV (G := G) (st.storeW "hv" i a) h := by
  intro j hj
  have key : (st.storeW "hv" i a).wa "hv" j = if j = i then a else st.wa "hv" j := by
    rw [wa_storeW]; simp
  by_cases hj2 : j = i
  · rw [key, if_pos hj2]; exact ha
  · rw [key, if_neg hj2]; exact V j hj

/-- The heap operations (`siftUp`, `pushBody`, `siftDown`, `popBody`) write only `hv`/`hd` and
scalars: every other array is left alone.  Stated as one bundle so the `Runs` postconditions that
need it carry a single conjunct. -/
structure HeapFrame (st st' : State ℝ≥0) : Prop where
  dist : ∀ j, st'.va "dist" j = st.va "dist" j
  reach : ∀ j, st'.wa "reach" j = st.wa "reach" j
  done : ∀ j, st'.wa "done" j = st.wa "done" j
  head : ∀ w, st'.wa "head" w = st.wa "head" w
  nxt : ∀ j, st'.wa "nxt" j = st.wa "nxt" j
  regv : st'.w "v" = st.w "v"

theorem HeapFrame.trivial (st : State ℝ≥0) : HeapFrame st st :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem HeapFrame.trans {a b c : State ℝ≥0} (h1 : HeapFrame a b) (h2 : HeapFrame b c) :
    HeapFrame a c where
  dist j := (h2.dist j).trans (h1.dist j)
  reach j := (h2.reach j).trans (h1.reach j)
  done j := (h2.done j).trans (h1.done j)
  head w := (h2.head w).trans (h1.head w)
  nxt j := (h2.nxt j).trans (h1.nxt j)
  regv := h2.regv.trans h1.regv

theorem HeapFrame.charge {st st' : State ℝ≥0} (h : HeapFrame st st') (k : ℕ) :
    HeapFrame st (st'.charge k) where
  dist j := h.dist j
  reach j := h.reach j
  done j := h.done j
  head w := h.head w
  nxt j := h.nxt j
  regv := h.regv

/-- `Inv` with one waived `entry_cur` hole: the pop-window invariant between
`popBody` and `settleBody`'s done-store (or the stale-skip). -/
structure InvH (holev : Fin G.n) (s : Fin G.n) (distA : Fin G.n → ℝ≥0)
    (reachA doneA : Fin G.n → ℕ) (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h ins : ℕ) : Prop where
  soft : SoftInvH holev s distA reachA doneA hv hd h ins
  heapOK : HeapOK hv hd h

/-- A stale pop (`done holev ≠ 0`) resolves the hole: full `Inv` follows. -/
theorem InvH.toInv_of_done {holev : Fin G.n} {distA : Fin G.n → ℝ≥0}
    {reachA doneA : Fin G.n → ℕ} {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}
    (I : InvH holev s distA reachA doneA hv hd h ins) (hdne : doneA holev ≠ 0) :
    Inv G s distA reachA doneA hv hd h ins := by
  refine ⟨I.soft.ghost, I.soft.relax_hold, I.heapOK, ?_,
    I.soft.entry_mono, I.soft.entry_reach, I.soft.source0, I.soft.done_reach⟩
  intro v hr hd0
  by_cases hvv : v = holev
  · subst hvv; exact absurd hd0 hdne
  · exact I.soft.entry_hole v hvv hr hd0

/-- Parent position in the implicit binary heap. -/
def par (i : ℕ) : ℕ := (i - 1) / 2

/-- Heap order on every edge except the single edge `(a, b)`. -/
def HeapOKExcept (hd : ℕ → ℝ≥0) (h a b : ℕ) : Prop :=
  ∀ i j, i < h → j < h → (j = 2 * i + 1 ∨ j = 2 * i + 2) → ¬(i = a ∧ j = b) → hd i ≤ hd j

/-- Full heap order once the excepted edge also holds (or is not a real edge). -/
theorem HeapOKExcept.toHeapOK {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h a b : ℕ}
    (H : HeapOKExcept hd h a b) (hedge : ¬(a < h ∧ b < h ∧ (b = 2 * a + 1 ∨ b = 2 * a + 2)) ∨ hd a ≤ hd b) :
    HeapOK hv hd h := by
  intro i hi j hj hjr
  by_cases heq : i = a ∧ j = b
  · rcases hedge with hneg | hok
    · refine (hneg ?_).elim
      refine ⟨?_, ?_, ?_⟩
      · rw [← heq.1]; exact hi
      · rw [← heq.2]; exact hj
      · rw [heq.1, heq.2] at hjr; exact hjr
    · rw [heq.1, heq.2]; exact hok
  · exact H i j hi hj hjr heq

/-- The sift-up state: entry fields intact (`SoftInv`), the moving pair `(x, xk)` at `ii`,
pairs are originals shifted one step down the sift path, heap order holds except the
edge into the moving pair, and the moving pair dominates its (possibly empty) children. -/
structure SiftUpOK (s : Fin G.n) (st : State ℝ≥0) (origHv : ℕ → Fin G.n) (origHd : ℕ → ℝ≥0)
    (x : Fin G.n) (xk : ℝ≥0) (ii₀ ii : ℕ) : Prop where
  soft : EntrySoft s (fun v => st.va "dist" v) (fun v => st.wa "reach" v)
      (fun v => st.wa "done" v) (hvD s st) (fun i => st.va "hd" i) (st.w "h") (st.w "ins")
  hole : hvD s st ii = x ∧ st.va "hd" ii = xk
  xle : ∀ j, j < st.w "h" → (j = 2 * ii + 1 ∨ j = 2 * ii + 2) → xk ≤ st.va "hd" j
  pairs : ∀ i, i < st.w "h" →
      (i = ii ∧ hvD s st i = x ∧ st.va "hd" i = xk) ∨
      (ii ≤ i ∧ i ≠ ii ∧ hvD s st i = origHv (par i) ∧ st.va "hd" i = origHd (par i)) ∨
      (i ≠ ii₀ ∧ hvD s st i = origHv i ∧ st.va "hd" i = origHd i)
  ok : HeapOKExcept (fun i => st.va "hd" i) (st.w "h") (par ii) ii
  origOK : HeapOKExcept origHd (st.w "h") (par ii₀) ii₀
  leaf0 : 2 * ii₀ + 1 ≥ st.w "h"
  hiir : ii < st.w "h"

/-- `par` is strictly decreasing away from 0. -/
theorem par_lt (i : ℕ) (hi : 0 < i) : par i < i := by
  simp only [par]
  omega

theorem par_ne (i : ℕ) (hi : 0 < i) : par i ≠ i := by
  have := par_lt i hi; omega

/-- Every positive position is one of its parent's two children. -/
theorem par_child (i : ℕ) (hi : 0 < i) : i = 2 * par i + 1 ∨ i = 2 * par i + 2 := by
  have hd := Nat.div_add_mod (i - 1) 2
  have hm : (i - 1) % 2 = 0 ∨ (i - 1) % 2 = 1 := by omega
  simp only [par]
  rcases hm with hm | hm <;> omega

/-- The parent of a child position. -/
theorem par_of_child {i j : ℕ} (h : j = 2 * i + 1 ∨ j = 2 * i + 2) : par j = i := by
  rcases h with h | h <;> simp only [par] <;> rw [h] <;> omega

/-- One sift-up swap: the moving pair rises to `par ii`, the pair there descends to `ii`
and becomes a shifted pair.  The hole moves to `par ii`. -/
theorem SiftUpOK.swap {st st' : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0} {ii₀ ii : ℕ}
    (K : SiftUpOK s st origHv origHd x xk ii₀ ii)
    (hii : 0 < ii) (hlt : ii < st.w "h")
    (hh : st'.w "h" = st.w "h") (hins : st'.w "ins" = st.w "ins")
    (hswap : xk ≤ st.va "hd" (par ii))
    (hdist : ∀ v : Fin G.n, st'.va "dist" v = st.va "dist" v)
    (hreach : ∀ v : Fin G.n, st'.wa "reach" v = st.wa "reach" v)
    (hdone : ∀ v : Fin G.n, st'.wa "done" v = st.wa "done" v)
    (heqv : ∀ i, hvD s st' i = if i = ii then hvD s st (par ii)
        else if i = par ii then hvD s st ii else hvD s st i)
    (heqd : ∀ i, st'.va "hd" i = if i = ii then st.va "hd" (par ii)
        else if i = par ii then st.va "hd" ii else st.va "hd" i) :
    SiftUpOK s st' origHv origHd x xk ii₀ (par ii) := by
  have hp : par ii < ii := par_lt ii hii
  have hne : par ii ≠ ii := par_ne ii hii
  have hplt : par ii < st.w "h" := lt_trans hp hlt
  have hpo : hvD s st (par ii) = origHv (par ii) ∧ st.va "hd" (par ii) = origHd (par ii) := by
    rcases K.pairs (par ii) hplt with h1 | h2 | h3
    · exact absurd h1.1 hne
    · exact absurd h2.1 (by omega)
    · exact ⟨h3.2.1, h3.2.2⟩
  have hdd : (fun v : Fin G.n => st'.va "dist" v) = (fun v : Fin G.n => st.va "dist" v) :=
    funext hdist
  have hrr : (fun v : Fin G.n => st'.wa "reach" v) = (fun v : Fin G.n => st.wa "reach" v) :=
    funext hreach
  have hdn : (fun v : Fin G.n => st'.wa "done" v) = (fun v : Fin G.n => st.wa "done" v) :=
    funext hdone
  have hsoft : EntrySoft s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v)
      (fun v => st'.wa "done" v) (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") := by
    have hsw := K.soft.swap (hab := hne.symm) (ha := hlt) (hb := hplt)
      (hv' := hvD s st') (hd' := fun i => st'.va "hd" i) heqv heqd
    rw [← hdd, ← hrr, ← hdn, ← hh, ← hins] at hsw
    exact hsw
  have e1 : hvD s st' (par ii) = hvD s st ii := by
    rw [heqv, if_neg hne, if_pos rfl]
  have e2 : st'.va "hd" (par ii) = xk := by
    rw [heqd, if_neg hne, if_pos rfl]; exact K.hole.2
  have hhole : hvD s st' (par ii) = x ∧ st'.va "hd" (par ii) = xk :=
    ⟨e1.trans K.hole.1, e2⟩
  have e3 : st'.va "hd" ii = origHd (par ii) := by
    rw [heqd, if_pos rfl, hpo.2]
  -- original parent edges, except the entry edge (vacuous there by `leaf0`)
  have hpar : ∀ i j, i < st.w "h" → j < st.w "h" → (j = 2 * i + 1 ∨ j = 2 * i + 2) →
      origHd (par i) ≤ origHd i := by
    intro i j hi hj hjr
    by_cases h0 : i = 0
    · subst h0; exact le_rfl
    have hedge : i = 2 * par i + 1 ∨ i = 2 * par i + 2 := par_child i (by omega)
    have hpl : par i < st.w "h" := lt_trans (par_lt i (by omega)) hi
    by_contra hn
    have hzi : i = ii₀ := by
      by_contra hn2
      exact absurd (K.origOK (par i) i hpl hi hedge (fun hcc => hn2 hcc.2)) hn
    subst hzi
    have hleaf := K.leaf0
    rcases hjr with hr | hr <;> omega
  refine ⟨hsoft, hhole, ?_, ?_, ?_, (by rw [hh]; exact K.origOK), (by rw [hh]; exact K.leaf0),
    (by omega)⟩
  · -- xle at the new hole: children of `par ii`
    intro j hj hjr
    by_cases hjii : j = ii
    · rw [hjii, e3, ← hpo.2]; exact hswap
    · have e : st'.va "hd" j = st.va "hd" j := by
        rw [heqd, if_neg hjii, if_neg (by omega)]
      rw [e]
      exact le_trans hswap
        (K.ok (par ii) j hplt (by omega) hjr (fun hh' => hjii hh'.2))
  · -- pairs
    intro i hi
    by_cases hii2 : i = ii
    · rw [hii2]
      refine Or.inr (Or.inl ⟨by omega, fun hh' => hne hh'.symm, ?_, ?_⟩)
      · rw [heqv, if_pos rfl]; exact hpo.1
      · rw [heqd, if_pos rfl]; exact hpo.2
    · by_cases hip : i = par ii
      · rw [hip]
        refine Or.inl ⟨rfl, ?_, ?_⟩
        · rw [heqv, if_neg hne, if_pos rfl]; exact K.hole.1
        · rw [heqd, if_neg hne, if_pos rfl]; exact K.hole.2
      · rcases K.pairs i (by omega) with h1 | h2 | h3
        · exact absurd h1.1 hii2
        · refine Or.inr (Or.inl ⟨by omega, hip, ?_, ?_⟩)
          · rw [heqv, if_neg hii2, if_neg hip]; exact h2.2.2.1
          · rw [heqd, if_neg hii2, if_neg hip]; exact h2.2.2.2
        · refine Or.inr (Or.inr ⟨h3.1, ?_, ?_⟩)
          · rw [heqv, if_neg hii2, if_neg hip]; exact h3.2.1
          · rw [heqd, if_neg hii2, if_neg hip]; exact h3.2.2
  · -- heap order except (par (par ii), par ii)
    intro i j hi hj hjr hneq
    show st'.va "hd" i ≤ st'.va "hd" j
    by_cases hcp : i = par ii
    · -- the hole sits at par ii
      rw [hcp]
      by_cases hcj : j = ii
      · rw [hcj, e2, e3, ← hpo.2]; exact hswap
      · have e : st'.va "hd" j = st.va "hd" j := by
          rw [heqd, if_neg hcj, if_neg (by omega)]
        rw [e2, e]
        exact le_trans hswap (K.ok (par ii) j hplt (by omega) (by omega) (fun hcc => hcj hcc.2))
    · have hjii : j ≠ ii := by
        intro hh
        rw [hh] at hjr
        exact hcp (par_of_child hjr).symm
      have hjp : j ≠ par ii := by
        intro hh
        rw [hh] at hjr
        exact hneq ⟨(par_of_child hjr).symm, hh⟩
      by_cases hci : i = ii
      · -- the shifted pair at ii
        rw [hci] at hjr
        rw [hci]
        have e : st'.va "hd" j = st.va "hd" j := by
          rw [heqd, if_neg hjii, if_neg hjp]
        rw [e3, e]
        have hok : origHd (par ii) ≤ origHd ii := hpar ii j hlt (by omega) hjr
        have hpj : par j = ii := par_of_child hjr
        rcases K.pairs j (by omega) with h1 | h2 | h3
        · exact absurd h1.1 hjii
        · rw [h2.2.2.2, hpj]; exact hok
        · rw [h3.2.2]
          exact le_trans hok
            (K.origOK ii j hlt (by omega) hjr (fun hcc => h3.1 hcc.2))
      · -- neither endpoint moved
        have e : st'.va "hd" j = st.va "hd" j := by
          rw [heqd, if_neg hjii, if_neg hjp]
        have e' : st'.va "hd" i = st.va "hd" i := by
          rw [heqd, if_neg hci, if_neg hcp]
        rw [e', e]
        exact K.ok i j (by omega) (by omega) hjr (fun hcc => hcp hcc.1)

/-! ## Sift-up loop plumbing -/

/-- `hvD` at one position from a `wa "hv"` equation. -/
theorem hvD_eq_of_wa {st st' : State ℝ≥0} {i j : ℕ} (h : st'.wa "hv" i = st.wa "hv" j) :
    hvD (G := G) s st' i = hvD s st j := by
  simp only [hvD, h]

theorem F0.setV {st : State ℝ≥0} (h : F0 G s st) (x : String) (a : ℝ≥0) :
    F0 G s (st.setV x a) :=
  F0.preserve h rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl

theorem F0.storeV {st : State ℝ≥0} (h : F0 G s st) (arr : String) (j : ℕ) (a : ℝ≥0)
    (har : arr ≠ "w") : F0 G s (st.storeV arr j a) := by
  refine F0.preserve h rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) ?_ rfl rfl rfl
  intro jj _
  rw [va_storeV]
  exact if_neg (fun hh => har hh.1.symm)

/-- The `vle` bit for `realOps.le` is the `≤` indicator. -/
theorem bit_le {a b : ℝ≥0} : (if realOps.le a b then 1 else 0) = if a ≤ b then 1 else 0 := by
  by_cases h : a ≤ b <;> simp [realOps, h]

/-- Sift rank: the number of halving steps from `i` to the root. -/
def rk (i : ℕ) : ℕ := Nat.log 2 (i + 1)

theorem rk_zero : rk 0 = 0 := rfl

theorem rk_pos {i : ℕ} (hi : 0 < i) : 0 < rk i :=
  Nat.log_pos (by norm_num) (by omega)

theorem rk_par {i : ℕ} (hi : 0 < i) : rk (par i) + 1 = rk i := by
  have hdiv : par i + 1 = (i + 1) / 2 := by
    have h1 : (i - 1) / 2 + 1 = (i + 1) / 2 := by omega
    simpa [par] using h1
  have hge : 1 ≤ Nat.log 2 (i + 1) :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by norm_num; omega)
  simp only [rk, hdiv, Nat.log_div_base]
  omega

/-- A sift-up state survives updates that leave the heap arrays, decoded labels and
sizes alone (register writes and charges). -/
theorem SiftUpOK.stable {st st' : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0} {ii₀ ii : ℕ}
    (K : SiftUpOK s st origHv origHd x xk ii₀ ii)
    (hvE : ∀ i, st'.wa "hv" i = st.wa "hv" i)
    (hdE : ∀ i, st'.va "hd" i = st.va "hd" i)
    (hdistE : ∀ (v : Fin G.n), st'.va "dist" v = st.va "dist" v)
    (hreachE : ∀ (v : Fin G.n), st'.wa "reach" v = st.wa "reach" v)
    (hdoneE : ∀ (v : Fin G.n), st'.wa "done" v = st.wa "done" v)
    (hhE : st'.w "h" = st.w "h") (hinsE : st'.w "ins" = st.w "ins") :
    SiftUpOK s st' origHv origHd x xk ii₀ ii := by
  have hdd : (fun (v : Fin G.n) => st'.va "dist" v) = (fun (v : Fin G.n) => st.va "dist" v) :=
    funext hdistE
  have hrr : (fun (v : Fin G.n) => st'.wa "reach" v) = (fun (v : Fin G.n) => st.wa "reach" v) :=
    funext hreachE
  have hdn : (fun (v : Fin G.n) => st'.wa "done" v) = (fun (v : Fin G.n) => st.wa "done" v) :=
    funext hdoneE
  have hhh : (fun i => st'.va "hd" i) = (fun i => st.va "hd" i) := funext hdE
  have hvv : hvD s st' = hvD s st := funext (fun i => hvD_eq_of_wa (hvE i))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdd, hrr, hdn, hvv, hhh, hhE, hinsE]; exact K.soft
  · rw [hvv, hdE ii]; exact K.hole
  · intro j hj hjr
    have hj' : j < st.w "h" := by rw [← hhE]; exact hj
    rw [hdE j]
    exact K.xle j hj' hjr
  · intro i hi
    have hi' : i < st.w "h" := by rw [← hhE]; exact hi
    rcases K.pairs i hi' with h1 | h2 | h3
    · exact Or.inl ⟨h1.1, by rw [hvv]; exact h1.2.1, by rw [hdE i]; exact h1.2.2⟩
    · exact Or.inr (Or.inl ⟨h2.1, h2.2.1, by rw [hvv]; exact h2.2.2.1,
        by rw [hdE i]; exact h2.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨h3.1, by rw [hvv]; exact h3.2.1,
        by rw [hdE i]; exact h3.2.2⟩)
  · rw [hhh, hhE]; exact K.ok
  · rw [hhE]; exact K.origOK
  · rw [hhE]; exact K.leaf0
  · rw [hhE]; exact K.hiir

/-- One `siftUp` run: from a sift-up state with the hole at `ii`, the loop restores `Inv`.
Cost: at most `12 * rk ii + 1` (each bubble step is ≤ 12 statements including its test). -/
theorem siftUp_runs {st : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0} {ii₀ ii : ℕ}
    (hF : F0 G s st) (hAF : AF G st)
    (hval : HeapV (G := G) st (st.w "h"))
    (K : SiftUpOK s st origHv origHd x xk ii₀ ii)
    (hiiE : st.w "ii" = ii) (hbound : st.w "h" ≤ G.m + 1) :
    Runs realOps siftUp st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      EntrySoft s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      HeapOK (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") ∧
      st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      HeapV (G := G) st' (st'.w "h") ∧ HeapFrame st st' ∧
      st'.cost ≤ st.cost + 12 * rk ii + 1) := by
  have hnpos : 0 < G.n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hcap0 : 2 < st.cap := by have := hF.hcap; omega
  refine runs_while_nat (I := fun q st' => ∃ ii', SiftUpOK s st' origHv origHd x xk ii₀ ii' ∧
      F0 G s st' ∧ AF G st' ∧ st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      q ≤ rk ii ∧
      ((st'.w "ii" = ii' ∧ 0 < ii' ∧ q = rk ii') ∨
       (st'.w "ii" = 0 ∧ q = 0 ∧ (ii' = 0 ∨ st'.va "hd" (par ii') ≤ st'.va "hd" ii'))) ∧
      HeapV (G := G) st' (st'.w "h") ∧ HeapFrame st st' ∧
      st'.cost ≤ st.cost + 12 * (rk ii - q))
    (Q := fun st' => F0 G s st' ∧ AF G st' ∧
      EntrySoft s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      HeapOK (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") ∧
      st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      HeapV (G := G) st' (st'.w "h") ∧ HeapFrame st st' ∧
      st'.cost ≤ st.cost + 12 * rk ii + 1) ?_ (rk ii) st
      ⟨ii, K, hF, hAF, rfl, rfl, le_rfl, ?_, hval, HeapFrame.trivial st, ?_⟩
  · -- hstep
    intro q s' ⟨ii', K', hF', hAF', hh', hins', hle, hmode, hV', hfr, hcost⟩
    have hcap' : 2 < s'.cap := by have := hF'.hcap; omega
    have hcond : evalW s' (lt (lit 0) (var "ii")) = some (if 0 < s'.w "ii" then 1 else 0) :=
      evalW_lt_of (x := 0) (y := s'.w "ii") (evalW_lit_of (by have := hcap'; omega))
        (by rw [evalW_var]) (by have := hcap'; omega)
    have hhiir : ii' < s'.w "h" := K'.hiir
    have hhlt : ii' < st.w "h" := by rw [← hh']; exact hhiir
    have hhdL : s'.vlen "hd" = G.m + 1 := hAF'.hdL
    have hhvL : s'.wlen "hv" = G.m + 1 := hAF'.hvL
    by_cases htest : s'.w "ii" = 0
    · -- test reads 0: exit into Q
      refine ⟨0, ?_, (fun hz => (hz rfl).elim), fun _ => ?_⟩
      · rw [hcond, htest]; simp
      · rcases hmode with h1 | h2
        · rw [h1.1] at htest; exact absurd htest (by omega)
        · refine ⟨F0.charge hF' 1, AF.charge hAF' 1, ?_, ?_, ?_, ?_, ?_, hfr.charge 1, ?_⟩
          · exact K'.soft
          · have hedge : ¬(par ii' < s'.w "h" ∧ ii' < s'.w "h" ∧
                (ii' = 2 * par ii' + 1 ∨ ii' = 2 * par ii' + 2)) ∨
                s'.va "hd" (par ii') ≤ s'.va "hd" ii' := by
              rcases h2.2.2 with hz | hle
              · left; simp [par, hz]
              · exact Or.inr hle
            exact HeapOKExcept.toHeapOK K'.ok hedge
          · rw [show (s'.charge 1).w "h" = s'.w "h" from rfl, hh']
          · rw [show (s'.charge 1).w "ins" = s'.w "ins" from rfl, hins']
          · exact hV'
          · rw [show (s'.charge 1).cost = s'.cost + 1 from rfl]
            have hq0 : q = 0 := h2.2.1
            omega
    · -- body branch: only mode 1 reaches it
      rcases hmode with h1 | h2
      · have hpos : 0 < ii' := h1.2.1
        have hparlt : par ii' < s'.w "h" := lt_trans (par_lt ii' hpos) hhiir
        refine ⟨1, ?_, fun _ => ?_, fun hz => (one_ne_zero hz).elim⟩
        · rw [hcond, h1.1]; simp [hpos]
        · -- body: wset p, vle b, ite b (swap | stop)
          set t0 := s'.charge 1 with ht0
          have hii0 : evalW t0 (var "ii") = some ii' := by
            rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [h1.1]
          have h1E : evalW t0 (lit 1) = some 1 := evalW_lit_of (by show 1 < s'.cap; omega)
          have h2E : evalW t0 (lit 2) = some 2 := evalW_lit_of (by show 2 < s'.cap; omega)
          have hpE : evalW t0 (div (sub (var "ii") (lit 1)) (lit 2)) = some (par ii') :=
            evalW_div_of (evalW_sub_of hii0 h1E) h2E (by norm_num)
          refine runs_seq (runs_wset hpE ?_)
          set t1 := (t0.setW "p" (par ii')).charge 1 with ht1
          have hii1 : evalW t1 (var "ii") = some ii' := by
            rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [h1.1]
          have hp1 : evalW t1 (var "p") = some (par ii') := by rw [evalW_var]; rfl
          have hvl1 : ii' < t1.vlen "hd" := by
            have hL : t1.vlen "hd" = G.m + 1 := hhdL; rw [hL]; omega
          have hvl2 : par ii' < t1.vlen "hd" := by
            have hL : t1.vlen "hd" = G.m + 1 := hhdL; rw [hL]
            have := par_lt ii' hpos; omega
          have hav1 : evalV realOps t1 (VExpr.load "hd" (var "ii")) = some (t1.va "hd" ii') :=
            evalV_load_of hii1 hvl1
          have hav2 : evalV realOps t1 (VExpr.load "hd" (var "p")) = some (t1.va "hd" (par ii')) :=
            evalV_load_of hp1 hvl2
          refine runs_seq (runs_vle (x := "b") hav1 hav2 (by show 1 < s'.cap; omega) ?_)
          set t2 := (t1.setW "b" (if realOps.le (t1.va "hd" ii') (t1.va "hd" (par ii'))
            then 1 else 0)).charge 1 with ht2
          have hbval : t2.w "b" = if xk ≤ s'.va "hd" (par ii') then 1 else 0 := by
            show (if realOps.le (t1.va "hd" ii') (t1.va "hd" (par ii')) then 1 else 0) = _
            rw [bit_le]
            show (if s'.va "hd" ii' ≤ s'.va "hd" (par ii') then 1 else 0) = _
            rw [K'.hole.2]
          have hbE : evalW t2 (var "b") = some (t2.w "b") := evalW_var t2 "b"
          by_cases hsw : xk ≤ s'.va "hd" (par ii')
          · -- swap branch: the bubble step
            have hb1 : t2.w "b" = 1 := by rw [hbval, if_pos hsw]
            refine runs_ite_true hbE (by rw [hb1]; norm_num) ?_
            set t3 := t2.charge 1 with ht3
            have hii3 : evalW t3 (var "ii") = some ii' := by
              rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [h1.1]
            have hvl3 : ii' < t3.vlen "hd" := by
              have hL : t3.vlen "hd" = G.m + 1 := hhdL; rw [hL]; omega
            have hav3 : evalV realOps t3 (VExpr.load "hd" (var "ii")) = some (t3.va "hd" ii') :=
              evalV_load_of hii3 hvl3
            refine runs_seq (runs_vset (x := "tv") hav3 ?_)
            set t4 := (t3.setV "tv" (t3.va "hd" ii')).charge 1 with ht4
            have hii4 : evalW t4 (var "ii") = some ii' := by
              rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [h1.1]
            have hp4 : evalW t4 (var "p") = some (par ii') := by rw [evalW_var]; rfl
            have hvl4 : ii' < t4.vlen "hd" := by
              have hL : t4.vlen "hd" = G.m + 1 := hhdL; rw [hL]; omega
            have hvl4b : par ii' < t4.vlen "hd" := by
              have hL : t4.vlen "hd" = G.m + 1 := hhdL; rw [hL]
              have := par_lt ii' hpos; omega
            have hav4 : evalV realOps t4 (VExpr.load "hd" (var "p"))
                = some (t4.va "hd" (par ii')) := evalV_load_of hp4 hvl4b
            refine runs_seq (runs_vstore (arr := "hd") hii4 hav4 hvl4 ?_)
            set t5 := (t4.storeV "hd" ii' (t4.va "hd" (par ii'))).charge 1 with ht5
            have hp5 : evalW t5 (var "p") = some (par ii') := by rw [evalW_var]; rfl
            have hvl5b : par ii' < t5.vlen "hd" := by
              have hL : t5.vlen "hd" = G.m + 1 := hhdL; rw [hL]
              have := par_lt ii' hpos; omega
            have htv5 : evalV realOps t5 (VExpr.var "tv") = some (s'.va "hd" ii') := rfl
            refine runs_seq (runs_vstore (arr := "hd") hp5 htv5 hvl5b ?_)
            set t6 := (t5.storeV "hd" (par ii') (s'.va "hd" ii')).charge 1 with ht6
            have hii6 : evalW t6 (var "ii") = some ii' := by
              rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [h1.1]
            have hwl6 : ii' < t6.wlen "hv" := by
              have hL : t6.wlen "hv" = G.m + 1 := hhvL; rw [hL]; omega
            have htw6 : evalW t6 (load "hv" (var "ii")) = some (s'.wa "hv" ii') :=
              evalW_load_of hii6 hwl6
            refine runs_seq (runs_wset (x := "tw") htw6 ?_)
            set t7 := (t6.setW "tw" (s'.wa "hv" ii')).charge 1 with ht7
            have hii7 : evalW t7 (var "ii") = some ii' := by
              rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [h1.1]
            have hp7 : evalW t7 (var "p") = some (par ii') := by rw [evalW_var]; rfl
            have hwl7 : ii' < t7.wlen "hv" := by
              have hL : t7.wlen "hv" = G.m + 1 := hhvL; rw [hL]; omega
            have hwl7b : par ii' < t7.wlen "hv" := by
              have hL : t7.wlen "hv" = G.m + 1 := hhvL; rw [hL]
              have := par_lt ii' hpos; omega
            have hiv7 : evalW t7 (load "hv" (var "ii")) = some (s'.wa "hv" ii') :=
              evalW_load_of hii7 hwl7
            have hpv7 : evalW t7 (load "hv" (var "p")) = some (s'.wa "hv" (par ii')) :=
              evalW_load_of hp7 hwl7b
            refine runs_seq (runs_wstore (arr := "hv") hii7 hpv7 hwl7 ?_)
            set t8 := (t7.storeW "hv" ii' (s'.wa "hv" (par ii'))).charge 1 with ht8
            have hp8 : evalW t8 (var "p") = some (par ii') := by rw [evalW_var]; rfl
            have htw8 : evalW t8 (var "tw") = some (s'.wa "hv" ii') := by rw [evalW_var]; rfl
            have hwl8 : par ii' < t8.wlen "hv" := by
              have hL : t8.wlen "hv" = G.m + 1 := hhvL; rw [hL]
              have := par_lt ii' hpos; omega
            refine runs_seq (runs_wstore (arr := "hv") hp8 htw8 hwl8 ?_)
            set t9 := (t8.storeW "hv" (par ii') (s'.wa "hv" ii')).charge 1 with ht9
            have hp9 : evalW t9 (var "p") = some (par ii') := by rw [evalW_var]; rfl
            refine runs_wset (x := "ii") hp9 ?_
            set t10 := (t9.setW "ii" (par ii')).charge 1 with ht10
            -- post: the invariant at the risen hole
            have htv : t5.v "tv" = s'.va "hd" ii' := rfl
            have e4 : ∀ i, t4.va "hd" i = s'.va "hd" i := fun i => rfl
            have g4 : ∀ i, t7.wa "hv" i = s'.wa "hv" i := fun i => rfl
            have htw : t7.w "tw" = s'.wa "hv" ii' := rfl
            have e2 : ∀ i, t6.va "hd" i = if i = par ii' then s'.va "hd" ii' else t5.va "hd" i := by
              intro i
              rw [ht6, va_charge, va_storeV]; simp [htv]
            have e3 : ∀ i, t5.va "hd" i = if i = ii' then t4.va "hd" (par ii')
                else t4.va "hd" i := by
              intro i
              rw [ht5, va_charge, va_storeV]; simp
            have f2 : ∀ i, t9.wa "hv" i = if i = par ii' then s'.wa "hv" ii' else t8.wa "hv" i := by
              intro i
              rw [ht9, wa_charge, wa_storeW]; simp
            have f3 : ∀ i, t8.wa "hv" i = if i = ii' then s'.wa "hv" (par ii')
                else t7.wa "hv" i := by
              intro i
              rw [ht8, wa_charge, wa_storeW]; simp
            have hhd : ∀ i, t10.va "hd" i = if i = par ii' then s'.va "hd" ii'
                else if i = ii' then s'.va "hd" (par ii') else s'.va "hd" i := by
              intro i
              have e1 : t10.va "hd" i = t6.va "hd" i := rfl
              rw [e1, e2, e3]
              split_ifs
              · rfl
              · exact e4 (par ii')
              · exact e4 i
            have heqd : ∀ i, t10.va "hd" i = if i = ii' then s'.va "hd" (par ii')
                else if i = par ii' then s'.va "hd" ii' else s'.va "hd" i := by
              intro i
              rw [hhd]
              by_cases hi : i = ii'
              · rw [hi]
                have hne : ¬ (ii' = par ii') := (par_ne ii' hpos).symm
                simp [hne]
              · by_cases hp : i = par ii'
                · rw [hp]
                  simp [par_ne ii' hpos]
                · simp [hi, hp]
            have hwaE : ∀ i, t10.wa "hv" i = if i = par ii' then s'.wa "hv" ii'
                else if i = ii' then s'.wa "hv" (par ii') else s'.wa "hv" i := by
              intro i
              have e1 : t10.wa "hv" i = t9.wa "hv" i := rfl
              rw [e1, f2, f3]
              split_ifs
              · rfl
              · rfl
              · exact g4 i
            have heqv : ∀ i, hvD s t10 i = if i = ii' then hvD s s' (par ii')
                else if i = par ii' then hvD s s' ii' else hvD s s' i := by
              intro i
              by_cases hi : i = ii'
              · rw [hi]
                have hw : t10.wa "hv" ii' = s'.wa "hv" (par ii') := by
                  rw [hwaE]; simp [Ne.symm (par_ne ii' hpos)]
                have key := hvD_eq_of_wa (s := s) hw
                simp [key]
              · by_cases hp : i = par ii'
                · rw [hp]
                  have hw : t10.wa "hv" (par ii') = s'.wa "hv" ii' := by
                    rw [hwaE]; simp
                  have key := hvD_eq_of_wa (s := s) hw
                  simp [key, par_ne ii' hpos]
                · have hw : t10.wa "hv" i = s'.wa "hv" i := by
                    rw [hwaE]; simp [hi, hp]
                  have key := hvD_eq_of_wa (s := s) hw
                  simp [key, hi, hp]
            have hK10 : SiftUpOK s t10 origHv origHd x xk ii₀ (par ii') :=
              SiftUpOK.swap K' (hii := hpos) (hlt := K'.hiir) (hh := rfl) (hins := rfl)
                (hswap := hsw) (hdist := fun _ => rfl) (hreach := fun _ => rfl)
                (hdone := fun _ => rfl) (heqv := heqv) (heqd := heqd)
            have hF10 : F0 G s t10 :=
              F0.preserve hF' rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                (fun _ _ => rfl) rfl rfl rfl
            have hAF10 : AF G t10 := AF.preserve hAF' rfl rfl rfl rfl rfl rfl rfl
            have hc10 : t10.cost = s'.cost + 11 := rfl
            have hV10 : HeapV (G := G) t10 (t10.w "h") := by
              intro i hi
              have hi' : i < s'.w "h" := by
                rw [show t10.w "h" = s'.w "h" from rfl] at hi; exact hi
              rw [hwaE]
              by_cases h1i : i = par ii'
              · rw [if_pos h1i]; exact hV' ii' K'.hiir
              · rw [if_neg h1i]
                by_cases h2i : i = ii'
                · rw [if_pos h2i]
                  exact hV' (par ii') (lt_trans (par_lt ii' hpos) K'.hiir)
                · rw [if_neg h2i]; exact hV' i hi'
            have hn' : rk (par ii') < q := by
              rw [h1.2.2]
              by_cases hz : par ii' = 0
              · rw [hz, rk_zero]; exact rk_pos hpos
              · have hpar := rk_par hpos
                have hpp := rk_pos hpos
                omega
            refine ⟨rk (par ii'), hn', par ii', hK10, hF10, hAF10, hh', hins', ?_, ?_, hV10,
              (hfr.trans ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
                fun _ => rfl, rfl⟩), ?_⟩
            · -- index bound
              omega
            · -- mode
              by_cases hz : par ii' = 0
              · exact Or.inr ⟨by rw [show t10.w "ii" = par ii' from rfl, hz],
                  by rw [hz, rk_zero], Or.inl hz⟩
              · exact Or.inl ⟨show t10.w "ii" = par ii' from rfl, by omega, rfl⟩
            · -- cost
              have hle1 : 1 ≤ q := by rw [h1.2.2]; exact rk_pos hpos
              rw [hc10]
              by_cases hz : par ii' = 0
              · rw [hz, rk_zero]; omega
              · have hpar := rk_par hpos
                omega
          · -- stop branch: `¬b` zeroes `ii`, hole stays
            have hb0 : t2.w "b" = 0 := by rw [hbval, if_neg hsw]
            refine runs_ite_false (by rw [hbE, hb0]) ?_
            set t3 := t2.charge 1 with ht3
            have h0E : evalW t3 (lit 0) = some 0 := evalW_lit_of (by show 0 < s'.cap; omega)
            refine runs_wset (a := 0) h0E ?_
            set tS := (t3.setW "ii" 0).charge 1 with htS
            have hK2 : SiftUpOK s tS origHv origHd x xk ii₀ ii' :=
              SiftUpOK.stable K' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) rfl rfl
            have hF2 : F0 G s tS :=
              F0.preserve hF' rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                (fun _ _ => rfl) rfl rfl rfl
            have hAF2 : AF G tS := AF.preserve hAF' rfl rfl rfl rfl rfl rfl rfl
            have hcS : tS.cost = s'.cost + 5 := rfl
            have hVS : HeapV (G := G) tS (tS.w "h") := by
              intro i hi
              have hi' : i < s'.w "h" := by
                rw [show tS.w "h" = s'.w "h" from rfl] at hi; exact hi
              exact hV' i hi'
            have hle2 : s'.va "hd" (par ii') ≤ s'.va "hd" ii' := by
              have hlt : s'.va "hd" (par ii') < xk := lt_of_not_ge hsw
              rw [K'.hole.2]
              exact le_of_lt hlt
            refine ⟨0, by rw [h1.2.2]; exact rk_pos hpos, ii', hK2, hF2, hAF2, hh', hins',
              ?_, ?_, hVS, (hfr.trans ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl,
                fun _ => rfl, fun _ => rfl, rfl⟩), ?_⟩
            · omega
            · refine Or.inr ⟨show tS.w "ii" = 0 from rfl, rfl, Or.inr ?_⟩
              show tS.va "hd" (par ii') ≤ tS.va "hd" ii'
              exact hle2
            · have hle1 : 1 ≤ q := by rw [h1.2.2]; exact rk_pos hpos
              rw [hcS]; omega
      · exact absurd h2.1 htest
  · -- initial: mode
    rcases (Nat.eq_zero_or_pos ii) with hz | hp
    · right
      refine ⟨by rw [hiiE, hz], by rw [hz, rk_zero], Or.inl hz⟩
    · left
      exact ⟨hiiE, hp, rfl⟩
  · -- initial: cost
    have : rk ii - rk ii = 0 := Nat.sub_self _
    omega

/-- One `pushBody` run: store the new entry at `h`, bump `h`/`ins`, sift up.  The caller
guarantees the pushed vertex `pv` is reached (`reach[pv] ≠ 0`).  Cost: `12 * rk h + 13`. -/
theorem pushBody_runs {st : State ℝ≥0}
    (hF : F0 G s st) (hAF : AF G st)
    (hpv : st.w "pv" < G.n)
    (hsoft : EntrySoftH ⟨st.w "pv", hpv⟩ s (fun v => st.va "dist" v) (fun v => st.wa "reach" v)
      (fun v => st.wa "done" v) (hvD s st) (fun i => st.va "hd" i) (st.w "h") (st.w "ins"))
    (hheap : HeapOK (hvD s st) (fun i => st.va "hd" i) (st.w "h"))
    (hval : HeapV (G := G) st (st.w "h"))
    (hreachv : st.wa "reach" (st.w "pv") ≠ 0)
    (hbound : st.w "h" ≤ G.m) (hinsb : st.w "ins" ≤ G.m) :
    Runs realOps pushBody st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      EntrySoft s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      HeapOK (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") ∧
      st'.w "h" = st.w "h" + 1 ∧ st'.w "ins" = st.w "ins" + 1 ∧
      HeapV (G := G) st' (st'.w "h") ∧ HeapFrame st st' ∧
      st'.cost ≤ st.cost + 12 * rk (st.w "h") + 13) := by
  have hcap : 2 < st.cap := by have := hF.hcap; omega
  have hhE : evalW st (var "h") = some (st.w "h") := evalW_var st "h"
  have hpvE : evalW st (var "pv") = some (st.w "pv") := evalW_var st "pv"
  have hb1 : st.w "h" < st.wlen "hv" := by rw [hAF.hvL]; omega
  refine runs_seq (runs_wstore hhE hpvE hb1 ?_)
  set t1 := (st.storeW "hv" (st.w "h") (st.w "pv")).charge 1 with ht1
  have hh1 : evalW t1 (var "h") = some (st.w "h") := by rw [evalW_var]; rfl
  have hwl1 : st.w "h" < t1.vlen "hd" := by
    have hL : t1.vlen "hd" = G.m + 1 := hAF.hdL; rw [hL]; omega
  have hpl1 : st.w "pv" < t1.vlen "dist" := by
    have hL : t1.vlen "dist" = G.n := hAF.distL; rw [hL]; exact hpv
  have hdp1 : evalV realOps t1 (VExpr.load "dist" (var "pv")) = some (t1.va "dist" (st.w "pv")) :=
    evalV_load_of (by rw [evalW_var]; rfl) hpl1
  refine runs_seq (runs_vstore (arr := "hd") hh1 hdp1 hwl1 ?_)
  set t2 := (t1.storeV "hd" (st.w "h") (t1.va "dist" (st.w "pv"))).charge 1 with ht2
  have hh2 : evalW t2 (var "h") = some (st.w "h") := by rw [evalW_var]; rfl
  refine runs_seq (runs_wset (x := "ii") hh2 ?_)
  set t3 := (t2.setW "ii" (st.w "h")).charge 1 with ht3
  have hadd3 : evalW t3 (add (var "h") (lit 1)) = some (st.w "h" + 1) := by
    apply evalW_add_of
    · rw [evalW_var]; rfl
    · exact evalW_lit_of (by show 1 < st.cap; omega)
    · show (st.w "h" + 1) < st.cap; have hc' := hF.hcap; omega
  refine runs_seq (runs_wset (x := "h") hadd3 ?_)
  set t4 := (t3.setW "h" (st.w "h" + 1)).charge 1 with ht4
  have hadd4 : evalW t4 (add (var "ins") (lit 1)) = some (st.w "ins" + 1) := by
    apply evalW_add_of
    · rw [evalW_var]; rfl
    · exact evalW_lit_of (by show 1 < st.cap; omega)
    · show (st.w "ins" + 1) < st.cap; have hc' := hF.hcap; omega
  refine runs_seq (runs_wset (x := "ins") hadd4 ?_)
  set t5 := (t4.setW "ins" (st.w "ins" + 1)).charge 1 with ht5
  -- composed push effects
  have eA : ∀ i, t5.va "hd" i = if i = st.w "h" then t1.va "dist" (st.w "pv")
      else t1.va "hd" i := by
    intro i
    have e1 : t5.va "hd" i = t2.va "hd" i := rfl
    rw [e1, ht2, va_charge, va_storeV]
    simp
  have hhd5 : ∀ i, t5.va "hd" i = if i = st.w "h" then st.va "dist" (st.w "pv")
      else st.va "hd" i := by
    intro i
    have e2 : t1.va "hd" i = st.va "hd" i := rfl
    have e3 : t1.va "dist" (st.w "pv") = st.va "dist" (st.w "pv") := rfl
    rw [eA, e3, e2]
  have hwa5 : ∀ i, t5.wa "hv" i = if i = st.w "h" then st.w "pv" else st.wa "hv" i := by
    intro i
    have e1 : t5.wa "hv" i = t1.wa "hv" i := rfl
    rw [e1, ht1, wa_charge, wa_storeW]
    simp
  have hhv5 : ∀ i, hvD s t5 i = if i = st.w "h" then ⟨st.w "pv", hpv⟩ else hvD s st i := by
    intro i
    by_cases hi : i = st.w "h"
    · rw [hi, if_pos rfl]
      show hvD s t5 (st.w "h") = ⟨st.w "pv", hpv⟩
      simp only [hvD]
      rw [hwa5, if_pos rfl]
      exact dif_pos hpv
    · rw [if_neg hi]
      have hw : t5.wa "hv" i = st.wa "hv" i := by rw [hwa5, if_neg hi]
      exact hvD_eq_of_wa hw
  have hh5 : t5.w "h" = st.w "h" + 1 := rfl
  have hins5 : t5.w "ins" = st.w "ins" + 1 := rfl
  have hfr5 : HeapFrame st t5 :=
    ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have hV5 : HeapV (G := G) t5 (t5.w "h") := by
    intro i hi
    rw [hwa5]
    by_cases hz : i = st.w "h"
    · rw [if_pos hz]; exact hpv
    · rw [if_neg hz]
      have hi' : i < st.w "h" := by rw [hh5] at hi; omega
      exact hval i hi'
  -- the sift-up state at the new entry
  have hK : SiftUpOK s t5 (fun i => if i = st.w "h" then ⟨st.w "pv", hpv⟩ else hvD s st i)
      (fun i => if i = st.w "h" then st.va "dist" (st.w "pv") else st.va "hd" i)
      ⟨st.w "pv", hpv⟩ (st.va "dist" (st.w "pv")) (st.w "h") (st.w "h") := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- soft
      refine ⟨?_, ?_, ?_⟩
      · intro v hrv hd0
        by_cases hvp : v = ⟨st.w "pv", hpv⟩
        · rw [hvp]
          exact ⟨st.w "h", by rw [hh5]; omega, by rw [hhv5, if_pos rfl],
            by rw [hhd5, if_pos rfl]; rfl⟩
        · obtain ⟨i, hi, hvi, hdi⟩ := hsoft.entry_hole v hvp hrv hd0
          refine ⟨i, by rw [hh5]; omega, ?_, ?_⟩
          · rw [hhv5, if_neg (by omega)]; exact hvi
          · rw [hhd5, if_neg (by omega)]; exact hdi
      · intro i hi
        by_cases hiz : i = st.w "h"
        · rw [hiz, hhd5, if_pos rfl, hhv5, if_pos rfl]
          show st.va "dist" (st.w "pv") ≤ st.va "dist" (st.w "pv")
          exact le_rfl
        · rw [hhd5, if_neg hiz, hhv5, if_neg hiz]
          exact hsoft.entry_mono i (by have := hh5; omega)
      · intro i hi
        by_cases hiz : i = st.w "h"
        · rw [hiz, hhv5, if_pos rfl]
          show st.wa "reach" (st.w "pv") ≠ 0
          exact hreachv
        · rw [hhv5, if_neg hiz]
          exact hsoft.entry_reach i (by have := hh5; omega)
    · -- hole
      refine ⟨?_, ?_⟩
      · rw [hhv5, if_pos rfl]
      · rw [hhd5, if_pos rfl]
    · -- xle (children of h are out of range)
      intro j hj hjr
      rw [hhd5]
      by_cases hz : j = st.w "h"
      · rw [hz, if_pos rfl] <;> try exact le_rfl
      · rw [if_neg hz]
        rcases hjr with hr | hr <;> omega
    · -- pairs
      intro i hi
      by_cases hiz : i = st.w "h"
      · refine Or.inl ⟨hiz, ?_, ?_⟩
        · rw [hiz, hhv5, if_pos rfl]
        · rw [hiz, hhd5, if_pos rfl]
      · refine Or.inr (Or.inr ⟨hiz, ?_, ?_⟩)
        · show hvD s t5 i = (if i = st.w "h" then ⟨st.w "pv", hpv⟩ else hvD s st i)
          rw [hhv5, if_neg hiz]
        · show t5.va "hd" i = (if i = st.w "h" then st.va "dist" (st.w "pv") else st.va "hd" i)
          rw [hhd5, if_neg hiz]
    · -- ok: only the edge into h can fail
      intro i j hi hj hjr hneq
      by_cases hjh : j = st.w "h"
      · have hip : i = par (st.w "h") := by
          rw [hjh] at hjr
          exact (par_of_child hjr).symm
        exact absurd ⟨hip, hjh⟩ hneq
      · by_cases hih : i = st.w "h"
        · rw [hih] at hjr; omega
        · show t5.va "hd" i ≤ t5.va "hd" j
          rw [hhd5 i, if_neg hih, hhd5 j, if_neg hjh]
          exact hheap i (by have := hh5; omega) j (by have := hh5; omega) hjr
    · -- origOK
      intro i j hi hj hjr hneq
      by_cases hjh : j = st.w "h"
      · have hip : i = par (st.w "h") := by
          rw [hjh] at hjr
          exact (par_of_child hjr).symm
        exact absurd ⟨hip, hjh⟩ hneq
      · by_cases hih : i = st.w "h"
        · rw [hih] at hjr; omega
        · show (if i = st.w "h" then st.va "dist" (st.w "pv") else st.va "hd" i)
            ≤ (if j = st.w "h" then st.va "dist" (st.w "pv") else st.va "hd" j)
          rw [if_neg hih, if_neg hjh]
          exact hheap i (by have := hh5; omega) j (by have := hh5; omega) hjr
    · rw [hh5]; omega
    · rw [hh5]; omega
  -- run the sift
  have hF5 : F0 G s t5 :=
    F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl
  have hAF5 : AF G t5 := AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl
  have hbound5 : t5.w "h" ≤ G.m + 1 := by rw [hh5]; omega
  refine (siftUp_runs hF5 hAF5 hV5 hK rfl hbound5).mono ?_
  rintro st' ⟨hF', hAF', hsoft', hheap', hheq, hinseq, hV', hfr', hcost⟩
  refine ⟨hF', hAF', hsoft', hheap', ?_, ?_, hV', ?_, ?_⟩
  · rw [hheq, hh5]
  · rw [hinseq, hins5]
  · exact hfr5.trans hfr'
  · have hc5 : t5.cost = st.cost + 5 := rfl
    rw [hc5] at hcost
    omega

/-! ## `siftDown`: bubble-down machinery -/

/-- Min-child selection of one sift-down step (right child preferred on ties,
matching `siftDownStep`). -/
noncomputable def mchOf (origHd : ℕ → ℝ≥0) (h i : ℕ) : ℕ :=
  if 2 * i + 2 < h then (if origHd (2 * i + 2) ≤ origHd (2 * i + 1) then 2 * i + 2 else 2 * i + 1)
  else 2 * i + 1

theorem mchOf_child (origHd : ℕ → ℝ≥0) (h i : ℕ) :
    mchOf origHd h i = 2 * i + 1 ∨ mchOf origHd h i = 2 * i + 2 := by
  simp only [mchOf]; split_ifs <;> omega

theorem mchOf_gt (origHd : ℕ → ℝ≥0) (h i : ℕ) : i < mchOf origHd h i := by
  have := mchOf_child origHd h i; omega

theorem mchOf_iter_le (origHd : ℕ → ℝ≥0) (h i : ℕ) : ∀ t, i ≤ (mchOf origHd h)^[t] i := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [Function.iterate_succ_apply']
    exact ih.trans (mchOf_gt origHd h ((mchOf origHd h)^[t] i)).le

theorem mchOf_inj (origHd : ℕ → ℝ≥0) (h : ℕ) {i j : ℕ}
    (heq : mchOf origHd h i = mchOf origHd h j) : i = j := by
  have a := mchOf_child origHd h i
  have b := mchOf_child origHd h j
  omega

/-- Reachability along a successor function. -/
def sreach (f : ℕ → ℕ) (a b : ℕ) : Prop := ∃ t, f^[t] a = b

theorem sreach_self (f : ℕ → ℕ) (a : ℕ) : sreach f a a := ⟨0, rfl⟩

theorem sreach_trans {f : ℕ → ℕ} {a b c : ℕ} (h1 : sreach f a b) (h2 : sreach f b c) :
    sreach f a c := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  refine ⟨t2 + t1, ?_⟩
  rw [Function.iterate_add_apply, ht1, ht2]

theorem sreach_succ_iff {f : ℕ → ℕ} (hinj : Function.Injective f) {a b : ℕ} :
    sreach f a (f b) ↔ a = f b ∨ sreach f a b := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with _ | t
    · exact Or.inl ht
    · simp only [Function.iterate_succ_apply'] at ht
      exact Or.inr ⟨t, hinj ht⟩
  · rintro (h | ⟨t, ht⟩)
    · exact ⟨0, h⟩
    · exact ⟨t + 1, by simp only [Function.iterate_succ_apply', ht]⟩

/-- Heap order on every edge except those out of position `a`. -/
def HeapOKExceptFrom (hd : ℕ → ℝ≥0) (h a : ℕ) : Prop :=
  ∀ i j, i < h → j < h → (j = 2 * i + 1 ∨ j = 2 * i + 2) → i ≠ a → hd i ≤ hd j

theorem HeapOKExceptFrom.toHeapOK {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h a : ℕ}
    (H : HeapOKExceptFrom hd h a)
    (hchild : ∀ j, j < h → (j = 2 * a + 1 ∨ j = 2 * a + 2) → hd a ≤ hd j) :
    HeapOK hv hd h := by
  intro i hi j hj hjr
  by_cases hia : i = a
  · subst hia; exact hchild j hj hjr
  · exact H i j hi hj hjr hia

/-- The sift-down state: hole at `ii`, pairs are originals shifted along the
min-child path (risen pairs), heap order holds except the edges out of the hole. -/
structure SiftDownOK (holev : Fin G.n) (s : Fin G.n) (st : State ℝ≥0)
    (origHv : ℕ → Fin G.n) (origHd : ℕ → ℝ≥0)
    (x : Fin G.n) (xk : ℝ≥0) (ii : ℕ) : Prop where
  soft : SoftInvH holev s (fun v => st.va "dist" v) (fun v => st.wa "reach" v)
      (fun v => st.wa "done" v) (hvD s st) (fun i => st.va "hd" i) (st.w "h") (st.w "ins")
  hole : hvD s st ii = x ∧ st.va "hd" ii = xk
  pairsV : ∀ i, i < st.w "h" →
      (i = ii ∧ hvD s st i = x) ∨
      (i ≠ ii ∧ sreach (mchOf origHd (st.w "h")) i ii ∧ sreach (mchOf origHd (st.w "h")) 0 i ∧
        hvD s st i = origHv (mchOf origHd (st.w "h") i)) ∨
      (¬ (sreach (mchOf origHd (st.w "h")) i ii ∧ sreach (mchOf origHd (st.w "h")) 0 i) ∧
        hvD s st i = origHv i)
  pairsK : ∀ i, i < st.w "h" →
      (i = ii ∧ st.va "hd" i = xk) ∨
      (i ≠ ii ∧ sreach (mchOf origHd (st.w "h")) i ii ∧ sreach (mchOf origHd (st.w "h")) 0 i ∧
        st.va "hd" i = origHd (mchOf origHd (st.w "h") i)) ∨
      (¬ (sreach (mchOf origHd (st.w "h")) i ii ∧ sreach (mchOf origHd (st.w "h")) 0 i) ∧
        st.va "hd" i = origHd i)
  ok : HeapOKExceptFrom (fun i => st.va "hd" i) (st.w "h") ii
  origOK : HeapOKExceptFrom origHd (st.w "h") 0
  pre0 : sreach (mchOf origHd (st.w "h")) 0 ii
  hiir : ii < st.w "h"

/-- One sift-down swap: the hole descends to the min child `c`. -/
theorem SiftDownOK.swap {holev : Fin G.n} {st st' : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0} {ii c : ℕ}
    (K : SiftDownOK holev s st origHv origHd x xk ii)
    (hc : c = mchOf origHd (st.w "h") ii)
    (hcin : c < st.w "h")
    (hswap : st.va "hd" c ≤ xk)
    (hmin : ∀ j, j < st.w "h" → (j = 2 * ii + 1 ∨ j = 2 * ii + 2) → st.va "hd" c ≤ st.va "hd" j)
    (hh : st'.w "h" = st.w "h") (hins : st'.w "ins" = st.w "ins")
    (hdist : ∀ v : Fin G.n, st'.va "dist" v = st.va "dist" v)
    (hreach : ∀ v : Fin G.n, st'.wa "reach" v = st.wa "reach" v)
    (hdone : ∀ v : Fin G.n, st'.wa "done" v = st.wa "done" v)
    (heqv : ∀ i, hvD s st' i = if i = ii then hvD s st c
        else if i = c then hvD s st ii else hvD s st i)
    (heqd : ∀ i, st'.va "hd" i = if i = ii then st.va "hd" c
        else if i = c then st.va "hd" ii else st.va "hd" i) :
    SiftDownOK holev s st' origHv origHd x xk c := by
  have hii : ii < st.w "h" := K.hiir
  have hgt : ii < c := by rw [hc]; exact mchOf_gt origHd (st.w "h") ii
  have hne : ii ≠ c := by omega
  set f : ℕ → ℕ := mchOf origHd (st.w "h") with hf
  have hinj : Function.Injective f := by
    intro a b heq
    apply mchOf_inj origHd (st.w "h")
    rw [← hf]; exact heq
  have hfeq : f ii = c := by rw [hf]; exact hc.symm
  have hpre : sreach f 0 c := sreach_trans K.pre0 ⟨1, hfeq⟩
  have hpar : 0 < ii → f (par ii) = ii ∧ sreach f 0 (par ii) := by
    intro hpos
    obtain ⟨t, ht⟩ := K.pre0
    rcases t with _ | t
    · simp at ht; omega
    · simp only [Function.iterate_succ_apply'] at ht
      have hfeq2 : mchOf origHd (st.w "h") (f^[t] 0) = ii := by rw [← hf]; exact ht
      have hfi : f^[t] 0 = par ii := by
        have hch := mchOf_child origHd (st.w "h") (f^[t] 0)
        simp only [par]
        rcases hch with h | h <;> rw [h] at hfeq2 <;> omega
      exact ⟨by rw [← hfi]; exact ht, ⟨t, hfi⟩⟩
  have hchain : ∀ {a b}, sreach f a b ↔ sreach (mchOf origHd (st.w "h")) a b := fun {a b} => Iff.rfl
  have hcorig : hvD s st c = origHv c ∧ st.va "hd" c = origHd c := by
    have hnf : ¬ (sreach f c ii ∧ sreach f 0 c) := by
      intro hh2
      obtain ⟨t, ht⟩ := hh2.1
      rcases t with _ | t
      · simp at ht; omega
      · simp only [Function.iterate_succ_apply'] at ht
        have hlt : f^[t] c < ii := by
          have := mchOf_gt origHd (st.w "h") (f^[t] c)
          rw [← hf, ht] at this
          exact this
        have hge : c ≤ f^[t] c := mchOf_iter_le origHd (st.w "h") c t
        omega
    rcases K.pairsV c hcin with h1 | h2 | h3
    · exact absurd h1.1 (Ne.symm hne)
    · exact (hnf ⟨h2.2.1, h2.2.2.1⟩).elim
    · rcases K.pairsK c hcin with a1 | a2 | a3
      · exact absurd a1.1 (Ne.symm hne)
      · exact (hnf ⟨a2.2.1, a2.2.2.1⟩).elim
      · exact ⟨h3.2, a3.2⟩
  have hdd : (fun v : Fin G.n => st'.va "dist" v) = (fun v : Fin G.n => st.va "dist" v) :=
    funext hdist
  have hrr : (fun v : Fin G.n => st'.wa "reach" v) = (fun v : Fin G.n => st.wa "reach" v) :=
    funext hreach
  have hdn : (fun v : Fin G.n => st'.wa "done" v) = (fun v : Fin G.n => st.wa "done" v) :=
    funext hdone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [hh]; exact hpre, ?_⟩
  · have hsw := K.soft.swap (hab := hne) (ha := hii) (hb := hcin)
      (hv' := hvD s st') (hd' := fun i => st'.va "hd" i) heqv heqd
    rw [← hdd, ← hrr, ← hdn, ← hh, ← hins] at hsw
    exact hsw
  · refine ⟨?_, ?_⟩
    · rw [heqv]; simp [Ne.symm hne]; exact K.hole.1
    · rw [heqd]; simp [Ne.symm hne]; exact K.hole.2
  · -- pairsV at the new hole `c`
    intro i hi
    have hi' : i < st.w "h" := by rw [← hh]; exact hi
    rw [hh]
    have hchain2 : sreach (mchOf origHd (st.w "h")) i c ↔
        i = c ∨ sreach (mchOf origHd (st.w "h")) i ii := by
      rw [← hf, ← hfeq]; exact sreach_succ_iff hinj
    by_cases hiz : i = c
    · exact Or.inl ⟨hiz, by rw [hiz, heqv]; simp [Ne.symm hne]; exact K.hole.1⟩
    · by_cases hii2 : i = ii
      · refine Or.inr (Or.inl ⟨by omega, ?_, ?_, ?_⟩)
        · rw [hchain2]; exact Or.inr (by rw [hii2]; exact sreach_self _ ii)
        · rw [hii2]; exact K.pre0
        · rw [hii2, heqv]; simp [Ne.symm hne]; exact hcorig.1.trans (congrArg origHv hc)
      · have h1 : hvD s st' i = hvD s st i := by
          rw [heqv, if_neg hii2, if_neg hiz]
        rcases K.pairsV i hi' with h2 | h3 | h4
        · exact absurd h2.1 hii2
        · refine Or.inr (Or.inl ⟨hiz, ?_, ?_, ?_⟩)
          · rw [hchain2]; exact Or.inr h3.2.1
          · exact h3.2.2.1
          · rw [h1]; exact h3.2.2.2
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · intro hh2
            have hh3 := hh2
            rw [hchain2] at hh3
            rcases hh3 with ⟨h | h, h0⟩
            · exact absurd h hiz
            · exact h4.1 ⟨h, h0⟩
          · rw [h1]; exact h4.2
  · -- pairsK at the new hole `c`
    intro i hi
    have hi' : i < st.w "h" := by rw [← hh]; exact hi
    rw [hh]
    have hchain2 : sreach (mchOf origHd (st.w "h")) i c ↔
        i = c ∨ sreach (mchOf origHd (st.w "h")) i ii := by
      rw [← hf, ← hfeq]; exact sreach_succ_iff hinj
    by_cases hiz : i = c
    · exact Or.inl ⟨hiz, by rw [hiz, heqd]; simp [Ne.symm hne]; exact K.hole.2⟩
    · by_cases hii2 : i = ii
      · refine Or.inr (Or.inl ⟨by omega, ?_, ?_, ?_⟩)
        · rw [hchain2]; exact Or.inr (by rw [hii2]; exact sreach_self _ ii)
        · rw [hii2]; exact K.pre0
        · rw [hii2, heqd]; simp [Ne.symm hne]; exact hcorig.2.trans (congrArg origHd hc)
      · have h1 : st'.va "hd" i = st.va "hd" i := by
          rw [heqd, if_neg hii2, if_neg hiz]
        rcases K.pairsK i hi' with h2 | h3 | h4
        · exact absurd h2.1 hii2
        · refine Or.inr (Or.inl ⟨hiz, ?_, ?_, ?_⟩)
          · rw [hchain2]; exact Or.inr h3.2.1
          · exact h3.2.2.1
          · rw [h1]; exact h3.2.2.2
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · intro hh2
            have hh3 := hh2
            rw [hchain2] at hh3
            rcases hh3 with ⟨h | h, h0⟩
            · exact absurd h hiz
            · exact h4.1 ⟨h, h0⟩
          · rw [h1]; exact h4.2
  · -- ok: heap order except the edges out of `c`
    intro i j hi hj hjr hnic
    show st'.va "hd" i ≤ st'.va "hd" j
    have hi' : i < st.w "h" := by rw [← hh]; exact hi
    have hj' : j < st.w "h" := by rw [← hh]; exact hj
    by_cases hci : i = ii
    · rw [hci]
      show st'.va "hd" ii ≤ st'.va "hd" j
      by_cases hcj : j = c
      · rw [hcj]; simp [heqd, Ne.symm hne]
        exact hswap.trans K.hole.2.symm.le
      · have e : st'.va "hd" j = st.va "hd" j := by
          rw [heqd, if_neg hcj, if_neg (by omega)]
        rw [e]; simp [heqd, Ne.symm hne]
        exact hmin j hj' (by rw [hci] at hjr; exact hjr)
    · have hjc : j ≠ c := by
        intro hhj
        rw [hhj] at hjr
        have hparc : i = par c := (par_of_child hjr).symm
        have hpi : par c = ii := by
          rw [hc]
          show par (mchOf origHd (st.w "h") ii) = ii
          exact par_of_child (mchOf_child origHd (st.w "h") ii)
        rw [hparc] at hci
        exact hci hpi
      have e1 : st'.va "hd" i = st.va "hd" i := by
        rw [heqd, if_neg hci, if_neg (by omega)]
      by_cases hcj : j = ii
      · -- edge into the old hole: its parent holds the risen pair `origHd ii`
        have hipar : i = par ii := by
          rw [hcj] at hjr
          exact (par_of_child hjr).symm
        have hpos : 0 < ii := by rcases hjr with hr | hr <;> omega
        have hpar' := hpar hpos
        have hp2 : mchOf origHd (st.w "h") (par ii) = ii := by rw [← hf]; exact hpar'.1
        have hle1 : st.va "hd" i = origHd ii := by
          rw [hipar]
          rcases K.pairsK (par ii) (by have hpt := par_lt ii hpos; omega)
            with h1 | h2 | h3
          · exact absurd h1.1 (by have hpt := par_lt ii hpos; omega)
          · rw [h2.2.2.2, hp2]
          · exact absurd ⟨⟨1, by rw [← hf]; exact hpar'.1⟩,
              by rw [← hf]; exact hpar'.2⟩ h3.1
        have hle2 : origHd c = st.va "hd" c := hcorig.2.symm
        rw [e1, hcj]; simp [heqd, Ne.symm hne]
        rw [hle1, ← hle2]
        exact K.origOK ii c (by omega) hcin
          (by rw [hc]; exact mchOf_child origHd (st.w "h") ii) (by omega)
      · have e2 : st'.va "hd" j = st.va "hd" j := by
          rw [heqd, if_neg hcj, if_neg hjc]
        rw [e1, e2]
        exact K.ok i j hi' hj' hjr hci
  · rw [hh]; exact K.origOK
  · rw [hh]; exact hcin

/-! ## `siftDown` loop: rank machinery -/

/-- Sift-down rank: the descent budget of hole `i` in a heap of size `h`. -/
def rkD (h i : ℕ) : ℕ := Nat.log 2 (h / (i + 1))

theorem rkD_zero (h : ℕ) : rkD h 0 = Nat.log 2 h := by
  simp [rkD]

/-- Division is antitone in the denominator (positive denominator). -/
theorem div_le_of_le_den {x a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : x / b ≤ x / a :=
  (Nat.le_div_iff_mul_le ha).2
    ((Nat.mul_le_mul_left (x / b) hab).trans (Nat.div_mul_le_self x b))

/-- One descent step drops the sift-down rank by at least one. -/
theorem rkD_succ_of_child {h i c : ℕ} (hc : c = 2 * i + 1 ∨ c = 2 * i + 2)
    (hi : 2 * i + 1 < h) : rkD h c + 1 ≤ rkD h i := by
  have hcd : 2 * (i + 1) ≤ c + 1 := by omega
  have hle : h / (c + 1) ≤ h / (2 * (i + 1)) := div_le_of_le_den (by omega) hcd
  have hm : h / (2 * (i + 1)) = (h / (i + 1)) / 2 := by
    rw [Nat.div_div_eq_div_mul]; congr 1; omega
  have hy : 2 ≤ h / (i + 1) := (Nat.le_div_iff_mul_le (by omega : 0 < i + 1)).2 (by omega)
  have hdrop : Nat.log 2 (h / (c + 1)) + 1 ≤ Nat.log 2 (h / (i + 1)) := by
    have h1 : Nat.log 2 (h / (c + 1)) ≤ Nat.log 2 ((h / (i + 1)) / 2) := by
      rw [← hm]; exact Nat.log_mono_right hle
    rw [Nat.log_div_base] at h1
    have h2 : 1 ≤ Nat.log 2 (h / (i + 1)) :=
      (Nat.le_log_iff_pow_le (by norm_num) (by omega : h / (i + 1) ≠ 0)).2 (by norm_num; omega)
    omega
  simpa [rkD] using hdrop

/-- A hole with a child has sift-down rank at least one. -/
theorem rkD_pos_of_child {h i : ℕ} (hi : 2 * i + 1 < h) : 1 ≤ rkD h i := by
  have hy : 2 ≤ h / (i + 1) := (Nat.le_div_iff_mul_le (by omega : 0 < i + 1)).2 (by omega)
  have hz : h / (i + 1) ≠ 0 := by omega
  rw [rkD]
  exact (Nat.le_log_iff_pow_le (by norm_num) hz).2 (by simpa using hy)

/-- The min child is minimal among the children. -/
theorem mchOf_min (origHd : ℕ → ℝ≥0) {h i c j : ℕ}
    (hc : c = mchOf origHd h i) (hj : j < h) (hjr : j = 2 * i + 1 ∨ j = 2 * i + 2) :
    origHd c ≤ origHd j := by
  by_cases hri : 2 * i + 2 < h
  · by_cases hle : origHd (2 * i + 2) ≤ origHd (2 * i + 1)
    · have hcm : c = 2 * i + 2 := by
        rw [hc]; simp only [mchOf]; rw [if_pos hri, if_pos hle]
      subst hcm
      rcases hjr with hr | hr
      · rw [hr]; exact hle
      · exact le_of_eq (congrArg origHd hr.symm)
    · have hcm : c = 2 * i + 1 := by
        rw [hc]; simp only [mchOf]; rw [if_pos hri, if_neg hle]
      subst hcm
      rcases hjr with hr | hr
      · exact le_of_eq (congrArg origHd hr.symm)
      · rw [hr]; exact le_of_lt (lt_of_not_ge hle)
  · have hcm : c = 2 * i + 1 := by
      rw [hc]; simp only [mchOf]; rw [if_neg hri]
    subst hcm
    rcases hjr with hr | hr
    · exact le_of_eq (congrArg origHd hr.symm)
    · rw [hr] at hj; omega

/-- Children of the hole hold their original pairs: the min-child path strictly
increases indices, so no child of the hole is on it. -/
theorem SiftDownOK.child_orig {holev : Fin G.n} {st : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0} {ii j : ℕ}
    (K : SiftDownOK holev s st origHv origHd x xk ii)
    (hj : j < st.w "h") (hjr : j = 2 * ii + 1 ∨ j = 2 * ii + 2) :
    hvD s st j = origHv j ∧ st.va "hd" j = origHd j := by
  have hjgt : ii < j := by omega
  have hne : j ≠ ii := by omega
  have hnreach : ¬sreach (mchOf origHd (st.w "h")) j ii := by
    rintro ⟨t, ht⟩
    have hle : j ≤ (mchOf origHd (st.w "h"))^[t] j := mchOf_iter_le origHd (st.w "h") j t
    rw [ht] at hle
    omega
  rcases K.pairsV j hj with h1 | h2 | h3
  · exact absurd h1.1 hne
  · exact absurd h2.2.1 hnreach
  · rcases K.pairsK j hj with a1 | a2 | a3
    · exact absurd a1.1 hne
    · exact absurd a2.2.1 hnreach
    · exact ⟨h3.2, a3.2⟩

/-- A sift-down state survives updates that leave the heap arrays, decoded labels and
sizes alone (register writes and charges). -/
theorem SiftDownOK.stable {holev : Fin G.n} {st st' : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0} {ii : ℕ}
    (K : SiftDownOK holev s st origHv origHd x xk ii)
    (hvE : ∀ i, st'.wa "hv" i = st.wa "hv" i)
    (hdE : ∀ i, st'.va "hd" i = st.va "hd" i)
    (hdistE : ∀ (v : Fin G.n), st'.va "dist" v = st.va "dist" v)
    (hreachE : ∀ (v : Fin G.n), st'.wa "reach" v = st.wa "reach" v)
    (hdoneE : ∀ (v : Fin G.n), st'.wa "done" v = st.wa "done" v)
    (hhE : st'.w "h" = st.w "h") (hinsE : st'.w "ins" = st.w "ins") :
    SiftDownOK holev s st' origHv origHd x xk ii := by
  have hdd : (fun (v : Fin G.n) => st'.va "dist" v) = (fun (v : Fin G.n) => st.va "dist" v) :=
    funext hdistE
  have hrr : (fun (v : Fin G.n) => st'.wa "reach" v) = (fun (v : Fin G.n) => st.wa "reach" v) :=
    funext hreachE
  have hdn : (fun (v : Fin G.n) => st'.wa "done" v) = (fun (v : Fin G.n) => st.wa "done" v) :=
    funext hdoneE
  have hhh : (fun i => st'.va "hd" i) = (fun i => st.va "hd" i) := funext hdE
  have hvv : hvD s st' = hvD s st := funext (fun i => hvD_eq_of_wa (hvE i))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdd, hrr, hdn, hvv, hhh, hhE, hinsE]; exact K.soft
  · rw [hvv, hdE ii]; exact K.hole
  · intro i hi
    have hi' : i < st.w "h" := by rw [← hhE]; exact hi
    rcases K.pairsV i hi' with h1 | h2 | h3
    · exact Or.inl ⟨h1.1, by rw [hvv]; exact h1.2⟩
    · exact Or.inr (Or.inl ⟨h2.1, by rw [hhE]; exact h2.2.1,
        by rw [hhE]; exact h2.2.2.1, by rw [hvv, hhE]; exact h2.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨by rw [hhE]; exact h3.1, by rw [hvv]; exact h3.2⟩)
  · intro i hi
    have hi' : i < st.w "h" := by rw [← hhE]; exact hi
    rcases K.pairsK i hi' with h1 | h2 | h3
    · exact Or.inl ⟨h1.1, by rw [hdE i]; exact h1.2⟩
    · exact Or.inr (Or.inl ⟨h2.1, by rw [hhE]; exact h2.2.1,
        by rw [hhE]; exact h2.2.2.1, by rw [hdE i, hhE]; exact h2.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨by rw [hhE]; exact h3.1, by rw [hdE i]; exact h3.2⟩)
  · rw [hhh, hhE]; exact K.ok
  · rw [hhE]; exact K.origOK
  · rw [hhE]; exact K.pre0
  · rw [hhE]; exact K.hiir

/-- The tail of one sift-down step: compare the hole against the min child `c`, swap or stop. -/
def siftDownTail : Stmt :=
  seq (vle "b" (.load "hd" (var "c")) (.load "hd" (var "ii")))
    (ite (var "b")
      (seq (vset "tv" (.load "hd" (var "ii")))
      (seq (vstore "hd" (var "ii") (.load "hd" (var "c")))
      (seq (vstore "hd" (var "c") (.var "tv"))
      (seq (wset "tw" (load "hv" (var "ii")))
      (seq (wstore "hv" (var "ii") (load "hv" (var "c")))
      (seq (wstore "hv" (var "c") (var "tw"))
           (wset "ii" (var "c"))))))))
      (wset "go" (lit 0)))

/-- Loop invariant for `siftDown_runs`: the index is the remaining descent measure
(rank + 1 while `go`, 0 once stopped). -/
def SiftDownInv (holev : Fin G.n) (st : State ℝ≥0) (origHv : ℕ → Fin G.n) (origHd : ℕ → ℝ≥0)
    (x : Fin G.n) (xk : ℝ≥0) (m : ℕ) (st' : State ℝ≥0) : Prop :=
  ∃ ii', SiftDownOK holev s st' origHv origHd x xk ii' ∧
    F0 G s st' ∧ AF G st' ∧
    st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
    ((st'.w "go" = 1 ∧ st'.w "ii" = ii' ∧ m = rkD (st.w "h") ii' + 1 ∧
        st'.cost ≤ st.cost + 2 + 18 * (rkD (st.w "h") 0 - rkD (st.w "h") ii') + 12) ∨
     (st'.w "go" = 0 ∧ m = 0 ∧
        (∀ j, j < st'.w "h" → (j = 2 * ii' + 1 ∨ j = 2 * ii' + 2) →
          st'.va "hd" ii' ≤ st'.va "hd" j) ∧
        st'.cost ≤ st.cost + 2 + 18 * rkD (st.w "h") 0 + 15)) ∧
    st'.w "v" = st.w "v" ∧ st'.v "dv" = st.v "dv" ∧
    HeapV (G := G) st' (st'.w "h")

/-- The root rank dominates every hole rank. -/
theorem rkD_le_zero {h i : ℕ} : rkD h i ≤ rkD h 0 := by
  have h1 : h / (i + 1) ≤ h / 1 := div_le_of_le_den (by omega) (by omega)
  simpa [rkD, Nat.div_one] using Nat.log_mono_right h1

/-- Swap-step budget: `+29` absorbed by one rank drop under `Kd = 18`. -/
theorem budget_swap {x q q' : ℕ} (hle : q ≤ x) (hq : q' + 1 ≤ q) :
    18 * (x - q) + 29 ≤ 18 * (x - q') + 12 := by omega

/-- Stop-step budget at `q ≥ 1`: `+23` absorbed into the full-rank bound. -/
theorem budget_bstop {x q : ℕ} (hle : q ≤ x) (hq : 1 ≤ q) :
    18 * (x - q) + 23 ≤ 18 * x + 15 := by omega

-- Budget arithmetic on plain variables (avoids rkD-term atomization in omega goals).
theorem budget_init {x : ℕ} : 2 ≤ 2 + 18 * (x - x) + 12 := by omega

theorem budget_stop {x q : ℕ} : 18 * (x - q) + 15 ≤ 18 * x + 15 := by omega

theorem budget_exit {x : ℕ} : 2 + 18 * x + 15 + 1 ≤ 18 * x + 18 := by omega

/-- One `siftDown` run: from a sift-down state with the hole at `0`, the loop restores `Inv`.
Cost: at most `18 * rkD h 0 + 18` — ≤ 17 per descent step (incl. its tests), stop tail,
the two entry writes, and the final test. -/
theorem siftDown_runs {holev : Fin G.n} {st : State ℝ≥0} {origHv : ℕ → Fin G.n} {origHd : ℕ → ℝ≥0}
    {x : Fin G.n} {xk : ℝ≥0}
    (hF : F0 G s st) (hAF : AF G st) (hval : HeapV (G := G) st (st.w "h"))
    (K : SiftDownOK holev s st origHv origHd x xk 0)
    (hbound : st.w "h" ≤ G.m + 1) :
    Runs realOps siftDown st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      InvH holev s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      st'.w "v" = st.w "v" ∧ st'.v "dv" = st.v "dv" ∧
      st'.cost ≤ st.cost + 18 * rkD (st.w "h") 0 + 18 ∧
      HeapV (G := G) st' (st'.w "h")) := by
  have hnpos : 0 < G.n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hcap0 : 2 < st.cap := by have := hF.hcap; omega
  refine runs_seq (runs_wset (x := "ii") (a := 0)
      (evalW_lit_of (by show 0 < st.cap; omega)) ?_)
  refine runs_seq (runs_wset (x := "go") (a := 1)
      (evalW_lit_of (by show 1 < st.cap; omega)) ?_)
  set t1 := (((st.setW "ii" 0).charge 1).setW "go" 1).charge 1 with ht1
  have hK1 : SiftDownOK holev s t1 origHv origHd x xk 0 :=
    SiftDownOK.stable K (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) rfl rfl
  have hF1 : F0 G s t1 :=
    F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl
  have hAF1 : AF G t1 := AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl
  refine runs_while_nat (I := SiftDownInv holev st origHv origHd x xk)
      (Q := fun st' => F0 G s st' ∧ AF G st' ∧
        InvH holev s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v)
          (fun v => st'.wa "done" v) (hvD s st') (fun i => st'.va "hd" i)
          (st'.w "h") (st'.w "ins") ∧
        st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
        st'.w "v" = st.w "v" ∧ st'.v "dv" = st.v "dv" ∧
        st'.cost ≤ st.cost + 18 * rkD (st.w "h") 0 + 18 ∧
        HeapV (G := G) st' (st'.w "h"))
      ?_ (rkD (st.w "h") 0 + 1) t1
      ⟨0, hK1, hF1, hAF1, rfl, rfl, Or.inl ⟨rfl, rfl, rfl,
        by rw [show t1.cost = st.cost + 2 from rfl]
           have hsub0 : rkD (st.w "h") 0 - rkD (st.w "h") 0 ≤ rkD (st.w "h") 0 :=
             Nat.sub_le _ _
           omega⟩, rfl, rfl, by intro i hi; exact hval i hi⟩
  · intro m s' ⟨ii', K', hF', hAF', hh', hins', hmode, hvR, hdvR, hvalR⟩
    have hcap' : 2 < s'.cap := by have := hF'.hcap; omega
    have hhdL : s'.vlen "hd" = G.m + 1 := hAF'.hdL
    have hhvL : s'.wlen "hv" = G.m + 1 := hAF'.hvL
    refine ⟨s'.w "go", evalW_var s' "go", fun hgo => ?_, fun hgz => ?_⟩
    swap -- anonymous constructor order is (body, exit); exit block goes first below
    · -- exit: `go` reads 0
      rcases hmode with h1 | h2
      · omega
      · have hedge : ∀ j, j < s'.w "h" → (j = 2 * ii' + 1 ∨ j = 2 * ii' + 2) →
            s'.va "hd" ii' ≤ s'.va "hd" j := h2.2.2.1
        refine ⟨F0.charge hF' 1, AF.charge hAF' 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨K'.soft, HeapOKExceptFrom.toHeapOK K'.ok (fun j hj hjr => hedge j hj hjr)⟩
        · rw [show (s'.charge 1).w "h" = s'.w "h" from rfl, hh']
        · rw [show (s'.charge 1).w "ins" = s'.w "ins" from rfl, hins']
        · rw [show (s'.charge 1).w "v" = s'.w "v" from rfl]; exact hvR
        · rw [show (s'.charge 1).v "dv" = s'.v "dv" from rfl]; exact hdvR
        · rw [show (s'.charge 1).cost = s'.cost + 1 from rfl]
          have hq0 : m = 0 := h2.2.1
          have hc2 : s'.cost ≤ st.cost + 2 + 18 * rkD (st.w "h") 0 + 15 := h2.2.2.2
          omega
        · intro i hi; exact hvalR i hi
    · -- body: only mode 1 reaches it
      rcases hmode with h1 | h2
      · obtain ⟨hgo1, hii1, hm1, hc1⟩ := h1
        set t0 := s'.charge 1 with ht0
        have h0E : evalW t0 (lit 0) = some 0 := evalW_lit_of (by show 0 < s'.cap; omega)
        have h1E : evalW t0 (lit 1) = some 1 := evalW_lit_of (by show 1 < s'.cap; omega)
        have h2E : evalW t0 (lit 2) = some 2 := evalW_lit_of (by show 2 < s'.cap; omega)
        have hii0 : evalW t0 (var "ii") = some ii' := by
          rw [evalW_var]; show some (s'.w "ii") = some ii'; rw [hii1]
        have hh0 : evalW t0 (var "h") = some (s'.w "h") := evalW_var t0 "h"
        have hhl : s'.w "h" ≤ G.m + 1 := by rw [hh']; exact hbound
        have hcapG : G.n + G.m + 2 ≤ s'.cap := hF'.hcap
        have hiilt : ii' + 1 < s'.cap := by
          have := K'.hiir; have := hhl; have := hcapG; omega
        have hh2lt : s'.w "h" / 2 + 1 < s'.cap := by
          have := hhl; have := hcapG; have := hnpos; omega
        have haddii : evalW t0 (add (var "ii") (lit 1)) = some (ii' + 1) :=
          evalW_add_of hii0 h1E (by show ii' + 1 < s'.cap; exact hiilt)
        have hdivh : evalW t0 (div (var "h") (lit 2)) = some (s'.w "h" / 2) :=
          evalW_div_of hh0 h2E (by norm_num)
        have haddh : evalW t0 (add (div (var "h") (lit 2)) (lit 1))
            = some (s'.w "h" / 2 + 1) :=
          evalW_add_of hdivh h1E (by show s'.w "h" / 2 + 1 < s'.cap; exact hh2lt)
        have hcondE : evalW t0
            (lt (add (var "ii") (lit 1)) (add (div (var "h") (lit 2)) (lit 1)))
            = some (if ii' + 1 < s'.w "h" / 2 + 1 then 1 else 0) :=
          evalW_lt_of haddii haddh (by show 1 < s'.cap; have := hcapG; omega)
        by_cases hlt : ii' + 1 < s'.w "h" / 2 + 1
        · -- step runs: siftDownStep = wset cl, wset c, child-pick ite, siftDownTail
          have htail : ∀ (tX : State ℝ≥0) (cx : ℕ),
              SiftDownOK holev s tX origHv origHd x xk ii' → F0 G s tX → AF G tX →
              tX.w "h" = st.w "h" → tX.w "ins" = st.w "ins" → tX.w "ii" = ii' →
              evalW tX (var "c") = some cx →
              cx < s'.w "h" →
              tX.w "go" = 1 →
              cx = 2 * ii' + 1 ∨ cx = 2 * ii' + 2 →
              cx = mchOf origHd (st.w "h") ii' →
              tX.cost ≤ s'.cost + 8 →
              tX.w "v" = st.w "v" → tX.v "dv" = st.v "dv" →
              HeapV (G := G) tX (tX.w "h") →
              Runs realOps siftDownTail tX
                (fun s'' => ∃ m', m' < m ∧ SiftDownInv (s := s) holev st origHv origHd x xk m' s'') := by
            intro tX cx hKX hFX hAFX hhX hinsX hiiX hcX hcxlt hgoX hcx0 hcm hcostX hvX hdvX hvalX
            have h1lt : 1 < tX.cap := by have := hFX.hcap; have := hnpos; omega
            have hcxltT : cx < tX.w "h" := by rw [hhX, ← hh']; exact hcxlt
            have hcxorig : tX.va "hd" cx = origHd cx :=
              (hKX.child_orig hcxltT hcx0).2
            have hmin : ∀ j, j < tX.w "h" → (j = 2 * ii' + 1 ∨ j = 2 * ii' + 2) →
                tX.va "hd" cx ≤ tX.va "hd" j := by
              intro j hj hjr
              have hj' : j < st.w "h" := by rw [← hhX]; exact hj
              have ho := hKX.child_orig hj hjr
              rw [hcxorig, ho.2]
              exact mchOf_min origHd hcm hj' hjr
            have hiiE : evalW tX (var "ii") = some ii' := by
              rw [evalW_var]; exact congrArg some hiiX
            have havC : evalV realOps tX (VExpr.load "hd" (var "c")) = some (tX.va "hd" cx) :=
              evalV_load_of hcX (by show _ < tX.vlen "hd"; rw [hAFX.hdL]; omega)
            have havI : evalV realOps tX (VExpr.load "hd" (var "ii")) = some (tX.va "hd" ii') :=
              evalV_load_of hiiE (by show _ < tX.vlen "hd"; rw [hAFX.hdL]; have := hKX.hiir; rw [hhX] at this; omega)
            refine runs_seq (runs_vle (x := "b") havC havI (by omega) ?_)
            set tY := (tX.setW "b" (if realOps.le (tX.va "hd" cx) (tX.va "hd" ii')
              then 1 else 0)).charge 1 with htY
            have hbval : tY.w "b" = if tX.va "hd" cx ≤ xk then 1 else 0 := by
              show (if realOps.le (tX.va "hd" cx) (tX.va "hd" ii') then 1 else 0) = _
              rw [bit_le]
              show (if tX.va "hd" cx ≤ tX.va "hd" ii' then 1 else 0) = _
              rw [hKX.hole.2]
            have hbE : evalW tY (var "b") = some (tY.w "b") := evalW_var tY "b"
            by_cases hsw : tX.va "hd" cx ≤ xk
            · -- swap branch: hole descends to cx
              have hb1 : tY.w "b" = 1 := by rw [hbval, if_pos hsw]
              refine runs_ite_true hbE (by rw [hb1]; norm_num) ?_
              set t2 := tY.charge 1 with ht2
              have hii2 : evalW t2 (var "ii") = some ii' := by
                rw [evalW_var]; show some (tX.w "ii") = some ii'; rw [hiiX]
              have hcx2 : evalW t2 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                rw [show tX.w "c" = tX.w "c" from rfl]
                have := hcX; rw [evalW_var] at this; exact this
              have hvl2 : ii' < t2.vlen "hd" := by
                show _ < tX.vlen "hd"; rw [hAFX.hdL]; have := hKX.hiir; rw [hhX] at this; omega
              have hvl2b : cx < t2.vlen "hd" := by show _ < tX.vlen "hd"; rw [hAFX.hdL]; omega
              have hav2i : evalV realOps t2 (VExpr.load "hd" (var "ii")) = some (t2.va "hd" ii') :=
                evalV_load_of hii2 hvl2
              have hav2c : evalV realOps t2 (VExpr.load "hd" (var "c")) = some (t2.va "hd" cx) :=
                evalV_load_of hcx2 hvl2b
              refine runs_seq (runs_vset (x := "tv") hav2i ?_)
              set t3 := (t2.setV "tv" (t2.va "hd" ii')).charge 1 with ht3
              have hii3 : evalW t3 (var "ii") = some ii' := by
                rw [evalW_var]; show some (tX.w "ii") = some ii'; rw [hiiX]
              have hcx3 : evalW t3 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                have := hcX; rw [evalW_var] at this; exact this
              have hvl3 : ii' < t3.vlen "hd" := by
                show _ < tX.vlen "hd"; rw [hAFX.hdL]; have := hKX.hiir; rw [hhX] at this; omega
              have hvl3b : cx < t3.vlen "hd" := by show _ < tX.vlen "hd"; rw [hAFX.hdL]; omega
              have hav3i : evalV realOps t3 (VExpr.load "hd" (var "ii")) = some (t3.va "hd" ii') :=
                evalV_load_of hii3 hvl3
              have hav3c : evalV realOps t3 (VExpr.load "hd" (var "c")) = some (t3.va "hd" cx) :=
                evalV_load_of hcx3 hvl3b
              refine runs_seq (runs_vstore (arr := "hd") hii3 hav3c hvl3 ?_)
              set t4 := (t3.storeV "hd" ii' (t3.va "hd" cx)).charge 1 with ht4
              have hcx4 : evalW t4 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                have := hcX; rw [evalW_var] at this; exact this
              have hvl4b : cx < t4.vlen "hd" := by show _ < tX.vlen "hd"; rw [hAFX.hdL]; omega
              have htv4 : evalV realOps t4 (VExpr.var "tv") = some (tX.va "hd" ii') := rfl
              refine runs_seq (runs_vstore (arr := "hd") hcx4 htv4 hvl4b ?_)
              set t5 := (t4.storeV "hd" cx (tX.va "hd" ii')).charge 1 with ht5
              have hii5 : evalW t5 (var "ii") = some ii' := by
                rw [evalW_var]; show some (tX.w "ii") = some ii'; rw [hiiX]
              have hcx5 : evalW t5 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                have := hcX; rw [evalW_var] at this; exact this
              have hwl5 : ii' < t5.wlen "hv" := by
                show _ < tX.wlen "hv"; rw [hAFX.hvL]; have := hKX.hiir; rw [hhX] at this; omega
              have hwl5b : cx < t5.wlen "hv" := by show _ < tX.wlen "hv"; rw [hAFX.hvL]; omega
              have hiv5 : evalW t5 (load "hv" (var "ii")) = some (tX.wa "hv" ii') :=
                evalW_load_of hii5 hwl5
              have hcxv5 : evalW t5 (load "hv" (var "c")) = some (tX.wa "hv" cx) :=
                evalW_load_of hcx5 hwl5b
              refine runs_seq (runs_wset (x := "tw") hiv5 ?_)
              set t6 := (t5.setW "tw" (tX.wa "hv" ii')).charge 1 with ht6
              have hii6 : evalW t6 (var "ii") = some ii' := by
                rw [evalW_var]; show some (tX.w "ii") = some ii'; rw [hiiX]
              have hcx6 : evalW t6 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                have := hcX; rw [evalW_var] at this; exact this
              have htw6 : evalW t6 (var "tw") = some (tX.wa "hv" ii') := by rw [evalW_var]; rfl
              have hwl6 : ii' < t6.wlen "hv" := by
                show _ < tX.wlen "hv"; rw [hAFX.hvL]; have := hKX.hiir; rw [hhX] at this; omega
              have hwl6b : cx < t6.wlen "hv" := by show _ < tX.wlen "hv"; rw [hAFX.hvL]; omega
              have hiv6 : evalW t6 (load "hv" (var "ii")) = some (tX.wa "hv" ii') :=
                evalW_load_of hii6 hwl6
              have hcxv6 : evalW t6 (load "hv" (var "c")) = some (tX.wa "hv" cx) :=
                evalW_load_of hcx6 hwl6b
              refine runs_seq (runs_wstore (arr := "hv") hii6 hcxv6 hwl6 ?_)
              set t7 := (t6.storeW "hv" ii' (tX.wa "hv" cx)).charge 1 with ht7
              have hcx7 : evalW t7 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                have := hcX; rw [evalW_var] at this; exact this
              have htw7 : evalW t7 (var "tw") = some (tX.wa "hv" ii') := by rw [evalW_var]; rfl
              have hwl7b : cx < t7.wlen "hv" := by show _ < tX.wlen "hv"; rw [hAFX.hvL]; omega
              refine runs_seq (runs_wstore (arr := "hv") hcx7 htw7 hwl7b ?_)
              set t8 := (t7.storeW "hv" cx (tX.wa "hv" ii')).charge 1 with ht8
              have hcx8 : evalW t8 (var "c") = some cx := by
                rw [evalW_var]; show some (tX.w "c") = some cx
                have := hcX; rw [evalW_var] at this; exact this
              refine runs_wset (x := "ii") hcx8 ?_
              set t9 := (t8.setW "ii" cx).charge 1 with ht9
              -- transposition facts for the swap lemma (partner cx, hole ii')
              have e3 : ∀ i, t3.va "hd" i = tX.va "hd" i := fun i => rfl
              have e1 : ∀ i, t4.va "hd" i = if i = ii' then t3.va "hd" cx
                  else t3.va "hd" i := by
                intro j
                rw [ht4, va_charge, va_storeV]; simp
              have e2 : ∀ i, t5.va "hd" i = if i = cx then tX.va "hd" ii'
                  else t4.va "hd" i := by
                intro j
                rw [ht5, va_charge, va_storeV]; simp
              have hhd : ∀ i, t9.va "hd" i = if i = cx then tX.va "hd" ii'
                  else if i = ii' then tX.va "hd" cx else tX.va "hd" i := by
                intro i
                have e0 : t9.va "hd" i = t5.va "hd" i := rfl
                have hx : t3.va "hd" cx = tX.va "hd" cx := rfl
                rw [e0, e2, e1, hx]
                split_ifs
                · rfl
                · rfl
                · exact e3 i
              have hneIC : ii' ≠ cx := by rcases hcx0 with h | h <;> omega
              have heqd : ∀ i, t9.va "hd" i = if i = ii' then tX.va "hd" cx
                  else if i = cx then tX.va "hd" ii' else tX.va "hd" i := by
                intro i
                rw [hhd]
                by_cases hi : i = ii'
                · rw [hi]; simp [hneIC]
                · by_cases hj : i = cx
                  · rw [hj]; simp [Ne.symm hneIC]
                  · simp [hi, hj]
              have w1 : ∀ i, t7.wa "hv" i = if i = ii' then tX.wa "hv" cx
                  else tX.wa "hv" i := by
                intro j
                rw [ht7, wa_charge, wa_storeW]; simp
                split_ifs <;> rfl
              have w2 : ∀ i, t8.wa "hv" i = if i = cx then tX.wa "hv" ii'
                  else t7.wa "hv" i := by
                intro j
                rw [ht8, wa_charge, wa_storeW]; simp
              have hwaE : ∀ i, t9.wa "hv" i = if i = cx then tX.wa "hv" ii'
                  else if i = ii' then tX.wa "hv" cx else tX.wa "hv" i := by
                intro i
                have w0 : t9.wa "hv" i = t8.wa "hv" i := rfl
                rw [w0, w2, w1]
              have heqv : ∀ i, hvD s t9 i = if i = ii' then hvD s tX cx
                  else if i = cx then hvD s tX ii' else hvD s tX i := by
                intro i
                by_cases hi : i = ii'
                · rw [hi]
                  have hw : t9.wa "hv" ii' = tX.wa "hv" cx := by
                    rw [hwaE, if_neg hneIC, if_pos rfl]
                  have key := hvD_eq_of_wa (s := s) hw
                  simp [key]
                · by_cases hj : i = cx
                  · rw [hj]
                    have hw : t9.wa "hv" cx = tX.wa "hv" ii' := by
                      rw [hwaE, if_pos rfl]
                    have key := hvD_eq_of_wa (s := s) hw
                    simp [key, Ne.symm hneIC]
                  · have hw : t9.wa "hv" i = tX.wa "hv" i := by
                      rw [hwaE, if_neg hj, if_neg hi]
                    have key := hvD_eq_of_wa (s := s) hw
                    simp [key, hi, hj]
              have hlt2 : 2 * ii' + 1 < st.w "h" := by
                rw [← hh']; omega
              have hdrop : rkD (st.w "h") cx + 1 ≤ rkD (st.w "h") ii' :=
                rkD_succ_of_child hcx0 hlt2
              have hK9 : SiftDownOK holev s t9 origHv origHd x xk cx :=
                SiftDownOK.swap hKX (by rw [hhX]; exact hcm) hcxltT hsw hmin
                  (rfl) (rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) heqv heqd
              have hF9 : F0 G s t9 :=
                F0.preserve hFX rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                  (fun _ _ => rfl) rfl rfl rfl
              have hAF9 : AF G t9 := AF.preserve hAFX rfl rfl rfl rfl rfl rfl rfl
              have hc9 : t9.cost = tX.cost + 9 := rfl
              refine ⟨rkD (st.w "h") cx + 1, ?_, cx, hK9, hF9, hAF9,
                by rw [show t9.w "h" = tX.w "h" from rfl, hhX],
                by rw [show t9.w "ins" = tX.w "ins" from rfl, hinsX],
                Or.inl ⟨by rw [show t9.w "go" = tX.w "go" from rfl, hgoX], rfl, rfl, ?_⟩,
                by rw [show t9.w "v" = tX.w "v" from rfl]; exact hvX,
                by rw [show t9.v "dv" = tX.v "dv" from rfl]; exact hdvX,
                by
                  intro i hi
                  rw [hwaE i]
                  split_ifs
                  · exact hvalX ii' hKX.hiir
                  · exact hvalX cx hcxltT
                  · exact hvalX i (by rw [show t9.w "h" = tX.w "h" from rfl] at hi; exact hi)⟩
              · omega
              · rw [hc9]
                have hbs := budget_swap (x := rkD (st.w "h") 0) (q := rkD (st.w "h") ii')
                  (q' := rkD (st.w "h") cx) (rkD_le_zero) hdrop
                have h1 : s'.cost ≤ st.cost + 2 + 18 * (rkD (st.w "h") 0 - rkD (st.w "h") ii') + 12
                  := hc1
                omega
            · -- stop branch: `go := 0`, hole stays at ii', hedge xk < hd c ≤ children
              have hb0 : tY.w "b" = 0 := by rw [hbval, if_neg hsw]
              refine runs_ite_false (by rw [hbE, hb0]) ?_
              refine runs_wset (x := "go") (a := 0)
                  (evalW_lit_of (by show 0 < tX.cap; have := h1lt; omega)) ?_
              set tS2 := ((tY.charge 1).setW "go" 0).charge 1 with htS2
              have hKS2 : SiftDownOK holev s tS2 origHv origHd x xk ii' :=
                SiftDownOK.stable hKX (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) rfl rfl
              have hFS2 : F0 G s tS2 :=
                F0.preserve hFX rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                  (fun _ _ => rfl) rfl rfl rfl
              have hAFS2 : AF G tS2 := AF.preserve hAFX rfl rfl rfl rfl rfl rfl rfl
              have hcS2 : tS2.cost = tX.cost + 3 := rfl
              refine ⟨0, by omega, ii', hKS2, hFS2, hAFS2,
                by rw [show tS2.w "h" = tX.w "h" from rfl, hhX],
                by rw [show tS2.w "ins" = tX.w "ins" from rfl, hinsX],
                Or.inr ⟨rfl, rfl, ?_, ?_⟩,
                by rw [show tS2.w "v" = tX.w "v" from rfl]; exact hvX,
                by rw [show tS2.v "dv" = tX.v "dv" from rfl]; exact hdvX,
                by intro i hi; exact hvalX i hi⟩
              · intro j hj hjr
                have hjh : j < s'.w "h" := by
                  rw [show tS2.w "h" = tX.w "h" from rfl, hhX, ← hh'] at hj; exact hj
                have hlt2 : 2 * ii' + 1 < st.w "h" := by rw [← hh']; omega
                have hle2 : tX.va "hd" cx ≤ tX.va "hd" j := hmin j (by
                  rw [hhX, ← hh']; exact hjh) hjr
                have hgt : xk < tX.va "hd" cx := lt_of_not_ge hsw
                show tS2.va "hd" ii' ≤ tS2.va "hd" j
                rw [show tS2.va "hd" ii' = tX.va "hd" ii' from rfl, hKX.hole.2]
                exact le_trans hgt.le hle2
              · rw [hcS2]
                have h1 : s'.cost ≤ st.cost + 2 + 18 * (rkD (st.w "h") 0 - rkD (st.w "h") ii') + 12
                  := hc1
                have hdrop0 : rkD (st.w "h") cx + 1 ≤ rkD (st.w "h") ii' :=
                  rkD_succ_of_child hcx0 (by rw [← hh']; omega)
                have hq : 1 ≤ rkD (st.w "h") ii' :=
                  rkD_pos_of_child (by rw [← hh']; omega)
                have hbs := budget_bstop (x := rkD (st.w "h") 0) (q := rkD (st.w "h") ii')
                  (rkD_le_zero) hq
                omega
          refine runs_ite_true hcondE (by rw [if_pos hlt]; norm_num) ?_
          have hlt2 : 2 * ii' + 1 < s'.w "h" := by
            have h1' : ii' < s'.w "h" / 2 := by omega
            have hmod := Nat.div_add_mod (s'.w "h") 2
            have hm2 : s'.w "h" % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          have hcap2 : 2 * ii' + 2 < s'.cap := by have := hcapG; have := hlt2; have := hhl; omega
          -- 1. cl := 2*ii'+1
          have hclE : evalW (t0.charge 1) (add (add (var "ii") (var "ii")) (lit 1))
              = some (2 * ii' + 1) := by
            rw [evalW_charge]
            have ha : evalW t0 (add (var "ii") (var "ii")) = some (ii' + ii') :=
              evalW_add_of hii0 hii0 (by show ii' + ii' < s'.cap; omega)
            have hb : evalW t0 (add (add (var "ii") (var "ii")) (lit 1))
                = some (ii' + ii' + 1) :=
              evalW_add_of ha h1E (by show ii' + ii' + 1 < s'.cap; omega)
            rw [hb]
            exact congrArg some (by omega)
          refine runs_seq (runs_wset hclE ?_)
          set d1 := ((t0.charge 1).setW "cl" (2 * ii' + 1)).charge 1 with hd1
          have hcl1 : evalW d1 (var "cl") = some (2 * ii' + 1) := by rw [evalW_var]; rfl
          -- 2. c := cl
          refine runs_seq (runs_wset hcl1 ?_)
          set d2 := (d1.setW "c" (2 * ii' + 1)).charge 1 with hd2
          have hcl2 : evalW d2 (var "cl") = some (2 * ii' + 1) := by rw [evalW_var]; rfl
          have h1d2 : evalW d2 (lit 1) = some 1 := evalW_lit_of (by show 1 < s'.cap; omega)
          have hcl1E : evalW d2 (add (var "cl") (lit 1)) = some (2 * ii' + 2) :=
            evalW_add_of (x := 2 * ii' + 1) (y := 1) hcl2 h1d2
              (by show 2 * ii' + 2 < s'.cap; omega)
          have hhd2 : evalW d2 (var "h") = some (s'.w "h") := by rw [evalW_var]; rfl
          have hcond2 : evalW d2 (lt (add (var "cl") (lit 1)) (var "h"))
              = some (if 2 * ii' + 2 < s'.w "h" then 1 else 0) :=
            evalW_lt_of hcl1E hhd2 (by show 1 < s'.cap; omega)
          -- 3. child pick
          by_cases hright : 2 * ii' + 2 < s'.w "h"
          · refine runs_seq (runs_ite_true hcond2 (by rw [if_pos hright]; norm_num) ?_)
            set d3 := d2.charge 1 with hd3
            have hcl3 : evalW d3 (var "cl") = some (2 * ii' + 1) := by rw [evalW_var]; rfl
            have h1d3 : evalW d3 (lit 1) = some 1 := evalW_lit_of (by show 1 < s'.cap; omega)
            have hcl13 : evalW d3 (add (var "cl") (lit 1)) = some (2 * ii' + 2) :=
              evalW_add_of (x := 2 * ii' + 1) (y := 1) hcl3 h1d3
                (by show 2 * ii' + 2 < s'.cap; omega)
            have hvl3a : 2 * ii' + 2 < d3.vlen "hd" := by
              have hL : d3.vlen "hd" = G.m + 1 := hhdL; rw [hL]; omega
            have hvl3b : 2 * ii' + 1 < d3.vlen "hd" := by
              have hL : d3.vlen "hd" = G.m + 1 := hhdL; rw [hL]; omega
            have hav3 : evalV realOps d3 (VExpr.load "hd" (add (var "cl") (lit 1)))
                = some (d3.va "hd" (2 * ii' + 2)) := evalV_load_of hcl13 hvl3a
            have hav3' : evalV realOps d3 (VExpr.load "hd" (var "cl"))
                = some (d3.va "hd" (2 * ii' + 1)) := evalV_load_of hcl3 hvl3b
            refine runs_seq (runs_vle (x := "b") hav3 hav3'
                (by show 1 < s'.cap; omega) ?_)
            set d4 := (d3.setW "b" (if realOps.le (d3.va "hd" (2 * ii' + 2))
                (d3.va "hd" (2 * ii' + 1)) then 1 else 0)).charge 1 with hd4
            have hco2 : s'.va "hd" (2 * ii' + 2) = origHd (2 * ii' + 2) :=
              (K'.child_orig hright (Or.inr rfl)).2
            have hco1 : s'.va "hd" (2 * ii' + 1) = origHd (2 * ii' + 1) :=
              (K'.child_orig hlt2 (Or.inl rfl)).2
            have hbval : d4.w "b" = if s'.va "hd" (2 * ii' + 2) ≤ s'.va "hd" (2 * ii' + 1)
                then 1 else 0 := by
              show (if realOps.le (d3.va "hd" (2 * ii' + 2)) (d3.va "hd" (2 * ii' + 1))
                then 1 else 0) = _
              rw [bit_le]
              show (if d3.va "hd" (2 * ii' + 2) ≤ d3.va "hd" (2 * ii' + 1) then 1 else 0) = _
              rw [show d3.va "hd" (2 * ii' + 2) = s'.va "hd" (2 * ii' + 2) from rfl,
                show d3.va "hd" (2 * ii' + 1) = s'.va "hd" (2 * ii' + 1) from rfl]
            have hbE : evalW d4 (var "b") = some (d4.w "b") := evalW_var d4 "b"
            have hright' : 2 * ii' + 2 < st.w "h" := by rw [← hh']; exact hright
            by_cases hbb : s'.va "hd" (2 * ii' + 2) ≤ s'.va "hd" (2 * ii' + 1)
            · -- b = 1: c := 2*ii'+2
              have hb1 : d4.w "b" = 1 := by rw [hbval, if_pos hbb]
              refine runs_ite_true hbE (by rw [hb1]; norm_num) ?_
              have hcl4 : evalW (d4.charge 1) (add (var "cl") (lit 1))
                  = some (2 * ii' + 2) := by
                rw [evalW_charge]
                exact evalW_add_of (x := 2 * ii' + 1) (y := 1)
                    (by rw [evalW_var]; rfl)
                    (evalW_lit_of (by show 1 < s'.cap; omega))
                    (by show 2 * ii' + 2 < s'.cap; omega)
              refine runs_wset (x := "c") hcl4 ?_
              set d5 := ((d4.charge 1).setW "c" (2 * ii' + 2)).charge 1 with hd5
              have hcm5 : (2:ℕ) * ii' + 2 = mchOf origHd (st.w "h") ii' := by
                have hrightS : 2 * ii' + 2 < st.w "h" := by rw [← hh']; exact hright
                have hbbO : origHd (2 * ii' + 2) ≤ origHd (2 * ii' + 1) := by
                  rw [← hco2, ← hco1]; exact hbb
                simp only [mchOf]
                rw [if_pos hrightS, if_pos hbbO]
              exact htail d5 (2 * ii' + 2)
                (SiftDownOK.stable K' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) rfl rfl)
                (F0.preserve hF' rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                  (fun _ _ => rfl) rfl rfl rfl)
                (AF.preserve hAF' rfl rfl rfl rfl rfl rfl rfl)
                (by rw [show d5.w "h" = s'.w "h" from rfl, hh'])
                (by rw [show d5.w "ins" = s'.w "ins" from rfl, hins'])
                (by rw [show d5.w "ii" = s'.w "ii" from rfl, hii1])
                (by rw [evalW_var]; rfl)
                hright
                (by rw [show d5.w "go" = s'.w "go" from rfl, hgo1])
                (Or.inr rfl)
                hcm5
                (by show s'.cost + 8 ≤ s'.cost + 8; omega)
                (by rw [show d5.w "v" = s'.w "v" from rfl]; exact hvR)
                (by rw [show d5.v "dv" = s'.v "dv" from rfl]; exact hdvR)
                (by intro i hi; exact hvalR i hi)
            · -- b = 0: skip, c stays 2*ii'+1
              have hb0 : d4.w "b" = 0 := by rw [hbval, if_neg hbb]
              refine runs_ite_false (by rw [hbE, hb0]) ?_
              refine runs_skip ?_
              set d5 := ((d4.charge 1).charge 1) with hd5
              have hcm5 : (2:ℕ) * ii' + 1 = mchOf origHd (st.w "h") ii' := by
                have hrightS : 2 * ii' + 2 < st.w "h" := by rw [← hh']; exact hright
                have hbbN : ¬(origHd (2 * ii' + 2) ≤ origHd (2 * ii' + 1)) := by
                  rw [← hco2, ← hco1]; exact hbb
                simp only [mchOf]
                rw [if_pos hrightS, if_neg hbbN]
              exact htail d5 (2 * ii' + 1)
                (SiftDownOK.stable K' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                  (fun _ => rfl) (fun _ => rfl) rfl rfl)
                (F0.preserve hF' rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                  (fun _ _ => rfl) rfl rfl rfl)
                (AF.preserve hAF' rfl rfl rfl rfl rfl rfl rfl)
                (by rw [show d5.w "h" = s'.w "h" from rfl, hh'])
                (by rw [show d5.w "ins" = s'.w "ins" from rfl, hins'])
                (by rw [show d5.w "ii" = s'.w "ii" from rfl, hii1])
                (by rw [evalW_var]; rfl)
                hlt2
                (by rw [show d5.w "go" = s'.w "go" from rfl, hgo1])
                (Or.inl rfl)
                hcm5
                (by show s'.cost + 8 ≤ s'.cost + 8; omega)
                (by rw [show d5.w "v" = s'.w "v" from rfl]; exact hvR)
                (by rw [show d5.v "dv" = s'.v "dv" from rfl]; exact hdvR)
                (by intro i hi; exact hvalR i hi)
          · -- no right child: skip the pick, c = 2*ii'+1
            refine runs_seq (runs_ite_false (by rw [hcond2, if_neg hright]) ?_)
            refine runs_skip ?_
            set d3 := ((d2.charge 1).charge 1) with hd3
            have hcm3 : (2:ℕ) * ii' + 1 = mchOf origHd (st.w "h") ii' := by
              have hrightN : ¬(2 * ii' + 2 < st.w "h") := by rw [← hh']; exact hright
              simp only [mchOf]
              rw [if_neg hrightN]
            exact htail d3 (2 * ii' + 1)
              (SiftDownOK.stable K' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                (fun _ => rfl) (fun _ => rfl) rfl rfl)
              (F0.preserve hF' rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
                (fun _ _ => rfl) rfl rfl rfl)
              (AF.preserve hAF' rfl rfl rfl rfl rfl rfl rfl)
              (by rw [show d3.w "h" = s'.w "h" from rfl, hh'])
              (by rw [show d3.w "ins" = s'.w "ins" from rfl, hins'])
              (by rw [show d3.w "ii" = s'.w "ii" from rfl, hii1])
              (by rw [evalW_var]; rfl)
              hlt2
              (by rw [show d3.w "go" = s'.w "go" from rfl, hgo1])
              (Or.inl rfl)
              hcm3
              (by show s'.cost + 6 ≤ s'.cost + 8; omega)
              (by rw [show d3.w "v" = s'.w "v" from rfl]; exact hvR)
              (by rw [show d3.v "dv" = s'.v "dv" from rfl]; exact hdvR)
              (by intro i hi; exact hvalR i hi)
        · have hge : s'.w "h" ≤ 2 * ii' + 1 := by
            have h1' : s'.w "h" / 2 ≤ ii' := by omega
            have hmod := Nat.div_add_mod (s'.w "h") 2
            have hm2 : s'.w "h" % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          refine runs_ite_false (by rw [hcondE, if_neg hlt]) ?_
          refine runs_wset (x := "go") (a := 0) h0E ?_
          set tS := ((t0.charge 1).setW "go" 0).charge 1 with htS
          have hKS : SiftDownOK holev s tS origHv origHd x xk ii' :=
            SiftDownOK.stable K' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              (fun _ => rfl) (fun _ => rfl) rfl rfl
          have hFS : F0 G s tS :=
            F0.preserve hF' rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
              (fun _ _ => rfl) rfl rfl rfl
          have hAFS : AF G tS := AF.preserve hAF' rfl rfl rfl rfl rfl rfl rfl
          have hcS : tS.cost = s'.cost + 3 := rfl
          refine ⟨0, by omega, ii', hKS, hFS, hAFS,
            by rw [show tS.w "h" = s'.w "h" from rfl, hh'],
            by rw [show tS.w "ins" = s'.w "ins" from rfl, hins'],
            Or.inr ⟨rfl, rfl, ?_, ?_⟩,
            by rw [show tS.w "v" = s'.w "v" from rfl]; exact hvR,
            by rw [show tS.v "dv" = s'.v "dv" from rfl]; exact hdvR,
            by intro i hi; exact hvalR i hi⟩
          · intro j hj hjr
            have hjh : j < s'.w "h" := by
              rw [show tS.w "h" = s'.w "h" from rfl] at hj; exact hj
            rcases hjr with hr | hr <;> omega
          · rw [hcS]
            have hsub : rkD (st.w "h") 0 - rkD (st.w "h") ii' ≤ rkD (st.w "h") 0 :=
              Nat.sub_le _ _
            omega
      · exact absurd h2.1 hgo

/-- One `popBody`: pop the min entry into `v`/`dv`, shrink the heap, move the last
entry to the root and sift the hole down.  Post: `InvH` with the entry-cur hole at
the popped vertex (filled by `settleBody`, or vacuous on the stale skip), the popped
registers, heap-entry validity, and cost `≤ 18 * rkD h 0 + 25`. -/
theorem popBody_runs {st : State ℝ≥0}
    (hF : F0 G s st) (hAF : AF G st)
    (hInv : Inv G s (fun v => st.va "dist" v) (fun v => st.wa "reach" v) (fun v => st.wa "done" v)
      (hvD s st) (fun i => st.va "hd" i) (st.w "h") (st.w "ins"))
    (hval : HeapV (G := G) st (st.w "h"))
    (hpos : 0 < st.w "h") (hbound : st.w "h" ≤ G.m + 1) :
    Runs realOps popBody st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      InvH (hvD s st 0) s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v)
        (fun v => st'.wa "done" v) (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = st.w "h" - 1 ∧ st'.w "ins" = st.w "ins" ∧
      st'.w "v" = st.wa "hv" 0 ∧ st'.v "dv" = st.va "hd" 0 ∧
      st'.w "v" < G.n ∧ HeapV (G := G) st' (st'.w "h") ∧
      st'.cost ≤ st.cost + 18 * rkD (st.w "h") 0 + 25) := by
  have hnpos : 0 < G.n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hcap : 2 < st.cap := by have := hF.hcap; omega
  have hhdL : st.vlen "hd" = G.m + 1 := hAF.hdL
  have hhvL : st.wlen "hv" = G.m + 1 := hAF.hvL
  have hv0lt : st.wa "hv" 0 < G.n := hval 0 hpos
  have hhE0 : evalW st (load "hv" (lit 0)) = some (st.wa "hv" 0) :=
    evalW_load_of (evalW_lit_of (by show 0 < st.cap; omega))
      (by show 0 < st.wlen "hv"; rw [hhvL]; omega)
  refine runs_seq (runs_wset (x := "v") hhE0 ?_)
  set t1 := (st.setW "v" (st.wa "hv" 0)).charge 1 with ht1
  have hdvE : evalV realOps t1 (VExpr.load "hd" (lit 0)) = some (t1.va "hd" 0) :=
    evalV_load_of (evalW_lit_of (by show 0 < st.cap; omega))
      (by show 0 < st.vlen "hd"; rw [hhdL]; omega)
  refine runs_seq (runs_vset (x := "dv") hdvE ?_)
  set t2 := (t1.setV "dv" (st.va "hd" 0)).charge 1 with ht2
  have hsubE : evalW t2 (sub (var "h") (lit 1)) = some (st.w "h" - 1) :=
    evalW_sub_of (evalW_var t2 "h") (evalW_lit_of (by show 1 < st.cap; omega))
  refine runs_seq (runs_wset (x := "h") hsubE ?_)
  set t3 := (t2.setW "h" (st.w "h" - 1)).charge 1 with ht3
  have hltE : evalW t3 (lt (lit 0) (var "h")) = some (if 0 < st.w "h" - 1 then 1 else 0) :=
    evalW_lt_of (evalW_lit_of (by show 0 < st.cap; omega)) (evalW_var t3 "h")
      (by show 1 < st.cap; omega)
  -- moved-pair facts (indices in the pre-move arrays)
  have hmoved : ∀ i, i < st.w "h" - 1 ∨ i = st.w "h" - 1 → i < st.w "h" := by
    intro i hi; omega
  by_cases hsmall : st.w "h" = 1
  · -- skip: the pop emptied the heap
    have hlt0 : evalW t3 (lt (lit 0) (var "h")) = some 0 := by
      rw [hltE, hsmall]; simp
    refine runs_ite_false hlt0 ?_
    refine runs_skip ?_
    set tS := ((t3.charge 1).charge 1) with htS
    have hFS : F0 G s tS :=
      F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl
    have hAFS : AF G tS := AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl
    have hzz : tS.w "h" = 0 := by rw [show tS.w "h" = st.w "h" - 1 from rfl, hsmall]
    have hKS : InvH (hvD s st 0) s (fun v => tS.va "dist" v) (fun v => tS.wa "reach" v)
        (fun v => tS.wa "done" v) (hvD s tS) (fun i => tS.va "hd" i) (tS.w "h") (tS.w "ins") := by
      have hdd : (fun v => tS.va "dist" v) = (fun v => st.va "dist" v) := funext (fun _ => rfl)
      have hrr : (fun v => tS.wa "reach" v) = (fun v => st.wa "reach" v) := funext (fun _ => rfl)
      have hdn : (fun v => tS.wa "done" v) = (fun v => st.wa "done" v) := funext (fun _ => rfl)
      have hvv : hvD s tS = hvD s st := funext (fun i => hvD_eq_of_wa (s := s) rfl)
      have hhh : (fun i => tS.va "hd" i) = (fun i => st.va "hd" i) := funext (fun _ => rfl)
      refine ⟨⟨hInv.ghost, hInv.relax_hold, ?_, ?_, ?_, hInv.source0, hInv.done_reach⟩, ?_⟩
      · intro v hvne hr hd0
        obtain ⟨i, hi, hvi, _⟩ := hInv.entry_cur v hr hd0
        have hi0 : i = 0 := by rw [hsmall] at hi; omega
        subst hi0; exact absurd hvi.symm hvne
      · intro i hi; rw [hzz] at hi; exact absurd hi (by omega)
      · intro i hi; rw [hzz] at hi; exact absurd hi (by omega)
      · intro i hi j hj hjr; rw [hzz] at hi; exact absurd hi (by omega)
    have hVS : HeapV (G := G) tS (tS.w "h") := by
      intro i hi; rw [hzz] at hi; exact absurd hi (by omega)
    refine ⟨hFS, hAFS, hKS, rfl, rfl, rfl, rfl, hv0lt, hVS, ?_⟩
    · show tS.cost ≤ st.cost + 18 * rkD (st.w "h") 0 + 25
      have hc5 : tS.cost = st.cost + 5 := rfl
      omega
  · -- move branch: the last entry goes to the root
    have hge2 : 2 ≤ st.w "h" := by omega
    have hlt0 : evalW t3 (lt (lit 0) (var "h")) = some (if 0 < st.w "h" - 1 then 1 else 0) :=
      hltE
    refine runs_ite_true hlt0 (by rw [if_pos (by omega)]; norm_num) ?_
    set b0 := t3.charge 1 with hb0
    have hcl0 : evalW b0 (lit 0) = some 0 := evalW_lit_of (by show 0 < st.cap; omega)
    have hhhE : evalW b0 (var "h") = some (st.w "h" - 1) := by rw [evalW_var]; rfl
    have hldhv : evalW b0 (load "hv" (var "h")) = some (b0.wa "hv" (st.w "h" - 1)) :=
      evalW_load_of hhhE (by show (st.w "h" - 1) < st.wlen "hv"; rw [hhvL]; omega)
    refine runs_seq (runs_wstore hcl0 hldhv
        (by show 0 < b0.wlen "hv"; rw [show b0.wlen "hv" = st.wlen "hv" from rfl, hhvL]; omega) ?_)
    set b1 := (b0.storeW "hv" 0 (b0.wa "hv" (st.w "h" - 1))).charge 1 with hb1
    have hcl1 : evalW b1 (lit 0) = some 0 := evalW_lit_of (by show 0 < st.cap; omega)
    have hhh1 : evalW b1 (var "h") = some (st.w "h" - 1) := by rw [evalW_var]; rfl
    have hldhd : evalV realOps b1 (VExpr.load "hd" (var "h")) = some (b1.va "hd" (st.w "h" - 1)) :=
      evalV_load_of hhh1 (by show (st.w "h" - 1) < st.vlen "hd"; rw [hhdL]; omega)
    refine runs_seq (runs_vstore (arr := "hd") hcl1 hldhd
        (by show 0 < b1.vlen "hd"; rw [show b1.vlen "hd" = st.vlen "hd" from rfl, hhdL]; omega) ?_)
    set t5 := (b1.storeV "hd" 0 (b1.va "hd" (st.w "h" - 1))).charge 1 with ht5
    have hht : t5.w "h" = st.w "h" - 1 := rfl
    -- moved-pair equations on the post-move arrays
    have ehd : ∀ i, t5.va "hd" i = if i = 0 then st.va "hd" (st.w "h" - 1) else st.va "hd" i := by
      intro i
      have e1 : ∀ j, t5.va "hd" j = if j = 0 then b1.va "hd" (st.w "h" - 1) else b1.va "hd" j := by
        intro j; rw [ht5, va_charge, va_storeV]; simp
      have e2 : ∀ j, b1.va "hd" j = st.va "hd" j := fun _ => rfl
      simp only [e1, e2]
    have ehv : ∀ i, t5.wa "hv" i = if i = 0 then st.wa "hv" (st.w "h" - 1) else st.wa "hv" i := by
      intro i
      have e1 : ∀ j, t5.wa "hv" j = b1.wa "hv" j := fun _ => rfl
      have e2 : ∀ j, b1.wa "hv" j = if j = 0 then b0.wa "hv" (st.w "h" - 1) else b0.wa "hv" j := by
        intro j; rw [hb1, wa_charge, wa_storeW]; simp
      have e3 : ∀ j, b0.wa "hv" j = st.wa "hv" j := fun _ => rfl
      simp only [e1, e2, e3]
    have ehvD : ∀ i, hvD s t5 i = if i = 0 then hvD s st (st.w "h" - 1) else hvD s st i := by
      intro i
      by_cases hi0 : i = 0
      · rw [hi0, if_pos rfl]
        have hw : t5.wa "hv" 0 = st.wa "hv" (st.w "h" - 1) := by rw [ehv]; simp
        exact hvD_eq_of_wa (s := s) hw
      · rw [if_neg hi0]
        have hw : t5.wa "hv" i = st.wa "hv" i := by rw [ehv, if_neg hi0]
        exact hvD_eq_of_wa (s := s) hw
    -- SoftInvH at the post-move state, hole = popped vertex
    have hsoft5 : SoftInvH (hvD s st 0) s (fun v => t5.va "dist" v) (fun v => t5.wa "reach" v)
        (fun v => t5.wa "done" v) (hvD s t5) (fun i => t5.va "hd" i) (t5.w "h") (t5.w "ins") := by
      have hdd : (fun v => t5.va "dist" v) = (fun v => st.va "dist" v) := funext (fun _ => rfl)
      have hrr : (fun v => t5.wa "reach" v) = (fun v => st.wa "reach" v) := funext (fun _ => rfl)
      have hdn : (fun v => t5.wa "done" v) = (fun v => st.wa "done" v) := funext (fun _ => rfl)
      refine ⟨hInv.ghost, hInv.relax_hold, ?_, ?_, ?_, hInv.source0, hInv.done_reach⟩
      · -- entry hole at the popped vertex only
        intro u hne hr hd0
        obtain ⟨i, hi, hvi, hdi⟩ := hInv.entry_cur u hr hd0
        have hi0 : i ≠ 0 := by
          rintro rfl
          exact hne hvi.symm
        have hi1 : i ≤ st.w "h" - 1 := by omega
        by_cases him : i = st.w "h" - 1
        · refine ⟨0, by rw [hht]; omega, ?_, ?_⟩
          · rw [ehvD, if_pos rfl]; rw [him] at hvi; exact hvi
          · rw [ehd, if_pos rfl]; rw [him] at hdi; exact hdi
        · refine ⟨i, by rw [hht]; omega, ?_, ?_⟩
          · rw [ehvD, if_neg hi0]; exact hvi
          · rw [ehd, if_neg hi0]; exact hdi
      · -- entry_mono
        intro i hi
        by_cases hi0 : i = 0
        · rw [ehd, if_pos hi0, ehvD, if_pos hi0]
          exact hInv.entry_mono (st.w "h" - 1) (by omega)
        · rw [ehd, if_neg hi0, ehvD, if_neg hi0]
          exact hInv.entry_mono i (by rw [hht] at hi; omega)
      · -- entry_reach
        intro i hi
        by_cases hi0 : i = 0
        · rw [ehvD, if_pos hi0]
          exact hInv.entry_reach (st.w "h" - 1) (by omega)
        · rw [ehvD, if_neg hi0]
          exact hInv.entry_reach i (by rw [hht] at hi; omega)
    -- HeapOKExceptFrom at the root (pre-sift) + SiftDownOK entry
    have hOK5 : HeapOKExceptFrom (fun i => t5.va "hd" i) (t5.w "h") 0 := by
      intro i j hi hj hjr hine
      have hi' : i < st.w "h" := by rw [show t5.w "h" = st.w "h" - 1 from rfl] at hi; omega
      have hj' : j < st.w "h" := by rw [show t5.w "h" = st.w "h" - 1 from rfl] at hj; omega
      show t5.va "hd" i ≤ t5.va "hd" j
      rw [ehd, ehd]
      by_cases hz : i = 0
      · exact absurd hz hine
      · rw [if_neg hz]
        by_cases hz2 : j = 0
        · rw [hz2] at hjr; omega
        · rw [if_neg hz2]
          exact hInv.heapOK i hi' j hj' hjr
    have hK5 : SiftDownOK (hvD s st 0) s t5 (hvD s t5) (fun i => t5.va "hd" i)
        (hvD s st (st.w "h" - 1)) (st.va "hd" (st.w "h" - 1)) 0 := by
      refine ⟨hsoft5, ⟨?_, ?_⟩, ?_, ?_, hOK5, hOK5, ⟨0, rfl⟩, ?_⟩
      · rw [ehvD, if_pos rfl]
      · rw [ehd, if_pos rfl]
      · intro i hi
        by_cases hi0 : i = 0
        · exact Or.inl ⟨hi0, by rw [ehvD, if_pos hi0]⟩
        · exact Or.inr (Or.inr ⟨fun h => hi0 (by
            obtain ⟨t, ht⟩ := h.1
            have hle := mchOf_iter_le (fun i => t5.va "hd" i) (t5.w "h") i t
            rw [ht] at hle
            omega), rfl⟩)
      · intro i hi
        by_cases hi0 : i = 0
        · exact Or.inl ⟨hi0, by rw [ehd, if_pos hi0]⟩
        · exact Or.inr (Or.inr ⟨fun h => hi0 (by
            obtain ⟨t, ht⟩ := h.1
            have hle := mchOf_iter_le (fun i => t5.va "hd" i) (t5.w "h") i t
            rw [ht] at hle
            omega), rfl⟩)
      · rw [hht]; omega
    have hF5 : F0 G s t5 :=
      F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl
    have hAF5 : AF G t5 := AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl
    have hval5 : HeapV (G := G) t5 (t5.w "h") := by
      intro i hi
      rw [ehv]; split_ifs
      · exact hval (st.w "h" - 1) (by omega)
      · exact hval i (by rw [hht] at hi; omega)
    refine (siftDown_runs hF5 hAF5 hval5 hK5 (by rw [show t5.w "h" = st.w "h" - 1 from rfl]; omega)).mono ?_
    rintro st' ⟨hF', hAF', hInv', hheq, hinseq, hvR2, hdvR2, hcost, hvalS⟩
    refine ⟨hF', hAF', hInv', hheq.trans hht, hinseq, hvR2, hdvR2, ?_, hvalS, ?_⟩
    · rw [hvR2]; exact hv0lt
    · have hc5 : t5.cost = st.cost + 6 := rfl
      have hht : t5.w "h" = st.w "h" - 1 := rfl
      have h1 : rkD (st.w "h" - 1) 0 ≤ rkD (st.w "h") 0 := by
        have h2 : (st.w "h" - 1) / 1 = st.w "h" - 1 := Nat.div_one _
        have h3 : st.w "h" / 1 = st.w "h" := Nat.div_one _
        have h4 : st.w "h" - 1 ≤ st.w "h" := Nat.sub_le _ _
        simpa [rkD, h2, h3] using Nat.log_mono_right h4
      rw [hht] at hcost
      rw [hc5] at hcost
      omega

/-! ## The settle sweep (step 3)

`settleBody` stores `done[u] = 1` BEFORE relaxing `u`'s out-edges one at a time, so the
global `Inv.relax_hold` does not hold pre-sweep.  `SweepInv` weakens `relax_hold` to
(a) edges out of done sources other than `u`, and (b) `u`'s already-swept out-edges —
the first `k` links of the `head`/`nxt` chain (`chainOf st u k`).  `SweepInv.toInv`
collapses it back to `Inv` once `k` covers the full chain. -/

/-- One-edge relaxation obligation (state form; ENNReal to match `Inv.relax_hold`). -/
def EdgeRelaxed (G : Graph) (st : State ℝ≥0) (e : Fin G.m) : Prop :=
  st.wa "reach" (G.dst e) ≠ 0 ∧
    ((st.va "dist" (G.dst e) : ℝ≥0) : ℝ≥0∞) ≤ ((st.va "dist" (G.src e) : ℝ≥0) : ℝ≥0∞) + G.w e

/-- Chain well-formedness: every vertex's `head`/`nxt` chain enumerates its out-edges. -/
def ChainWF (G : Graph) (st : State ℝ≥0) : Prop :=
  ∀ u : ℕ, u < G.n → chainOf st u (G.m + 1) = outChainK G G.m u

/-- Sweep invariant of the settle sweep of `u`, at chain cursor `k`. -/
structure SweepInv (G : Graph) (s : Fin G.n) (u : Fin G.n) (st : State ℝ≥0) (k : ℕ) : Prop where
  ghost : ∀ v : Fin G.n, st.wa "reach" v ≠ 0 → ∃ p, G.IsWalk s v p ∧ G.len p = st.va "dist" v
  settled_exact : ∀ v : Fin G.n, st.wa "done" v ≠ 0 → ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) = G.dist s v
  relaxed_other : ∀ e : Fin G.m, G.src e ≠ u → st.wa "done" (G.src e) ≠ 0 → EdgeRelaxed G st e
  relaxed_swept : ∀ e : Fin G.m, (e : ℕ) ∈ chainOf st u k → EdgeRelaxed G st e
  entry_cur : ∀ v : Fin G.n, st.wa "reach" v ≠ 0 → st.wa "done" v = 0 →
    ∃ i, i < st.w "h" ∧ hvD s st i = v ∧ st.va "hd" i = st.va "dist" v
  entry_mono : ∀ i, i < st.w "h" → st.va "dist" (hvD s st i) ≤ st.va "hd" i
  entry_reach : ∀ i, i < st.w "h" → st.wa "reach" (hvD s st i) ≠ 0
  heapOK : HeapOK (hvD s st) (fun i => st.va "hd" i) (st.w "h")
  val : HeapV (G := G) st (st.w "h")
  source0 : st.va "dist" s = 0 ∧ st.wa "reach" s ≠ 0
  done_reach : ∀ v : Fin G.n, st.wa "done" v ≠ 0 → st.wa "reach" v ≠ 0
  chainWF : ChainWF G st
  done_u : st.wa "done" u ≠ 0
  k_le : k ≤ (chainOf st u (G.m + 1)).length

/-- A settled vertex's label is never undercut: any candidate along an edge into it is at
least its exact label, so `relaxBody`'s improvement test reads false and writes nothing. -/
theorem cand_ge_dist_done {G : Graph} {s : Fin G.n} {u x : Fin G.n} {st : State ℝ≥0}
    (e : Fin G.m) (hsrc : G.src e = u) (hdst : G.dst e = x)
    (hsettled : ∀ v : Fin G.n, st.wa "done" v ≠ 0 → ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) = G.dist s v)
    (hu : st.wa "done" u ≠ 0) (hx : st.wa "done" x ≠ 0) :
    st.va "dist" x ≤ st.va "dist" u + G.w e := by
  have huE : ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) = G.dist s u := hsettled u hu
  have hxE : ((st.va "dist" x : ℝ≥0) : ℝ≥0∞) = G.dist s x := hsettled x hx
  have htri : G.dist s x ≤ G.dist s u + G.w e := by
    simpa [hsrc, hdst] using Graph.dist_edge (s := s) e
  have hcast : ((st.va "dist" x : ℝ≥0) : ℝ≥0∞)
      ≤ ((st.va "dist" u : ℝ≥0) : ℝ≥0∞) + G.w e := by
    rw [hxE, huE]
    exact htri
  exact_mod_cast hcast

/-- At full chain coverage the sweep invariant collapses to the model `Inv`. -/
theorem SweepInv.toInv {G : Graph} {s u : Fin G.n} {st : State ℝ≥0} {k : ℕ}
    (S : SweepInv G s u st k) (hk : (chainOf st u (G.m + 1)).length ≤ k) :
    Inv G s (fun v => st.va "dist" v) (fun v => st.wa "reach" v) (fun v => st.wa "done" v)
      (hvD s st) (fun i => st.va "hd" i) (st.w "h") (st.w "ins") := by
  have hklen : k ≤ G.m + 1 := by
    have hkle := S.k_le
    have h1 := chainWalk_length_le st (st.wa "head" u) (G.m + 1)
    have h2 : (chainOf st u (G.m + 1)).length
        = (chainWalk st (st.wa "head" u) (G.m + 1)).length := rfl
    omega
  have hfull : chainOf st u k = chainOf st u (G.m + 1) :=
    chainWalk_fuel_stable hklen hk
  refine ⟨S.ghost, ?_, S.heapOK, S.entry_cur, S.entry_mono, S.entry_reach, S.source0, S.done_reach⟩
  intro e hdne
  by_cases hsu : G.src e = u
  · have hmem : (e : ℕ) ∈ chainOf st u k := by
      rw [hfull, S.chainWF u u.isLt]
      simp only [outChainK, List.mem_reverse, List.mem_filter, List.mem_range]
      exact ⟨e.isLt, by simp [srcN, hsu]⟩
    exact S.relaxed_swept e hmem
  · exact S.relaxed_other e hsu hdne

/-! ### The settle sweep: edge relaxation

`relaxBody` lowers the label of an unsettled vertex and (on a strict improvement) pushes it.
The edge being relaxed is the `k`-th link of `u`'s out-edge chain, so the sweep invariant
advances from cursor `k` to `k + 1`. -/

theorem v_setV (st : State ℝ≥0) (x y : String) (a : ℝ≥0) :
    (st.setV x a).v y = if y = x then a else st.v y := rfl

theorem v_setW (st : State ℝ≥0) (x y : String) (a : ℕ) : (st.setW x a).v y = st.v y := rfl

theorem v_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) (x : String) :
    (st.storeW arr j a).v x = st.v x := rfl

theorem v_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) (x : String) :
    (st.storeV arr j z).v x = st.v x := rfl

theorem v_charge (st : State ℝ≥0) (k : ℕ) (x : String) : (st.charge k).v x = st.v x := rfl

theorem HeapOK.congr {hd hd' : ℕ → ℝ≥0} {h h' : ℕ} {hv hv' : ℕ → Fin G.n}
    (H : HeapOK hv hd h) (hh : h' = h) (he : ∀ i, hd' i = hd i) : HeapOK hv' hd' h' := by
  intro i hi j hj hjr
  rw [hh] at hi hj
  rw [he i, he j]
  exact H i hi j hj hjr

/-- A failed `vle` test: the right operand is strictly smaller. -/
theorem lt_of_vle_zero {a b : ℝ≥0} (h : (if realOps.le a b then 1 else 0) = 0) : b < a := by
  rw [bit_le] at h
  by_cases hle : a ≤ b
  · rw [if_pos hle] at h
    exact absurd h (by simp)
  · exact not_le.mp hle

/-- The out-edge chain at fuel `k` is a prefix of the full chain. -/
theorem chainOf_take {st : State ℝ≥0} {u : ℕ} {k : ℕ} (hk : k ≤ G.m + 1) :
    chainOf st u k = (chainOf st u (G.m + 1)).take k := by
  have hidx : k + (G.m + 1 - k) = G.m + 1 := by omega
  have h := chainWalk_take st k (st.wa "head" u) (G.m + 1 - k)
  rw [hidx] at h
  exact h

/-- A sweep cursor never exceeds the chain fuel. -/
theorem SweepInv.k_le_fuel {st : State ℝ≥0} {u : Fin G.n} {k : ℕ}
    (S : SweepInv G s u st k) : k ≤ G.m + 1 := by
  have h1 := S.k_le
  have h2 := chainWalk_length_le st (st.wa "head" u) (G.m + 1)
  simp only [chainOf] at h1 h2 ⊢
  omega

/-- Relaxing the label of an unsettled vertex preserves an established edge obligation: the
target may only sit lower, and the source of such an obligation is settled, hence not `x`. -/
theorem EdgeRelaxed.lower {st t : State ℝ≥0} {e : Fin G.m} {x : Fin G.n} {cand : ℝ≥0}
    (h : EdgeRelaxed G st e) (hxnot : G.src e ≠ x)
    (hreachx : t.wa "reach" x ≠ 0)
    (hreach : t.wa "reach" (G.dst e) ≠ 0)
    (hdist : ∀ v : Fin G.n, v ≠ x → t.va "dist" v = st.va "dist" v)
    (hdistx : t.va "dist" x = cand)
    (hle : st.wa "reach" x ≠ 0 → cand ≤ st.va "dist" x) :
    EdgeRelaxed G t e := by
  refine ⟨hreach, ?_⟩
  have hsrc : t.va "dist" (G.src e) = st.va "dist" (G.src e) := hdist _ hxnot
  by_cases hd : G.dst e = x
  · rw [hd] at hreach ⊢
    have hrx : st.wa "reach" x ≠ 0 := by rw [← hd]; exact h.1
    have h2 := h.2
    rw [hd] at h2
    rw [hdistx, hsrc]
    exact le_trans (by exact_mod_cast hle hrx) h2
  · rw [hdist _ hd, hsrc]
    exact h.2

/-- Transport the sweep invariant across a state that agrees on the heap, the registers it
reads, and the three label arrays. -/
theorem SweepInv.congr {st t : State ℝ≥0} {u : Fin G.n} {k : ℕ} (S : SweepInv G s u st k)
    (hhead : ∀ w, t.wa "head" w = st.wa "head" w)
    (hnxt : ∀ j, t.wa "nxt" j = st.wa "nxt" j)
    (hreach : ∀ j, t.wa "reach" j = st.wa "reach" j)
    (hdone : ∀ j, t.wa "done" j = st.wa "done" j)
    (hdist : ∀ j, t.va "dist" j = st.va "dist" j)
    (hhv : ∀ i, t.wa "hv" i = st.wa "hv" i)
    (hhd : ∀ i, t.va "hd" i = st.va "hd" i)
    (hh : t.w "h" = st.w "h") (hins : t.w "ins" = st.w "ins") :
    SweepInv G s u t k := by
  have hchain : ∀ (v : ℕ) (k' : ℕ), k' ≤ G.m + 1 → chainOf t v k' = chainOf st v k' := by
    intro v k' _
    simp only [chainOf, hhead]
    exact chainWalk_congr (fun j _ => hnxt j)
  have hnot : chainOf t u (G.m + 1) = chainOf st u (G.m + 1) := hchain u _ (le_refl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨p, hp, hlen⟩ := S.ghost v (by rw [← hreach ↑v]; exact hv)
    exact ⟨p, hp, by rw [hlen, hdist ↑v]⟩
  · intro v hd
    rw [hdist ↑v]
    exact S.settled_exact v (by rw [← hdone ↑v]; exact hd)
  · intro e' hsrc' hdn'
    obtain ⟨h1, h2⟩ := S.relaxed_other e' hsrc' (by rw [← hdone ↑(G.src e')]; exact hdn')
    refine ⟨by rw [hreach ↑(G.dst e')]; exact h1, ?_⟩
    show ((t.va "dist" ↑(G.dst e') : ℝ≥0) : ℝ≥0∞)
      ≤ ((t.va "dist" ↑(G.src e') : ℝ≥0) : ℝ≥0∞) + G.w e'
    rw [hdist ↑(G.dst e'), hdist ↑(G.src e')]
    exact h2
  · intro e' hmem
    obtain ⟨h1, h2⟩ := S.relaxed_swept e' (by rw [← hchain u k (S.k_le_fuel)]; exact hmem)
    refine ⟨by rw [hreach ↑(G.dst e')]; exact h1, ?_⟩
    show ((t.va "dist" ↑(G.dst e') : ℝ≥0) : ℝ≥0∞)
      ≤ ((t.va "dist" ↑(G.src e') : ℝ≥0) : ℝ≥0∞) + G.w e'
    rw [hdist ↑(G.dst e'), hdist ↑(G.src e')]
    exact h2
  · intro v hr hd0
    obtain ⟨i, hi, hiv, hid⟩ := S.entry_cur v (by rw [← hreach ↑v]; exact hr)
      (by rw [← hdone ↑v]; exact hd0)
    exact ⟨i, by rw [hh]; exact hi, (hvD_congr hhv i).trans hiv,
      by rw [hhd i, hdist ↑v]; exact hid⟩
  · intro i hi
    rw [hvD_congr hhv i, hdist ↑(hvD s st i), hhd i]
    exact S.entry_mono i (by rw [← hh]; exact hi)
  · intro i hi
    rw [hvD_congr hhv i, hreach ↑(hvD s st i)]
    exact S.entry_reach i (by rw [← hh]; exact hi)
  · exact HeapOK.congr S.heapOK hh hhd
  · intro i hi
    rw [hh] at hi
    rw [hhv i]
    exact S.val i hi
  · refine ⟨?_, ?_⟩
    · rw [hdist ↑s]; exact S.source0.1
    · rw [hreach ↑s]; exact S.source0.2
  · intro v hd
    rw [hreach ↑v]
    exact S.done_reach v (by rw [← hdone ↑v]; exact hd)
  · intro w hw
    rw [hchain w (G.m + 1) (le_refl _)]
    exact S.chainWF w hw
  · rw [hdone ↑u]; exact S.done_u
  · rw [hnot]; exact S.k_le

/-- Advance the sweep cursor by one edge whose obligation already holds (no write taken). -/
theorem SweepInv.advance_static {st : State ℝ≥0} {u : Fin G.n} {k : ℕ} {e : Fin G.m}
    (S : SweepInv G s u st k) (hEk : EdgeRelaxed G st e)
    (htake : (chainOf st u (G.m + 1)).take (k + 1)
      = (chainOf st u (G.m + 1)).take k ++ [(e : ℕ)]) :
    SweepInv G s u st (k + 1) := by
  have hlen : k + 1 ≤ (chainOf st u (G.m + 1)).length := by
    have h := congrArg List.length htake
    simp at h
    omega
  refine ⟨S.ghost, S.settled_exact, S.relaxed_other, ?_, S.entry_cur, S.entry_mono,
    S.entry_reach, S.heapOK, S.val, S.source0, S.done_reach, S.chainWF, S.done_u, hlen⟩
  intro e' hmem
  have hk1 : k + 1 ≤ G.m + 1 := by
    have h2 := chainWalk_length_le st (st.wa "head" u) (G.m + 1)
    simp only [chainOf] at hlen h2 ⊢
    omega
  have hkf : k ≤ G.m + 1 := by omega
  have hkt : chainOf st u k = (chainOf st u (G.m + 1)).take k := chainOf_take hkf
  have hkt1 :
      chainOf st u (k + 1) = (chainOf st u (G.m + 1)).take (k + 1) := chainOf_take hk1
  have hmem1 : (e' : ℕ) ∈ (chainOf st u (G.m + 1)).take (k + 1) := by
    rw [← hkt1]; exact hmem
  rcases List.mem_append.mp (htake ▸ hmem1) with h | h
  · exact S.relaxed_swept e' (by rw [hkt]; exact h)
  · have hve : e' = e := Fin.eq_of_val_eq (List.mem_singleton.mp h)
    rw [hve]
    exact hEk

/-- Advance the sweep cursor by one edge whose head was just lowered to `cand` and pushed. -/
theorem SweepInv.push_relax {st t : State ℝ≥0} {u x : Fin G.n} {cand : ℝ≥0} {k : ℕ}
    {e : Fin G.m}
    (S : SweepInv G s u st k)
    (hdonex : st.wa "done" x = 0)
    (hxnot : x ≠ u) (hxs : x ≠ s)
    (hsrcv : G.src e = u) (hdstv : G.dst e = x)
    (hcand : st.va "dist" u + G.w e = cand)
    (htake : (chainOf st u (G.m + 1)).take (k + 1)
      = (chainOf st u (G.m + 1)).take k ++ [(e : ℕ)])
    (hEk : EdgeRelaxed G t e)
    (ES : EntrySoft s (fun v => t.va "dist" v) (fun v => t.wa "reach" v) (fun v => t.wa "done" v)
      (hvD s t) (fun i => t.va "hd" i) (t.w "h") (t.w "ins"))
    (HOK : HeapOK (hvD s t) (fun i => t.va "hd" i) (t.w "h"))
    (VAL : HeapV (G := G) t (t.w "h"))
    (hhead : ∀ w, t.wa "head" w = st.wa "head" w)
    (hnxt : ∀ j, t.wa "nxt" j = st.wa "nxt" j)
    (hdone : ∀ j, t.wa "done" j = st.wa "done" j)
    (hdist : ∀ j, j ≠ (x : ℕ) → t.va "dist" j = st.va "dist" j)
    (hdistx : t.va "dist" ↑x = cand)
    (hreach : ∀ j, j ≠ (x : ℕ) → t.wa "reach" j = st.wa "reach" j)
    (hreachx : t.wa "reach" ↑x ≠ 0)
    (hle : st.wa "reach" ↑x ≠ 0 → cand ≤ st.va "dist" ↑x)
    (hsw : ∀ e' : Fin G.m, (e' : ℕ) ∈ (chainOf st u (G.m + 1)).take k → G.src e' = u) :
    SweepInv G s u t (k + 1) := by
  have hxne : ∀ (v : Fin G.n), v ≠ x → (v : ℕ) ≠ (x : ℕ) := by
    intro v hv hvv
    exact hv (Fin.eq_of_val_eq hvv)
  have hchain : ∀ (v : ℕ) (k' : ℕ), k' ≤ G.m + 1 → chainOf t v k' = chainOf st v k' := by
    intro v k' _
    simp only [chainOf, hhead]
    exact chainWalk_congr (fun j _ => hnxt j)
  have hnot : chainOf t u (G.m + 1) = chainOf st u (G.m + 1) := hchain u _ (le_refl _)
  have hlen : k + 1 ≤ (chainOf st u (G.m + 1)).length := by
    have h := congrArg List.length htake
    simp at h
    omega
  have hkf : k ≤ G.m + 1 := by
    have h2 := chainWalk_length_le st (st.wa "head" u) (G.m + 1)
    simp only [chainOf] at hlen h2 ⊢
    omega
  have hkt : chainOf st u k = (chainOf st u (G.m + 1)).take k := chainOf_take hkf
  have hk1 : k + 1 ≤ G.m + 1 := by
    have h2 := chainWalk_length_le st (st.wa "head" u) (G.m + 1)
    simp only [chainOf] at hlen h2 ⊢
    omega
  have hkt1 :
      chainOf st u (k + 1) = (chainOf st u (G.m + 1)).take (k + 1) := chainOf_take hk1
  -- the transport of an already-obliged edge through the label write
  have hold : ∀ e' : Fin G.m, (e' : ℕ) ∈ (chainOf st u (G.m + 1)).take k →
      EdgeRelaxed G t e' := by
    intro e' hmem
    have hold' := S.relaxed_swept e' (by rw [hkt]; exact hmem)
    have hsrcn : G.src e' ≠ x := by
      rw [hsw e' hmem]
      exact fun hh => hxnot hh.symm
    refine EdgeRelaxed.lower hold' hsrcn hreachx ?_ ?_ hdistx hle
    · by_cases hd : G.dst e' = x
      · rw [hd]; exact hreachx
      · rw [hreach ↑(G.dst e') (hxne _ hd)]; exact hold'.1
    · exact fun v hv => hdist ↑v (hxne v hv)
  refine ⟨?_, ?_, ?_, ?_, ES.entry_cur, ES.entry_mono, ES.entry_reach, HOK, VAL, ?_, ?_, ?_, ?_, ?_⟩
  · -- ghost: the new walk to `x` is `u`'s walk extended by the relaxed edge
    intro v hr
    by_cases hvx : v = x
    · rw [hvx]
      obtain ⟨p, hp, hlen'⟩ := S.ghost u (S.done_reach u S.done_u)
      refine ⟨p ++ [e], ?_, ?_⟩
      · refine Graph.IsWalk.append hp ?_
        rw [← hsrcv, ← hdstv]
        exact Graph.IsWalk.single e
      · rw [hdistx]
        rw [G.len_append, G.len_singleton, hlen', hcand]
    · obtain ⟨p, hp, hlen'⟩ := S.ghost v (by rw [← hreach ↑v (hxne v hvx)]; exact hr)
      exact ⟨p, hp, by rw [hlen', hdist ↑v (hxne v hvx)]⟩
  · -- settled_exact: nothing is written at a settled vertex
    intro v hd
    by_cases hvx : v = x
    · rw [hvx] at hd ⊢
      have hst : st.wa "done" ↑x = 0 := hdonex
      rw [hdone ↑x] at hd
      exact absurd hst hd
    · rw [hdist ↑v (hxne v hvx)]
      exact S.settled_exact v (by rw [← hdone ↑v]; exact hd)
  · -- relaxed_other
    intro e' hsrc' hdn'
    have hold' := S.relaxed_other e' hsrc' (by rw [← hdone ↑(G.src e')]; exact hdn')
    have hsrcn : G.src e' ≠ x := by
      intro hxx
      have hst : st.wa "done" ↑x ≠ 0 := by
        rw [← hxx]
        rw [← hdone ↑(G.src e')]
        exact hdn'
      rw [hdonex] at hst
      exact hst rfl
    refine EdgeRelaxed.lower hold' hsrcn hreachx ?_ ?_ hdistx hle
    · by_cases hd : G.dst e' = x
      · rw [hd]; exact hreachx
      · rw [hreach ↑(G.dst e') (hxne _ hd)]; exact hold'.1
    · exact fun v hv => hdist ↑v (hxne v hv)
  · -- relaxed_swept: the old prefix transports, the new edge is `e`
    intro e' hmem
    have hmem1 : (e' : ℕ) ∈ (chainOf st u (G.m + 1)).take (k + 1) := by
      have h3 : (e' : ℕ) ∈ chainOf t u (k + 1) := hmem
      rw [hchain u (k + 1) hk1, hkt1] at h3
      exact h3
    rcases List.mem_append.mp (htake ▸ hmem1) with h | h
    · exact hold e' h
    · have hve : e' = e := Fin.eq_of_val_eq (List.mem_singleton.mp h)
      rw [hve]
      exact hEk
  · -- source0: the source is reached, so the test could not improve it
    refine ⟨?_, ?_⟩
    · rw [hdist ↑s (hxne s (Ne.symm hxs))]; exact S.source0.1
    · rw [hreach ↑s (hxne s (Ne.symm hxs))]; exact S.source0.2
  · -- done_reach
    intro v hd
    by_cases hvx : v = x
    · rw [hvx] at hd ⊢
      rw [hdone ↑x] at hd
      exact absurd hdonex hd
    · rw [hreach ↑v (hxne v hvx)]
      exact S.done_reach v (by rw [← hdone ↑v]; exact hd)
  · -- chainWF
    intro w hw
    rw [hchain w (G.m + 1) (le_refl _)]
    exact S.chainWF w hw
  · -- done_u
    rw [hdone ↑u]; exact S.done_u
  · -- k_le
    rw [hnot]
    exact hlen

/-- The taken-relax suffix of `relaxBody` (`fl = 1`): lower `x`'s label to `cand`, mark it
reached, and — since `x` is unsettled — push it. -/
theorem relax_take_runs {t : State ℝ≥0} {u x : Fin G.n} {e : Fin G.m} {k : ℕ} {cand : ℝ≥0}
    (hF : F0 G s t) (hAF : AF G t)
    (hxv : t.w "x" = (x : ℕ))
    (hcandv : t.v "cand" = cand)
    (hcand : t.va "dist" u + G.w e = cand)
    (hval : HeapV (G := G) t (t.w "h"))
    (hbound : t.w "h" ≤ G.m) (hinsb : t.w "ins" ≤ G.m)
    (hdx0 : t.wa "done" x = 0)
    (hxnot : x ≠ u) (hxs : x ≠ s)
    (hsrcv : G.src e = u) (hdstv : G.dst e = x)
    (htake : (chainOf t u (G.m + 1)).take (k + 1)
      = (chainOf t u (G.m + 1)).take k ++ [(e : ℕ)])
    (S : SweepInv G s u t k)
    (hsw : ∀ e' : Fin G.m, (e' : ℕ) ∈ (chainOf t u (G.m + 1)).take k → G.src e' = u)
    (hle : t.wa "reach" x ≠ 0 → cand ≤ t.va "dist" x) :
    Runs realOps
      (seq (vstore "dist" (var "x") (.var "cand"))
        (seq (wstore "reach" (var "x") (lit 1))
          (ite (eq (load "done" (var "x")) (lit 0))
            (seq (wset "pv" (var "x")) pushBody) skip))) t (fun t' =>
      SweepInv G s u t' (k + 1) ∧ F0 G s t' ∧ AF G t' ∧
      chainOf t' u (G.m + 1) = chainOf t u (G.m + 1) ∧
      t'.w "v" = t.w "v" ∧
      t'.w "h" = t.w "h" + 1 ∧
      t'.w "ins" = t.w "ins" + 1 ∧
      t'.cost ≤ t.cost + 12 * rk (t.w "h") + 20) := by
  have hcap0 : 0 < t.cap := by have := hF.hcap; omega
  have hcap1 : 1 < t.cap := by have := hF.hcap; omega
  have hdstLen : (x : ℕ) < t.vlen "dist" := by rw [hAF.distL]; exact x.isLt
  refine runs_seq (runs_vstore (arr := "dist") (i := var "x") (e := .var "cand")
    (by rw [evalW_var, hxv]) rfl hdstLen ?_)
  set t1 := (t.storeV "dist" (x : ℕ) (t.v "cand")).charge 1 with ht1
  have hx1 : evalW t1 (var "x") = some (x : ℕ) := by
    rw [evalW_var]
    rw [show t1.w "x" = t.w "x" from rfl, hxv]
  have hone1 : evalW t1 (lit 1) = some 1 :=
    evalW_lit_of (by show 1 < t1.cap; exact hcap1)
  have hreachLen : (x : ℕ) < t1.wlen "reach" := by
    rw [show t1.wlen "reach" = t.wlen "reach" from rfl, hAF.reachL]; exact x.isLt
  refine runs_seq (runs_wstore (arr := "reach") (i := var "x") (e := lit 1) hx1 hone1
    hreachLen ?_)
  set t2 := (t1.storeW "reach" (x : ℕ) 1).charge 1 with ht2
  have hdoneE : evalW t2 (eq (load "done" (var "x")) (lit 0))
      = some (if t.wa "done" (x : ℕ) = 0 then 1 else 0) := by
    have hload : evalW t2 (load "done" (var "x")) = some (t.wa "done" (x : ℕ)) := by
      have h := evalW_load_of (s := t2) (arr := "done") (i := var "x") (j := (x : ℕ))
        (by rw [evalW_var]; rw [show t2.w "x" = t.w "x" from rfl, hxv])
        (by rw [show t2.wlen "done" = t.wlen "done" from rfl, hAF.doneL]; exact x.isLt)
      rwa [show t2.wa "done" (x : ℕ) = t.wa "done" (x : ℕ) from rfl] at h
    exact evalW_eq_of hload (evalW_lit_of (by show 0 < t2.cap; exact hcap0)) (by
      show 1 < t2.cap; exact hcap1)
  refine runs_ite_true (x := 1) (by rw [hdoneE, if_pos hdx0]) (by decide) ?_
  have hpvE : evalW (t2.charge 1) (var "x") = some (x : ℕ) := by
    rw [evalW_var]
    rw [show (t2.charge 1).w "x" = t.w "x" from rfl, hxv]
  refine runs_seq (runs_wset (x := "pv") hpvE ?_)
  set t3 := ((t2.charge 1).setW "pv" (x : ℕ)).charge 1 with ht3
  -- final-state register/array reads
  have hdistT : ∀ j, j ≠ (x : ℕ) → t3.va "dist" j = t.va "dist" j := by
    intro j hj
    rw [ht3, va_charge, va_setW, ht2, va_charge, va_charge, va_storeW, ht1, va_charge,
      va_storeV]
    rw [if_neg (by intro hc; exact hj hc.2)]
  have hdistTx : t3.va "dist" (x : ℕ) = cand := by
    rw [ht3, va_charge, va_setW, ht2, va_charge, va_charge, va_storeW, ht1, va_charge,
      va_storeV]
    rw [if_pos ⟨rfl, rfl⟩, hcandv]
  have hreachT : ∀ j, j ≠ (x : ℕ) → t3.wa "reach" j = t.wa "reach" j := by
    intro j hj
    rw [ht3, wa_charge, wa_setW, ht2, wa_charge, wa_charge, wa_storeW, ht1, wa_charge,
      wa_storeV]
    rw [if_neg (by intro hc; exact hj hc.2)]
  have hreachTx : t3.wa "reach" (x : ℕ) = 1 := by
    rw [ht3, wa_charge, wa_setW, ht2, wa_charge, wa_charge, wa_storeW, ht1, wa_charge,
      wa_storeV]
    rw [if_pos ⟨rfl, rfl⟩]
  have hhdT : ∀ i, t3.va "hd" i = t.va "hd" i := by
    intro i
    rw [ht3, va_charge, va_setW, ht2, va_charge, va_charge, va_storeW, ht1, va_charge,
      va_storeV]
    rw [if_neg (by intro hc; exact absurd hc.1 (by decide))]
  -- every word array other than `reach` is untouched by the relax prefix
  have hwT : ∀ (arr : String) (j : ℕ), arr ≠ "reach" → t3.wa arr j = t.wa arr j := by
    intro arr j harr
    rw [ht3, wa_charge, wa_setW, ht2, wa_charge, wa_charge, wa_storeW, ht1, wa_charge,
      wa_storeV]
    rw [if_neg (by intro hc; exact absurd hc.1 harr)]
  have hdoneT : ∀ j, t3.wa "done" j = t.wa "done" j := fun j => hwT "done" j (by decide)
  have hhvT3 : ∀ i, t3.wa "hv" i = t.wa "hv" i := fun i => hwT "hv" i (by decide)
  have hheadT : ∀ w, t3.wa "head" w = t.wa "head" w := fun w => hwT "head" w (by decide)
  have hnxtT : ∀ j, t3.wa "nxt" j = t.wa "nxt" j := fun j => hwT "nxt" j (by decide)
  have hhvT : ∀ i, hvD s t3 i = hvD s t i := fun i => hvD_eq_of_wa (hhvT3 i)
  have hhT : t3.w "h" = t.w "h" := by
    rw [ht3, w_charge, w_setW, ht2, w_charge, w_charge, w_storeW, ht1, w_charge, w_storeV]
    rw [if_neg (by decide)]
  have hinsT : t3.w "ins" = t.w "ins" := by
    rw [ht3, w_charge, w_setW, ht2, w_charge, w_charge, w_storeW, ht1, w_charge, w_storeV]
    rw [if_neg (by decide)]
  have hpv3 : t3.w "pv" = (x : ℕ) := by
    rw [ht3, w_charge, w_setW]
    rw [if_pos rfl]
  have hpvlt : t3.w "pv" < G.n := by rw [hpv3]; exact x.isLt
  have hreachv3 : t3.wa "reach" (t3.w "pv") ≠ 0 := by
    rw [hpv3, hreachTx]; exact one_ne_zero
  have hN : ∀ (v : Fin G.n), (v : ℕ) ≠ (x : ℕ) → v ≠ x :=
    fun v hv hvv => hv (by rw [hvv])
  have hNatNe : ∀ (v : Fin G.n), v ≠ x → (v : ℕ) ≠ (x : ℕ) :=
    fun v hv hc => hv (Fin.eq_of_val_eq hc)
  -- the entry set at `t3`, holed at the vertex being pushed
  have hESH : EntrySoftH ⟨t3.w "pv", hpvlt⟩ s (fun v => t3.va "dist" v)
      (fun v => t3.wa "reach" v) (fun v => t3.wa "done" v) (hvD s t3)
      (fun i => t3.va "hd" i) (t3.w "h") (t3.w "ins") := by
    have hne : ∀ (v : Fin G.n), v ≠ ⟨t3.w "pv", hpvlt⟩ → (v : ℕ) ≠ (x : ℕ) := by
      intro v hv hvv
      exact hv (Fin.ext (by rw [hvv]; exact hpv3.symm))
    refine ⟨?_, ?_, ?_⟩
    · intro v hvx' hr hd0
      obtain ⟨i, hi, hiv, hid⟩ := S.entry_cur v
        (by rw [← hreachT ↑v (hne v hvx')]; exact hr)
        (by rw [← hdoneT ↑v]; exact hd0)
      refine ⟨i, hi, ?_, ?_⟩
      · rw [hhvT i]; exact hiv
      · rw [hhdT i, hdistT ↑v (hne v hvx')]; exact hid
    · intro i hi
      have hi' : i < t.w "h" := hi
      by_cases hix : hvD s t3 i = x
      · have hix' : hvD s t i = x := by rw [← hhvT i]; exact hix
        have hrx : t.wa "reach" (x : ℕ) ≠ 0 := by
          have h := S.entry_reach i hi'
          rw [← hhvT i, hix] at h
          exact h
        rw [hix, hdistTx, hhdT i]
        calc cand ≤ t.va "dist" (x : ℕ) := hle hrx
          _ = t.va "dist" (hvD s t i) := by rw [hix']
          _ ≤ t.va "hd" i := S.entry_mono i hi'
      · rw [hdistT ↑(hvD s t3 i) (hNatNe _ hix), hhdT i, hhvT i]
        exact S.entry_mono i hi'
    · intro i hi
      have hi' : i < t.w "h" := hi
      by_cases hix : hvD s t3 i = x
      · rw [hix, hreachTx]; exact one_ne_zero
      · rw [hreachT ↑(hvD s t3 i) (hNatNe _ hix), hhvT i]
        exact S.entry_reach i hi'
  have hF3 : F0 G s t3 := F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl rfl rfl
  have hAF3 : AF G t3 := AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl
  have hheap3 : HeapOK (hvD s t3) (fun i => t3.va "hd" i) (t3.w "h") :=
    HeapOK.congr S.heapOK hhT hhdT
  have hval3 : HeapV (G := G) t3 (t3.w "h") := by
    intro i hi
    rw [hhT] at hi
    rw [hhvT3 i]
    exact S.val i hi
  refine (pushBody_runs (st := t3) hF3 hAF3 hpvlt hESH hheap3 hval3 hreachv3
    (by rw [hhT]; exact hbound) (by rw [hinsT]; exact hinsb)).mono ?_
  rintro t4 ⟨hF4, hAF4, hES4, hHOK4, hh4, hins4, hval4, hfr4, hcost4⟩
  have hh4' : t4.w "h" = t.w "h" + 1 := by rw [hh4, hhT]
  -- `pushBody` writes only heap slots and counters (its Q carries the frame)
  have hEk : EdgeRelaxed G t4 e := by
    refine ⟨?_, ?_⟩
    · rw [hdstv, hfr4.reach, hreachTx]; exact one_ne_zero
    · have hxl : t4.va "dist" (x : ℕ) = cand := (hfr4.dist x).trans hdistTx
      have hul : t4.va "dist" (u : ℕ) = t.va "dist" (u : ℕ) :=
        (hfr4.dist u).trans (hdistT (u : ℕ) (hNatNe u hxnot.symm))
      rw [hdstv, hsrcv, hxl, hul, ← hcand, ENNReal.coe_add]
  refine ⟨SweepInv.push_relax (st := t) (t := t4) S hdx0 hxnot hxs hsrcv hdstv hcand htake hEk
    hES4 hHOK4 hval4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hle hsw, hF4, hAF4, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [hfr4.head w, hheadT w]
  · intro j
    rw [hfr4.nxt j, hnxtT j]
  · intro j
    rw [hfr4.done j, hdoneT j]
  · intro j hj
    rw [hfr4.dist j, hdistT j hj]
  · rw [hfr4.dist x, hdistTx]
  · intro j hj
    rw [hfr4.reach j, hreachT j hj]
  · rw [hfr4.reach x, hreachTx]
    exact one_ne_zero
  · -- chain stability
    have hch : ∀ (v : ℕ) (k' : ℕ), chainOf t4 v k' = chainOf t v k' := by
      intro v k'
      simp only [chainOf]
      rw [hfr4.head v, hheadT v]
      exact chainWalk_congr (fun j _ => by rw [hfr4.nxt j, hnxtT j])
    exact hch u (G.m + 1)
  · -- the popped-vertex register is untouched
    rw [hfr4.regv, ht3, w_charge, w_setW, ht2, w_charge, w_charge, w_storeW, ht1,
      w_charge, w_storeV]
    rw [if_neg (by decide)]
  · -- the heap grows by exactly one (the push)
    rw [hh4, hhT]
  · -- so does the insert counter
    rw [hins4, hinsT]
  · -- cost
    have hc3 : t3.cost = t.cost + 4 := rfl
    rw [hc3, hhT] at hcost4
    omega

/-- `relaxBody`: the taken write arms (label unset, or `cand` strictly improves it) delegate
to `relax_take_runs`; the arm where the improvement test fails takes no write and advances the
sweep cursor statically, the edge obligation being discharged by the test itself. -/
theorem relaxBody_runs {t : State ℝ≥0} {u x : Fin G.n} {e : Fin G.m} {k : ℕ} {cand : ℝ≥0}
    (hF : F0 G s t) (hAF : AF G t)
    (hxv : t.w "x" = (x : ℕ))
    (hcandv : t.v "cand" = cand)
    (hcand : t.va "dist" u + G.w e = cand)
    (hval : HeapV (G := G) t (t.w "h"))
    (hbound : t.w "h" ≤ G.m) (hinsb : t.w "ins" ≤ G.m)
    (hxnot : x ≠ u) (hxs : x ≠ s)
    (hsrcv : G.src e = u) (hdstv : G.dst e = x)
    (htake : (chainOf t u (G.m + 1)).take (k + 1)
      = (chainOf t u (G.m + 1)).take k ++ [(e : ℕ)])
    (S : SweepInv G s u t k)
    (hsw : ∀ e' : Fin G.m, (e' : ℕ) ∈ (chainOf t u (G.m + 1)).take k → G.src e' = u) :
    Runs realOps relaxBody t (fun t' =>
      SweepInv G s u t' (k + 1) ∧ F0 G s t' ∧ AF G t' ∧
      chainOf t' u (G.m + 1) = chainOf t u (G.m + 1) ∧
      t'.w "v" = t.w "v" ∧
      t'.w "h" ≤ t.w "h" + 1 ∧
      t'.w "ins" ≤ t.w "ins" + 1 ∧
      t'.cost ≤ t.cost + 12 * rk (t.w "h") + 25) := by
  have hcap0 : 0 < t.cap := by have := hF.hcap; omega
  have hcap1 : 1 < t.cap := by have := hF.hcap; omega
  have hxE : evalW t (var "x") = some (x : ℕ) := by
    rw [evalW_var]; exact congrArg some hxv
  have hloadR : evalW t (load "reach" (var "x")) = some (t.wa "reach" (x : ℕ)) :=
    evalW_load_of hxE (by rw [hAF.reachL]; exact x.isLt)
  have hcondE : evalW t (eq (load "reach" (var "x")) (lit 0))
      = some (if t.wa "reach" (x : ℕ) = 0 then 1 else 0) :=
    evalW_eq_of hloadR (evalW_lit_of (by show 0 < t.cap; exact hcap0))
      (by show 1 < t.cap; exact hcap1)
  have hchfix : ∀ {t' : State ℝ≥0}, (∀ w, t'.wa "head" w = t.wa "head" w) →
      (∀ j, t'.wa "nxt" j = t.wa "nxt" j) →
      chainOf t' u (G.m + 1) = chainOf t u (G.m + 1) := by
    intro t' h1 h2
    simp only [chainOf]
    rw [h1 u]
    exact chainWalk_congr (fun j _ => h2 j)
  simp only [relaxBody]
  refine runs_seq ?_
  by_cases hr : t.wa "reach" (x : ℕ) = 0
  · -- arm A: `reach x = 0` — take, no `dist` test
    refine runs_ite_true (x := 1) (by rw [hcondE, if_pos hr]) (by decide) ?_
    refine runs_wset (x := "fl") (a := 1)
      (evalW_lit_of (by show 1 < (t.charge 1).cap; rw [cap_charge]; exact hcap1)) ?_
    set tA := ((t.charge 1).setW "fl" 1).charge 1 with htA
    have hflA : tA.w "fl" = 1 := by rw [htA, w_charge, w_setW, if_pos rfl]
    refine runs_ite_true (x := 1) (by rw [evalW_var, hflA]) (by decide) ?_
    set tB := tA.charge 1 with htB
    have hhB : tB.w "h" = t.w "h" := rfl
    have hiB : tB.w "ins" = t.w "ins" := rfl
    have hSB : SweepInv G s u tB k :=
      S.congr (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) hhB hiB
    have hvalB : HeapV (G := G) tB (tB.w "h") := by
      intro i hi
      rw [hhB] at hi
      exact hval i hi
    have hdx0 : t.wa "done" (x : ℕ) = 0 := by
      by_contra hne
      exact S.done_reach x hne hr
    have hleB : tB.wa "reach" (x : ℕ) ≠ 0 → cand ≤ tB.va "dist" (x : ℕ) := by
      intro hne
      rw [show tB.wa "reach" (x : ℕ) = t.wa "reach" (x : ℕ) from rfl] at hne
      exact absurd hr hne
    have hchB : chainOf tB u (G.m + 1) = chainOf t u (G.m + 1) :=
      hchfix (fun _ => rfl) (fun _ => rfl)
    have hcostB : tB.cost = t.cost + 3 := by
      simp only [htB, htA, cost_charge, cost_setW]
    refine (relax_take_runs (t := tB) (s := s) (u := u) (x := x) (e := e) (k := k)
      (cand := cand)
      (F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        rfl rfl rfl)
      (AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl)
      hxv hcandv hcand hvalB hbound hinsb
      hdx0 hxnot hxs hsrcv hdstv (by rw [hchB]; exact htake) hSB
      (by rw [hchB]; exact hsw) hleB).mono ?_
    rintro t' ⟨hS', hF', hAF', hch', hv', hst', hins', hc'⟩
    refine ⟨hS', hF', hAF', hch'.trans hchB, hv'.trans rfl, ?_, ?_, ?_⟩
    · rw [hst'] at *
      omega
    · rw [hins'] at *
      omega
    · rw [hcostB, hhB] at hc'
      omega
  · -- arms B/C: `reach x ≠ 0` — the improvement test decides
    refine runs_ite_false (by rw [hcondE, if_neg hr]) ?_
    have hdistE : evalV realOps (t.charge 1) (.load "dist" (var "x"))
        = some (t.va "dist" (x : ℕ)) :=
      evalV_load_of (by rw [evalW_charge]; exact hxE)
        (by rw [show (t.charge 1).vlen "dist" = t.vlen "dist" from rfl, hAF.distL];
            exact x.isLt)
    have hcandE : evalV realOps (t.charge 1) (.var "cand") = some cand := by
      show some ((t.charge 1).v "cand") = some cand
      rw [show (t.charge 1).v "cand" = t.v "cand" from rfl]
      exact congrArg some hcandv
    set bv : ℕ := (if realOps.le (t.va "dist" (x : ℕ)) cand then 1 else 0) with hbv
    refine runs_seq (runs_vle (x := "b") hdistE hcandE
      (by show 1 < (t.charge 1).cap; rw [cap_charge]; exact hcap1) ?_)
    set tC := ((t.charge 1).setW "b" bv).charge 1 with htC
    have hbitC : tC.w "b" = if t.va "dist" (x : ℕ) ≤ cand then 1 else 0 := by
      rw [htC, w_charge, w_setW, if_pos rfl, hbv, bit_le]
    by_cases hdr : t.va "dist" (x : ℕ) ≤ cand
    · -- arm B: the test reads `dist x ≤ cand` — no write, the test discharges the edge
      have hb1 : tC.w "b" = 1 := by rw [hbitC, if_pos hdr]
      refine runs_ite_true (x := 1) (by rw [evalW_var, hb1]) (by decide) ?_
      refine runs_wset (x := "fl") (a := 0)
        (evalW_lit_of (by show 0 < (tC.charge 1).cap; rw [cap_charge]; exact hcap0)) ?_
      set tD := ((tC.charge 1).setW "fl" 0).charge 1 with htD
      have hflD : tD.w "fl" = 0 := by rw [htD, w_charge, w_setW, if_pos rfl]
      refine runs_ite_false (by rw [evalW_var, hflD]) ?_
      set tE := tD.charge 1 with htE
      refine runs_skip ?_
      set tF := tE.charge 1 with htF
      have hhF : tF.w "h" = t.w "h" := rfl
      have hiF : tF.w "ins" = t.w "ins" := rfl
      have hEk : EdgeRelaxed G t e := by
        have hc : t.va "dist" (x : ℕ) ≤ cand := hcand ▸ hdr
        have h1 : ((t.va "dist" (x : ℕ) : ℝ≥0) : ℝ≥0∞) ≤ ((cand : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast hc
        have h2 : ((cand : ℝ≥0) : ℝ≥0∞)
            = ((t.va "dist" (u : ℕ) : ℝ≥0) : ℝ≥0∞) + G.w e := by
          rw [← hcand, ENNReal.coe_add]
        refine ⟨?_, ?_⟩
        · rw [hdstv]; exact hr
        · rw [hdstv, hsrcv]
          exact h2 ▸ h1
      have hSF : SweepInv G s u tF (k + 1) :=
        (S.advance_static hEk htake).congr (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hhF hiF
      have hcostF : tF.cost = t.cost + 6 := by
        simp only [htF, htE, htD, htC, cost_charge, cost_setW]
      refine ⟨hSF, ?_, AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl,
        hchfix (fun _ => rfl) (fun _ => rfl), rfl, by omega, by omega, ?_⟩
      · exact F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) rfl rfl rfl
      · rw [hcostF]
        omega
    · -- arm C: `cand < dist x` — lower the label and push
      have hb0 : tC.w "b" = 0 := by rw [hbitC, if_neg hdr]
      refine runs_ite_false (by rw [evalW_var, hb0]) ?_
      refine runs_wset (x := "fl") (a := 1)
        (evalW_lit_of (by show 1 < (tC.charge 1).cap; rw [cap_charge]; exact hcap1)) ?_
      set tF := ((tC.charge 1).setW "fl" 1).charge 1 with htF
      have hflF : tF.w "fl" = 1 := by rw [htF, w_charge, w_setW, if_pos rfl]
      refine runs_ite_true (x := 1) (by rw [evalW_var, hflF]) (by decide) ?_
      set tG := tF.charge 1 with htG
      have hhG : tG.w "h" = t.w "h" := rfl
      have hiG : tG.w "ins" = t.w "ins" := rfl
      have hSG : SweepInv G s u tG k :=
        S.congr (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) hhG hiG
      have hvalG : HeapV (G := G) tG (tG.w "h") := by
        intro i hi
        rw [hhG] at hi
        exact hval i hi
      have hlt : cand < t.va "dist" (x : ℕ) := not_le.mp hdr
      have hdx0 : t.wa "done" (x : ℕ) = 0 := by
        by_contra hne
        have hge := cand_ge_dist_done (s := s) e hsrcv hdstv S.settled_exact S.done_u hne
        have hle' : t.va "dist" (x : ℕ) ≤ cand := by rw [← hcand]; exact hge
        exact absurd hle' hdr
      have hleG : tG.wa "reach" (x : ℕ) ≠ 0 → cand ≤ tG.va "dist" (x : ℕ) := by
        intro _
        rw [show tG.va "dist" (x : ℕ) = t.va "dist" (x : ℕ) from rfl]
        exact le_of_lt hlt
      have hchG : chainOf tG u (G.m + 1) = chainOf t u (G.m + 1) :=
        hchfix (fun _ => rfl) (fun _ => rfl)
      have hcostG : tG.cost = t.cost + 5 := by
        simp only [htG, htF, htC, cost_charge, cost_setW]
      refine (relax_take_runs (t := tG) (s := s) (u := u) (x := x) (e := e) (k := k)
        (cand := cand)
        (F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          rfl rfl rfl)
        (AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl)
        hxv hcandv hcand hvalG hbound hinsb
        hdx0 hxnot hxs hsrcv hdstv (by rw [hchG]; exact htake) hSG
        (by rw [hchG]; exact hsw) hleG).mono ?_
      rintro t' ⟨hS', hF', hAF', hch', hv', hst', hins', hc'⟩
      refine ⟨hS', hF', hAF', hch'.trans hchG, hv'.trans rfl, ?_, ?_, ?_⟩
      · rw [hst'] at *
        omega
      · rw [hins'] at *
        omega
      · rw [hcostG, hhG] at hc'
        omega

/-- `relaxBody` when the edge cannot improve anything: `x` is already reached and its label is
no worse than `cand`.  Then BOTH write arms are unreachable (`reach x = 0` contradicts the
reached hypothesis, and `cand < dist x` contradicts the label bound), so the body takes no
write at all and merely advances the sweep cursor.  This is the case of a self-loop at `u`
(`x = u`, `done u ≠ 0`) and of an edge into the source (`x = s`, `dist s = 0`). -/
theorem relaxBody_runs_static {t : State ℝ≥0} {u x : Fin G.n} {e : Fin G.m} {k : ℕ}
    {cand : ℝ≥0}
    (hF : F0 G s t) (hAF : AF G t)
    (hxv : t.w "x" = (x : ℕ))
    (hcandv : t.v "cand" = cand)
    (hcand : t.va "dist" u + G.w e = cand)
    (hreachne : t.wa "reach" (x : ℕ) ≠ 0)
    (hdistle : t.va "dist" (x : ℕ) ≤ cand)
    (hsrcv : G.src e = u) (hdstv : G.dst e = x)
    (htake : (chainOf t u (G.m + 1)).take (k + 1)
      = (chainOf t u (G.m + 1)).take k ++ [(e : ℕ)])
    (S : SweepInv G s u t k) :
    Runs realOps relaxBody t (fun t' =>
      SweepInv G s u t' (k + 1) ∧ F0 G s t' ∧ AF G t' ∧
      chainOf t' u (G.m + 1) = chainOf t u (G.m + 1) ∧
      t'.w "v" = t.w "v" ∧
      t'.w "h" ≤ t.w "h" + 1 ∧
      t'.w "ins" ≤ t.w "ins" + 1 ∧
      t'.cost ≤ t.cost + 12 * rk (t.w "h") + 25) := by
  have hcap0 : 0 < t.cap := by have := hF.hcap; omega
  have hcap1 : 1 < t.cap := by have := hF.hcap; omega
  have hxE : evalW t (var "x") = some (x : ℕ) := by
    rw [evalW_var]; exact congrArg some hxv
  have hloadR : evalW t (load "reach" (var "x")) = some (t.wa "reach" (x : ℕ)) :=
    evalW_load_of hxE (by rw [hAF.reachL]; exact x.isLt)
  have hcondE : evalW t (eq (load "reach" (var "x")) (lit 0))
      = some (if t.wa "reach" (x : ℕ) = 0 then 1 else 0) :=
    evalW_eq_of hloadR (evalW_lit_of (by show 0 < t.cap; exact hcap0))
      (by show 1 < t.cap; exact hcap1)
  have hchfix : ∀ {t' : State ℝ≥0}, (∀ w, t'.wa "head" w = t.wa "head" w) →
      (∀ j, t'.wa "nxt" j = t.wa "nxt" j) →
      chainOf t' u (G.m + 1) = chainOf t u (G.m + 1) := by
    intro t' h1 h2
    simp only [chainOf]
    rw [h1 u]
    exact chainWalk_congr (fun j _ => h2 j)
  simp only [relaxBody]
  refine runs_seq ?_
  by_cases hr : t.wa "reach" (x : ℕ) = 0
  · -- arm A is unreachable: `x` is already reached
    exact absurd hr hreachne
  · refine runs_ite_false (by rw [hcondE, if_neg hr]) ?_
    have hdistE : evalV realOps (t.charge 1) (.load "dist" (var "x"))
        = some (t.va "dist" (x : ℕ)) :=
      evalV_load_of (by rw [evalW_charge]; exact hxE)
        (by rw [show (t.charge 1).vlen "dist" = t.vlen "dist" from rfl, hAF.distL];
            exact x.isLt)
    have hcandE : evalV realOps (t.charge 1) (.var "cand") = some cand := by
      show some ((t.charge 1).v "cand") = some cand
      rw [show (t.charge 1).v "cand" = t.v "cand" from rfl]
      exact congrArg some hcandv
    set bv : ℕ := (if realOps.le (t.va "dist" (x : ℕ)) cand then 1 else 0) with hbv
    refine runs_seq (runs_vle (x := "b") hdistE hcandE
      (by show 1 < (t.charge 1).cap; rw [cap_charge]; exact hcap1) ?_)
    set tC := ((t.charge 1).setW "b" bv).charge 1 with htC
    have hbitC : tC.w "b" = if t.va "dist" (x : ℕ) ≤ cand then 1 else 0 := by
      rw [htC, w_charge, w_setW, if_pos rfl, hbv, bit_le]
    by_cases hdr : t.va "dist" (x : ℕ) ≤ cand
    · -- arm B: the improvement test reads false — take no write, the test discharges the edge
      have hb1 : tC.w "b" = 1 := by rw [hbitC, if_pos hdr]
      refine runs_ite_true (x := 1) (by rw [evalW_var, hb1]) (by decide) ?_
      refine runs_wset (x := "fl") (a := 0)
        (evalW_lit_of (by show 0 < (tC.charge 1).cap; rw [cap_charge]; exact hcap0)) ?_
      set tD := ((tC.charge 1).setW "fl" 0).charge 1 with htD
      have hflD : tD.w "fl" = 0 := by rw [htD, w_charge, w_setW, if_pos rfl]
      refine runs_ite_false (by rw [evalW_var, hflD]) ?_
      set tE := tD.charge 1 with htE
      refine runs_skip ?_
      set tF := tE.charge 1 with htF
      have hhF : tF.w "h" = t.w "h" := rfl
      have hiF : tF.w "ins" = t.w "ins" := rfl
      have hEk : EdgeRelaxed G t e := by
        have hc : t.va "dist" (x : ℕ) ≤ cand := hdr
        have h1 : ((t.va "dist" (x : ℕ) : ℝ≥0) : ℝ≥0∞) ≤ ((cand : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast hc
        have h2 : ((cand : ℝ≥0) : ℝ≥0∞)
            = ((t.va "dist" (u : ℕ) : ℝ≥0) : ℝ≥0∞) + G.w e := by
          rw [← hcand, ENNReal.coe_add]
        refine ⟨?_, ?_⟩
        · rw [hdstv]; exact hr
        · rw [hdstv, hsrcv]
          exact h2 ▸ h1
      have hSF : SweepInv G s u tF (k + 1) :=
        (S.advance_static hEk htake).congr (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hhF hiF
      have hcostF : tF.cost = t.cost + 6 := by
        simp only [htF, htE, htD, htC, cost_charge, cost_setW]
      refine ⟨hSF, ?_, AF.preserve hAF rfl rfl rfl rfl rfl rfl rfl,
        hchfix (fun _ => rfl) (fun _ => rfl), rfl, by omega, by omega, ?_⟩
      · exact F0.preserve hF rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) rfl rfl rfl
      · rw [hcostF]
        omega
    · -- arm C is unreachable: `cand < dist x` contradicts the label bound
      exact absurd hdistle hdr

end Submission.DijkstraHeap
