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
  soft : SoftInv s (fun v => st.va "dist" v) (fun v => st.wa "reach" v)
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
  have hsoft : SoftInv s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v)
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
  refine ⟨hsoft, hhole, ?_, ?_, ?_, (by rw [hh]; exact K.origOK), (by rw [hh]; exact K.leaf0)⟩
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

end Submission.DijkstraHeap
