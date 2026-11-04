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
    (K : SiftUpOK s st origHv origHd x xk ii₀ ii)
    (hiiE : st.w "ii" = ii) (hbound : st.w "h" ≤ G.m + 1) :
    Runs realOps siftUp st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      Inv G s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      st'.cost ≤ st.cost + 12 * rk ii + 1) := by
  have hnpos : 0 < G.n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hcap0 : 2 < st.cap := by have := hF.hcap; omega
  refine runs_while_nat (I := fun q st' => ∃ ii', SiftUpOK s st' origHv origHd x xk ii₀ ii' ∧
      F0 G s st' ∧ AF G st' ∧ st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      q ≤ rk ii ∧
      ((st'.w "ii" = ii' ∧ 0 < ii' ∧ q = rk ii') ∨
       (st'.w "ii" = 0 ∧ q = 0 ∧ (ii' = 0 ∨ st'.va "hd" (par ii') ≤ st'.va "hd" ii'))) ∧
      st'.cost ≤ st.cost + 12 * (rk ii - q))
    (Q := fun st' => F0 G s st' ∧ AF G st' ∧
      Inv G s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = st.w "h" ∧ st'.w "ins" = st.w "ins" ∧
      st'.cost ≤ st.cost + 12 * rk ii + 1) ?_ (rk ii) st ⟨ii, K, hF, hAF, rfl, rfl, le_rfl, ?_, ?_⟩
  · -- hstep
    intro q s' ⟨ii', K', hF', hAF', hh', hins', hle, hmode, hcost⟩
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
        · refine ⟨F0.charge hF' 1, AF.charge hAF' 1, ?_, ?_, ?_, ?_⟩
          · have hedge : ¬(par ii' < s'.w "h" ∧ ii' < s'.w "h" ∧
                (ii' = 2 * par ii' + 1 ∨ ii' = 2 * par ii' + 2)) ∨
                s'.va "hd" (par ii') ≤ s'.va "hd" ii' := by
              rcases h2.2.2 with hz | hle
              · left; simp [par, hz]
              · exact Or.inr hle
            exact K'.soft.toInv (HeapOKExcept.toHeapOK K'.ok hedge)
          · rw [show (s'.charge 1).w "h" = s'.w "h" from rfl, hh']
          · rw [show (s'.charge 1).w "ins" = s'.w "ins" from rfl, hins']
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
            have hn' : rk (par ii') < q := by
              rw [h1.2.2]
              by_cases hz : par ii' = 0
              · rw [hz, rk_zero]; exact rk_pos hpos
              · have hpar := rk_par hpos
                have hpp := rk_pos hpos
                omega
            refine ⟨rk (par ii'), hn', par ii', hK10, hF10, hAF10, hh', hins', ?_, ?_, ?_⟩
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
            have hle2 : s'.va "hd" (par ii') ≤ s'.va "hd" ii' := by
              have hlt : s'.va "hd" (par ii') < xk := lt_of_not_ge hsw
              rw [K'.hole.2]
              exact le_of_lt hlt
            refine ⟨0, by rw [h1.2.2]; exact rk_pos hpos, ii', hK2, hF2, hAF2, hh', hins',
              ?_, ?_, ?_⟩
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

end Submission.DijkstraHeap
