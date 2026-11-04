import Frontier.RAMWitness
import Submission.DijkstraModel

/-!
# Submission.DijkstraDecode — state decodes and `head`/`nxt` chain walks

Decoding layers between the RAM state and `Submission.DijkstraModel.Inv`:
* `hvD`/`hdD` — heap arrays decoded as model entry functions (the `Fin` wrapper
  defaults to `s` out of range; `hvD_congr` reduces permutation questions to
  `wa` equalities);
* `chainWalk`/`chainOf` — the `e + 1`-encoded `head`/`nxt` adjacency lists;
* `outChainK` — the expected chain after `k` build steps (decreasing order);
* walk-stability and chain algebra lemmas for `buildAdj` and the scan.
-/

namespace Submission.DijkstraDecode

open Frontier Frontier.RAM NNReal ENNReal

variable {G : Graph} {s : Fin G.n}

/-! ## Heap decodes -/

/-- Vertex at heap position `i` (defaults to `s` out of range). -/
def hvD (s : Fin G.n) (st : State ℝ≥0) (i : ℕ) : Fin G.n :=
  if h : st.wa "hv" i < G.n then ⟨st.wa "hv" i, h⟩ else s

/-- Key at heap position `i`. -/
def hdD (st : State ℝ≥0) (i : ℕ) : ℝ≥0 := st.va "hd" i

theorem hvD_congr {st st' : State ℝ≥0} (h : ∀ i, st'.wa "hv" i = st.wa "hv" i) (i : ℕ) :
    hvD (G := G) s st' i = hvD s st i := by
  simp only [hvD, h i]

theorem hvD_lt (st : State ℝ≥0) {i : ℕ} (hi : st.wa "hv" i < G.n) :
    hvD (G := G) s st i = ⟨st.wa "hv" i, hi⟩ := by
  simp only [hvD, dif_pos hi]

theorem hvD_wa {st : State ℝ≥0} {i : ℕ} (hi : st.wa "hv" i < G.n) :
    (hvD (G := G) s st i : ℕ) = st.wa "hv" i := by
  simp only [hvD_lt st hi, Fin.val_mk]

/-! ## Chain walks -/

/-- Follow an `e + 1` pointer chain through `nxt` for `k` steps, decoding edge indices. -/
def chainWalk (st : State ℝ≥0) (q : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => if q = 0 then [] else (q - 1) :: chainWalk st (st.wa "nxt" (q - 1)) k

theorem chainWalk_zero (st : State ℝ≥0) (q : ℕ) : chainWalk st q 0 = [] := rfl

theorem chainWalk_succ (st : State ℝ≥0) (q k : ℕ) :
    chainWalk st q (k + 1) =
      if q = 0 then [] else (q - 1) :: chainWalk st (st.wa "nxt" (q - 1)) k :=
  rfl

/-- The out-edge list of `u` decoded from `head`/`nxt`; supply `fuel = G.m + 1`. -/
def chainOf (st : State ℝ≥0) (u : ℕ) : ℕ → List ℕ := chainWalk st (st.wa "head" u)

/-- Source of edge `e`, totalised to `0` out of range. -/
def srcN (G : Graph) (e : ℕ) : ℕ := if h : e < G.m then (G.src ⟨e, h⟩ : ℕ) else 0

/-- The expected chain of `u` after `k` build steps: out-edges `< k`, decreasing. -/
def outChainK (G : Graph) (k u : ℕ) : List ℕ :=
  ((List.range k).filter (fun e => decide (srcN G e = u))).reverse

theorem outChainK_zero (u : ℕ) : outChainK G 0 u = [] := by
  simp [outChainK]

/-- Prepending the current edge `k` (with `srcN G k = u`) extends the expected chain of `u`. -/
theorem outChainK_succ_same {k u : ℕ} (h : srcN G k = u) :
    outChainK G (k + 1) u = k :: outChainK G k u := by
  simp only [outChainK]
  rw [List.range_succ, List.filter_append]
  simp [h, List.reverse_append]

/-- A different source leaves the expected chain unchanged. -/
theorem outChainK_succ_ne {k u : ℕ} (h : srcN G k ≠ u) :
    outChainK G (k + 1) u = outChainK G k u := by
  simp only [outChainK]
  rw [List.range_succ, List.filter_append]
  simp [h]

theorem outChainK_lt (k u : ℕ) : ∀ e ∈ outChainK G k u, e < k := by
  intro e he
  simp only [outChainK, List.mem_reverse, List.mem_filter, List.mem_range] at he
  omega

theorem outChainK_src (k u : ℕ) : ∀ e ∈ outChainK G k u, srcN G e = u := by
  intro e he
  simp only [outChainK, List.mem_reverse, List.mem_filter, List.mem_range] at he
  exact of_decide_eq_true he.2

theorem outChainK_length_le (k u : ℕ) : (outChainK G k u).length ≤ k := by
  simp only [outChainK, List.length_reverse]
  exact (List.length_filter_le _ _).trans (by simp)

theorem outChainK_nodup (k u : ℕ) : (outChainK G k u).Nodup := by
  simp only [outChainK, List.nodup_reverse]
  exact (List.nodup_range).filter _

/-! ## Walk stability -/

/-- A chain walk that never visits an edge whose `nxt` changed is unaffected. -/
theorem chainWalk_congr_aux (st st' : State ℝ≥0) (k : ℕ) :
    ∀ q, (∀ j ∈ chainWalk st q k, st'.wa "nxt" j = st.wa "nxt" j) →
      chainWalk st' q k = chainWalk st q k := by
  induction k with
  | zero => intro q _; rfl
  | succ k ih =>
    intro q h
    simp only [chainWalk_succ]
    by_cases hq : q = 0
    · simp [hq]
    · rw [if_neg hq, if_neg hq]
      have hhead : st'.wa "nxt" (q - 1) = st.wa "nxt" (q - 1) :=
        h (q - 1) (by simp [chainWalk_succ, hq])
      have htail : ∀ j ∈ chainWalk st (st.wa "nxt" (q - 1)) k,
          st'.wa "nxt" j = st.wa "nxt" j := by
        intro j hj
        exact h j (by simp [chainWalk_succ, hq, hj])
      rw [hhead]
      rw [ih _ htail]

theorem chainWalk_congr {st st' : State ℝ≥0} {q k : ℕ}
    (h : ∀ j ∈ chainWalk st q k, st'.wa "nxt" j = st.wa "nxt" j) :
    chainWalk st' q k = chainWalk st q k :=
  chainWalk_congr_aux st st' k q h

/-- All edges of a well-formed chain lie below `k`, so `nxt` updates at `≥ k` cannot affect
its walk. -/
theorem chainWalk_stable_of_mem {st st' : State ℝ≥0} {q k : ℕ}
    (hmem : ∀ j ∈ chainWalk st q (G.m + 1), j < k)
    (hag : ∀ j < k, st'.wa "nxt" j = st.wa "nxt" j) :
    chainWalk st' q (G.m + 1) = chainWalk st q (G.m + 1) :=
  chainWalk_congr (fun j hj => hag j (hmem j hj))

/-! ## Fuel -/

/-- A chain walk is the prefix of any longer-fuel walk. -/
theorem chainWalk_take (st : State ℝ≥0) (k : ℕ) :
    ∀ q j, chainWalk st q k = (chainWalk st q (k + j)).take k := by
  induction k with
  | zero => intro q j; rfl
  | succ k ih =>
    intro q j
    have hre : (k + 1) + j = (k + j) + 1 := by omega
    rw [hre]
    by_cases hq : q = 0
    · simp [hq, chainWalk_succ]
    · rw [chainWalk_succ, chainWalk_succ, if_neg hq, if_neg hq]
      simp
      rw [ih (st.wa "nxt" (q - 1)) j]

/-- A chain walk visits at most `n` edges with fuel `n`. -/
theorem chainWalk_length_le (st : State ℝ≥0) (q n : ℕ) : (chainWalk st q n).length ≤ n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [chainWalk_succ]
    by_cases hq : q = 0
    · simp [hq]
    · rw [if_neg hq]
      simpa using ih (st.wa "nxt" (q - 1))

/-- If the long walk fits in the short fuel, the two walks agree (no truncation). -/
theorem chainWalk_fuel_stable {st : State ℝ≥0} {q a b : ℕ} (hab : a ≤ b)
    (hlen : (chainWalk st q b).length ≤ a) : chainWalk st q a = chainWalk st q b := by
  have h := chainWalk_take st a q (b - a)
  have hba : a + (b - a) = b := by omega
  rw [hba] at h
  rw [h]
  exact List.take_of_length_le hlen

end Submission.DijkstraDecode
