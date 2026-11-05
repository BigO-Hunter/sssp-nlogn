import Submission.DijkstraMain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Submission.DijkstraRow — the `n·log n ; n·log²n` row

The dispatch wrapper `prog = seq calcPa (ite (pa < m/n) BF.prog dijkstraBody)` with
`pa = ⌊log₂ n⌋`:

* on a graph with `m ≤ n·⌊log₂ n⌋` the test is false (`m/n ≤ pa`), so the run takes the
  binary-heap Dijkstra branch, which is exact and costs
  `4·⌊log₂ n⌋ + 6 + 1 + (4n + 3m + 9) + (6m + 2) + 4 + 13 + Kc·(2m+3) + 1`;
* on any graph the run is exact, and either branch costs `≤ 1200·(n+1)(m+1)`
  (Bellman–Ford when the test fires, Dijkstra otherwise).

The row is `Bound 1 1 1 2 0`: density `D(n) = n·⌊log₂ n⌋`, time `T(n) = n·(log n)²`.
-/

namespace Submission.DijkstraRow

open Frontier Frontier.RAM WExpr Stmt NNReal ENNReal
open Submission.DijkstraProg Submission.DijkstraModel Submission.DijkstraDecode
open Submission.DijkstraSim Submission.DijkstraHeap Submission.DijkstraMain

variable {G : Graph} {s : Fin G.n}

/-- The Dijkstra branch, started from the dispatch's charged state, is exact and costs at most
`1 + BODY` on top of the entry cost. -/
theorem dijkstra_branch_from (st : State ℝ≥0) (hF : F0 G s st) :
    Runs realOps dijkstraBody (st.charge 1) (fun r => r.Solves G s ∧
      r.cost ≤ st.cost + 1 + (4 * G.n + 3 * G.m + 9) + (6 * G.m + 2) + 4
        + (12 * rk 0 + 13) + (Kc G * (2 * G.m + 3) + 1)) := by
  refine (dijkstraBody_solves (G := G) (s := s) (st := st.charge 1) (hF.charge 1)).mono ?_
  rintro r ⟨hsv, hc⟩
  exact ⟨hsv, hc⟩

/-- Bellman–Ford, started from the dispatch's charged state. -/
theorem bf_branch_from (st : State ℝ≥0) (hF : F0 G s st) :
    Runs realOps Frontier.RAM.BF.prog (st.charge 1) (fun r => r.Solves G s ∧
      r.cost ≤ st.cost + 1 + 2 * G.n + 4 + (9 * G.m + 4) * G.n + 1) := by
  have h0 : Frontier.RAM.BF.InputFrame G s (st.charge 1) :=
    ⟨hF.hn, hF.hm, hF.hs, hF.hcap, hF.hsrc, hF.hdst, hF.hw, hF.hsrcL, hF.hdstL, hF.hwL⟩
  refine (Frontier.RAM.BF.prog_runs_gen (G := G) s (st.charge 1) h0).mono ?_
  rintro r ⟨hFr, hlab, hc⟩
  refine ⟨⟨hFr.hreachL, hFr.hdistL, fun v => ?_⟩, hc⟩
  calc r.label v = Frontier.RAM.BF.lab G r v := rfl
    _ = Frontier.RAM.BF.rounds G s G.n v := congrFun hlab v
    _ = G.dist s v := Frontier.RAM.BF.rounds_n_eq_dist s v

/-- The dispatch test evaluated at the post-`calcPa` state. -/
theorem test_eval {st1 : State ℝ≥0} (hF1 : F0 G s st1) (hpa1 : st1.w "pa" = Nat.log 2 G.n) :
    evalW st1 (lt (var "pa") (div (var "m") (var "n")))
      = some (if Nat.log 2 G.n < G.m / G.n then 1 else 0) := by
  have hcap1 : 1 < st1.cap := by have := hF1.hcap; omega
  have hpaE : evalW st1 (var "pa") = some (Nat.log 2 G.n) := by rw [evalW_var, hpa1]
  have hmE : evalW st1 (var "m") = some G.m := by rw [evalW_var, hF1.hm]
  have hnE : evalW st1 (var "n") = some G.n := by rw [evalW_var, hF1.hn]
  have hnne : G.n ≠ 0 := by have := s.isLt; omega
  have hdivE : evalW st1 (div (var "m") (var "n")) = some (G.m / G.n) :=
    evalW_div_of hmE hnE hnne
  exact evalW_lt_of hpaE hdivE hcap1

/-- `calcPa` then the dispatch test, in one step: the branch bodies both start at the state
`st1.charge 1`. -/
theorem prog_runs_dij (hdiv : G.m / G.n ≤ Nat.log 2 G.n) :
    Runs realOps prog (initState p1 G s) (fun r => r.Solves G s ∧
      r.cost ≤ 4 * Nat.log 2 G.n + 6 + 1 + (4 * G.n + 3 * G.m + 9) + (6 * G.m + 2) + 4
        + (12 * rk 0 + 13) + (Kc G * (2 * G.m + 3) + 1)) := by
  refine runs_seq ((calcPa_runs (G := G) (s := s) (initState p1 G s)
    (F0.init_state (G := G) p1 s)).mono ?_)
  rintro st1 ⟨hF1, hpa1, hc1⟩
  have htest : evalW st1 (lt (var "pa") (div (var "m") (var "n"))) = some 0 := by
    rw [test_eval hF1 hpa1, if_neg (by omega)]
  refine runs_ite_false (a := Frontier.RAM.BF.prog) htest ?_
  refine (dijkstra_branch_from (G := G) (s := s) (st := st1) hF1).mono ?_
  rintro r ⟨hsv, hc⟩
  have hinit : (initState p1 G s).cost = 0 := rfl
  exact ⟨hsv, by omega⟩

/-- The same run on the Bellman–Ford side of the dispatch. -/
theorem prog_runs_bf (hdiv : Nat.log 2 G.n < G.m / G.n) :
    Runs realOps prog (initState p1 G s) (fun r => r.Solves G s ∧
      r.cost ≤ 4 * Nat.log 2 G.n + 6 + 1 + 2 * G.n + 4 + (9 * G.m + 4) * G.n + 1) := by
  refine runs_seq ((calcPa_runs (G := G) (s := s) (initState p1 G s)
    (F0.init_state (G := G) p1 s)).mono ?_)
  rintro st1 ⟨hF1, hpa1, hc1⟩
  have htest : evalW st1 (lt (var "pa") (div (var "m") (var "n"))) = some 1 := by
    rw [test_eval hF1 hpa1, if_pos hdiv]
  refine runs_ite_true (b := dijkstraBody) htest (by decide) ?_
  refine (bf_branch_from (G := G) (s := s) (st := st1) hF1).mono ?_
  rintro r ⟨hsv, hc⟩
  have hinit : (initState p1 G s).cost = 0 := rfl
  exact ⟨hsv, by omega⟩

/-! ## The two logarithm caps -/

variable {L : ℕ}

/-- `L + 1 ≤ 2^(L+1)`. -/
theorem le_two_pow (L : ℕ) : L + 1 ≤ 2 ^ (L + 1) := by
  induction L with
  | zero => norm_num
  | succ k ih =>
    have h2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    omega

/-- `3 * n * (L+1) < 2^(2L+4)` for `n < 2^(L+1)`. -/
theorem three_mul_lt_pow (hn : G.n < 2 ^ (L + 1)) : 3 * G.n * (L + 1) < 2 ^ (2 * L + 4) := by
  have hx : G.n * (L + 1) ≤ 2 ^ (L + 1) * 2 ^ (L + 1) :=
    Nat.mul_le_mul (Nat.le_of_lt hn) (le_two_pow L)
  have h3 : 3 * (G.n * (L + 1)) ≤ 3 * (2 ^ (L + 1) * 2 ^ (L + 1)) :=
    Nat.mul_le_mul_left 3 hx
  have hpos : 0 < 2 ^ (L + 1) * 2 ^ (L + 1) := by positivity
  have h4 : 3 * (2 ^ (L + 1) * 2 ^ (L + 1)) < 4 * (2 ^ (L + 1) * 2 ^ (L + 1)) := by
    nlinarith
  have h5 : 4 * (2 ^ (L + 1) * 2 ^ (L + 1)) = 2 ^ (2 * L + 4) := by
    have hp : 2 ^ (L + 1) * 2 ^ (L + 1) = 2 ^ (2 * L + 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  calc 3 * G.n * (L + 1) = 3 * (G.n * (L + 1)) := by ring
    _ ≤ 3 * (2 ^ (L + 1) * 2 ^ (L + 1)) := h3
    _ < 4 * (2 ^ (L + 1) * 2 ^ (L + 1)) := h4
    _ = 2 ^ (2 * L + 4) := h5

/-- The Nat log cap: `log₂(m+2) ≤ 2·log₂n + 3` when `m + 2 ≤ 3n(⌊log₂n⌋+1)`. -/
theorem log_m_add_two (h : G.m + 2 ≤ 3 * G.n * (Nat.log 2 G.n + 1)) :
    Nat.log 2 (G.m + 2) ≤ 2 * Nat.log 2 G.n + 3 := by
  have hnlt : G.n < 2 ^ (Nat.log 2 G.n + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) G.n
    simpa [Nat.succ_eq_add_one] using this
  have hlt := lt_of_le_of_lt h (three_mul_lt_pow (G := G) (L := Nat.log 2 G.n) hnlt)
  have hpos : G.m + 2 ≠ 0 := by omega
  have := Nat.log_lt_of_lt_pow (b := 2) (x := 2 * Nat.log 2 G.n + 4) hpos hlt
  omega

/-- `Kc G ≤ 60·⌊log₂ n⌋ + 123` on the dispatch's Dijkstra side. -/
theorem Kc_le (h : G.m + 2 ≤ 3 * G.n * (Nat.log 2 G.n + 1)) :
    Kc G ≤ 60 * Nat.log 2 G.n + 123 := by
  have h3 : Nat.log 2 (G.m + 2) ≤ 2 * Nat.log 2 G.n + 3 := log_m_add_two (G := G) h
  have h2 : Nat.log 2 (G.m + 1) ≤ 2 * Nat.log 2 G.n + 3 :=
    le_trans (Nat.log_mono_right (by omega)) h3
  have h4 : rkD (G.m + 1) 0 = Nat.log 2 (G.m + 1) := rkD_zero _
  have h5 : rk (G.m + 1) = Nat.log 2 (G.m + 2) := rfl
  simp only [Kc, h4, h5]
  omega

/-- The real log cap: `⌊log₂ n⌋ ≤ log n / log 2`. -/
theorem L_le_log_div (hn : 0 < G.n) :
    ((Nat.log 2 G.n : ℕ) : ℝ) ≤ Real.log (G.n : ℝ) / Real.log 2 := by
  have h1 : (2 : ℝ) ^ (Nat.log 2 G.n : ℕ) ≤ (G.n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : Real.log ((2 : ℝ) ^ (Nat.log 2 G.n)) ≤ Real.log (G.n : ℝ) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  linarith

/-- `⌊log₂ n⌋ ≤ 1.5·log n`. -/
theorem L_le_one_five (hn : 16 ≤ G.n) :
    ((Nat.log 2 G.n : ℕ) : ℝ) ≤ 1.5 * Real.log (G.n : ℝ) := by
  have h := L_le_log_div (G := G) (by omega)
  have hlog2 : (0.693 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog : (0 : ℝ) < Real.log (G.n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < G.n by omega))
  rw [le_div_iff₀ (by linarith : (0:ℝ) < Real.log 2)] at h
  nlinarith [h, hlog2, hlog]

end Submission.DijkstraRow
