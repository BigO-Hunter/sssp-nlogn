import Submission.DijkstraMain

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

end Submission.DijkstraRow
