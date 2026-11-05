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

end Submission.DijkstraRow
