import Submission.SsspStatement
import Submission.DijkstraRow

/-!
The `n·log n ; n·log² n` row for the Big O Speedrun directed shortest paths race: one uniform
program (dispatching on `m/n` against `⌊log₂ n⌋`: the fork's verified Bellman–Ford on dense
graphs, a binary-heap Dijkstra on sparse ones) is exact on every graph, runs within
`C·n·(log n)²` at `m ≤ n·⌊log₂ n⌋` for `n ≥ 16`, and within `C·(n+1)(m+1)` on every graph.
-/

theorem Race.bound :
    BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((1 : ℚ) / 1) ((1 : ℚ) / 1) ((2 : ℚ) / 1)
      ((0 : ℚ) / 1) :=
  Submission.DijkstraRow.dijkstra_bound
