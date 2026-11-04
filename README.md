# directed-sssp row: n log n ; n log^2 n (binary-heap Dijkstra)

Lean submission for the Big O Speedrun directed shortest paths race
(https://bigospeedrun.com/directed-sssp), staged B1 of R2125608239.

Row: D(n) = n · ⌊log₂ n⌋ (a=1, b=1), T(n) = n · (ln n)² (a'=1, b'=2, c'=0).
Bound field: `n log ; n log^2`.

Program: `ite (m/n ≤ ⌊log₂ n⌋) Dijkstra Bellman-Ford` in the Frontier word RAM
(wordExp = 0). The Dijkstra branch is a lazy binary-heap Dijkstra over adjacency
lists (head/nxt, e+1 encoding) with true min-extraction; the fallback branch is
the fork's verified `bfProgram` (Frontier.RAMWitness, cost ≤ 9(n+1)(m+1)),
transported via `InputFrame` / `prog_runs_gen` (designed for dispatch splicing).

Pins: leanprover/lean4:v4.34.1, Mathlib d13f23b, Frontier = bigospeedrun/c-hd-proof
@ 98c53acc formal/lean (autoImplicit=true for Frontier root only; submission
autoImplicit=false), lake-manifest byte-exact from profiles/lake-manifest.json.
