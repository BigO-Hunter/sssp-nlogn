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

---

## Why this repo is up

Reproducible verified bounds: the n log n ; n log² n row (binary-heap Dijkstra + verified Bellman-Ford dispatch over the pinned Frontier) — staged evidence for the board row.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Staged B1 (R2125608239). Open work: filing-day re-verification against the pinned Frontier commit; independent rebuilds.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard. 
