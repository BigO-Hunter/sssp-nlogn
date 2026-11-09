# B2 handoff — the board-work entry point (FT filing prep)

Owner state: branch `wip-consolidation-measure` @ `661ea7b` **pushed** to
`origin` (darkhipo/sssp-nlogn); row file assembled (`ROW_STATEMENT.md`,
same commit); full build green at the tip (`m22_final.log`: 0 errors, one
linter warning); no `sorry` in `Submission/`.  What follows is what the
row proves, what it names as premise/seam, and the exact board-facing
shape for an `n log ; n log` sssp row, read off the board's own
conventions.

## What the row proves

`row_nlog` (`Submission/FibHeapRow.lean:255`): `m` decrease-keys under the
clearing discipline plus one extract-min with its consolidation walk
raise the machine potential by at most `m·5 + (2·rankCap st.n + 2)`,
`rankCap n = 2·⌊log₂ n⌋ + 1` — i.e. the decrease-key half is **constant
per op** and both extract walk terms sit at the **log-class cap**.  This
is the amortized core of FT-1987's `O(m + n log n)`: the potential
ledger that makes a Fibonacci-heap Dijkstra run in `n log n` at
`m ≤ n log n`.  The scaled sibling `row_decreaseKeyClear_scaled` carries
the same half in the machine's `D0 + 6K + D1` per-op units.

## What it names as premise / seam

1. **`hmono` / `deg_lt_of_kids` (wound 2125609385)** — the walk recount's
   degree-strictness enters `row_nlog` as an explicit hypothesis.  Until
   the lemma lands (a machine `InvOK` carry from the link-time
   discipline), the row composes with the seam stated, not discharged.
   Full verbatim text: `ROW_STATEMENT.md`, Residual 1.
2. **The CLRS/transfer seam** — the row's decrease-key half is the
   clearing discipline; the transfer run (`DkRun`, `count·(st.n + 5)`)
   and its `CascadeMarks` ledger remain the stated accounting boundary.
   The honest-6K note (the `D0+3K+D1` gap in the fresh-parent run model)
   is attached verbatim in `ROW_STATEMENT.md`, Residual 2.
3. **The extract-state bundle** — NOT a seam: discharged fully internally
   by the `extract_*` preservation suite + `extract_PosOK` (commit
   `661ea7b`).

## The board-facing statement shape (`n log ; n log`)

Read off bigospeedrun.com/directed-sssp and the lane's own statement
file (`Submission/SsspStatement.lean`, byte-exact from the board's
profiles; the board rebuilds the proof from source and kernel-checks the
exact statement):

- **Lean statement.** `BigOSpeedrun.DirectedSSSP.Bound 1 1 1 1 0` — one
  uniform program `P`, exact on every graph; at `m ≤ n·⌊⌊log₂ n⌋⌋`
  (`Cap 1 1`), `n ≥ 16`, it runs within `C · n · (ln n)^1 · (ln ln n)^0`;
  polynomial fallback `C·(n+1)(m+1)` on every graph.  (B1 #158 was
  `Bound 1 1 1 2 0` via `DijkstraRow.dijkstra_bound`; B2 swaps the time
  rationals to `1 1 0` and the proof to the FT row.)
- **Issue form** (exact, per the board's #158/#147 filings — four H3
  fields, nothing else in the body):
  - Title: `[Lean submission] darkhipo: directed-sssp n log ; n log`
  - `### Problem` → `directed-sssp`
  - `### Repository URL` → `https://github.com/darkhipo/sssp-nlogn`
  - `### Commit SHA` → the full sha of the filing commit
  - `### Bound` → `n log ; n log`
- **Board effect.** FT-1987 `O(n log n)` at `m ≤ n log n` is currently
  **Claimed** (citation only, doi 10.1145/28869.28874).  darkhipo holds
  Lean Verified at `n log^2` (issue #158).  This row would replace the
  Claimed classical row with a Lean Verified `n log` — the first Lean
  verification at the classical bound.

## Distance from row to `Race.bound` (the honest gap)

The row is potential-level accounting, not yet the program-level
`Bound`.  Remaining, in order:

1. `deg_lt_of_kids` (wound 2125609385) — **partially closed 2026-11-09**:
   the carry landed as the named machine clause `DegOK`
   (`FibHeapRefine`) — the link-time discipline's static form, honestly
   documented as a modeled constraint (pointwise strictness is not a
   reachable-state theorem; the two-loss cascade is the counterexample,
   stated in the docstring).  What is proved: `link_DegOK` (the clause is
   inductive at the equal-degree link), `extract_DegOK` (unconditional —
   the extract splice deletes edges only), and `row_nlog` now consumes
   `hdeg : DegOK s.last` with the extract-state strictness derived
   internally.  The anonymous per-call `hmono` over the extract state is
   gone; the clause sits where the row's other bundle pieces sit.
2. **The def-swap session** — **LANDED 2026-11-09**: the clearing writes
   ARE the machine's canonical `promoteState` (`FibHeapPromote:1297`);
   the transfer splice survives as `transferPromoteState` with its
   `transfer_*` suite (the `DkRun` / `cascadeRun` / `decreaseKeyPath`
   aggregates run on it), so the CLRS/transfer seam stays dual-track
   exactly as the row states it.  The mark anchors re-keyed with the
   splice: `machineMarks_promoteState_intermediate` / `_terminal`
   (−2/−1, the clearing consumption) vs
   `machineMarks_transferPromoteState` (the net-zero move).  Not a bound
   risk (both units are constant-per-op); the honesty seam for the
   literal CLRS charge remains the stated boundary.
3. **The transport** — wire the Fib-heap Dijkstra into Frontier's word
   RAM (`Frontier.CostModel`), charge the potential deltas as time, and
   prove the program-level `CorrectWithin` + fallback.  Then
   `Submission.lean`: `theorem Race.bound := BigOSpeedrun.DirectedSSSP
   …Bound 1 1 1 1 0` with the FT row as the proof.

   **Scope (2026-11-09, the STEP 3 scoping pass).**  The B1 pattern
   (`DijkstraRow.lean:200-335`) is the template: program run theorems
   (`prog_runs_dij`/`prog_runs_bf` — a RAM program `p1` with
   `r.Solves` + cost bound) wrapped by clause1/clause2 arithmetic into
   `Bound 1 1 1 2 0`.  The FT transport re-runs that shape at
   `Bound 1 1 1 1 0` with a Fib-heap program `p2`.  Pieces, in build
   order: (a) **the machine consolidation fold** — `extractState` only
   splices; the equal-degree meld (`extractRun` over `mergeState` cells,
   ExtractMin header's "next module") is NOT yet machine-landed and is
   the biggest single build (the linking loop, its `InvOK`-analog
   preservation, the distinct-degrees table discipline);
   **(a) LANDED 2026-11-09, the `DegOK` discipline leg (STEP 4):**
   `merge_DegOK` (`FibHeapMerge` — the clause survives the meld *at
   equal degree*; `MergePre`'s bare inequality provably cannot carry
   it), the deg-aware cell premise `ExtractOkDeg` (`MergePre` +
   `st.deg c = st.deg p` per cell) with projection
   `extractOkDeg_imp_ok`, the fold climb `extractRun_DegOK`, and the
   bridge `extractMin_DegOK` (splice leg `extract_DegOK` + fold leg).
   Honest seam, unchanged in kind: the equal-degree cell premise is
   caller discipline — the distinct-degrees table that *generates*
   well-formed chains is still to land, and `DegOK` at the program
   level remains the named clause (wound 2125609385); the fold does not
   discharge the seam, it moves the clause across the one genuinely
   inductive transition.  Still open in (a): the table discipline;
   (b) **the sim**
   — RAM program ⟹ `HState` step sequence (the `DijkstraSim` pattern
   extended with heap-op witnesses: each decrease-key must EVIDENCE its
   `DkRunClear` premises — `hyn/hy0/hm/hcc/hlen` per step); (c) **the
   charge** — per-op RAM cost constants (cut/promote/link O(1)-splices,
   extract O(deg r) + the walk), with the potential ledger (`row_nlog`'s
   `m·5 + 2·rankCap + 2`, scaled lane `D0+6K+D1`) as the amortized
   certificate — charge the deltas as time; (d) **the arithmetic** —
   `Time 1 1 0 = n·log n` at `m ≤ n·⌊log₂ n⌋` + the `2000·(n+1)(m+1)`
   fallback: B1's `log_ge`/`cap_one_one`/`sparse_one_one`/`arith_clause*`
   scaffolding re-runs with FT constants.  Risks named: the roots list
   as a RAM array (B1's `p1` is array-native; `roots : List ℕ` needs the
   array encoding), the consolidation fold's witness generation, and the
   verifier's pinned Frontier commit (no Frontier edits — the B1
   transport proves the shape suffices).

## Gating before any filing (B2 task 2125608602)

Zero `sorry`; root `Race.bound`; axioms exactly
`[propext, Classical.choice, Quot.sound]` (`VerifierAudit.lean` probe);
statement byte-exact; root `Submission.lean` + 6-check; **do not file
publicly until the parent reviews a green artifact.**

## Owner's calls pending

- When to run the def-swap session.
- The board-row filing decision (only after items 1–3 close and the
  gating passes — the board checks the program-level statement, so the
  row alone does not file).
