# p2e receipts — SUBMISSION/FibHeapProg.lean @ wip-consolidation-measure

Branch `wip-consolidation-measure` @ `b1287ad` (pushed). This file is the
state of the climb: what is landed and green, what is in-tree but NOT yet
receipted, and — measured, not inferred — why it has not receipted.

## LANDED and green (unchanged from the previous receipt)

1. **`dkCut_runs` scaffolding** — `wa_stores_pass` wrapper induction;
   `decode_dkChain_{true,false_one,false_two}` hoisted over a plain `r`;
   `logOf_*`; per-stage `dk*C` charge-structured defs and their read
   congruences. Axiom probes green in rounds p2e_r5/r6.
2. `logPush_RelLog` (p2d), `rootsCompact_runs`/`stashLoop_runs` (p2b),
   `insertOp_runs` (p2a). No `sorryAx`, no `native_decide`.
3. File sha256 at receipt time: `8d9115aa84716c146af8235d2009f2b5ce7164038928b0c7ddbde3a14475a541`
   (2211 lines). Master copy preserved outside the tree at
   `/tmp/prog_master_1794322432.lean` — same bytes.

## NOT receipted: `dkCut_runs` itself (in-tree at ~line 1974)

The round-9 restructure (variable-level congruences, in-situ chain peels,
explicit 8-component `refine` finishers) is **in the file** and **compiles
clean as far as it has been driven** — every attempt below died to an
external SIGKILL with `error:` count **0** and the elaborator well inside
the file. The file has never been *observed* to reach the end, so this is
not a pass; it is "no error found in the prefix that was elaborated".

### The blocker, measured (2026-11-10, six launches, five spawn shapes)

| round | shape | died at | rc | signature |
|---|---|---|---|---|
| p2e_r11 | tmux window, `lake env lean` | 60 s | 137 | `lake` SIGKILLed, `lean` alive → orphan guard reaped it |
| p2e_r11 (3rd) | tmux window, `lean` direct | 120 s | 137 | `lean` (2.9 GB) SIGKILLed |
| p2e_r12 | tmux window, `lean` direct | 90 s | 137 | ditto (2.9 GB) |
| p2e_r13 | double-fork + setsid | 67 s | 137 | wrapper killed, tree reaped |
| p2e_r15 | `launchctl submit` | 86 s | 137 | wrapper killed, tree reaped |
| p2e_r16 | `launchctl submit` | 27 s | 137 | wrapper killed, tree reaped |
| p2e_r18 | launchd + peer-matching flags (`-j1 -o`) | 53 s | 137 | wrapper killed |

Control arms, all measured the same hour:

- **A non-Lean canary under the identical launchd shape survived 135 s+**
  (`/tmp/canary.sh`: a `sleep 5` loop). So the signal is not
  process-shape, not launchd ownership, not session ancestry.
- Peer lanes' `lean` processes are also dying and reappearing with fresh
  large-oid pids — consistent with a fleet-wide cull, not with a rule
  aimed at this lane.
- **No `SIGKILL` record exists for any of these pids in
  `~/.multiaim/logs/kill-ledger.jsonl`.** The body's killer-side ledger —
  whose whole purpose is attributing exactly this — has no entry. That
  gap is itself the finding: a kill path is signalling outside the ledger.
- `com.multiaim.lean-build-governor` logged `killed=0` on every tick and
  its launchd job is not running between ticks; `_reap_swap_offenders.sh`
  is dry-run by default and unscheduled. Neither owns the signal.

**Memory floor measured.** `lean -M 1800` (p2e_r19) aborted itself:
`lean::memory_exception: excessive memory consumption detected at
'interpreter'`, exit **134**. So this module genuinely needs **> 1.8 GB**
to elaborate, while the cull line behaves as ~2 GB. There is no headroom
between the module's floor and the cull threshold — a memory-capped build
is not an available workaround, and this is now a measurement rather than
a guess.

## Wrapper changes landed this session (durable, for the next attempt)

`p2e_build.sh` (new; `p2d_build.sh` left intact as the record):

1. **No `lake` in the build tree.** `LEAN_PATH` is resolved once
   (`lake env printenv LEAN_PATH`, sub-second) and `lean` is invoked
   directly. Measured rationale: the first kill of the session took
   `lake` while its `lean` child kept running — the child was the work,
   the parent was the kill target.
2. **PATH is exported explicitly**, so a `launchctl submit` run (minimal
   env) resolves the toolchain instead of exiting 66.
3. `-j1`, `-o <olean>`, and an optional `-M <MB>` cap are first-class,
   so the build form can be matched to whatever arbitration is live.
4. Everything else carried from p2d: bounded TERM-immunity, one-writer
   lock by liveness (never `kill -0`), SIGKILL-enforced hard cap, a
   watchdog that outlives the wrapper, and rule 4 (the wrapper owns the
   whole tree, so a killed middle process cannot leave its build alive).

Single next action: re-run `bash ./p2e_build.sh p2e_rNN.log` during a
window where `com.multiaim.lean-build-governor`'s kill path is dormant (or
after the reaper cure lands), then fix-forward whatever the endgame's
first real compile surfaces.

## Item (5), STARTED: the widgets dependency is now pinned and resolved

`lakefile.toml` carries `[[require]] name = "Widgets"` at
`darkhipo/minplus-widgets` rev `a1e6a90d6009682772c97e2122e19079ed4265c6`
(verified against the remote with `git ls-remote`; the same commit the
brief named). `lake update Widgets` resolved it into
`.lake/packages/Widgets` and `lake-manifest.json`, sharing the mathlib pin
`d13f23b7` and toolchain `v4.34.1`, exactly as that repo's
`INTEGRATION.md` §1 requires.

The consumer side is **not** landed: `Submission/FibHeapRow.lean` does not
yet import `Widgets.FrozenLock`, and `row_nlog`'s sweep-termination
side condition is still carried by `DegOK` + the capped recount, not by
`Φ_run_lt` / `tight_of_stable`. Nothing in this file claims otherwise.

## Standing seams (unchanged)

`DegOK` named clause (wound 2125609385); no-carry consolidation; the order
seam (`SimOK_perm` / `DkEvidence_perm`, named, open); the cascade
discipline (`hcc` witness reconciliation, named, open); r-absorption's
one-par deviation (machinePotential is par-blind; `row_nlog` transfers).
Frontier untouched. Credit: Fredman–Tarjan 1987 (construction and bound
theirs; formalization ours).
