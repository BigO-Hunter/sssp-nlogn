# p2b receipts — Submission/FibHeapProg.lean @ wip-consolidation-measure

Landed: `stashLoop_runs` (task item 1) + `rootsCompact_runs` (task item 2) — the full
store-compaction receipt for the consolidation roots filter.

1. Exit-code receipt: `lake env lean Submission/FibHeapProg.lean` → **exit 0**
   (p2b_r9.log; rounds p2b_r1–r9, one foreground kill at load ~150 → detached
   `trap "" TERM` wrapper per convention); `lake build Submission` → **exit 0**,
   `lake build Submission.FibHeapProg` → **exit 0** (p2b_final.log).
2. Named olean: `.lake/build/lib/lean/Submission/FibHeapProg.olean`
   (2,462,480 bytes, built 13:18, fresh from this tree).
3. Axiom probe (in-file `#print axioms`, echoed in p2b_r9.log and p2b_final.log):
   - `stashLoop_runs`   : [propext, Classical.choice, Quot.sound]
   - `rootsCompact_runs`: [propext, Classical.choice, Quot.sound]
   (insertOp_runs/copyLoop_runs unchanged: same axiom set.) **No `sorryAx`, no
   `native_decide` anywhere in the module.**

What landed:

- `stashLoop_runs` — invariant `StashI` (k cells scanned, live prefix of the combined
  source in `"rt2"` in total-`getD` form, decode untouched, `L`/`e` pinned, log reads
  stable, cost ≤ 8·k); per-iteration select-ite/live-test/store chain reusing
  `wa_roots_of_rel`/`wa_par_of_rel`; post: j = L+e, t = live count, cost ≤ 8·(L+e)+1.
- `rootsCompact_runs` — stashLoop + copyLoop through the `walloc "roots"` re-length
  (`decode_allocW_roots`): post `Rel {st with roots := flt st (r.wa "elog") L (L+e)}`
  (decode exact at the compaction boundary), `wlen "roots"` = live count, cost
  ≤ 14·(L+e)+7 (arithmetic `(k+1)+2+(8k+1)+(T+1)+1+(4T+1)`, `T ≤ k`).
- Supporting: `w_allocW`, `evalW_sub_of`, `flt_zero` plumbing lemmas; `StashI`.

Design notes for the next mind: the select's post-select state carries THREE charges
(while test + ite test + write) — `s1.cost = s.cost + 3`, and every state literal in
the select branches must show all three layers or the unification fails silently.
Cell agreement in `StashI` is stated in bounded `List.getD` form (non-dependent), so
`flt_step` rewrites stay motive-correct on climb; the final `Rel` assembly bridges
`getD` → `getElem?` → `getElem` via `List.getD_eq_getElem?_getD` +
`List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩`.

Position of the wiring (task item 3): NOT started — decrease-key/extract-min program
texts + SimOK/merge_SimOK/DkEvidence Runs-wiring (pending-log window relation shape
`decode r = st ∧ log r = pending`), then the charge (m·5 + 2·rankCap + 2; scaled
D0+6K+D1) and the arithmetic climb (`log_ge`/`cap_one_one`/`sparse_one_one`/
`arith_clause*` at `Time 1 1 0`) toward `Bound 1 1 1 1 0`.  Module docstring updated
to the landed state with the remaining remainder stated.

Standing seams unchanged: DegOK is the named clause (wound 2125609385); no-carry
consolidation (`FibHeapConsolidate`).  Frontier untouched.
Credit: Fredman–Tarjan 1987 (construction and bound theirs; formalization ours).
