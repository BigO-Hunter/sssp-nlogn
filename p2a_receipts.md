# p2a receipts — Submission/FibHeapProg.lean @ wip-consolidation-measure

1. Exit-code receipt: `lake env lean Submission/FibHeapProg.lean` → **exit 0**
   (p2a_final.log last line: `exit 0`; rounds p2a_build1–17 in-tree, one host SIGTERM at round 6).
2. Build log: `p2a_final.log` — **0 errors**, 28 linter warnings only
   (deprecated if_pos/if_neg + 1 unused simp arg; same classes as m22_final).
3. Axiom probe (in-file `#print axioms`, echoed in p2a_final.log):
   - `insertOp_runs`  : [propext, Classical.choice, Quot.sound]
   - `copyLoop_runs`  : [propext, Classical.choice, Quot.sound]
   No `sorryAx` anywhere in the module.

Landed theorems: `insertOp_runs` (the O(1) promotion-log append; decode untouched,
cost exactly 2), `copyLoop_runs` (the copy-back loop; every step splices the decoded
roots list via the landed `decode_storeW_roots`, so the decoded list climbs from the
zero-fill to `range t ↦ rd` — the congruence-carry the task named, end-to-end).
Also landed: `decode_allocW_foreign`/`Rel.allocW_foreign` (foreign-alloc decode
invariance), `wa_roots_of_rel`/`wa_par_of_rel` (decode-side read lemmas),
`flt`/`flt_step`/`flt_len_le` (the filtered-prefix machinery), and the program texts
`stashLoop`/`copyLoop`/`rootsCompact`/`insertOp`.

Named remainder (next landing, stated in the module docstring): `stashLoop_runs`
(invariant `StashI` sketched in the docstring) and its composition
`rootsCompact_runs` (post `Rel {st with roots := flt st elogR L (L+e)}`,
cost `≤ 14·(L+e)+7`); then decrease-key/extract-min texts + SimOK/merge_SimOK/
DkEvidence Runs-wiring; then the charge (m·5 + 2·rankCap + 2; D0+6K+D1) and the
arithmetic climb to `Bound 1 1 1 1 0`.

Standing seams unchanged: DegOK is the named clause (wound 2125609385); no-carry
consolidation (`FibHeapConsolidate`).  Credit: Fredman–Tarjan 1987.
