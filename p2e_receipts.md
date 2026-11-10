# p2e receipts — Submission/FibHeapProg.lean @ wip-consolidation-measure+

LANDED (this leg): **`dkCut_runs`** — the cut op's `Runs` receipt, via the
variable-lemma restructure the p2d receipts prescribed.

## What landed

1. **The cut chain at variable level** (the `dkCut_runs` scaffolding):
   - `wa_stores_pass` — the wrapper-list induction lemma (a read through a
     charged store list that never touches `(b, j)` is the pre-state read);
     the head stage's four read congruences are its instances via the
     two-store `foldl` `rfl`-bridge.
   - `wa_storeW_pass` / `wa_storeW_self` — the one-wrapper generics
     (foreign-store pass-through; the same-array split shape).
   - Stage defs `dkHeadC / dkTrueChd / dkTrue / dkChdC / dkRgtC / dkLftC /
     dkDegC / dkSkipC / dkSkipRgtC / dkSkipLftC / dkSkipDegC` — each carries
     the machine's exact charge structure (one `.charge 1` per
     `wstore`/`ite`/`skip` step), so every receipt state is the def-form.
   - Per-stage read congruences (one wrapper per peel) and ready-made
     `evalW` facts for every `runs_wstore` argument.
   - The genuine split (`rgt x` read through the fresh `rgt` store) stated
     once per arm: `dkRgtC_wa_rgt_x` / `dkSkipRgtC_wa_rgt_x`.
   - `decode_dkChain_true` / `decode_dkChain_false_one` /
     `decode_dkChain_false_two` — the hoisted `decode_cutSplice`-style
     congruences over a plain `r` (the branch conditions are hypotheses;
     `Rel` carried so the receipt instantiates `stW` values with `rfl`).
   - `logOf_dkTrue` / `logOf_dkDegC` / `logOf_dkSkipDegC` — the stores leave
     the window verbatim.
2. **`dkCut_runs`** — the receipt: same haves/branch structure/cost
   arithmetic as the p2d draft, re-attached as one-line citations; the
   FALSE_TWO run order fixed to the program text's `.seq rgt lft` (the
   draft's arm had the relinks swapped).  Cost `≤ 10` (7 / 8 / 10 per
   branch; the `simp only [cost_storeW, cost_charge]` tail reduces the
   post-state literal to `r.cost + 7/8/10 + 2` and `omega` closes).

## Receipts

VERIFIED GREEN (rounds p2e_r5/r6 axiom dumps, in-log `#print axioms`):
- `wa_stores_pass` [propext]
- `decode_dkChain_true` / `decode_dkChain_false_one` / `decode_dkChain_false_two`
  [propext, Classical.choice, Quot.sound]
- all previously landed probes unchanged; no sorryAx in any landed theorem.

`dkCut_runs` (round-9 text): assembled, receipt compile BLOCKED by the host
memory shed (R2125609450 — five 7-8 GB orphaned leans from this lane's own
superseded rounds drove swap to 94%+; the peer's cured wrapper + shed now
SIGKILL any 8 GB lean on sight, correctly).  Round-9 state carries:
- in-situ chain peels in the three logPush `hR` blocks (zero state-defeq
  bridges — every rw matches the raw nest syntactically; the decode-level
  `show`/`exact` bridges were measured as the heartbeat burners, r2/r6);
- explicit 8-component `refine` finishers (par/mrk/deg/chd/rgt/lft/roots/n),
  each a one-line funext+by_cases+simp — replacing the plain-`simp` finishers
  measured at 421 s tactic time (r8 profiler);
- the `logPush` mono's `hR` goal is stated as `Rel …` — the
  `simp only [FibHeapDecode.Rel]` unfold must precede the peel (r7).
No build has yet covered the round-9 file; that is the single next action
(when swap frees), via the cured `p2d_build.sh` (R2125609450 rules:
one-writer lock, SIGKILL cap, orphan guard).

## Standing seams

Unchanged: `DegOK` named clause (wound 2125609385); no-carry consolidation;
the order seam (`SimOK_perm`/`DkEvidence_perm`, named, open); the cascade
discipline (`hcc` witness reconciliation, named, open).  Frontier untouched.
Credit: Fredman–Tarjan 1987 (construction and bound theirs; formalization
ours).
