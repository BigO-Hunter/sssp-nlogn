# p2c receipts — Submission/FibHeapProg.lean @ wip-consolidation-measure

Landed: task item (3), first leg — **the pending-log window + the decrease-key and
extract-min op texts + their step congruences**, plus the first per-step wiring
receipt (`insertOp_RelLog`).

1. Exit-code receipt: `lake env lean Submission/FibHeapProg.lean` → **exit 0**
   (p2c_r6.log; rounds p2c_r1–r6, all under the detached `trap "" TERM` wrapper —
   host load 90–150 throughout, no foreground kills this session);
   `lake build Submission.FibHeapProg` → **exit 0**, `lake build Submission` →
   **exit 0** (p2c_final.log).
2. Named olean: `.lake/build/lib/lean/Submission/FibHeapProg.olean` (fresh from
   this tree; size/time in p2c_final.log tail).
3. Axiom probe (in-file `#print axioms`, echoed in p2c_r6.log):
   - `insertOp_runs` / `copyLoop_runs` / `stashLoop_runs` / `rootsCompact_runs`
     (landed p2a/p2b, unchanged): [propext, Classical.choice, Quot.sound]
   - `insertOp_RelLog`, `decode_cutSplice`, `decode_twoStore_clear`,
     `decode_foldl_clear`, `decode_extractSplice`:
     [propext, Classical.choice, Quot.sound]
   - `flt_filter_append`, `flt_eq_filter_append`: [propext, Quot.sound]
   **No `sorryAx`, no `native_decide` anywhere in the module.**

What landed:

- **The pending-log window** (the relation shape the design demands): `logOf`
  (the log's logical contents, cells `0…e−1` of `"elog"` in cell order),
  `RelLog stW pending r := Rel stW r ∧ logOf r = pending` — the decode stays
  EXACT while appends ride the log — the join `win`, the append mechanics
  (`logOf_append`, `RelLog.bump`: one `"elog"` store + count bump = window
  grows one cell, decode untouched), foreign-store/`setW` preservation
  (`RelLog.storeW`, `RelLog.w_other`), and the compaction boundary's closure
  (`flt_filter_append` / `flt_eq_filter_append`: the landed filter's source is
  exactly `stW.roots ++ pending`, so the compaction's post-`Rel` IS the joined
  abstract state).
- **`insertOp_RelLog`** — the insert op re-wired at the window: the first
  per-step Runs receipt in the pending-log relation shape
  (`RelLog stW (pending ++ [r.w "x"]) r' ∧ cost = r.cost + 2`).
  `logPush reg` factored out; `insertOp = logPush "x"` by `rfl`.
- **The decrease-key op text**: `dkCut` (the seven-store cut — branch tests
  reading pre-store cells: `load "deg" y` before the decrement, relink indices
  `lft x`/`rgt x` pre-state — plus the pending append), `promoteCell`
  (`promoteState`'s stores per cascade cell + the append), `dkCascade` (the CLRS
  walk from the cut's marked `y`, product test `0 < mrk z · z` = "marked ∧
  non-NIL"), `dkOp` = cut + walk + stop-mark.
- **The extract-min op text**: `kidStep`/`kidLoop` (re-root each child of the
  `deg r`-step ring walk: `par c := 0`, `mrk c := 0`, append to the log),
  `absorbMin` (`deg r := 0`, `chd r := 0`, slot absorbed off-tree at
  `absorbVal r` — `1`, or `2` when the slot IS 1; side condition `3 ≤ n`), and
  `extractOp` = kidLoop + absorbMin + the landed `rootsCompact` (which drops
  `r` — its `par` fails the live test — and absorbs the log; the compaction's
  scan register `"r"` clobbers the dead min id after `absorbMin`).
- **The step congruences** (the wiring's mechanics, proved):
  `decode_cutSplice` — the decode lands exactly at the window frame `cutPend`
  (`cutState` with the roots-prepend deferred to the pending log), all three
  branch shapes; `decode_foldl_clear` / `decode_twoStore_clear` — the
  child-clearing fold; `decode_extractSplice` — the decode lands exactly at
  `extractStateAbs` (`extractState` with the roots change deferred and the slot
  absorbed at the register's sentinel). Supporting: per-field decode readers
  (`wa_mrk/deg/chd/rgt/lft_of_rel`), `map_range_getD`, `degUpd_eq`.

Design decisions taken (and their seams, named):

1. **The window relation is exact-decode + log** (`RelLog`), with the abstract
   state the algorithm sees being the join `win stW pending`
   (`roots := stW.roots ++ pending`).  The compaction boundary closes exactly
   (`flt_eq_filter_append`).
2. **r-absorption**: the extracted min keeps its slot (arrays are length `n`)
   and must not survive the compaction's live test `par x = 0` — the program
   absorbs it off-tree at `absorbVal r` (`par r := 1`, or `2` when `r = 1`).
   Sound because nothing points at `r` (it was a root; its children are
   re-rooted first) and `Acyc` only forbids non-NIL `par`-cycles the new edge
   cannot create.  Side condition `3 ≤ n`; the sim invariant should carry
   `3 ≤ n` (the race's `N ≥ 16` anyway).  **This deviates from `extractState`**
   by one `par` cell — `extractStateAbs` IS that state, and `machinePotential`
   is `par`-blind, so `row_nlog`'s bound transfers; the relanding of the
   extract-preservation suite at the absorbed form is wiring work.
3. **THE ORDER SEAM (named, open)**: the abstract splices PREPEND to `roots`
   (`x :: st.roots`); the log appends land at the window's TAIL.
   `SimOK` and `machinePotential` are roots-order-insensitive, so the seam is a
   roots-permutation transfer family (`SimOK_perm`, `DkEvidence_perm`) —
   bounded, not yet written.
4. **THE CASCADE DISCIPLINE (named, open)**: `ClearChain`'s cells need each
   cell's `y` marked in the cell's own running state, but the clearing promote
   clears the parent `z` too — so consecutive overlapping cells are impossible
   in the model while the CLRS walk text promotes consecutively.  The walk text
   is the algorithm; the `hcc` witness-generation reconciliation (the risk
   `DkEvidence` already names) is the open seam.

Gotchas for the next mind (all measured this session):

- `rw [if_pos h]` matches ONE occurrence — the LHS `cutSplice`'s own branch
  if-terms steal it from the RHS `cutState`'s; use `simp only […, if_pos h]`
  which rewrites all instances.
- The op texts' `.seq` chains: the OUTERMOST `.seq` must NOT be wrapped in its
  own `(...)` — the dotted identifier loses its expected type inside the paren
  (`lean.invalidDottedIdent`).  Nest `(.seq …)` from the second level on.
- The paren count that matters is the STACK TRACE, not global balance — one
  `)` too many mid-def closes an outer group early and still balances globally
  (two such bugs shipped to round 4).  Verify with a depth tracker per group.
- `HState.mk.injEq` needs FULL application — `(HState.mk.injEq _ _).2` fails
  (the remaining fields stay as ∀-binders); use `rw […, HState.mk.injEq]` in
  the tactic chain instead.
- `List.append_assoc` direction: the compaction boundary needs `←` (left-assoc
  target); `Nat.add_assoc` likewise `←` for `L + (e+1) → L+e+1`.
- The `Runs`-rule chains key on the OUTERMOST state constructor: for
  `((storeW …).charge 1).setW …` the decode rw order is `decode_w_other`,
  `decode_charge`, `decode_storeW_foreign` (setW before charge); for
  `(((…).charge 1).setW …).w "x"` the value rw order is `w_setW`, `if_pos`,
  then nothing (auto-rfl).  Mismatched order = silent rewrite failures.
- `simp`'s discharger does NOT do funext-then-rfl: residue goals of the shape
  `(fun j => … j) = fun i => … i` (alpha or pointwise-equal bodies) need either
  a pointwise transfer lemma (`degUpd_eq`) or an explicit funext pass.

Position of item (3) now:

- Texts: LANDED (both ops, full branch coverage, `Runs`-mechanics proved at the
  congruence level).
- Wiring: `insertOp_RelLog` proved; `dkCut`/`dkOp`/`extractOp` `Runs` receipts
  are now MECHANICAL (eval facts + `cutSplice`/`extractSplice` bridges +
  `insertOp_RelLog` for the appends) but not yet written — the next landing.
  Then `SimOK` + `merge_SimOK` + `DkEvidence` across `Runs` at `RelLog`, with
  the order-seam transfer family.
- Charge (c) / arithmetic (d): NOT started — blocked behind the sim receipts
  (unchanged from p2b's assessment).

Standing seams unchanged: `DegOK` named clause (wound 2125609385); no-carry
consolidation (`FibHeapConsolidate`).  Frontier untouched.  Credit:
Fredman–Tarjan 1987 (construction and bound theirs; formalization ours).
