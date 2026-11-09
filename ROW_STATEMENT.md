# The row statement — directed-sssp `n log ; n log` (Fibonacci-heap Dijkstra)

**Fredman–Tarjan 1987.  Bound theirs; formalization ours.**

Lane: `darkhipo/sssp-nlogn`, branch `wip-consolidation-measure` @ `661ea7b`
(`661ea7bd9365c6007e26316b5693b9f13dabd0f7`, pushed).  Row file:
`Submission/FibHeapRow.lean`.  This document is the submission-facing
assembly of that row: the two landed row theorems, the two named residuals
attached verbatim, and the credit.

## The row, as landed

`rankCap n = 2 * Nat.log 2 n + 1` (`FibHeapAccounting.lean:73` — the loose
elementary log cap, golden-ratio-free), so every `rankCap` term below is in
the `⌊log₂ n⌋` class.

### `row_nlog` — the `n log ; n log` row (`FibHeapRow.lean:255`)

```lean
theorem row_nlog {st : HState} (s : DkRunClear (FibHeapAccounting.rankCap st.n) st)
    (r : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hmc : MarkChain (extractState s.last r) (extractState s.last r).n chain)
    (hpre : ExtractPre s.last r) (hrl : RootsLive s.last) (hnn : NILNotRoot s.last)
    (hpar : ParOK s.last) (hslot : SlotOK s.last) (hps : ParSlot s.last)
    (hs : NILSelf s.last) (hac : Acyc s.last) (hnl : NILLeaf s.last)
    (hm : MarkOK s.last) (hpos : PosOK s.last) (hnd : ∀ q, KidsNodup s.last q)
    (hnc : NILNotChild s.last) (hrnc : RootNotChild s.last)
    {y : ℕ} (hW : WalkUp (extractState s.last r) y chain)
    (hyw : y < (extractState s.last r).n)
    (hy0 : 0 < (extractState s.last r).deg y)
    (hmono : ∀ a b : ℕ, a ∈ kids (extractState s.last r) b →
      (extractState s.last r).deg a < (extractState s.last r).deg b) :
    machinePotential (cascadeRun (extractState s.last r) chain stop)
      ≤ machinePotential st + s.count * 5
        + (2 * FibHeapAccounting.rankCap st.n + 2)
```

In words: `m = s.count` decrease-keys under the clearing discipline
(constant `+5` potential per op) followed by one extract-min with its
consolidation walk raise the machine potential by at most `m·5 +
(2·rankCap st.n + 2)` — the decrease-key half constant per op, both
extract walk terms (the splice `(kids r).length` at the run's final state
and the consolidation `chain.length` via `recount_len_le_rankCap`)
at the log-class cap.  The recount is self-contained over the extract
state: the `extract_*` preservation suite discharges the walk's bundle,
`extract_PosOK` supplies its `PosOK` piece, `hy0` is the program fact
that the cascade starts at the cut node's parent (which retains a
child).  `hmono` is the named seam — Residual 1 below.

### `row_decreaseKeyClear_scaled` — the machine's FT per-op charge (`FibHeapRow.lean:234`)

```lean
theorem row_decreaseKeyClear_scaled {K D0 D1 : ℕ} (hK : D1 ≤ K) {L : ℕ} {st : HState}
    (s : DkRunClear L st) :
    FibHeapAccounting.scaledPotential K s.last.roots.length (machineMarks s.last)
      ≤ FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
        + s.count * (D0 + 6 * K + D1)
```

In words: telescoped over the capped run, each decrease-key op is charged
the machine's FT unit `D0 + 6K + D1` (the fold segment `D0 + 3K + D1` via
`decrease_amortized_of_clearCascadeRun` plus the cut's own `+3K` rise).
Its honesty note is Residual 2 below.

## Residual 1 — `deg_lt_of_kids` (wound 2125609385), VERBATIM + STATUS 2026-11-09

> FibHeapDepth.lean (lines 17, 74) names deg_lt_of_kids (y in kids st z -> st.deg y < st.deg z) as the single missing lemma. walkUp_len_le_deg takes degree-strictness (hmono) as a hypothesis, so the cascade-walk length bound chain.length <= rankCap st.n (the decrease-key half log cap, the L := rankCap n instantiation) is blocked on it. PosOK cannot supply it: PosOK lower-bounds a child degree by its kid-list position (ldeg ordering), it gives no parent-strictness. The lemma needs the link-time discipline carried on the machine state (children linked only at equal degree, so deg parent = deg child + 1 at link; cuts/promotes only decrement) -- a machine InvOK carry in the FibHeapDynamic lineage. Until it lands, the recount composes with hmono as an explicit seam hypothesis.

**STATUS (this session): the carry is LANDED as the named machine clause `DegOK`
(`FibHeapRefine`), with the honest boundary stated in its docstring.  Pointwise strictness
is NOT a theorem of the reachable states — a parent that loses two children through
separate cascades decrements past a high frozen-degree child (the `ldeg` variant fails at
equality the same way) — so the clause is the modeled link-time discipline, exactly as
`FibHeapDynamic.InvOK` is the *static form* of the same discipline on the abstract forest
(whose `lost` accounting likewise does not imply parent-strictness).  What IS proved: the
link is genuinely inductive (`link_DegOK`, equal-degree precondition — the consolidation
step), the extract splice preserves it *unconditionally* (`extract_DegOK` — the splice
deletes edges only), and `row_nlog` now takes the clause as `hdeg : DegOK s.last` with the
extract-state strictness derived INSIDE the row (the anonymous `hmono` hypothesis over the
extract state is gone).  The seam is one named machine invariant at the run's final state,
no longer a hand-supplied per-call fact.

Scope: the log-class recount's strictness.  Register status: **open** (the pointwise
lemma is not discharged as a reachable-state theorem — the named clause is the landing;
closures of 2125609385 should cite this boundary).

## Residual 2 — the honest-6K charge (fresh-parent run model), VERBATIM

From `DkRunClear.potential_scaled_ft` (`FibHeapAmortized.lean:166-181`):

> Residual named: the literal CLRS charge `D0 + 3K + D1` for the full op is not derivable in this model — the fresh-parent run banks a new mark at every cut and the terminal leaves it spent, so the amortized unit carries the cut's `3K` on top of the fold's `3K + D0 + D1`; reaching `3K` needs the old-mark cascade shape (where the cut banks nothing) or an explicit work-sum on the run.

Scope: the scaled per-op unit only.  Both `+5` (unscaled, `row_nlog`'s
half) and `D0 + 6K + D1` (scaled) are constant-per-op — the `n log`
decrease-key class holds under either; the gap to the literal CLRS `3K`
unit is the honesty seam, not a bound risk.

## Accounting boundary (stated, not papered)

The row's decrease-key half is the *clearing* discipline (`DkRunClear`,
the CLRS-write cascade landed in the Measure lane).  The transfer-
discipline run (`DkRun`, `count * (st.n + 5)`) is kept alongside as the
seam's other side; the transfer lane's `CascadeMarks` ledger remains the
accounting boundary between them.  The def-swap that would move the
machine ledger onto the row's discipline is the named separate session —
not this filing's premise.

## Credit

Fredman–Tarjan 1987, *Fibonacci heaps and their uses in improved network
optimization algorithms* (STOC '87; JACM 34(3)) — the `O(m + n log n)`
bound theirs; formalization ours.
