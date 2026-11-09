# M3c PROMOTE — machine splice for the marked-parent cut (the CLRS cascade step)

Status: **LANDED 2026-11-08** as d1afc71 (`Submission/FibHeapPromote.lean`, b2-refine).
The landed splice differs from this spec in one planned way: the z-marking is FUSED into
the step (`mrk z := 1` write with `mrk z = 0` premise), which keeps `ldeg z` exactly
invariant — so the spec's `deg z ≤ deg y` position-inequality fallback was NOT needed.
This file is kept as the design record.

## The spec anchor

`Submission/FibHeapCut.lean`, section "The marked-parent boundary": `CutPre` carries
`st.mrk y = 0` because the cut keeps `ldeg y = deg y + mrk y` invariant only for an
unmarked parent. Cutting from a *marked* parent drops `ldeg y` by 2 — that case
"belongs to the promote/cascade updater". The abstract-level cascade already exists in
`Submission/FibHeapDynamic.lean` (`cascadeCut`, `promoteRoots`, transition 3 + 4);
M3c is its machine-array counterpart over `HState`, exactly as M3a did `cutState` and
M3b did `mergeState`.

## The shape (mirroring M3a/M3b)

`promoteState st y z` (naming free): the marked root-child `y` (`mrk y = 1`, so
`ldeg y = deg y + 1`) is cut from its parent `z` and re-rooted, `mrk y := 0` (the
promote — the mark is *spent*), `deg z := deg z - 1`, y spliced out of z's ring,
prepended to the root list. Suggested `PromotePre`: `y ∈ kids st z` at position k,
`z < st.n`, plus the ring facts M3a needed (`rgt (lft x) = x`, `lft x ∈ kids st z`
for `deg z ≥ 2`) and — the new bit —

  the PosOK arithmetic: y's old position k in z's list satisfies
  `k ≤ ldeg st y = deg y + 1`; after the step `ldeg (promoteState st y z) y =
  (deg y - 1) + 0 = deg y - 1`, and the discharge needs `k ≤ deg y - 1`, which is
  the *M3b inequality pattern*: `k < deg z ≤ deg y` (z is y's parent, so `deg z ≤
  deg y` by the old PosOK at position `deg z - 1 ≤ ...` — read it off
  `PosOK` at z's list the way `merge_posOK` reads `MergePre`'s fourth component).

The grandparent's mark (z) does NOT change in this step (the abstract cascade's
unmarked-stop semantics: see `cascadeCut` in FibHeapDynamic — whether z gets marked
is a policy decision; CLRS marks z. Check `cascadeCut_cons_zero` before fixing the
splice: if z is to be marked, MarkOK's discharge needs `mrk z ≤ 1` from
`mrk z = 0` premise — same shape as M3a's).

## Build discipline (measured this lane, 2026-11-08)

- Build the MODULE, not the root: `lake build Submission.FibHeapMerge` worked; the
  module is NOT in Submission.lean's import closure (root is M3a-green and must stay
  import-clean until promotion of the whole arc). Detached nohup + bounded poll;
  ~2-10 min/cycle; full dep bank replay 2259 jobs only on first build.
- v4.34.1 core lemma directions (burned twice this session):
  `Function.iterate_succ_apply : f^[n+1] x = f^[n] (f x)` and
  `Function.iterate_succ_apply' : f^[n+1] x = f (f^[n] x)` — PRIME is the
  `f (f^[n] x)` form. `ParOK` takes BOTH `p` and `c` explicitly (`hpar p c hmem`);
  never leave the `c` slot as `_` under a `.trans` (the unifier assigns it from the
  trans midpoint, not from the membership proof).
- Witness-region simp sets need `mergePreSt`-style explicit pre-state unfolding
  (see `kids_merged`, `merged_NILNotRoot`), and `FibHeapSupport`-size goals need
  `FibHeapForest.Child.tree` in the simp set (match-def accessor, not a structure
  projection — does not reduce otherwise).
- No sorry/admit/native_decide; the file stays uncommitted until green; ONE atomic
  commit; ls-remote verify. Axiom budget: all theorems ⊆
  [propext, Classical.choice, Quot.sound] (M3b landed with 25 axiom-free).

## After the splice lands

The arc is then complete at machine level: link (M2) → cut-unmarked (M3a) →
consolidation merge (M3b) → promote-cut-marked (M3c). Promotion into the
`Submission.lean` closure + the dynamic↔machine refinement glue is the milestone
after that (M4), not this one.
