import Submission.FibHeapDecode
import Mathlib.Data.List.Basic

/-!
# Submission.FibHeapProg — the p2 program texts over the decoded frame

The Fib-heap program `p2` runs on the `Frontier.RAM` machine and simulates `HState`
through `FibHeapDecode.Rel` (`decode r = st`).  This module lands the first build
items of p2 proper:

1. **The consolidation roots filter as the store-compaction loop** (`rootsCompact`).
   The machine has no re-lengthing statement — the only way to change `wlen` is the
   zeroing `walloc` — so the filter of the surviving roots is a real store-compaction:
   scan the roots array plus the promotion log, stash the live entries (`par x = 0`)
   into the scratch array `"rt2"`, re-allocate `"roots"` at the live count, and copy
   back.  The step mechanics are exactly the landed congruences: every copy-back store
   splices the decoded list (`decode_storeW_roots` — carried here end-to-end by
   `copyLoop_runs`), the re-allocation re-lengths it (`decode_allocW_roots`), and the
   pointwise bridge (`rel_of_pointwise`) lands the relation at the end.

2. **The insert op** (`insertOp`, proved: `insertOp_runs`) — one O(1) machine step:
   the new root id (register `"x"`) is appended to the promotion log `"elog"` (an
   array foreign to the decode) and the log count register `"e"` is bumped.  The
   roots list itself is re-lengthed only by the next `rootsCompact` — the pending-log
   design that makes every per-op roots mutation ride the ONE compaction point.

## The pending-log layout decision (why the compaction is the one roots mutation)

`State.wlen` changes only through `State.allocW`, which zeroes the array.  A per-op
append (cut/cascade promote, insert) at exact array length would therefore cost O(L)
per op and break the `n log` row.  The design: `insertOp` and the cut/cascade promote
append into the promotion log `"elog"` (register `"e"` = logical count; `wlen "elog"`
is capacity), and `rootsCompact` — run once per extract-min — is the single point
where the roots array is re-lengthed, absorbing the log.  The absorbed entries are
exactly the meld-consumed roots (`par ≠ 0` after the melding pass); the live test
`par x = 0` is the NIL convention (`NILRoots`).  The decode stays exact at every
compaction boundary; between boundaries the pending log is extra machine state that
the step lemmas carry (next leg).

## Standing seams (unchanged)

**`DegOK` is the named clause** (wound 2125609385) — the frame carries it, the program
does not discharge it.  **No carry** — the consolidation fold consumes `ExtractOkDeg`
chains the table generates (`FibHeapConsolidate`); the pairwise-distinct-degrees
restriction is the stated remainder.

## Landed (this module, complete)

1. **The stash loop** (`stashLoop_runs`) — invariant `StashI`: `k` cells scanned, the
   live prefix of the combined source sits in `"rt2"` (cell agreement in total-`getD`
   form), the decode is untouched, `L`/`e` pinned, cost `≤ 8·k`.  Per iteration the
   select `ite` reads cell `j` (roots list below `L`, promotion log above —
   `wa_roots_of_rel`/`wa_par_of_rel` carry the reads), the live test reads `par`
   through the decode, and the stash store is foreign (`decode_storeW_foreign`).
   The per-iteration state after the select carries the while + ite + write charges
   (`s.cost + 3`); the tail re-establishes `StashI (k+1)`.
2. **The full compaction** (`rootsCompact_runs`) — `stashLoop_runs` + the proved
   `copyLoop_runs` composed through the re-allocating `walloc "roots"`
   (`decode_allocW_roots`): post
   `Rel {st with roots := flt st (r.wa "elog") L (L+e)}` (the decode exact at the
   compaction boundary), `wlen "roots"` = the live count, cost `≤ 14·(L+e) + 7`
   (arithmetic: `(k+1) + 2 + (8k+1) + (T+1) + 1 + (4T+1)` with `T ≤ k`).

## Landed, second leg (the p2c session): the window + the two op texts

3. **The pending-log window** — `logOf`/`RelLog` (`decode r = stW ∧ logOf r =
   pending`, the relation shape the design demands: the log appends do not
   disturb the decode), the join `win`, the append step (`RelLog.bump`, the
   landed `insertOp` re-wired: `insertOp_RelLog`), and the compaction
   boundary's closure (`flt_eq_filter_append`: the landed filter's source is
   exactly `stW.roots ++ pending`).
4. **The decrease-key op text** (`dkCut` + `dkCascade` + `dkOp`) and the
   extract-min op text (`kidLoop` + `absorbMin` + `extractOp`), with the pure
   store-sequence congruences `decode_cutSplice` / `decode_extractSplice` —
   the decode lands exactly at the window frames `cutPend` /
   `extractStateAbs` (`cutState`/`extractState` with the roots change
   deferred to the pending log; the extract's slot absorbed off-tree at
   `absorbVal`).

## Named remainder (next landing)

- The `Runs` receipts for `dkCut`/`dkOp`/`extractOp`: now mechanical — eval
  facts + the `cutSplice`/`extractSplice` bridges + `insertOp_RelLog` for the
  appends — but not yet written.  Then the per-step `SimOK` +
  `merge_SimOK` + `DkEvidence` wiring across `Runs` at the window relation.
- **The order seam (named):** the abstract splices prepend to `roots`
  (`x :: st.roots`); the log appends land at the window's tail.  `SimOK` and
  `machinePotential` are roots-order-insensitive, so the seam is a
  roots-permutation transfer family (`SimOK_perm`, `DkEvidence_perm`) —
  bounded, not yet written.
- **The cascade discipline (named):** `ClearChain`'s cells each need their
  `y` marked in the cell's own running state, and the clearing promote
  clears the parent `z` too — so consecutive overlapping cells are
  impossible in the model while the CLRS walk text promotes consecutively.
  The walk text is the algorithm; the chain-witness reconciliation (the
  `hcc` generation risk `DkEvidence` already names) is the open wiring seam.
- The charge (potential deltas as time: `row_nlog`'s `m·5 + 2·rankCap + 2`,
  scaled `D0+6K+D1`) and the arithmetic climb (`log_ge`/`cap_one_one`/
  `sparse_one_one`/`arith_clause*` at `Time 1 1 0`) toward
  `Bound 1 1 1 1 0` — blocked behind the sim receipts.

Credit: Fredman–Tarjan 1987, *Fibonacci heaps and their uses in improved network
optimization algorithms* (STOC '87; JACM 34(3)) — the construction and the bound
theirs; formalization ours.
-/

namespace Submission.FibHeapProg

open Frontier Frontier.RAM WExpr Stmt
open Submission.FibHeapRefine Submission.FibHeapDecode
open scoped NNReal

variable {V : Type}

/-! ## State-access plumbing (generic in `V`; `rfl`) -/

theorem w_charge (s : State V) (k : ℕ) (x : String) : (s.charge k).w x = s.w x := rfl
theorem w_setW (s : State V) (x : String) (a : ℕ) (y : String) :
    (s.setW x a).w y = if y = x then a else s.w y := rfl
theorem w_storeW (s : State V) (arr : String) (j a : ℕ) (y : String) :
    (s.storeW arr j a).w y = s.w y := rfl
theorem wa_charge (s : State V) (k : ℕ) (x : String) (j : ℕ) :
    (s.charge k).wa x j = s.wa x j := rfl
theorem wa_setW (s : State V) (x : String) (a : ℕ) (arr : String) (j : ℕ) :
    (s.setW x a).wa arr j = s.wa arr j := rfl
theorem wa_storeW (s : State V) (arr : String) (j a : ℕ) (x : String) (i : ℕ) :
    (s.storeW arr j a).wa x i = if x = arr ∧ i = j then a else s.wa x i := rfl
theorem wa_allocW (s : State V) (arr : String) (k : ℕ) (x : String) (j : ℕ) :
    (s.allocW arr k).wa x j = if x = arr then 0 else s.wa x j := rfl
theorem wlen_charge (s : State V) (k : ℕ) (x : String) :
    (s.charge k).wlen x = s.wlen x := rfl
theorem wlen_setW (s : State V) (x : String) (a : ℕ) (arr : String) :
    (s.setW x a).wlen arr = s.wlen arr := rfl
theorem wlen_storeW (s : State V) (arr : String) (j a : ℕ) (x : String) :
    (s.storeW arr j a).wlen x = s.wlen x := rfl
theorem wlen_allocW (s : State V) (arr : String) (k : ℕ) (x : String) :
    (s.allocW arr k).wlen x = if x = arr then k else s.wlen x := rfl
theorem cap_charge (s : State V) (k : ℕ) : (s.charge k).cap = s.cap := rfl
theorem cap_setW (s : State V) (x : String) (a : ℕ) : (s.setW x a).cap = s.cap := rfl
theorem cap_storeW (s : State V) (arr : String) (j a : ℕ) :
    (s.storeW arr j a).cap = s.cap := rfl
theorem cap_allocW (s : State V) (arr : String) (k : ℕ) :
    (s.allocW arr k).cap = s.cap := rfl
theorem cost_charge (s : State V) (k : ℕ) : (s.charge k).cost = s.cost + k := rfl
theorem cost_setW (s : State V) (x : String) (a : ℕ) : (s.setW x a).cost = s.cost := rfl
theorem cost_storeW (s : State V) (arr : String) (j a : ℕ) :
    (s.storeW arr j a).cost = s.cost := rfl
theorem cost_allocW (s : State V) (arr : String) (k : ℕ) :
    (s.allocW arr k).cost = s.cost := rfl

/-- Charging does not touch the decode (the decode reads no cost). -/
theorem decode_charge (r : State V) (k : ℕ) : decode (r.charge k) = decode r := rfl

/-- A foreign array allocation leaves the decode untouched (parity with the landed
`decode_storeW_foreign`; the decode reads no array outside the layout). -/
theorem decode_allocW_foreign (r : State V) {b : String}
    (hb : b ≠ "par" ∧ b ≠ "mrk" ∧ b ≠ "deg" ∧ b ≠ "chd" ∧ b ≠ "rgt" ∧ b ≠ "lft" ∧
      b ≠ "roots") (k : ℕ) : decode (r.allocW b k) = decode r := by
  simp [State.allocW, decode, Ne.symm hb.1, Ne.symm hb.2.1, Ne.symm hb.2.2.1,
    Ne.symm hb.2.2.2.1, Ne.symm hb.2.2.2.2.1, Ne.symm hb.2.2.2.2.2.1,
    Ne.symm hb.2.2.2.2.2.2]

/-- The relation survives a foreign allocation verbatim. -/
theorem Rel.allocW_foreign {st : HState} {r : State V} (h : Rel st r) {b : String}
    (hb : b ≠ "par" ∧ b ≠ "mrk" ∧ b ≠ "deg" ∧ b ≠ "chd" ∧ b ≠ "rgt" ∧ b ≠ "lft" ∧
      b ≠ "roots") (k : ℕ) : Rel st (r.allocW b k) := by
  show decode (r.allocW b k) = st
  rw [decode_allocW_foreign r hb, h]

/-- Pointwise map agreement under a pointwise function agreement (in-range). -/
theorem map_range_congr {f g : ℕ → ℕ} {t : ℕ} (h : ∀ j, j < t → f j = g j) :
    (List.range t).map f = (List.range t).map g := by
  refine List.ext_getElem (by simp) (fun i h₁ _ => ?_)
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  exact h i (by simpa using h₁)

/-- In-range roots-array reads off the decoded relation: the machine read is the
abstract list's entry. -/
theorem wa_roots_of_rel {st : HState} {r : State V} (h : Rel st r) {L j : ℕ}
    (hrl : r.wlen "roots" = L) (hj : j < L) : r.wa "roots" j = st.roots.getD j 0 := by
  have hm : (List.range L).map (r.wa "roots") = st.roots := by
    rw [← h, decode_roots, hrl]
  have h1 := congrArg (fun l => l.getD j 0) hm
  rw [getD_map_lt (r.wa "roots") (0 : ℕ) (0 : ℕ) (List.range L) j (by simpa using hj),
    List.getD_eq_getElem?_getD] at h1
  simp [List.getElem?_range, hj] at h1
  exact h1

/-- Par reads through the decoded relation. -/
theorem wa_par_of_rel {st : HState} {r : State V} (h : Rel st r) (j : ℕ) :
    r.wa "par" j = st.par j := by
  have := congrFun (congrArg HState.par h) j
  simpa [decode_par] using this

/-! ## The p2 register and array inventory

Registers: `"n"` (decoded), `"L"` (roots logical length; pinned equal to
`wlen "roots"`), `"e"` (promotion-log logical count), `"t"` (scratch count),
`"j"` (scan index), `"r"` (current root id), `"b"` (live-test bit).
Arrays: the six layout arrays `par mrk deg chd rgt lft` (length `n`), `"roots"`
(exact logical length), `"elog"` (promotion log; `wlen` is capacity, register `"e"`
counts), `"rt2"` (compaction scratch).  Only `"roots"`, the six, and `"n"` are
decoded; `"elog"`/`"rt2"` and every scratch register are foreign to the decode. -/

/-- The live predicate: the NIL convention (`NILRoots` — a root's parent is 0; a
meld-consumed root's parent is its absorber). -/
def isLive (st : HState) : ℕ → Bool := fun x => st.par x == 0

/-- The filtered prefix of the combined source scanned so far: cells `j < k` of the
roots list (`j < L`) and the promotion log (`j ≥ L`), keeping the live entries. -/
def flt (st : HState) (elogR : ℕ → ℕ) (L k : ℕ) : List ℕ :=
  ((List.range k).map
    (fun j => if j < L then st.roots.getD j 0 else elogR (j - L))).filter (isLive st)

theorem flt_step (st : HState) (elogR : ℕ → ℕ) (L k : ℕ) :
    flt st elogR L (k + 1) =
      flt st elogR L k ++
        (if isLive st (if k < L then st.roots.getD k 0 else elogR (k - L))
         then [if k < L then st.roots.getD k 0 else elogR (k - L)] else []) := by
  rw [flt, flt, List.range_succ, List.map_append, List.map_singleton, List.filter_append,
    List.filter_cons]
  simp

theorem flt_len_le (st : HState) (elogR : ℕ → ℕ) (L k : ℕ) :
    (flt st elogR L k).length ≤ k := by
  unfold flt
  have h1 := List.length_filter_le (isLive st)
    (List.map (fun j => if j < L then st.roots.getD j 0 else elogR (j - L))
      (List.range k))
  rw [List.length_map, List.length_range] at h1
  exact h1

/-! ## The program texts -/

/-- **The stash loop**: scan cells `j < L + e` of the combined source (roots list for
`j < L`, promotion log for `j ≥ L`), stashing every live entry into `"rt2"` at
position `t`, `t` counting.  (Proved: `stashLoop_runs` — invariant `StashI`, cost
`≤ 8·(L+e) + 1`.) -/
def stashLoop : Stmt :=
  .while (lt (var "j") (add (var "L") (var "e")))
    (.seq
      (.ite (lt (var "j") (var "L"))
        (wset "r" (load "roots" (var "j")))
        (wset "r" (load "elog" (sub (var "j") (var "L")))))
      (.seq (.ite (eq (load "par" (var "r")) (lit 0))
                  (.seq (wstore "rt2" (var "t") (var "r"))
                        (wset "t" (add (var "t") (lit 1))))
                  skip)
            (wset "j" (add (var "j") (lit 1)))))

/-- **The copy-back loop**: refill the re-allocated roots array from `"rt2"`. -/
def copyLoop : Stmt :=
  .while (lt (var "j") (var "t"))
    (.seq (wset "r" (load "rt2" (var "j")))
      (.seq (wstore "roots" (var "j") (var "r"))
            (wset "j" (add (var "j") (lit 1)))))

/-- **The consolidation roots filter — the store-compaction loop.**  Allocates the
scratch, stashes the live entries of the combined source, re-allocates `"roots"` at
the live count, and copies back. -/
def rootsCompact : Stmt :=
  .seq (walloc "rt2" (add (var "L") (var "e")))
    (.seq (wset "t" (lit 0))
      (.seq (wset "j" (lit 0))
        (.seq stashLoop
          (.seq (walloc "roots" (var "t"))
            (.seq (wset "j" (lit 0)) copyLoop)))))

/-- **The insert op.**  O(1): append the new root id (register `"x"`) to the promotion
log and bump the log count.  The roots array is re-lengthed by the next `rootsCompact`. -/
def insertOp : Stmt :=
  .seq (wstore "elog" (var "e") (var "x")) (wset "e" (add (var "e") (lit 1)))

/-! ## The insert op's receipt -/

/-- **`insertOp` runs.**  The decode is untouched (the log and the count register are
foreign to it), the new cell lands at position `e` with the register's value, the
count bumps, and the op costs exactly `2`. -/
theorem insertOp_runs (st : HState) (r : State ℝ≥0) (e : ℕ)
    (hR : Rel st r) (hcap0 : 1 < r.cap) (hcapE : e + 1 < r.cap)
    (he : r.w "e" = e) (hb : e < r.wlen "elog") :
    Runs realOps insertOp r (fun r' =>
      Rel st r' ∧ r'.w "e" = e + 1 ∧ r'.wa "elog" e = r.w "x" ∧
      (∀ j, j ≠ e → r'.wa "elog" j = r.wa "elog" j) ∧ r'.cost = r.cost + 2) := by
  unfold insertOp
  have hadd : evalW ((r.storeW "elog" e (r.w "x")).charge 1)
      (add (var "e") (lit 1)) = some (e + 1) := by
    refine evalW_add_of ?_
      (evalW_lit_of (by rw [cap_charge, cap_storeW]; exact hcap0))
      (by rw [cap_charge, cap_storeW]; exact hcapE)
    rw [evalW_var, w_charge, w_storeW, he]
  refine runs_seq (runs_wstore (hi := by rw [evalW_var, he]) (he := by rw [evalW_var]) hb
    (runs_wset hadd ?_))
  set s2 := (((r.storeW "elog" e (r.w "x")).charge 1).setW "e" (e + 1)).charge 1 with hs2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Rel st s2
    show decode s2 = st
    rw [hs2, decode_charge, decode_w_other _ (by decide : ("e" : String) ≠ "n"),
      decode_charge, decode_storeW_foreign r (by decide) e (r.w "x")]
    exact hR
  · -- w "e" = e + 1
    rw [hs2, w_charge, w_setW, if_pos (by simp)]
  · -- wa "elog" e = r.w "x"
    rw [hs2, wa_charge, wa_setW, wa_charge, wa_storeW, if_pos (by simp)]
  · -- unchanged elsewhere
    intro j hj
    show s2.wa "elog" j = r.wa "elog" j
    rw [hs2, wa_charge, wa_setW, wa_charge, wa_storeW, if_neg (by simp [hj])]
  · -- cost (the rw chain closes by rfl on the ℕ successors)
    rw [hs2, cost_charge, cost_setW, cost_charge, cost_storeW]

/-! ## The copy-back loop's receipt -/

/-- The copy-loop invariant: `k` cells refilled from `"rt2"`, the decode riding the
splice chain at the re-lengthed roots array. -/
def CopyI (r : State V) (st : HState) (rd : ℕ → ℕ) (t k : ℕ) (s : State V) : Prop :=
  s.w "j" = k ∧ s.w "t" = t ∧ k ≤ t ∧
  Rel {st with roots := (List.range t).map (fun j => if j < k then rd j else 0)} s ∧
  (∀ j, s.wa "roots" j = if j < k then rd j else 0) ∧
  (∀ j, s.wa "rt2" j = rd j) ∧
  s.wlen "roots" = t ∧ s.wlen "rt2" = r.wlen "rt2" ∧
  s.cap = r.cap ∧ s.cost ≤ r.cost + 4 * k

/-- **The copy-back loop runs** — the landed `decode_storeW_roots` congruence carries
every step: each store splices the decoded roots list at the written index, so the
decoded list climbs from the zero-fill to `range t ↦ rd`. -/
theorem copyLoop_runs (r : State ℝ≥0) (st : HState) (rd : ℕ → ℕ) (t : ℕ)
    (hR : Rel {st with roots := (List.range t).map (fun _ => (0 : ℕ))} r)
    (hj0 : r.w "j" = 0) (ht0 : r.w "t" = t) (hwa0 : ∀ j, r.wa "roots" j = 0)
    (hcap0 : 1 < r.cap) (hrl : r.wlen "roots" = t) (hrt2L : t ≤ r.wlen "rt2")
    (hrt2 : ∀ j, r.wa "rt2" j = rd j) (hcapT : t < r.cap) :
    Runs realOps copyLoop r (fun r' =>
      (∀ j, j < t → r'.wa "roots" j = rd j) ∧
      (∀ j, r'.wa "rt2" j = rd j) ∧
      r'.wlen "roots" = t ∧
      Rel {st with roots := (List.range t).map rd} r' ∧
      r'.cap = r.cap ∧ r'.cost ≤ r.cost + 4 * t + 1) := by
  unfold copyLoop
  refine runs_while (I := CopyI r st rd t) (K := t)
    (Q := fun r' => (∀ j, j < t → r'.wa "roots" j = rd j) ∧
      (∀ j, r'.wa "rt2" j = rd j) ∧ r'.wlen "roots" = t ∧
      Rel {st with roots := (List.range t).map rd} r' ∧
      r'.cap = r.cap ∧ r'.cost ≤ r.cost + 4 * t + 1)
    ?hstep ?hexit r ?entry
  case hstep =>
    intro k hk s his
    obtain ⟨hj, hwt, hkt, hrel, hwa, hrt2', hrl', hrt2L', hcap, hcost⟩ := his
    have hcap' : 1 < s.cap := by rw [hcap]; exact hcap0
    have htest : evalW s (lt (var "j") (var "t")) = some 1 := by
      rw [evalW_lt_of (x := k) (y := t) (by rw [evalW_var, hj]) (by rw [evalW_var, hwt])
        hcap']
      simp [show k < t from hk]
    refine ⟨1, htest, one_ne_zero, ?_⟩
    -- wset "r" (load "rt2" (var "j"))
    have hld : evalW (s.charge 1) (load "rt2" (var "j")) = some (rd k) := by
      rw [evalW_load_of (by rw [evalW_var, w_charge, hj])
        (by rw [wlen_charge, hrt2L']; exact lt_of_lt_of_le hk hrt2L), wa_charge, hrt2' k]
    refine runs_seq (runs_wset hld ?_)
    set s1 := ((s.charge 1).setW "r" (rd k)).charge 1 with hs1
    have hwj1 : s1.w "j" = k := by
      rw [hs1, w_charge, w_setW, if_neg (by decide : ("j" : String) ≠ "r"), w_charge]
      exact hj
    have hwa1 : ∀ j, s1.wa "roots" j = if j < k then rd j else 0 := by
      intro j; rw [hs1, wa_charge, wa_setW, wa_charge]; exact hwa j
    have hrt21 : ∀ j, s1.wa "rt2" j = rd j := by
      intro j; rw [hs1, wa_charge, wa_setW, wa_charge]; exact hrt2' j
    have hrl1 : s1.wlen "roots" = t := by
      rw [hs1, wlen_charge, wlen_setW, wlen_charge]; exact hrl'
    have hcap1 : s1.cap = r.cap := by
      rw [hs1, cap_charge, cap_setW, cap_charge]; exact hcap
    have hrel1 : Rel {st with roots := (List.range t).map (fun j => if j < k then rd j else 0)} s1 := by
      show decode s1 = {st with roots := (List.range t).map (fun j => if j < k then rd j else 0)}
      rw [hs1, decode_charge, decode_w_other _ (by decide : ("r" : String) ≠ "n"),
        decode_charge]
      exact hrel
    -- wstore "roots" (var "j") (var "r")
    have hb1 : k < s1.wlen "roots" := by rw [hrl1]; exact hk
    have hij : evalW s1 (var "j") = some k := by rw [evalW_var, hwj1]
    have hir : evalW s1 (var "r") = some (rd k) := by
      rw [evalW_var, hs1, w_charge, w_setW, w_charge, if_pos (by simp)]
    refine runs_seq (runs_wstore hij hir hb1 ?_)
    set s2 := (s1.storeW "roots" k (rd k)).charge 1 with hs2
    have hwl2 : s2.wlen "roots" = t := by
      rw [hs2, wlen_charge, wlen_storeW]; exact hrl1
    have hrt22 : ∀ j, s2.wa "rt2" j = rd j := by
      intro j
      rw [hs2, wa_charge, wa_storeW, if_neg (by simp)]
      exact hrt21 j
    have hwa2 : ∀ j, s2.wa "roots" j = if j = k then rd k else (if j < k then rd j else 0) := by
      intro j
      rw [hs2, wa_charge, wa_storeW, hwa1 j]
      by_cases hjk : j = k
      · subst hjk; simp
      · have hcond : ¬ ("roots" = "roots" ∧ j = k) := by simp [hjk]
        rw [if_neg hcond, if_neg hjk]
    have hcap2 : s2.cap = r.cap := by rw [hs2, cap_charge, cap_storeW]; exact hcap1
    have hwj2 : s2.w "j" = k := by
      rw [hs2, w_charge, w_storeW, hs1, w_charge, w_setW, w_charge,
        if_neg (by decide : ("j" : String) ≠ "r")]
      exact hj
    have hwt2 : s2.w "t" = t := by
      rw [hs2, w_charge, w_storeW, hs1, w_charge, w_setW, w_charge,
        if_neg (by decide : ("t" : String) ≠ "r")]
      exact hwt
    have hwrt2 : s2.wlen "rt2" = r.wlen "rt2" := by
      rw [hs2, wlen_charge, wlen_storeW, hs1, wlen_charge, wlen_setW, wlen_charge]
      exact hrt2L'
    have hc2 : s2.cost = s.cost + 3 := by
      rw [hs2, cost_charge, cost_storeW, hs1, cost_charge, cost_setW, cost_charge]
    -- wset "j" (add (var "j") (lit 1))
    have hj2 : evalW s2 (var "j") = some k := by rw [evalW_var, hwj2]
    have hadd : evalW s2 (add (var "j") (lit 1)) = some (k + 1) := by
      refine evalW_add_of hj2 (evalW_lit_of (by rw [hcap2]; exact hcap0)) ?_
      rw [hcap2]
      have := hcapT
      have := hk
      omega
    refine runs_wset hadd ?_
    set s3 := (s2.setW "j" (k + 1)).charge 1 with hs3
    have c1 : s3.w "j" = k + 1 := by
      rw [hs3, w_charge, w_setW, if_pos (by simp)]
    have c2 : s3.w "t" = t := by
      rw [hs3, w_charge, w_setW, if_neg (by decide : ("t" : String) ≠ "j")]
      exact hwt2
    have c3 : k + 1 ≤ t := by have := hk; omega
    have c4 : Rel {st with roots := (List.range t).map (fun j => if j < k + 1 then rd j else 0)}
        s3 := by
      show decode s3 = {st with roots := (List.range t).map (fun j => if j < k + 1 then rd j else 0)}
      rw [hs3, decode_charge, decode_w_other _ (by decide : ("j" : String) ≠ "n") (k + 1),
        decode_charge, decode_storeW_roots s1 k (rd k), hrel1]
      have hwlr : (List.range (s1.wlen "roots")).map
          (fun i => if i = k then rd k else s1.wa "roots" i)
          = (List.range t).map (fun i => if i = k then rd k else (if i < k then rd i else 0)) := by
        rw [hrl1]
        refine map_range_congr (fun i _ => ?_)
        rw [hwa1 i]
      rw [hwlr]
      have hpts : ∀ i, i < t →
          (if i = k then rd k else (if i < k then rd i else 0))
            = (if i < k + 1 then rd i else 0) := by
        intro i _
        rcases Nat.lt_trichotomy i k with h | h | h
        · rw [if_neg (by omega : ¬ (i = k)), if_pos h, if_pos (by omega : i < k + 1)]
        · subst h; rw [if_pos (by simp), if_pos (by omega)]
        · have h1 : ¬ (i = k) := by omega
          have h3 : ¬ (i < k) := by omega
          have h2 : ¬ (i < k + 1) := by omega
          rw [if_neg h1, if_neg h3, if_neg h2]
      rw [map_range_congr hpts]
    have c5 : ∀ j, s3.wa "roots" j = if j < k + 1 then rd j else 0 := by
      intro j
      rw [hs3, wa_charge, wa_setW, hwa2 j]
      rcases Nat.lt_trichotomy j k with h | h | h
      · rw [if_neg (by simp [show ¬ (j = k) from by omega]), if_pos h,
          if_pos (by omega : j < k + 1)]
      · subst h; rw [if_pos (by simp), if_pos (by omega)]
      · have h1 : ¬ (j = k) := by omega
        have h3 : ¬ (j < k) := by omega
        have h2 : ¬ (j < k + 1) := by omega
        rw [if_neg h1, if_neg h3, if_neg h2]
    have c6 : ∀ j, s3.wa "rt2" j = rd j := by
      intro j
      rw [hs3, wa_charge, wa_setW]
      exact hrt22 j
    have c7 : s3.wlen "roots" = t := by
      rw [hs3, wlen_charge, wlen_setW]
      exact hwl2
    have c8 : s3.wlen "rt2" = r.wlen "rt2" := by
      rw [hs3, wlen_charge, wlen_setW]
      exact hwrt2
    have c9 : s3.cap = r.cap ∧ s3.cost ≤ r.cost + 4 * (k + 1) := by
      refine ⟨by rw [hs3, cap_charge, cap_setW]; exact hcap2, ?_⟩
      rw [hs3, cost_charge, cost_setW]
      have h1 := hcost
      have h4 := hc2
      omega
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩
  case hexit =>
    intro s his
    obtain ⟨hj, hwt, hkt, hrel, hwa, hrt2', hrl', hrt2L', hcap, hcost⟩ := his
    have hcap' : 1 < s.cap := by rw [hcap]; exact hcap0
    have htest : evalW s (lt (var "j") (var "t")) = some 0 := by
      rw [evalW_lt_of (x := t) (y := t) (by rw [evalW_var, hj]) (by rw [evalW_var, hwt])
        hcap']
      simp [show ¬ (t < t) from lt_irrefl t]
    have q1 : ∀ j, j < t → ((s.charge 1).wa "roots") j = rd j := fun j hjl => by
      rw [wa_charge, hwa j, if_pos hjl]
    have q2 : ∀ j, ((s.charge 1).wa "rt2") j = rd j := fun j => by
      rw [wa_charge]; exact hrt2' j
    have q3 : ((s.charge 1).wlen "roots") = t := by rw [wlen_charge]; exact hrl'
    have q4 : Rel {st with roots := (List.range t).map rd} (s.charge 1) := by
      have hmaps : (List.range t).map (fun j => if j < t then rd j else 0)
          = (List.range t).map rd := by
        refine map_range_congr (fun i hi => ?_)
        rw [if_pos hi]
      rw [← hmaps]
      exact hrel
    have q6 : (s.charge 1).cost ≤ r.cost + 4 * t + 1 := by
      rw [cost_charge]
      have := hcost
      omega
    exact ⟨htest, q1, q2, q3, q4, hcap, q6⟩
  case entry =>
    have hmaps0 : (List.range t).map (fun j => if j < 0 then rd j else 0)
        = (List.range t).map (fun _ => (0 : ℕ)) := by
      refine map_range_congr (fun j _ => ?_); simp
    have h4 : Rel {st with roots := (List.range t).map (fun j => if j < 0 then rd j else 0)}
        r := by
      rw [hmaps0]
      exact hR
    have h5 : ∀ j, r.wa "roots" j = if j < 0 then rd j else 0 := fun j => by
      rw [hwa0 j]
      simp
    exact ⟨hj0, ht0, Nat.zero_le t, h4, h5, hrt2, hrl, rfl, rfl, le_refl _⟩

/-! ## The stash loop's receipt -/

/-- A register read survives an allocation (`allocW` touches only `wa`/`wlen`/`space`). -/
theorem w_allocW (s : State V) (arr : String) (k : ℕ) (y : String) :
    (s.allocW arr k).w y = s.w y := rfl

/-- Evaluate a truncated subtraction (no word-size check: the result is below the
minuend). -/
theorem evalW_sub_of {s : State V} {a b : WExpr} {x y : ℕ}
    (ha : evalW s a = some x) (hb : evalW s b = some y) :
    evalW s (.sub a b) = some (x - y) := by
  simp [evalW, ha, hb]

/-- `flt` at zero scans is empty. -/
theorem flt_zero (st : HState) (elogR : ℕ → ℕ) (L : ℕ) : flt st elogR L 0 = [] := by
  unfold flt; simp

/-- **The stash-loop invariant** (the module-docstring sketch): `k` cells of the combined
source scanned (the roots list for `j < L`, the promotion log above), the live prefix
sitting in `"rt2"` (cell agreement in total-`getD` form: in range it is the cell, and
`"rt2"` is zeroed scratch), the decode untouched, `"L"`/`"e"` pinned, the log reads
stable, cost `≤ 8·k`. -/
def StashI (r : State V) (st : HState) (elogR : ℕ → ℕ) (L e k : ℕ) (s : State V) : Prop :=
  s.w "j" = k ∧
  s.w "t" = (flt st elogR L k).length ∧
  Rel st s ∧
  (∀ j, j < (flt st elogR L k).length →
    s.wa "rt2" j = (flt st elogR L k).getD j 0) ∧
  s.wlen "rt2" = L + e ∧
  s.wlen "roots" = L ∧
  s.wlen "par" = r.wlen "par" ∧
  s.wlen "elog" = r.wlen "elog" ∧
  s.w "L" = L ∧
  s.w "e" = e ∧
  (∀ i, s.wa "elog" i = elogR i) ∧
  s.cap = r.cap ∧
  s.cost ≤ r.cost + 8 * k

/-- **The stash loop runs** — the named remainder: `L + e` cells of the combined source
scanned (the select `ite` reads cell `j` of the roots list below `L`, of the promotion
log above; `wa_roots_of_rel`/`wa_par_of_rel` carry the reads through the decode), the
live prefix parked in `"rt2"` at the count register, the decode untouched throughout
(every stash store is foreign, every register write non-`n`), cost `≤ 8·(L+e) + 1`. -/
theorem stashLoop_runs (r : State ℝ≥0) (st : HState) (elogR : ℕ → ℕ) (L e : ℕ)
    (hR : Rel st r) (hcap0 : 1 < r.cap)
    (hj0 : r.w "j" = 0) (ht0 : r.w "t" = 0)
    (hL : r.w "L" = L) (he : r.w "e" = e)
    (hrl : r.wlen "roots" = L) (hrt2L : r.wlen "rt2" = L + e)
    (helog0 : ∀ i, r.wa "elog" i = elogR i)
    (hlogcap : ∀ i, i < e → i < r.wlen "elog")
    (hid : (∀ j, j < L → st.roots.getD j 0 < r.wlen "par") ∧
      (∀ i, i < e → elogR i < r.wlen "par"))
    (hcap : L + e < r.cap) :
    Runs realOps stashLoop r (fun r' =>
      r'.w "j" = L + e ∧
      r'.w "t" = (flt st elogR L (L + e)).length ∧
      Rel st r' ∧
      (∀ j, j < (flt st elogR L (L + e)).length →
        r'.wa "rt2" j = (flt st elogR L (L + e)).getD j 0) ∧
      r'.wlen "rt2" = L + e ∧ r'.wlen "roots" = L ∧
      r'.w "L" = L ∧ r'.w "e" = e ∧ (∀ i, r'.wa "elog" i = elogR i) ∧
      r'.cap = r.cap ∧ r'.cost ≤ r.cost + 8 * (L + e) + 1) := by
  unfold stashLoop
  refine runs_while (I := StashI r st elogR L e) (K := L + e) (Q := fun r' =>
      r'.w "j" = L + e ∧
      r'.w "t" = (flt st elogR L (L + e)).length ∧
      Rel st r' ∧
      (∀ j, j < (flt st elogR L (L + e)).length →
        r'.wa "rt2" j = (flt st elogR L (L + e)).getD j 0) ∧
      r'.wlen "rt2" = L + e ∧ r'.wlen "roots" = L ∧
      r'.w "L" = L ∧ r'.w "e" = e ∧ (∀ i, r'.wa "elog" i = elogR i) ∧
      r'.cap = r.cap ∧ r'.cost ≤ r.cost + 8 * (L + e) + 1)
    ?hstep ?hexit r ?entry
  case hstep =>
    intro k hk s his
    obtain ⟨hj, hwt, hrel, hwa, hwl2, hrl', hwlP, hwlE, hL', he', helog, hcapS, hcost⟩ := his
    set t := (flt st elogR L k).length with htd
    have hcap' : 1 < s.cap := by rw [hcapS]; exact hcap0
    have hbLe : evalW s (add (var "L") (var "e")) = some (L + e) := by
      refine evalW_add_of (x := L) (y := e) (by rw [evalW_var, hL']) (by rw [evalW_var, he']) ?_
      rw [hcapS]; exact hcap
    have hte : evalW s (lt (var "j") (add (var "L") (var "e"))) = some 1 := by
      rw [evalW_lt_of (x := k) (y := L + e) (by rw [evalW_var, hj]) hbLe hcap']
      simp [hk]
    refine ⟨1, hte, one_ne_zero, ?_⟩
    -- The shared tail (live-test + stash + count) from the post-select state; the select
    -- costs the while test, its own test and the register write: `s.cost + 3`.
    have htail : ∀ (v : ℕ) (s1 : State ℝ≥0),
        v < r.wlen "par" →
        (if k < L then st.roots.getD k 0 else elogR (k - L)) = v →
        s1.w "r" = v → s1.w "j" = k → s1.w "t" = t →
        Rel st s1 → (∀ j, s1.wa "rt2" j = s.wa "rt2" j) →
        s1.wlen "rt2" = L + e → s1.wlen "roots" = L →
        s1.wlen "par" = r.wlen "par" → s1.wlen "elog" = r.wlen "elog" →
        s1.w "L" = L → s1.w "e" = e → (∀ i, s1.wa "elog" i = elogR i) →
        s1.cap = r.cap → s1.cost = s.cost + 3 →
        Runs realOps
          (.seq (.ite (eq (load "par" (var "r")) (lit 0))
              (.seq (wstore "rt2" (var "t") (var "r"))
                (wset "t" (add (var "t") (lit 1))))
              skip)
            (.wset "j" (add (var "j") (lit 1))))
          s1 (StashI r st elogR L e (k + 1)) := by
      intro v s1 hv hsrcv hr1 hj1 hwt1 hrel1 hwa1 hwl21 hrl1 hwlP1 hwlE1 hL1 he1 helog1
        hcap1 hcost1
      have hcap1' : 1 < s1.cap := by rw [hcap1]; exact hcap0
      have htL : t ≤ k := flt_len_le st elogR L k
      have hparv : s1.wa "par" v = st.par v := wa_par_of_rel hrel1 v
      have hldp : evalW s1 (load "par" (var "r")) = some (s1.wa "par" v) := by
        rw [evalW_load_of (by rw [evalW_var, hr1]) (by rw [hwlP1]; exact hv)]
      have hc2 : evalW s1 (eq (load "par" (var "r")) (lit 0))
          = some (if s1.wa "par" v = 0 then 1 else 0) := by
        rw [evalW_eq_of hldp (evalW_lit_of (by have := hcap1; omega)) hcap1']
      have hlivB : isLive st v = true ↔ st.par v = 0 := by simp [isLive]
      by_cases hpv : st.par v = 0
      · -- live: stash the cell
        have hliv : isLive st v = true := hlivB.mpr hpv
        have hc2' : evalW s1 (eq (load "par" (var "r")) (lit 0)) = some 1 := by
          rw [hc2, hparv, if_pos hpv]
        have hlenk1 : (flt st elogR L (k + 1)).length = t + 1 := by
          rw [flt_step, hsrcv, if_pos hliv, List.length_append, ← htd]; simp
        refine runs_seq (runs_ite_true hc2' (by decide) ?_)
        refine runs_seq (runs_wstore (hi := by rw [evalW_var, w_charge, hwt1])
          (he := by rw [evalW_var, w_charge, hr1]) (hj := by rw [wlen_charge, hwl21]; omega) ?_)
        set s2 := ((s1.charge 1).storeW "rt2" t v).charge 1 with hs2
        have hwt2 : s2.w "t" = t := by rw [hs2, w_charge, w_storeW, w_charge, hwt1]
        have hcap2 : s2.cap = r.cap := by rw [hs2, cap_charge, cap_storeW, cap_charge, hcap1]
        have hwa2 : ∀ j, s2.wa "rt2" j = if j = t then v else s.wa "rt2" j := by
          intro j
          rw [hs2, wa_charge, wa_storeW, wa_charge, hwa1]
          by_cases hjt : j = t
          · simp [hjt]
          · simp [hjt]
        have hcost2 : s2.cost = s1.cost + 2 := by
          rw [hs2, cost_charge, cost_storeW, cost_charge]
        have hadd : evalW s2 (add (var "t") (lit 1)) = some (t + 1) := by
          refine evalW_add_of (x := t) (y := 1) (by rw [evalW_var, hwt2])
            (evalW_lit_of (by rw [hcap2]; omega)) ?_
          rw [hcap2]; omega
        refine runs_wset hadd ?_
        set s3 := (s2.setW "t" (t + 1)).charge 1 with hs3
        have hwt3 : s3.w "t" = t + 1 := by rw [hs3, w_charge, w_setW, if_pos (by simp)]
        have hj3' : s3.w "j" = k := by
          rw [hs3, w_charge, w_setW, if_neg (by decide : ("j" : String) ≠ "t"), hs2,
            w_charge, w_storeW, w_charge, hj1]
        have hL3' : s3.w "L" = L := by
          rw [hs3, w_charge, w_setW, if_neg (by decide : ("L" : String) ≠ "t"), hs2,
            w_charge, w_storeW, w_charge, hL1]
        have he3' : s3.w "e" = e := by
          rw [hs3, w_charge, w_setW, if_neg (by decide : ("e" : String) ≠ "t"), hs2,
            w_charge, w_storeW, w_charge, he1]
        have hwl23 : s3.wlen "rt2" = L + e := by
          rw [hs3, wlen_charge, wlen_setW, hs2, wlen_charge, wlen_storeW, wlen_charge]
          exact hwl21
        have hrl3' : s3.wlen "roots" = L := by
          rw [hs3, wlen_charge, wlen_setW, hs2, wlen_charge, wlen_storeW, wlen_charge]
          exact hrl1
        have hwlP3' : s3.wlen "par" = r.wlen "par" := by
          rw [hs3, wlen_charge, wlen_setW, hs2, wlen_charge, wlen_storeW, wlen_charge]
          exact hwlP1
        have hwlE3' : s3.wlen "elog" = r.wlen "elog" := by
          rw [hs3, wlen_charge, wlen_setW, hs2, wlen_charge, wlen_storeW, wlen_charge]
          exact hwlE1
        have helog3 : ∀ i, s3.wa "elog" i = elogR i := by
          intro i
          rw [hs3, wa_charge, wa_setW, hs2, wa_charge, wa_storeW,
            if_neg (by simp), wa_charge]
          exact helog1 i
        have hrel3 : Rel st s3 := by
          show decode s3 = st
          rw [hs3, decode_charge, decode_w_other _ (by decide : ("t" : String) ≠ "n"), hs2,
            decode_charge, decode_storeW_foreign _ (by decide) t v, decode_charge]
          exact hrel1
        have hcap3' : s3.cap = r.cap := by
          rw [hs3, cap_charge, cap_setW, hs2, cap_charge, cap_storeW, cap_charge, hcap1]
        have hadd2 : evalW s3 (add (var "j") (lit 1)) = some (k + 1) := by
          refine evalW_add_of (x := k) (y := 1) (by rw [evalW_var, hj3'])
            (evalW_lit_of (by rw [hcap3']; omega)) ?_
          rw [hcap3']; omega
        refine runs_wset hadd2 ?_
        set s4 := (s3.setW "j" (k + 1)).charge 1 with hs4
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hs4, w_charge, w_setW, if_pos (by simp)]
        · rw [hs4, w_charge, w_setW, if_neg (by decide : ("t" : String) ≠ "j"), hwt3, hlenk1]
        · show decode s4 = st
          rw [hs4, decode_charge, decode_w_other _ (by decide : ("j" : String) ≠ "n"), hs3,
            decode_charge, decode_w_other _ (by decide : ("t" : String) ≠ "n"), hs2,
            decode_charge, decode_storeW_foreign _ (by decide) t v, decode_charge]
          exact hrel1
        · intro j hjl
          rw [hlenk1] at hjl
          rw [hs4, wa_charge, wa_setW, hs3, wa_charge, wa_setW, hwa2 j, flt_step, hsrcv,
            if_pos hliv]
          rcases Nat.lt_or_ge j t with hjt | hjt
          · rw [if_neg (by omega : ¬(j = t)), List.getD_append _ _ _ _ (by omega)]
            exact hwa j (by omega)
          · have hjte : j = t := by omega
            subst hjte
            rw [if_pos (by simp), List.getD_append_right _ _ _ _ (by omega), htd]
            simp
        · rw [hs4, wlen_charge, wlen_setW, wlen_charge]; exact hwl23
        · rw [hs4, wlen_charge, wlen_setW, wlen_charge]; exact hrl3'
        · rw [hs4, wlen_charge, wlen_setW, wlen_charge]; exact hwlP3'
        · rw [hs4, wlen_charge, wlen_setW, wlen_charge]; exact hwlE3'
        · rw [hs4, w_charge, w_setW, if_neg (by decide : ("L" : String) ≠ "j")]; exact hL3'
        · rw [hs4, w_charge, w_setW, if_neg (by decide : ("e" : String) ≠ "j")]; exact he3'
        · intro i
          rw [hs4, wa_charge, wa_setW]; exact helog3 i
        · rw [hs4, cap_charge, cap_setW]; exact hcap3'
        · rw [hs4, cost_charge, cost_setW, hs3, cost_charge, cost_setW, hcost2, hcost1]
          omega
      · -- dead: skip the stash
        have hdead : ¬(isLive st v = true) := by
          simp [isLive, hpv]
        have hc2'' : evalW s1 (eq (load "par" (var "r")) (lit 0)) = some 0 := by
          rw [hc2, hparv, if_neg hpv]
        refine runs_seq (runs_ite_false hc2'' ?_)
        refine runs_skip ?_
        set s2 := (s1.charge 1).charge 1 with hs2
        have hwt2 : s2.w "t" = t := by rw [hs2, w_charge, w_charge, hwt1]
        have hj2 : s2.w "j" = k := by rw [hs2, w_charge, w_charge, hj1]
        have hL2 : s2.w "L" = L := by rw [hs2, w_charge, w_charge, hL1]
        have he2 : s2.w "e" = e := by rw [hs2, w_charge, w_charge, he1]
        have hwl22 : s2.wlen "rt2" = L + e := by
          rw [hs2, wlen_charge, wlen_charge]; exact hwl21
        have hrl2 : s2.wlen "roots" = L := by
          rw [hs2, wlen_charge, wlen_charge]; exact hrl1
        have hwlP2 : s2.wlen "par" = r.wlen "par" := by
          rw [hs2, wlen_charge, wlen_charge]; exact hwlP1
        have hwlE2 : s2.wlen "elog" = r.wlen "elog" := by
          rw [hs2, wlen_charge, wlen_charge]; exact hwlE1
        have helog2 : ∀ i, s2.wa "elog" i = elogR i := by
          intro i; rw [hs2, wa_charge, wa_charge]; exact helog1 i
        have hrel2 : Rel st s2 := by
          show decode s2 = st
          rw [hs2, decode_charge, decode_charge]
          exact hrel1
        have hcap2 : s2.cap = r.cap := by rw [hs2, cap_charge, cap_charge]; exact hcap1
        have hcost2 : s2.cost = s1.cost + 2 := by rw [hs2, cost_charge, cost_charge]
        have hadd : evalW s2 (add (var "j") (lit 1)) = some (k + 1) := by
          refine evalW_add_of (x := k) (y := 1) (by rw [evalW_var, hj2])
            (evalW_lit_of (by rw [hcap2]; omega)) ?_
          rw [hcap2]; omega
        refine runs_wset hadd ?_
        set s3 := (s2.setW "j" (k + 1)).charge 1 with hs3
        have hfltd : flt st elogR L (k + 1) = flt st elogR L k := by
          rw [flt_step, hsrcv, if_neg hdead]; simp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hs3, w_charge, w_setW, if_pos (by simp)]
        · rw [hs3, w_charge, w_setW, if_neg (by decide : ("t" : String) ≠ "j"), hwt2, hfltd,
            ← htd]
        · show decode s3 = st
          rw [hs3, decode_charge, decode_w_other _ (by decide : ("j" : String) ≠ "n"), hs2,
            decode_charge, decode_charge]
          exact hrel1
        · intro j hjl
          rw [hfltd] at hjl ⊢
          rw [hs3, wa_charge, wa_setW, hs2, wa_charge, wa_charge, hwa1]
          exact hwa j hjl
        · rw [hs3, wlen_charge, wlen_setW, wlen_charge]; exact hwl22
        · rw [hs3, wlen_charge, wlen_setW, wlen_charge]; exact hrl2
        · rw [hs3, wlen_charge, wlen_setW, wlen_charge]; exact hwlP2
        · rw [hs3, wlen_charge, wlen_setW, wlen_charge]; exact hwlE2
        · rw [hs3, w_charge, w_setW, if_neg (by decide : ("L" : String) ≠ "j")]; exact hL2
        · rw [hs3, w_charge, w_setW, if_neg (by decide : ("e" : String) ≠ "j")]; exact he2
        · intro i
          rw [hs3, wa_charge, wa_setW]; exact helog2 i
        · rw [hs3, cap_charge, cap_setW]; exact hcap2
        · rw [hs3, cost_charge, cost_setW, hcost2, hcost1]
          omega
    rcases Nat.lt_or_ge k L with hkL | hkL
    · -- the select reads the roots cell
      have hc1 : evalW s (lt (var "j") (var "L")) = some 1 := by
        rw [evalW_lt_of (x := k) (y := L) (by rw [evalW_var, hj]) (by rw [evalW_var, hL']) hcap']
        simp [hkL]
      have hldR : evalW ((s.charge 1).charge 1) (load "roots" (var "j"))
          = some (((s.charge 1).charge 1).wa "roots" k) := by
        rw [evalW_load_of (by rw [evalW_var, w_charge, w_charge, hj])
          (by rw [wlen_charge, wlen_charge, hrl']; exact hkL)]
      have hrelR : Rel st
          ((((s.charge 1).charge 1).setW "r" (((s.charge 1).charge 1).wa "roots" k)).charge 1) := by
        show decode _ = st
        rw [decode_charge, decode_w_other _ (by decide : ("r" : String) ≠ "n"), decode_charge,
          decode_charge]
        exact hrel
      have hcostR : ((((s.charge 1).charge 1).setW "r"
            (((s.charge 1).charge 1).wa "roots" k)).charge 1).cost = s.cost + 3 := by
        rw [cost_charge, cost_setW, cost_charge, cost_charge]
      refine runs_seq (runs_ite_true hc1 one_ne_zero ?_)
      refine runs_wset hldR ?_
      refine htail (((s.charge 1).charge 1).wa "roots" k) _
        (by rw [wa_charge, wa_charge, wa_roots_of_rel hrel hrl' hkL]; exact hid.1 k hkL)
        (by rw [if_pos hkL, wa_charge, wa_charge, wa_roots_of_rel hrel hrl' hkL])
        (by simp [State.charge, State.setW])
        (by simp [State.charge, State.setW, hj])
        (by simp [State.charge, State.setW, hwt])
        hrelR
        (by intro j; simp [State.charge, State.setW])
        (by simp [State.charge, State.setW, hwl2])
        (by simp [State.charge, State.setW, hrl'])
        (by simp [State.charge, State.setW, hwlP])
        (by simp [State.charge, State.setW, hwlE])
        (by simp [State.charge, State.setW, hL'])
        (by simp [State.charge, State.setW, he'])
        (by intro i; simp [State.charge, State.setW, helog])
        (by simp [State.charge, State.setW, hcapS])
        hcostR
    · -- the select reads the promotion-log cell
      have hc1' : evalW s (lt (var "j") (var "L")) = some 0 := by
        rw [evalW_lt_of (x := k) (y := L) (by rw [evalW_var, hj]) (by rw [evalW_var, hL']) hcap']
        simp [hkL]
      have hsub : evalW ((s.charge 1).charge 1) (sub (var "j") (var "L")) = some (k - L) := by
        refine evalW_sub_of (by rw [evalW_var, w_charge, w_charge, hj])
          (by rw [evalW_var, w_charge, w_charge, hL'])
      have hld : evalW ((s.charge 1).charge 1) (load "elog" (sub (var "j") (var "L")))
          = some (elogR (k - L)) := by
        rw [evalW_load_of hsub
          (by rw [wlen_charge, wlen_charge, hwlE]; exact hlogcap (k - L) (by omega)),
          wa_charge, wa_charge, helog]
      have hrelL : Rel st ((((s.charge 1).charge 1).setW "r" (elogR (k - L))).charge 1) := by
        show decode _ = st
        rw [decode_charge, decode_w_other _ (by decide : ("r" : String) ≠ "n"), decode_charge,
          decode_charge]
        exact hrel
      have hcostL : ((((s.charge 1).charge 1).setW "r" (elogR (k - L))).charge 1).cost
          = s.cost + 3 := by
        rw [cost_charge, cost_setW, cost_charge, cost_charge]
      refine runs_seq (runs_ite_false hc1' ?_)
      refine runs_wset hld ?_
      refine htail (elogR (k - L)) _ (hid.2 (k - L) (by omega))
        (by rw [if_neg (Nat.not_lt.mpr hkL)])
        (by simp [State.charge, State.setW])
        (by simp [State.charge, State.setW, hj])
        (by simp [State.charge, State.setW, hwt])
        hrelL
        (by intro j; simp [State.charge, State.setW])
        (by simp [State.charge, State.setW, hwl2])
        (by simp [State.charge, State.setW, hrl'])
        (by simp [State.charge, State.setW, hwlP])
        (by simp [State.charge, State.setW, hwlE])
        (by simp [State.charge, State.setW, hL'])
        (by simp [State.charge, State.setW, he'])
        (by intro i; simp [State.charge, State.setW, helog])
        (by simp [State.charge, State.setW, hcapS])
        hcostL
  case hexit =>
    intro s his
    obtain ⟨hj, hwt, hrel, hwa, hwl2, hrl', hwlP, hwlE, hL', he', helog, hcapS, hcost⟩ := his
    have hcap' : 1 < s.cap := by rw [hcapS]; exact hcap0
    have hbLe : evalW s (add (var "L") (var "e")) = some (L + e) := by
      refine evalW_add_of (x := L) (y := e) (by rw [evalW_var, hL']) (by rw [evalW_var, he']) ?_
      rw [hcapS]; exact hcap
    have hte : evalW s (lt (var "j") (add (var "L") (var "e"))) = some 0 := by
      rw [evalW_lt_of (x := L + e) (y := L + e) (by rw [evalW_var, hj]) hbLe hcap']
      simp
    refine ⟨hte, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w_charge, hj]
    · rw [w_charge]; exact hwt
    · show decode (s.charge 1) = st
      rw [decode_charge]
      exact hrel
    · intro j hjl; rw [wa_charge]; exact hwa j hjl
    · rw [wlen_charge]; exact hwl2
    · rw [wlen_charge]; exact hrl'
    · rw [w_charge]; exact hL'
    · rw [w_charge]; exact he'
    · intro i; rw [wa_charge]; exact helog i
    · rw [cap_charge]; exact hcapS
    · rw [cost_charge]; omega
  case entry =>
    refine ⟨hj0, ?_, hR, ?_, hrt2L, hrl, rfl, rfl, hL, he, helog0, rfl, by omega⟩
    · rw [flt_zero, ht0]; simp
    · intro j hjl
      rw [flt_zero] at hjl
      simp at hjl

/-! ## The full compaction receipt -/

/-- **The consolidation roots filter runs** — the full store-compaction: allocate the
scratch (`walloc "rt2"`), stash the live entries of the combined source (the proved
`stashLoop_runs`), re-allocate `"roots"` at the live count (`walloc "roots"`,
`decode_allocW_roots`), and copy back (the proved `copyLoop_runs` through the landed
`decode_storeW_roots` splices).  The decode is exact at the compaction boundary:
post `Rel {st with roots := flt st (r.wa "elog") L (L+e)}`, cost `≤ 14·(L+e) + 7`. -/
theorem rootsCompact_runs (r : State ℝ≥0) (st : HState) (L e : ℕ)
    (hR : Rel st r) (hcap0 : 1 < r.cap)
    (hL : r.w "L" = L) (he : r.w "e" = e)
    (hrl : r.wlen "roots" = L)
    (hlogcap : ∀ i, i < e → i < r.wlen "elog")
    (hid : (∀ j, j < L → st.roots.getD j 0 < r.wlen "par") ∧
      (∀ i, i < e → r.wa "elog" i < r.wlen "par"))
    (hcap : L + e + 1 < r.cap) :
    Runs realOps rootsCompact r (fun r' =>
      Rel {st with roots := flt st (r.wa "elog") L (L + e)} r' ∧
      r'.wlen "roots" = (flt st (r.wa "elog") L (L + e)).length ∧
      r'.cap = r.cap ∧ r'.cost ≤ r.cost + 14 * (L + e) + 7) := by
  unfold rootsCompact
  -- Phase 1: allocate the scratch
  have halloc : evalW r (add (var "L") (var "e")) = some (L + e) := by
    refine evalW_add_of (x := L) (y := e) (by rw [evalW_var, hL]) (by rw [evalW_var, he]) ?_
    omega
  refine runs_seq (runs_walloc halloc ?_)
  set r1 := (r.allocW "rt2" (L + e)).charge (L + e + 1) with hr1
  -- Phase 2: t := 0
  have hl0 : evalW r1 (lit 0) = some 0 :=
    evalW_lit_of (by rw [hr1, cap_charge, cap_allocW]; omega)
  refine runs_seq (runs_wset hl0 ?_)
  set r2 := (r1.setW "t" 0).charge 1 with hr2
  -- Phase 3: j := 0
  have hl0' : evalW r2 (lit 0) = some 0 :=
    evalW_lit_of (by rw [hr2, cap_charge, cap_setW, hr1, cap_charge, cap_allocW]; omega)
  refine runs_seq (runs_wset hl0' ?_)
  set r3 := (r2.setW "j" 0).charge 1 with hr3
  -- r3 facts
  have hwlen_ne : ∀ X : String, X ≠ "rt2" → r3.wlen X = r.wlen X := by
    intro X hX
    rw [hr3, wlen_charge, wlen_setW, hr2, wlen_charge, wlen_setW, hr1, wlen_charge,
      wlen_allocW, if_neg hX]
  have hR3 : Rel st r3 := by
    show decode r3 = st
    rw [hr3, decode_charge, decode_w_other _ (by decide : ("j" : String) ≠ "n"), hr2,
      decode_charge, decode_w_other _ (by decide : ("t" : String) ≠ "n"), hr1, decode_charge,
      decode_allocW_foreign (b := "rt2") r (by decide) (L + e)]
    exact hR
  have hj03 : r3.w "j" = 0 := by rw [hr3, w_charge, w_setW, if_pos (by simp)]
  have ht03 : r3.w "t" = 0 := by
    rw [hr3, w_charge, w_setW, if_neg (by decide : ("t" : String) ≠ "j"), hr2, w_charge,
      w_setW, if_pos (by simp)]
  have hL3 : r3.w "L" = L := by
    rw [hr3, w_charge, w_setW, if_neg (by decide : ("L" : String) ≠ "j"), hr2, w_charge,
      w_setW, if_neg (by decide : ("L" : String) ≠ "t"), hr1, w_charge, w_allocW, hL]
  have he3 : r3.w "e" = e := by
    rw [hr3, w_charge, w_setW, if_neg (by decide : ("e" : String) ≠ "j"), hr2, w_charge,
      w_setW, if_neg (by decide : ("e" : String) ≠ "t"), hr1, w_charge, w_allocW, he]
  have hrt23 : r3.wlen "rt2" = L + e := by
    rw [hr3, wlen_charge, wlen_setW, hr2, wlen_charge, wlen_setW, hr1, wlen_charge,
      wlen_allocW, if_pos (by simp)]
  have hrl3 : r3.wlen "roots" = L := by
    rw [hwlen_ne "roots" (by decide)]; exact hrl
  have hlogcap3 : ∀ i, i < e → i < r3.wlen "elog" := by
    intro i hi; rw [hwlen_ne "elog" (by decide)]; exact hlogcap i hi
  have hid3 : (∀ j, j < L → st.roots.getD j 0 < r3.wlen "par") ∧
      (∀ i, i < e → r.wa "elog" i < r3.wlen "par") := by
    constructor
    · intro j hj; rw [hwlen_ne "par" (by decide)]; exact hid.1 j hj
    · intro i hi; rw [hwlen_ne "par" (by decide)]; exact hid.2 i hi
  have hcap3 : 1 < r3.cap := by
    rw [hr3, cap_charge, cap_setW, hr2, cap_charge, cap_setW, hr1, cap_charge, cap_allocW]
    exact hcap0
  have hcap3eq : r3.cap = r.cap := by
    rw [hr3, cap_charge, cap_setW, hr2, cap_charge, cap_setW, hr1, cap_charge, cap_allocW]
  have hr3cost : r3.cost = r.cost + (L + e + 1) + 1 + 1 := by
    rw [hr3, cost_charge, cost_setW, hr2, cost_charge, cost_setW, hr1, cost_charge,
      cost_allocW]
  -- Phase 4: the stash loop
  refine runs_seq ?head
  · refine Runs.mono (h := stashLoop_runs r3 st (r.wa "elog") L e hR3 hcap3 hj03 ht03
      hL3 he3 hrl3 hrt23 (fun _ => rfl) hlogcap3 hid3 (by rw [hcap3eq]; omega)) ?_
    intro s' hs'
    obtain ⟨hj4, hwt4, hrel4, hwa4, hwl24, hrl4, hL4, he4, helog4, hcap4, hcost4⟩ := hs'
    set T := (flt st (r.wa "elog") L (L + e)).length with hT
    have hcap4' : 1 < s'.cap := by rw [hcap4]; exact hcap0
    have hTle : T ≤ L + e := flt_len_le st (r.wa "elog") L (L + e)
    -- Phase 5: re-allocate "roots" at the live count
    have hte5 : evalW s' (var "t") = some T := by rw [evalW_var, hwt4]
    refine runs_seq (runs_walloc hte5 ?_)
    set s5 := (s'.allocW "roots" T).charge (T + 1) with hs5
    have hrl5 : s5.wlen "roots" = T := by rw [hs5, wlen_charge, wlen_allocW, if_pos (by simp)]
    have hwa5 : ∀ j, s5.wa "roots" j = 0 := by
      intro j; rw [hs5, wa_charge, wa_allocW, if_pos (by simp)]
    have hR5 : Rel {st with roots := (List.range T).map (fun _ => (0 : ℕ))} s5 := by
      show decode s5 = {st with roots := (List.range T).map (fun _ => (0 : ℕ))}
      rw [hs5, decode_charge, decode_allocW_roots, hrel4]
    have hrt2L5 : s5.wlen "rt2" = L + e := by
      rw [hs5, wlen_charge, wlen_allocW, if_neg (by decide : ("rt2" : String) ≠ "roots")]
      exact hwl24
    have hwa45 : ∀ j, s5.wa "rt2" j = s'.wa "rt2" j := by
      intro j
      rw [hs5, wa_charge, wa_allocW, if_neg (by decide : ("rt2" : String) ≠ "roots")]
    have hcap5 : s5.cap = r.cap := by rw [hs5, cap_charge, cap_allocW]; exact hcap4
    have hcost5 : s5.cost = s'.cost + (T + 1) := by rw [hs5, cost_charge, cost_allocW]
    -- Phase 6: j := 0
    have hl6 : evalW s5 (lit 0) = some 0 :=
      evalW_lit_of (by rw [hs5, cap_charge, cap_allocW]; omega)
    refine runs_seq (runs_wset hl6 ?_)
    set s6 := (s5.setW "j" 0).charge 1 with hs6
    have hj06 : s6.w "j" = 0 := by rw [hs6, w_charge, w_setW, if_pos (by simp)]
    have hwt6 : s6.w "t" = T := by
      rw [hs6, w_charge, w_setW, if_neg (by decide : ("t" : String) ≠ "j"), hs5, w_charge]
      exact hwt4
    have hwa06 : ∀ j, s6.wa "roots" j = 0 := by
      intro j; rw [hs6, wa_charge, wa_setW, hs5, wa_charge, wa_allocW, if_pos (by simp)]
    have hrt26 : ∀ j, s6.wa "rt2" j = s'.wa "rt2" j := by
      intro j
      rw [hs6, wa_charge, wa_setW, hs5, wa_charge, wa_allocW,
        if_neg (by decide : ("rt2" : String) ≠ "roots")]
    have hrt2L6 : s6.wlen "rt2" = L + e := by
      rw [hs6, wlen_charge, wlen_setW, hs5, wlen_charge, wlen_allocW,
        if_neg (by decide : ("rt2" : String) ≠ "roots")]
      exact hwl24
    have hR6 : Rel {st with roots := (List.range T).map (fun _ => (0 : ℕ))} s6 := by
      show decode s6 = _
      rw [hs6, decode_charge, decode_w_other _ (by decide : ("j" : String) ≠ "n")]
      exact hR5
    have hcap6 : 1 < s6.cap := by rw [hs6, cap_charge, cap_setW]; exact hcap4'
    -- Phase 7: the copy-back loop
    refine Runs.mono (h := copyLoop_runs (r := s6) (st := st) (rd := s'.wa "rt2") (t := T)
      hR6 hj06 hwt6 hwa06 hcap6 hrl5 (by rw [hrt2L6]; exact hTle) hrt26
      (by rw [hs6, cap_charge, cap_setW, hs5, cap_charge, cap_allocW]; rw [hcap4]; omega)) ?_
    intro s7 hs7
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hs7
    -- the refilled array IS the filtered source
    have hlist : (List.range T).map (s'.wa "rt2") = flt st (r.wa "elog") L (L + e) := by
      refine List.ext_getElem (by simp [hT]) (fun j hj1 hj2 => ?_)
      rw [List.getElem_map, List.getElem_range, hwa4 j hj2, List.getD_eq_getElem?_getD,
        List.getElem?_eq_some_iff.mpr ⟨hj2, rfl⟩]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hlist]; exact q4
    · exact q3
    · rw [q5, hs6, cap_charge, cap_setW, hs5, cap_charge, cap_allocW]; exact hcap4
    · rw [hs6, cost_charge, cost_setW, hcost5] at q6
      have hT := hTle
      omega

/-! ## The pending-log window

Between compactions the machine's roots appends ride the promotion log `"elog"`
(register `"e"` = logical count): the decode (`Rel`) stays exact, and the pending
window is the log's contents.  `RelLog stW pending r` — the decode equals the
window frame `stW` and the log reads `pending` — is the relation shape the design
demands: the log appends must not disturb the decode, and they do not (every
append is an `"elog"` store plus a non-`"n"` register write, both decode-foreign).
The abstract state the algorithm sees between compactions is the join `win stW
pending`; the compaction boundary closes it (`flt_eq_filter_append`).  Order
convention: the log is read in cell order, so an append lands at the window's
TAIL — the abstract splices prepend to `roots`; that prepend↔append order seam
is a roots-permutation transfer family, named in the module docstring. -/

/-- The pending window: the promotion log's logical contents — cells
`0 … "e" − 1` of `"elog"`, in cell order. -/
def logOf (r : State V) : List ℕ := (List.range (r.w "e")).map (r.wa "elog")

/-- **The pending-log window relation**: the decode equals the window frame
`stW` (exact — the appends do not disturb it) and the log reads `pending`. -/
def RelLog (stW : HState) (pending : List ℕ) (r : State V) : Prop :=
  Rel stW r ∧ logOf r = pending

/-- The window join: the frame's roots with the pending appends at the tail. -/
def win (stW : HState) (pending : List ℕ) : HState :=
  {stW with roots := stW.roots ++ pending}

/-- `getD`-at-zero over the range reads the list back. -/
theorem map_range_getD (l : List ℕ) : (List.range l.length).map (l.getD · 0) = l := by
  refine List.ext_getElem (by simp) (fun j h1 _ => ?_)
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_some_iff.mpr ⟨by simpa using h1, rfl⟩]
  simp

/-- The window grows by one cell at an append: the new log cell lands at the
tail. -/
theorem logOf_append (r : State V) (v e : ℕ) (he : r.w "e" = e)
    (hs : State V) (hse : hs.w "e" = e + 1)
    (h0 : ∀ j, j < e → hs.wa "elog" j = r.wa "elog" j) (he0 : hs.wa "elog" e = v) :
    logOf hs = logOf r ++ [v] := by
  unfold logOf
  rw [he, hse, List.range_succ, List.map_append, List.map_singleton,
    map_range_congr (fun j hj => h0 j (by simpa using hj)), he0]

/-- A store outside `"elog"` leaves the window verbatim. -/
theorem logOf_storeW {r : State V} {b : String} (hb : b ≠ "elog") (j v : ℕ) :
    logOf (r.storeW b j v) = logOf r := by
  unfold logOf
  simp [State.storeW, Ne.symm hb]

/-- A register write outside `"e"` leaves the window verbatim. -/
theorem logOf_setW {r : State V} {x : String} (hx : x ≠ "e") (v : ℕ) :
    logOf (r.setW x v) = logOf r := by
  unfold logOf
  simp [State.setW, Ne.symm hx]

theorem logOf_charge (r : State V) (k : ℕ) : logOf (r.charge k) = logOf r := rfl

/-- The window survives a store to a foreign array (outside the layout and
outside the log). -/
theorem RelLog.storeW {stW : HState} {pending : List ℕ} {r : State V}
    (h : RelLog stW pending r) {b : String}
    (hb : b ≠ "par" ∧ b ≠ "mrk" ∧ b ≠ "deg" ∧ b ≠ "chd" ∧ b ≠ "rgt" ∧ b ≠ "lft" ∧
      b ≠ "roots" ∧ b ≠ "elog") (j v : ℕ) :
    RelLog stW pending (r.storeW b j v) := by
  refine ⟨Rel.storeW_foreign h.1 ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1⟩ j v,
    (logOf_storeW (r := r) hb.2.2.2.2.2.2.2 j v).trans h.2⟩

/-- The window survives a register write outside `"e"` and `"n"`. -/
theorem RelLog.w_other {stW : HState} {pending : List ℕ} {r : State V}
    (h : RelLog stW pending r) {x : String} (hx : x ≠ "e" ∧ x ≠ "n") (v : ℕ) :
    RelLog stW pending (r.setW x v) :=
  ⟨Rel.w_other h.1 hx.2 v, (logOf_setW hx.1 v).trans h.2⟩

/-- The window grows by one cell at the append step: the `"elog"` store at
`"e"` plus the count bump; the decode is untouched. -/
theorem RelLog.bump {stW : HState} {pending : List ℕ} {r : State V}
    (h : RelLog stW pending r) (v e : ℕ) (he : r.w "e" = e)
    (hcap : e + 1 < r.cap) (hwl : e < r.wlen "elog") :
    RelLog stW (pending ++ [v])
      (((r.storeW "elog" e v).charge 1).setW "e" (e + 1)) := by
  refine ⟨?_, ?_⟩
  · show decode (((r.storeW "elog" e v).charge 1).setW "e" (e + 1)) = stW
    rw [decode_w_other _ (by decide : ("e" : String) ≠ "n"), decode_charge,
      decode_storeW_foreign r (by decide) e v]
    exact h.1
  · rw [← h.2]
    refine logOf_append r v e he _ ?_ ?_ ?_
    · rw [w_setW, if_pos (by simp)]
    · intro j hj
      rw [wa_setW, wa_charge, wa_storeW,
        if_neg (by simp [show j ≠ e from by omega])]
    · rw [wa_setW, wa_charge, wa_storeW, if_pos (by simp)]

/-- The pending append as a statement: one `"elog"` store + the count bump.
`insertOp` is `logPush "x"`. -/
def logPush (reg : String) : Stmt :=
  .seq (wstore "elog" (var "e") (var reg)) (wset "e" (add (var "e") (lit 1)))

theorem insertOp_eq : insertOp = logPush "x" := rfl

/-- **The insert op's window receipt** — the landed `insertOp_runs` re-wired:
the window grows by the one pending cell and the op costs exactly `2`. -/
theorem insertOp_RelLog (stW : HState) (pending : List ℕ) (r : State ℝ≥0) (e : ℕ)
    (hR : RelLog stW pending r) (hcap0 : 1 < r.cap) (hcapE : e + 1 < r.cap)
    (he : r.w "e" = e) (hb : e < r.wlen "elog") :
    Runs realOps insertOp r (fun r' =>
      RelLog stW (pending ++ [r.w "x"]) r' ∧ r'.cost = r.cost + 2) := by
  refine Runs.mono (insertOp_runs stW r e hR.1 hcap0 hcapE he hb) ?_
  rintro r' ⟨hrel, he', hxe, ho, hcst⟩
  refine ⟨⟨hrel, ?_⟩, hcst⟩
  rw [← hR.2]
  exact logOf_append r (r.w "x") e he r' he' (fun j hj => ho j (by omega)) hxe

/-- The compaction filter's source is the frame's roots plus the log, in
order — the pure list fact behind the boundary closure. -/
theorem flt_filter_append (stW : HState) (elogR : ℕ → ℕ) (L e : ℕ)
    (hL : L = stW.roots.length) :
    flt stW elogR L (L + e) = (stW.roots ++ (List.range e).map elogR).filter (isLive stW) := by
  induction e generalizing L with
  | zero =>
    have hmap : (List.range L).map
        (fun j => if j < L then stW.roots.getD j 0 else elogR (j - L)) = stW.roots := by
      refine (map_range_congr (fun j hj => if_pos (by simpa using hj))).trans ?_
      rw [hL]
      exact map_range_getD stW.roots
    unfold flt
    rw [Nat.add_zero, List.range_zero, List.map_nil, List.append_nil, hmap]
  | succ e ih =>
    have hstep := flt_step stW elogR L (L + e)
    have hcell : (if L + e < L then stW.roots.getD (L + e) 0 else elogR (L + e - L))
        = elogR e := by
      rw [if_neg (show ¬(L + e < L) from by omega), Nat.add_sub_cancel_left]
    rw [← Nat.add_assoc, hstep, hcell, List.range_succ, List.map_append, List.map_singleton,
      ← List.append_assoc, List.filter_append, List.filter_singleton, ih L hL]
    cases hb : isLive stW (elogR e) <;> simp [hb]

/-- **The compaction boundary closes the window**: the landed filter's source
is exactly the joined list. -/
theorem flt_eq_filter_append (stW : HState) (r : State V) (pending : List ℕ)
    (L e : ℕ) (hR : Rel stW r) (hrl : r.wlen "roots" = L) (he : r.w "e" = e)
    (hlog : logOf r = pending) :
    flt stW (r.wa "elog") L (L + e) = (stW.roots ++ pending).filter (isLive stW) := by
  rw [flt_filter_append stW (r.wa "elog") L e (by rw [← hR, decode_roots, hrl,
    List.length_map, List.length_range]), ← hlog]
  unfold logOf
  rw [he]


/-! ## The decrease-key op

The abstract cut (`cutState`, FibHeapCut) is seven conditional stores; the machine
text `dkCut` runs them over the decoded frame — every branch test reads a
pre-store cell (`load "deg" y` before the decrement; the relink indices
`lft x`/`rgt x` are pre-state values) — and the roots prepend rides the pending
log (`logPush "x"`, the landed `insertOp`).  The text's data content is the pure
store sequence `cutSplice` (branches resolved against the pre-state decode);
`decode_cutSplice` is the step congruence: the decode lands exactly at the
window frame `cutPend` — `cutState` with the prepend deferred to the window.
The `Runs` receipt reduces to eval facts + this bridge + `insertOp_RelLog`;
it is the named remainder's first slice. -/

theorem wa_mrk_of_rel {st : HState} {r : State V} (h : Rel st r) (j : ℕ) :
    r.wa "mrk" j = st.mrk j := by
  have := congrFun (congrArg HState.mrk h) j
  simpa [decode_mrk] using this

theorem wa_deg_of_rel {st : HState} {r : State V} (h : Rel st r) (j : ℕ) :
    r.wa "deg" j = st.deg j := by
  have := congrFun (congrArg HState.deg h) j
  simpa [decode_deg] using this

theorem wa_chd_of_rel {st : HState} {r : State V} (h : Rel st r) (j : ℕ) :
    r.wa "chd" j = st.chd j := by
  have := congrFun (congrArg HState.chd h) j
  simpa [decode_chd] using this

theorem wa_rgt_of_rel {st : HState} {r : State V} (h : Rel st r) (j : ℕ) :
    r.wa "rgt" j = st.rgt j := by
  have := congrFun (congrArg HState.rgt h) j
  simpa [decode_rgt] using this

theorem wa_lft_of_rel {st : HState} {r : State V} (h : Rel st r) (j : ℕ) :
    r.wa "lft" j = st.lft j := by
  have := congrFun (congrArg HState.lft h) j
  simpa [decode_lft] using this

open Submission.FibHeapCut Submission.FibHeapExtractMin

/-- `cutState` with the roots-prepend deferred to the pending log: the window
frame one machine cut produces. -/
def cutPend (st : HState) (x y : ℕ) : HState :=
  {cutState st x y with roots := st.roots}

/-- The cut's store sequence as one pure state function: `dkCut`'s control
flow, with every branch test resolved against the pre-state decode. -/
def cutSplice (r : State V) (x y : ℕ) : State V :=
  let s₀ := (r.storeW "par" x 0).storeW "mrk" y 1
  let s₁ := if (decode r).deg y = 1 then s₀.storeW "chd" y 0
    else (((if (decode r).chd y = x then s₀.storeW "chd" y (r.wa "rgt" x) else s₀)
      |>.storeW "rgt" (r.wa "lft" x) (r.wa "rgt" x))
      |>.storeW "lft" (r.wa "rgt" x) (r.wa "lft" x))
  s₁.storeW "deg" y ((decode r).deg y - 1)

/-- The deg-update's two shapes agree: the pre-read value `g y - 1` and the
bound-var form `g i - 1` are the same function. -/
theorem degUpd_eq (g : ℕ → ℕ) (y : ℕ) :
    (fun i => if i = y then g y - 1 else g i) = (fun i => if i = y then g i - 1 else g i) := by
  funext i
  by_cases h : i = y <;> simp [h]

/-- **The cut's step congruence.**  The decode lands exactly at `cutPend` —
`cutState`'s stores, with the roots prepend deferred to the pending log. -/
theorem decode_cutSplice (r : State V) (x y : ℕ) :
    decode (cutSplice r x y) = cutPend (decode r) x y := by
  by_cases h1 : (decode r).deg y = 1
  · simp only [cutSplice, cutPend, cutState, if_pos h1]
    simp [h1, decode, State.storeW, HState.mk.injEq, degUpd_eq]
  · simp only [cutSplice, cutPend, cutState, if_neg h1]
    by_cases h2 : (decode r).chd y = x
    · simp only [if_pos h2]
      simp [h1, h2, decode, State.storeW, HState.mk.injEq, degUpd_eq]
      all_goals first
        | rfl
        | exact ⟨rfl, rfl⟩
    · simp only [if_neg h2]
      simp [h1, h2, decode, State.storeW, HState.mk.injEq, degUpd_eq]
      all_goals first
        | rfl
        | exact ⟨rfl, rfl⟩

/-- One clearing-promote cell of the cascade walk: `s` (the marked child) out
of `z` (its parent) — `promoteState`'s stores over the decoded frame, the
branch tests reading pre-store cells, then the pending append of `s`. -/
def promoteCell : Stmt :=
  .seq (wstore "par" (var "s") (lit 0))
    (.seq (wstore "mrk" (var "s") (lit 0))
      (.seq (wstore "mrk" (var "z") (lit 0))
        (.seq (.ite (eq (load "deg" (var "z")) (lit 1))
                 (wstore "chd" (var "z") (lit 0))
                 (.seq (.ite (eq (load "chd" (var "z")) (var "s"))
                          (wstore "chd" (var "z") (load "rgt" (var "s")))
                          skip)
                   (.seq (wstore "rgt" (load "lft" (var "s")) (load "rgt" (var "s")))
                         (wstore "lft" (load "rgt" (var "s")) (load "lft" (var "s"))))))
          (.seq (wstore "deg" (var "z") (sub (load "deg" (var "z")) (lit 1)))
                (logPush "s")))))

/-- **The cut op's machine text.**  The cut splice (`cutSplice`'s control
flow) plus the pending append of the cut child. -/
def dkCut : Stmt :=
  .seq (wstore "par" (var "x") (lit 0))
    (.seq (wstore "mrk" (var "y") (lit 1))
      (.seq (.ite (eq (load "deg" (var "y")) (lit 1))
                (wstore "chd" (var "y") (lit 0))
                (.seq (.ite (eq (load "chd" (var "y")) (var "x"))
                          (wstore "chd" (var "y") (load "rgt" (var "x")))
                          skip)
                    (.seq (wstore "rgt" (load "lft" (var "x")) (load "rgt" (var "x")))
                          (wstore "lft" (load "rgt" (var "x")) (load "lft" (var "x"))))))
        (.seq (wstore "deg" (var "y") (sub (load "deg" (var "y")) (lit 1)))
              (logPush "x"))))

/-- The cascade walk: from the cut's freshly marked `y`, walk `z := par s` up
while the parent is marked and non-NIL (the product test `0 < mrk z · z`),
each cell `promoteCell`, then mark the stopping ancestor (`markState`'s one
store).  **The chain-discipline seam is named in the module docstring**: the
model's `ClearChain` cells need each cell's `y` marked in the cell's own
running state while the clearing promote clears the parent `z` too, so the
walk's exact stop discipline is the `hcc` witness-generation question. -/
def dkCascade : Stmt :=
  .seq (wset "s" (var "y"))
    (.seq (wset "z" (load "par" (var "y")))
      (.while (lt (lit 0) (mul (load "mrk" (var "z")) (var "z")))
        (.seq promoteCell
          (.seq (wset "s" (var "z"))
                (wset "z" (load "par" (var "z")))))))

def dkOp : Stmt :=
  .seq dkCut (.seq dkCascade (wstore "mrk" (var "s") (lit 1)))

/-! ## The extract-min op text

The abstract extract (`extractState`, FibHeapExtractMin) clears `par`/`mrk`
on `r`'s children, empties `r`'s degree and child head, and rebuilds the root
list (`r` filtered out, the children appended).  The machine text:
`kidLoop` re-roots each child of the ring walk (`deg r` steps of `rgt` from
`chd r` — the list `kids` names) and appends it to the pending log;
`absorbMin` empties `r` and absorbs its slot **off-tree** at the sentinel
`absorbVal r` (`par r ≠ 0` is the compaction's live test — the extracted slot
is consumed exactly like a meld-consumed root; the side condition `3 ≤ n`
keeps the sentinel in range).  The compaction then drops `r` and absorbs the
log.  The text's data content is `extractSplice`; `decode_extractSplice` is
the step congruence onto the window frame `extractStateAbs`. -/

/-- The machine absorb sentinel for a consumed slot: off-tree, non-NIL
(`par ≠ 0` is the compaction's live test), never the slot itself.  A freed
slot keeps its index (the layout arrays are length `n`), so it needs a `par`
value; `1` — or `2` when the slot IS 1 — is the honest tombstone.  Side
condition: `3 ≤ n` (the race's `N ≥ 16`). -/
def absorbVal (rr : ℕ) : ℕ := if rr = 1 then 2 else 1

/-- `extractState` with the roots change deferred to the pending log and the
extracted slot absorbed off-tree at sentinel `a`: the window frame one
machine extract produces. -/
def extractStateAbs (st : HState) (rr a : ℕ) : HState :=
  {extractState st rr with
    par := fun i => if i = rr then a else (extractState st rr).par i
    roots := st.roots}

/-- The extract's store sequence as one pure state function: the child-clearing
fold over `kids` (each visited cell `par c := 0`, `mrk c := 0`), the deg/chd
empties, and the absorb's branch (the machine register's value). -/
def extractSplice (r : State V) (rr : ℕ) : State V :=
  let s₁ := (kids (decode r) rr).foldl
      (fun s c => (s.storeW "par" c 0).storeW "mrk" c 0) r
  let s₂ := (s₁.storeW "deg" rr 0).storeW "chd" rr 0
  if r.w "r" = 1 then s₂.storeW "par" rr 2 else s₂.storeW "par" rr 1

/-- Two clear stores (`par c := 0`, `mrk c := 0`) as one decode splice. -/
theorem decode_twoStore_clear (r : State V) (c : ℕ) :
    decode ((r.storeW "par" c 0).storeW "mrk" c 0)
      = {decode r with par := fun i => if i = c then 0 else (decode r).par i,
                       mrk := fun i => if i = c then 0 else (decode r).mrk i} := by
  rw [decode_storeW_mrk, decode_storeW_par, HState.mk.injEq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  funext i
  simp

/-- The child-clearing fold's decode: the visited cells get `par`/`mrk` 0. -/
theorem decode_foldl_clear (r : State V) : ∀ ks : List ℕ,
    decode (ks.foldl (fun s c => (s.storeW "par" c 0).storeW "mrk" c 0) r)
      = {decode r with par := fun i => if i ∈ ks then 0 else (decode r).par i,
                       mrk := fun i => if i ∈ ks then 0 else (decode r).mrk i} := by
  intro ks
  induction ks generalizing r with
  | nil => simp [decode]
  | cons c ks ih =>
    show decode (List.foldl _ ((r.storeW "par" c 0).storeW "mrk" c 0) ks) = _
    rw [ih ((r.storeW "par" c 0).storeW "mrk" c 0), decode_twoStore_clear,
      HState.mk.injEq]
    have hsplit : ∀ (g : ℕ → ℕ) (i : ℕ),
        (if i ∈ ks then (0:ℕ) else (if i = c then 0 else g i))
          = (if i ∈ c :: ks then 0 else g i) := by
      intro g i
      by_cases hic : i = c
      · subst hic
        by_cases hik : i ∈ ks <;> simp [hik]
      · by_cases hik : i ∈ ks <;> simp [hic, hik]
    refine ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    · funext i
      dsimp only
      rw [hsplit (decode r).par i]
    · funext i
      dsimp only
      rw [hsplit (decode r).mrk i]

/-- **The extract's step congruence.**  The decode lands exactly at
`extractStateAbs` — `extractState`'s stores, with the roots change deferred
to the pending log and the slot absorbed at the register's sentinel. -/
theorem decode_extractSplice (r : State V) (rr : ℕ) :
    decode (extractSplice r rr)
      = extractStateAbs (decode r) rr (if r.w "r" = 1 then 2 else 1) := by
  unfold extractSplice extractStateAbs
  by_cases h : r.w "r" = 1
  · rw [if_pos h, decode_storeW_par, decode_storeW_chd, decode_storeW_deg,
      decode_foldl_clear, HState.mk.injEq]
    all_goals first
      | simp [h, decode, State.storeW, extractState]
      | (funext i; simp [h, decode, State.storeW, extractState])
  · rw [if_neg h, decode_storeW_par, decode_storeW_chd, decode_storeW_deg,
      decode_foldl_clear, HState.mk.injEq]
    all_goals first
      | simp [h, decode, State.storeW, extractState]
      | (funext i; simp [h, decode, State.storeW, extractState])

/-- One child-visiting step of the extract's promotion loop: re-root `c`
(`extractState` clears both `par` and `mrk`), append it to the pending log,
advance the ring walk. -/
def kidStep : Stmt :=
  .seq (wstore "par" (var "c") (lit 0))
    (.seq (wstore "mrk" (var "c") (lit 0))
      (.seq (logPush "c")
        (.seq (wset "j" (add (var "j") (lit 1)))
              (wset "c" (load "rgt" (var "c"))))))

/-- The child-promotion loop: `deg r` ring steps from `chd r` — the visited
list is exactly `kids st r` (the congruence's `ks`). -/
def kidLoop : Stmt :=
  .seq (wset "c" (load "chd" (var "r")))
    (.while (lt (var "j") (load "deg" (var "r"))) kidStep)

/-- The extracted min leaves the heap: its slot absorbed off-tree
(`absorbVal` — the branch on the register's value), its degree and child head
emptied (`extractState`'s `deg r := 0`, `chd r := 0`). -/
def absorbMin : Stmt :=
  .seq (.ite (eq (var "r") (lit 1)) (wstore "par" (var "r") (lit 2))
                               (wstore "par" (var "r") (lit 1)))
    (.seq (wstore "deg" (var "r") (lit 0)) (wstore "chd" (var "r") (lit 0)))

/-- **The extract-min op text**: promote `r`'s children to the pending log,
absorb `r`, then the compaction absorbs the log and drops `r` (its `par` is
the absorb sentinel — the live test `par x = 0` fails).  The compaction's
scan register `"r"` clobbers the (by then dead) min id — `absorbMin` runs
first. -/
def extractOp : Stmt :=
  .seq (wset "j" (lit 0))
    (.seq kidLoop (.seq absorbMin rootsCompact))

/-! ## The op `Runs` receipts (p2d)

The per-op receipts: eval facts from the `wa_*_of_rel` readers (every branch
test reads a pre-store cell), the store chains bridged by the landed
`decode_cutSplice` / `decode_extractSplice` congruences (the decode lands
exactly at the window frames `cutPend` / `extractStateAbs`), and the appends
wired by the pending-append receipt.  Cost bounds are per-branch counts.
Peel discipline (measured this session): every state-layer peel goes through
`simp only` (order-insensitive over the charge/storeW wrappers — hand-counted
`rw` chains fail on the outermost-constructor order), with the meta-assigning
`rw`/`rfl` as the tail. -/

/-- The generic pending append: `logPush reg` from a window state — the window
grows by one cell carrying the register's value, cost exactly `2`.
(`insertOp_RelLog` is the `"x"` instance; the cascade cells and the extract's
child loop append through other registers.) -/
theorem logPush_RelLog (reg : String) (stW : HState) (pending : List ℕ)
    (r : State ℝ≥0) (e : ℕ)
    (hR : RelLog stW pending r) (hcap0 : 1 < r.cap) (hcapE : e + 1 < r.cap)
    (he : r.w "e" = e) (hb : e < r.wlen "elog") :
    Runs realOps (logPush reg) r (fun r' =>
      RelLog stW (pending ++ [r.w reg]) r' ∧ r'.cost = r.cost + 2) := by
  unfold logPush
  have hadd : evalW ((r.storeW "elog" e (r.w reg)).charge 1)
      (add (var "e") (lit 1)) = some (e + 1) := by
    refine evalW_add_of ?_
      (evalW_lit_of (by simp only [cap_charge, cap_storeW]; exact hcap0))
      (by simp only [cap_charge, cap_storeW]; exact hcapE)
    rw [evalW_var, w_charge, w_storeW, he]
  refine runs_seq (runs_wstore (hi := by rw [evalW_var, he]) (he := by rw [evalW_var]) hb
    (runs_wset hadd ?_))
  refine ⟨?_, ?_⟩
  · -- RelLog stW (pending ++ [r.w reg]) (final state): decode/logOf read no cost,
    -- so the tail charge is transparent and RelLog.bump lands it exactly
    show decode (((((r.storeW "elog" e (r.w reg)).charge 1).setW "e" (e + 1))).charge 1) = stW ∧
      logOf (((((r.storeW "elog" e (r.w reg)).charge 1).setW "e" (e + 1))).charge 1)
        = pending ++ [r.w reg]
    rw [decode_charge, logOf_charge]
    exact RelLog.bump hR (r.w reg) e he hcapE hb
  · -- cost
    rw [cost_charge, cost_setW, cost_charge, cost_storeW]

/-! ## Axiom probes -/

#print axioms insertOp_runs
#print axioms copyLoop_runs
#print axioms stashLoop_runs
#print axioms rootsCompact_runs
#print axioms insertOp_RelLog
#print axioms decode_cutSplice
#print axioms decode_twoStore_clear
#print axioms decode_foldl_clear
#print axioms decode_extractSplice
#print axioms flt_filter_append
#print axioms flt_eq_filter_append
#print axioms logPush_RelLog
