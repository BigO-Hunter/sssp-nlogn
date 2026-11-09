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

## Named remainder (next landing)

- `stashLoop_runs` — the stash loop's per-iteration proof: invariant "`k` cells
  scanned, the live prefix of the combined source sits in `"rt2"`, the decode is
  untouched, cost `≤ 8·k`"; per iteration the select `ite` reads cell `j` (roots list
  below `L`, promotion log above), the live test reads `par` through the decode
  (`wa_par_of_rel`), and the stash store is foreign (`decode_storeW_foreign`).
  Its composition with the proved `copyLoop_runs` through the re-allocating
  `walloc "roots"` (`decode_allocW_roots`) and the final `rel_of_pointwise` assembly
  is `rootsCompact_runs`: post `Rel {st with roots := flt st elogR L (L+e)}`,
  cost `≤ 14·(L+e) + 7`.
- The decrease-key and extract-min program texts, and the per-step lemmas wiring
  `SimOK` + `merge_SimOK` + `DkEvidence` across `Runs` (the pending-log window needs
  its own relation shape: `decode r = st ∧ log r = pending`).
- The charge (potential deltas as time: `row_nlog`'s `m·5 + 2·rankCap + 2`, scaled
  `D0+6K+D1`) and the arithmetic climb (`log_ge`/`cap_one_one`/`sparse_one_one`/
  `arith_clause*` at `Time 1 1 0`) toward `Bound 1 1 1 1 0`.

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
position `t`, `t` counting.  (Runs lemma = the named remainder `stashLoop_runs`.) -/
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

/-! ## Axiom probes -/

#print axioms insertOp_runs
#print axioms copyLoop_runs

end Submission.FibHeapProg
