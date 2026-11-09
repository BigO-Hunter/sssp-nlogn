import Frontier.RAMLogic
import Submission.FibHeapConsolidate

/-!
# Submission.FibHeapDecode — the `p2` memory frame (the state relation's other half)

The Fib-heap program `p2` (not yet written) will run on the `Frontier.RAM` machine and
simulate `HState`.  This module pins the **memory layout** — which RAM arrays decode to
the seven `HState` fields — and lands the decode-congruence toolkit the step lemmas
will consume.  It deliberately lands the RELATION, not the program: nothing here
presumes `p2`'s control flow.

## The layout (pinned)

| `HState` field | RAM location | decode |
|---|---|---|
| `par` | word-array `"par"`, length `n` | `r.wa "par"` |
| `mrk` | word-array `"mrk"`, length `n` | `r.wa "mrk"` |
| `deg` | word-array `"deg"`, length `n` | `r.wa "deg"` |
| `chd` | word-array `"chd"`, length `n` | `r.wa "chd"` |
| `rgt` | word-array `"rgt"`, length `n` | `r.wa "rgt"` |
| `lft` | word-array `"lft"`, length `n` | `r.wa "lft"` |
| `roots` | word-array `"roots"`, length = root count | `(range len).map (r.wa "roots")` |
| `n` | register `"n"` | `r.w "n"` |

**The roots-list-as-RAM-array decision:** the root list is a **contiguous word-array
carrying its length** (`wlen "roots"`), index order = list order.  Rejected
alternatives: (i) a 0-terminated chain in the array — sound (0 is the NIL sentinel and
`NILNotRoot` keeps 0 out of roots) but every consolidation filter becomes an O(len)
compaction with explicit index management and the length register disappears; (ii)
intrusive linking of roots through spare pointer fields — there are no spare fields
(`rgt`/`lft` are the child rings), and a second ring would double the link-discharge
surface.  Contiguous+length matches B1's array idiom (every array carries its `wlen`)
and makes the consolidation's filter a store-compaction the step lemmas already know
how to carry.

## The relation and the toolkit

`Rel st r` is `decode r = st` — one clause.  The congruence lemmas are the step
mechanics: `decode (r.storeW "par" j v) = { decode r with par := fun i => if i = j
then v else … }` is *exactly* the pointwise shape every machine splice proves
(`mergeState_par`, `linkState_par`, `cutState`, `promoteState`, `extractState`), so a
sim step is: run the stores, apply the congruences, land on the splice equation.
Foreign writes (any name outside the layout) and non-`n` register writes leave the
relation untouched.

Standing seams (unchanged): **`DegOK` is the named clause** (wound 2125609385) — the
frame carries it, the layout does not discharge it; **no carry** — the consolidation
fold consumes `ExtractOkDeg` chains the table generates (`FibHeapConsolidate`).

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapDecode

open Frontier Frontier.RAM Submission.FibHeapRefine

variable {V : Type}

/-- The abstract heap state decoded out of the RAM state (the pinned layout). -/
def decode (r : State V) : HState where
  par := r.wa "par"
  mrk := r.wa "mrk"
  deg := r.wa "deg"
  chd := r.wa "chd"
  rgt := r.wa "rgt"
  lft := r.wa "lft"
  roots := (List.range (r.wlen "roots")).map (r.wa "roots")
  n := r.w "n"

/-- **The state relation.**  One clause: the RAM state decodes to the abstract heap. -/
def Rel (st : HState) (r : State V) : Prop := decode r = st

/-! ## Field reads -/

@[simp] theorem decode_par (r : State V) : (decode r).par = r.wa "par" := rfl
@[simp] theorem decode_mrk (r : State V) : (decode r).mrk = r.wa "mrk" := rfl
@[simp] theorem decode_deg (r : State V) : (decode r).deg = r.wa "deg" := rfl
@[simp] theorem decode_chd (r : State V) : (decode r).chd = r.wa "chd" := rfl
@[simp] theorem decode_rgt (r : State V) : (decode r).rgt = r.wa "rgt" := rfl
@[simp] theorem decode_lft (r : State V) : (decode r).lft = r.wa "lft" := rfl
@[simp] theorem decode_n (r : State V) : (decode r).n = r.w "n" := rfl
@[simp] theorem decode_roots (r : State V) :
    (decode r).roots = (List.range (r.wlen "roots")).map (r.wa "roots") := rfl

/-! ## Single-cell word writes (the splice shapes) -/

/-- A `par` write: the decode updates `par` at exactly the written index — the shape of
`mergeState_par` / `linkState_par` / `cutState_par` / `promoteState_par`. -/
@[simp] theorem decode_storeW_par (r : State V) (j v : ℕ) :
    decode (r.storeW "par" j v) =
      { decode r with par := fun i => if i = j then v else (decode r).par i } := by
  simp [State.storeW, decode]

/-- A `mrk` write — the shape of the clear (`mrk := 0`) writes. -/
@[simp] theorem decode_storeW_mrk (r : State V) (j v : ℕ) :
    decode (r.storeW "mrk" j v) =
      { decode r with mrk := fun i => if i = j then v else (decode r).mrk i } := by
  simp [State.storeW, decode]

/-- A `deg` write — the absorber's `+1` in the merge, the cuts' decrements, `deg r := 0`
in the extract. -/
@[simp] theorem decode_storeW_deg (r : State V) (j v : ℕ) :
    decode (r.storeW "deg" j v) =
      { decode r with deg := fun i => if i = j then v else (decode r).deg i } := by
  simp [State.storeW, decode]

/-- A `chd` write — the merge's head swap and the extract's emptying. -/
@[simp] theorem decode_storeW_chd (r : State V) (j v : ℕ) :
    decode (r.storeW "chd" j v) =
      { decode r with chd := fun i => if i = j then v else (decode r).chd i } := by
  simp [State.storeW, decode]

/-- An `rgt` write — the ring relink. -/
@[simp] theorem decode_storeW_rgt (r : State V) (j v : ℕ) :
    decode (r.storeW "rgt" j v) =
      { decode r with rgt := fun i => if i = j then v else (decode r).rgt i } := by
  simp [State.storeW, decode]

/-- An `lft` write — the ring relink's twin. -/
@[simp] theorem decode_storeW_lft (r : State V) (j v : ℕ) :
    decode (r.storeW "lft" j v) =
      { decode r with lft := fun i => if i = j then v else (decode r).lft i } := by
  simp [State.storeW, decode]

/-- A `roots`-array write: the decode updates position `j` of the decoded list. -/
theorem decode_storeW_roots (r : State V) (j v : ℕ) :
    decode (r.storeW "roots" j v) =
      { decode r with
        roots :=
          (List.range (r.wlen "roots")).map
            (fun k => if k = j then v else r.wa "roots" k) } := by
  simp [State.storeW, decode]

/-- A `roots`-length write: the decode re-lengths the decoded list. -/
theorem decode_setWlen_roots (r : State V) (len : ℕ) :
    decode ({ r with wlen := fun b => if b = "roots" then len else r.wlen b } : State V) =
      { decode r with roots := (List.range len).map (r.wa "roots") } := by
  simp [decode]

/-! ## Register writes -/

/-- The `n` register write. -/
@[simp] theorem decode_w_n (r : State V) (v : ℕ) :
    decode (r.setW "n" v) = { decode r with n := v } := by
  simp [State.setW, decode]

/-- Any other register write leaves the decode untouched (only `"n"` is decoded). -/
theorem decode_w_other (r : State V) {x : String} (hx : x ≠ "n") (v : ℕ) :
    decode (r.setW x v) = decode r := by
  simp [State.setW, decode, Ne.symm hx]

/-! ## Foreign writes and allocation -/

/-- A store to an array outside the layout leaves the decode untouched. -/
theorem decode_storeW_foreign (r : State V) {b : String}
    (hb : b ≠ "par" ∧ b ≠ "mrk" ∧ b ≠ "deg" ∧ b ≠ "chd" ∧ b ≠ "rgt" ∧ b ≠ "lft" ∧
      b ≠ "roots") (j v : ℕ) : decode (r.storeW b j v) = decode r := by
  simp [State.storeW, decode, Ne.symm hb.1, Ne.symm hb.2.1, Ne.symm hb.2.2.1,
    Ne.symm hb.2.2.2.1, Ne.symm hb.2.2.2.2.1, Ne.symm hb.2.2.2.2.2.1,
    Ne.symm hb.2.2.2.2.2.2]

/-- An allocation zeroes the array and re-lengths it — the initialization step's decode
(parity with `decode_setWlen_roots`: allocating `"roots"` re-lengths the decoded list). -/
@[simp] theorem decode_allocW_roots (r : State V) (len : ℕ) :
    decode (r.allocW "roots" len) =
      { decode r with roots := (List.range len).map (fun _ => 0) } := by
  simp [State.allocW, decode]

/-- The relation survives a foreign write verbatim. -/
theorem Rel.storeW_foreign {st : HState} {r : State V} (h : Rel st r) {b : String}
    (hb : b ≠ "par" ∧ b ≠ "mrk" ∧ b ≠ "deg" ∧ b ≠ "chd" ∧ b ≠ "rgt" ∧ b ≠ "lft" ∧
      b ≠ "roots") (j v : ℕ) : Rel st (r.storeW b j v) := by
  rw [Rel, decode_storeW_foreign r hb, h]

/-- The relation survives a non-`n` register write verbatim. -/
theorem Rel.w_other {st : HState} {r : State V} (h : Rel st r) {x : String}
    (hx : x ≠ "n") (v : ℕ) : Rel st (r.setW x v) := by
  rw [Rel, decode_w_other r hx, h]

/-! ## The pointwise bridge -/

/-- **The pointwise agreement constructor** (the F0 idiom): pointwise array equalities,
in-range root cells, and the length/register agreement give the relation — how the
initialization sequence's postcondition lands in `Rel`. -/
theorem rel_of_pointwise {st : HState} {r : State V}
    (hpar : ∀ i, r.wa "par" i = st.par i) (hmrk : ∀ i, r.wa "mrk" i = st.mrk i)
    (hdeg : ∀ i, r.wa "deg" i = st.deg i) (hchd : ∀ i, r.wa "chd" i = st.chd i)
    (hrgt : ∀ i, r.wa "rgt" i = st.rgt i) (hlft : ∀ i, r.wa "lft" i = st.lft i)
    (hlen : r.wlen "roots" = st.roots.length)
    (hroots : ∀ j, j < st.roots.length → r.wa "roots" j = st.roots.getD j 0)
    (hn : r.w "n" = st.n) : Rel st r := by
  rw [Rel]
  have hr8 : decode r = HState.mk (par := r.wa "par") (chd := r.wa "chd")
      (rgt := r.wa "rgt") (lft := r.wa "lft") (deg := r.wa "deg") (mrk := r.wa "mrk")
      (roots := (List.range (r.wlen "roots")).map (r.wa "roots")) (n := r.w "n") := rfl
  have hst8 : st = HState.mk (par := st.par) (chd := st.chd) (rgt := st.rgt)
      (lft := st.lft) (deg := st.deg) (mrk := st.mrk) (roots := st.roots)
      (n := st.n) := rfl
  have hrootsL : (List.range (r.wlen "roots")).map (r.wa "roots") = st.roots := by
    rw [hlen]
    refine List.ext_getElem (by simp) (fun j hj => ?_)
    have hj' : j < st.roots.length := by simpa using hj
    rw [List.getElem_map, List.getElem_range, hroots j hj',
      List.getD_eq_getElem?_getD,
      show st.roots[j]? = some st.roots[j] from
        (List.getElem?_eq_some_iff).mpr ⟨hj', rfl⟩]
    simp
  rw [hr8, hst8, HState.mk.injEq, hrootsL]
  exact ⟨funext hpar, funext hchd, funext hrgt, funext hlft, funext hdeg, funext hmrk,
    rfl, hn⟩

end Submission.FibHeapDecode
