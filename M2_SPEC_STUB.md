# M2-proper SPEC STUB — the RAM-level program + Faithful (node count ≥ height)

Status: STUB, opened by the M3c session 2026-11-08 after M3c landed (d1afc71).
Anchors below are real file/line references, but several claims are TO-VERIFY —
each is marked. The next session should verify the TO-VERIFYs by reading before
building anything.

## The mountain (per the M3c handoff)

"Node count ≥ height per Faithful": the abstract `treeOf` representation (fuel-indexed,
`FibHeapRefine.lean` ~253) must not lose nodes — `Faithful st f p` (FibHeapRefine ~257:
`0 → deg p = 0`; `f+1 → ∀ c ∈ kids st p, Faithful st f c`) says no represented node sits
at depth `f` with children.  The bridge to prove: under the machine invariants,
`Faithful` holds at suitable fuel for every live node, so `Tree.size`/`Support` bound the
REAL node count — which is what makes the rank cap a statement about the actual heap, not
just the abstraction.  TO-VERIFY: whether the needed bridge is `faithful_of_machine`-style
(AllFaithful from the invariant bundle) and whether it already exists in FibHeapSupport
(`Support` consumers) or FibHeapDynamic.

## The program layer

`Submission/FibHeapDynamic.lean` holds the abstract transitions (link/cut/cascade/
promoteRoots, `cascadeCut` at ~306).  M2-proper lifts the MACHINE splices — now complete
at bundle level: link (M2b, FibHeapLink/FibHeapLinkWalk), cut-unmarked (M3a
FibHeapCut.cutState), consolidation merge (M3b FibHeapMerge.mergeState), promote-marked
(M3c FibHeapPromote.promoteState) — into the decrease-key/extract-min programs and shows
the program preserves the invariant bundle stepwise (each step's bundle discharge is
already landed; the program layer composes them and carries the premise CHAIN: e.g.
promote's `mrk y = 1` is produced by cutState's `mrk z := 1`; promote's `mrk z = 0` is
the cascade-stop condition).

## Established machine facts the program layer consumes (all landed)

- Every transition keeps the 12-machine-invariant set (each module's discharges).
- Every transition's output has a Support model (`*_capstone` in Cut/Merge/Promote,
  `witness_capstone` in Witness) — the invariant set is non-vacuous after each step.
- Precondition chains: LinkPre needs deg p = deg c; MergePre needs deg p ≤ deg r;
  CutPre needs mrk y = 0; PromotePre needs mrk y = 1 ∧ mrk z = 0.  The cascade loop's
  correctness = these premises threading through the ancestor chain (position-tagged,
  as in Dynamic's `List (ℕ × Child)`).

## Discipline notes carried from M3b/M3c (verified this session)

- Build the MODULE target, not the root (`lake build Submission.<Mod>`); the arc modules
  are NOT in Submission.lean's import closure — keep the root import-clean until the
  whole arc promotes (M4?).
- Detached-build gotcha MEASURED 2026-11-08: nohup + `ps -p` polling can report a
  truncated log with 0 errors and NO "Build completed successfully" banner (the run had
  actually failed/was killed).  A green claim requires the BANNER (or exit 0) + the
  .olean existing.  Prefer foreground `lake build` when the module is warm (~2-5 min).
- v4.34 lemma directions: `iterate_succ_apply : f^[n+1] x = f^[n] (f x)`,
  `iterate_succ_apply' : f^[n+1] x = f (f^[n] x)`; ParOK takes both node args
  explicitly; a `rw` that ends in a concrete `ite` (e.g. `(if 0 = 3 then 2 else 0) = 0`)
  may NOT auto-close — rewrite via a named concrete equation instead.
- Witness recipe: hand-rolled pre-state def + @[simp] pointwise lemmas (by_cases-cascade
  with the pre-state in the simp args) + kids lemma + 14 bundle theorems + Support
  (Child.size/Child.tree/size_node/sizeSum/treeOf/kids in the final simp) + capstone.
- The Axiom budget: every theorem ⊆ [propext, Classical.choice, Quot.sound]; M3c landed
  12/61 axiom-free.


---

## WIP STATE (M2a session, 2026-11-08, ended mid-build)

`Submission/FibHeapCascade.lean` EXISTS in the worktree, UNTRACKED, NOT GREEN (22 errors,
all in the witness section).  Do NOT commit until green.  Current state:

DONE-IN-FILE (0 errors, verified by build19):
- `markState` + all 15 mark discharges (14 are definitional identities; PosOK needs
  MarkOK; see the file).
- `cascadeRun` fold + minimal recursive `ChainOk` (cell premises on the state the cell
  runs in — the threading is IN the def, no separate lemma needed).
- `promote_bridge`: with the recursive ChainOk it reduced to nearly-identity — comps 3-6
  are direct copies of `hnext`'s components; comps 1-2 via kids_promote_unchanged and
  promoteState_n.  KEEP IT THIS SHAPE (the earlier "linkage + no-hit + st-level" design
  was abandoned: `generalizing st` reverts every st-dependent premise, so st-level chain
  premises cannot thread through a plain list induction).
- 15 `cascadeRun_*` bundle theorems: premises-as-implications pattern — signature is
  `(st) (stop) (chain)` + `Premise st → ChainOk st chain → Conclusion`, `intro` AFTER
  `induction chain generalizing st` (the IH is then `∀ st, premises → ChainOk → ...` and
  the cons case threads the promote_* discharges).  RootNotChild's IH needs the running
  KidsNodup slot-wise; RootsLive's IH needs SlotOK (its theorem carries hslot).
- `decreaseKeyPath` + 15 corollaries (cut_* premise-shapes: cut_ParOK takes
  `KidsNodup st y` slot-wise = `hnd y`; cut_NILNotChild takes NO hnl; cut_RootsLive and
  promote_RootsLive take `hslot : SlotOK st`).

REMAINING ERRORS (all witness-section; ~22):
1. `kids_casOut` (~569): the unfold-first + by_cases + simp[hq] proof leaves goals — the
   composite deg/chd for symbolic q needs the q=2/3/4 case split (only ¬q=1 available).
   FIX: by_cases on q = 1, = 2, = 3, = 4 exhaustively, subst each, `rfl` per concrete
   case (all concrete reductions are fast).
2. `casOut_deg/chd` (~554/560): same symbolic-q issue — the rfl cases for
   v ∈ {1,2,3,4,5} close, but the residual "all-false" case (v ∉ {1..5}) needs
   `simp [h1, h2, h3, h4, h5]` with the ne-hypotheses reducing the ite chain; verify
   what the residual actually is with a minimal probe (the build10 failure showed
   `⊢ False` unresolved in one branch — diagnose with
   `lake env lean` on a slice before changing tactics again).
3. `cas_Acyc` (~587-614): the pre-state Acyc's chain walk (5→1→2→3→4→0) — the inner
   `rw [casPreSt.par, if_neg h]` projection-rewrites are INVALID (casPreSt.par is a
   projection, not an equation).  FIX: replace every `rw [..., casPreSt.par, ...]` with
   `simp only [casPreSt]`-style or restructure as in the working cas_Acyc pattern from
   M3b/M3c witnesses (hp5/hp1/hp2/hp3/hp4 named facts + iterate_add_apply steps, all
   closed by `exact`/`simp`, never rw-on-a-projection).
4. `cas_PosOK` (~611-614): the compact by_cases+simp-at-hj-⊢ form makes no progress in
   the deg-0 branches.  FIX: `<;> omega` after the simps (the M3b cas_PosOK shape).
5. After 1-4: rebuild; the 15 `casOut_*` output-bundle corollaries are one-liners
   already written; `casOut_Support`/`casOut_capstone` written (Support needs the
   Child.tree simp-set gotcha, already handled).

THEN: green → full `lake build Submission` receipt → #print axioms (witness family ⊆
[propext, Classical.choice, Quot.sound]) → ONE atomic commit
("M2a: decrease-key program — mark step, cascade fold, premise threading") → push
b2-refine → ls-remote verify.  Milestone 3 (program-level rankCap recounts) and the
consolidation program (extract-min side: link/merge loops over the root list) are the
next mountains.


## WIP UPDATE #2 (2026-11-08, later — 22 errors remain, all witness-section)

Progress this session: mark_PosOK FIXED (the pos-branch needs its own hj'/h1 inside the
by_cases branch); bridge FIXED (direct copies); all 15 cascadeRun_* FIXED (premises-as-
implications + intro-after-induction); NILSelf/NILNotRoot/Acyc threading FIXED
(promote_NILSelf takes hs/hns as its LAST arg; NILNotChild takes NO hnl; cut_NILNotChild
takes NO hnl; cut_ParOK takes slot-wise (hnd y) and NO hnl; cut_RootsLive/promote_
RootsLive take hslot).  Pre-state bundle: cas_MarkOK/ParSlot/KidsNodup/NILRoots/NILSelf/
NILNotRoot/NILLeaf/RootsLive/RingOK compile; everything AFTER cas_Acyc compiles
(cas_RootNotChild, cas_RootsLive, cas_RingOK, all 15 casOut_* output corollaries,
casOut_Support, casOut_capstone statements — pending only the earlier theorems).

THE 22 REMAINING ERRORS — locations + diagnoses:
1. casOut_deg (:554) / casOut_chd (:560): the unfold-first + 5×by_cases + simp [h1..h5]
   proof reduces ONE branch to a residual `⊢ False` (branch ¬v=1 ∧ v=5, h2/h3/h4
   substituted or absent).  The statement IS true at v=5 (deg 5 = 0, RHS 0).  Diagnose
   with a minimal slice: `lake env lean` on head-through-casOut + one lemma, inspect the
   residual.  SUSPECT: simp rewriting inside the nat `- 1` subterms of the unfolded
   deg fields.  Candidate fix: add `Nat.sub_self`-safe handling or prove these two by
   `rcases`-concrete + `rfl` per case with `simp only [if_neg h*]` for the symbolic
   remainder (NOT plain simp — the plain-simp symbolic case is what produced ⊢ False).
2. kids_casOut (:569): `unfold kids casOut decreaseKeyPath cascadeRun cutState
   promoteState casPreSt` + by_cases q=1 + simp [hq] — symbolic-q branch stuck: for
   q ∉ {1} the composite deg needs q ≠ 2,3,4 case splits too.  FIX: exhaustive
   by_cases q = 1, = 2, = 3, = 4 + subst + rfl per concrete case + the all-false case
   via simp with all four ne-hypotheses (deg reduces to 0 → List.ofFn over Fin 0 → []).
3. cas_ParOK (:587) / cas_KidsNodup (:592) / cas_SlotOK (:597): the simp sets are
   MISSING the membership hypothesis itself — `simp [kids, casPreSt, hq1..hq4] at
   hv ⊢` never uses hv : v = 5.  FIX: add hv (resp. hjk, hk, hj) to the simp args:
   `simp [kids, casPreSt, hq1, hq2, hq3, hq4, hv] at hv ⊢`.  For KidsNodup prefer the
   explicit M3b merged_KidsNodup pattern per slot (rw deg at hk; k = 0 by omega;
   rcases j).
4. cas_Acyc (:611-615 hz/hstep/hrec, :620 rcases): KEY SIMPLIFICATION DISCOVERED —
   `casPreSt.par Y ≠ 5` for EVERY Y (par Y = if Y = 5 then 1 else 0 ∈ {0,1}), hence
   `par^[k+1] X = par (par^[k] X) ≠ 5` for k ≥ 1 by ONE application of that fact
   (induction with unused ih).  Rewrite the whole x = 5 branch as:
   hpos5 : ∀ Y, casPreSt.par Y ≠ 5 := fun Y => by simp [casPreSt]
   hne : ∀ k, 0 < k → (casPreSt.par)^[k] 5 ≠ 5 — induction k, succ case:
   rw [iterate_succ_apply']; intro hc; exact hpos5 _ hc  (ih unused).
   Then rcases j: j = 0 by omega; j ≥ 1: exact hne j hj heq.  The x ≠ 5 branch: hx0 by
   the 4-way by_cases simp; hall by induction with
   `rw [iterate_succ_apply']; simp [ih, casPreSt]` (the par-Y-ne-5 fact makes every
   step land in {0,1} — all ≠ 5 as needed).  DELETE the broken hz/hrest2/hrec blocks
   (their arithmetic claimed par^[m+2] 5 = 0 for m ≥ 0 — FALSE at m = 0:
   par^[2] 5 = 2).
5. cas_PosOK was ALREADY FIXED this session (<;> omega tail) — the build15-listed
   611-615 errors were cas_Acyc's neighbors; re-check after 1-4.

THEN (unchanged): green → banner+exit0+.olean → lake build Submission → fresh axioms
(capstone family exact) → ONE commit "M2a: decrease-key program — markState,
cascadeRun, decreaseKeyPath, witness" → push b2-refine → ls-remote.  Then the
consolidation program (extract-min: link/merge fold over the root list) as M2b-proper.


## WIP UPDATE #3 (final for this session — 28 errors, all witness/pre-state-simp)

Error locations (build28): cas_Acyc hz-induction simps (:611-617), cas_Acyc rcases
(:620), cas_Acyc x≠5 hall (:670-689), cas_PosOK by_cases simps (:630-636),
kids_casOut/Support chain (:569, :689+), pre-state ParOK/KidsNodup/SlotOK/RootNotChild
(:612-615 hv-args form, :625-627), casOut pointwise deg/chd (:554/560 — the
rcases-rfl-simp form is SLOW-FAILING; use the by_cases+subst+simp flat form that
PROVED WORKING for par/mrk/rgt/lft in the same file).

THE KEY DIAGNOSED FIX FOR cas_Acyc (verified math, needs correct tactic encoding):
`casPreSt.par Y ≠ 5` for EVERY Y (par Y = if Y = 5 then 1 else 0 ∈ {0,1}), so
`par^[k+1] X = par (par^[k] X) ≠ 5` for k ≥ 1 in ONE step. Structure:
  hpos5 : ∀ Y, casPreSt.par Y ≠ 5 := fun Y => by simp [casPreSt]
  hne : ∀ k, 0 < k → par^[k] 5 ≠ 5 — induction k, succ: rw [iterate_succ_apply'];
    exact hpos5 _  (ih unused).
  x = 5 branch: rcases Nat.lt_or_ge j 1: j = 0 → rw [iterate_zero] at heq; omega.
    j ≥ 1 → exact absurd heq (hne j hj).
  x ≠ 5 branch: hx0 : par x = 0 (4-way by_cases simp); par^[k+1] x = par (par^[k] x),
    and par (anything) ∈ {0,1} ≠ 5 — so hall : par^[m+1] x = 0 by induction with
    succ: rw [iterate_succ_apply']; simp [ih, casPreSt] — the simp reduces
    par (par^[m] x) → ih-value → 0 (decidable ite on the ih-equality).
cas_PosOK (keep the disjunction form already in the file — its residual simps need
  `<;> omega` on the closure goals; the deg-0 branches close by False, the deg-1
  branches by j = 0 + Nat.zero_le).
Pre-state ParOK/SlotOK/RootNotChild: hv must be IN the simp args (already applied —
  re-verify the residual goals; the remaining failures may be the kids-unfold depth:
  after `simp [kids, casPreSt, ...]` the ofFn-over-Fin-0/Fin-1 reduction may need
  `List.ofFn_nil`-adjacent lemmas — if stuck, replace kids-unfold by
  `rw [cas_kids-style disjunction]` lemmas proven per-slot FIRST (cas_kids 1 = [5] by
  rfl; cas_kids q ≠ 1 → [] by rw casOut_deg — pattern proven in the file for
  kids_casOut_one/kids_casOut_ne).
error: Submission/FibHeapCascade.lean:611:4: unsolved goals
case pos
h1 : ¬2 = 1
⊢ False
error: Submission/FibHeapCascade.lean:614:6: unsolved goals
case pos
h1 : ¬3 = 1
h2 : ¬3 = 2
⊢ False
error: Submission/FibHeapCascade.lean:617:8: unsolved goals
case pos
h1 : ¬4 = 1
h2 : ¬4 = 2
h3 : ¬4 = 3
error: Submission/FibHeapCascade.lean:670:38: unsolved goals
case pos
q v : ℕ
hq1 : q = 1
hq2 : q = 2
hq3 : q = 3
hq4 : q = 4
hv : v = 5
⊢ (if v = 1 then 2 else if v = 2 then 3 else if v = 3 then 4 else if v = 5 then 1 else 0) = 1



## WIP UPDATE #4 (round 2 committed — 23 errors, ALL in the witness section)

Everything outside the witness section now compiles CLEAN: markState+15, cascadeRun,
ChainOk, promote_bridge, all 15 cascadeRun_* theorems, decreaseKeyPath + 15
corollaries, casPreSt defs, the 6 casOut_* pointwise lemmas (unfold-first +
exhaustive by_cases+subst+rfl tree — casOut_par/mrk/deg/chd/rgt/lft), casOut_roots/n,
cas_MarkOK/ParSlot/NILRoots/NILSelf/NILNotRoot/NILLeaf.

The 23 remaining (build r4):
- kids_casOut rfl-tree: ONE branch's rfl fails (:687 — the q=4-true branch;
  `kids composite 4` needs deg 4 = 0 — the promote (3,4) write makes deg 4 = 0 ✓
  but the rfl-reduction may need simp — replace that single branch's `rfl` with
  `simp` or `rfl <;> simp`).
- cas_ParOK (:702/714/717): hv must be IN the simp args (verify it survived the
  re-append; the compact by_cases chain form needs `simp [kids, casPreSt, hq1..hq4,
  hv] at hv ⊢`).
- cas_KidsNodup (:719): same — hjk/hk in args + per-slot explicit pattern.
- cas_SlotOK: same — hv in args.
- cas_Acyc (:761/762/772): the x=5 branch's `rcases Nat.lt_or_ge j 1 with h0 | h1`
  — h0 : j < 1 used by omega inside; :761 unknown h0 means the rcases binding
  names shifted — re-check the exact text; the hpos5/hne structure is CORRECT.
- casOut_Support/capstone (:837+): may be cascade-effects from kids_casOut.
THE PROBE (verified): flat by_cases+subst+simp [casOut, decreaseKeyPath, cascadeRun,
markState, cutState, promoteState, casPreSt(+ne-hyps)] WORKS for deg at v=5/v∉{1..4}
and deg 1.  Reuse that exact tactic block for kids_casOut's failing branch.


## WIP UPDATE #5 (round 3 — final for this session; 28 errors, witness-only)

Round-3 findings (build29):
- Adding `kids` to kids_casOut's simp sets made it WORSE (685-694 unsolved — the
  unfold-first composite + kids double-unfold interact).  REVERT kids_casOut to the
  r4 rfl-tree state and fix ONLY the single failing branch: find which `subst hX;
  rfl` fails (build r4 said :687 — one branch) and replace that ONE `rfl` with
  `simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
  casPreSt]`.
- `rw [hv] at hv` fails (`hv is a proof of ...` — the membership hyp's type after
  kids-unfold is not a plain Eq in some branches).  REVERT to hv-in-args
  (`simp [kids, casPreSt, hq1..hq4, hv] at hv ⊢`) and diagnose why simp leaves the
  nested-ite ⊢: the residual goals (build r3 :712) showed `(if v = 1 then 2 else
  ...) = 3` UNREDUCED with hv : v = 2 in context — simp consumed hv while rewriting
  hv itself.  Robust idiom: `rw [show v = 2 from hv] at *`-style with explicit
  terms, or `obtain ⟨rfl⟩ := hv` BEFORE the simp (destruct v instead).
  RECOMMENDED: replace the compact by_cases+simp-at form with explicit
  `rcases`-destruct of q first (q ∈ {1,2,3,4} by the hq disjunction), subst v per
  cell from the kid-list equalities, then `simp [casPreSt]` per cell.
- casOut_roots/casOut_n are RE-ADDED after kids_casOut (needed by casOut_capstone).
- Round-3 file state = committed d8.. (round 3 commit).  Error list: 685-694
  (kids_casOut six branches — revert-first), 714 ×4 (rw [hv] idiom — revert-first),
  then the previously-listed ParOK/KidsNodup/SlotOK/PosOK/Acyc/Support sites.


## WIP UPDATE #6 (round 4 — 22 errors; THE DIAGNOSED ROOT CAUSE + THE PROVEN SHAPE)

Round-4 finding: per-cell `simp at hv` makes NO PROGRESS whenever q stays SYMBOLIC
(the else-cells of the q-by_cases) — the unfolded composite's ite chain cannot reduce
without the ne-hypotheses being applied, and `simp` at a symbolic term bails.

THE PROVEN WORKING SHAPE (already in the file and compiling: cas_PosOK, and the
x≠5 branch of cas_Acyc):
  have hq : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
    by_cases hq1 : q = 1 <;> ... <;> simp_all
  rcases hq with rfl | rfl | rfl | rfl    ← substitutes q := 1/2/3/4 CONCRETE
  · unfold kids casPreSt at hj ⊢          ← now every ite is concrete
    simp / omega / Nat.zero_le ...
APPLY THIS SHAPE to cas_ParOK, cas_KidsNodup, cas_SlotOK, cas_NILNotChild,
cas_RootNotChild (replace their by_cases-chains with the rcases-rfl-per-slot +
concrete simp/omega).  Also cas_Acyc's x=5 branch: rcases Nat.lt_or_ge j 1 works,
but h0 is scoped to branch 1 — branch 2 must use `hne j (by omega)` (j ≥ 1 → 0 < j),
NOT h0.  kids_casOut: the rfl-tree fails in exactly one concrete branch — change that
branch's `rfl` to `simp` (probe-verified defs tactic).
Round-4 state committed; error lines in build r7 (m2a_r7.log): 694 (kids last-branch),
716-731 (cas_ParOK cells), 736 (KidsNodup unfold), 746-756 (SlotOK cells),
761-772 (cas_Acyc h0), plus the output-corollary cascade behind them.
