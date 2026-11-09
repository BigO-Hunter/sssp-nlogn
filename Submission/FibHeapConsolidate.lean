import Submission.FibHeapMeasure
import Submission.FibHeapAmortized

/-!
# M4b: the consolidation table — the fold's witness generation

`extractRun`'s cell premise (`ExtractOkDeg`: the merge's `MergePre` at **equal degree**,
FibHeapExtractMin) is caller discipline — the fold consumes well-formed chains, it does
not generate them.  This module closes that gap: the consolidation **table** (a
degree-indexed partial map on roots, the machine form of the degree-bucket array), the
chain the table **generates** for a list of arriving (promoted) roots, and the theorem
that the generated chain satisfies `ExtractOkDeg` + `ExtractOk` — the named
"witness generation" risk becomes a theorem.

## The model

- `TableOK st tbl`: slot `i` holds the root of degree `i`, or `0` (unoccupied — the NIL
  sentinel is never a root, so `0` is free as the empty marker).  Occupied slots are
  *typed*: the occupant is a root and its degree is the slot index.  "≤1 root per degree
  slot" is exactly `tableOK_inj` (two slots holding one root share its degree-key).
- `tableOf st`: the canonical table — the first root of the requested degree.  It is
  always a table (`tableOK_tableOf`), and it is *complete* (every root in its slot,
  `tableOf_complete`) exactly under M2's `Consolidated` (`consolidated_of_tableOK` is
  the M2 direction: a complete table has distinct root degrees).

## The discipline and the two theorems

- `TableChain tbl st chain` (static — stated once, at the state the fold starts in):
  each cell melds the arriving root `c` with the table's occupant `p` of its degree
  slot; each cell's nodes are outside all its successors' cells — which is what keeps
  every later cell's degree and membership at its static value while the fold runs.
- `tableChain tbl st arr`: the generator — for each arriving root, the cell
  `(c, tbl (deg c))` when the slot is occupied and not `c` itself; otherwise no cell
  (the arrival simply takes the empty slot).  `tableChain_generate` proves the generated
  chain disciplined; `tableChain_extractOkDeg` consumes a disciplined chain through the
  fold's own recursion (the disjointness carries the running-state premises); and
  `tableChain_generate_ok` composes the two: **TableOK + arrivals in roots +
  pairwise-distinct arrival degrees ⟹ the generated fold satisfies `ExtractOkDeg` +
  `ExtractOk`.**

## Honest seams

1. **No carry (the named remainder).**  The generator reads the *static* table: each
   slot absorbs at most once.  The literal algorithm's carry loop (the re-slotted
   absorber, now at degree `k+1`, meeting the next arrival) is NOT modeled — the
   pairwise-distinct-arrival-degrees premise is that restriction stated honestly.  The
   carry is downstream work: iterate the pass against the re-keyed table (each iteration
   is one `extractRun` at equal degree; `root_count_bound`'s O(log n) root bound caps
   the iterations), or extend the generator to thread the re-keying.
2. **`DegOK` stays the named clause** (wound 2125609385): the equal-degree cell premise
   is exactly what the fold's `DegOK` climb (`merge_DegOK`) rides — this module
   *generates* those cells, it does not discharge the clause at the program level.

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapConsolidate

open Submission.FibHeapRefine Submission.FibHeapMeasure Submission.FibHeapMerge
  Submission.FibHeapExtractMin Submission.FibHeapLink Submission.FibHeapSupport
  Submission.FibHeapCascade Submission.FibHeapAmortized Submission.FibHeapCut

/-! ## The table: a degree-indexed partial map on roots -/

/-- The consolidation table: slot `i` holds the root of degree `i`, or `0` (unoccupied;
the NIL sentinel is never a root, so `0` is free as the empty marker). -/
def TableOK (st : HState) (tbl : ℕ → ℕ) : Prop :=
  ∀ i, tbl i = 0 ∨ (tbl i ∈ st.roots ∧ st.deg (tbl i) = i)

/-- **≤1 root per degree slot.**  Two slots holding the same root share its degree-key
(each occupant's degree is its slot index), so the slots coincide. -/
theorem tableOK_inj (st : HState) (tbl : ℕ → ℕ) (hT : TableOK st tbl) {i j : ℕ}
    (hi : tbl i ≠ 0) (hj : tbl j ≠ 0) (hq : tbl i = tbl j) : i = j := by
  obtain ⟨_, hdgi⟩ := (hT i).resolve_left hi
  obtain ⟨_, hdgj⟩ := (hT j).resolve_left hj
  rw [← hq] at hdgj
  omega

/-- **The M2 direction:** a complete table is the consolidation measure — distinct root
degrees (the map `r ↦ tbl (deg r)` would otherwise send two roots to one slot). -/
theorem consolidated_of_tableOK (st : HState) (tbl : ℕ → ℕ)
    (hcomp : ∀ r ∈ st.roots, tbl (st.deg r) = r) : Consolidated st := by
  intro r hr p hp hrp hde
  have h1 := hcomp r hr
  have h2 := hcomp p hp
  rw [← hde] at h2
  rw [h1] at h2
  exact hrp h2

/-- The canonical table: the first root of the requested degree, `0` when none. -/
def tableOf (st : HState) : ℕ → ℕ :=
  fun i => (st.roots.filter (fun r => st.deg r = i)).getD 0 0

/-- The canonical table is always a table: the filter's head is a root of exactly the
requested degree (the filter's own predicate), and the empty case is `0`. -/
theorem tableOK_tableOf (st : HState) : TableOK st (tableOf st) := by
  intro i
  unfold tableOf
  by_cases hnil : (st.roots.filter (fun r => st.deg r = i)) = []
  · left
    rw [hnil]
    rfl
  · right
    obtain ⟨a, l, hcons⟩ := List.exists_cons_of_ne_nil hnil
    rw [hcons]
    have ham : a ∈ st.roots ∧ st.deg a = i := by
      have hmem : a ∈ (st.roots.filter (fun r => st.deg r = i)) := by
        rw [hcons]; exact List.mem_cons_self ..
      obtain ⟨hm, hdg⟩ := List.mem_filter.mp hmem
      exact ⟨hm, by simpa using hdg⟩
    simp [List.getD]
    exact ham

/-- Completeness of the canonical table under consolidation: every root sits in its own
degree slot (the slot's filter holds exactly that root, so its head is it). -/
theorem tableOf_complete (st : HState) (hc : Consolidated st) :
    ∀ r ∈ st.roots, tableOf st (st.deg r) = r := by
  intro r hr
  have hmem : r ∈ st.roots.filter (fun q => st.deg q = st.deg r) :=
    List.mem_filter.mpr ⟨hr, by simp⟩
  obtain ⟨a, l, hcons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
  have hall : ∀ x ∈ (st.roots.filter (fun q => st.deg q = st.deg r)), x = r := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := List.mem_filter.mp hx
    by_contra hxne
    exact absurd (by simpa using hx1) (hc x hx0 r hr hxne)
  have har : a = r := hall a (by rw [hcons]; exact List.mem_cons_self ..)
  unfold tableOf
  rw [hcons]
  simp [List.getD]
  exact har

/-! ## The chain discipline -/

/-- The nodes a chain's cells name (children and absorbers, in order). -/
def chainNodes : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (c, p) :: rest => c :: p :: chainNodes rest

/-- **The consolidation discipline** (static — stated once, at the state the fold starts
in): each cell melds the arriving root `c` with the table's occupant `p` of its degree
slot; each cell's nodes are outside all its successors' cells, which is what keeps the
successors' degrees and memberships at their static values while the fold runs. -/
def TableChain (tbl : ℕ → ℕ) (st : HState) : List (ℕ × ℕ) → Prop
  | [] => True
  | (c, p) :: rest =>
    c ∈ st.roots ∧ p ∈ st.roots ∧ p ≠ c ∧ st.deg c = st.deg p ∧ tbl (st.deg c) = p ∧
    (∀ x ∈ chainNodes rest, x ≠ c ∧ x ≠ p) ∧
    TableChain tbl st rest

/-! ## Consumption: the discipline satisfies the fold's premises -/

/-- **The discipline discharges the fold.**  Running the consolidation fold over a
disciplined chain, every cell's `ExtractOkDeg` premise holds *at the state that cell
actually runs in*: the cell's own facts are static, and the successor-disjointness is
exactly what carries the stability (a meld writes only its own two nodes' degrees and
only removes its own child) through the fold's recursion.  With it, `ExtractOk` follows
by the projection. -/
theorem tableChain_extractOkDeg (tbl : ℕ → ℕ) (st₀ : HState) :
    ∀ (st : HState) (chain : List (ℕ × ℕ)),
      NILNotRoot st →
      (∀ x ∈ chainNodes chain, x ∈ st.roots) →
      (∀ x ∈ chainNodes chain, x ≠ 0 → st.deg x = st₀.deg x) →
      TableChain tbl st₀ chain →
      ExtractOkDeg st chain ∧ ExtractOk st chain := by
  intro st chain
  induction chain generalizing st with
  | nil => intro _ _ _ _; exact ⟨trivial, trivial⟩
  | cons head tail ih =>
    obtain ⟨c, p⟩ := head
    intro hnr hmem hstab hch
    obtain ⟨hm, hmp, hne, hde, hkey, hdis, hrest⟩ := hch
    have hcm : c ∈ chainNodes ((c, p) :: tail) := List.mem_cons_self ..
    have hpm : p ∈ chainNodes ((c, p) :: tail) := List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hc0 : c ≠ 0 := fun hc => hnr (hc ▸ hmem c hcm)
    have hp0 : p ≠ 0 := fun hp => hnr (hp ▸ hmem p hpm)
    have hdgc : st.deg c = st₀.deg c := hstab c hcm hc0
    have hdgp : st.deg p = st₀.deg p := hstab p hpm hp0
    have hmem' : ∀ x ∈ chainNodes tail, x ∈ (mergeState st c p).roots := by
      intro x hx
      rw [mergeState_roots, List.mem_filter]
      exact ⟨hmem x (List.mem_cons_of_mem c (List.mem_cons_of_mem p hx)),
        by simpa using (hdis x hx).1⟩
    have hstab' : ∀ x ∈ chainNodes tail, x ≠ 0 → (mergeState st c p).deg x = st₀.deg x := by
      intro x hx hx0
      rw [mergeState_deg, if_neg (hdis x hx).2]
      exact hstab x (List.mem_cons_of_mem c (List.mem_cons_of_mem p hx)) hx0
    obtain ⟨hok, hokE⟩ := ih (mergeState st c p) (merge_NILNotRoot st c p hnr)
      hmem' hstab' hrest
    have hpre4 : MergePre st c p := by
      refine ⟨hmem c hcm, hmem p hpm, fun hc => hne hc.symm, ?_⟩
      rw [hdgp, hdgc]
      omega
    have heq : st.deg c = st.deg p := by
      rw [hdgc, hdgp]
      exact hde
    have hfull : ExtractOkDeg st ((c, p) :: tail) := ⟨hpre4, heq, hok⟩
    exact ⟨hfull, extractOkDeg_imp_ok _ _ hfull⟩

/-! ## Generation: the table builds disciplined chains -/

/-- **The generator**: for each arriving root, the cell `(c, tbl (deg c))` when the slot
is occupied and not `c` itself; otherwise no cell (the arrival simply takes the empty
slot — or is the slot's occupant, degenerate).  The chain is a pure function of the
arrival list against the static table. -/
def tableChain (tbl : ℕ → ℕ) (st : HState) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | c :: rest =>
    if tbl (st.deg c) = 0 ∨ tbl (st.deg c) = c then tableChain tbl st rest
    else (c, tbl (st.deg c)) :: tableChain tbl st rest

/-- Every node a generated chain names is an arrival, or the guarded slot-occupant of
one (occupied slot, not itself). -/
theorem tableChain_nodes (tbl : ℕ → ℕ) (st : HState) :
    ∀ (arr : List ℕ) (x : ℕ), x ∈ chainNodes (tableChain tbl st arr) →
      x ∈ arr ∨ (∃ c ∈ arr, tbl (st.deg c) = x ∧ tbl (st.deg c) ≠ 0 ∧ tbl (st.deg c) ≠ c) := by
  intro arr
  induction arr with
  | nil => intro x hx; simp [tableChain, chainNodes] at hx
  | cons c rest ih =>
    intro x hx
    by_cases hguard : tbl (st.deg c) = 0 ∨ tbl (st.deg c) = c
    · rw [tableChain, if_pos hguard] at hx
      rcases ih x hx with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · obtain ⟨c', hc', h1, h2, h3⟩ := h
        exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h1, h2, h3⟩
    · rw [tableChain, if_neg hguard] at hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr ⟨c, List.mem_cons_self .., rfl,
            fun h0 => hguard (Or.inl h0), fun hcc => hguard (Or.inr hcc)⟩
        · rcases ih x h with h1 | ⟨c', hc', e1, e2, e3⟩
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', e1, e2, e3⟩

/-- **The generated chain is disciplined.**  `TableOK` types the occupants (membership
and the degree-key), the arrival list supplies membership, and the pairwise-distinct
arrival degrees supply the disjointness: arrivals differ from every earlier cell's nodes
by *degree* (the keying makes an occupant's degree its cell's arrival degree), which is
exactly the successor-disjointness `TableChain` asks for. -/
theorem tableChain_generate (tbl : ℕ → ℕ) (st : HState) (hT : TableOK st tbl) :
    ∀ arr : List ℕ, (∀ c ∈ arr, c ∈ st.roots) → (arr.map st.deg).Nodup →
      (∀ x ∈ chainNodes (tableChain tbl st arr), x ∈ st.roots) ∧
      TableChain tbl st (tableChain tbl st arr) := by
  intro arr
  induction arr with
  | nil => intro _ _; exact ⟨by simp [tableChain, chainNodes], trivial⟩
  | cons c rest ih =>
    intro harrmem hnd
    have hrestnd : (rest.map st.deg).Nodup := (List.nodup_cons.mp hnd).2
    have hrestmem : ∀ c' ∈ rest, c' ∈ st.roots :=
      fun c' hc => harrmem c' (List.mem_cons_of_mem _ hc)
    obtain ⟨hnodes, hch⟩ := ih hrestmem hrestnd
    by_cases hguard : tbl (st.deg c) = 0 ∨ tbl (st.deg c) = c
    · simp only [tableChain]
      rw [if_pos hguard]
      exact ⟨fun x hx => hnodes x hx, hch⟩
    · have hp0 : tbl (st.deg c) ≠ 0 := fun h0 => hguard (Or.inl h0)
      have hpc : tbl (st.deg c) ≠ c := fun hcc => hguard (Or.inr hcc)
      have hprm : tbl (st.deg c) ∈ st.roots := ((hT (st.deg c)).resolve_left hp0).1
      have hdegkey : st.deg (tbl (st.deg c)) = st.deg c :=
        ((hT (st.deg c)).resolve_left hp0).2
      have hdis : ∀ x ∈ chainNodes (tableChain tbl st rest),
          x ≠ c ∧ x ≠ tbl (st.deg c) := by
        intro x hx
        rcases tableChain_nodes tbl st rest x hx with hxarr | ⟨c', hc', hxdef, hx0, hxc⟩
        · -- x is an arrival: its degree differs from c's (distinct arrival degrees)
          have hxd : st.deg x ≠ st.deg c := by
            intro hh
            have hm' : st.deg x ∈ rest.map st.deg := List.mem_map.mpr ⟨x, hxarr, rfl⟩
            rw [hh] at hm'
            exact (List.nodup_cons.mp hnd).1 hm'
          refine ⟨fun hc => ?_, fun hx2 => ?_⟩
          · rw [hc] at hxd
            exact hxd rfl
          · rw [hx2, hdegkey] at hxd
            exact hxd rfl
        · -- x is the occupant of c''s slot: its degree IS c''s arrival degree
          have hxd : st.deg x = st.deg c' := by
            rw [← hxdef]
            exact ((hT (st.deg c')).resolve_left hx0).2
          have hne : st.deg c' ≠ st.deg c := by
            intro hh
            have hm' : st.deg c' ∈ rest.map st.deg := List.mem_map.mpr ⟨c', hc', rfl⟩
            rw [hh] at hm'
            exact (List.nodup_cons.mp hnd).1 hm'
          refine ⟨fun hc => ?_, fun hx2 => ?_⟩
          · rw [hc] at hxd
            exact hne hxd.symm
          · rw [hx2, hdegkey] at hxd
            exact hne hxd.symm
      simp only [tableChain]
      rw [if_neg hguard]
      refine ⟨fun x hx => ?_,
        ⟨harrmem c (List.mem_cons_self ..), hprm, hpc, ?_, rfl, hdis, hch⟩⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact harrmem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hprm
          · exact hnodes x hx
      · rw [hdegkey]

/-- **The witness-generation theorem (the (a)-closer).**  A table plus an arrival list
with pairwise-distinct degrees generates a consolidation fold whose every cell satisfies
`ExtractOkDeg` (equal-degree `MergePre`) and `ExtractOk`, at the states the cells
actually run in.  The named "witness generation" risk, now a theorem. -/
theorem tableChain_generate_ok (st : HState) (tbl : ℕ → ℕ) (arr : List ℕ)
    (hT : TableOK st tbl) (hnr : NILNotRoot st) (hmem : ∀ c ∈ arr, c ∈ st.roots)
    (hnd : (arr.map st.deg).Nodup) :
    ExtractOkDeg st (tableChain tbl st arr) ∧ ExtractOk st (tableChain tbl st arr) := by
  obtain ⟨hnodes, hch⟩ := tableChain_generate tbl st hT arr hmem hnd
  exact tableChain_extractOkDeg tbl st st (tableChain tbl st arr) hnr hnodes
    (fun _ _ _ => rfl) hch

/-! ## (b) opening slice: the sim-side state relation and one step's evidence

The RAM simulation (the Fib-heap program `p2`, not yet written) will carry `SimOK` as
its invariant and discharge, per machine step, that step's own evidence.  This section
lands the `HState`-side half of the relation — everything that does not presume `p2`'s
memory layout:

- `SimOK`: the sixteen-clause bundle every machine lemma consumes, as one conjunction —
  the sim carries ONE invariant instead of sixteen.
- `merge_SimOK`: one consolidation cell's evidence — the bundle survives the meld at the
  cell's equal-degree premise.  The step evidence `hde` is exactly the caller-discipline
  seam (wound 2125609385): the relation carries the clause, it does not discharge it.
- `DkEvidence` / `DkRunClear.cons_of_evidence`: the decode contract for one simulated
  decrease-key — the RAM step supplies `x, y, chain, stop` with `y` live and unmarked,
  the cascade-chain witness `hcc` (the sim's own witness-generation risk), and the
  length cap; the carried `MarkOK` completes `DkRunClear.cons`.

The `p2`-layout half of the relation (which RAM arrays decode to `par / mrk / deg / chd
/ rgt / lft / roots`, the roots-list-as-RAM-array encoding) is the next leg — it is
deliberately NOT presumed here. -/

/-- The sim-side invariant bundle: everything the machine's array-level lemmas consume,
as one conjunction.  The RAM simulation carries this across every step; each step's
preservation lemma assembles the step's own discharge suite. -/
def SimOK (st : HState) : Prop :=
  MarkOK st ∧ ParOK st ∧ RootNotChild st ∧ NILNotRoot st ∧ NILRoots st ∧ RingOK st ∧
  NILLeaf st ∧ NILNotChild st ∧ NILSelf st ∧ Acyc st ∧ PosOK st ∧ SlotOK st ∧
  RootsLive st ∧ ParSlot st ∧ (∀ q, KidsNodup st q) ∧ DegOK st

/-- **One consolidation cell's evidence.**  The bundle survives the meld at the cell's
equal-degree premise: `MergePre` + `deg r = deg p` (the discipline `ExtractOkDeg` names;
`merge_DegOK` is the one discharge that needs it).  Every other component rides the
merge's own suite.  This is the one-step preservation the consolidation fold composes. -/
theorem merge_SimOK (st : HState) (r p : ℕ) (hpre : MergePre st r p)
    (hde : st.deg r = st.deg p) (h : SimOK st) : SimOK (mergeState st r p) := by
  obtain ⟨hm, hpar, hrnc, hnr, hnrs, hrk, hnl, hnc, hns, hac, hpos, hslot, hrl, hps,
    hnd, hdeg⟩ := h
  exact ⟨merge_markOK st r p hm,
    merge_parOK st r p hpar hrnc hnr hrk hpre hnl,
    merge_RootNotChild st r p hpar hrnc hnr hrk hpre hnl,
    merge_NILNotRoot st r p hnr,
    merge_NILRoots st r p hnrs,
    merge_RingOK st r p hpar hrnc hnr hnrs hrk hpre hnl hac,
    merge_NILLeaf st r p hpre hnr hnl,
    merge_NILNotChild st r p hpar hrnc hnr hrk hpre hnl hnc,
    merge_NILSelf st r p hpre hnr hns,
    merge_acyc st r p hnr hpre hnrs hns hac,
    merge_posOK st r p hpar hrnc hnr hrk hpre hnl hpos,
    merge_slotOK st r p hpar hrnc hnr hrk hpre hrl hnl hslot,
    merge_RootsLive st r p hpre hrl,
    merge_parSlot st r p hpre hps hrl,
    merge_kidsNodup st r p hpar hrnc hnr hrk hpre hnl hnd,
    merge_DegOK st r p hpar hrnc hnr hrk hpre hnl hde hdeg⟩

/-- One simulated decrease-key step's evidence: the data the RAM decode must supply for
`DkRunClear.cons` to fire.  `hcc` — the cascade-chain witness, from `y` up to the first
unmarked ancestor — is the sim's own witness-generation risk; `hlen` is the per-step
cascade cap the amortized accounting consumes. -/
structure DkEvidence (st : HState) (L : ℕ) : Type where
  x : ℕ
  y : ℕ
  chain : List (ℕ × ℕ)
  stop : ℕ
  hyn : y < st.n
  hy0 : st.mrk y = 0
  hcc : ClearChain (cutState st x y) st.n chain
  hlen : chain.length ≤ L

/-- **One step's evidence, assembled.**  The decode package plus the carried `MarkOK`
is exactly `DkRunClear.cons`' premise tuple — the sim's per-step discharge is this
constructor call. -/
def DkRunClear.cons_of_evidence {st : HState} {L : ℕ} (hm : MarkOK st)
    (e : DkEvidence st L)
    (rest : DkRunClear L (decreaseKeyPathClear st e.x e.y e.chain e.stop)) :
    DkRunClear L st :=
  .cons st e.x e.y e.chain e.stop e.hyn e.hy0 hm e.hcc e.hlen rest

end Submission.FibHeapConsolidate
