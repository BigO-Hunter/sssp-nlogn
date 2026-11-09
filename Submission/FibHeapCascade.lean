import Submission.FibHeapPromote

/-!
# M2a: the decrease-key program — mark step, cascade fold, premise threading

The three updaters (cut M3a, consolidate M3b, promote M3c) compose into the CLRS
decrease-key path.  This module is the RAM-level program layer:

1. `markState` — the one machine write no splice carried: the cascade's *stop* case
   (CASCADING-CUT at an unmarked ancestor marks it and stops).  The mark is the only
   field written, so the invariants that do not read `mrk` are unchanged *definitionally*
   and their discharges are the identity; `MarkOK` is safe because the written constant
   is `1`, and `PosOK` is safe because `ldeg` only *grows*.
2. `cascadeRun` — the cascade as a fold over the ancestor chain
   `[(y₀, z₀), (z₀, z₁), …]`: each head pair promotes the marked child out of its
   parent, and the fold ends in `markState` at the stopping ancestor.
3. `ChainOk` — one cell's `PromotePre` on the state that cell actually runs in, with the
   rest of the chain on the state *after* that promote.  `promote_bridge` is how
   original-state facts produce the running-state premises: the next cell's `mrk y = 1`
   is exactly the current promote's `mrk z := 1` write (`promoteState_mrk_z`), `b`'s
   unmarkedness survives, `z ∈ kids b` survives, and `z`'s neighbour pointers survive the
   splice by the linkage.
4. The fifteen bundle theorems for `cascadeRun` (structural induction composing the
   per-step discharges through `ChainOk`), and `decreaseKeyPath` —
   `cascadeRun (cutState st x y) chain stop` — with its own bundle corollaries.

The output witness (`casOut`: a three-level decrease-key path — cut the child, promote
twice, mark the stop) exercises `promote_bridge` and the fold, and the capstone applies
to the path's output: the decrease-key program keeps the machine inside the invariant
set, so the row's `n log` half rests on proven transitions end to end.

Credit: Fredman–Tarjan 1987 construction; formalization ours.
-/

namespace Submission.FibHeapCascade

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink Submission.FibHeapLinkWalk Submission.FibHeapCut
  Submission.FibHeapPromote

/-! ## The mark step -/

/-- The cascade's stop step: mark the unmarked stopping ancestor.  The only write is the
mark itself. -/
def markState (st : HState) (y : ℕ) : HState :=
  { st with mrk := (fun i => if i = y then 1 else st.mrk i) }

theorem markState_mrk (st : HState) (y q : ℕ) :
    (markState st y).mrk q = if q = y then 1 else st.mrk q := rfl

theorem markState_mrk_ne (st : HState) (y q : ℕ) (h : q ≠ y) :
    (markState st y).mrk q = st.mrk q := by
  rw [markState_mrk, if_neg h]

theorem markState_deg (st : HState) (y q : ℕ) : (markState st y).deg q = st.deg q := rfl
theorem markState_par (st : HState) (y q : ℕ) : (markState st y).par q = st.par q := rfl
theorem markState_chd (st : HState) (y q : ℕ) : (markState st y).chd q = st.chd q := rfl
theorem markState_rgt (st : HState) (y q : ℕ) : (markState st y).rgt q = st.rgt q := rfl
theorem markState_lft (st : HState) (y q : ℕ) : (markState st y).lft q = st.lft q := rfl
theorem markState_roots (st : HState) (y : ℕ) : (markState st y).roots = st.roots := rfl
theorem markState_n (st : HState) (y : ℕ) : (markState st y).n = st.n := rfl
theorem kids_mark (st : HState) (y q : ℕ) : kids (markState st y) q = kids st q := rfl

/-- `MarkOK` survives the mark: the written constant is `1`. -/
theorem mark_MarkOK (st : HState) (y : ℕ) (hm : MarkOK st) : MarkOK (markState st y) := by
  intro q
  rw [markState_mrk]
  by_cases h : q = y
  · rw [if_pos h]
  · rw [if_neg h]; exact hm q

/-- `PosOK` survives the mark: `ldeg` only grows. -/
theorem mark_PosOK (st : HState) (y : ℕ) (hm : MarkOK st) (hpos : PosOK st) :
    PosOK (markState st y) := by
  intro p j hj
  rw [kids_mark] at hj
  have hx : (kids (markState st y) p).getD j 0 = (kids st p).getD j 0 := rfl
  rw [hx]
  unfold ldeg
  rw [markState_deg, markState_mrk]
  by_cases h : (kids st p).getD j 0 = y
  · rw [if_pos h]
    have hj' : j ≤ st.deg ((kids st p).getD j 0) + st.mrk ((kids st p).getD j 0) :=
      hpos p j hj
    have h1 := hm ((kids st p).getD j 0)
    omega
  · rw [if_neg h]; exact hpos p j hj

/-- The fourteen mrk-reading-free invariants survive the mark *by identity*: the state's
other fields and the child lists are definitionally unchanged. -/
theorem mark_ParSlot (st : HState) (y : ℕ) (hps : ParSlot st) : ParSlot (markState st y) :=
  fun q hq => hps q hq

theorem mark_ParOK (st : HState) (y : ℕ) (hpar : ParOK st) : ParOK (markState st y) := hpar

theorem mark_KidsNodup (st : HState) (y : ℕ) (hnd : ∀ q, KidsNodup st q) :
    ∀ q, KidsNodup (markState st y) q := hnd

theorem mark_SlotOK (st : HState) (y : ℕ) (hslot : SlotOK st) : SlotOK (markState st y) := hslot

theorem mark_Acyc (st : HState) (y : ℕ) (hac : Acyc st) : Acyc (markState st y) := hac

theorem mark_NILRoots (st : HState) (y : ℕ) (hnrs : NILRoots st) :
    NILRoots (markState st y) := hnrs

theorem mark_NILSelf (st : HState) (y : ℕ) (hs : NILSelf st) : NILSelf (markState st y) := hs

theorem mark_NILNotRoot (st : HState) (y : ℕ) (hnn : NILNotRoot st) :
    NILNotRoot (markState st y) := hnn

theorem mark_NILLeaf (st : HState) (y : ℕ) (hnl : NILLeaf st) : NILLeaf (markState st y) := hnl

theorem mark_NILNotChild (st : HState) (y : ℕ) (hnc : NILNotChild st) :
    NILNotChild (markState st y) := hnc

theorem mark_RootNotChild (st : HState) (y : ℕ) (hrnc : RootNotChild st) :
    RootNotChild (markState st y) := hrnc

theorem mark_RootsLive (st : HState) (y : ℕ) (hrl : RootsLive st) :
    RootsLive (markState st y) := hrl

theorem mark_RingOK (st : HState) (y : ℕ) (hrk : RingOK st) : RingOK (markState st y) := hrk

/-! ## The cascade fold -/

/-- The cascade as a fold over the ancestor chain: each head pair `(y, z)` promotes the
marked child `y` out of `z`; the fold ends by marking the stopping ancestor. -/
def cascadeRun (st : HState) : List (ℕ × ℕ) → ℕ → HState
  | [], stop => markState st stop
  | (y, z) :: rest, stop => cascadeRun (promoteState st y z) rest stop

/-- One cell's premises: the promote's own preconditions — on the state that cell
actually runs in — and the rest of the chain on the state *after* that promote.
`promote_bridge` is how original-state facts produce the running-state premises. -/
def ChainOk (st : HState) : List (ℕ × ℕ) → Prop
  | [] => True
  | (y, z) :: rest => PromotePre st y z ∧ ChainOk (promoteState st y z) rest

/-! ## The premise bridge -/

/-- **The premise bridge.**  With `ChainOk` recursive on the running state, the next
cell's premises are already stated where they are consumed; the bridge only has to note
that `z ∈ kids b` survives the splice (`kids_promote_unchanged` — `b ≠ z`) and that `n`
is untouched.  The original-state-to-running-state lifting that callers need is exactly
`promoteState_mrk_z` (the hand-off), `promoteState_mrk_ne`, `promoteState_lft_ne` /
`promoteState_rgt_ne`, and `kids_promote_unchanged`, applied per component. -/
theorem promote_bridge (st : HState) (y z b : ℕ) (hpar : ParOK st)
    (hpre : PromotePre st y z) (hnext : PromotePre (promoteState st y z) z b)
    (hnoz : b ≠ z) : PromotePre (promoteState st y z) z b := by
  refine ⟨hnext.1, hnext.2.1, hnext.2.2.1, hnext.2.2.2.1, hnext.2.2.2.2.1,
    hnext.2.2.2.2.2⟩

/-- `cascadeRun_MarkOK`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_MarkOK (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    MarkOK st → ChainOk st chain → MarkOK (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hm _; exact mark_MarkOK st stop hm
  | cons head tail ih =>
    intro hm hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    exact ih (promoteState st y z) (promote_MarkOK st y z hm) hchain'
/-- `cascadeRun_ParSlot`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_ParSlot (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    ParSlot st → ChainOk st chain → ParSlot (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hps _; exact mark_ParSlot st stop hps
  | cons head tail ih =>
    intro hps hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    exact ih (promoteState st y z) (promote_ParSlot st y z hpre hps) hchain'
/-- `cascadeRun_ParOK`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_ParOK (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → ChainOk st chain → ParOK (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hpar hrk hnd hnl _; exact mark_ParOK st stop hpar
  | cons head tail ih =>
    intro hpar hrk hnd hnl hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    exact ih (promoteState st y z) hpar' hrk' hnd' hnl' hchain'
/-- `cascadeRun_KidsNodup`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_KidsNodup (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → ChainOk st chain → ∀ q, KidsNodup (cascadeRun st chain stop) q := by
  induction chain generalizing st with
  | nil => intro hpar hrk hnd hnl _; exact mark_KidsNodup st stop hnd
  | cons head tail ih =>
    intro hpar hrk hnd hnl hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    exact ih (promoteState st y z) hpar' hrk' hnd' hnl' hchain'
/-- `cascadeRun_PosOK`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_PosOK (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    MarkOK st → ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → PosOK st → ChainOk st chain → PosOK (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hm hpar hrk hnd hnl hpos _; exact mark_PosOK st stop hm hpos
  | cons head tail ih =>
    intro hm hpar hrk hnd hnl hpos hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hm' : MarkOK (promoteState st y z) := promote_MarkOK st y z hm
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    have hpos' : PosOK (promoteState st y z) := promote_PosOK st y z hrk hpar hpre hpos
    exact ih (promoteState st y z) hm' hpar' hrk' hnd' hnl' hpos' hchain'
/-- `cascadeRun_SlotOK`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_SlotOK (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → SlotOK st → ChainOk st chain → SlotOK (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hpar hrk hnd hnl hslot _; exact mark_SlotOK st stop hslot
  | cons head tail ih =>
    intro hpar hrk hnd hnl hslot hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    have hslot' : SlotOK (promoteState st y z) := promote_SlotOK st y z hrk hpar hpre hslot
    exact ih (promoteState st y z) hpar' hrk' hnd' hnl' hslot' hchain'
/-- `cascadeRun_Acyc`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_Acyc (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    NILSelf st → NILNotChild st → ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → Acyc st → ChainOk st chain → Acyc (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hns hnc hpar hrk hnd hnl hac _; exact mark_Acyc st stop hac
  | cons head tail ih =>
    intro hns hnc hpar hrk hnd hnl hac hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hns' : NILSelf (promoteState st y z) := promote_NILSelf st y z hpre hnc hns
    have hnc' : NILNotChild (promoteState st y z) :=
      promote_NILNotChild st y z hrk hpar hpre hnc
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    have hac' : Acyc (promoteState st y z) := promote_Acyc st y z hpre hns hac
    exact ih (promoteState st y z) hns' hnc' hpar' hrk' hnd' hnl' hac' hchain'
/-- `cascadeRun_NILRoots`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_NILRoots (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    NILRoots st → ChainOk st chain → NILRoots (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hnrs _; exact mark_NILRoots st stop hnrs
  | cons head tail ih =>
    intro hnrs hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    exact ih (promoteState st y z) (promote_NILRoots st y z hnrs) hchain'
/-- `cascadeRun_NILSelf`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_NILSelf (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    NILSelf st → NILNotChild st → ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → ChainOk st chain → NILSelf (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hs hnc hpar hrk hnd hnl _; exact mark_NILSelf st stop hs
  | cons head tail ih =>
    intro hs hnc hpar hrk hnd hnl hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hs' : NILSelf (promoteState st y z) := promote_NILSelf st y z hpre hnc hs
    have hnc' : NILNotChild (promoteState st y z) :=
      promote_NILNotChild st y z hrk hpar hpre hnc
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    exact ih (promoteState st y z) hs' hnc' hpar' hrk' hnd' hnl' hchain'
/-- `cascadeRun_NILNotRoot`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_NILNotRoot (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    NILNotRoot st → NILNotChild st → ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → ChainOk st chain → NILNotRoot (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hnn hnc hpar hrk hnd hnl _; exact mark_NILNotRoot st stop hnn
  | cons head tail ih =>
    intro hnn hnc hpar hrk hnd hnl hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hnn' : NILNotRoot (promoteState st y z) := promote_NILNotRoot st y z hpre hnc hnn
    have hnc' : NILNotChild (promoteState st y z) :=
      promote_NILNotChild st y z hrk hpar hpre hnc
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    exact ih (promoteState st y z) hnn' hnc' hpar' hrk' hnd' hnl' hchain'
/-- `cascadeRun_NILLeaf`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_NILLeaf (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    NILLeaf st → ChainOk st chain → NILLeaf (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hnl _; exact mark_NILLeaf st stop hnl
  | cons head tail ih =>
    intro hnl hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    exact ih (promoteState st y z) (promote_NILLeaf st y z hpre hnl) hchain'
/-- `cascadeRun_NILNotChild`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_NILNotChild (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → NILNotChild st → ChainOk st chain → NILNotChild (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hpar hrk hnd hnl hnc _; exact mark_NILNotChild st stop hnc
  | cons head tail ih =>
    intro hpar hrk hnd hnl hnc hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    have hnc' : NILNotChild (promoteState st y z) :=
      promote_NILNotChild st y z hrk hpar hpre hnc
    exact ih (promoteState st y z) hpar' hrk' hnd' hnl' hnc' hchain'
/-- `cascadeRun_RootNotChild`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_RootNotChild (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    RootNotChild st → ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → NILNotChild st → ChainOk st chain → RootNotChild (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hrnc hpar hrk hnd hnl hnc _; exact mark_RootNotChild st stop hrnc
  | cons head tail ih =>
    intro hrnc hpar hrk hnd hnl hnc hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    have hnc' : NILNotChild (promoteState st y z) :=
      promote_NILNotChild st y z hrk hpar hpre hnc
    have hrnc' : RootNotChild (promoteState st y z) :=
      promote_RootNotChild st y z hrk hpar hpre (hnd z) hnc hnl hrnc
    exact ih (promoteState st y z) hrnc' hpar' hrk' hnd' hnl' hnc' hchain'
/-- `cascadeRun_RootsLive`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_RootsLive (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    RootsLive st → ParOK st → RingOK st → (∀ q, KidsNodup st q) → NILLeaf st → SlotOK st →
    ChainOk st chain → RootsLive (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hrl hpar hrk hnd hnl hslot _; exact mark_RootsLive st stop hrl
  | cons head tail ih =>
    intro hrl hpar hrk hnd hnl hslot hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hrl' : RootsLive (promoteState st y z) :=
      promote_RootsLive st y z hrk hpre hslot hrl
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    have hslot' : SlotOK (promoteState st y z) := promote_SlotOK st y z hrk hpar hpre hslot
    exact ih (promoteState st y z) hrl' hpar' hrk' hnd' hnl' hslot' hchain'
/-- `cascadeRun_RingOK`: the invariant survives the whole cascade fold. -/
theorem cascadeRun_RingOK (st : HState) (stop : ℕ) (chain : List (ℕ × ℕ)) :
    RingOK st → ParOK st → (∀ q, KidsNodup st q) → NILLeaf st → ChainOk st chain → RingOK (cascadeRun st chain stop) := by
  induction chain generalizing st with
  | nil => intro hrk hpar hnd hnl _; exact mark_RingOK st stop hrk
  | cons head tail ih =>
    intro hrk hpar hnd hnl hchain
    obtain ⟨y, z⟩ := head
    obtain ⟨hpre, hchain'⟩ := hchain
    have hrk' : RingOK (promoteState st y z) := promote_RingOK st y z hrk hpar hpre hnl
    have hpar' : ParOK (promoteState st y z) := promote_ParOK st y z hpar hrk hpre (hnd z)
    have hnd' : ∀ q, KidsNodup (promoteState st y z) q :=
      promote_KidsNodup st y z hrk hpar hpre hnd
    have hnl' : NILLeaf (promoteState st y z) := promote_NILLeaf st y z hpre hnl
    exact ih (promoteState st y z) hrk' hpar' hnd' hnl' hchain'

/-! ## The decrease-key program -/

/-- **The decrease-key path**: cut `x` off `y` (marking `y`), then cascade the marked
ancestors up to the stopping ancestor, which the fold marks. -/
def decreaseKeyPath (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ) : HState :=
  cascadeRun (cutState st x y) chain stop

theorem decreaseKeyPath_MarkOK (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hm : MarkOK st) (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    MarkOK (decreaseKeyPath st x y chain stop) :=
  cascadeRun_MarkOK _ _ _ (cut_MarkOK st x y hm) hchain

theorem decreaseKeyPath_ParSlot (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hps : ParSlot st) (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    ParSlot (decreaseKeyPath st x y chain stop) :=
  cascadeRun_ParSlot _ _ _ (cut_ParSlot st x y hc hps) hchain

theorem decreaseKeyPath_ParOK (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hpar : ParOK st) (hrk : RingOK st) (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st)
    (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    ParOK (decreaseKeyPath st x y chain stop) :=
  cascadeRun_ParOK _ _ _ (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) hchain

theorem decreaseKeyPath_KidsNodup (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hpar : ParOK st) (hrk : RingOK st) (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st)
    (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    ∀ q, KidsNodup (decreaseKeyPath st x y chain stop) q :=
  cascadeRun_KidsNodup _ _ _ (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) hchain

theorem decreaseKeyPath_PosOK (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hm : MarkOK st) (hpar : ParOK st) (hrk : RingOK st) (hnd : ∀ q, KidsNodup st q)
    (hnl : NILLeaf st) (hpos : PosOK st) (hc : CutPre st x y)
    (hchain : ChainOk (cutState st x y) chain) :
    PosOK (decreaseKeyPath st x y chain stop) :=
  cascadeRun_PosOK _ _ _ (cut_MarkOK st x y hm) (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) (cut_PosOK st x y hrk hpar hc hpos) hchain

theorem decreaseKeyPath_SlotOK (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hpar : ParOK st) (hrk : RingOK st) (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st)
    (hslot : SlotOK st) (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    SlotOK (decreaseKeyPath st x y chain stop) :=
  cascadeRun_SlotOK _ _ _ (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) (cut_SlotOK st x y hrk hpar hc hslot) hchain

theorem decreaseKeyPath_Acyc (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hns : NILSelf st) (hnc : NILNotChild st) (hpar : ParOK st) (hrk : RingOK st)
    (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st) (hac : Acyc st) (hc : CutPre st x y)
    (hchain : ChainOk (cutState st x y) chain) :
    Acyc (decreaseKeyPath st x y chain stop) :=
  cascadeRun_Acyc _ _ _ (cut_NILSelf st x y hc hnc hns)
    (cut_NILNotChild st x y hrk hpar hc hnc)
    (cut_ParOK st x y hpar hrk hc (hnd y) ) (cut_RingOK st x y hrk hpar hc hnl)
    (cut_KidsNodup st x y hrk hpar hc hnd) (cut_NILLeaf st x y hc hnl)
    (cut_Acyc st x y hc hns hac) hchain

theorem decreaseKeyPath_NILRoots (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hnrs : NILRoots st) (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    NILRoots (decreaseKeyPath st x y chain stop) :=
  cascadeRun_NILRoots _ _ _ (cut_NILRoots st x y hnrs) hchain

theorem decreaseKeyPath_NILSelf (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hnc : NILNotChild st) (hs : NILSelf st) (hpar : ParOK st) (hrk : RingOK st)
    (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st) (hc : CutPre st x y)
    (hchain : ChainOk (cutState st x y) chain) :
    NILSelf (decreaseKeyPath st x y chain stop) :=
  cascadeRun_NILSelf _ _ _ (cut_NILSelf st x y hc hnc hs)
    (cut_NILNotChild st x y hrk hpar hc hnc) (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) hchain

theorem decreaseKeyPath_NILNotRoot (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hnn : NILNotRoot st) (hnc : NILNotChild st) (hpar : ParOK st) (hrk : RingOK st)
    (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st) (hc : CutPre st x y)
    (hchain : ChainOk (cutState st x y) chain) :
    NILNotRoot (decreaseKeyPath st x y chain stop) :=
  cascadeRun_NILNotRoot _ _ _ (cut_NILNotRoot st x y hc hnc hnn)
    (cut_NILNotChild st x y hrk hpar hc hnc) (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) hchain

theorem decreaseKeyPath_NILLeaf (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hnl : NILLeaf st) (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    NILLeaf (decreaseKeyPath st x y chain stop) :=
  cascadeRun_NILLeaf _ _ _ (cut_NILLeaf st x y hc hnl) hchain

theorem decreaseKeyPath_NILNotChild (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hpar : ParOK st) (hrk : RingOK st) (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st)
    (hnc : NILNotChild st) (hc : CutPre st x y)
    (hchain : ChainOk (cutState st x y) chain) :
    NILNotChild (decreaseKeyPath st x y chain stop) :=
  cascadeRun_NILNotChild _ _ _ (cut_ParOK st x y hpar hrk hc (hnd y))
    (cut_RingOK st x y hrk hpar hc hnl) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) (cut_NILNotChild st x y hrk hpar hc hnc) hchain

theorem decreaseKeyPath_RootNotChild (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ))
    (stop : ℕ) (hrnc : RootNotChild st) (hpar : ParOK st) (hrk : RingOK st)
    (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st) (hnc : NILNotChild st)
    (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    RootNotChild (decreaseKeyPath st x y chain stop) :=
  cascadeRun_RootNotChild _ _ _ (cut_RootNotChild st x y hrk hpar hc (hnd y) hnc hnl hrnc)
    (cut_ParOK st x y hpar hrk hc (hnd y)) (cut_RingOK st x y hrk hpar hc hnl)
    (cut_KidsNodup st x y hrk hpar hc hnd) (cut_NILLeaf st x y hc hnl)
    (cut_NILNotChild st x y hrk hpar hc hnc) hchain

theorem decreaseKeyPath_RootsLive (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hrl : RootsLive st) (hpar : ParOK st) (hrk : RingOK st)
    (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st) (hslot : SlotOK st) (hc : CutPre st x y)
    (hchain : ChainOk (cutState st x y) chain) :
    RootsLive (decreaseKeyPath st x y chain stop) :=
  cascadeRun_RootsLive _ _ _ (cut_RootsLive st x y hrk hc hslot hrl)
    (cut_ParOK st x y hpar hrk hc (hnd y)) (cut_RingOK st x y hrk hpar hc hnl)
    (cut_KidsNodup st x y hrk hpar hc hnd) (cut_NILLeaf st x y hc hnl)
    (cut_SlotOK st x y hrk hpar hc hslot) hchain

theorem decreaseKeyPath_RingOK (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
    (hrk : RingOK st) (hpar : ParOK st) (hnd : ∀ q, KidsNodup st q) (hnl : NILLeaf st)
    (hc : CutPre st x y) (hchain : ChainOk (cutState st x y) chain) :
    RingOK (decreaseKeyPath st x y chain stop) :=
  cascadeRun_RingOK _ _ _ (cut_RingOK st x y hrk hpar hc hnl)
    (cut_ParOK st x y hpar hrk hc (hnd y)) (cut_KidsNodup st x y hrk hpar hc hnd)
    (cut_NILLeaf st x y hc hnl) hchain

/-! ## The decrease-key path's output witness -/

/-- The path witness's pre-state: NIL at slot 0; the root slot 4 holds marked child 3,
which holds child 2, which holds the cut child 1, which holds its own child 5. -/
def casPreSt : HState where
  par := fun i => if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else if i = 5 then 1 else 0
  chd := fun i => if i = 1 then 5 else if i = 2 then 1 else if i = 3 then 2 else if i = 4 then 3 else 0
  rgt := fun i => if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 0
  lft := fun i => if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4 else if i = 5 then 5 else 0
  deg := fun i => if i = 1 then 1 else if i = 2 then 1 else if i = 3 then 1 else if i = 4 then 1 else 0
  mrk := fun i => if i = 3 then 1 else 0
  roots := [4]
  n := 6

/-- The decrease-key path's output: the cut child `1` is re-rooted with its own subtree
intact, the promoted ancestors `2`, `3` join it as roots with their marks cleared, and
the stopping ancestor `4` is left marked. -/
def casOut : HState := decreaseKeyPath casPreSt 1 2 [(2, 3), (3, 4)] 4

@[simp] theorem casOut_par (v : ℕ) : casOut.par v = if v = 5 then 1 else 0 := by
  by_cases h1 : v = 1
  · subst h1
    simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
      casPreSt]
  · by_cases h2 : v = 2
    · subst h2
      simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
        casPreSt]
    · by_cases h3 : v = 3
      · subst h3
        simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
          casPreSt]
      · by_cases h4 : v = 4
        · subst h4
          simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
            casPreSt]
        · by_cases h5 : v = 5
          · subst h5
            simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt]
          · simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt, h1, h2, h3, h4]

@[simp] theorem casOut_mrk (v : ℕ) : casOut.mrk v = if v = 4 then 1 else 0 := by
  by_cases h1 : v = 1
  · subst h1
    simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
      casPreSt]
  · by_cases h2 : v = 2
    · subst h2
      simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
        casPreSt]
    · by_cases h3 : v = 3
      · subst h3
        simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
          casPreSt]
      · by_cases h4 : v = 4
        · subst h4
          simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
            casPreSt]
        · by_cases h5 : v = 5
          · subst h5
            simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt]
          · simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt, h1, h2, h3, h4]

@[simp] theorem casOut_deg (v : ℕ) : casOut.deg v = if v = 1 then 1 else 0 := by
  by_cases h1 : v = 1
  · subst h1
    simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
      casPreSt]
  · by_cases h2 : v = 2
    · subst h2
      simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
        casPreSt]
    · by_cases h3 : v = 3
      · subst h3
        simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
          casPreSt]
      · by_cases h4 : v = 4
        · subst h4
          simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
            casPreSt]
        · by_cases h5 : v = 5
          · subst h5
            simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt]
          · simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt, h1, h2, h3, h4]

@[simp] theorem casOut_chd (v : ℕ) : casOut.chd v = if v = 1 then 5 else 0 := by
  by_cases h1 : v = 1
  · subst h1
    simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
      casPreSt]
  · by_cases h2 : v = 2
    · subst h2
      simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
        casPreSt]
    · by_cases h3 : v = 3
      · subst h3
        simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
          casPreSt]
      · by_cases h4 : v = 4
        · subst h4
          simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
            casPreSt]
        · by_cases h5 : v = 5
          · subst h5
            simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt]
          · simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt, h1, h2, h3, h4]

@[simp] theorem casOut_rgt (v : ℕ) :
    casOut.rgt v = if v = 1 then 1 else if v = 2 then 2 else if v = 3 then 3 else if v = 4 then 4 else if v = 5 then 5 else 0 := by
  by_cases h1 : v = 1
  · subst h1
    simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
      casPreSt]
  · by_cases h2 : v = 2
    · subst h2
      simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
        casPreSt]
    · by_cases h3 : v = 3
      · subst h3
        simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
          casPreSt]
      · by_cases h4 : v = 4
        · subst h4
          simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
            casPreSt]
        · by_cases h5 : v = 5
          · subst h5
            simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt]
          · simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt, h1, h2, h3, h4]

@[simp] theorem casOut_lft (v : ℕ) :
    casOut.lft v = if v = 1 then 1 else if v = 2 then 2 else if v = 3 then 3 else if v = 4 then 4 else if v = 5 then 5 else 0 := by
  by_cases h1 : v = 1
  · subst h1
    simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
      casPreSt]
  · by_cases h2 : v = 2
    · subst h2
      simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
        casPreSt]
    · by_cases h3 : v = 3
      · subst h3
        simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
          casPreSt]
      · by_cases h4 : v = 4
        · subst h4
          simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState, promoteState,
            casPreSt]
        · by_cases h5 : v = 5
          · subst h5
            simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt]
          · simp [casOut, decreaseKeyPath, cascadeRun, markState, cutState,
              promoteState, casPreSt, h1, h2, h3, h4]

@[simp] theorem kids_casOut (q : ℕ) : kids casOut q = if q = 1 then [5] else [] := by
  unfold kids casOut decreaseKeyPath cascadeRun cutState promoteState casPreSt
  by_cases h1 : q = 1
  · subst h1; rfl
  · by_cases h2 : q = 2
    · subst h2; rfl
    · by_cases h3 : q = 3
      · subst h3; rfl
      · by_cases h4 : q = 4
        · subst h4; rfl
        · by_cases h5 : q = 5
          · subst h5; rfl
          · rfl

/-! ### The pre-state satisfies the bundle -/

theorem cas_MarkOK : MarkOK casPreSt := by
  intro q
  by_cases h : q = 3
  · subst h; simp [casPreSt]
  · simp [casPreSt, h]

theorem cas_ParSlot : ParSlot casPreSt := by
  intro q hq
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    by_cases hq5 : q = 5 <;> simp [casPreSt, hq1, hq2, hq3, hq4, hq5]

theorem cas_ParOK : ParOK casPreSt := by
  intro q v hv
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    simp [kids, casPreSt, hq1, hq2, hq3, hq4, hv] at hv ⊢

theorem cas_KidsNodup : ∀ q, KidsNodup casPreSt q := by
  intro q j k hjk hk
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    simp [kids, casPreSt, hq1, hq2, hq3, hq4, hjk, hk] at hjk hk ⊢

theorem cas_SlotOK : SlotOK casPreSt := by
  intro q hq v hv
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    simp [kids, casPreSt, hq1, hq2, hq3, hq4, hv] at hv ⊢

theorem cas_PosOK : PosOK casPreSt := by
  intro q j hj
  have hq : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
    by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
      simp_all
  rcases hq with rfl | rfl | rfl | rfl
  · unfold kids at hj
    simp [casPreSt] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact Nat.zero_le _
  · unfold kids at hj
    simp [casPreSt] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact Nat.zero_le _
  · unfold kids at hj
    simp [casPreSt] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact Nat.zero_le _
  · unfold kids at hj
    simp [casPreSt] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact Nat.zero_le _

theorem cas_Acyc : Acyc casPreSt := by
  intro x j hj heq
  have hpos5 : ∀ Y : ℕ, casPreSt.par Y ≠ 5 := fun Y => by simp [casPreSt]
  have hne : ∀ k : ℕ, 0 < k → (casPreSt.par)^[k] 5 ≠ 5 := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hpos5 _
  by_cases hx5 : x = 5
  · subst hx5
    rcases Nat.lt_or_ge j 1 with h0 | h1
    · have hj1 : j = 0 := by omega
      subst hj1
      rw [Function.iterate_zero] at heq
      omega
    · exact absurd heq (hne j h0)
  · have hx0 : casPreSt.par x = 0 := by
      by_cases hx1 : x = 1 <;> by_cases hx2 : x = 2 <;> by_cases hx3 : x = 3 <;> by_cases hx4 : x = 4 <;>
        simp [casPreSt, hx5, hx1, hx2, hx3, hx4]
    cases j with
    | zero => omega
    | succ k =>
      have hall : ∀ m : ℕ, (casPreSt.par)^[m + 1] x = 0 := by
        intro m
        induction m with
        | zero => exact hx0
        | succ m ih =>
          rw [Function.iterate_succ_apply']
          simp [ih, casPreSt]
      rw [hall k] at heq
      exact heq.symm

theorem cas_NILRoots : NILRoots casPreSt := by
  intro r hr
  simp only [casPreSt] at hr
  simp at hr
  subst hr
  simp [casPreSt]

theorem cas_NILSelf : NILSelf casPreSt := rfl

theorem cas_NILNotRoot : NILNotRoot casPreSt := by
  intro h
  simp [casPreSt] at h

theorem cas_NILLeaf : NILLeaf casPreSt := rfl

theorem cas_NILNotChild : NILNotChild casPreSt := by
  intro q hv
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    simp [kids, casPreSt, hq1, hq2, hq3, hq4, hv] at hv

theorem cas_RootNotChild : RootNotChild casPreSt := by
  intro r hr q _ hv
  simp only [casPreSt] at hr
  simp at hr
  subst hr
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    simp [kids, casPreSt, hq1, hq2, hq3, hq4, hv] at hv ⊢

theorem cas_RootsLive : RootsLive casPreSt := by
  intro r hr
  simp only [casPreSt] at hr
  simp at hr
  subst hr
  simp [casPreSt]

theorem cas_RingOK : RingOK casPreSt := by
  intro q
  by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;> by_cases hq3 : q = 3 <;> by_cases hq4 : q = 4 <;>
    simp [casPreSt, hq1, hq2, hq3, hq4]

/-! ### The cut and the chain premises, concretely -/

theorem cas_CutPre : CutPre casPreSt 1 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold kids
    simp [casPreSt]
  · simp [casPreSt]
  · simp [casPreSt]
  · simp [casPreSt]
  · intro h
    exact absurd h (by simp [casPreSt])

theorem cas_chainOk : ChainOk (cutState casPreSt 1 2) [(2, 3), (3, 4)] := by
  have hpre23 : PromotePre (cutState casPreSt 1 2) 2 3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold kids
      simp [cutState, casPreSt]
    · simp [cutState, casPreSt]
    · exact cutState_mrk_y casPreSt 1 2
    · rw [cutState_mrk_ne casPreSt 1 2 3 (by decide)]
      simp [casPreSt]
    · simp [cutState, casPreSt]
    · intro h
      exact absurd h (by simp [cutState, casPreSt])
  have hpre34 : PromotePre (cutState casPreSt 1 2) 3 4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold kids
      simp [cutState, casPreSt]
    · simp [cutState, casPreSt]
    · rw [cutState_mrk_ne casPreSt 1 2 3 (by decide)]
      simp [casPreSt]
    · simp [cutState, casPreSt]
    · simp [cutState, casPreSt]
    · intro h
      exact absurd h (by simp [cutState, casPreSt])
  have hpar : ParOK (cutState casPreSt 1 2) :=
    cut_ParOK casPreSt 1 2 cas_ParOK cas_RingOK cas_CutPre cas_NILLeaf
  refine ⟨hpre23, ⟨hpre34, trivial⟩⟩

/-! ### The output state satisfies the bundle -/

theorem casOut_MarkOK : MarkOK casOut :=
  decreaseKeyPath_MarkOK casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_MarkOK cas_CutPre cas_chainOk

theorem casOut_ParSlot : ParSlot casOut :=
  decreaseKeyPath_ParSlot casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_ParSlot cas_CutPre cas_chainOk

theorem casOut_ParOK : ParOK casOut :=
  decreaseKeyPath_ParOK casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_ParOK cas_RingOK cas_KidsNodup
    cas_NILLeaf cas_CutPre cas_chainOk

theorem casOut_KidsNodup : ∀ q, KidsNodup casOut q :=
  decreaseKeyPath_KidsNodup casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_ParOK cas_RingOK
    cas_KidsNodup cas_NILLeaf cas_CutPre cas_chainOk

theorem casOut_PosOK : PosOK casOut :=
  decreaseKeyPath_PosOK casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_MarkOK cas_ParOK cas_RingOK
    cas_KidsNodup cas_NILLeaf cas_PosOK cas_CutPre cas_chainOk

theorem casOut_SlotOK : SlotOK casOut :=
  decreaseKeyPath_SlotOK casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_ParOK cas_RingOK cas_KidsNodup
    cas_NILLeaf cas_SlotOK cas_CutPre cas_chainOk

theorem casOut_Acyc : Acyc casOut :=
  decreaseKeyPath_Acyc casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_NILSelf cas_NILNotChild cas_ParOK
    cas_RingOK cas_KidsNodup cas_NILLeaf cas_Acyc cas_CutPre cas_chainOk

theorem casOut_NILRoots : NILRoots casOut :=
  decreaseKeyPath_NILRoots casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_NILRoots cas_CutPre cas_chainOk

theorem casOut_NILSelf : NILSelf casOut :=
  decreaseKeyPath_NILSelf casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_NILNotChild cas_NILSelf
    cas_ParOK cas_RingOK cas_KidsNodup cas_NILLeaf cas_CutPre cas_chainOk

theorem casOut_NILNotRoot : NILNotRoot casOut :=
  decreaseKeyPath_NILNotRoot casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_NILNotRoot cas_NILNotChild
    cas_ParOK cas_RingOK cas_KidsNodup cas_NILLeaf cas_CutPre cas_chainOk

theorem casOut_NILLeaf : NILLeaf casOut :=
  decreaseKeyPath_NILLeaf casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_NILLeaf cas_CutPre cas_chainOk

theorem casOut_NILNotChild : NILNotChild casOut :=
  decreaseKeyPath_NILNotChild casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_ParOK cas_RingOK
    cas_KidsNodup cas_NILLeaf cas_NILNotChild cas_CutPre cas_chainOk

theorem casOut_RootNotChild : RootNotChild casOut :=
  decreaseKeyPath_RootNotChild casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_RootNotChild cas_ParOK
    cas_RingOK cas_KidsNodup cas_NILLeaf cas_NILNotChild cas_CutPre cas_chainOk

theorem casOut_RootsLive : RootsLive casOut :=
  decreaseKeyPath_RootsLive casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_RootsLive cas_ParOK
    cas_RingOK cas_KidsNodup cas_NILLeaf cas_CutPre cas_chainOk

theorem casOut_RingOK : RingOK casOut :=
  decreaseKeyPath_RingOK casPreSt 1 2 [(2, 3), (3, 4)] 4 cas_RingOK cas_ParOK cas_KidsNodup
    cas_NILLeaf cas_CutPre cas_chainOk

/-- The path output satisfies the support condition at the re-rooted child: its
abstraction is the two-node tree over slots 1, 5. -/
theorem casOut_Support : Support casOut (casOut.n + 1) 1 := by
  refine ⟨{1, 5}, ?_, ?_⟩
  · have hshape : treeOf casOut (casOut.n + 1) 1
        = FibHeapForest.Tree.node 1
            [FibHeapForest.Child.mk (treeOf casOut 6 5) (ldeg casOut 5) (casOut.mrk 5)] := by
      simp [treeOf, kids_casOut_one, kids_casOut_ne]
    rw [hshape, FibHeapForest.size_node, FibHeapForest.sizeSum]
    simp [FibHeapForest.Child.size, FibHeapForest.Child.tree, FibHeapForest.size_node,
      FibHeapForest.sizeSum, treeOf, kids_casOut_one, kids_casOut_ne]
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp

/-- **The capstone applied to the decrease-key path's output.**  The program keeps the
machine inside the invariant set, so the rank cap applies to the freshly cut root. -/
theorem casOut_capstone : casOut.deg 1 ≤ FibHeapAccounting.rankCap casOut.n := by
  have hsup := casOut_Support
  have hpn : casOut.n + 1 = 7 := by rw [casOut_n]
  rw [casOut_n] at hsup ⊢
  exact degree_le_rankCap_zero casOut casOut_ParOK casOut_SlotOK casOut_ParSlot
    casOut_KidsNodup casOut_Acyc casOut_NILSelf casOut_NILLeaf casOut_NILNotChild
    casOut_MarkOK casOut_PosOK (by simp) (by simp) hsup

end Submission.FibHeapCascade
