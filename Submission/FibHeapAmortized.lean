/-
The n-log row's aggregate: a sequence of decrease-key operations under a
per-op cascade cap `L`.

Each step of a `DkRun` carries its full witness relative to the running
state (`cutState` precondition, `MarkChain` consolidation discipline) and
its own cap instance `chain.length ≤ L`.  The per-op bounds telescope:
the potential terms cancel along the run, leaving

    Φ(last) ≤ Φ(first) + count * (L + 5)                (unscaled)
    K·Φ(last) ≤ K·Φ(first) + count * K * (L + 5)        (scaled)

— the amortization ledger's aggregate form.  The potential rise of the
whole run is covered by `count * (L + 5)`, which is the cost class the
run's own cascade work pays for.

Scope notes (carried, not papered):
- **Transfer seam.**  This aggregate inherits the measure lane's transfer
  mark discipline (`FibHeapMeasure` header): the cut banks one fresh mark
  and each consolidation cell moves it one link up, so the per-op bound is
  `Φ'' ≤ Φ + len + 5` — linear in the cascade length.  The CLRS
  clear-per-step discipline would give the c-independent corollary
  (`Φ'' + c ≤ Φ + 4`, hence a `count * 5`-class bound); reaching it here
  needs a clear-semantics cascade and is the cross-lane todo.
- **The `L := log n` instantiation.**  The cap is a hypothesis of every
  step.  Supplying `L := FibHeapAccounting.rankCap n` (or `log₂ n`)
  requires the depth recount: chain lengths bounded by the tree depth
  that the root-count/degree bound (`root_count_bound` with
  `B = rankCap n`) controls.  That recount is the next module; it is not
  claimed here.
-/
import Submission.FibHeapMeasure
import Submission.FibHeapScaled
import Submission.FibHeapAccounting

namespace Submission.FibHeapAmortized

open Submission.FibHeapMeasure Submission.FibHeapScaled Submission.FibHeapRefine
open Submission.FibHeapCut Submission.FibHeapPromote Submission.FibHeapCascade

/-- A run of decrease-key operations under the per-op cascade cap `L`.
Each `cons` step carries its witness data relative to the running state;
the run's state threads through `decreaseKeyPath`. -/
inductive DkRun (L : ℕ) : HState → Type where
  | nil (st : HState) : DkRun L st
  | cons (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
      (hyn : y < st.n) (hy0 : st.mrk y = 0)
      (hmc : MarkChain (cutState st x y) st.n chain)
      (hlen : chain.length ≤ L)
      (rest : DkRun L (decreaseKeyPath st x y chain stop)) : DkRun L st

/-- The run's final state. -/
def DkRun.last {L : ℕ} {st : HState} : DkRun L st → HState
  | .nil _ => st
  | .cons _ _ _ _ _ _ _ _ _ rest => DkRun.last rest

/-- The run's operation count. -/
def DkRun.count {L : ℕ} {st : HState} : DkRun L st → ℕ
  | .nil _ => 0
  | .cons _ _ _ _ _ _ _ _ _ rest => DkRun.count rest + 1

/-- The live size is untouched along a run: cut, mark, promote, and the cascade
fold all keep `n`. -/
theorem DkRun.last_n {L : ℕ} {st : HState} : ∀ (s : DkRun L st), s.last.n = st.n := by
  intro s
  induction s with
  | nil => rfl
  | cons st x y chain stop hyn hy0 hmc hlen rest ih =>
    simp only [DkRun.last] at ih ⊢
    rw [ih]
    have h : (decreaseKeyPath st x y chain stop).n = st.n := by
      simp only [decreaseKeyPath, cascadeRun_n, cutState_n]
    exact h

/-- **The aggregate (unscaled).**  A capped run raises the machine
potential by at most `count * (L + 5)` — the per-op bounds telescope,
the intermediate potentials cancel. -/
theorem DkRun.potential_cap {L : ℕ} {st : HState} : ∀ (s : DkRun L st),
    machinePotential s.last ≤ machinePotential st + s.count * (L + 5) := by
  intro s
  induction s with
  | nil => simp only [DkRun.last, DkRun.count]; omega
  | cons st x y chain stop hyn hy0 hmc hlen rest ih =>
    simp only [DkRun.last, DkRun.count]
    have hstep := decreaseKeyPath_potential st x y chain stop hyn hy0 hmc
    calc machinePotential rest.last
        ≤ machinePotential (decreaseKeyPath st x y chain stop)
          + DkRun.count rest * (L + 5) := ih
      _ ≤ machinePotential st + (chain.length + 5)
          + DkRun.count rest * (L + 5) := by omega
      _ ≤ machinePotential st + (DkRun.count rest + 1) * (L + 5) := by
          simp only [Nat.add_mul]; omega

/-- **The aggregate (scaled).**  The same telescope in the accounting
lane's ledger units: `K·Φ(last) ≤ K·Φ(first) + count * K * (L + 5)` —
`Nat.mul_le_mul_left`, the accounting lane's own step, lifts the per-op
scaled bound. -/
theorem DkRun.potential_scaled_cap {L : ℕ} {st : HState} : ∀ {K : ℕ}
    (s : DkRun L st),
    K * machinePotential s.last
      ≤ K * machinePotential st + s.count * K * (L + 5) := by
  intro K s
  induction s with
  | nil => simp only [DkRun.last, DkRun.count]; omega
  | cons st x y chain stop hyn hy0 hmc hlen rest ih =>
    simp only [DkRun.last, DkRun.count]
    have hstep : K * machinePotential (decreaseKeyPath st x y chain stop)
        ≤ K * machinePotential st + K * (chain.length + 5) := by
      have h1 := decreaseKeyPath_scaled (K := K) st x y chain stop hyn hy0 hmc
      simpa only [machinePotential_eq_potential, FibHeapAccounting.scaledPotential,
        FibHeapAccounting.potential] using h1
    have hcap : K * (chain.length + 5) ≤ K * (L + 5) :=
      Nat.mul_le_mul_left K (by omega)
    calc K * machinePotential rest.last
        ≤ K * machinePotential (decreaseKeyPath st x y chain stop)
          + DkRun.count rest * K * (L + 5) := ih
      _ ≤ K * machinePotential st + K * (chain.length + 5)
          + DkRun.count rest * K * (L + 5) := by omega
      _ ≤ K * machinePotential st + (DkRun.count rest + 1) * K * (L + 5) := by
          simp only [Nat.add_mul, Nat.one_mul]; omega

/-! ## The clearing run: Route A's aggregate (the `n log` per-op form) -/

/-- **The clearing run.**  `DkRun`'s CLRS-write sibling: each step carries the
cut's slot/mark data, `MarkOK`, the clearing chain witness, and the per-step
cascade cap (`chain.length ≤ L`).  The per-op bound is **c-independent**
(`decreaseKeyPathClear_potential`: `Φ' ≤ Φ + 5`), so the aggregate is
`count * 5` — the `n log` form's decrease-key half (the transfer `DkRun`'s
`count * (L + 5)` grows with the live size through `L`). -/
inductive DkRunClear (L : ℕ) : HState → Type where
  | nil (st : HState) : DkRunClear L st
  | cons (st : HState) (x y : ℕ) (chain : List (ℕ × ℕ)) (stop : ℕ)
      (hyn : y < st.n) (hy0 : st.mrk y = 0) (hm : MarkOK st)
      (hcc : ClearChain (cutState st x y) st.n chain)
      (hlen : chain.length ≤ L)
      (rest : DkRunClear L (decreaseKeyPathClear st x y chain stop)) : DkRunClear L st

/-- The clearing run's final state. -/
def DkRunClear.last {L : ℕ} {st : HState} : DkRunClear L st → HState
  | .nil s => s
  | .cons _ _ _ _ _ _ _ _ _ _ rest => DkRunClear.last rest

/-- The clearing run's operation count. -/
def DkRunClear.count {L : ℕ} {st : HState} : DkRunClear L st → ℕ
  | .nil _ => 0
  | .cons _ _ _ _ _ _ _ _ _ _ rest => DkRunClear.count rest + 1

/-- **The clearing aggregate.**  The per-op bound is constant (`+5`: the
cut's `+3` plus the cascade's stop `+2`), so the run telescopes at
`count * 5` — independent of both the cascade lengths and the live size. -/
theorem DkRunClear.potential_clrs {L : ℕ} {st : HState} : ∀ (s : DkRunClear L st),
    machinePotential s.last ≤ machinePotential st + s.count * 5 := by
  intro s
  induction s with
  | nil => simp only [DkRunClear.last, DkRunClear.count]; omega
  | cons st x y chain stop hyn hy0 hm hcc hlen rest ih =>
    simp only [DkRunClear.last, DkRunClear.count] at ih ⊢
    have hstep := decreaseKeyPathClear_potential st x y chain stop hyn hy0 hm hcc
    calc machinePotential rest.last
        ≤ machinePotential (decreaseKeyPathClear st x y chain stop)
            + DkRunClear.count rest * 5 := ih
      _ ≤ machinePotential st + 5 + DkRunClear.count rest * 5 := by omega
      _ = machinePotential st + (DkRunClear.count rest + 1) * 5 := by
            simp only [Nat.add_mul, Nat.one_mul]; omega

/-- **The clearing run's scaled aggregate: the machine's FT per-op charge.**
Each step is charged `D0 + 6K + D1`: a cascaded step via the machine-ledger
lift `decrease_amortized_of_clearCascadeRun` (`c := chain.length`, the
count-level mark ledger as `hmarks`) — whose fold-segment charge
`D0 + 3K + D1` plus the cut's own `+3K` potential rise gives the full-op
unit — and an empty-chain step via the stop's `+≤2` (`5K ≤` the charge).
Telescoping over the run: the scaled potential of the final state exceeds
the first state's by at most `count * (D0 + 6K + D1)`.  Residual named: the
literal CLRS charge `D0 + 3K + D1` for the full op is not derivable in this
model — the fresh-parent run banks a new mark at every cut and the terminal
leaves it spent, so the amortized unit carries the cut's `3K` on top of the
fold's `3K + D0 + D1`; reaching `3K` needs the old-mark cascade shape (where
the cut banks nothing) or an explicit work-sum on the run.  The `n log`
form's decrease-key half at the FT-1987 per-op bound class (bound theirs,
formalization ours); the transfer seam remains the stated accounting
boundary. -/
theorem DkRunClear.potential_scaled_ft {L : ℕ} {st : HState} :
    ∀ {K D0 D1 : ℕ} (hK : D1 ≤ K) (s : DkRunClear L st),
    FibHeapAccounting.scaledPotential K s.last.roots.length (machineMarks s.last)
      ≤ FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
        + DkRunClear.count s * (D0 + 6 * K + D1) := by
  intro K D0 D1 hK s
  induction s with
  | nil => simp only [DkRunClear.last, DkRunClear.count]; omega
  | cons st x y chain stop hyn hy0 hm hcc hlen rest ih =>
    simp only [DkRunClear.last, DkRunClear.count] at ih ⊢
    -- the cut's potential step: Φ(cut) = Φ(st) + 3, scaled + 3K
    have hcutroots : (cutState st x y).roots.length = st.roots.length + 1 := by
      rw [cutState_roots]; simp
    have hcutmarks : machineMarks (cutState st x y) = machineMarks st + 1 :=
      machineMarks_cutState st x y hyn hy0
    have hcutscaled : FibHeapAccounting.scaledPotential K (cutState st x y).roots.length
        (machineMarks (cutState st x y))
        = FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st) + 3 * K := by
      simp only [FibHeapAccounting.scaledPotential, FibHeapAccounting.potential,
        hcutroots, hcutmarks]
      ring
    -- the per-op segment: cut → fold output, charged once
    have hperop : FibHeapAccounting.scaledPotential K
        (decreaseKeyPathClear st x y chain stop).roots.length
        (machineMarks (decreaseKeyPathClear st x y chain stop))
        ≤ FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
          + (D0 + 6 * K + D1) := by
      by_cases hc : 1 ≤ chain.length
      · have hlift := decrease_amortized_of_clearCascadeRun (K := K) (D0 := D0) (D1 := D1)
          (s := cutState st x y) (chain := chain) (stop := stop) hK hc rfl rfl rfl rfl
          (cut_MarkOK st x y hm) (by rw [cutState_n]; exact hcc)
        have hconv1 : (decreaseKeyPathClear st x y chain stop).roots.length
            = (clearCascadeRun (cutState st x y) chain stop).roots.length := rfl
        have hconv2 : machineMarks (decreaseKeyPathClear st x y chain stop)
            = machineMarks (clearCascadeRun (cutState st x y) chain stop) := rfl
        rw [hconv1, hconv2]
        omega
      · -- empty chain: the fold is the stop's mark only (+≤1 mark, +0 roots)
        have hchain : chain = [] := by
          cases chain with
          | nil => rfl
          | cons p l => exfalso; simp at hc
        subst hchain
        have hmark := machineMarks_markState_le (cutState st x y) stop
        have hroots : (markState (cutState st x y) stop).roots.length
            = (cutState st x y).roots.length := by rw [markState_roots]
        have hle : machinePotential (markState (cutState st x y) stop)
            ≤ machinePotential (cutState st x y) + 2 := by
          simp only [machinePotential, hroots]
          omega
        have hdef : decreaseKeyPathClear st x y [] stop
            = markState (cutState st x y) stop := rfl
        have e1 : FibHeapAccounting.scaledPotential K
              (markState (cutState st x y) stop).roots.length
              (machineMarks (markState (cutState st x y) stop))
            = K * machinePotential (markState (cutState st x y) stop) := rfl
        have e2 : FibHeapAccounting.scaledPotential K (cutState st x y).roots.length
              (machineMarks (cutState st x y))
            = K * machinePotential (cutState st x y) := rfl
        have hstep : FibHeapAccounting.scaledPotential K
              (decreaseKeyPathClear st x y [] stop).roots.length
              (machineMarks (decreaseKeyPathClear st x y [] stop))
            ≤ FibHeapAccounting.scaledPotential K (cutState st x y).roots.length
                (machineMarks (cutState st x y)) + 2 * K := by
          rw [hdef, e1, e2]
          exact le_trans (Nat.mul_le_mul_left K hle)
            (by rw [Nat.mul_add]; omega)
        omega
    calc FibHeapAccounting.scaledPotential K rest.last.roots.length
            (machineMarks rest.last)
        ≤ FibHeapAccounting.scaledPotential K
            (decreaseKeyPathClear st x y chain stop).roots.length
            (machineMarks (decreaseKeyPathClear st x y chain stop))
          + DkRunClear.count rest * (D0 + 6 * K + D1) := ih
      _ ≤ FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
            + (D0 + 6 * K + D1) + DkRunClear.count rest * (D0 + 6 * K + D1) := by omega
      _ = FibHeapAccounting.scaledPotential K st.roots.length (machineMarks st)
            + (DkRunClear.count rest + 1) * (D0 + 6 * K + D1) := by
          ring

end Submission.FibHeapAmortized
