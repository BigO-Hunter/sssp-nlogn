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

end Submission.FibHeapAmortized
