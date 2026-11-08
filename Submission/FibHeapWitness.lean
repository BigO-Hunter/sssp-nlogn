import Submission.FibHeapSupportSet
import Submission.FibHeapLink

/-!
# M2c: the satisfiability witness — the capstone is non-vacuous

`degree_le_rankCap_zero`'s premise set changed in the acyclicity redesign (the old `NoCycle` was
unsatisfiable for a total `par` on finite slots, which made the capstone vacuous).  This module
ends that: `witness` is a concrete `HState` — slot 0 the NIL sentinel, slot 1 a single live root
with an empty child list, `roots = [1]`, `n = 2` — and every premise of the capstone is proved of
it, so the capstone **applies** to a real state: `witness.deg 1 = 0 ≤ rankCap 2 = 3`.

Non-vacuity is now a theorem, not a hope: the capstone's premise set has a model.
-/

namespace Submission.FibHeapWitness

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport Submission.FibHeapLink

/-- The witness state: NIL at slot 0, one live root at slot 1. -/
def witness : HState where
  par := fun _ => 0
  chd := fun _ => 0
  rgt := fun _ => 0
  lft := fun _ => 0
  deg := fun _ => 0
  mrk := fun _ => 0
  roots := [1]
  n := 2

@[simp] theorem kids_witness (q : ℕ) : kids witness q = [] := by
  simp [kids, witness]

theorem witness_ParOK : ParOK witness := by
  intro q v hv
  rw [kids_witness] at hv
  cases hv

theorem witness_SlotOK : SlotOK witness := by
  intro q hq v hv
  rw [kids_witness] at hv
  cases hv

theorem witness_ParSlot : ParSlot witness := by
  intro q _
  simp [witness]

theorem witness_KidsNodup : ∀ q, KidsNodup witness q := by
  intro q j k _ hk _
  simp [witness] at hk

theorem witness_NILRoots : NILRoots witness := by
  intro r hr
  simp [witness] at hr ⊢

theorem witness_NILSelf : NILSelf witness := rfl

theorem witness_NILNotChild : NILNotChild witness := by
  intro q hv
  rw [kids_witness] at hv
  cases hv

theorem witness_RootNotChild : RootNotChild witness := by
  intro r hr q _ hv
  rw [kids_witness] at hv
  cases hv

theorem witness_RootsLive : RootsLive witness := by
  intro r hr
  simp [witness] at hr ⊢
  omega

theorem witness_NILNotRoot : NILNotRoot witness := by
  intro h
  simp [witness] at h

theorem witness_NILLeaf : NILLeaf witness := rfl

theorem witness_iterate (x : ℕ) : ∀ j, 0 < j → (witness.par)^[j] x = 0 := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ k ih =>
    intro _
    cases k with
    | zero => simp [Function.iterate_succ_apply, witness]
    | succ k' => rw [Function.iterate_succ_apply', ih (by omega)]; simp [witness]

theorem witness_Acyc : Acyc witness := by
  intro x j hj heq
  rw [witness_iterate x j hj] at heq
  exact heq.symm

theorem witness_MarkOK : MarkOK witness := by
  intro q
  simp [witness]

theorem witness_PosOK : PosOK witness := by
  intro q j hj
  rw [kids_witness] at hj
  simp at hj

/-- The support witness at the live root. -/
theorem witness_Support : Support witness 3 1 := by
  refine ⟨{1}, ?_, ?_⟩
  · have hshape : treeOf witness 3 1 = FibHeapForest.Tree.node 1
        ((kids witness 1).map fun c =>
          FibHeapForest.Child.mk (treeOf witness 2 c) (ldeg witness c) (witness.mrk c)) := rfl
    rw [hshape, FibHeapForest.size_node, kids_witness, FibHeapForest.sizeSum]
    simp
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    simp [witness]

/-- **The capstone applied to a real state.**  `witness` satisfies every premise, and the
conclusion evaluates to `0 ≤ 3`: the rank cap has a model, so it is not vacuous. -/
theorem witness_capstone :
    witness.deg 1 ≤ FibHeapAccounting.rankCap witness.n := by
  have hsup : Support witness 3 1 := witness_Support
  have hpv : (1 : ℕ) < witness.n := by simp [witness]
  have hp0 : (1 : ℕ) ≠ 0 := by norm_num
  exact degree_le_rankCap_zero witness witness_ParOK witness_SlotOK witness_ParSlot
    witness_KidsNodup witness_Acyc witness_NILSelf witness_NILLeaf witness_NILNotChild
    witness_MarkOK witness_PosOK hpv hp0 hsup

theorem witness_nonvacuous :
    (witness.deg 1 : ℕ) = 0 ∧ FibHeapAccounting.rankCap witness.n = 3 :=
  ⟨rfl, by decide⟩

end Submission.FibHeapWitness
