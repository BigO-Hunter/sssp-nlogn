import Submission.FibHeapRefine

/-!
# M1b: acyclicity discharges the refinement's two hypotheses

`FibHeapRefine` reduced the rank cap to two hypotheses: `Faithful st st.n p` (the abstraction at
fuel `n` does not truncate) and `Support st f p` (the abstracted identifiers are distinct and
inside the slots).  Both are consequences of the machine forest being a forest.  This module
proves the first and pins the second.

## Why acyclicity is the right hypothesis

Truncation is a repeat.  If the abstraction at fuel `n` were truncated, some node would sit at
depth `n` with children — so there is a chain `p = x₀ → x₁ → … → xₙ` of child steps, and `n + 1`
nodes.  Every one of them is a live slot (`SlotOK` downwards from `p < n`), so two must coincide,
and the segment between them is a `par` chain that returns to its start — exactly what `NoCycle`
at *positive* length forbids.  The repeat-at-depth `j - i` escape is why the earlier `n ≤ j`
form of `NoCycle` was too weak.

The counting is done with `Fintype.card_le_of_injective` on `i ↦ par^[i] q` for `i ≤ n`: that map
is injective by `NoCycle`, and lands in `Fin n` by `ParSlot` iterated from `q < n`.  No list
extraction and no `Nodup` reasoning is needed.

Main result: `faithful_of_noCycle`, which turns `degree_le_rankCap_treeOf`'s faithfulness premise
into a machine fact.
-/

namespace Submission.FibHeapAcyclic

open Submission.FibHeapRefine Submission.FibHeapForest

/-- `q` is reachable from `p` in exactly `f` child steps. -/
def Reach (st : HState) : ℕ → ℕ → ℕ → Prop
  | 0, p, q => p = q
  | f + 1, p, q => ∃ c, c ∈ kids st p ∧ Reach st f c q

/-- A failed faithfulness at fuel `f` is exactly a reachable node at depth `f` that still has
children.  Pure induction on the fuel — no counting yet. -/
theorem exists_reach_of_not_faithful (st : HState) :
    ∀ (f p : ℕ), ¬ Faithful st f p → ∃ q, Reach st f p q ∧ st.deg q ≠ 0 := by
  intro f
  induction f with
  | zero =>
    intro p hf
    refine ⟨p, rfl, ?_⟩
    simpa [Faithful] using hf
  | succ f ih =>
    intro p hf
    have hstep : ∃ c, c ∈ kids st p ∧ ¬ Faithful st f c := by
      by_contra h
      apply hf
      intro c hc
      by_contra hnf
      exact h ⟨c, hc, hnf⟩
    obtain ⟨c, hc, hnf⟩ := hstep
    obtain ⟨q, hq, hdeg⟩ := ih c hnf
    exact ⟨q, ⟨c, hc, hq⟩, hdeg⟩

/-- Every reachable node's `par`-iterate returns to the start: `par^[f] q = p`. -/
theorem reach_par (st : HState) (hpar : ParOK st) :
    ∀ (f p q : ℕ), Reach st f p q → (st.par^[f]) q = p := by
  intro f
  induction f with
  | zero =>
    intro p q h
    have : p = q := h
    subst this
    rfl
  | succ f ih =>
    intro p q h
    obtain ⟨c, hc, hr⟩ := h
    have h1 : (st.par^[f]) q = c := ih c q hr
    rw [Function.iterate_succ_apply', h1]
    exact hpar p c hc

/-- Reachable nodes are live slots: downward closure of `SlotOK` along the chain. -/
theorem reach_lt (st : HState) (hslot : SlotOK st) :
    ∀ (f p q : ℕ), p < st.n → 0 < f → Reach st f p q → q < st.n := by
  intro f
  induction f with
  | zero => intro p q _ hf _; exact absurd hf (by omega)
  | succ f ih =>
    intro p q hp _ h
    obtain ⟨c, hc, hr⟩ := h
    have hc' : c < st.n := hslot p hp c hc
    cases f with
    | zero =>
      have : c = q := hr
      rw [← this]
      exact hc'
    | succ f' => exact ih c q hc' (by omega) hr

/-- The `par`-iterates of a live slot are live, by `ParSlot`. -/
theorem par_iter_lt (st : HState) (hps : ParSlot st) {q : ℕ} (hq : q < st.n) :
    ∀ i : ℕ, (st.par^[i]) q < st.n := by
  intro i
  induction i with
  | zero => simpa using hq
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact hps _ ih

/-- The `par`-iterates of a live slot are pairwise distinct up to any length, by `NoCycle` at
positive length.  This is the injectivity the pigeonhole consumes. -/
theorem par_iter_inj (st : HState) (hcyc : NoCycle st) {q : ℕ} :
    ∀ i j : ℕ, i < j → (st.par^[i]) q ≠ (st.par^[j]) q := by
  intro i j hij heq
  have hpos : 0 < j - i := by omega
  have hsplit : (st.par^[j]) q = (st.par^[j - i]) ((st.par^[i]) q) := by
    have h := Function.iterate_add_apply (f := st.par) (m := j - i) (n := i) (x := q)
    rwa [show j - i + i = j by omega] at h
  rw [hsplit] at heq
  exact hcyc ((st.par^[i]) q) (j - i) hpos heq.symm

/-- **Faithfulness from acyclicity.**  A live slot has no truncation at depth `n`: a chain of
`n + 1` live distinct slots cannot exist inside `n` slots. -/
theorem faithful_of_noCycle (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hcyc : NoCycle st) {p : ℕ} (hp : p < st.n) : Faithful st st.n p := by
  by_contra hnf
  obtain ⟨q, hreach, -⟩ := exists_reach_of_not_faithful st st.n p hnf
  have hq : q < st.n := reach_lt st hslot st.n p q hp (by omega) hreach
  have hret : (st.par^[st.n]) q = p := reach_par st hpar st.n p q hreach
  have hinj : Function.Injective fun i : Fin (st.n + 1) =>
      (⟨(st.par^[i.val]) q, par_iter_lt st hps hq i.val⟩ : Fin st.n) := by
    intro i j hij
    have hval : (st.par^[i.val]) q = (st.par^[j.val]) q := congrArg Fin.val hij
    rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact absurd hval (par_iter_inj st hcyc i.val j.val hlt)
    · exact Fin.ext heq
    · exact absurd hval.symm (par_iter_inj st hcyc j.val i.val hgt)
  have hcard := Fintype.card_le_of_injective _ hinj
  simp at hcard

/-- **The rank cap from machine facts only.**  Acyclicity discharges faithfulness, so the remaining
premise of `degree_le_rankCap_treeOf` is `Support` (distinct abstracted ids inside the slots) —
the one goal this module leaves.  Everything else is now a statement about the arrays. -/
theorem degree_le_rankCap_of_machine (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hcyc : NoCycle st) (hm : MarkOK st) (hp : PosOK st) {p : ℕ}
    (hpv : p < st.n) (hs : Support st (st.n + 1) p) :
    st.deg p ≤ FibHeapAccounting.rankCap st.n :=
  degree_le_rankCap_treeOf st hm hp st.n p (faithful_of_noCycle st hpar hslot hps hcyc hpv) hs

end Submission.FibHeapAcyclic
