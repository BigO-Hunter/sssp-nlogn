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
is injective because a repetition would be a `par`-cycle at a path node, and the only cycle `Acyc`
permits is the NIL self-loop at slot 0 — which no path node can be (`chain_ne_zero`: the chain
reaches the non-NIL node `p` at step `n`, and NIL is absorbing).  It lands in `Fin n` by `ParSlot`
iterated from `q < n`.  No list extraction and no `Nodup` reasoning is needed.

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

/-- NIL is absorbing: once a chain reaches 0 it stays there. -/
theorem iterate_par_zero (st : HState) (hs : NILSelf st) :
    ∀ j : ℕ, (st.par)^[j] 0 = 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hs]

/-- A chain from a non-NIL node avoids NIL for its first `n` steps, when the chain reaches a
non-NIL node at step `n`.  This is what makes the pigeonhole injective. -/
theorem chain_ne_zero (st : HState) (hs : NILSelf st) {q p : ℕ} (hq : q ≠ 0) (hp0 : p ≠ 0)
    (hn : (st.par)^[st.n] q = p) :
    ∀ i, i ≤ st.n → (st.par)^[i] q ≠ 0 := by
  intro i hi hc
  have hsplit : (st.par)^[st.n] q = (st.par)^[st.n - i] ((st.par)^[i] q) := by
    have h := Function.iterate_add_apply (f := st.par) (m := st.n - i) (n := i) (x := q)
    rwa [show st.n - i + i = st.n by omega] at h
  rw [hsplit, hc, iterate_par_zero st hs] at hn
  exact hp0 hn.symm

/-- **Faithfulness from acyclicity.**  A live root's subtree truncates nowhere: the chain of `n+1`
path nodes would have to repeat, and the only cycle `Acyc` permits is the NIL self-loop, which no
path node can be (`chain_ne_zero`). -/
theorem faithful_of_acyc (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hs : NILSelf st) (hac : Acyc st) (hnl : NILLeaf st) {p : ℕ}
    (hp : p < st.n) (hp0 : p ≠ 0) : Faithful st st.n p := by
  by_contra hnf
  obtain ⟨q, hreach, hdeg⟩ := exists_reach_of_not_faithful st st.n p hnf
  have hqne : q ≠ 0 := fun hc => hdeg (by rw [hc]; exact hnl)
  have hq : q < st.n := reach_lt st hslot st.n p q hp (by omega) hreach
  have hret : (st.par)^[st.n] q = p := reach_par st hpar st.n p q hreach
  have hq0 : ∀ i, i ≤ st.n → (st.par)^[i] q ≠ 0 :=
    chain_ne_zero st hs hqne hp0 hret
  have hinj : Function.Injective fun i : Fin (st.n + 1) =>
      (⟨(st.par)^[i.val] q, par_iter_lt st hps hq i.val⟩ : Fin st.n) := by
    intro a b hab
    have hval : (st.par)^[a.val] q = (st.par)^[b.val] q := congrArg Fin.val hab
    rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
    · exact (hq0 a.val (by simpa using a.isLt) (by
        have hsplit : (st.par)^[b.val] q = (st.par)^[b.val - a.val] ((st.par)^[a.val] q) := by
          have h := Function.iterate_add_apply (f := st.par) (m := b.val - a.val)
              (n := a.val) (x := q)
          rwa [show b.val - a.val + a.val = b.val by omega] at h
        have hcyc' : (st.par)^[b.val - a.val] ((st.par)^[a.val] q) = (st.par)^[a.val] q := by
          rw [hsplit.symm, hval]
        exact hac (st.par^[a.val] q) (b.val - a.val) (by omega) hcyc')).elim
    · exact Fin.ext heq
    · exact (hq0 b.val (by simpa using b.isLt) (by
        have hsplit : (st.par)^[a.val] q = (st.par)^[a.val - b.val] ((st.par)^[b.val] q) := by
          have h := Function.iterate_add_apply (f := st.par) (m := a.val - b.val)
              (n := b.val) (x := q)
          rwa [show a.val - b.val + b.val = a.val by omega] at h
        have hcyc' : (st.par)^[a.val - b.val] ((st.par)^[b.val] q) = (st.par)^[b.val] q := by
          rw [hsplit.symm, hval.symm]
        exact hac (st.par^[b.val] q) (a.val - b.val) (by omega) hcyc')).elim
  have hcard := Fintype.card_le_of_injective _ hinj
  simp at hcard

/-- **The rank cap with no analytic hypothesis left.**  Every premise is a machine invariant. -/
theorem degree_le_rankCap_of_machine (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hs' : NILSelf st) (hac : Acyc st) (hnl : NILLeaf st) (hm : MarkOK st)
    (hp : PosOK st) {p : ℕ} (hpv : p < st.n) (hp0 : p ≠ 0) (hsup : Support st (st.n + 1) p) :
    st.deg p ≤ FibHeapAccounting.rankCap st.n :=
  degree_le_rankCap_treeOf st hm hp st.n p
    (faithful_of_acyc st hpar hslot hps hs' hac hnl hpv hp0) hsup


end Submission.FibHeapAcyclic
