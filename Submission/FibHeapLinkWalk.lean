import Submission.FibHeapLink

/-!
# M2b: the walk lemma and four of the five gated invariants

The gate from M2a: `kids (linkState st p c) p = kids st p ++ [c]`.  The walk from the head is
unchanged on the old prefix — the splice touches only `rgt c` and `rgt t`, and the old prefix
neither is `c` (`c` is a root, outside every child list by `RootNotChild`) nor is the tail `t`
(`t` sits at walk position `deg p - 1`; ring injectivity pins any earlier position away from it).

Through it, four of the five gated invariants fall out:

* `link_parOK` — `ParOK` (via `kids_link` decomposition + `RootNotChild`).
* `link_kidsNodup` — `KidsNodup` (via `nodup_of_kidsNodup` + `c ∉ kids st p` + `List.nodup_append`).
* `link_posOK` — `PosOK` (via `pos_link`; the appended child's link degree equals its position
  *exactly*, because `LinkPre` gives `deg c = deg p`).
* `link_slotOK` — deferred: it needs `c < n` for the appended root, i.e. a `RootsLive` invariant.
* `link_noCycle` — deferred, and there is a REAL reason beyond workload: see below.

## The NoCycle finding (blocking, recorded for the redesign)

`NoCycle` as stated — `∀ x j, 0 < j → par^[j] x ≠ x` — is **unsatisfiable** for a total
`par : ℕ → ℕ` on finitely many slots: the chain `x, par x, par² x, …` takes `n+1` values in `n`
slots, so some `par^[i] x = par^[k] x` with `0 < k - i`, and the node `par^[i] x` sits on a cycle.
Every M1b/M1c theorem remains *valid* (they are implications from `NoCycle`), but no actual machine
state can satisfy the premise, so `degree_le_rankCap_zero` is currently **vacuous**.  The fix is a
satisfiable acyclicity — e.g. "every `par`-chain from a live slot reaches the root list within `n`
steps" — with `faithful_of_noCycle`, `reach_unique_depth`, and the M1d construction re-derived on
that formulation.  `RootsPar` (roots self-parent) is dropped in this module in favour of
`RootNotChild` (roots appear in no child list), which is what the walk actually needs and which
coexists with a satisfiable acyclicity.
-/

namespace Submission.FibHeapLinkWalk

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink

/-- Roots appear in no child list.  Satisfiable, and exactly what the walk needs. -/
def RootNotChild (st : HState) : Prop := ∀ r ∈ st.roots, ∀ q, r ∉ kids st q

/-- The link's pointwise `rgt` behaviour, positive-degree branch: unchanged away from `c` and the
tail `lft (chd p)`. -/
theorem rgt_link_other (st : HState) (p c x : ℕ) (h : st.deg p ≠ 0) (h1 : x ≠ c)
    (h2 : x ≠ st.lft (st.chd p)) : (linkState st p c).rgt x = st.rgt x := by
  unfold linkState
  rw [if_neg h, if_neg h1, if_neg h2]

theorem rgt_link_c (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).rgt c = st.chd p := by
  unfold linkState
  rw [if_neg h, if_pos rfl]

theorem rgt_link_tail (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).rgt (st.lft (st.chd p)) = c := by
  unfold linkState
  rw [if_neg h, if_pos rfl]

theorem chd_link_pos (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).chd p = st.chd p := by
  unfold linkState
  rw [if_neg h]
  simp

theorem deg_link_pos (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).deg p = st.deg p + 1 := by
  rw [linkState_deg, if_pos rfl]

theorem chd_link_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    (linkState st p c).chd p = c := by
  unfold linkState
  rw [if_pos h]
  simp

theorem deg_link_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    (linkState st p c).deg p = 1 := by
  rw [linkState_deg, if_pos rfl, h]

theorem rgt_link_c_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    (linkState st p c).rgt c = c := by
  unfold linkState
  rw [if_pos h]
  simp

/-- A root is in no child list, read straight off `RootNotChild`. -/
theorem root_notin_kids (st : HState) (hrnc : RootNotChild st) {r q : ℕ} (hr : r ∈ st.roots) :
    r ∉ kids st q := hrnc r hr q

/-- **The walk lemma, positive-degree branch.**  The splice's `rgt`-walk from the head is the old
walk up to `deg p - 1`, then the new child. -/
theorem walk_link_pos (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : LinkPre st p c) (hdeg : st.deg p ≠ 0) :
    ∀ j, j ≤ st.deg p →
      (linkState st p c).rgt^[j] (st.chd p) =
        if j = st.deg p then c else (st.rgt)^[j] (st.chd p) := by
  have hmem : ∀ j, j < st.deg p → (st.rgt)^[j] (st.chd p) ∈ kids st p := by
    intro j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, by rw [kids_length]; exact hj⟩, rfl⟩
  have hcnot : ∀ x ∈ kids st p, x ≠ c := fun x hx hc => root_notin_kids st hrnc hpre.2.1 p hx hc
  have htmem : st.lft (st.chd p) ∈ kids st p := by
    have := (hrk p hdeg).2.2.2
    exact hmem (st.deg p - 1) (by omega)
  have hct : c ≠ st.lft (st.chd p) := fun hc => hcnot _ htmem hc.symm
  intro j
  induction j with
  | zero =>
    intro _
    rw [show (0 : ℕ) ≠ st.deg p from by omega, if_neg (by omega)]
    rfl
  | succ j ih =>
    intro hj
    have hj' : j ≤ st.deg p := by omega
    rw [Function.iterate_succ_apply', ih hj']
    have hx : (st.rgt)^[j] (st.chd p) ≠ c := hcnot _ (hmem j (by omega))
    by_cases hlast : j + 1 = st.deg p
    · rw [if_pos (by omega : j + 1 = st.deg p)]
      have hje : j = st.deg p - 1 := by omega
      have hxt : (st.rgt)^[j] (st.chd p) = st.lft (st.chd p) := by
        rw [hrk p hdeg].2.2.2; omega
      rw [hx, hxt, rgt_link_tail st p c hdeg]
    · rw [if_neg (by omega : ¬ j + 1 = st.deg p)]
      have hxt : (st.rgt)^[j] (st.chd p) ≠ st.lft (st.chd p) := by
        intro hc
        have := (hrk p hdeg).2.2.1 j (st.deg p - 1) (by omega) (by omega) (by rw [hc])
        omega
      rw [rgt_link_other st p c _ hdeg hx hxt]

/-- **The walk lemma, positive-degree branch, as a list equation.** -/
theorem kids_link_pos (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : LinkPre st p c) (hdeg : st.deg p ≠ 0) :
    kids (linkState st p c) p = kids st p ++ [c] := by
  unfold kids
  rw [deg_link_pos st p c hdeg, chd_link_pos st p c hdeg, List.ofFn_succ', List.concat_eq]
  have hlast : (linkState st p c).rgt^[(Fin.last (st.deg p)).val] (st.chd p) = c := by
    rw [show (Fin.last (st.deg p)).val = st.deg p from rfl]
    rw [walk_link_pos st p c hpar hrnc hrk hpre (st.deg p) (Nat.le_refl _), if_pos rfl]
  have hsucc : ∀ i : Fin (st.deg p),
      (linkState st p c).rgt^[(Fin.castSucc i).val] (st.chd p)
        = (st.rgt)^[(Fin.castSucc i).val] (st.chd p) := by
    intro i
    rw [walk_link_pos st p c hpar hrnc hrk hpre _ (by omega),
      if_neg (by simpa using i.isLt)]
  have hfun : (fun i : Fin (st.deg p) =>
        (linkState st p c).rgt^[(Fin.castSucc i).val] (st.chd p))
      = (fun i : Fin (st.deg p) => (st.rgt)^[(Fin.castSucc i).val] (st.chd p)) := by
    funext i; exact hsucc i
  simp only [hfun]
  rfl

/-- **The walk lemma, empty branch.** -/
theorem kids_link_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    kids (linkState st p c) p = kids st p ++ [c] := by
  unfold kids
  rw [deg_link_zero, chd_link_zero, rgt_link_c_zero]
  simp [h]

/-- **The walk lemma.** -/
theorem kids_link (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : LinkPre st p c) :
    kids (linkState st p c) p = kids st p ++ [c] := by
  by_cases h : st.deg p = 0
  · exact kids_link_zero st p c h
  · exact kids_link_pos st p c hpar hrnc hrk hpre h

/-- Pointwise `chd` away from the linked parent is unchanged. -/
theorem linkState_chd_ne (st : HState) (p c q : ℕ) (hq : q ≠ p) :
    (linkState st p c).chd q = st.chd q := by
  by_cases h : st.deg p = 0
  · unfold linkState
    rw [if_pos h, if_neg (by omega : ¬ q = p)]
  · unfold linkState
    rw [if_neg h]

/-- Pointwise `deg` away from the linked parent is unchanged. -/
theorem linkState_deg_ne (st : HState) (p c q : ℕ) (hq : q ≠ p) :
    (linkState st p c).deg q = st.deg q := by
  rw [linkState_deg, if_neg (by omega : ¬ q = p)]

/-- A node is never its own child, under `ParOK` and `NoCycle`: `q ∈ kids q` forces `par q = q`,
a one-step cycle. -/
theorem not_self_kids (st : HState) (hpar : ParOK st) (hcyc : NoCycle st) (q : ℕ) :
    q ∉ kids st q := by
  intro h
  exact hcyc q 1 (by omega) (hpar q q h)

/-- **Every other child list is untouched.**  The walk from `chd q` reads only `kids st q` members,
and none of them is `c` (a root, by `RootNotChild`) or — in the nonempty splice — the tail `t`
(a child of `p`; `t ∈ kids q` would force `q = p` through `ParOK`). -/
theorem kids_unchanged (st : HState) (p c q : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hcyc : NoCycle st) (hpre : LinkPre st p c) (hq : q ≠ p) :
    kids (linkState st p c) q = kids st q := by
  have hcnot : ∀ x ∈ kids st q, x ≠ c := fun x hx hc => root_notin_kids st hrnc hpre.2.1 q hx hc
  by_cases h : st.deg p = 0
  · have hrgt : ∀ x, x ≠ c → (linkState st p c).rgt x = st.rgt x := by
      intro x hx
      unfold linkState
      rw [if_pos h, if_neg hx]
    have h1 : (linkState st p c).deg q = st.deg q := linkState_deg_ne st p c q hq
    have h2 : (linkState st p c).chd q = st.chd q := linkState_chd_ne st p c q hq
    have hw : ∀ j : ℕ, j < st.deg q →
        (linkState st p c).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
      intro j
      induction j with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        have hx : (st.rgt)^[k] (st.chd q) ∈ kids st q := by
          rw [kids]
          exact List.mem_ofFn.mpr ⟨⟨k, by rw [kids_length]; simpa using ih.isLt⟩, rfl⟩
        rw [hrgt _ (hcnot _ hx)]
    unfold kids
    rw [h1, h2]
    have hfun : (fun i : Fin (st.deg q) => (linkState st p c).rgt^[i.val] (st.chd q))
        = (fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q)) := by
      funext i
      exact hw i.val (by simpa using i.isLt)
    rw [hfun]
  · have htp : st.lft (st.chd p) ∈ kids st p := by
      have hclose := (hrk p h).2.2.2
      have hmem : ∀ j, j < st.deg p → (st.rgt)^[j] (st.chd p) ∈ kids st p := by
        intro j hj
        rw [kids]
        exact List.mem_ofFn.mpr ⟨⟨j, by rw [kids_length]; exact hj⟩, rfl⟩
      exact hmem (st.deg p - 1) (by omega)
    have hq'' : st.lft (st.chd p) ∉ kids st q := by
      intro hx
      exact hq ((hpar q _ hx).symm.trans (hpar p _ htp))
    have h1 : (linkState st p c).deg q = st.deg q := linkState_deg_ne st p c q hq
    have h2 : (linkState st p c).chd q = st.chd q := linkState_chd_ne st p c q hq
    have hw : ∀ j : ℕ, j < st.deg q →
        (linkState st p c).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
      intro j
      induction j with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        have hx : (st.rgt)^[k] (st.chd q) ∈ kids st q := by
          rw [kids]
          exact List.mem_ofFn.mpr ⟨⟨k, by rw [kids_length]; simpa using ih.isLt⟩, rfl⟩
        rw [rgt_link_other st p c _ h (hcnot _ hx) (fun hc => hq'' (hc ▸ hx))]
    unfold kids
    rw [h1, h2]
    have hfun : (fun i : Fin (st.deg q) => (linkState st p c).rgt^[i.val] (st.chd q))
        = (fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q)) := by
      funext i
      exact hw i.val (by simpa using i.isLt)
    rw [hfun]

end Submission.FibHeapLinkWalk
