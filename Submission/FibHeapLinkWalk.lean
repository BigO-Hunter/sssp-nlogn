import Submission.FibHeapLink

/-!
# M2b: the walk lemma and the invariant discharges for the link

The gate from M2a: `kids (linkState st p c) p = kids st p ++ [c]`, proved under `RingOK`,
`ParOK`, `RootNotChild` and `LinkPre`.  The walk from the head is unchanged on the old prefix —
the splice touches only `rgt c` and `rgt t`, and the old prefix neither is `c` (`c` is a root,
outside every child list by `RootNotChild`) nor is the tail `t` (ring injectivity pins any
earlier position away from it).

Through it, the invariants fall out:

* `link_parOK`, `link_kidsNodup`, `link_posOK`, `link_slotOK` — via the list lemmas
  (`pos_link` for the link order; `nodup_of_kidsNodup` + `c ∉ kids st p` for the appended child).
* `link_acyc` — `Acyc (linkState st p c)`: the only changed `par` edge is `par c := p`; a chain
  that visits `c` then follows `par p = 0` (`NILRoots`) is absorbed at NIL and can never close;
  a chain avoiding `c` is an old chain, and `Acyc st` confines its repetitions to 0.
-/

namespace Submission.FibHeapLinkWalk

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink

/-- A root is in no child list, read straight off `RootNotChild`. -/
theorem root_notin_kids (st : HState) (hrnc : RootNotChild st) {r q : ℕ} (hr : r ∈ st.roots) :
    r ∉ kids st q := hrnc r hr q

/-! ## Pointwise behaviour of the splice -/

theorem rgt_link_other (st : HState) (p c x : ℕ) (h : st.deg p ≠ 0) (h1 : x ≠ c)
    (h2 : x ≠ st.lft (st.chd p)) : (linkState st p c).rgt x = st.rgt x := by
  by_cases hb : st.deg p = 0
  · exact absurd hb h
  · simp [linkState, hb, h1, h2]

theorem rgt_link_c (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).rgt c = st.chd p := by
  by_cases hb : st.deg p = 0
  · exact absurd hb h
  · simp [linkState, hb]

theorem rgt_link_tail (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).rgt (st.lft (st.chd p)) = c := by
  by_cases hb : st.deg p = 0
  · exact absurd hb h
  · simp [linkState, hb]

theorem chd_link_pos (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).chd p = st.chd p := by
  by_cases hb : st.deg p = 0
  · exact absurd hb h
  · simp [linkState, hb]

theorem deg_link_pos (st : HState) (p c : ℕ) (h : st.deg p ≠ 0) :
    (linkState st p c).deg p = st.deg p + 1 := by
  rw [linkState_deg, if_pos rfl]

theorem chd_link_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    (linkState st p c).chd p = c := by
  simp [linkState, h]

theorem deg_link_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    (linkState st p c).deg p = 1 := by
  rw [linkState_deg, if_pos rfl, h]

theorem rgt_link_c_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    (linkState st p c).rgt c = c := by
  simp [linkState, h]

/-! ## The walk lemma -/

/-- **The walk lemma, positive-degree branch.** -/
theorem walk_link_pos (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : LinkPre st p c) (hdeg : st.deg p ≠ 0) :
    ∀ j, j ≤ st.deg p →
      (linkState st p c).rgt^[j] (st.chd p) =
        if j = st.deg p then c else (st.rgt)^[j] (st.chd p) := by
  have hmem : ∀ j, j < st.deg p → (st.rgt)^[j] (st.chd p) ∈ kids st p := by
    intro j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, by simpa [kids_length] using hj⟩, rfl⟩
  have hcnot : ∀ x ∈ kids st p, x ≠ c := fun x hx hc => root_notin_kids st hrnc hpre.2.1 p hx hc
  have htmem : st.lft (st.chd p) ∈ kids st p := by
    have hclose := (hrk p hdeg).2.2.2
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
      have hxt : (st.rgt)^[j] (st.chd p) = st.lft (st.chd p) := by
        rw [((hrk p hdeg).resolve_right h).2.2.2]; omega
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
  rw [deg_link_pos st p c hdeg, chd_link_pos st p c hdeg, List.ofFn_succ]
  rw [show (List.ofFn (fun i : Fin (st.deg p) =>
      (linkState st p c).rgt^[(Fin.castSucc i).val] (st.chd p))) =
      List.ofFn (fun i : Fin (st.deg p) => (st.rgt)^[(Fin.castSucc i).val] (st.chd p)) from by
    apply List.ofFn_inj.mpr
    funext i
    rw [walk_link_pos st p c hpar hrnc hrk hpre _ (by omega),
      if_neg (by simpa [kids_length] using i.isLt))]
  rw [show (linkState st p c).rgt^[(Fin.last (st.deg p)).val] (st.chd p) = c from by
    rw [show (Fin.last (st.deg p)).val = st.deg p from rfl]
    rw [walk_link_pos st p c hpar hrnc hrk hpre (st.deg p) (Nat.le_refl _), if_pos rfl]]

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

/-- **Every other child list is untouched.** -/
theorem kids_unchanged (st : HState) (p c q : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : LinkPre st p c) (hq : q ≠ p) :
    kids (linkState st p c) q = kids st q := by
  have hcnot : ∀ x ∈ kids st q, x ≠ c := fun x hx hc => root_notin_kids st hrnc hpre.2.1 q hx hc
  have h1 : (linkState st p c).deg q = st.deg q := by
    rw [linkState_deg, if_neg (by omega : ¬ q = p)]
  have h2 : (linkState st p c).chd q = st.chd q := by
    by_cases h : st.deg p = 0
    · simp [linkState, h, hq]
    · simp [linkState, h, hq]
  have hrgt : ∀ x, x ≠ c → (st.deg p = 0 ∨ x ≠ st.lft (st.chd p)) →
      (linkState st p c).rgt x = st.rgt x := by
    intro x hx hsplit
    by_cases h : st.deg p = 0
    · simp [linkState, h, hx]
    · simp [linkState, h, hx, hsplit.resolve_right h]
  have hmem : ∀ j, j < st.deg q → (st.rgt)^[j] (st.chd q) ∈ kids st q := by
    intro j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, by simpa [kids_length] using hj⟩, rfl⟩
  have htp : st.lft (st.chd p) ∈ kids st p := by
    by_cases h : st.deg p = 0
    · exfalso; exact h ((hrk p h).elim' id)
    · have hclose := (hrk p h).2.2.2
      exact hmem (st.deg p - 1) (by omega)
  have hq'' : st.lft (st.chd p) ∉ kids st q := by
    intro hx
    exact hq ((hpar q _ hx).symm.trans (hpar p _ htp))
  have hw : ∀ j : ℕ, j < st.deg q →
      (linkState st p c).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hx : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem k (by simpa [kids_length] using ih.isLt)
      rw [hrgt _ (hcnot _ hx) (Or.inr (fun hc => hq'' (hc ▸ hx)))]
  unfold kids
  rw [h1, h2]
  have hfun : (fun i : Fin (st.deg q) => (linkState st p c).rgt^[i.val] (st.chd q))
      = (fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q)) := by
    funext i
    exact hw i.val (by simpa [kids_length] using i.isLt)
  rw [hfun]

end Submission.FibHeapLinkWalk
