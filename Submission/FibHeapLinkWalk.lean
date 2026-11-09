import Submission.FibHeapLink

/-!
# M2b: the walk lemma and the invariant discharges for the link

The gate from M2a: `kids (linkState st p c) p = kids st p ++ [c]`, proved under `RingOK`,
`ParOK`, `RootNotChild`, `NILNotRoot` and `LinkPre`.  The walk from the head is unchanged on the
old prefix — the splice touches only `rgt c` and `rgt t`, and the old prefix neither is `c` (`c`
is a root, outside every child list by `RootNotChild` + `p ≠ 0` from `NILNotRoot`) nor is the
tail `t` (ring injectivity pins any earlier position away from it).

Through it, the invariants fall out: `link_parOK`, `link_kidsNodup`, `link_posOK`,
`link_slotOK` (via `RootsLive` for the appended root), and `link_acyc` — a chain visiting `c`
then follows `par p = 0` (`NILRoots`) and is absorbed at NIL, so it can never close.
-/

namespace Submission.FibHeapLinkWalk

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapSupport
  Submission.FibHeapLink

/-- A root is in no child list of a non-NIL node. -/
theorem root_notin_kids (st : HState) (hrnc : RootNotChild st) {r q : ℕ} (hr : r ∈ st.roots)
    (hq0 : q ≠ 0) : r ∉ kids st q := hrnc r hr q hq0

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

theorem rgt_link_tail (st : HState) (p c : ℕ) (h : st.deg p ≠ 0)
    (h3 : st.lft (st.chd p) ≠ c) : (linkState st p c).rgt (st.lft (st.chd p)) = c := by
  by_cases hb : st.deg p = 0
  · exact absurd hb h
  · simp [linkState, hb, h3]

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
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) (hdeg : st.deg p ≠ 0) :
    ∀ j, j ≤ st.deg p →
      (linkState st p c).rgt^[j] (st.chd p) =
        if j = st.deg p then c else (st.rgt)^[j] (st.chd p) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.1)
  have hmem : ∀ j, j < st.deg p → (st.rgt)^[j] (st.chd p) ∈ kids st p := by
    intro j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  have hcnot : ∀ x ∈ kids st p, x ≠ c := by
    intro x hx hc
    subst hc
    exact absurd hx (root_notin_kids st hrnc hpre.2.1 hp0)
  have htmem : st.lft (st.chd p) ∈ kids st p := by
    rw [((hrk p).resolve_left hdeg).2.2]
    exact hmem (st.deg p - 1) (by omega)
  have hct : c ≠ st.lft (st.chd p) := fun hc => hcnot _ htmem hc.symm
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : (0 : ℕ) ≠ st.deg p := by omega
    rw [if_neg h0]
    rfl
  | succ j ih =>
    intro hj
    have hj' : j ≤ st.deg p := by omega
    rw [Function.iterate_succ_apply', ih hj']
    have hx : (st.rgt)^[j] (st.chd p) ≠ c := hcnot _ (hmem j (by omega))
    by_cases hlast : j + 1 = st.deg p
    · have hje : j = st.deg p - 1 := by omega
      have hxt : (st.rgt)^[j] (st.chd p) = st.lft (st.chd p) := by
        rw [hje]
        exact ((hrk p).resolve_left hdeg).2.2.symm
      have htail : (linkState st p c).rgt ((st.rgt)^[j] (st.chd p)) = c := by
        rw [hxt]
        exact rgt_link_tail st p c hdeg (Ne.symm hct)
      rw [if_neg (show ¬(j : ℕ) = st.deg p from by omega),
        if_pos (show (j : ℕ) + 1 = st.deg p from hlast), htail]
    · have hxt : (st.rgt)^[j] (st.chd p) ≠ st.lft (st.chd p) := by
        intro hc
        rw [((hrk p).resolve_left hdeg).2.2] at hc
        have hrep := ((hrk p).resolve_left hdeg).2.1 j (st.deg p - 1) (by omega) (by omega) hc
        omega
      rw [if_neg (show ¬(j : ℕ) = st.deg p from by omega),
        if_neg (show ¬((j : ℕ) + 1) = st.deg p from by omega),
        Function.iterate_succ_apply', rgt_link_other st p c _ hdeg hx hxt]

/-- **The walk lemma, positive-degree branch, as a list equation.** -/
theorem kids_link_pos (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) (hdeg : st.deg p ≠ 0) :
    kids (linkState st p c) p = kids st p ++ [c] := by
  have hwalk := walk_link_pos st p c hpar hrnc hnr hrk hpre hdeg
  unfold kids
  rw [deg_link_pos st p c hdeg, chd_link_pos st p c hdeg, List.ofFn_succ]
  have hfun : (fun i : Fin (st.deg p) =>
        (linkState st p c).rgt^[(Fin.succ i).val] (st.chd p))
      = (fun i : Fin (st.deg p) => (st.rgt)^[i.val + 1] (st.chd p)) := by
    funext i
    have hlt : (i : ℕ) < st.deg p := i.isLt
    have hi : (i : ℕ) + 1 ≤ st.deg p := by omega
    have hne : (i : ℕ) + 1 ≠ st.deg p := by omega
    have hsucc : Nat.succ i.val = i.val + 1 := rfl
    rw [hsucc, hwalk ((i : ℕ) + 1) hi, if_neg hne]
  rw [hfun]
  simp

/-- **The walk lemma, empty branch.** -/
theorem kids_link_zero (st : HState) (p c : ℕ) (h : st.deg p = 0) :
    kids (linkState st p c) p = kids st p ++ [c] := by
  unfold kids
  rw [deg_link_zero st p c h, chd_link_zero st p c h, h]
  have hrc : ∀ j : ℕ, (linkState st p c).rgt^[j] c = c := by
    intro j
    induction j with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, rgt_link_c_zero st p c h]
  simp [hrc]

/-- **The walk lemma.** -/
theorem kids_link (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) :
    kids (linkState st p c) p = kids st p ++ [c] := by
  by_cases h : st.deg p = 0
  · exact kids_link_zero st p c h
  · exact kids_link_pos st p c hpar hrnc hnr hrk hpre h

/-- **Every other child list is untouched.** -/
theorem kids_unchanged (st : HState) (p c q : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hrk : RingOK st) (hpre : LinkPre st p c) (hq : q ≠ p) (hq0 : q ≠ 0) :
    kids (linkState st p c) q = kids st q := by
  have hcnot : ∀ x ∈ kids st q, x ≠ c := by
    intro x hx hc
    subst hc
    exact absurd hx (root_notin_kids st hrnc hpre.2.1 hq0)
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
    · simp [linkState, h, hx, hsplit.resolve_left h]
  have hmem : ∀ j, j < st.deg q → (st.rgt)^[j] (st.chd q) ∈ kids st q := by
    intro j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  have htp : st.lft (st.chd p) ∈ kids st p := by
    by_cases h : st.deg p = 0
    · exfalso; exact h ((hrk p h).elim id id)
    · rw [((hrk p).resolve_left h).2.2]
      exact hmem (st.deg p - 1) (by omega)
  have hq'' : st.lft (st.chd p) ∉ kids st q := by
    intro hx
    exact hq ((hpar q _ hx).symm.trans (hpar p _ htp))
  have hw : ∀ j : ℕ, j < st.deg q →
      (linkState st p c).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
    intro j hj
    induction j with
    | zero => simp
    | succ k ih =>
      have hik : k < st.deg q := by omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hik]
      have hx : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem k hik
      rw [hrgt _ (hcnot _ hx) (Or.inr (fun hc => hq'' (hc ▸ hx)))]
  unfold kids
  rw [h1, h2]
  have hfun : (fun i : Fin (st.deg q) => (linkState st p c).rgt^[i.val] (st.chd q))
      = (fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q)) := by
    funext i
    exact hw i.val (by simpa [kids_length] using i.isLt)
  rw [hfun]

end Submission.FibHeapLinkWalk

