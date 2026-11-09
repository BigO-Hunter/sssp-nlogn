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
  rw [deg_link_pos st p c hdeg, chd_link_pos st p c hdeg]
  refine List.ext_get (by simp) (fun n h1 h2 => ?_)
  simp only [List.get_eq_getElem]
  by_cases hlast : n = st.deg p
  · subst hlast
    rw [List.getElem_append_right (by simp)]
    simp only [List.getElem_ofFn]
    rw [hwalk (st.deg p) (le_refl (st.deg p)), if_pos rfl]
    simp
  · have hn : n < st.deg p := by
      have h2' : n < st.deg p + 1 := by simpa using h2
      omega
    rw [List.getElem_append_left (by simpa using hn)]
    simp only [List.getElem_ofFn]
    rw [hwalk n (Nat.le_of_lt hn), if_neg (Nat.ne_of_lt hn)]

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
  have hmem : ∀ z j, j < st.deg z → (st.rgt)^[j] (st.chd z) ∈ kids st z := by
    intro z j hj
    rw [kids]
    exact List.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩
  -- With `deg p ≠ 0`, the old tail `t = lft (chd p)` is a child of `p` (`RingOK`), hence of no
  -- other node (`ParOK`, `q ≠ p`); with `deg p = 0` the splice's second `rgt` write is absent.
  have hq'' : st.deg p ≠ 0 → st.lft (st.chd p) ∉ kids st q := by
    intro hdp hx
    have htp : st.lft (st.chd p) ∈ kids st p := by
      rw [(Or.resolve_left (hrk p) hdp).2.2]
      exact hmem p (st.deg p - 1) (by omega)
    exfalso
    exact hq ((hpar q _ hx).symm.trans (hpar p _ htp))
  have hw : ∀ j : ℕ, j < st.deg q →
      (linkState st p c).rgt^[j] (st.chd q) = (st.rgt)^[j] (st.chd q) := by
    intro j hj
    induction j with
    | zero => simp
    | succ k ih =>
      have hik : k < st.deg q := by omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hik]
      have hx : (st.rgt)^[k] (st.chd q) ∈ kids st q := hmem q k hik
      by_cases hdp : st.deg p = 0
      · exact hrgt _ (hcnot _ hx) (Or.inl hdp)
      · exact hrgt _ (hcnot _ hx) (Or.inr (fun hc => hq'' hdp (hc ▸ hx)))
  unfold kids
  rw [h1, h2]
  refine List.ext_get (by simp) (fun n h1 h2 => ?_)
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact hw n (by simpa using h2)

/-! ## The five invariant discharges

The walk lemma's consumers: `link_parOK`, `link_kidsNodup`, `link_posOK`, `link_slotOK` (via
`RootsLive` for the appended root), and `link_acyc` — a chain visiting `c` then follows
`par p = 0` (`NILRoots`) and is absorbed at NIL (`NILSelf`), so it can never close.  Every
`q ≠ p` child list goes through `kids_unchanged` (with the `q = 0` case closed separately by
`NILLeaf`: slot 0's child list is untouched by the link and is empty anyway). -/

/-- `ParOK` survives the link. -/
theorem link_parOK (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) (hnl : NILLeaf st) :
    ParOK (linkState st p c) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.1)
  have hcnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ c := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids st hrnc hpre.2.1 hq0)
  intro q v hv
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    rw [kids_link st p c hpar hrnc hnr hrk hpre] at hv
    rcases List.mem_append.mp hv with hv | hv
    · rw [linkState_par_ne st p c v (hcnot p hp0 v hv)]
      exact hpar p v hv
    · have hvc : c = v := (List.mem_singleton.mp hv).symm
      subst hvc
      exact linkState_par_c st p c
  · by_cases hq0 : q = 0
    · subst hq0
      rw [kids_eq_nil (by rw [linkState_deg, if_neg (Ne.symm hp0)]; exact hnl)] at hv
      simp at hv
    · rw [kids_unchanged st p c q hpar hrnc hrk hpre hqp hq0] at hv
      rw [linkState_par_ne st p c v (hcnot q hq0 v hv)]
      exact hpar q v hv

/-- `KidsNodup` survives the link: other lists are untouched, `p`'s old prefix is untouched by
`getD`, and the appended `c` is new (`RootNotChild`). -/
theorem link_kidsNodup (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) (hnl : NILLeaf st)
    (hnd : ∀ q, KidsNodup st q) : ∀ q, KidsNodup (linkState st p c) q := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.1)
  have hcnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ c := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids st hrnc hpre.2.1 hq0)
  have hmemD : ∀ q j, j < (kids st q).length → (kids st q).getD j 0 ∈ kids st q := by
    intro q j hj
    have hs : (List.ofFn fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q))[j]?
        = some ((st.rgt)^[j] (st.chd q)) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨by simpa using hj, List.getElem_ofFn (by simpa using hj)⟩
    rw [kids, List.getD_eq_getElem?_getD, hs]
    exact List.mem_ofFn.mpr ⟨⟨j, by simpa using hj⟩, rfl⟩
  intro q j k hjk hk
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    by_cases hdeg : st.deg p = 0
    · rw [deg_link_zero st p c hdeg] at hk
      rw [kids_link_zero st p c hdeg, kids_eq_nil hdeg]
      have hk0 : k = 0 := by omega
      subst hk0
      exact absurd hjk (by omega)
    · rw [deg_link_pos st p c hdeg] at hk
      rw [kids_link_pos st p c hpar hrnc hnr hrk hpre hdeg]
      by_cases hklt : k < st.deg p
      have hkl : (kids st p).length = st.deg p := kids_length st p
      rw [getD_append_lt (by rw [hkl]; omega : j < (kids st p).length),
        getD_append_lt (by rw [hkl]; omega : k < (kids st p).length)]
      exact hnd p j k hjk hklt
      · have hk0 : k = st.deg p := by omega
        subst hk0
        rw [getD_append_lt (by rw [kids_length]; omega : j < (kids st p).length),
          ← kids_length, getD_append_last]
        exact hcnot p hp0 _ (hmemD p j (by rw [kids_length]; omega))
  · by_cases hq0 : q = 0
    · subst hq0
      rw [linkState_deg, if_neg (Ne.symm hp0), hnl] at hk
      exact absurd hk (by omega)
    · rw [linkState_deg, if_neg hqp] at hk
      rw [kids_unchanged st p c q hpar hrnc hrk hpre hqp hq0]
      exact hnd q j k hjk hk

/-- `PosOK` survives the link: old positions keep their `ldeg` (only slot `c`'s mark drops, and
`c` is not on any old list), and the appended `c` sits at position `deg p` with `ldeg c =
deg c = deg p`. -/
theorem link_posOK (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) (hnl : NILLeaf st)
    (hpos : PosOK st) : PosOK (linkState st p c) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.1)
  have hpc : c ≠ p := fun hc => hpre.2.2.1 hc.symm
  have hcnot : ∀ q : ℕ, q ≠ 0 → ∀ x ∈ kids st q, x ≠ c := by
    intro q hq0 x hx hc
    subst hc
    exact absurd hx (root_notin_kids st hrnc hpre.2.1 hq0)
  have hmemD : ∀ q j, j < (kids st q).length → (kids st q).getD j 0 ∈ kids st q := by
    intro q j hj
    have hs : (List.ofFn fun i : Fin (st.deg q) => (st.rgt)^[i.val] (st.chd q))[j]?
        = some ((st.rgt)^[j] (st.chd q)) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨by simpa using hj, List.getElem_ofFn (by simpa using hj)⟩
    rw [kids, List.getD_eq_getElem?_getD, hs]
    exact List.mem_ofFn.mpr ⟨⟨j, by simpa using hj⟩, rfl⟩
  intro q j hj
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    by_cases hdeg : st.deg p = 0
    · rw [kids_link_zero st p c hdeg, kids_eq_nil hdeg] at hj ⊢
      simp only [List.nil_append, List.length_cons, List.length_nil, Nat.lt_one_iff] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      have hget : (([] : List ℕ) ++ [c]).getD 0 0 = c := rfl
      rw [hget]
      unfold ldeg
      rw [linkState_deg, if_neg hpc, linkState_mrk_c]
      omega
    · rw [kids_link_pos st p c hpar hrnc hnr hrk hpre hdeg] at hj ⊢
      have hj1 : j < st.deg p + 1 := by
        simp only [List.length_append, kids_length] at hj
        exact hj
      by_cases hjl : j < st.deg p
      · rw [getD_append_lt (by rw [kids_length]; omega : j < (kids st p).length)]
        have hxne : (kids st p).getD j 0 ≠ c :=
          hcnot p hp0 _ (hmemD p j (by rw [kids_length]; omega))
        have hl : ldeg st ((kids st p).getD j 0)
            ≤ ldeg (linkState st p c) ((kids st p).getD j 0) := by
          unfold ldeg
          rw [linkState_deg, linkState_mrk]
          by_cases hxp : (kids st p).getD j 0 = p
          · rw [hxp, if_pos rfl, if_neg (show ¬(p = c) from hpre.2.2.1)]
            omega
          · rw [if_neg hxp, if_neg hxne]
        calc j ≤ ldeg st ((kids st p).getD j 0) := hpos p j (by rw [kids_length]; omega)
          _ ≤ ldeg (linkState st p c) ((kids st p).getD j 0) := hl
      · have hj0 : j = st.deg p := by omega
        subst hj0
        rw [← kids_length, getD_append_last]
        unfold ldeg
        rw [linkState_deg, if_neg hpc, linkState_mrk_c, kids_length, hpre.2.2.2]
        omega
  · by_cases hq0 : q = 0
    · subst hq0
      rw [kids_eq_nil (by rw [linkState_deg, if_neg (Ne.symm hp0)]; exact hnl)] at hj
      simp at hj
    · rw [kids_unchanged st p c q hpar hrnc hrk hpre hqp hq0] at hj ⊢
      have hxne : (kids st q).getD j 0 ≠ c := hcnot q hq0 _ (hmemD q j hj)
      have hl : ldeg st ((kids st q).getD j 0)
          ≤ ldeg (linkState st p c) ((kids st q).getD j 0) := by
        unfold ldeg
        rw [linkState_deg, linkState_mrk]
        by_cases hxp : (kids st q).getD j 0 = p
        · rw [hxp, if_pos rfl, if_neg (show ¬(p = c) from hpre.2.2.1)]
          omega
        · rw [if_neg hxp, if_neg hxne]
      calc j ≤ ldeg st ((kids st q).getD j 0) := hpos q j hj
        _ ≤ ldeg (linkState st p c) ((kids st q).getD j 0) := hl

/-- `SlotOK` survives the link: other lists are untouched, and the appended `c` is live
(`RootsLive`). -/
theorem link_slotOK (st : HState) (p c : ℕ) (hpar : ParOK st) (hrnc : RootNotChild st)
    (hnr : NILNotRoot st) (hrk : RingOK st) (hpre : LinkPre st p c) (hrl : RootsLive st)
    (hnl : NILLeaf st) (hslot : SlotOK st) : SlotOK (linkState st p c) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.1)
  have hn : (linkState st p c).n = st.n := linkState_n st p c
  intro q hq x hx
  by_cases hqp : q = p
  · have hqp' : p = q := hqp.symm
    subst hqp'
    by_cases hdeg : st.deg p = 0
    · rw [kids_link_zero st p c hdeg] at hx
      rw [hn] at hq ⊢
      rcases List.mem_append.mp hx with hx | hx
      · exact hslot p hq x hx
      · have hxc : c = x := (List.mem_singleton.mp hx).symm
        subst hxc
        exact hrl c hpre.2.1
    · rw [kids_link_pos st p c hpar hrnc hnr hrk hpre hdeg] at hx
      rw [hn] at hq ⊢
      rcases List.mem_append.mp hx with hx | hx
      · exact hslot p hq x hx
      · have hxc : c = x := (List.mem_singleton.mp hx).symm
        subst hxc
        exact hrl c hpre.2.1
  · by_cases hq0 : q = 0
    · subst hq0
      rw [kids_eq_nil (by rw [linkState_deg, if_neg (Ne.symm hp0)]; exact hnl)] at hx
      simp at hx
    · rw [kids_unchanged st p c q hpar hrnc hrk hpre hqp hq0] at hx
      rw [hn] at hq ⊢
      exact hslot q hq x hx

/-- `Acyc` survives the link (NIL discharge).  The splice's only `par` change is `par c := p`.
Every root's `par` is already 0 (`NILRoots`), so `par p = 0`; a chain that hits `c` moves to `p`
and dies at NIL (`NILSelf`), one that misses `c` is an old chain (`Acyc`), and either way a
closure forces the node to be 0. -/
theorem link_acyc (st : HState) (p c : ℕ) (hnr : NILNotRoot st) (hpre : LinkPre st p c)
    (hnrs : NILRoots st) (hns : NILSelf st) (hac : Acyc st) : Acyc (linkState st p c) := by
  have hp0 : p ≠ 0 := fun hc => hnr (hc ▸ hpre.1)
  have hc0 : 0 ≠ c := by
    intro hc
    subst hc
    exact hnr hpre.2.1
  have hpc : c ≠ p := fun hc => hpre.2.2.1 hc.symm
  have f0 : (linkState st p c).par 0 = 0 := by
    rw [linkState_par_ne st p c 0 hc0]; exact hns
  have fp0 : (linkState st p c).par p = 0 := by
    rw [linkState_par_ne st p c p hpre.2.2.1]; exact hnrs p hpre.1
  have fzero : ∀ k : ℕ, (linkState st p c).par^[k] 0 = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, f0]
  intro x j hj heq
  by_cases hhit : ∃ m, m < j ∧ (linkState st p c).par^[m] x = c
  · obtain ⟨m, hmj, hmc⟩ := hhit
    have hstep : (linkState st p c).par^[m + 2] x = 0 := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hmc,
        linkState_par_c st p c, fp0]
    by_cases hjm : j = m + 1
    · subst hjm
      have hfx : (linkState st p c).par^[m + 1] x = p := by
        rw [Function.iterate_succ_apply', hmc, linkState_par_c st p c]
      have hpx : p = x := hfx.symm.trans heq
      have h0 : (linkState st p c).par^[m + 1] x = 0 := by
        rw [Function.iterate_succ_apply, ← hpx, fp0, fzero]
      rw [h0] at heq
      exact heq.symm
    · have hj2 : m + 2 ≤ j := by omega
      rw [show j = j - (m + 2) + (m + 2) from by omega, Function.iterate_add_apply, hstep,
        fzero] at heq
      exact heq.symm
  · -- the chain never visits c: it is an old chain
    have hall : ∀ i, i ≤ j → (linkState st p c).par^[i] x = (st.par)^[i] x := by
      intro i hi
      induction i with
      | zero => rfl
      | succ k ih =>
        have hlt : k < j := by omega
        have hikj : k ≤ j := by omega
        have hkne : (st.par)^[k] x ≠ c := by
          intro hc
          rw [← ih hikj] at hc
          exact hhit ⟨k, hlt, hc⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hikj,
          linkState_par_ne st p c _ hkne]
    rw [hall j (le_refl j)] at heq
    exact hac x j hj heq

/-! ## The link-output witness

`FibHeapWitness.lean` proved the capstone's premise set satisfiable by a bare state; the link
step must preserve that.  `linkPre` is a state with two equal-degree roots, `linked` is the
output of linking them, and the invariants are proved of the output directly: the link
transition keeps the machine inside the invariant set, so the capstone applies after a link. -/

/-- The link-output witness's pre-state: NIL at slot 0, two equal-degree roots at slots 1, 2. -/
def linkPre : HState where
  par := fun _ => 0
  chd := fun _ => 0
  rgt := fun _ => 0
  lft := fun _ => 0
  deg := fun _ => 0
  mrk := fun _ => 0
  roots := [1, 2]
  n := 3

/-- The link output: slot 1 absorbs slot 2 (both of degree 0). -/
def linked : HState := linkState linkPre 1 2

@[simp] theorem linked_par (x : ℕ) : linked.par x = if x = 2 then 1 else 0 := rfl

@[simp] theorem linked_mrk (x : ℕ) : linked.mrk x = 0 := by
  by_cases h : x = 2 <;> simp [linked, linkPre, linkState, h]

@[simp] theorem linked_chd (x : ℕ) : linked.chd x = if x = 1 then 2 else 0 := rfl

@[simp] theorem linked_rgt (x : ℕ) : linked.rgt x = if x = 2 then 2 else 0 := rfl

@[simp] theorem linked_lft (x : ℕ) : linked.lft x = if x = 2 then 2 else 0 := rfl

@[simp] theorem linked_deg (x : ℕ) : linked.deg x = if x = 1 then 1 else 0 := rfl

@[simp] theorem linked_roots : linked.roots = [1] := rfl

@[simp] theorem linked_n : linked.n = 3 := rfl

theorem linked_iterate_zero (k : ℕ) : (linked.par)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

@[simp] theorem kids_linked (q : ℕ) : kids linked q = if q = 1 then [2] else [] := by
  unfold kids
  by_cases hq : q = 1
  · subst hq
    simp [List.ofFn_succ, List.ofFn_zero, Function.iterate_zero_apply]
  · simp [List.ofFn_zero, hq]

/-- The output's `par` chain reaches NIL in at most two steps. -/
theorem linked_iterate (x : ℕ) : ∀ j, 2 ≤ j → (linked.par)^[j] x = 0 := by
  intro j hj
  have h2 : (linked.par)^[2] x = 0 := by
    show linked.par (linked.par x) = 0
    by_cases hx2 : x = 2
    · subst hx2; simp
    · simp [hx2]
  rw [show j = (j - 2) + 2 from by omega, Function.iterate_add_apply, h2,
    linked_iterate_zero]

theorem linked_ParOK : ParOK linked := by
  intro q v hv
  by_cases hq : q = 1
  · subst hq
    simp at hv
    subst hv
    simp
  · rw [kids_linked, if_neg hq] at hv
    simp at hv

theorem linked_SlotOK : SlotOK linked := by
  intro q hq v hv
  by_cases hq1 : q = 1
  · subst hq1
    simp at hv
    subst hv
    simp
  · rw [kids_linked, if_neg hq1] at hv
    simp at hv

theorem linked_ParSlot : ParSlot linked := by
  intro q _
  by_cases hq : q = 2
  · subst hq; simp
  · simp [hq]

theorem linked_KidsNodup : ∀ q, KidsNodup linked q := by
  intro q j k hjk hk
  by_cases hq : q = 1
  · subst hq
    rw [linked_deg, if_pos rfl] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [kids_linked, if_pos rfl]
    by_cases hj0 : j = 0
    · subst hj0; exact absurd hjk (by omega)
    · simp [hj0]
  · simp [kids_linked, linked_deg, hq] at hk

theorem linked_NILRoots : NILRoots linked := by
  intro r hr
  rw [linked_roots] at hr
  simp at hr
  subst hr
  simp

theorem linked_NILSelf : NILSelf linked := rfl

theorem linked_NILNotChild : NILNotChild linked := by
  intro q hv
  by_cases hq : q = 1
  · subst hq
    simp at hv
  · rw [kids_linked, if_neg hq] at hv
    simp at hv

theorem linked_RootNotChild : RootNotChild linked := by
  intro r hr q _ hv
  by_cases hq : q = 1
  · subst hq
    rw [linked_roots] at hr
    simp at hv
    subst hv
    simp at hr
  · rw [kids_linked, if_neg hq] at hv
    simp at hr
    simp at hv

theorem linked_RootsLive : RootsLive linked := by
  intro r hr
  simp at hr
  subst hr
  simp

theorem linked_NILNotRoot : NILNotRoot linked := by
  intro h
  simp at h

theorem linked_NILLeaf : NILLeaf linked := rfl

theorem linked_Acyc : Acyc linked := by
  intro x j hj heq
  cases j with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      by_cases hx2 : x = 2
      · subst hx2
        simp at heq
      · simp [hx2] at heq
        exact heq.symm
    | succ k' =>
      rw [show k' + 1 + 1 = k' + 2 from by omega, Function.iterate_add_apply,
        linked_iterate x 2 (by omega), linked_iterate_zero] at heq
      exact heq.symm

theorem linked_MarkOK : MarkOK linked := by
  intro q
  simp

theorem linked_PosOK : PosOK linked := by
  intro q j hj
  by_cases hq : q = 1
  · subst hq
    rw [kids_linked, if_pos rfl] at hj ⊢
    simp only [List.length_cons, List.length_nil, Nat.lt_one_iff] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [ldeg]
  · rw [kids_linked] at hj ⊢
    simp [ldeg, linked_deg, linked_mrk, List.getD_nil, hq] at hj

end Submission.FibHeapLinkWalk
