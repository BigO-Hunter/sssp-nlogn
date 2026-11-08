import Submission.FibHeapSupport
import Mathlib.Data.List.GetD

/-!
# M1d: the support construction — `Support` proved from machine facts

`Support st f p` (as settled in `FibHeapRefine`, over `size` rather than the `ids` traversal) asks
for a finite set of live slots whose cardinality is the abstracted subtree's size.  This module
builds it by induction on the fuel:

  s(p, 0) = {p},   s(p, f+1) = {p} ∪ ⋃_{c ∈ kids p} s(c, f)

The cardinalities add because the child sets are pairwise disjoint, and that is where the machine
invariants earn their keep:

* `sib_disjoint` — two different children of one parent cannot share a node.  If `x` sits under
  both `a` and `b`, then `par^[i] x = a` and `par^[j] x = b`; the longer chain expresses `b` as a
  `par`-iterate of `a`, and one more step, followed by `par a = p`, closes a `par` cycle at `p` of
  positive length — excluded by `NoCycle`.
* `root_notin_child` — `p` itself is in no child's set: `par^[i] p = c` with `par c = p` closes
  the same cycle.
* `nodup_of_kidsNodup` — `KidsNodup` read as list `Nodup`, which the union's cardinality needs.

Notation note: `Support` was `ids`-based until M1c and is `size`-based from M1c2 on.  The content
is identical (`size` is `(ids t).length`) and no downstream statement changed; a branch comparison
should read the `Support` definition diff rather than assume either form.
-/

namespace Submission.FibHeapSupport

open Submission.FibHeapRefine Submission.FibHeapAcyclic Submission.FibHeapForest

/-- A set disjoint from every member of a list is disjoint from the list's union. -/
theorem disjoint_foldr {ι : Type} (l : List ι) (S : ι → Finset ℕ) {A : Finset ℕ}
    (h : ∀ b ∈ l, Disjoint A (S b)) : Disjoint A (l.foldr (fun a acc => S a ∪ acc) ∅) := by
  induction l with
  | nil => simp
  | cons b u ihu =>
    rw [List.foldr_cons, Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (Finset.disjoint_left.mp (h b (by simp))) hx hy
    · exact (Finset.disjoint_left.mp (ihu (fun c hc => h c (by simp [hc])))) hx hy

/-- A `Nodup` list-indexed union of pairwise disjoint finite sets adds its cardinalities. -/
theorem card_union_list {ι : Type} [DecidableEq ι] (l : List ι) (S : ι → Finset ℕ)
    (hnd : l.Nodup) (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → Disjoint (S a) (S b)) :
    (l.foldr (fun a acc => S a ∪ acc) ∅).card = (l.map fun a => (S a).card).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hnd' : t.Nodup := hnd.of_cons
    have hanot : a ∉ t := (List.nodup_cons.mp hnd).1
    have hdisjt : ∀ b ∈ t, ∀ c ∈ t, b ≠ c → Disjoint (S b) (S c) :=
      fun b hb c hc hbc => hdisj b (by simp [hb]) c (by simp [hc]) hbc
    have hda : Disjoint (S a) (t.foldr (fun a acc => S a ∪ acc) ∅) :=
      disjoint_foldr t S (fun b hb => hdisj a (by simp) b (by simp [hb]) (fun hab => hanot (hab ▸ hb)))
    have hstep := Finset.card_union_of_disjoint hda
    rw [List.foldr_cons, List.map_cons, List.sum_cons, hstep, ih hnd' hdisjt]

/-- Membership in a list-indexed union: the element is in some member set. -/
theorem mem_foldr_union {ι : Type} (l : List ι) (S : ι → Finset ℕ) {x : ℕ}
    (h : x ∈ l.foldr (fun a acc => S a ∪ acc) ∅) : ∃ a ∈ l, x ∈ S a := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rw [List.foldr_cons] at h
    rcases Finset.mem_union.mp h with h1 | h2
    · exact ⟨a, by simp, h1⟩
    · obtain ⟨b, hb, hx⟩ := ih h2
      exact ⟨b, by simp [hb], hx⟩

/-- An element in no member set is in no union. -/
theorem not_mem_foldr_union {ι : Type} (l : List ι) (S : ι → Finset ℕ) {x : ℕ}
    (h : ∀ a ∈ l, x ∉ S a) : x ∉ l.foldr (fun a acc => S a ∪ acc) ∅ := by
  intro hx
  obtain ⟨a, ha, hxa⟩ := mem_foldr_union l S hx
  exact h a ha hxa

/-- `KidsNodup` read as the list-level `Nodup` the union's cardinality needs. -/
theorem nodup_of_kidsNodup (st : HState) (p : ℕ) (h : KidsNodup st p) :
    (kids st p).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  by_contra hne
  have hlt : i.val < j.val ∨ j.val < i.val := by
    rcases Nat.lt_trichotomy i.val j.val with h | h | h
    · exact Or.inl h
    · exact absurd (Fin.ext h) hne
    · exact Or.inr h
  rcases hlt with hlt | hlt
  · have hne' : (kids st p).getD i.val 0 ≠ (kids st p).getD j.val 0 :=
      h i.val j.val hlt (by simpa [kids_length] using j.isLt)
    apply hne'
    rw [List.getD_eq_getElem (l := kids st p) (d := 0) (n := (i : ℕ)) i.isLt,
      List.getD_eq_getElem (l := kids st p) (d := 0) (n := (j : ℕ)) j.isLt]
    simpa using hij
  · have hne' : (kids st p).getD j.val 0 ≠ (kids st p).getD i.val 0 :=
      h j.val i.val hlt (by simpa [kids_length] using i.isLt)
    apply hne'
    rw [List.getD_eq_getElem (l := kids st p) (d := 0) (n := (j : ℕ)) j.isLt,
      List.getD_eq_getElem (l := kids st p) (d := 0) (n := (i : ℕ)) i.isLt]
    simpa using hij.symm

/-- **Two different children of one parent share no node.** -/
theorem sib_disjoint (st : HState) (hpar : ParOK st) (hac : Acyc st) {p a b : ℕ} (hp0 : p ≠ 0)
    (ha : a ∈ kids st p) (hb : b ∈ kids st p) (hne : a ≠ b) {x : ℕ} {i j : ℕ}
    (hi : Reach st i a x) (hj : Reach st j b x) : False := by
  have hpa : st.par a = p := hpar p a ha
  have hpb : st.par b = p := hpar p b hb
  have hia : (st.par^[i]) x = a := reach_par st hpar i a x hi
  have hjb : (st.par^[j]) x = b := reach_par st hpar j b x hj
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have hsplit : (st.par^[j]) x = (st.par^[j - i]) a := by
      have h := Function.iterate_add_apply (f := st.par) (m := j - i) (n := i) (x := x)
      rw [show j - i + i = j by omega] at h
      rw [h, hia]
    have hba : b = (st.par^[j - i]) a := hjb.symm.trans hsplit
    have hcyc' : (st.par^[j - i]) p = p := by
      have h1 : (st.par^[j - i + 1]) a = (st.par^[j - i]) p := by
        rw [show j - i + 1 = (j - i).succ by omega, Function.iterate_succ_apply, hpa]
      rw [← h1, Function.iterate_succ_apply', ← hba, hpb]
    exact hp0 (hac p (j - i) (by omega) hcyc')
  · exact hne (by rw [← hia, ← hjb, heq])
  · have hsplit : (st.par^[i]) x = (st.par^[i - j]) b := by
      have h := Function.iterate_add_apply (f := st.par) (m := i - j) (n := j) (x := x)
      rw [show i - j + j = i by omega] at h
      rw [h, hjb]
    have hab : a = (st.par^[i - j]) b := hia.symm.trans hsplit
    have hcyc' : (st.par^[i - j]) p = p := by
      have h1 : (st.par^[i - j + 1]) b = (st.par^[i - j]) p := by
        rw [show i - j + 1 = (i - j).succ by omega, Function.iterate_succ_apply, hpb]
      rw [← h1, Function.iterate_succ_apply', ← hab, hpa]
    exact hp0 (hac p (i - j) (by omega) hcyc')

/-- **The root is in no child's set.** -/
theorem root_notin_child (st : HState) (hpar : ParOK st) (hac : Acyc st) {p c : ℕ}
    (hp0 : p ≠ 0) (hc : c ∈ kids st p) {i : ℕ} (hi : Reach st i c p) : False := by
  have hpc : st.par c = p := hpar p c hc
  have hp : (st.par^[i]) p = c := reach_par st hpar i c p hi
  have hcyc' : (st.par^[i + 1]) p = p := by
    rw [Function.iterate_succ_apply', hp, hpc]
  exact hp0 (hac p (i + 1) (by omega) hcyc')

/-- **The support construction.**  A live root's abstracted subtree is covered by as many distinct
live slots as it has nodes, at every fuel. -/
theorem support_exists (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hkn : ∀ q, KidsNodup st q) (hac : Acyc st) (hnn : NILNotChild st) :
    ∀ (f p : ℕ), p < st.n → p ≠ 0 → ∃ s : Finset ℕ,
      s.card = (treeOf st f p).size ∧ (∀ x ∈ s, x < st.n) ∧
      (∀ x ∈ s, ∃ i, i ≤ f ∧ Reach st i p x) ∧ p ∈ s := by
  intro f
  induction f with
  | zero =>
    intro p hp hp0
    have hshape : treeOf st 0 p = FibHeapForest.Tree.node p ([] : List Child) := rfl
    refine ⟨{p}, ?_, ?_, ?_, by simp⟩
    · rw [hshape, FibHeapForest.size_node]
      simp [FibHeapForest.sizeSum]
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact hp
    · intro x hx
      rw [Finset.mem_singleton] at hx
      exact ⟨0, by omega, hx.symm⟩
  | succ f ih =>
    intro p hp hp0
    have hex : ∀ c, c ∈ kids st p → ∃ s : Finset ℕ,
        s.card = (treeOf st f c).size ∧ (∀ x ∈ s, x < st.n) ∧
        (∀ x ∈ s, ∃ i, i ≤ f ∧ Reach st i c x) ∧ c ∈ s :=
      fun c hc => ih c (hslot p hp c hc) (fun hcc => hnn p (hcc ▸ hc))
    let S : ℕ → Finset ℕ := fun c => if h : c ∈ kids st p then (hex c h).choose else ∅
    have hS : ∀ c (hc : c ∈ kids st p),
        (S c).card = (treeOf st f c).size ∧ (∀ x ∈ S c, x < st.n) ∧
        (∀ x ∈ S c, ∃ i, i ≤ f ∧ Reach st i c x) ∧ c ∈ S c := by
      intro c hc
      have hd : S c = (hex c hc).choose := by
        simp only [S]
        rw [dif_pos hc]
      rw [hd]
      exact (hex c hc).choose_spec
    have hnd : (kids st p).Nodup := nodup_of_kidsNodup st p (hkn p)
    have hdisj : ∀ a ∈ kids st p, ∀ b ∈ kids st p, a ≠ b → Disjoint (S a) (S b) := by
      intro a ha b hb hne'
      rw [Finset.disjoint_left]
      intro x hxa hxb
      obtain ⟨i, -, hi⟩ := (hS a ha).2.2.1 x hxa
      obtain ⟨j, -, hj⟩ := (hS b hb).2.2.1 x hxb
      exact sib_disjoint st hpar hac hp0 ha hb hne' hi hj
    have hpmem : ∀ c ∈ kids st p, p ∉ S c := by
      intro c hc hpc
      obtain ⟨i, -, hi⟩ := (hS c hc).2.2.1 p hpc
      exact root_notin_child st hpar hac hp0 hc hi
    have hnotin : p ∉ (kids st p).foldr (fun a acc => S a ∪ acc) ∅ :=
      not_mem_foldr_union _ S hpmem
    have hmaps : (kids st p).map (fun a => (S a).card)
        = (kids st p).map (fun c => (treeOf st f c).size) :=
      List.map_congr_left (fun c hc => (hS c hc).1)
    have hcardU : ((kids st p).foldr (fun a acc => S a ∪ acc) ∅).card
        = ((kids st p).map fun c => (treeOf st f c).size).sum := by
      rw [card_union_list (kids st p) S hnd hdisj, hmaps]
    refine ⟨insert p ((kids st p).foldr (fun a acc => S a ∪ acc) ∅), ?_, ?_, ?_, by simp⟩
    · have hshape : treeOf st (f + 1) p = FibHeapForest.Tree.node p
          ((kids st p).map fun c => Child.mk (treeOf st f c) (ldeg st c) (st.mrk c)) := rfl
      have hsum : FibHeapForest.sizeSum ((kids st p).map fun c =>
            Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))
          = ((kids st p).map fun c => (treeOf st f c).size).sum := by
        simp only [FibHeapForest.sizeSum]
        rw [List.map_map]
        have hm : (FibHeapForest.Child.size ∘ fun c =>
              Child.mk (treeOf st f c) (ldeg st c) (st.mrk c))
            = (fun c => (treeOf st f c).size) := by
          funext c
          rfl
        rw [hm]
      rw [Finset.card_insert_of_notMem hnotin, hcardU, hshape, FibHeapForest.size_node, hsum]
      omega
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · obtain ⟨c, hc, hxc⟩ := mem_foldr_union _ S hx
        exact (hS c hc).2.1 x hxc
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨0, by omega, rfl⟩
      · obtain ⟨c, hc, hxc⟩ := mem_foldr_union _ S hx
        obtain ⟨i, hi, hreachc⟩ := (hS c hc).2.2.1 x hxc
        exact ⟨i + 1, by omega, ⟨c, hc, hreachc⟩⟩

/-- **`Support` from machine facts** — the last premise of the rank cap, discharged. -/
theorem support_of_noCycle (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hkn : ∀ q, KidsNodup st q) (hac : Acyc st) (hnn : NILNotChild st) {f p : ℕ}
    (hp : p < st.n) (hp0 : p ≠ 0) : Support st f p := by
  obtain ⟨s, hcard, hlive, -, -⟩ := support_exists st hpar hslot hkn hac hnn f p hp hp0
  exact ⟨s, hcard, hlive⟩

/-- **The rank cap with no analytic hypothesis left.**  Every premise is a machine invariant:
parents and children agree (`ParOK`), slots are closed down and up (`SlotOK`, `ParSlot`), ring
children are distinct (`KidsNodup`), there is no `par` cycle (`NoCycle`), the mark is a bit
(`MarkOK`), and the child lists are in link order (`PosOK`).  `Faithful` is gone (M1b) and
`Support` is gone (here).  The updaters are what remain to establish those seven. -/
theorem degree_le_rankCap_zero (st : HState) (hpar : ParOK st) (hslot : SlotOK st)
    (hps : ParSlot st) (hkn : ∀ q, KidsNodup st q) (hac : Acyc st) (hs : NILSelf st)
    (hnl : NILLeaf st) (hnn : NILNotChild st) (hm : MarkOK st) (hp : PosOK st)
    {p : ℕ} (hpv : p < st.n) (hp0 : p ≠ 0) (hsup : Support st (st.n + 1) p) :
    st.deg p ≤ FibHeapAccounting.rankCap st.n :=
  degree_le_rankCap_of_machine st hpar hslot hps hs hac hnl hm hp hpv hp0 hsup

end Submission.FibHeapSupport
