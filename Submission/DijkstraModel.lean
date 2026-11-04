import Frontier.Spec

/-!
# Submission.DijkstraModel — lazy binary-heap Dijkstra: invariant, exchange, certificate

Pure math over decoded arrays (no `RAM`).  Decoded run quantities: `distA : Fin n → ℝ≥0`
(the `dist` array), `reachA doneA : Fin n → ℕ` (flag arrays), `hv : ℕ → Fin G.n` and
`hd : ℕ → ℝ≥0` (heap arrays; entries at positions `< h`), `h ins : ℕ` (heap size and
total inserts).

Standing invariant `Inv`: `ghost` (every reached vertex carries an exact realized
walk, `len = distA`), `relax_hold` (edges out of settled vertices
are relaxed at current labels; heads reached), `heapOK` (min-heap order),
`entry_cur`, `entry_mono`, `entry_reach`, `source0`, `done_reach`.

Main results: `pop_settle_exact` (min-exchange) and `certificate` (at heap
exhaustion the decoded labels are the exact distances).
-/

namespace Submission.DijkstraModel

open Frontier Graph NNReal ENNReal

variable {G : Graph} {s : Fin G.n}
variable {distA : Fin G.n → ℝ≥0} {reachA doneA : Fin G.n → ℕ}
variable {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h ins : ℕ}

/-! ## Heap order -/

/-- Min-heap order: a parent index never has a larger key than its children. -/
def HeapOK (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h : ℕ) : Prop :=
  ∀ i, i < h → ∀ j, j < h → (j = 2 * i + 1 ∨ j = 2 * i + 2) → hd i ≤ hd j

/-- On a min-heap the root key is at most every entry key. -/
theorem heapOK_min {hv : ℕ → Fin G.n} {hd : ℕ → ℝ≥0} {h : ℕ} (H : HeapOK hv hd h)
    {i : ℕ} (hi : i < h) : hd 0 ≤ hd i := by
  suffices ∀ k i, i < h → i ≤ k → hd 0 ≤ hd i by exact this i i hi le_rfl
  intro k
  induction k with
  | zero =>
    intro i hi hk
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    intro i hi hk
    by_cases h0 : i = 0
    · subst h0; exact le_rfl
    · set p := (i - 1) / 2 with hp
      have hpp : p < i := by
        have h1 : 2 * p ≤ i - 1 := by
          have := Nat.div_mul_le_self (i - 1) 2
          omega
        omega
      have hrel : i = 2 * p + 1 ∨ i = 2 * p + 2 := by
        have hdiv : 2 * ((i - 1) / 2) + (i - 1) % 2 = i - 1 := by omega
        have hmod : (i - 1) % 2 = 0 ∨ (i - 1) % 2 = 1 := by omega
        rcases hmod with hm | hm <;> rw [hm] at hdiv <;> omega
      have hph : p < h := Nat.lt_of_le_of_lt (Nat.le_of_lt hpp) hi
      have hle : hd p ≤ hd i := H p hph i hi hrel
      exact (ih p hph (by omega)).trans hle

/-- The full standing invariant of a lazy min-heap Dijkstra run. -/
structure Inv (G : Graph) (s : Fin G.n)
    (distA : Fin G.n → ℝ≥0) (reachA doneA : Fin G.n → ℕ)
    (hv : ℕ → Fin G.n) (hd : ℕ → ℝ≥0) (h ins : ℕ) : Prop where
  ghost : ∀ v, reachA v ≠ 0 → ∃ p, G.IsWalk s v p ∧ G.len p = distA v
  relax_hold : ∀ e : Fin G.m, doneA (G.src e) ≠ 0 →
    reachA (G.dst e) ≠ 0 ∧
    ((distA (G.dst e) : ℝ≥0) : ℝ≥0∞) ≤ ((distA (G.src e) : ℝ≥0) : ℝ≥0∞) + G.w e
  heapOK : HeapOK hv hd h
  entry_cur : ∀ v, reachA v ≠ 0 → doneA v = 0 → ∃ i, i < h ∧ hv i = v ∧ hd i = distA v
  entry_mono : ∀ i, i < h → distA (hv i) ≤ hd i
  entry_reach : ∀ i, i < h → reachA (hv i) ≠ 0
  source0 : distA s = 0 ∧ reachA s ≠ 0
  done_reach : ∀ u, doneA u ≠ 0 → reachA u ≠ 0

/-! ## Soundness of reached labels -/

/-- A reached vertex's label is at least its true distance. -/
theorem dist_le_distA (I : Inv G s distA reachA doneA hv hd h ins) {v : Fin G.n}
    (hv0 : reachA v ≠ 0) : ((G.dist s v : ℝ≥0∞)) ≤ ((distA v : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨p, hp, hlen⟩ := I.ghost v hv0
  rw [← hlen]
  exact_mod_cast dist_le_len hp

/-! ## Subpath optimality of shortest walks -/

/-- Splitting a shortest walk at `x` makes both pieces shortest. -/
theorem delta_split {y x v : Fin G.n} {q₁ q₂ : List (Fin G.m)}
    (h : G.dist s v = G.dist s y + ((G.len (q₁ ++ q₂) : ℝ≥0) : ℝ≥0∞))
    (h₁ : G.IsWalk y x q₁) (h₂ : G.IsWalk x v q₂) :
    G.dist s x = G.dist s y + ((G.len q₁ : ℝ≥0) : ℝ≥0∞) ∧
    G.dist s v = G.dist s x + ((G.len q₂ : ℝ≥0) : ℝ≥0∞) := by
  have h' : G.dist s v = G.dist s y + G.len (q₁ ++ q₂) := by
    simpa [len_append, ENNReal.coe_add, add_assoc] using h
  obtain ⟨a, b⟩ := visits_split (G := G) (s := s) (y := y) (x := x) (v := v)
    (q₁ := q₁) (q₂ := q₂) h' h₁ h₂
  exact ⟨a, b⟩

/-! ## The prefix-settled chain -/

/-- Along a walk whose edges all leave settled vertices, starting at an exactly
labelled vertex, the end label is exact. -/
theorem distA_eq_prefix_settled (I : Inv G s distA reachA doneA hv hd h ins) :
    ∀ (x v : Fin G.n) (p : List (Fin G.m)) (hp : G.IsWalk x v p),
      G.dist s v = G.dist s x + ((G.len p : ℝ≥0) : ℝ≥0∞) →
      ((distA x : ℝ≥0) : ℝ≥0∞) = G.dist s x →
      (∀ e ∈ p, doneA (G.src e) ≠ 0) →
      ((distA v : ℝ≥0) : ℝ≥0∞) = G.dist s v := by
  intro x v p hp
  induction hp with
  | nil u =>
    intro hshort hx hset
    exact hx
  | @cons e w q hq ih =>
    intro hshort hx hset
    have hdj : doneA (G.src e) ≠ 0 := hset e (by simp)
    have htail : ∀ e' ∈ q, doneA (G.src e') ≠ 0 :=
      fun e' he' => hset e' (by simp [he'])
    obtain ⟨hreachE, hrelE⟩ := I.relax_hold e hdj
    have hshort' : G.dist s w = G.dist s (G.src e) + ((G.len ([e] ++ q) : ℝ≥0) : ℝ≥0∞) := by
      simpa [List.singleton_append, len_cons, ENNReal.coe_add, add_assoc] using hshort
    have hsplit := delta_split (y := G.src e) (x := G.dst e) (v := w)
      (q₁ := [e]) (q₂ := q) hshort' (IsWalk.single e) hq
    obtain ⟨hdstEq, hrest⟩ := hsplit
    have hdstGe : G.dist s (G.dst e) ≤ ((distA (G.dst e) : ℝ≥0) : ℝ≥0∞) :=
      dist_le_distA I hreachE
    have hdstEx : ((distA (G.dst e) : ℝ≥0) : ℝ≥0∞) = G.dist s (G.dst e) := by
      refine le_antisymm ?_ hdstGe
      have h1 : ((distA (G.dst e) : ℝ≥0) : ℝ≥0∞) ≤ ((distA (G.src e) : ℝ≥0) : ℝ≥0∞) + G.w e :=
        hrelE
      rw [hx] at h1
      have h3 : (G.w e : ℝ≥0∞) = ((G.len [e] : ℝ≥0) : ℝ≥0∞) := by simp [len_singleton]
      rw [h3, ← hdstEq] at h1
      exact h1
    exact ih hrest hdstEx htail

/-! ## The first unsettled vertex of a walk -/

/-- A walk from a settled origin to an unsettled endpoint has a first unsettled
vertex `w`; every edge of the prefix leaves a settled vertex. -/
theorem exists_first_unsettled (doneA : Fin G.n → ℕ) (u : Fin G.n) :
    ∀ (v : Fin G.n) (p : List (Fin G.m)) (hp : G.IsWalk u v p),
      doneA u ≠ 0 → doneA v = 0 →
      ∃ (w : Fin G.n) (q₁ q₂ : List (Fin G.m)), p = q₁ ++ q₂ ∧
        G.IsWalk u w q₁ ∧ G.IsWalk w v q₂ ∧ doneA w = 0 ∧
        (∀ e ∈ q₁, doneA (G.src e) ≠ 0) := by
  intro v p hp
  induction hp with
  | nil x =>
    intro hu hv0
    refine ⟨x, [], [], rfl, IsWalk.nil _, IsWalk.nil _, ?_, ?_⟩
    · simpa using hv0
    · intro e he; simp at he
  | @cons e w q hq ih =>
    intro hu hv0
    by_cases hd0 : doneA (G.dst e) = 0
    · refine ⟨G.dst e, [e], q, rfl, IsWalk.single e, hq, hd0, ?_⟩
      intro e' he'
      rcases List.mem_singleton.mp he' with rfl
      exact hu
    · obtain ⟨w', q₁, q₂, hsplit, h1, h2, hw0, hsetQ⟩ := ih hd0 hv0
      refine ⟨w', e :: q₁, q₂, ?_, ?_, h2, hw0, ?_⟩
      · simp [hsplit]
      · exact IsWalk.cons h1
      · intro e' he'
        rcases List.mem_cons.mp he' with hmem | hmem
        · subst hmem; exact hu
        · exact hsetQ e' hmem

/-! ## The min-exchange at settle time -/

/-- A min-pop settle of an unsettled, reached vertex is exact:
`distA v = G.dist s v`.  (If `s` is still unsettled its zero entry caps the
popped value at `0` and the claim is immediate.) -/
theorem pop_settle_exact (I : Inv G s distA reachA doneA hv hd h ins)
    (hpos : 0 < h) (hnot : doneA (hv 0) = 0) (hreach : reachA (hv 0) ≠ 0) :
    ((distA (hv 0) : ℝ≥0) : ℝ≥0∞) = G.dist s (hv 0) := by
  set v := hv 0
  have hcur : distA v ≤ hd 0 := I.entry_mono 0 hpos
  obtain ⟨i, hi, hvi, hdi⟩ := I.entry_cur v hreach hnot
  have hmin : hd 0 ≤ hd i := heapOK_min I.heapOK hi
  rw [hdi] at hmin
  have hdv : hd 0 = distA v := le_antisymm hmin hcur
  have hge : G.dist s v ≤ ((distA v : ℝ≥0) : ℝ≥0∞) := dist_le_distA I hreach
  have hle : ((distA v : ℝ≥0) : ℝ≥0∞) ≤ G.dist s v := by
    by_cases hs0 : doneA s = 0
    · -- s unsettled: its zero entry caps the popped value at 0
      obtain ⟨j, hj, hjs, hjd⟩ := I.entry_cur s I.source0.2 hs0
      have hjm : hd 0 ≤ hd j := heapOK_min I.heapOK hj
      rw [hjd, I.source0.1] at hjm
      have hz : ((distA v : ℝ≥0) : ℝ≥0∞) = 0 := by
        refine le_antisymm ?_ bot_le
        rw [← hdv]
        exact_mod_cast hjm
      rw [hz]
      exact bot_le
    · by_cases htriv : G.dist s v = ⊤
      · rw [htriv]; exact le_top
      · obtain ⟨p, hp, hpe⟩ := exists_walk_eq_dist htriv
        obtain ⟨w, q₁, q₂, hsplit, h1, h2, hw0, hsetQ⟩ :=
          exists_first_unsettled doneA s v p hp hs0 hnot
        have hsrcEq : ((distA s : ℝ≥0) : ℝ≥0∞) = G.dist s s := by
          rw [dist_self]
          exact_mod_cast I.source0.1
        have hpe' : G.dist s v = G.dist s s + ((G.len (q₁ ++ q₂) : ℝ≥0) : ℝ≥0∞) := by
          rw [hsplit] at hpe
          rw [dist_self, zero_add]
          exact hpe.symm
        have hwp : G.dist s w = G.dist s s + ((G.len q₁ : ℝ≥0) : ℝ≥0∞) :=
          (delta_split (y := s) (x := w) (v := v) (q₁ := q₁) (q₂ := q₂) hpe' h1 h2).1
        have hex : ((distA w : ℝ≥0) : ℝ≥0∞) = G.dist s w :=
          distA_eq_prefix_settled I s w q₁ h1 (by simpa using hwp) hsrcEq hsetQ
        have hreachW : reachA w ≠ 0 := by
          by_contra! hn
          by_cases hwv : w = v
          · subst hwv; exact hreach hn
          · by_cases hws : w = s
            · subst hws; exact I.source0.2 hn
            · rcases List.eq_nil_or_concat q₁ with hq | ⟨q₁', e₀, rfl⟩
              · rw [hq] at h1
                rw [isWalk_nil_iff] at h1
                exact hws h1.symm
              · rw [List.concat_eq_append] at h1
                rw [IsWalk.concat_iff] at h1
                obtain ⟨_, hdst⟩ := h1
                have hs0' : doneA (G.src e₀) ≠ 0 := hsetQ e₀ (by simp)
                obtain ⟨hrE, _⟩ := I.relax_hold e₀ hs0'
                rw [hdst] at hrE
                exact hrE hn
        obtain ⟨j, hj, hjw, hjd⟩ := I.entry_cur w hreachW hw0
        have hjm : hd 0 ≤ hd j := heapOK_min I.heapOK hj
        rw [hjd] at hjm
        have hwle : G.dist s w ≤ G.dist s v := by
          have hsp := (delta_split (y := s) (x := w) (v := v) (q₁ := q₁) (q₂ := q₂)
            hpe' h1 h2).2
          rw [hsp]
          exact le_self_add
        rw [← hex] at hwle
        calc ((distA v : ℝ≥0) : ℝ≥0∞) = ((hd 0 : ℝ≥0) : ℝ≥0∞) := by rw [hdv]
          _ ≤ ((distA w : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hjm
          _ ≤ G.dist s v := hwle
  exact le_antisymm hle hge

/-! ## The certificate at heap exhaustion -/

/-- Decoded labels of the arrays. -/
noncomputable def labOf (distA : Fin G.n → ℝ≥0) (reachA : Fin G.n → ℕ) : Fin G.n → ℝ≥0∞ :=
  fun v => if reachA v = 0 then ⊤ else ((distA v : ℝ≥0) : ℝ≥0∞)

theorem labOf_apply (distA : Fin G.n → ℝ≥0) (reachA : Fin G.n → ℕ) (v : Fin G.n) :
    labOf distA reachA v = if reachA v = 0 then ⊤ else ((distA v : ℝ≥0) : ℝ≥0∞) := rfl

/-- At `h = 0` every reached vertex is settled. -/
theorem settled_of_empty (I : Inv G s distA reachA doneA hv hd 0 ins)
    {v : Fin G.n} (hv0 : reachA v ≠ 0) : doneA v ≠ 0 := by
  by_contra! hn
  obtain ⟨i, hi, -, -⟩ := I.entry_cur v hv0 (by simpa using hn)
  exact absurd hi (by simp)

/-- At heap exhaustion the decoded labels are exactly the distances. -/
theorem certificate (I : Inv G s distA reachA doneA hv hd 0 ins) :
    G.IsSSSP s (labOf distA reachA) := by
  refine isSSSP_of_relaxed_of_realized (G := G) (s := s) (d := labOf distA reachA) ?_ ?_ ?_
  · rw [labOf_apply]
    simp [I.source0.2, I.source0.1]
  · intro e
    by_cases hs : doneA (G.src e) = 0
    · have hn : reachA (G.src e) = 0 := by
        by_contra! h
        exact (settled_of_empty I h) hs
      rw [labOf_apply, labOf_apply, hn]
      simp
    · obtain ⟨hreachE, hrelE⟩ := I.relax_hold e hs
      have hs' : reachA (G.src e) ≠ 0 := I.done_reach _ hs
      rw [labOf_apply, labOf_apply]
      simp [hreachE, hs', hrelE]
  · intro v hdv
    rw [labOf_apply] at hdv
    by_cases hr : reachA v = 0
    · rw [hr] at hdv
      exact absurd hdv (by simp)
    · obtain ⟨p, hp, hlen⟩ := I.ghost v hr
      refine ⟨p, hp, ?_⟩
      rw [labOf_apply, if_neg hr, ← hlen]

end Submission.DijkstraModel
