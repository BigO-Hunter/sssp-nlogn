import Submission.DijkstraHeap

/-!
# Submission.DijkstraMain — the main loop of the row program

`mainLoop_runs` runs `Submission.DijkstraProg.mainLoop` under the measure
`mu st = 2 * (G.m + 1 - RoomSt st) + st.w "h"`: twice the unsettled edge budget plus the
heap size.  Every iteration pops the minimum (which strictly lowers `h`) and, when the popped
vertex is fresh, settles it (which strictly lowers the edge budget by its out-degree, raising
`h` back by at most that same amount).  So one iteration costs at most `K` units of the
measure, and the carried potential `cost ≤ c0 + K * (mu0 - mu st)` closes the loop.

The two room facts carried by the invariant (`h` and `ins` plus the unsettled edge budget
never exceed `m + 1`) are exactly what `settleBody_runs` wants as its `hroom` / `hinsroom`
hypotheses, and `RoomSt_store` + `RoomSt_add_outdeg` restore them after a settle.
-/

namespace Submission.DijkstraMain

open Frontier Frontier.RAM WExpr Stmt NNReal ENNReal
open Submission.DijkstraProg Submission.DijkstraModel Submission.DijkstraDecode
open Submission.DijkstraSim Submission.DijkstraHeap

variable {G : Graph} {s : Fin G.n}

/-- Loop measure: twice the unsettled edge budget plus the heap size. -/
noncomputable def mu (G : Graph) (st : State ℝ≥0) : ℕ := 2 * (G.m + 1 - RoomSt G st) + st.w "h"

/-- Per-iteration cost constant. -/
def Kc (G : Graph) : ℕ := 18 * rkD (G.m + 1) 0 + 3 + (12 * rk (G.m + 1) + 30)

/-- A charge moves no array. -/
theorem RoomSt_charge (st : State ℝ≥0) (k : ℕ) : RoomSt G (st.charge k) = RoomSt G st := by
  simp only [RoomSt]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [show (st.charge k).wa "done" (v : ℕ) = st.wa "done" (v : ℕ) from rfl]

/-- A charge moves no chain. -/
theorem chainOf_charge (st : State ℝ≥0) (u k : ℕ) : chainOf (st.charge 1) u k = chainOf st u k := by
  simp only [chainOf]
  rw [show (st.charge 1).wa "head" u = st.wa "head" u from rfl]
  exact chainWalk_congr (fun _ _ => rfl)

/-! ### Scalar accounting (measure, room, cost) -/

/-- A settle step never raises the measure. -/
theorem mu_step_le {m RS L h h' : ℕ} (hL : RS + L ≤ m) (hh : h' ≤ h - 1 + L) (h1 : 1 ≤ h) :
    2 * (m + 1 - (RS + L)) + h' ≤ 2 * (m + 1 - RS) + h - 1 := by omega

/-- A settle step drops the measure by at least the scanned edge count plus one. -/
theorem mu_step_gap {m RS L h h' : ℕ} (hL : RS + L ≤ m) (hh : h' ≤ h - 1 + L) (h1 : 1 ≤ h) :
    2 * (m + 1 - RS) + h - (2 * (m + 1 - (RS + L)) + h') ≥ L + 1 := by omega

/-- The heap room fact survives a settle step. -/
theorem room_step {m RS L h h' : ℕ} (hL : RS + L ≤ m) (hh : h' ≤ h - 1 + L)
    (hr : h + (m - RS) ≤ m + 1) : h' + (m - (RS + L)) ≤ m + 1 := by omega

/-- The insert room fact survives a settle step. -/
theorem insroom_step {m RS L ins ins' : ℕ} (hL : RS + L ≤ m) (hi : ins' ≤ ins + L)
    (hr : ins + (m - RS) ≤ m + 1) : ins' + (m - (RS + L)) ≤ m + 1 := by omega

/-- The loop invariant: the model invariant, the settled labels, heap validity, chain
well-formedness, the input frame, the two room facts, and the cost potential. -/
structure LoopInv (G : Graph) (s : Fin G.n) (c0 μ0 K : ℕ) (st : State ℝ≥0) : Prop where
  inv : Inv G s (fun v => st.va "dist" v) (fun v => st.wa "reach" v) (fun v => st.wa "done" v)
    (hvD s st) (fun i => st.va "hd" i) (st.w "h") (st.w "ins")
  se : SettledExact G s st
  val : HeapV (G := G) st (st.w "h")
  cw : ChainWF G st
  f0 : F0 G s st
  af : AF G st
  room : st.w "h" + (G.m - RoomSt G st) ≤ G.m + 1
  insroom : st.w "ins" + (G.m - RoomSt G st) ≤ G.m + 1
  mub : mu G st ≤ μ0
  costb : st.cost ≤ c0 + K * (μ0 - mu G st)

/-- The main loop: pop minima until the heap is exhausted. -/
theorem mainLoop_runs {st : State ℝ≥0} {c0 μ0 K : ℕ}
    (hKpop : ∀ h : ℕ, h ≤ G.m + 1 → 18 * rkD h 0 + 30 ≤ K)
    (hKs : 12 * rk (G.m + 1) + 30 ≤ K)
    (I : LoopInv G s c0 μ0 K st) :
    Runs realOps mainLoop st (fun st' =>
      Inv G s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = 0 ∧ st'.cost ≤ c0 + K * μ0 + 1 ∧ AF G st' ∧ F0 G s st') := by
  have hRm_le : RoomSt G st ≤ G.m := RoomSt_le (G := G) st
  have hcap0 : 0 < st.cap := by have := I.f0.hcap; omega
  have hcap1 : 1 < st.cap := by have := I.f0.hcap; omega
  simp only [mainLoop]
  refine runs_while_nat
    (I := fun n st' => LoopInv G s c0 μ0 K st' ∧ mu G st' = n)
    (Q := fun st' => Inv G s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v)
      (fun v => st'.wa "done" v) (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = 0 ∧ st'.cost ≤ c0 + K * μ0 + 1 ∧ AF G st' ∧ F0 G s st')
    ?_ (mu G st) st ⟨I, rfl⟩
  intro n s' ⟨IS, hmu⟩
  have hcap0' : 0 < s'.cap := by have := IS.f0.hcap; omega
  have hcap1' : 1 < s'.cap := by have := IS.f0.hcap; omega
  have hcond' : evalW s' (lt (lit 0) (var "h")) = some (if 0 < s'.w "h" then 1 else 0) :=
    evalW_lt_of (evalW_lit_of hcap0') (evalW_var s' "h") hcap1'
  by_cases hh : s'.w "h" = 0
  · -- exit: the heap is empty, the certificate clause sees `h = 0`
    refine ⟨0, ?_, fun hx => absurd hx (by decide), fun _ => ⟨?_, hh, ?_, IS.af.charge 1, IS.f0.charge 1⟩⟩
    · rw [hcond', if_neg (by omega)]
    · have h := IS.inv
      have hfun : hvD s s' = hvD s (s'.charge 1) :=
        funext (fun i => (hvD_congr (st := s') (st' := s'.charge 1) (fun _ => rfl) i).symm)
      rw [hfun] at h
      exact h
    · -- cost: the potential is nonnegative, and the final (failed) guard charge is the `+1`
      have hsub : μ0 - mu G s' ≤ μ0 := Nat.sub_le _ _
      have hmul := Nat.mul_le_mul_left K hsub
      have hcost : (s'.charge 1).cost = s'.cost + 1 := rfl
      have := IS.costb
      omega
  · have hpos : 0 < s'.w "h" := by omega
    have hbound : s'.w "h" ≤ G.m + 1 := by have := IS.room; omega
    refine ⟨1, ?_, ?_, fun hx => absurd hx (by decide)⟩
    · rw [hcond', if_pos hpos]
    · intro _
      have hval0 : s'.wa "hv" 0 < G.n := IS.val 0 hpos
      set u : Fin G.n := hvD s s' 0 with hu
      have huval : (u : ℕ) = (s'.charge 1).wa "hv" 0 := by
        rw [hu]; exact hvD_wa (show (s'.charge 1).wa "hv" 0 < G.n from hval0)
      have hreachS : s'.wa "reach" u ≠ 0 := IS.inv.entry_reach 0 hpos
      -- 1. pop the minimum
      refine runs_seq ?_
      refine (popBody_runs (st := s'.charge 1) (IS.f0.charge 1) (IS.af.charge 1) IS.inv IS.val
        hpos hbound).mono ?_
      rintro t1 ⟨hF1, hAF1, hIH1, hh1, hins1, hv1, hdv1, hv1n, hval1, hAFr1, hcost1⟩
      have hh1' : t1.w "h" = s'.w "h" - 1 := hh1
      have hins1' : t1.w "ins" = s'.w "ins" := hins1
      have hse1 : SettledExact G s t1 := IS.se.congr hAFr1.reach hAFr1.done hAFr1.dist
      have hcw1 : ChainWF G t1 := IS.cw.congr hAFr1.head hAFr1.nxt
      have hRm1 : RoomSt G t1 = RoomSt G s' := by
        have h0 : RoomSt G t1 = RoomSt G (s'.charge 1) := by
          simp only [RoomSt]
          exact Finset.sum_congr rfl (fun v _ => by rw [hAFr1.done (v : ℕ)])
        exact h0.trans (RoomSt_charge s' 1)
      have hpC : t1.cost ≤ s'.cost + 1 + (18 * rkD (s'.w "h") 0 + 25) := by
        have h1 : (s'.charge 1).cost = s'.cost + 1 := rfl
        have h2 : (s'.charge 1).w "h" = s'.w "h" := rfl
        have h3 := hcost1
        rw [h1, h2] at h3
        omega
      have hvreg : t1.w "v" = (u : ℕ) := hv1.trans huval.symm
      -- the relaxation test reads `done[v]`
      have hvE : evalW t1 (var "v") = some (u : ℕ) := by rw [evalW_var, hvreg]
      have hloadD : evalW t1 (load "done" (var "v")) = some (t1.wa "done" (u : ℕ)) :=
        evalW_load_of hvE (by rw [hAF1.doneL]; exact u.isLt)
      have ht1cap : 1 < t1.cap := by have := hF1.hcap; omega
      have ht1cap0 : 0 < t1.cap := by omega
      have hcondD : evalW t1 (eq (load "done" (var "v")) (lit 0))
          = some (if t1.wa "done" (u : ℕ) = 0 then 1 else 0) :=
        evalW_eq_of hloadD (evalW_lit_of ht1cap0) ht1cap
      by_cases hdne : t1.wa "done" (u : ℕ) = 0
      · -- 2a. fresh pop: settle `u`, then sweep its out-edges
        have hdu : t1.wa "done" u = 0 := hdne
        have hdu0 : s'.wa "done" u = 0 := (hAFr1.done (u : ℕ)).symm.trans hdne
        have hru1 : t1.wa "reach" u ≠ 0 := by
          have h := hAFr1.reach (u : ℕ)
          rw [h]; exact hreachS
        -- `pop_settle_exact` lives at the PRE-pop state, where the full `Inv` is available
        have huex0 : ((s'.va "dist" u : ℝ≥0) : ℝ≥0∞) = G.dist s u :=
          pop_settle_exact IS.inv hpos hdu0 hreachS
        have huex : ((t1.va "dist" u : ℝ≥0) : ℝ≥0∞) = G.dist s u := by
          rw [hAFr1.dist (u : ℕ)]; exact huex0
        have hIH1' : InvH u s (fun v => t1.va "dist" v) (fun v => t1.wa "reach" v)
            (fun v => t1.wa "done" v) (hvD s t1) (fun i => t1.va "hd" i) (t1.w "h")
            (t1.w "ins") := by
          have heq : hvD s (s'.charge 1) 0 = u :=
            (hvD_congr (st := s') (st' := s'.charge 1) (fun _ => rfl) 0).trans hu.symm
          rw [heq] at hIH1
          exact hIH1
        -- the two room facts `settleBody_runs` wants
        have hRm : RoomSt G s' + (chainOf t1 u (G.m + 1)).length ≤ G.m := by
          have h := RoomSt_add_outdeg (G := G) (u := u) hdu0
          rwa [← hcw1 (u : ℕ) u.isLt] at h
        have hroom : t1.w "h" + (chainOf t1 u (G.m + 1)).length ≤ G.m + 1 := by
          have hr := IS.room
          omega
        have hinsroom : t1.w "ins" + (chainOf t1 u (G.m + 1)).length ≤ G.m + 1 := by
          have hr := IS.insroom
          omega
        have hLc : (chainOf (t1.charge 1) u (G.m + 1)).length
            = (chainOf t1 u (G.m + 1)).length := by rw [chainOf_charge]
        have hroom' : (t1.charge 1).w "h" + (chainOf (t1.charge 1) u (G.m + 1)).length
            ≤ G.m + 1 := by
          rw [hLc]; exact hroom
        have hinsroom' : (t1.charge 1).w "ins" + (chainOf (t1.charge 1) u (G.m + 1)).length
            ≤ G.m + 1 := by
          rw [hLc]; exact hinsroom
        refine runs_ite_true hcondD (by rw [if_pos hdne]; decide) ?_
        refine (settleBody_runs (st := t1.charge 1) (u := u) (hF1.charge 1) (hAF1.charge 1) hIH1'
          hval1 hse1 huex (hcw1.congr (fun _ => rfl) (fun _ => rfl)) hvreg hdu hru1 hroom'
          hinsroom').mono ?_
        rintro t2 ⟨hInv2, hse2, hval2, hcw2, hF2, hAF2, hcost2, hh2, hins2, hRm2⟩
        -- normalise the settle postcondition to the pre-charge state `t1`
        have hcost2' : t2.cost
            ≤ t1.cost + 1 + 3 + (12 * rk (G.m + 1) + 30) * (chainOf t1 u (G.m + 1)).length := by
          have h1 : (t1.charge 1).cost = t1.cost + 1 := rfl
          have h3 := hcost2
          rw [h1, hLc] at h3
          omega
        have hRm2' : RoomSt G t2 = RoomSt G s' + (chainOf t1 u (G.m + 1)).length := by
          have h1 : RoomSt G (t1.charge 1) = RoomSt G t1 := RoomSt_charge t1 1
          have h3 := hRm2
          rw [h1, hLc] at h3
          omega
        have hh2' : t2.w "h" ≤ s'.w "h" - 1 + (chainOf t1 u (G.m + 1)).length := by
          have h3 := hh2
          rw [show (t1.charge 1).w "h" = t1.w "h" from rfl, hLc] at h3
          omega
        have hins2' : t2.w "ins" ≤ s'.w "ins" + (chainOf t1 u (G.m + 1)).length := by
          have h3 := hins2
          rw [show (t1.charge 1).w "ins" = t1.w "ins" from rfl, hLc] at h3
          omega
        -- the measure strictly drops, by at least `L + 1`
        have hmuDrop : mu G t2 ≤ mu G s' - 1 := by
          simp only [mu]
          rw [hRm2']
          exact mu_step_le hRm hh2' hpos
        have hmuDiff : mu G s' - mu G t2 ≥ (chainOf t1 u (G.m + 1)).length + 1 := by
          simp only [mu]
          rw [hRm2']
          exact mu_step_gap hRm hh2' hpos
        refine ⟨mu G t2, ?_, ?_, rfl⟩
        · rw [← hmu]; omega
        · refine ⟨hInv2, hse2, hval2, hcw2, hF2, hAF2, ?_, ?_, ?_, ?_⟩
          · -- room
            rw [hRm2']
            exact room_step hRm hh2' IS.room
          · -- insroom
            rw [hRm2']
            exact insroom_step hRm hins2' IS.insroom
          · -- the measure never exceeds its entry value
            have := IS.mub
            omega
          · -- the cost potential
            have hK := hKpop (s'.w "h") hbound
            have hS : (12 * rk (G.m + 1) + 30) * (chainOf t1 u (G.m + 1)).length
                ≤ K * (chainOf t1 u (G.m + 1)).length := Nat.mul_le_mul_right _ hKs
            have hcostc : t2.cost
                ≤ s'.cost + K + (12 * rk (G.m + 1) + 30) * (chainOf t1 u (G.m + 1)).length := by
              omega
            have hkey : μ0 - mu G t2 = (μ0 - mu G s') + (mu G s' - mu G t2) := by
              have := IS.mub; omega
            have hdist : K * (μ0 - mu G t2)
                = K * (μ0 - mu G s') + K * (mu G s' - mu G t2) := by
              rw [hkey]; ring
            have hmul : K * ((chainOf t1 u (G.m + 1)).length + 1)
                = K * (chainOf t1 u (G.m + 1)).length + K := by ring
            have hM : K * ((chainOf t1 u (G.m + 1)).length + 1)
                ≤ K * (mu G s' - mu G t2) := Nat.mul_le_mul_left K hmuDiff
            rw [hdist]
            have := IS.costb
            omega
      · -- 2b. stale pop: `u` was already settled, nothing to do
        have hdne' : t1.wa "done" u ≠ 0 := hdne
        refine runs_ite_false (by rw [hcondD, if_neg hdne]) ?_
        refine runs_skip ?_
        have hRSt : RoomSt G ((t1.charge 1).charge 1) = RoomSt G s' := by
          rw [RoomSt_charge, RoomSt_charge]; exact hRm1
        have hwT : ((t1.charge 1).charge 1).w "h" = s'.w "h" - 1 := hh1'
        have hmuT : mu G ((t1.charge 1).charge 1) = mu G s' - 1 := by
          simp only [mu]
          rw [hRSt, hwT]
          omega
        have hmu1 : 1 ≤ mu G s' := by
          simp only [mu]
          have := RoomSt_le (G := G) s'
          omega
        have hInv2 : Inv G s (fun v => ((t1.charge 1).charge 1).va "dist" v)
            (fun v => ((t1.charge 1).charge 1).wa "reach" v)
            (fun v => ((t1.charge 1).charge 1).wa "done" v)
            (hvD s ((t1.charge 1).charge 1)) (fun i => ((t1.charge 1).charge 1).va "hd" i)
            (((t1.charge 1).charge 1).w "h") (((t1.charge 1).charge 1).w "ins") :=
          InvH.toInv_of_done hIH1 hdne'
        refine ⟨mu G ((t1.charge 1).charge 1), ?_, ?_, rfl⟩
        · rw [← hmu, hmuT]; omega
        · refine ⟨hInv2, ?_, hval1, hcw1.congr (fun _ => rfl) (fun _ => rfl),
            (hF1.charge 1).charge 1, (hAF1.charge 1).charge 1, ?_, ?_, ?_, ?_⟩
          · exact IS.se.congr hAFr1.reach hAFr1.done hAFr1.dist
          · -- room
            rw [hRSt, hwT]
            have hr := IS.room
            omega
          · -- insroom
            rw [hRSt]
            rw [show ((t1.charge 1).charge 1).w "ins" = t1.w "ins" from rfl, hins1']
            have hr := IS.insroom
            omega
          · -- the measure never exceeds its entry value
            rw [hmuT]
            have := IS.mub
            omega
          · -- the cost potential
            have hK := hKpop (s'.w "h") hbound
            have hcostc : (((t1.charge 1).charge 1)).cost ≤ s'.cost + K := by
              have h2 : (((t1.charge 1).charge 1)).cost = t1.cost + 2 := rfl
              omega
            have hkey : μ0 - mu G ((t1.charge 1).charge 1)
                = (μ0 - mu G s') + (mu G s' - mu G ((t1.charge 1).charge 1)) := by
              have := IS.mub; omega
            have hdif : mu G s' - mu G ((t1.charge 1).charge 1) ≥ 1 := by
              rw [hmuT]; omega
            have hdist : K * (μ0 - mu G ((t1.charge 1).charge 1))
                = K * (μ0 - mu G s') + K * (mu G s' - mu G ((t1.charge 1).charge 1)) := by
              rw [hkey]; ring
            have hM : K * 1 ≤ K * (mu G s' - mu G ((t1.charge 1).charge 1)) :=
              Nat.mul_le_mul_left K hdif
            rw [hdist]
            have := IS.costb
            omega

/-! ### The Dijkstra branch: `dijkstraBody_runs` -/

/-- `dijkstraBody` runs end to end: allocate the six arrays, build the adjacency chains, write
the four pre-push registers (`h := 0`, `ins := 0`, `reach[s] := 1`, `pv := s`), push the source,
and run the main loop to heap exhaustion.

Cost: `4n + 3m + 9` (allocation) `+ 6m + 2` (adjacency) `+ 4` (the four writes)
`+ 12·rk 0 + 13` (the source push) `+ Kc·(2m+3) + 1` (the main loop; its potential at entry is
`μ0 = 2(m + 1 - 0) + 1 = 2m + 3`). -/
theorem dijkstraBody_runs (st : State ℝ≥0) (hF : F0 G s st) :
    Runs realOps dijkstraBody st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      Inv G s (fun v => st'.va "dist" v) (fun v => st'.wa "reach" v) (fun v => st'.wa "done" v)
        (hvD s st') (fun i => st'.va "hd" i) (st'.w "h") (st'.w "ins") ∧
      st'.w "h" = 0 ∧
      st'.cost ≤ st.cost + (4 * G.n + 3 * G.m + 9) + (6 * G.m + 2) + 4
        + (12 * rk 0 + 13) + (Kc G * (2 * G.m + 3) + 1)) := by
  simp only [dijkstraBody]
  refine runs_seq ((allocAll_runs (G := G) (s := s) st hF).mono ?_)
  rintro sa ⟨hFa, hAFa, hHead, hDist, hReach, hDone, hHv, hHd, hCa⟩
  refine runs_seq ((buildAdj_runs (G := G) (s := s) sa hFa hAFa hHead ⟨hDist, hReach, hDone⟩).mono ?_)
  rintro sb ⟨hFb, hAFb, hChainb, hCostb, hZ3b⟩
  have hcapb0 : 0 < sb.cap := by have := hFb.hcap; omega
  have hcapb1 : 1 < sb.cap := by have := hFb.hcap; omega
  -- write 1: `h := 0`
  refine runs_seq (runs_wset (x := "h") (a := 0) (evalW_lit_of hcapb0) ?_)
  set t1 := (sb.setW "h" 0).charge 1 with ht1
  -- write 2: `ins := 0`
  refine runs_seq (runs_wset (x := "ins") (a := 0)
    (evalW_lit_of (by rw [ht1]; exact hcapb0)) ?_)
  set t2 := (t1.setW "ins" 0).charge 1 with ht2
  -- write 3: `reach[s] := 1`
  have hsE2 : evalW t2 (var "s") = some (s : ℕ) := by
    rw [evalW_var, ht2, w_charge, w_setW, if_neg (by decide : ("s" : String) ≠ "ins"),
      ht1, w_charge, w_setW, if_neg (by decide : ("s" : String) ≠ "h"), hFb.hs]
  have hjreach : (s : ℕ) < t2.wlen "reach" := by
    have h : t2.wlen "reach" = G.n := by
      rw [ht2, ht1]
      simp [State.setW, State.charge, hAFb.reachL]
    rw [h]; exact s.isLt
  refine runs_seq (runs_wstore (arr := "reach") (i := var "s") (e := lit 1) hsE2
    (evalW_lit_of (by rw [ht2, ht1]; exact hcapb1)) hjreach ?_)
  set t3 := (t2.storeW "reach" (s : ℕ) 1).charge 1 with ht3
  -- write 4: `pv := s`
  refine runs_seq (runs_wset (x := "pv") (e := var "s") (a := (s : ℕ)) (by
    rw [evalW_var, ht3, w_charge, w_storeW, ht2, w_charge, w_setW,
      if_neg (by decide : ("s" : String) ≠ "ins"), ht1, w_charge, w_setW,
      if_neg (by decide : ("s" : String) ≠ "h"), hFb.hs]) ?_)
  set t4 := (t3.setW "pv" (s : ℕ)).charge 1 with ht4
  -- the pre-push state
  have hF4 : F0 G s t4 := by
    rw [ht4, ht3, ht2, ht1]
    exact ⟨hFb.hn, hFb.hm, hFb.hs, hFb.hcap, hFb.hsrc, hFb.hdst, hFb.hw, hFb.hsrcL, hFb.hdstL,
      hFb.hwL⟩
  have hAF4 : AF G t4 := by
    rw [ht4, ht3, ht2, ht1]
    exact ⟨hAFb.distL, hAFb.reachL, hAFb.doneL, hAFb.headL, hAFb.nxtL, hAFb.hvL, hAFb.hdL⟩
  have hH4 : t4.w "h" = 0 := by rw [ht4, ht3, ht2, ht1]; rfl
  have hI4 : t4.w "ins" = 0 := by rw [ht4, ht3, ht2, ht1]; rfl
  have hP4 : t4.w "pv" = (s : ℕ) := by rw [ht4, ht3, ht2, ht1]; rfl
  have hDist4 : ∀ j, t4.va "dist" j = 0 := by
    intro j; rw [ht4, ht3, ht2, ht1]; exact hZ3b.dist j
  have hDone4 : ∀ j, t4.wa "done" j = 0 := by
    intro j; rw [ht4, ht3, ht2, ht1]; exact hZ3b.done j
  have hReach4 : ∀ j, t4.wa "reach" j = if j = (s : ℕ) then 1 else 0 := by
    intro j
    rw [ht4, ht3, ht2, ht1]
    simp [State.setW, State.storeW, State.charge, hZ3b.reach j]
  have hcost4 : t4.cost = sb.cost + 4 := by
    rw [ht4, ht3, ht2, ht1]
    simp [State.setW, State.storeW, State.charge]
  -- the push preconditions at `t4`
  have hpv4 : t4.w "pv" < G.n := by rw [hP4]; exact s.isLt
  have hsoft4 : EntrySoftH ⟨t4.w "pv", hpv4⟩ s (fun v => t4.va "dist" v)
      (fun v => t4.wa "reach" v) (fun v => t4.wa "done" v) (hvD s t4)
      (fun i => t4.va "hd" i) (t4.w "h") (t4.w "ins") := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hvne hr _
      have hne : (v : ℕ) ≠ (s : ℕ) := fun hh => hvne (Fin.ext (hh.trans hP4.symm))
      have h0 : t4.wa "reach" (v : ℕ) = 0 := by rw [hReach4 (v : ℕ)]; simp [hne]
      exact absurd hr (by rw [h0]; simp)
    · intro i hi
      exact absurd hi (by rw [hH4]; omega)
    · intro i hi
      exact absurd hi (by rw [hH4]; omega)
  have hheap4 : HeapOK (hvD s t4) (fun i => t4.va "hd" i) (t4.w "h") := by
    intro i hi
    exact absurd hi (by rw [hH4]; omega)
  have hval4 : HeapV (G := G) t4 (t4.w "h") := by
    intro i hi
    exact absurd hi (by rw [hH4]; omega)
  have hreachv4 : t4.wa "reach" (t4.w "pv") ≠ 0 := by
    rw [hP4, hReach4 (s : ℕ)]
    simp
  -- the source push
  refine runs_seq ((pushBody_runs (st := t4) hF4 hAF4 hpv4 hsoft4 hheap4 hval4 hreachv4
    (by rw [hH4]; omega) (by rw [hI4]; omega)).mono ?_)
  rintro t5 ⟨hF5, hAF5, hSoft5, hHeap5, hH5, hI5, hVal5, hFrame5, hCost5⟩
  -- facts at the post-push state
  have hDist5 : ∀ j, t5.va "dist" j = 0 := fun j => (hFrame5.dist j).trans (hDist4 j)
  have hDone5 : ∀ j, t5.wa "done" j = 0 := fun j => (hFrame5.done j).trans (hDone4 j)
  have hReach5 : ∀ j, t5.wa "reach" j = if j = (s : ℕ) then 1 else 0 :=
    fun j => (hFrame5.reach j).trans (hReach4 j)
  have hcw5 : ChainWF G t5 := by
    intro u _
    have hhead : t5.wa "head" u = sb.wa "head" u := by
      rw [hFrame5.head u, ht4, ht3, ht2, ht1]; rfl
    have hnxt : ∀ j, t5.wa "nxt" j = sb.wa "nxt" j := by
      intro j; rw [hFrame5.nxt j, ht4, ht3, ht2, ht1]; rfl
    rw [show chainOf t5 u (G.m + 1) = chainOf sb u (G.m + 1) from by
      simp only [chainOf]
      rw [hhead]
      exact chainWalk_congr (fun j _ => hnxt j)]
    exact hChainb u
  have hse5 : SettledExact G s t5 := by
    intro v hd0
    exact absurd hd0 (by rw [hDone5 (v : ℕ)]; simp)
  have hRoom5 : RoomSt G t5 = 0 := by
    rw [RoomSt]
    refine Finset.sum_eq_zero (fun v _ => ?_)
    rw [if_neg (by rw [hDone5 (v : ℕ)]; simp)]
  have hmu5 : mu G t5 = 2 * G.m + 3 := by
    simp only [mu, hRoom5, hH5, hH4]
    omega
  -- the model invariant at the post-push state
  have hInv5 : Inv G s (fun v => t5.va "dist" v) (fun v => t5.wa "reach" v)
      (fun v => t5.wa "done" v) (hvD s t5) (fun i => t5.va "hd" i) (t5.w "h") (t5.w "ins") := by
    refine ⟨?_, ?_, hHeap5, hSoft5.entry_cur, hSoft5.entry_mono, hSoft5.entry_reach, ?_, ?_⟩
    · intro v hr
      have hvs : (v : ℕ) = (s : ℕ) := by
        by_contra hne
        have h0 : t5.wa "reach" (v : ℕ) = 0 := by rw [hReach5 (v : ℕ)]; simp [hne]
        exact hr h0
      have hv : v = s := Fin.ext hvs
      rw [hv]
      exact ⟨[], Graph.IsWalk.nil s, by simp [Graph.len, hDist5 (s : ℕ)]⟩
    · intro e hd0
      exact absurd hd0 (by rw [hDone5 (G.src e)]; simp)
    · exact ⟨hDist5 (s : ℕ), by rw [hReach5 (s : ℕ)]; simp⟩
    · intro u hu
      exact absurd hu (by rw [hDone5 (u : ℕ)]; simp)
  have hRoom5' : t5.w "h" + (G.m - RoomSt G t5) ≤ G.m + 1 := by
    rw [hH5, hRoom5, hH4]; omega
  have hIns5' : t5.w "ins" + (G.m - RoomSt G t5) ≤ G.m + 1 := by
    rw [hI5, hRoom5]; omega
  have hLI5 : LoopInv G s t5.cost (2 * G.m + 3) (Kc G) t5 :=
    { inv := hInv5
      se := hse5
      val := hVal5
      cw := hcw5
      f0 := hF5
      af := hAF5
      room := hRoom5'
      insroom := hIns5'
      mub := by rw [hmu5]
      costb := by rw [hmu5]; omega }
  -- the per-iteration constants
  have hKpop : ∀ h : ℕ, h ≤ G.m + 1 → 18 * rkD h 0 + 30 ≤ Kc G := by
    intro h hh
    have hmono : rkD h 0 ≤ rkD (G.m + 1) 0 := by
      rw [rkD_zero, rkD_zero]
      exact Nat.log_mono_right hh
    simp only [Kc]
    omega
  have hKs : 12 * rk (G.m + 1) + 30 ≤ Kc G := by
    simp only [Kc]
    omega
  -- the main loop
  refine (mainLoop_runs (st := t5) (c0 := t5.cost) (μ0 := 2 * G.m + 3) (K := Kc G)
    hKpop hKs hLI5).mono ?_
  rintro t6 ⟨hInv6, hH6, hCost6, hAF6, hF6⟩
  refine ⟨hF6, hAF6, hInv6, hH6, ?_⟩
  rw [hH4] at hCost5
  omega

end Submission.DijkstraMain
