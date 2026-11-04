import Frontier.RAMLogic
import Frontier.RAMWitness
import Submission.DijkstraProg
import Submission.DijkstraModel

/-!
# Submission.DijkstraSim — `Runs` proofs for the row program

Simulation of `Submission.DijkstraProg.p1` against the
`Submission.DijkstraModel.Inv` invariant, RAMWitness idiom.  Components:
`calcPa` (halving loop), `buildAdj` (linked-list build), heap ops (`siftUp`,
`siftDown`, `pushBody`, `popBody`), `scanBody` / `relaxBody` (out-edge chain),
`settleBody`, `mainLoop`, then dispatch assembly with the verified `bfProgram`.
-/

namespace Submission.DijkstraSim

open scoped ENNReal NNReal
open Frontier Frontier.RAM WExpr Stmt
open Submission.DijkstraProg Submission.DijkstraModel

variable {G : Graph} {s : Fin G.n}

/-! ## State normalization -/

/-- AC normal form for state record updates. -/
macro "st_simp" : tactic =>
  `(tactic| simp [State.charge, State.setW, State.setV, State.storeW, State.storeV,
      State.allocW, State.allocV, State.enter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])

/-! ## Input frame -/

/-- Input frame: registers `n m s`, arrays `src dst w` as initialised, cap ≥ `n + m + 2`. -/
structure F0 (G : Graph) (s : Fin G.n) (st : State ℝ≥0) : Prop where
  hn : st.w "n" = G.n
  hm : st.w "m" = G.m
  hs : st.w "s" = (s : ℕ)
  hcap : G.n + G.m + 2 ≤ st.cap
  hsrc : ∀ (j : ℕ) (hj : j < G.m), st.wa "src" j = (G.src ⟨j, hj⟩ : ℕ)
  hdst : ∀ (j : ℕ) (hj : j < G.m), st.wa "dst" j = (G.dst ⟨j, hj⟩ : ℕ)
  hw : ∀ (j : ℕ) (hj : j < G.m), st.va "w" j = G.w ⟨j, hj⟩
  hsrcL : st.wlen "src" = G.m
  hdstL : st.wlen "dst" = G.m
  hwL : st.vlen "w" = G.m

attribute [local simp] State.setW State.setV State.storeW State.storeV
  State.allocW State.allocV State.charge

theorem F0.setW {st : State ℝ≥0} (h : F0 G s st) {x : String}
    (hx : x ≠ "n" ∧ x ≠ "m" ∧ x ≠ "s") (a : ℕ) : F0 G s (st.setW x a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨?_, ?_, ?_, h4, h5, h6, h7, h8, h9, h10⟩
  · show (if "n" = x then a else st.w "n") = G.n
    rw [if_neg (Ne.symm hx.1)]; exact h1
  · show (if "m" = x then a else st.w "m") = G.m
    rw [if_neg (Ne.symm hx.2.1)]; exact h2
  · show (if "s" = x then a else st.w "s") = (s : ℕ)
    rw [if_neg (Ne.symm hx.2.2)]; exact h3

theorem F0.preserve {st : State ℝ≥0} (h : F0 G s st) {st' : State ℝ≥0}
    (hn : st'.w "n" = st.w "n") (hm : st'.w "m" = st.w "m") (hs : st'.w "s" = st.w "s")
    (hcap : st.cap = st'.cap)
    (hsrc : ∀ (j : ℕ), j < G.m → st'.wa "src" j = st.wa "src" j)
    (hdst : ∀ (j : ℕ), j < G.m → st'.wa "dst" j = st.wa "dst" j)
    (hw : ∀ (j : ℕ), j < G.m → st'.va "w" j = st.va "w" j)
    (hsrcL : st'.wlen "src" = st.wlen "src") (hdstL : st'.wlen "dst" = st.wlen "dst")
    (hwL : st'.vlen "w" = st.vlen "w") : F0 G s st' := by
  obtain ⟨a, b, c, d, e, f, g, i, j, l⟩ := h
  refine ⟨hn.trans a, hm.trans b, hs.trans c, ?_, ?_, ?_, ?_, hsrcL.trans i, hdstL.trans j,
    hwL.trans l⟩
  · rw [← hcap]; exact d
  · intro jj hj; rw [hsrc jj hj]; exact e jj hj
  · intro jj hj; rw [hdst jj hj]; exact f jj hj
  · intro jj hj; rw [hw jj hj]; exact g jj hj

theorem F0.charge {st : State ℝ≥0} (h : F0 G s st) (k : ℕ) : F0 G s (st.charge k) :=
  F0.preserve h rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl rfl

theorem F0.init_state (P : Program) (s : Fin G.n) : F0 G s (initState P G s) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · calc G.n + G.m + 2 = (G.n + G.m + 2) ^ 1 := (pow_one _).symm
      _ ≤ (G.n + G.m + 2) ^ (P.wordExp + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  · intro j hj; simp [Frontier.RAM.initState, hj]
  · intro j hj; simp [Frontier.RAM.initState, hj]
  · intro j hj; simp [Frontier.RAM.initState, hj]

/-! ## Dijkstra array frame -/

/-- Allocation facts for the Dijkstra arrays. -/
structure AF (G : Graph) (st : State ℝ≥0) : Prop where
  distL : st.vlen "dist" = G.n
  reachL : st.wlen "reach" = G.n
  doneL : st.wlen "done" = G.n
  headL : st.wlen "head" = G.n
  nxtL : st.wlen "nxt" = G.m
  hvL : st.wlen "hv" = G.m + 1
  hdL : st.vlen "hd" = G.m + 1

theorem AF.preserve {st st' : State ℝ≥0} (h : AF G st)
    (h1 : st'.vlen "dist" = st.vlen "dist") (h2 : st'.wlen "reach" = st.wlen "reach")
    (h3 : st'.wlen "done" = st.wlen "done") (h4 : st'.wlen "head" = st.wlen "head")
    (h5 : st'.wlen "nxt" = st.wlen "nxt") (h6 : st'.wlen "hv" = st.wlen "hv")
    (h7 : st'.vlen "hd" = st.vlen "hd") : AF G st' := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨h1.trans a, h2.trans b, h3.trans c, h4.trans d, h5.trans e, h6.trans f, h7.trans g⟩

theorem AF.charge {st : State ℝ≥0} (h : AF G st) (k : ℕ) : AF G (st.charge k) :=
  AF.preserve h rfl rfl rfl rfl rfl rfl rfl

theorem AF.setW {st : State ℝ≥0} (h : AF G st) {x : String} (a : ℕ) : AF G (st.setW x a) :=
  AF.preserve h rfl rfl rfl rfl rfl rfl rfl

theorem AF.setV {st : State ℝ≥0} (h : AF G st) {x : String} (a : ℝ≥0) : AF G (st.setV x a) :=
  AF.preserve h rfl rfl rfl rfl rfl rfl rfl

theorem AF.storeW {st : State ℝ≥0} (h : AF G st) (arr : String) (j a : ℕ) :
    AF G (st.storeW arr j a) :=
  AF.preserve h rfl rfl rfl rfl rfl rfl rfl

theorem AF.storeV {st : State ℝ≥0} (h : AF G st) (arr : String) (j : ℕ) (a : ℝ≥0) :
    AF G (st.storeV arr j a) :=
  AF.preserve h rfl rfl rfl rfl rfl rfl rfl

/-! ## Eval helpers (RAMLogic combinators plus `sub`/`div`/`mul`) -/

theorem evalW_sub_of {st : State ℝ≥0} {a b : WExpr} {x y : ℕ} (ha : evalW st a = some x)
    (hb : evalW st b = some y) : evalW st (.sub a b) = some (x - y) := by
  simp [evalW, ha, hb]

theorem evalW_div_of {st : State ℝ≥0} {a b : WExpr} {x y : ℕ} (ha : evalW st a = some x)
    (hb : evalW st b = some y) (hy : y ≠ 0) : evalW st (.div a b) = some (x / y) := by
  simp [evalW, ha, hb, hy]

theorem evalW_mul_of {st : State ℝ≥0} {a b : WExpr} {x y : ℕ} (ha : evalW st a = some x)
    (hb : evalW st b = some y) (hc : x * y < st.cap) : evalW st (.mul a b) = some (x * y) := by
  simp [evalW, ha, hb, fit, hc]

/-! ## `calcPa`: `pa := ⌊log₂ n⌋` by halving -/

/-- `calcPa` runs and leaves `pa = ⌊log₂ G.n⌋`. -/
theorem calcPa_runs (st : State ℝ≥0) (hF : F0 G s st) :
    Runs realOps calcPa st (fun st' =>
      F0 G s st' ∧ st'.w "pa" = Nat.log 2 G.n ∧
      st'.cost ≤ st.cost + 4 * (Nat.log 2 G.n + 1) + 2) := by
  have hnpos : 0 < G.n := lt_of_le_of_lt (Nat.zero_le _) s.isLt
  have hcap0 : 0 < st.cap := by have := hF.hcap; omega
  have h0 : evalW st (var "n") = some G.n := by rw [evalW_var, hF.hn]
  have h1 : evalW st (lit 0) = some 0 := evalW_lit_of hcap0
  refine runs_seq (runs_wset h0 ?_)
  refine runs_seq (runs_wset h1 ?_)
  have h2F : F0 G s (((st.setW "t" G.n).charge 1).setW "pa" 0 |>.charge 1) :=
    (((hF.setW (x := "t") (a := G.n) (by simp)).charge 1).setW (x := "pa") (a := 0)
      (by simp)).charge 1
  have h2c : (((st.setW "t" G.n).charge 1).setW "pa" 0 |>.charge 1).cost = st.cost + 2 := by
    simp
  have h2t : ((((st.setW "t" G.n).charge 1).setW "pa" 0 |>.charge 1)).w "t" = G.n := by simp
  have h2pa : ((((st.setW "t" G.n).charge 1).setW "pa" 0 |>.charge 1)).w "pa" = 0 := by simp
  refine runs_while_nat (I := fun q st' => F0 G s st' ∧ st'.w "t" = q ∧
      q = G.n / 2 ^ (st'.w "pa") ∧ st'.w "pa" ≤ Nat.log 2 G.n ∧
      st'.cost ≤ st.cost + 2 + 4 * st'.w "pa")
    (Q := fun st' => F0 G s st' ∧ st'.w "pa" = Nat.log 2 G.n ∧
      st'.cost ≤ st.cost + 4 * (Nat.log 2 G.n + 1) + 2) ?_ G.n _
    ⟨h2F, h2t, ?_, ?_, ?_⟩
  · -- step
    intro q st' ⟨hF', ht, hrel, hple, hc⟩
    have hcap' : 1 < st'.cap := by have := hF'.hcap; omega
    have hcond : evalW st' (lt (lit 1) (var "t")) = some (if 1 < q then 1 else 0) :=
      evalW_lt_of (x := 1) (y := q) (evalW_lit_of hcap')
        (by rw [evalW_var, ht]) hcap'
    by_cases hq : 1 < q
    · refine ⟨1, ?_, fun _ => ?_, fun hz => (one_ne_zero hz).elim⟩
      · rw [hcond, if_pos hq]
      · have hc2 : 2 < st'.cap := by have := hF'.hcap; omega
        have hdiv : evalW (st'.charge 1) (.div (var "t") (lit 2)) = some (q / 2) := by
          rw [evalW_charge]
          exact evalW_div_of (by rw [evalW_var, ht]) (evalW_lit_of hc2) (by norm_num)
        refine runs_seq (runs_wset hdiv ?_)
        have hadd : evalW ((st'.charge 1).setW "t" (q / 2) |>.charge 1)
            (add (var "pa") (lit 1)) = some (st'.w "pa" + 1) := by
          have hpaE : evalW ((st'.charge 1).setW "t" (q / 2) |>.charge 1) (var "pa")
              = some (st'.w "pa") := by
            rw [evalW_charge]; simp
          have h1E : evalW ((st'.charge 1).setW "t" (q / 2) |>.charge 1) (lit 1) = some 1 := by
            apply evalW_lit_of
            simp
            exact hcap'
          have hsum : st'.w "pa" + 1 < ((st'.charge 1).setW "t" (q / 2) |>.charge 1).cap := by
            simp
            have hlog : Nat.log 2 G.n ≤ G.n := Nat.log_le_self 2 G.n
            have := hF'.hcap; omega
          exact evalW_add_of hpaE h1E hsum
        refine runs_wset hadd ?_
        refine ⟨q / 2, Nat.div_lt_self (by omega : 0 < q) (by norm_num : 1 < 2), ?_⟩
        refine ⟨(((((hF'.charge 1).setW (x := "t") (a := q / 2) (by simp)).charge 1).setW (x := "pa")
          (a := st'.w "pa" + 1) (by simp)).charge 1), ?_, ?_, ?_, ?_⟩
        · simp
        · have hpae : ((((((st'.charge 1).setW "t" (q / 2)).charge 1).setW "pa"
              (st'.w "pa" + 1)).charge 1)).w "pa" = st'.w "pa" + 1 := by simp
          rw [hpae, hrel, Nat.div_div_eq_div_mul, Nat.pow_succ]
        · have h2 : 2 ^ (st'.w "pa" + 1) ≤ G.n := by
            have h2q : 2 ≤ q := by omega
            have hm : 2 * 2 ^ (st'.w "pa") ≤ G.n := by
              have hdiv2 : 2 ≤ G.n / 2 ^ (st'.w "pa") := by rw [← hrel]; exact h2q
              exact (Nat.le_div_iff_mul_le (by positivity)).mp hdiv2
            rw [Nat.pow_succ, Nat.mul_comm]; exact hm
          simp
          exact Nat.le_log_of_pow_le (by norm_num) h2
        · simp
          omega
    · refine ⟨0, ?_, fun hz => (hz rfl).elim, fun _ => ?_⟩
      · rw [hcond, if_neg hq]
      · have hple' : Nat.log 2 G.n ≤ st'.w "pa" := by
          by_contra h
          have hlt : st'.w "pa" < Nat.log 2 G.n := Nat.not_le.mp h
          have h2 : 2 ^ Nat.log 2 G.n ≤ G.n := Nat.pow_log_le_self 2 (by omega)
          have hpow : 2 ^ (st'.w "pa" + 1) ≤ G.n :=
            (Nat.pow_le_pow_right (by norm_num) (show st'.w "pa" + 1 ≤ Nat.log 2 G.n by
              omega)).trans h2
          have h2q : 2 ≤ q := by
            rw [hrel, Nat.le_div_iff_mul_le (by positivity)]
            have h3 : 2 ^ (st'.w "pa") * 2 ≤ G.n := by
              rw [Nat.pow_succ] at hpow; exact hpow
            rw [Nat.mul_comm]; exact h3
          omega
        refine ⟨hF'.charge 1, ?_, ?_⟩
        · simp
          omega
        · have := hF'.hcap; simp at hc ⊢; omega
  · rw [h2pa, Nat.pow_zero, Nat.div_one]
  · rw [h2pa]; exact Nat.zero_le _
  · simp

end Submission.DijkstraSim
