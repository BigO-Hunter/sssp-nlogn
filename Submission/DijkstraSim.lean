import Frontier.RAMLogic
import Frontier.RAMWitness
import Submission.DijkstraProg
import Submission.DijkstraModel
import Submission.DijkstraDecode

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
open Submission.DijkstraProg Submission.DijkstraModel Submission.DijkstraDecode

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

/-! ## Record calculus (definitional equations; avoids simp blowup on record chains) -/

theorem w_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) (x : String) :
    (st.allocW arr k).w x = st.w x := rfl
theorem w_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) (x : String) :
    (st.allocV arr k z).w x = st.w x := rfl
theorem w_charge (st : State ℝ≥0) (k : ℕ) (x : String) : (st.charge k).w x = st.w x := rfl
theorem w_setW (st : State ℝ≥0) (x y : String) (a : ℕ) :
    (st.setW x a).w y = if y = x then a else st.w y := rfl
theorem cap_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) : (st.allocW arr k).cap = st.cap := rfl
theorem cap_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) :
    (st.allocV arr k z).cap = st.cap := rfl
theorem cap_charge (st : State ℝ≥0) (k : ℕ) : (st.charge k).cap = st.cap := rfl
theorem cap_setW (st : State ℝ≥0) (x : String) (a : ℕ) : (st.setW x a).cap = st.cap := rfl
theorem wlen_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) (x : String) :
    (st.allocW arr k).wlen x = if x = arr then k else st.wlen x := rfl
theorem wlen_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) (x : String) :
    (st.allocV arr k z).wlen x = st.wlen x := rfl
theorem wlen_charge (st : State ℝ≥0) (k : ℕ) (x : String) : (st.charge k).wlen x = st.wlen x := rfl
theorem vlen_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) (x : String) :
    (st.allocV arr k z).vlen x = if x = arr then k else st.vlen x := rfl
theorem vlen_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) (x : String) :
    (st.allocW arr k).vlen x = st.vlen x := rfl
theorem vlen_charge (st : State ℝ≥0) (k : ℕ) (x : String) : (st.charge k).vlen x = st.vlen x := rfl
theorem wa_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) (x : String) (j : ℕ) :
    (st.allocW arr k).wa x j = if x = arr then 0 else st.wa x j := rfl
theorem wa_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) (x : String) (j : ℕ) :
    (st.allocV arr k z).wa x j = st.wa x j := rfl
theorem wa_charge (st : State ℝ≥0) (k : ℕ) (x : String) (j : ℕ) :
    (st.charge k).wa x j = st.wa x j := rfl
theorem va_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) (x : String) (j : ℕ) :
    (st.allocW arr k).va x j = st.va x j := rfl
theorem va_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) (x : String) (j : ℕ) :
    (st.allocV arr k z).va x j = if x = arr then z else st.va x j := rfl
theorem va_charge (st : State ℝ≥0) (k : ℕ) (x : String) (j : ℕ) :
    (st.charge k).va x j = st.va x j := rfl
theorem w_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) (x : String) :
    (st.storeW arr j a).w x = st.w x := rfl
theorem w_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) (x : String) :
    (st.storeV arr j z).w x = st.w x := rfl
theorem wa_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) (x : String) (i : ℕ) :
    (st.storeW arr j a).wa x i = if x = arr ∧ i = j then a else st.wa x i := rfl
theorem wa_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) (x : String) (i : ℕ) :
    (st.storeV arr j z).wa x i = st.wa x i := rfl
theorem va_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) (x : String) (i : ℕ) :
    (st.storeW arr j a).va x i = st.va x i := rfl
theorem va_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) (x : String) (i : ℕ) :
    (st.storeV arr j z).va x i = if x = arr ∧ i = j then z else st.va x i := rfl
theorem wlen_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) (x : String) :
    (st.storeW arr j a).wlen x = st.wlen x := rfl
theorem wlen_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) (x : String) :
    (st.storeV arr j z).wlen x = st.wlen x := rfl
theorem vlen_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) (x : String) :
    (st.storeW arr j a).vlen x = st.vlen x := rfl
theorem vlen_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) (x : String) :
    (st.storeV arr j z).vlen x = st.vlen x := rfl
theorem cap_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) : (st.storeW arr j a).cap = st.cap := rfl
theorem cost_storeW (st : State ℝ≥0) (arr : String) (j a : ℕ) : (st.storeW arr j a).cost = st.cost := rfl
theorem cost_storeV (st : State ℝ≥0) (arr : String) (j : ℕ) (z : ℝ≥0) :
    (st.storeV arr j z).cost = st.cost := rfl

theorem F0.storeW {st : State ℝ≥0} (h : F0 G s st) {arr : String} (j a : ℕ)
    (har : arr ≠ "src" ∧ arr ≠ "dst") : F0 G s (st.storeW arr j a) := by
  refine F0.preserve h rfl rfl rfl rfl ?_ ?_ (fun _ _ => rfl) rfl rfl rfl
  · intro jj _; rw [wa_storeW]; exact if_neg (fun hh => har.1 hh.1.symm)
  · intro jj _; rw [wa_storeW]; exact if_neg (fun hh => har.2 hh.1.symm)
theorem w_setW_of_ne (st : State ℝ≥0) (x y : String) (a : ℕ) (h : y ≠ x) :
    (st.setW x a).w y = st.w y := by rw [w_setW]; exact if_neg h
theorem cost_setW (st : State ℝ≥0) (x : String) (a : ℕ) : (st.setW x a).cost = st.cost := rfl
theorem wa_setW (st : State ℝ≥0) (x : String) (a : ℕ) (arr : String) (j : ℕ) :
    (st.setW x a).wa arr j = st.wa arr j := rfl
theorem va_setW (st : State ℝ≥0) (x : String) (a : ℕ) (arr : String) (j : ℕ) :
    (st.setW x a).va arr j = st.va arr j := rfl
theorem wlen_setW (st : State ℝ≥0) (x : String) (a : ℕ) (arr : String) :
    (st.setW x a).wlen arr = st.wlen arr := rfl
theorem vlen_setW (st : State ℝ≥0) (x : String) (a : ℕ) (arr : String) :
    (st.setW x a).vlen arr = st.vlen arr := rfl
theorem cost_charge (st : State ℝ≥0) (k : ℕ) : (st.charge k).cost = st.cost + k := rfl
theorem cost_allocW (st : State ℝ≥0) (arr : String) (k : ℕ) : (st.allocW arr k).cost = st.cost := rfl
theorem cost_allocV (st : State ℝ≥0) (arr : String) (k : ℕ) (z : ℝ≥0) :
    (st.allocV arr k z).cost = st.cost := rfl

/-- Charging a state does not change its decoded chains. -/
theorem chainOf_charge (st : State ℝ≥0) (k : ℕ) (u : ℕ) :
    chainOf (st.charge k) u (G.m + 1) = chainOf st u (G.m + 1) := by
  simp only [chainOf, wa_charge]
  apply chainWalk_congr
  intro j _
  exact wa_charge _ _ _ _

/-! ## `allocAll`: the six arrays -/

/-- `allocAll` runs and establishes the array-frame `AF` with every fresh array zero-filled
(the five flag arrays `reach done hv` / `hd` by `allocW`/`allocV`, and `dist` by `allocV`). -/
theorem allocAll_runs (st : State ℝ≥0) (hF : F0 G s st) :
    Runs realOps allocAll st (fun st' =>
      F0 G s st' ∧ AF G st' ∧ (∀ j, st'.wa "head" j = 0) ∧
      (∀ j, st'.va "dist" j = 0) ∧ (∀ j, st'.wa "reach" j = 0) ∧
      (∀ j, st'.wa "done" j = 0) ∧ (∀ j, st'.wa "hv" j = 0) ∧
      (∀ j, st'.va "hd" j = 0) ∧
      st'.cost ≤ st.cost + 4 * G.n + 3 * G.m + 9) := by
  have hcap : G.n + G.m + 2 ≤ st.cap := hF.hcap
  have hnE : evalW st (var "n") = some G.n := by rw [evalW_var, hF.hn]
  have hmE : evalW st (var "m") = some G.m := by rw [evalW_var, hF.hm]
  refine runs_seq (runs_valloc (k := G.n) hnE ?_)
  set st1 := (st.allocV "dist" G.n realOps.zero).charge (G.n + 1) with hst1
  refine runs_seq (runs_walloc (k := G.n)
    (by rw [evalW_var, hst1, w_charge, w_allocV, hF.hn]) ?_)
  set st2 := (st1.allocW "reach" G.n).charge (G.n + 1) with hst2
  refine runs_seq (runs_walloc (k := G.n)
    (by rw [evalW_var, hst2, w_charge, w_allocW, hst1, w_charge, w_allocV, hF.hn]) ?_)
  set st3 := (st2.allocW "done" G.n).charge (G.n + 1) with hst3
  refine runs_seq (runs_walloc (k := G.n)
    (by rw [evalW_var, hst3, w_charge, w_allocW, hst2, w_charge, w_allocW, hst1, w_charge,
      w_allocV, hF.hn]) ?_)
  set st4 := (st3.allocW "head" G.n).charge (G.n + 1) with hst4
  refine runs_seq (runs_walloc (k := G.m)
    (by rw [evalW_var, hst4, w_charge, w_allocW, hst3, w_charge, w_allocW, hst2, w_charge,
      w_allocW, hst1, w_charge, w_allocV, hF.hm]) ?_)
  set st5 := (st4.allocW "nxt" G.m).charge (G.m + 1) with hst5
  have hvar5 : evalW st5 (var "m") = some G.m := by
    rw [evalW_var, hst5, w_charge, w_allocW, hst4, w_charge, w_allocW, hst3, w_charge, w_allocW,
      hst2, w_charge, w_allocW, hst1, w_charge, w_allocV, hF.hm]
  have hcap5 : G.n + G.m + 2 ≤ st5.cap := by
    rw [hst5, cap_charge, cap_allocW, hst4, cap_charge, cap_allocW, hst3, cap_charge, cap_allocW,
      hst2, cap_charge, cap_allocW, hst1, cap_charge, cap_allocV]
    exact hcap
  have hm1E5 : evalW st5 (add (var "m") (lit 1)) = some (G.m + 1) :=
    evalW_add_of hvar5 (evalW_lit_of (by have := hcap5; omega)) (by have := hcap5; omega)
  refine runs_seq (runs_walloc (k := G.m + 1) hm1E5 ?_)
  set st6 := (st5.allocW "hv" (G.m + 1)).charge (G.m + 2) with hst6
  have hvar6 : evalW st6 (var "m") = some G.m := by
    rw [evalW_var, hst6, w_charge, w_allocW]; exact hvar5
  have hcap6 : G.n + G.m + 2 ≤ st6.cap := by
    rw [hst6, cap_charge, cap_allocW]; exact hcap5
  have hm1E6 : evalW st6 (add (var "m") (lit 1)) = some (G.m + 1) :=
    evalW_add_of hvar6 (evalW_lit_of (by have := hcap6; omega)) (by have := hcap6; omega)
  refine runs_valloc (k := G.m + 1) hm1E6 ?_
  set st7 := (st6.allocV "hd" (G.m + 1) realOps.zero).charge (G.m + 2) with hst7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- F0: input registers and arrays untouched
    refine F0.preserve hF ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hst7, w_charge, w_allocV, hst6, w_charge, w_allocW, hst5, w_charge, w_allocW,
        hst4, w_charge, w_allocW, hst3, w_charge, w_allocW, hst2, w_charge, w_allocW,
        hst1, w_charge, w_allocV]
    · rw [hst7, w_charge, w_allocV, hst6, w_charge, w_allocW, hst5, w_charge, w_allocW,
        hst4, w_charge, w_allocW, hst3, w_charge, w_allocW, hst2, w_charge, w_allocW,
        hst1, w_charge, w_allocV]
    · rw [hst7, w_charge, w_allocV, hst6, w_charge, w_allocW, hst5, w_charge, w_allocW,
        hst4, w_charge, w_allocW, hst3, w_charge, w_allocW, hst2, w_charge, w_allocW,
        hst1, w_charge, w_allocV]
    · rw [hst7, cap_charge, cap_allocV, hst6, cap_charge, cap_allocW, hst5, cap_charge,
        cap_allocW, hst4, cap_charge, cap_allocW, hst3, cap_charge, cap_allocW, hst2,
        cap_charge, cap_allocW, hst1, cap_charge, cap_allocV]
    · intro j _; rw [hst7, wa_charge, wa_allocV, hst6, wa_charge, wa_allocW,
        if_neg (by decide : ("src" : String) ≠ "hv"), hst5, wa_charge, wa_allocW,
        if_neg (by decide), hst4, wa_charge, wa_allocW, if_neg (by decide), hst3, wa_charge,
        wa_allocW, if_neg (by decide), hst2, wa_charge, wa_allocW, if_neg (by decide),
        hst1, wa_charge, wa_allocV]
    · intro j _; rw [hst7, wa_charge, wa_allocV, hst6, wa_charge, wa_allocW,
        if_neg (by decide : ("dst" : String) ≠ "hv"), hst5, wa_charge, wa_allocW,
        if_neg (by decide), hst4, wa_charge, wa_allocW, if_neg (by decide), hst3, wa_charge,
        wa_allocW, if_neg (by decide), hst2, wa_charge, wa_allocW, if_neg (by decide),
        hst1, wa_charge, wa_allocV]
    · intro j _; rw [hst7, va_charge, va_allocV,
        if_neg (by decide : ("w" : String) ≠ "hd"), hst6, va_charge, va_allocW, hst5,
        va_charge, va_allocW, hst4, va_charge, va_allocW, hst3, va_charge, va_allocW,
        hst2, va_charge, va_allocW, hst1, va_charge, va_allocV, if_neg (by decide)]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW, if_neg (by decide),
        hst5, wlen_charge, wlen_allocW, if_neg (by decide), hst4, wlen_charge, wlen_allocW,
        if_neg (by decide), hst3, wlen_charge, wlen_allocW, if_neg (by decide), hst2,
        wlen_charge, wlen_allocW, if_neg (by decide), hst1, wlen_charge, wlen_allocV]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW, if_neg (by decide),
        hst5, wlen_charge, wlen_allocW, if_neg (by decide), hst4, wlen_charge, wlen_allocW,
        if_neg (by decide), hst3, wlen_charge, wlen_allocW, if_neg (by decide), hst2,
        wlen_charge, wlen_allocW, if_neg (by decide), hst1, wlen_charge, wlen_allocV]
    · rw [hst7, vlen_charge, vlen_allocV, if_neg (by decide : ("w" : String) ≠ "hd"),
        hst6, vlen_charge, vlen_allocW, hst5, vlen_charge, vlen_allocW, hst4, vlen_charge,
        vlen_allocW, hst3, vlen_charge, vlen_allocW, hst2, vlen_charge, vlen_allocW,
        hst1, vlen_charge, vlen_allocV, if_neg (by decide)]
  · -- AF lengths
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hst7, vlen_charge, vlen_allocV, if_neg (by decide : ("dist" : String) ≠ "hd"),
        hst6, vlen_charge, vlen_allocW, hst5, vlen_charge, vlen_allocW, hst4, vlen_charge,
        vlen_allocW, hst3, vlen_charge, vlen_allocW, hst2, vlen_charge, vlen_allocW,
        hst1, vlen_charge, vlen_allocV, if_pos rfl]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW,
        if_neg (by decide : ("reach" : String) ≠ "hv"), hst5, wlen_charge, wlen_allocW,
        if_neg (by decide), hst4, wlen_charge, wlen_allocW, if_neg (by decide),
        hst3, wlen_charge, wlen_allocW, if_neg (by decide), hst2, wlen_charge, wlen_allocW,
        if_pos rfl]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW, if_neg (by decide),
        hst5, wlen_charge, wlen_allocW, if_neg (by decide), hst4, wlen_charge, wlen_allocW,
        if_neg (by decide), hst3, wlen_charge, wlen_allocW, if_pos rfl]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW, if_neg (by decide),
        hst5, wlen_charge, wlen_allocW, if_neg (by decide), hst4, wlen_charge, wlen_allocW,
        if_pos rfl]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW, if_neg (by decide),
        hst5, wlen_charge, wlen_allocW, if_pos rfl]
    · rw [hst7, wlen_charge, wlen_allocV, hst6, wlen_charge, wlen_allocW, if_pos rfl]
    · rw [hst7, vlen_charge, vlen_allocV, if_pos rfl]
  · intro j
    rw [hst7, wa_charge, wa_allocV, hst6, wa_charge, wa_allocW,
      if_neg (by decide : ("head" : String) ≠ "hv"), hst5, wa_charge, wa_allocW,
      if_neg (by decide), hst4, wa_charge, wa_allocW, if_pos rfl]
  · -- `dist` is zero-filled by the `allocV`
    intro j
    rw [hst7, va_charge, va_allocV, if_neg (by decide : ("dist" : String) ≠ "hd"),
      hst6, va_charge, va_allocW, hst5, va_charge, va_allocW, hst4, va_charge, va_allocW,
      hst3, va_charge, va_allocW, hst2, va_charge, va_allocW, hst1, va_charge, va_allocV,
      if_pos rfl]
    rfl
  · -- `reach` is zero-filled by its `allocW`
    intro j
    rw [hst7, wa_charge, wa_allocV, hst6, wa_charge, wa_allocW,
      if_neg (by decide : ("reach" : String) ≠ "hv"), hst5, wa_charge, wa_allocW,
      if_neg (by decide), hst4, wa_charge, wa_allocW, if_neg (by decide), hst3, wa_charge,
      wa_allocW, if_neg (by decide), hst2, wa_charge, wa_allocW, if_pos rfl]
  · -- `done` is zero-filled by its `allocW`
    intro j
    rw [hst7, wa_charge, wa_allocV, hst6, wa_charge, wa_allocW,
      if_neg (by decide : ("done" : String) ≠ "hv"), hst5, wa_charge, wa_allocW,
      if_neg (by decide), hst4, wa_charge, wa_allocW, if_neg (by decide), hst3, wa_charge,
      wa_allocW, if_pos rfl]
  · -- `hv` is zero-filled by its `allocW`
    intro j
    rw [hst7, wa_charge, wa_allocV, hst6, wa_charge, wa_allocW, if_pos rfl]
  · -- `hd` is zero-filled by the `allocV`
    intro j
    rw [hst7, va_charge, va_allocV, if_pos rfl]
    rfl
  · simp only [hst7, hst6, hst5, hst4, hst3, hst2, hst1, cost_charge, cost_allocW, cost_allocV]
    omega

/-! ## `buildAdj`: the adjacency lists -/

/-- `buildAdj` runs and builds the `head`/`nxt` chains: after the loop, the chain of `u`
is exactly the out-edges of `u` in decreasing order. -/
theorem buildAdj_runs (st : State ℝ≥0) (hF : F0 G s st) (hAF : AF G st)
    (hzero : ∀ u, st.wa "head" u = 0) :
    Runs realOps buildAdj st (fun st' =>
      F0 G s st' ∧ AF G st' ∧
      (∀ u, chainOf st' u (G.m + 1) = outChainK G G.m u) ∧
      st'.cost ≤ st.cost + 6 * G.m + 2) := by
  have hcap : G.n + G.m + 2 ≤ st.cap := hF.hcap
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by have := hcap; omega)) ?_)
  set st0 := (st.setW "e" 0).charge 1 with hst0
  refine runs_while (I := fun k st' => F0 G s st' ∧ AF G st' ∧ st'.w "e" = k ∧ k ≤ G.m ∧
      (∀ u, chainOf st' u (G.m + 1) = outChainK G k u) ∧
      st'.cost ≤ st.cost + 1 + 6 * k) G.m
    (fun st' => F0 G s st' ∧ AF G st' ∧
      (∀ u, chainOf st' u (G.m + 1) = outChainK G G.m u) ∧
      st'.cost ≤ st.cost + 6 * G.m + 2) ?_ ?_ st0 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- step
    intro k hk s' ⟨hF', hAF', he, hle, hchain, hc⟩
    have hcap' : G.n + G.m + 2 ≤ s'.cap := hF'.hcap
    have hcond : evalW s' (lt (var "e") (var "m")) = some 1 := by
      rw [evalW_lt_of (x := k) (y := G.m) (by rw [evalW_var, he]) (by rw [evalW_var, hF'.hm])
        (by have := hcap'; omega)]
      simp [hk]
    refine ⟨1, hcond, one_ne_zero, ?_⟩
    set t0 := s'.charge 1 with ht0
    set uu : ℕ := (G.src ⟨k, hk⟩ : ℕ)
    have huu : s'.wa "src" k = uu := hF'.hsrc k hk
    have huE : evalW t0 (load "src" (var "e")) = some uu := by
      have hiE : evalW t0 (var "e") = some k := by rw [ht0, evalW_charge, evalW_var, he]
      have hjE : k < t0.wlen "src" := by rw [ht0, wlen_charge, hF'.hsrcL]; exact hk
      have hwaE : t0.wa "src" k = uu := by rw [ht0, wa_charge, huu]
      rw [evalW_load_of hiE hjE, hwaE]
    refine runs_seq (runs_wset (a := uu) huE ?_)
    set t1 := (t0.setW "u" uu).charge 1 with ht1
    set q0 : ℕ := s'.wa "head" uu
    have hqE : evalW t1 (load "head" (var "u")) = some q0 := by
      have h1u : t1.w "u" = uu := by simp [ht1, ht0, State.setW, State.charge]
      have h1l : uu < t1.wlen "head" := by
        rw [ht1, wlen_charge, wlen_setW, ht0, wlen_charge, hAF'.headL]
        exact (G.src ⟨k, hk⟩).isLt
      have hiQ : evalW t1 (var "u") = some uu := by rw [evalW_var, h1u]
      have hwaQ : t1.wa "head" uu = q0 := by
        rw [ht1, wa_charge, wa_setW, ht0, wa_charge]
      rw [evalW_load_of hiQ h1l, hwaQ]
    refine runs_seq (runs_wset (a := q0) hqE ?_)
    set t2 := (t1.setW "q" q0).charge 1 with ht2
    have hnxtE : evalW t2 (var "e") = some k := by
      rw [evalW_var, ht2, w_charge, w_setW, if_neg (by decide : ("e" : String) ≠ "q"),
        ht1, w_charge, w_setW, if_neg (by decide), ht0, w_charge, he]
    have hqvE : evalW t2 (var "q") = some q0 := by
      rw [evalW_var, ht2, w_charge, w_setW, if_pos rfl]
    refine runs_seq (runs_wstore (arr := "nxt") hnxtE hqvE
      (by rw [ht2, wlen_charge, wlen_setW, ht1, wlen_charge, wlen_setW, ht0, wlen_charge,
        hAF'.nxtL]; exact hk) ?_)
    set t3 := (t2.storeW "nxt" k q0).charge 1 with ht3
    have hcap3 : G.n + G.m + 2 ≤ t3.cap := by
      rw [ht3, cap_charge, cap_storeW, ht2, cap_charge, cap_setW, ht1, cap_charge, cap_setW,
        ht0, cap_charge]; exact hcap'
    have huuE : evalW t3 (var "u") = some uu := by
      rw [evalW_var, ht3, w_charge, w_storeW, ht2, w_charge, w_setW,
        if_neg (by decide : ("u" : String) ≠ "q"), ht1, w_charge, w_setW, if_pos rfl]
    have haddE : evalW t3 (add (var "e") (lit 1)) = some (k + 1) := by
      apply evalW_add_of
      · rw [evalW_var, ht3, w_charge, w_storeW, ht2, w_charge, w_setW,
          if_neg (by decide : ("e" : String) ≠ "q"), ht1, w_charge, w_setW,
          if_neg (by decide), ht0, w_charge, he]
      · exact evalW_lit_of (by have := hcap3; omega)
      · have := hcap3; omega
    refine runs_seq (runs_wstore (arr := "head") huuE haddE
      (by rw [ht3, wlen_charge, wlen_storeW, ht2, wlen_charge, wlen_setW, ht1, wlen_charge,
        wlen_setW, ht0, wlen_charge, hAF'.headL]; exact (G.src ⟨k, hk⟩).isLt) ?_)
    set t4 := (t3.storeW "head" uu (k + 1)).charge 1 with ht4
    have hcap4 : G.n + G.m + 2 ≤ t4.cap := by
      rw [ht4, cap_charge, cap_storeW]; exact hcap3
    have hfinE : evalW t4 (add (var "e") (lit 1)) = some (k + 1) := by
      apply evalW_add_of
      · rw [evalW_var, ht4, w_charge, w_storeW, ht3, w_charge, w_storeW, ht2, w_charge,
          w_setW, if_neg (by decide : ("e" : String) ≠ "q"), ht1, w_charge, w_setW,
          if_neg (by decide), ht0, w_charge, he]
      · exact evalW_lit_of (by have := hcap4; omega)
      · have := hcap4; omega
    refine runs_wset (a := k + 1) hfinE ?_
    set t5 := (t4.setW "e" (k + 1)).charge 1 with ht5
    -- the composed array effects of one iteration
    have hwa5 : ∀ x i, t5.wa x i = if x = "head" ∧ i = uu then k + 1
        else if x = "nxt" ∧ i = k then q0 else s'.wa x i := by
      intro x i
      rw [ht5, wa_charge, wa_setW, ht4, wa_charge, wa_storeW, ht3, wa_charge, wa_storeW,
        ht2, wa_charge, wa_setW, ht1, wa_charge, wa_setW, ht0, wa_charge]
    -- post: I (k + 1) t5
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine F0.charge ?_ 1
      refine F0.setW ?_ (by simp) _
      refine F0.charge ?_ 1
      refine F0.storeW ?_ _ _ (by simp)
      refine F0.charge ?_ 1
      refine F0.storeW ?_ _ _ (by simp)
      refine F0.charge ?_ 1
      refine F0.setW ?_ (by simp) _
      refine F0.charge ?_ 1
      refine F0.setW ?_ (by simp) _
      exact hF'.charge 1
    · refine AF.charge ?_ 1
      refine AF.setW ?_ _
      refine AF.charge ?_ 1
      refine AF.storeW ?_ _ _ _
      refine AF.charge ?_ 1
      refine AF.storeW ?_ _ _ _
      refine AF.charge ?_ 1
      refine AF.setW ?_ _
      refine AF.charge ?_ 1
      refine AF.setW ?_ _
      exact hAF'.charge 1
    · rw [ht5, w_charge, w_setW, if_pos rfl]
    · omega
    · -- the chain equations
      intro u
      by_cases hu : u = uu
      · subst hu
        have hhead5 : t5.wa "head" uu = k + 1 := by rw [hwa5, if_pos ⟨rfl, rfl⟩]
        have hnxt5 : t5.wa "nxt" k = q0 := by
          rw [hwa5, if_neg (fun hh => (by decide : ("nxt" : String) ≠ "head") hh.1),
            if_pos ⟨rfl, rfl⟩]
        rw [chainOf, hhead5, chainWalk_succ, if_neg (by omega : (k + 1 : ℕ) ≠ 0),
          Nat.add_sub_cancel, hnxt5]
        have hwalk0 : chainWalk s' q0 (G.m + 1) = outChainK G k uu := by
          rw [← hchain uu, chainOf]
        have hwalk0m : chainWalk s' q0 G.m = outChainK G k uu := by
          rw [chainWalk_take s' G.m q0 1, hwalk0]
          exact List.take_of_length_le
            ((outChainK_length_le k uu).trans (Nat.le_of_lt hk))
        have hstab : chainWalk t5 q0 G.m = chainWalk s' q0 G.m := by
          apply chainWalk_congr
          intro j hj
          have hjk : j < k := by
            rw [hwalk0m] at hj
            exact outChainK_lt k uu j hj
          rw [hwa5, if_neg (fun hh => (by decide : ("nxt" : String) ≠ "head") hh.1),
            if_neg (fun hh => by omega)]
        rw [hstab, hwalk0m, outChainK_succ_same (by rw [srcN, dif_pos hk])]
      · have hhead5 : t5.wa "head" u = s'.wa "head" u := by
          rw [hwa5, if_neg (fun hh => hu hh.2),
            if_neg (fun hh => (by decide : ("head" : String) ≠ "nxt") hh.1)]
        rw [chainOf, hhead5]
        have hstab : chainWalk t5 (s'.wa "head" u) (G.m + 1)
            = chainWalk s' (s'.wa "head" u) (G.m + 1) := by
          apply chainWalk_congr
          intro j hj
          have hjk : j < k := by
            have h := hchain u
            rw [chainOf] at h
            rw [h] at hj
            exact outChainK_lt k u j hj
          rw [hwa5, if_neg (fun hh => (by decide : ("nxt" : String) ≠ "head") hh.1),
            if_neg (fun hh => by omega)]
        rw [hstab, ← chainOf, hchain, outChainK_succ_ne (by
          have hsn : srcN G k = uu := by rw [srcN, dif_pos hk]
          intro hh
          rw [hsn] at hh
          exact hu hh.symm)]
    · -- cost
      have hcc : t5.cost = s'.cost + 6 := by
        rw [ht5, cost_charge, cost_setW, ht4, cost_charge, cost_storeW, ht3, cost_charge,
          cost_storeW, ht2, cost_charge, cost_setW, ht1, cost_charge, cost_setW, ht0,
          cost_charge]
      rw [hcc]; omega
  · -- exit
    intro s' ⟨hF', hAF', he, hle, hchain, hc⟩
    have hcond : evalW s' (lt (var "e") (var "m")) = some 0 := by
      rw [evalW_lt_of (x := G.m) (y := G.m) (by rw [evalW_var, he]) (by rw [evalW_var, hF'.hm])
        (by have := hF'.hcap; omega)]
      simp
    refine ⟨hcond, hF'.charge 1, hAF'.charge 1, fun u => ?_, ?_⟩
    · rw [chainOf_charge]; exact hchain u
    · rw [cost_charge]; omega
  · exact (hF.setW (x := "e") (a := 0) (by simp)).charge 1
  · exact (hAF.setW (x := "e") (a := 0)).charge 1
  · rw [hst0, w_charge, w_setW, if_pos rfl]
  · omega
  · intro u
    simp [chainOf, chainWalk, hst0, wa_charge, wa_setW, hzero, outChainK]
  · simp [hst0, cost_charge, cost_setW]

end Submission.DijkstraSim
