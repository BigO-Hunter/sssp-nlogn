import Submission.DijkstraRow
import Mathlib.Data.Nat.Fib.Basic

/-!
# Scalar accounting for a Fibonacci-heap Dijkstra lane

This module proves only the arithmetic used by the B2 feasibility envelope.  It does not define
a RAM heap or a race target.  Potentials and operation costs are natural-number ledger quantities;
the shortest-path real-log estimates reuse B1's proved caps.
-/

namespace Submission.FibHeapAccounting

/-- Two Fibonacci steps at least double the value. -/
theorem fib_add_four_double (k : ℕ) : 2 * Nat.fib (k + 2) ≤ Nat.fib (k + 4) := by
  have h := Nat.fib_le_fib_succ (n := k + 2)
  calc
    2 * Nat.fib (k + 2) = Nat.fib (k + 2) + Nat.fib (k + 2) := by ring
    _ ≤ Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.add_le_add_left h _
    _ = Nat.fib (k + 4) := by
      simpa [Nat.add_assoc] using (Nat.fib_add_two (n := k + 2)).symm

/-- The elementary exponential lower bound used for the logarithmic rank cap. -/
theorem fib_pow_half (k : ℕ) : 2 ^ (k / 2) ≤ Nat.fib (k + 2) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => norm_num
    | 1 => norm_num [Nat.fib_add_two]
    | k + 2 =>
      have prev := ih k (by omega)
      have double := fib_add_four_double k
      have hpow : 2 ^ ((k + 2) / 2) = 2 * 2 ^ (k / 2) := by
        rw [show (k + 2) / 2 = k / 2 + 1 by omega, pow_succ]
        ring
      rw [hpow]
      exact (Nat.mul_le_mul_left 2 prev).trans double

/-- A Fibonacci-size lower bound yields the deliberately elementary `2L+1` degree cap. -/
theorem degree_log_bound {k n : ℕ} (hsize : Nat.fib (k + 2) ≤ n) :
    k ≤ 2 * Nat.log 2 n + 1 := by
  have hnlt : n < 2 ^ (Nat.log 2 n + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    simpa [Nat.succ_eq_add_one] using h
  have hhalf : k / 2 ≤ Nat.log 2 n := by
    by_contra h
    have hgt : Nat.log 2 n + 1 ≤ k / 2 := by omega
    have hpow : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ (k / 2) :=
      Nat.pow_le_pow_right (by norm_num) hgt
    have hchain : 2 ^ (Nat.log 2 n + 1) ≤ n := hpow.trans ((fib_pow_half k).trans hsize)
    omega
  omega

/-- The independent tiny-`n` slot bound: a tree of `N` nodes has degree below `N`. -/
theorem degree_slot_bound {d N n : ℕ} (hd : d < N) (hN : N ≤ n) : d < n + 1 := by
  omega

/-- Base Fibonacci potential: trees plus twice the marked-live-node count. -/
def potential (t μ : ℕ) : ℕ := t + 2 * μ

/-- RAM-scaled potential, used to cancel multi-statement root-processing loops. -/
def scaledPotential (K t μ : ℕ) : ℕ := K * potential t μ

/-- The loose elementary rank cap, avoiding any golden-ratio formalization. -/
def rankCap (n : ℕ) : ℕ := 2 * Nat.log 2 n + 1

/-- One more than the rank cap: the post-consolidation root-count cap. -/
def rootCap (n : ℕ) : ℕ := rankCap n + 1

/-- The empty heap has zero base potential. -/
theorem potential_empty : potential 0 0 = 0 := rfl

/-- Insert costs at most `I0+K` after paying for one new root of potential. -/
theorem insert_amortized (K I0 t μ : ℕ) :
    I0 + scaledPotential K (t + 1) μ ≤ scaledPotential K t μ + (I0 + K) := by
  simp only [scaledPotential, potential]
  nlinarith

/-- A link is amortized-free when its actual budget is at most one scaled potential unit. -/
theorem link_amortized {K L0 t μ t' μ' : ℕ} (hK : L0 ≤ K) (ht : t' + 1 ≤ t)
    (hμ : μ' ≤ μ) : L0 + scaledPotential K t' μ' ≤ scaledPotential K t μ := by
  have hp : potential t' μ' + 1 ≤ potential t μ := by
    simp only [potential]
    omega
  have hm := Nat.mul_le_mul_left K hp
  simp only [scaledPotential] at *
  nlinarith

/-- A decrease-key with `c≥1` cuts has amortized budget `D0+3K+D1`. -/
theorem decrease_amortized {K D0 D1 c t μ t' μ' : ℕ} (hc : 1 ≤ c) (hK : D1 ≤ K)
    (hpot : potential t' μ' + c ≤ potential t μ + 4) :
    D0 + D1 * c + scaledPotential K t' μ' ≤ scaledPotential K t μ + (D0 + 3 * K + D1) := by
  have hm := Nat.mul_le_mul_left K hpot
  have hmul := Nat.mul_le_mul_right (c - 1) hK
  have hD : D1 * c + K ≤ K * c + D1 := by
    nlinarith
  simp only [scaledPotential] at *
  nlinarith

/-- Extraction's root-processing and linking costs are cancelled by scaled tree potential. -/
theorem extract_amortized {K E0 Er El Ed Em t0 ell t d t1 μ μ' Q : ℕ}
    (hB : Er + El ≤ K) (ht0 : t0 + 1 = t + d) (hell : ell ≤ t0) (ht1 : t1 ≤ Q)
    (hd : d < Q) (hpot : potential t1 μ' + t ≤ potential t μ + Q) :
    E0 + Er * t0 + El * ell + Ed * d + Em * t1 + scaledPotential K t1 μ'
      ≤ scaledPotential K t μ + (E0 + (K + (Er + El) + Ed + Em) * Q) := by
  have hEll := Nat.mul_le_mul_left El hell
  have ht1m := Nat.mul_le_mul_left Em ht1
  have hdQ : d ≤ Q := by omega
  have hKd := Nat.mul_le_mul_left K hdQ
  have hEd := Nat.mul_le_mul_left Ed hdQ
  have hBt0 := Nat.mul_le_mul_right t0 hB
  have hBQ := Nat.mul_le_mul_right Q hB
  have hpotK := Nat.mul_le_mul_left K hpot
  have ht0K := congrArg (fun x : ℕ => K * x) ht0
  simp only [scaledPotential] at *
  nlinarith

/-- The root cap is `2L+2`, including the positive `L=0` case. -/
theorem rootCap_eq (n : ℕ) : rootCap n = 2 * Nat.log 2 n + 2 := by
  simp [rootCap, rankCap, Nat.add_assoc]

/-- The concrete B2 scalar envelope from the feasibility probe. -/
def total (r n m L : ℕ) : ℕ := 280 * r * L + 384 * r + 13 * n + 279 * m + 4 * L + 50

/-- Its sparse simplification after `r≤n` and `m≤nL`. -/
def sparseTotal (n L : ℕ) : ℕ := 559 * n * L + 397 * n + 4 * L + 50

/-- Sparse Nat arithmetic, with no approximation or weakened constants. -/
theorem total_sparse {r n m L : ℕ} (hr : r ≤ n) (hm : m ≤ n * L) :
    total r n m L ≤ sparseTotal n L := by
  have hr280 := Nat.mul_le_mul_left 280 hr
  have hRL := Nat.mul_le_mul_right L hr280
  have hr384 := Nat.mul_le_mul_left 384 hr
  have hm279 := Nat.mul_le_mul_left 279 hm
  simp only [total, sparseTotal]
  nlinarith

/-- The Dijkstra-side polynomial fallback, including all tiny inputs. -/
theorem total_fallback {r n m L : ℕ} (hr : r ≤ m + 1) (hL : L ≤ n) :
    total r n m L ≤ 1010 * (n + 1) * (m + 1) := by
  have hrl : r * L ≤ n * (m + 1) := by
    have h := Nat.mul_le_mul hr hL
    simpa [Nat.mul_comm] using h
  have hBn : n ≤ (n + 1) * (m + 1) := by nlinarith
  have hBm : m ≤ (n + 1) * (m + 1) := by nlinarith
  have hB1 : 1 ≤ (n + 1) * (m + 1) := by nlinarith
  have hBnMul : n * (m + 1) ≤ (n + 1) * (m + 1) := by nlinarith
  have hBm1 : m + 1 ≤ (n + 1) * (m + 1) := by nlinarith
  have hrlB := (Nat.mul_le_mul_left 280 hrl).trans (Nat.mul_le_mul_left 280 hBnMul)
  have hrB := (Nat.mul_le_mul_left 384 hr).trans (Nat.mul_le_mul_left 384 hBm1)
  have hLB := (Nat.mul_le_mul_left 4 hL).trans (Nat.mul_le_mul_left 4 hBn)
  have hnB := Nat.mul_le_mul_left 13 hBn
  have hmB := Nat.mul_le_mul_left 279 hBm
  have h50 := Nat.mul_le_mul_left 50 hB1
  simp only [total]
  nlinarith

/-- Positive control for the smallest sourced graph: exact cost 447 and fallback margin. -/
theorem tiny_one_zero : total 1 1 0 0 = 447 ∧ total 1 1 0 0 ≤ 1010 * (1 + 1) * (0 + 1) := by
  norm_num [total]

end Submission.FibHeapAccounting
