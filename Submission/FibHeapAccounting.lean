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

end Submission.FibHeapAccounting
