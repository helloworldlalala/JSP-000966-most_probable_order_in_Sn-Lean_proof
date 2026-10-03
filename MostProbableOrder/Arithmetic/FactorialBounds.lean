import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Factorial growth bounds (M2a)

Elementary bounds on `n!` derived from mathlib's Stirling lower bound
`Stirling.le_factorial_stirling : √(2πn)·(n/e)^n ≤ n!`, together with the
geometric-series tail decay used in the cycle-count tail estimate (M4).
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-- `1 ≤ √(2πk)` for `k ≥ 1`. -/
lemma one_le_sqrt_two_pi_mul {k : ℕ} (hk : 1 ≤ k) : (1 : ℝ) ≤ Real.sqrt (2 * π * k) := by
  rw [← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [Real.pi_gt_three, hkR]

/-- **(Stirling's lower bound, exponential form)** `(k/e)^k ≤ k!` for `k ≥ 1`. -/
theorem pow_div_exp_le_factorial {k : ℕ} (hk : 1 ≤ k) :
    (k / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
  have h := Stirling.le_factorial_stirling k
  have h1 := one_le_sqrt_two_pi_mul hk
  have hnn : (0 : ℝ) ≤ (k / Real.exp 1) ^ k := by positivity
  calc (k / Real.exp 1) ^ k = 1 * (k / Real.exp 1) ^ k := (one_mul _).symm
    _ ≤ Real.sqrt (2 * π * k) * (k / Real.exp 1) ^ k :=
        mul_le_mul_of_nonneg_right h1 hnn
    _ ≤ (Nat.factorial k : ℝ) := h

/-- **(Stirling's lower bound, logarithmic form)** `k·log k − k ≤ log(k!)` for `k ≥ 1`. -/
theorem log_factorial_lower {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * Real.log k - k ≤ Real.log (Nat.factorial k) := by
  have hk0 : k ≠ 0 := by omega
  have h := Stirling.le_log_factorial_stirling hk0
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have hlogpi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

/-- **Geometric tail decay.** For `0 ≤ x < 1`, every partial sum of the
geometric series is bounded by the full sum: `∑_{i<N} x^i ≤ 1/(1-x)`. -/
theorem geom_sum_le_inv_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, x ^ i ≤ 1 / (1 - x) := by
  have hxne : x ≠ 1 := ne_of_lt hx1
  have hden : (0 : ℝ) < 1 - x := by linarith
  rw [geom_sum_eq hxne]
  have hconv : (x ^ N - 1) / (x - 1) = (1 - x ^ N) / (1 - x) := by
    rw [div_eq_div_iff (by linarith : x - 1 ≠ 0) (by linarith : (1 : ℝ) - x ≠ 0)]
    ring
  rw [hconv, div_le_div_iff_of_pos_right hden]
  have : (0 : ℝ) ≤ x ^ N := by positivity
  linarith

end MostProbableOrder
