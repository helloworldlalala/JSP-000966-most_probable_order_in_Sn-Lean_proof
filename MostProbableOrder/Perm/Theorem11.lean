import MostProbableOrder.Perm.Recursion
import MostProbableOrder.Perm.LargeOrders43
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Theorem 1.1 — the two-divisor lemma and related counting facts

This file collects the elementary pieces of the proof of the characterization half of
Theorem 1.1 (paper §3, lines 216–246), starting with the "two divisors" argument that rules
out more than one large divisor of `m` in the interval `(n - n^{1/2}, n]`.
-/

open Filter
open scoped Real
open scoped Topology

namespace MostProbableOrder

/-! ### The lcm inequality `d₁ d₂ ≤ lcm(d₁,d₂) · (d₂ - d₁)` -/

/-- `gcd(d₁,d₂) | d₂ - d₁` (as `gcd` divides both). -/
lemma gcd_dvd_sub {d₁ d₂ : ℕ} : Nat.gcd d₁ d₂ ∣ d₂ - d₁ :=
  Nat.dvd_sub (Nat.gcd_dvd_right d₁ d₂) (Nat.gcd_dvd_left d₁ d₂)

/-- `gcd(d₁,d₂) ≤ d₂ - d₁` when `d₁ < d₂`. -/
lemma gcd_le_sub {d₁ d₂ : ℕ} (h : d₁ < d₂) : Nat.gcd d₁ d₂ ≤ d₂ - d₁ :=
  Nat.le_of_dvd (Nat.sub_pos_of_lt h) (gcd_dvd_sub (d₁ := d₁) (d₂ := d₂))

/-- The key lcm inequality: `d₁ · d₂ ≤ lcm(d₁,d₂) · (d₂ - d₁)` for `d₁ < d₂`. -/
lemma mul_le_lcm_mul_sub {d₁ d₂ : ℕ} (h : d₁ < d₂) :
    d₁ * d₂ ≤ Nat.lcm d₁ d₂ * (d₂ - d₁) := by
  have hgcd : Nat.gcd d₁ d₂ ≤ d₂ - d₁ := gcd_le_sub h
  have hlcm : Nat.lcm d₁ d₂ * Nat.gcd d₁ d₂ = d₁ * d₂ := Nat.lcm_mul_gcd d₁ d₂
  calc d₁ * d₂ = Nat.lcm d₁ d₂ * Nat.gcd d₁ d₂ := hlcm.symm
    _ ≤ Nat.lcm d₁ d₂ * (d₂ - d₁) := Nat.mul_le_mul_left _ hgcd

/-- If `d₁` and `d₂` both divide `m`, then so does their lcm. -/
lemma lcm_dvd_of_dvd {d₁ d₂ m : ℕ} (hd₁ : d₁ ∣ m) (hd₂ : d₂ ∣ m) : Nat.lcm d₁ d₂ ∣ m :=
  Nat.lcm_dvd hd₁ hd₂

/-- If `d₁` and `d₂` both divide a positive `m`, then `lcm(d₁,d₂) ≤ m`. -/
lemma lcm_le_of_dvd {d₁ d₂ m : ℕ} (hm : 0 < m) (hd₁ : d₁ ∣ m) (hd₂ : d₂ ∣ m) :
    Nat.lcm d₁ d₂ ≤ m :=
  Nat.le_of_dvd hm (lcm_dvd_of_dvd hd₁ hd₂)

/-! ### The real lower bound `(n - √n)² / √n > n^{4/3}` -/

/-- `2 ≤ n^{1/3}` for `n ≥ 8`. -/
lemma cube_root_ge_two (n : ℕ) (hn : 8 ≤ n) : (2 : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) := by
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (8 : ℝ)) hnR (by norm_num : 0 ≤ (1/3 : ℝ))
  rwa [show (8 : ℝ)^(1/3 : ℝ) = 2 by norm_num] at h

/-- `2 ≤ n^{1/6}` for `n ≥ 64`. -/
lemma sixth_root_ge_two (n : ℕ) (hn : 64 ≤ n) : (2 : ℝ) ≤ (n : ℝ)^(1/6 : ℝ) := by
  have hnR : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (64 : ℝ)) hnR (by norm_num : 0 ≤ (1/6 : ℝ))
  rwa [show (64 : ℝ)^(1/6 : ℝ) = 2 by norm_num] at h

/-- `n^{11/6} < n² - 2n^{3/2} + n` for `n ≥ 64`. -/
lemma rpow_eleven_sixth_lt_sq_sub (n : ℕ) (hn : 64 ≤ n) :
    (n : ℝ)^(11/6 : ℝ) < (n : ℝ)^2 - 2 * (n : ℝ)^(3/2 : ℝ) + (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2pow : 2 * (n : ℝ)^(11/6 : ℝ) ≤ (n : ℝ)^2 := by
    have h6 : (2 : ℝ) ≤ (n : ℝ)^(1/6 : ℝ) := sixth_root_ge_two n hn
    have hdecomp : (n : ℝ)^2 = (n : ℝ)^(11/6 : ℝ) * (n : ℝ)^(1/6 : ℝ) := by
      have h := calc (n : ℝ)^(11/6 : ℝ) * (n : ℝ)^(1/6 : ℝ)
          = (n : ℝ)^((11/6 : ℝ) + (1/6 : ℝ)) := by rw [← Real.rpow_add hnpos]
        _ = (n : ℝ)^(2 : ℝ) := by congr 1; norm_num
        _ = (n : ℝ)^2 := by simpa using (Real.rpow_natCast (n : ℝ) 2)
      exact h.symm
    rw [hdecomp]
    have hnonneg : 0 ≤ (n : ℝ)^(11/6 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h := mul_le_mul_of_nonneg_right h6 hnonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hb : 0 < (n : ℝ)^(11/6 : ℝ) - 2 * (n : ℝ)^(3/2 : ℝ) + (n : ℝ) := by
    have hcbrt : (2 : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) := cube_root_ge_two n (by omega : 8 ≤ n)
    have hdecomp : (n : ℝ)^(11/6 : ℝ) = (n : ℝ)^(3/2 : ℝ) * (n : ℝ)^(1/3 : ℝ) := by
      rw [show (11/6 : ℝ) = (3/2 : ℝ) + (1/3 : ℝ) by norm_num]
      rw [Real.rpow_add hnpos]
    have hnonneg : 0 ≤ (n : ℝ)^(3/2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hprod : 2 * (n : ℝ)^(3/2 : ℝ) ≤ (n : ℝ)^(3/2 : ℝ) * (n : ℝ)^(1/3 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hcbrt hnonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    rw [← hdecomp] at hprod
    nlinarith
  have h1 : (n : ℝ)^2 - (n : ℝ)^(11/6 : ℝ) ≥ (n : ℝ)^(11/6 : ℝ) := by
    nlinarith [h2pow]
  nlinarith [h1, hb]

/-- The key lower bound of the two-divisor argument:
`n^{4/3} < (n - √n)² / √n` for `n ≥ 64`. -/
lemma rpow_four_third_lt_sq_sub_sqrt_div_sqrt (n : ℕ) (hn : 64 ≤ n) :
    (n : ℝ)^(4/3 : ℝ) < (((n : ℝ) - Real.sqrt (n : ℝ))^2) / Real.sqrt (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  rw [lt_div_iff₀ hsqrt_pos]
  have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ)^(1/2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
  have hrew : (n : ℝ)^(4/3 : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ)^(11/6 : ℝ) := by
    rw [hsqrt]
    calc (n : ℝ)^(4/3 : ℝ) * (n : ℝ)^(1/2 : ℝ)
        = (n : ℝ)^((4/3 : ℝ) + (1/2 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ)^(11/6 : ℝ) := by congr 1; norm_num
  rw [hrew]
  have hsq : ((n : ℝ) - Real.sqrt (n : ℝ))^2 = (n : ℝ)^2 - 2 * (n : ℝ) * Real.sqrt (n : ℝ) + (Real.sqrt (n : ℝ))^2 := by ring
  have hsqrt_sq : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  have hmid : (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ)^(3/2 : ℝ) := by
    rw [hsqrt]
    calc (n : ℝ) * (n : ℝ)^(1/2 : ℝ) = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(1/2 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ)^((1 : ℝ) + (1/2 : ℝ)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ)^(3/2 : ℝ) := by congr 1; norm_num
  rw [hsq, hsqrt_sq]
  rw [show (n : ℝ)^2 - 2 * (n : ℝ) * Real.sqrt (n : ℝ) + (n : ℝ) =
      (n : ℝ)^2 - 2 * ((n : ℝ) * Real.sqrt (n : ℝ)) + (n : ℝ) by ring]
  rw [hmid]
  exact rpow_eleven_sixth_lt_sq_sub n hn

/-! ### Reduction to `m < n^{4/3}` (from `prop_large_orders_43`) -/

/-- Under `p_n(m) ≥ 1/n`, we must have `m < n^{4/3}` (eventually): indeed `m ≥ n^{4/3}`
forces `n · p_n(m) ≤ 1/2` by `prop_large_orders_43`, contradicting `n · p_n(m) ≥ 1`. -/
theorem p_ge_one_div_n_implies_not_rpow_four_third :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (1 : ℝ) / (n : ℝ) ≤ p n m →
      ¬ (n : ℝ) ^ (4 / 3 : ℝ) ≤ (m : ℝ) := by
  filter_upwards [prop_large_orders_43, Filter.eventually_ge_atTop 1] with n h43 hn1
  intro m hp hle
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnp : (1 : ℝ) ≤ (n : ℝ) * p n m := by
    have h := (div_le_iff₀ hnpos).mp hp
    simpa [mul_comm] using h
  have hnp2 : (n : ℝ) * p n m ≤ (1 : ℝ) / 2 := h43 m hle
  have hcontra : (1 : ℝ) ≤ (1 : ℝ) / 2 := le_trans hnp hnp2
  norm_num at hcontra

/-! ### The `τ(m)` bound: `τ(m)² / n^{3/2} = o(1/n)` -/

/-- `(τ m)² ≤ (C·m)^{1/8}` from `(τ m)^16 ≤ C·m`. -/
lemma tau_sq_le_rpow_eighth (m C : ℕ) (hC : (tau m)^16 ≤ C * m) :
    (tau m : ℝ)^2 ≤ ((C * m : ℕ) : ℝ)^(1/8 : ℝ) := by
  have hcast : (tau m : ℝ)^16 ≤ ((C * m : ℕ) : ℝ) := by
    exact_mod_cast hC
  have hnonneg : 0 ≤ (tau m : ℝ) := Nat.cast_nonneg _
  have hmono : ((tau m : ℝ)^16)^(1/8 : ℝ) ≤ ((C * m : ℕ) : ℝ)^(1/8 : ℝ) :=
    Real.rpow_le_rpow (by positivity : 0 ≤ (tau m : ℝ)^16) hcast (by norm_num : 0 ≤ (1/8 : ℝ))
  have hrew : ((tau m : ℝ)^16)^(1/8 : ℝ) = (tau m : ℝ)^2 := by
    rw [show (tau m : ℝ)^16 = (tau m : ℝ)^(16 : ℝ) by
          exact (Real.rpow_natCast (tau m : ℝ) 16).symm]
    rw [← Real.rpow_mul hnonneg (16 : ℝ) (1/8 : ℝ)]
    rw [show (tau m : ℝ)^((16 : ℝ) * (1/8 : ℝ)) = (tau m : ℝ)^(2 : ℝ) by congr 1; norm_num]
    exact (Real.rpow_natCast (tau m : ℝ) 2)
  rw [← hrew]
  exact hmono

/-- `Nat.sqrt n ≤ √n` (as reals). -/
lemma nat_sqrt_le_real_sqrt (n : ℕ) : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hsq : (Nat.sqrt n : ℝ)^2 ≤ (n : ℝ) := by
    rw [sq]
    have h := Nat.sqrt_le n
    exact_mod_cast h
  have hle := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt n))] at hle

/-- `(τ m)² ≤ C^{1/8} · n^{1/6}` whenever `m < n^{4/3}`. -/
lemma tau_sq_le_of_lt_rpow_four_third (n m C : ℕ) (hC : (tau m)^16 ≤ C * m)
    (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) :
    (tau m : ℝ)^2 ≤ (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(1/6 : ℝ) := by
  have htau := tau_sq_le_rpow_eighth m C hC
  have hmul : ((C * m : ℕ) : ℝ)^(1/8 : ℝ) = (C : ℝ)^(1/8 : ℝ) * (m : ℝ)^(1/8 : ℝ) := by
    rw [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg C) (Nat.cast_nonneg m)
  have hmpow : (m : ℝ)^(1/8 : ℝ) ≤ (n : ℝ)^(1/6 : ℝ) := by
    have hmle : (m : ℝ) ≤ (n : ℝ)^(4/3 : ℝ) := le_of_lt hm
    have h1 := Real.rpow_le_rpow (Nat.cast_nonneg m) hmle (by norm_num : 0 ≤ (1/8 : ℝ))
    have hrew : ((n : ℝ)^(4/3 : ℝ))^(1/8 : ℝ) = (n : ℝ)^(1/6 : ℝ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg n) (4/3 : ℝ) (1/8 : ℝ)]
      congr 1; norm_num
    rwa [hrew] at h1
  calc (tau m : ℝ)^2 ≤ ((C * m : ℕ) : ℝ)^(1/8 : ℝ) := htau
    _ = (C : ℝ)^(1/8 : ℝ) * (m : ℝ)^(1/8 : ℝ) := hmul
    _ ≤ (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(1/6 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hmpow (Real.rpow_nonneg (Nat.cast_nonneg C) _)

/-- **The `τ(m)` estimate** of Theorem 1.1: for `m < n^{4/3}`,
`τ(m)² / n^{3/2} ≤ 1/(6n)` eventually (so `= o(1/n)`). -/
lemma eventually_tau_sq_div_n_pow_three_half_le :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (m : ℝ) < (n : ℝ)^(4/3 : ℝ) →
      (tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ) ≤ (1 : ℝ) / (6 : ℝ) / (n : ℝ) := by
  rcases tau_pow_sixteen_le with ⟨C, hC⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)^(1/3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/3 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hn_ge : ∀ᶠ (n : ℕ) in atTop, 6 * (C : ℝ)^(1/8 : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) :=
    hnat.eventually (Ici_mem_atTop (6 * (C : ℝ)^(1/8 : ℝ)))
  filter_upwards [hn_ge, Filter.eventually_ge_atTop 1] with n hnge hn1
  intro m hm
  have htau := tau_sq_le_of_lt_rpow_four_third n m C (hC m) hm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnnonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
  -- (τ m)² / n^{3/2} ≤ C^{1/8}·n^{1/6} / n^{3/2} = C^{1/8}·n^{-4/3}
  have hdiv : (tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ) ≤ (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(1/6 : ℝ) / (n : ℝ)^(3/2 : ℝ) :=
    div_le_div_of_nonneg_right htau (Real.rpow_nonneg hnnonneg _)
  -- C^{1/8}·n^{1/6} / n^{3/2} = C^{1/8}·n^{-4/3}
  have hrew : (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(1/6 : ℝ) / (n : ℝ)^(3/2 : ℝ) =
      (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) := by
    have hpow : (n : ℝ)^(1/6 : ℝ) / (n : ℝ)^(3/2 : ℝ) = (n : ℝ)^(-(4/3 : ℝ)) := by
      rw [div_eq_mul_inv]
      rw [show ((n : ℝ)^(3/2 : ℝ))⁻¹ = (n : ℝ)^(-(3/2 : ℝ)) by
            exact (Real.rpow_neg (le_of_lt hnpos) (3/2 : ℝ)).symm]
      rw [← Real.rpow_add hnpos (1/6 : ℝ) (-(3/2 : ℝ))]
      rw [show (1/6 : ℝ) + (-(3/2 : ℝ)) = -(4/3 : ℝ) by norm_num]
    rw [mul_div_assoc]
    rw [hpow]
  have hle : (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) ≤ (1 : ℝ) / (6 : ℝ) / (n : ℝ) := by
    -- C^{1/8} ≤ (1/6)·n^{1/3}
    have hc : (C : ℝ)^(1/8 : ℝ) ≤ (1 / 6 : ℝ) * (n : ℝ)^(1/3 : ℝ) := by
      nlinarith [hnge]
    have hnonneg : 0 ≤ (n : ℝ)^(-(4/3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnpos) _
    have h1 := mul_le_mul_of_nonneg_right hc hnonneg
    -- C^{1/8}·n^{-4/3} ≤ (1/6)·n^{1/3}·n^{-4/3} = 1/(6n)
    have h2 : (1 / 6 : ℝ) * (n : ℝ)^(1/3 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) = (1 : ℝ) / (6 : ℝ) / (n : ℝ) := by
      rw [mul_assoc]
      rw [show (n : ℝ)^(1/3 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) = (n : ℝ)⁻¹ by
        rw [← Real.rpow_add hnpos (1/3 : ℝ) (-(4/3 : ℝ))]
        rw [show (1/3 : ℝ) + (-(4/3 : ℝ)) = -(1 : ℝ) by norm_num]
        rw [show (n : ℝ)^(-(1 : ℝ)) = (n : ℝ)⁻¹ by
          rw [Real.rpow_neg (le_of_lt hnpos) (1 : ℝ)]
          rw [Real.rpow_one]]]
      rw [show (1 / 6 : ℝ) * (n : ℝ)⁻¹ = (1 : ℝ) / (6 : ℝ) / (n : ℝ) by ring]
    exact h1.trans (le_of_eq h2)
  exact le_trans (le_trans hdiv (le_of_eq hrew)) hle

/-! ### The two-divisor argument: at most one divisor in `(n - √n, n]` -/

/-- `0 < n - √n` for `n ≥ 2`. -/
lemma n_sub_sqrt_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℝ) - Real.sqrt (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt_lt_n : Real.sqrt (n : ℝ) < (n : ℝ) := by
    rw [Real.sqrt_lt' hnpos]
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hnn := mul_lt_mul_of_pos_left hn1 hnpos
    nlinarith [hnn]
  linarith

/-- `d₁·d₂ / (d₂-d₁) ≤ lcm(d₁,d₂)` for `d₁ < d₂`. -/
lemma div_le_lcm_of_mul_le {d₁ d₂ : ℕ} (hlt : d₁ < d₂) :
    (d₁ : ℝ) * (d₂ : ℝ) / ((d₂ - d₁ : ℕ) : ℝ) ≤ (Nat.lcm d₁ d₂ : ℝ) := by
  have hnat : d₁ * d₂ ≤ Nat.lcm d₁ d₂ * (d₂ - d₁) := mul_le_lcm_mul_sub hlt
  have hcast : (d₁ : ℝ) * (d₂ : ℝ) ≤ (Nat.lcm d₁ d₂ : ℝ) * ((d₂ - d₁ : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsub_pos : 0 < ((d₂ - d₁ : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hlt)
  exact (div_le_iff₀ hsub_pos).mpr hcast

/-- `(n - √n)²/√n < d₁d₂/(d₂-d₁)` for divisors `d₁ < d₂` with `d₁,d₂ > n - √n`, `d₂ ≤ n`. -/
lemma sq_sub_sqrt_div_sqrt_lt_div {n d₁ d₂ : ℕ} (hn : 2 ≤ n) (hlt : d₁ < d₂)
    (hd₁gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₁ : ℝ))
    (hd₂gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₂ : ℝ))
    (hd₂le : d₂ ≤ n) :
    ((n : ℝ) - Real.sqrt (n : ℝ))^2 / Real.sqrt (n : ℝ) <
      (d₁ : ℝ) * (d₂ : ℝ) / ((d₂ - d₁ : ℕ) : ℝ) := by
  have hnsub_pos : 0 < (n : ℝ) - Real.sqrt (n : ℝ) := n_sub_sqrt_pos hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hsq_lt : ((n : ℝ) - Real.sqrt (n : ℝ))^2 < (d₁ : ℝ) * (d₂ : ℝ) := by
    have h1 : ((n : ℝ) - Real.sqrt (n : ℝ)) * ((n : ℝ) - Real.sqrt (n : ℝ)) < (d₁ : ℝ) * (d₂ : ℝ) := by
      exact mul_lt_mul hd₁gt (le_of_lt hd₂gt) hnsub_pos (le_of_lt (lt_trans hnsub_pos hd₁gt))
    simpa [sq] using h1
  have hsub_lt : (d₂ : ℝ) - (d₁ : ℝ) < Real.sqrt (n : ℝ) := by
    have hd2le : (d₂ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hd₂le
    nlinarith [hd2le, hd₁gt]
  have hsub_pos : 0 < (d₂ : ℝ) - (d₁ : ℝ) := sub_pos.mpr (by exact_mod_cast hlt)
  have hinv_lt : (1 : ℝ) / Real.sqrt (n : ℝ) < (1 : ℝ) / ((d₂ : ℝ) - (d₁ : ℝ)) :=
    one_div_lt_one_div_of_lt hsub_pos hsub_lt
  have hcomb : ((n : ℝ) - Real.sqrt (n : ℝ))^2 * ((1 : ℝ) / Real.sqrt (n : ℝ)) <
      (d₁ : ℝ) * (d₂ : ℝ) * ((1 : ℝ) / ((d₂ : ℝ) - (d₁ : ℝ))) := by
    have hnonneg : 0 ≤ (d₁ : ℝ) * (d₂ : ℝ) := by positivity
    have hinv_pos : 0 < (1 : ℝ) / Real.sqrt (n : ℝ) := one_div_pos.mpr hsqrt_pos
    exact mul_lt_mul hsq_lt (le_of_lt hinv_lt) hinv_pos hnonneg
  rw [show ((d₂ - d₁ : ℕ) : ℝ) = (d₂ : ℝ) - (d₁ : ℝ) by
        rw [Nat.cast_sub (Nat.le_of_lt hlt)]]
  simpa [div_eq_mul_inv] using hcomb

/-- The core two-divisor contradiction (for `d₁ < d₂`). -/
lemma two_divisors_contradict_lt (n m d₁ d₂ : ℕ) (hn : 64 ≤ n)
    (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) (hmpos : 0 < m)
    (hlt : d₁ < d₂)
    (hd₁ : d₁ ∣ m) (hd₂ : d₂ ∣ m)
    (hd₁gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₁ : ℝ))
    (hd₂gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₂ : ℝ))
    (hd₂le : d₂ ≤ n) :
    False := by
  have hlcm_le_m : (Nat.lcm d₁ d₂ : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (lcm_le_of_dvd hmpos hd₁ hd₂)
  have hfact1 := div_le_lcm_of_mul_le hlt
  have hfact2 := sq_sub_sqrt_div_sqrt_lt_div (by omega : 2 ≤ n) hlt hd₁gt hd₂gt hd₂le
  have hmain : (n : ℝ)^(4/3 : ℝ) < (m : ℝ) := by
    calc (n : ℝ)^(4/3 : ℝ) < ((n : ℝ) - Real.sqrt (n : ℝ))^2 / Real.sqrt (n : ℝ) :=
          rpow_four_third_lt_sq_sub_sqrt_div_sqrt n hn
      _ < (d₁ : ℝ) * (d₂ : ℝ) / ((d₂ - d₁ : ℕ) : ℝ) := hfact2
      _ ≤ (Nat.lcm d₁ d₂ : ℝ) := hfact1
      _ ≤ (m : ℝ) := hlcm_le_m
  exact (lt_irrefl ((n : ℝ)^(4/3 : ℝ))) (lt_trans hmain hm)

/-- **The two-divisor argument**: if `m < n^{4/3}` (and `n ≥ 64`), then `m` has at most one
divisor in the interval `(n - √n, n]`. (Paper §3, line 226.) -/
lemma two_divisors_contradict (n m d₁ d₂ : ℕ) (hn : 64 ≤ n)
    (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) (hmpos : 0 < m)
    (hd₁ : d₁ ∣ m) (hd₂ : d₂ ∣ m)
    (hd₁gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₁ : ℝ))
    (hd₂gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₂ : ℝ))
    (hd₁le : d₁ ≤ n) (hd₂le : d₂ ≤ n) :
    d₁ = d₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact two_divisors_contradict_lt n m d₁ d₂ hn hm hmpos hlt hd₁ hd₂ hd₁gt hd₂gt hd₂le
  · exact two_divisors_contradict_lt n m d₂ d₁ hn hm hmpos hgt hd₂ hd₁ hd₂gt hd₁gt hd₁le

/-! ### The summand bound and the strong `τ` bound (for the recursion sum split) -/

/-- `lcmOrderProb n d m ≤ τ(m)/(n-d)`: each recursion summand is bounded via
Corollary 2.2 (second statement), since `lcm(d, ord σ) = m` forces `ord σ | m`. -/
lemma lcmOrderProb_le_tau_div (n d m : ℕ) (hm : 1 ≤ m) (hn_d : 1 ≤ n - d) :
    lcmOrderProb n d m ≤ (tau m : ℝ) / ((n - d : ℕ) : ℝ) := by
  classical
  haveI : NeZero (n - d) := ⟨by omega⟩
  unfold lcmOrderProb lcmOrderCount
  have hsub : ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)) ⊆
      ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => orderOf σ ∣ m)) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨hσ.1, by rw [← hσ.2]; exact Nat.dvd_lcm_right d (orderOf σ)⟩
  have hcard : ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card ≤
      ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => orderOf σ ∣ m)).card :=
    Finset.card_le_card hsub
  have hle := ord_dvd_prob_le_tau_div_n (n := n - d) m hm
  calc ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card / (Nat.factorial (n-d) : ℝ)
      ≤ ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => orderOf σ ∣ m)).card / (Nat.factorial (n-d) : ℝ) := by
            exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ (tau m : ℝ) / ((n - d : ℕ) : ℝ) := by
            simpa [tau] using hle

/-- `√n ≤ 2·Nat.sqrt n` for `n ≥ 1`. -/
lemma sqrt_le_two_mul_nat_sqrt (n : ℕ) (hn : 1 ≤ n) : Real.sqrt (n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
  have hs1 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hn)
  have hlt_succ : n < (Nat.sqrt n + 1)^2 := by
    simpa [pow_two] using Nat.lt_succ_sqrt n
  have hsqrt_lt : Real.sqrt (n : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_lt' (by exact_mod_cast (by omega : 0 < Nat.sqrt n + 1))]
    exact_mod_cast hlt_succ
  have hs_succ_le : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
    exact_mod_cast (by omega : Nat.sqrt n + 1 ≤ 2 * Nat.sqrt n)
  exact le_trans (le_of_lt hsqrt_lt) hs_succ_le

/-- **Strong `τ` bound**: `τ(m)² / n^{3/2} ≤ C^{1/8} · n^{-4/3}` for `m < n^{4/3}`. -/
lemma tau_sq_div_n_pow_three_half_le_rpow (n m C : ℕ) (hn : 0 < n) (hC : (tau m)^16 ≤ C * m)
    (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) :
    (tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ) ≤ (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) := by
  have htau := tau_sq_le_of_lt_rpow_four_third n m C hC hm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdiv : (tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ) ≤ (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(1/6 : ℝ) / (n : ℝ)^(3/2 : ℝ) :=
    div_le_div_of_nonneg_right htau (Real.rpow_nonneg (le_of_lt hnpos) _)
  have hrew : (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(1/6 : ℝ) / (n : ℝ)^(3/2 : ℝ) =
      (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) := by
    have hpow : (n : ℝ)^(1/6 : ℝ) / (n : ℝ)^(3/2 : ℝ) = (n : ℝ)^(-(4/3 : ℝ)) := by
      rw [div_eq_mul_inv]
      rw [show ((n : ℝ)^(3/2 : ℝ))⁻¹ = (n : ℝ)^(-(3/2 : ℝ)) by
            exact (Real.rpow_neg (le_of_lt hnpos) (3/2 : ℝ)).symm]
      rw [← Real.rpow_add hnpos (1/6 : ℝ) (-(3/2 : ℝ))]
      rw [show (1/6 : ℝ) + (-(3/2 : ℝ)) = -(4/3 : ℝ) by norm_num]
    rw [mul_div_assoc]
    rw [hpow]
  exact le_trans hdiv (le_of_eq hrew)

/-! ### The recursion sum split: small divisors contribute `o(1/n)` -/

/-- `lcmOrderProb n d m = 0` unless `d | m`. -/
lemma lcmOrderProb_eq_zero_of_not_dvd {n d m : ℕ} (h : ¬ d ∣ m) : lcmOrderProb n d m = 0 := by
  unfold lcmOrderProb lcmOrderCount
  have hfilter : ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro σ hσ hlcm
    have hdvd : d ∣ m := by rw [← hlcm]; exact Nat.dvd_lcm_left d (orderOf σ)
    exact h hdvd
  rw [hfilter, Finset.card_empty]
  norm_num

/-- The contribution of the "small" divisors `d ≤ n - √n` (i.e. `n - d ≥ √n`) to the recursion
sum is at most `τ(m)² / √n`. (Paper §3, line 224–225.) -/
lemma sum_small_lcmOrderProb_le (n m : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ Nat.sqrt n) :
    (∑ d ∈ Finset.Icc 1 (n - Nat.sqrt n), lcmOrderProb n d m) ≤
      (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) := by
  classical
  let s : ℕ := Nat.sqrt n
  have hs1 : 1 ≤ s := by dsimp [s]; exact hn
  have hs_le_n : s ≤ n := by dsimp [s]; exact Nat.sqrt_le_self n
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hm0 : m ≠ 0 := by omega
  have htau_pos : 0 < (tau m : ℝ) := by
    have h : 0 < tau m := by
      unfold tau
      exact Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm0⟩⟩
    exact_mod_cast h
  have hsum_le : (∑ d ∈ Finset.Icc 1 (n - s), lcmOrderProb n d m) ≤
      ∑ d ∈ Finset.Icc 1 (n - s), (if d ∣ m then (tau m : ℝ) / (s : ℝ) else 0) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    by_cases hdvd : d ∣ m
    · simp [hdvd]
      have hdn : d ≤ n - s := (Finset.mem_Icc.mp hd).2
      have hnd : 1 ≤ n - d := by omega
      have hle := lcmOrderProb_le_tau_div n d m hm hnd
      have hdiv : (tau m : ℝ) / ((n-d:ℕ):ℝ) ≤ (tau m : ℝ) / (s : ℝ) := by
        have hnd_ge_s : (s : ℝ) ≤ ((n-d:ℕ):ℝ) := by exact_mod_cast (by omega : s ≤ n - d)
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg (tau m)) hs_pos hnd_ge_s
      exact le_trans hle hdiv
    · simp [hdvd]
      exact le_of_eq (lcmOrderProb_eq_zero_of_not_dvd (n := n) hdvd)
  have hfilter_count : (Finset.Icc 1 (n - s)).filter (fun d => d ∣ m) ⊆ m.divisors := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Nat.mem_divisors]
    exact ⟨hd.2, hm0⟩
  have hcard_le : ((Finset.Icc 1 (n - s)).filter (fun d => d ∣ m)).card ≤ tau m := by
    simpa [tau] using Finset.card_le_card hfilter_count
  calc (∑ d ∈ Finset.Icc 1 (n - s), lcmOrderProb n d m)
      ≤ ∑ d ∈ Finset.Icc 1 (n - s), (if d ∣ m then (tau m : ℝ) / (s : ℝ) else 0) := hsum_le
    _ = ∑ d ∈ (Finset.Icc 1 (n - s)).filter (fun d => d ∣ m), (tau m : ℝ) / (s : ℝ) := by
          rw [Finset.sum_filter]
    _ = (((Finset.Icc 1 (n - s)).filter (fun d => d ∣ m)).card : ℝ) * ((tau m : ℝ) / (s : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (tau m : ℝ) * ((tau m : ℝ) / (s : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (le_of_lt (div_pos htau_pos hs_pos))
    _ = (tau m : ℝ)^2 / (s : ℝ) := by ring

/-- Each recursion summand is a probability, so `lcmOrderProb n d m ≤ 1`. -/
lemma lcmOrderProb_le_one (n d m : ℕ) : lcmOrderProb n d m ≤ 1 := by
  unfold lcmOrderProb lcmOrderCount
  have hle : (((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card : ℝ) ≤
      (Nat.factorial (n - d) : ℝ) := by
    have h := Finset.card_le_univ ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m))
    rw [card_symmetricGroup (n-d)] at h
    exact_mod_cast h
  exact div_le_one_of_le₀ hle (by positivity)

/-- If `n - s + 1 ≤ d` with `s ≤ n` and `s ≤ √n`, then `d > n - √n`. -/
lemma large_d_gt_sub_sqrt {n s d : ℕ} (hs_le_n : s ≤ n) (hs_le_sqrt : (s:ℝ) ≤ Real.sqrt (n:ℝ))
    (hdge : n - s + 1 ≤ d) : (n : ℝ) - Real.sqrt (n : ℝ) < (d : ℝ) := by
  have h1 : (n : ℝ) - (s : ℝ) < ((n - s + 1 : ℕ) : ℝ) := by
    have hcast : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := by rw [Nat.cast_sub hs_le_n]
    have hlt : ((n - s : ℕ) : ℝ) < ((n - s + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_succ_self (n - s))
    rwa [← hcast]
  have h2 : ((n - s + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdge
  have h3 : (n : ℝ) - (s : ℝ) < (d : ℝ) := lt_of_lt_of_le h1 h2
  have h4 : (n : ℝ) - Real.sqrt (n : ℝ) ≤ (n : ℝ) - (s : ℝ) := sub_le_sub_left hs_le_sqrt (n : ℝ)
  exact lt_of_le_of_lt h4 h3

/-- **At most one large divisor**: `m` has at most one divisor in `(n - √n, n]`. This is the
"two divisors" argument packaged as a cardinality bound on the large divisors. -/
lemma card_filter_large_dvd_le_one (n m : ℕ) (hn : 64 ≤ n) (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) (hmpos : 0 < m) :
    ((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)).card ≤ 1 := by
  classical
  let s : ℕ := Nat.sqrt n
  have hs_le_n : s ≤ n := by dsimp [s]; exact Nat.sqrt_le_self n
  have hs_le_sqrt : (s : ℝ) ≤ Real.sqrt (n : ℝ) := nat_sqrt_le_real_sqrt n
  apply Finset.card_le_one.mpr
  intro d₁ hd₁ d₂ hd₂
  have hd₁m : d₁ ∣ m := (Finset.mem_filter.mp hd₁).2
  have hd₂m : d₂ ∣ m := (Finset.mem_filter.mp hd₂).2
  have hd₁in : d₁ ∈ Finset.Icc (n - s + 1) n := (Finset.mem_filter.mp hd₁).1
  have hd₂in : d₂ ∈ Finset.Icc (n - s + 1) n := (Finset.mem_filter.mp hd₂).1
  have hd₁le : d₁ ≤ n := (Finset.mem_Icc.mp hd₁in).2
  have hd₂le : d₂ ≤ n := (Finset.mem_Icc.mp hd₂in).2
  have hd₁gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₁ : ℝ) :=
    large_d_gt_sub_sqrt hs_le_n hs_le_sqrt (Finset.mem_Icc.mp hd₁in).1
  have hd₂gt : (n : ℝ) - Real.sqrt (n : ℝ) < (d₂ : ℝ) :=
    large_d_gt_sub_sqrt hs_le_n hs_le_sqrt (Finset.mem_Icc.mp hd₂in).1
  exact two_divisors_contradict n m d₁ d₂ hn hm hmpos hd₁m hd₂m hd₁gt hd₂gt hd₁le hd₂le

/-! ### The q-prime-power dichotomy (valuation-free core of the Erdős–Turán step) -/

/-- If `q | m` and `lcm(d, x) = m` and `q ∤ d` (q a prime power), then `q | x`. -/
lemma dvd_orderOf_of_lcm_eq_of_dvd {q d m x : ℕ} (hq : IsPrimePow q) (hqd : ¬ q ∣ d)
    (hqm : q ∣ m) (hlcm : Nat.lcm d x = m) : q ∣ x := by
  have hq_lcm : q ∣ Nat.lcm d x := by rw [hlcm]; exact hqm
  have h := (dvd_lcm_iff_of_isPrimePow hq).mp hq_lcm
  exact h.resolve_left hqd

/-- If `q ∤ m` and `lcm(d, x) = m` (q a prime power), then `q ∤ x`. -/
lemma not_dvd_orderOf_of_lcm_eq_of_not_dvd {q d m x : ℕ} (hq : IsPrimePow q)
    (hqm : ¬ q ∣ m) (hlcm : Nat.lcm d x = m) : ¬ q ∣ x := by
  intro hqx
  have hq_lcm : q ∣ Nat.lcm d x := (dvd_lcm_iff_of_isPrimePow hq).mpr (Or.inr hqx)
  rw [hlcm] at hq_lcm
  exact hqm hq_lcm

/-- If `q | m`, then `#{q ∤ ord} ≤ #{lcm(d, ord) ≠ m}`. -/
lemma count_orderNotDiv_le_count_lcm_ne_of_dvd {q d m n : ℕ} (hq : IsPrimePow q) (hqd : ¬ q ∣ d) (hqm : q ∣ m) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => ¬ q ∣ orderOf σ)).card ≤
      ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => Nat.lcm d (orderOf σ) ≠ m)).card := by
  refine Finset.card_le_card ?_
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨hσ.1, by
    intro hlcm
    have hqσ : q ∣ orderOf σ := dvd_orderOf_of_lcm_eq_of_dvd hq hqd hqm hlcm
    exact hσ.2 hqσ⟩

/-- If `q ∤ m`, then `#{q | ord} ≤ #{lcm(d, ord) ≠ m}`. -/
lemma count_orderDiv_le_count_lcm_ne_of_not_dvd {q d m n : ℕ} (hq : IsPrimePow q) (hqm : ¬ q ∣ m) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => q ∣ orderOf σ)).card ≤
      ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => Nat.lcm d (orderOf σ) ≠ m)).card := by
  refine Finset.card_le_card ?_
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨hσ.1, by
    intro hlcm
    have hqσ : ¬ q ∣ orderOf σ := not_dvd_orderOf_of_lcm_eq_of_not_dvd hq hqm hlcm
    exact hqσ hσ.2⟩

/-- `1 - lcmOrderProb n d m = P(lcm(d, ord) ≠ m)`. -/
lemma one_sub_lcmOrderProb_eq (n d m : ℕ) :
    1 - lcmOrderProb n d m =
      (((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) ≠ m)).card : ℝ) /
        (Nat.factorial (n - d) : ℝ) := by
  let A := (Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)
  let B := (Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) ≠ m)
  have hpart : A.card + B.card = Nat.factorial (n - d) := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (SymmetricGroup (n - d)))) (fun σ => Nat.lcm d (orderOf σ) = m)
    rw [Finset.card_univ, card_symmetricGroup] at h
    exact h
  have hcast_part : (A.card : ℝ) + (B.card : ℝ) = (Nat.factorial (n - d) : ℝ) := by
    exact_mod_cast hpart
  have hfac : (Nat.factorial (n - d) : ℝ) ≠ 0 := by positivity
  unfold lcmOrderProb lcmOrderCount
  change (1 : ℝ) - (A.card : ℝ) / (Nat.factorial (n - d) : ℝ) = (B.card : ℝ) / (Nat.factorial (n - d) : ℝ)
  rw [show (1 : ℝ) = (Nat.factorial (n - d) : ℝ) / (Nat.factorial (n - d) : ℝ) by exact (div_self hfac).symm]
  rw [div_sub_div_same]
  rw [show (Nat.factorial (n - d) : ℝ) - (A.card : ℝ) = (B.card : ℝ) by nlinarith [hcast_part]]

/-- `1 - orderNotDivByProb q n = P(q | ord)`. -/
lemma one_sub_orderNotDivByProb_eq (q n : ℕ) :
    1 - orderNotDivByProb q n =
      (((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => q ∣ orderOf σ)).card : ℝ) /
        (Nat.factorial n : ℝ) := by
  let A := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => q ∣ orderOf σ)
  let B := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => ¬ q ∣ orderOf σ)
  have hpart : A.card + B.card = Nat.factorial n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (SymmetricGroup n))) (fun σ => q ∣ orderOf σ)
    rw [Finset.card_univ, card_symmetricGroup] at h
    exact h
  have hcast_part : (A.card : ℝ) + (B.card : ℝ) = (Nat.factorial n : ℝ) := by
    exact_mod_cast hpart
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  unfold orderNotDivByProb orderNotDivByCount
  change (1 : ℝ) - (B.card : ℝ) / (Nat.factorial n : ℝ) = (A.card : ℝ) / (Nat.factorial n : ℝ)
  rw [show (1 : ℝ) = (Nat.factorial n : ℝ) / (Nat.factorial n : ℝ) by exact (div_self hfac).symm]
  rw [div_sub_div_same]
  rw [show (Nat.factorial n : ℝ) - (B.card : ℝ) = (A.card : ℝ) by nlinarith [hcast_part]]

/-! ### The split of the recursion sum into small and large divisors -/

/-- Split the recursion sum at `d = n - √n`: `pₙ(m)` is at most the (weighted) large part
plus a `τ(m)²/(n·√n)` error coming from the small divisors. -/
lemma p_le_sum_large_add_tau_sq_div (n m : ℕ) [NeZero n] (hm : 1 ≤ m) (hn : 1 ≤ Nat.sqrt n) :
    p n m ≤ (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m)
      + (tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ)) := by
  let s : ℕ := Nat.sqrt n
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hsplit : (∑ d ∈ Finset.Icc 1 n, lcmOrderProb n d m) =
      (∑ d ∈ Finset.Icc 1 (n - s), lcmOrderProb n d m) + (∑ d ∈ Finset.Icc (n - s + 1) n, lcmOrderProb n d m) := by
    have h := (Finset.sum_Ico_consecutive (f := fun d => lcmOrderProb n d m) (m := 1) (n := n - s + 1) (k := n + 1) (by omega : 1 ≤ n - s + 1) (by omega : n - s + 1 ≤ n + 1)).symm
    rw [Finset.Ico_add_one_right_eq_Icc (1 : ℕ) n] at h
    rw [Finset.Ico_add_one_right_eq_Icc (1 : ℕ) (n - s)] at h
    rw [Finset.Ico_add_one_right_eq_Icc (n - s + 1) n] at h
    exact h
  have hsmall : (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc 1 (n - s), lcmOrderProb n d m) ≤
      (1 / (n : ℝ)) * ((tau m : ℝ)^2 / (s : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (by simpa [s] using (sum_small_lcmOrderProb_le n m hm hn)) (le_of_lt (one_div_pos.mpr hnposR))
  have halg : (1 / (n : ℝ)) * ((tau m : ℝ)^2 / (s : ℝ)) = (tau m : ℝ)^2 / ((n : ℝ) * (s : ℝ)) := by
    field_simp [ne_of_gt hnposR, ne_of_gt hs_pos]
  calc p n m
      = (1 / (n : ℝ)) * ∑ d ∈ Finset.Icc 1 n, lcmOrderProb n d m := p_eq_sum_recursion m
    _ = (1 / (n : ℝ)) * ((∑ d ∈ Finset.Icc 1 (n - s), lcmOrderProb n d m) + (∑ d ∈ Finset.Icc (n - s + 1) n, lcmOrderProb n d m)) := by
          rw [hsplit]
    _ = (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc 1 (n - s), lcmOrderProb n d m) + (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc (n - s + 1) n, lcmOrderProb n d m) := by
          rw [mul_add]
    _ ≤ (1 / (n : ℝ)) * ((tau m : ℝ)^2 / (s : ℝ)) + (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc (n - s + 1) n, lcmOrderProb n d m) := by
          exact add_le_add hsmall (le_refl _)
    _ = (tau m : ℝ)^2 / ((n : ℝ) * (s : ℝ)) + (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc (n - s + 1) n, lcmOrderProb n d m) := by
          rw [halg]
    _ = (1 / (n : ℝ)) * (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) + (tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ)) := by
          simp [s]
          ring

/-- The large part of the recursion sum is concentrated on divisors of `m`; the sum equals the
sum over `d ∣ m` in the large interval. -/
lemma sum_large_eq_filter_dvd (n m : ℕ) :
    (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) =
      (∑ d ∈ (Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m), lcmOrderProb n d m) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdvd : d ∣ m
  · simp [hdvd]
  · simp [hdvd, lcmOrderProb_eq_zero_of_not_dvd hdvd]

/-! ### Consequences of the split: `n - d ≤ 2τ(m)` and the harmonic bound -/

/-- `1/2 ≤ lcmOrderProb n d m` forces `n - d ≤ 2τ(m)` (via `lcmOrderProb ≤ τ(m)/(n-d)`). -/
lemma n_sub_d_le_two_mul_tau_of_lcmOrderProb_ge (n d m : ℕ) (hm : 1 ≤ m) (hn_d : 1 ≤ n - d)
    (hprob : (1 : ℝ) / 2 ≤ lcmOrderProb n d m) :
    n - d ≤ 2 * tau m := by
  have hle := lcmOrderProb_le_tau_div n d m hm hn_d
  have h : (1 : ℝ) / 2 ≤ (tau m : ℝ) / ((n - d : ℕ) : ℝ) := le_trans hprob hle
  have hnd_pos : 0 < ((n - d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - d)
  have h' : ((n - d : ℕ) : ℝ) ≤ 2 * (tau m : ℝ) := by
    have h'' : (1 / 2 : ℝ) * ((n - d : ℕ) : ℝ) ≤ (tau m : ℝ) := (le_div_iff₀ hnd_pos).mp h
    nlinarith
  exact_mod_cast h'

/-- `log x ≤ 2·√x` for `0 ≤ x` (from `log ≤ id` applied to `√x`). -/
lemma log_le_two_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  by_cases h0 : x = 0
  · simp [h0]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h : Real.log (Real.sqrt x) ≤ Real.sqrt x := Real.log_le_self hs
    have hlogsqrt : Real.log (Real.sqrt x) = (1 / 2 : ℝ) * Real.log x := by
      rw [Real.log_sqrt hx]
      ring
    rw [hlogsqrt] at h
    nlinarith

/-- `√q ≤ q/5` for `q ≥ 25`. -/
lemma sqrt_le_div_five_of_ge_25 (q : ℕ) (hq : 25 ≤ q) :
    Real.sqrt (q : ℝ) ≤ (q : ℝ) / 5 := by
  have hqle : (q : ℝ) ≤ ((q : ℝ) / 5)^2 := by
    have h25 : (25 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hqR_nonneg : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith [mul_le_mul_of_nonneg_left h25 hqR_nonneg]
  have hsqrt_le := Real.sqrt_le_sqrt hqle
  have hright : Real.sqrt (((q : ℝ) / 5)^2) = (q : ℝ) / 5 := by
    rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg q) (by norm_num : 0 ≤ (5 : ℝ)))]
  rwa [hright] at hsqrt_le

/-- `(1 + log q)/q < 1/2` for `q ≥ 25`. -/
lemma one_add_log_div_lt_half_of_ge_25 (q : ℕ) (hq : 25 ≤ q) :
    (1 + Real.log (q : ℝ)) / (q : ℝ) < (1 / 2 : ℝ) := by
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog : Real.log (q : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := log_le_two_sqrt (q : ℝ) (Nat.cast_nonneg q)
  have hsqrt : Real.sqrt (q : ℝ) ≤ (q : ℝ) / 5 := sqrt_le_div_five_of_ge_25 q hq
  have h1 : (1 : ℝ) ≤ (q : ℝ) / 25 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 25)]
    norm_num
    exact_mod_cast hq
  have hmain : 1 + Real.log (q : ℝ) ≤ (q : ℝ) * (11 / 25 : ℝ) := by
    nlinarith [hlog, hsqrt, h1]
  have hhalf : (q : ℝ) * (11 / 25 : ℝ) < (q : ℝ) * (1 / 2 : ℝ) := by
    exact mul_lt_mul_of_pos_left (by norm_num : (11 / 25 : ℝ) < (1 / 2 : ℝ)) hq_pos
  rw [div_lt_iff₀ hq_pos]
  exact lt_of_le_of_lt hmain (by simpa [mul_comm] using hhalf)

/-- `(1 + log q)/q ≥ 1/2` forces `q ≤ 24`. -/
lemma le_24_of_one_add_log_div_ge_half (q : ℕ) (h : (1 : ℝ) / 2 ≤ (1 + Real.log (q : ℝ)) / (q : ℝ)) :
    q ≤ 24 := by
  by_contra hq
  have hq25 : 25 ≤ q := by omega
  exact not_lt_of_ge h (one_add_log_div_lt_half_of_ge_25 q hq25)

/-- **The Erdős–Turán harmonic tail**: for `1 ≤ q` and `N/q ≤ q`,
`Σ_{j=1}^{⌊N/q⌋} 1/(jq) ≤ (1 + log q)/q`. -/
lemma sum_inv_jq_le_one_add_log_div_q (q N : ℕ) (hq : 1 ≤ q) (hN : N / q ≤ q) :
    (∑ j ∈ Finset.range (N / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))) ≤
      (1 + Real.log (q : ℝ)) / (q : ℝ) := by
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hrew : (∑ j ∈ Finset.range (N / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))) =
      (1 / (q : ℝ)) * (harmonic (N / q) : ℝ) := by
    rw [show (harmonic (N / q) : ℝ) = ∑ i ∈ Finset.range (N / q), (1 : ℝ) / ((i + 1 : ℕ) : ℝ) by
          simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hq_ne, (by exact_mod_cast (by omega : (j + 1 : ℕ) ≠ 0))]
  rw [hrew]
  have hharm : (harmonic (N / q) : ℝ) ≤ 1 + Real.log (q : ℝ) := by
    have h1 : (harmonic (N / q) : ℝ) ≤ 1 + Real.log ((N / q : ℕ) : ℝ) := by
      exact_mod_cast (harmonic_le_one_add_log (N / q))
    have hlog : Real.log ((N / q : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
      by_cases h0 : N / q = 0
      · simp [h0, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hq)
      · have hpos : 0 < ((N / q : ℕ) : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)
        exact Real.log_le_log hpos (by exact_mod_cast hN)
    nlinarith
  have hle : (1 / (q : ℝ)) * (harmonic (N / q) : ℝ) ≤ (1 / (q : ℝ)) * (1 + Real.log (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hharm (le_of_lt (one_div_pos.mpr hq_pos))
  rwa [show (1 / (q : ℝ)) * (1 + Real.log (q : ℝ)) = (1 + Real.log (q : ℝ)) / (q : ℝ) by
    rw [div_eq_mul_inv]
    ring] at hle

/-- **The q-prime-power dichotomy**: for a prime power `q` with `q ∤ d`,
`min(P(q | ord), P(q ∤ ord)) ≤ P(lcm(d, ord) ≠ m)`. (Paper §3, line 238–240.) -/
lemma min_orderNotDivByProb_le_one_sub_lcmOrderProb (n d m q : ℕ) (hq : IsPrimePow q) (hqd : ¬ q ∣ d) :
    min (orderNotDivByProb q (n - d)) (1 - orderNotDivByProb q (n - d)) ≤ 1 - lcmOrderProb n d m := by
  by_cases hqm : q ∣ m
  · have hsub := count_orderNotDiv_le_count_lcm_ne_of_dvd (n := n - d) hq hqd hqm
    have hle : orderNotDivByProb q (n - d) ≤ 1 - lcmOrderProb n d m := by
      unfold orderNotDivByProb orderNotDivByCount
      rw [one_sub_lcmOrderProb_eq]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
    exact le_trans (min_le_left _ _) hle
  · have hsub := count_orderDiv_le_count_lcm_ne_of_not_dvd (d := d) (n := n - d) hq hqm
    have hle : 1 - orderNotDivByProb q (n - d) ≤ 1 - lcmOrderProb n d m := by
      rw [one_sub_orderNotDivByProb_eq, one_sub_lcmOrderProb_eq]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
    exact le_trans (min_le_right _ _) hle

/-! ### The "maximal prime power" extraction -/

/-- `lcm(1,…,N) | d` iff every prime power `q ≤ N` divides `d`. -/
lemma dvd_lcm1to_iff_prime_pow_dvd (N d : ℕ) :
    lcm1to N ∣ d ↔ ∀ q, IsPrimePow q → q ≤ N → q ∣ d := by
  constructor
  · intro h q hq hqN
    have hq_ge1 : 1 ≤ q := le_trans (by norm_num : (1:ℕ) ≤ 2) (IsPrimePow.two_le hq)
    have hq_mem : q ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hq_ge1, hqN⟩
    have hq_lcm : q ∣ lcm1to N := by
      unfold lcm1to
      exact Finset.dvd_lcm hq_mem
    exact dvd_trans hq_lcm h
  · intro h
    by_cases hd0 : d = 0
    · subst d
      exact dvd_zero _
    · unfold lcm1to
      apply Finset.lcm_dvd
      intro t ht
      have htN : t ≤ N := (Finset.mem_Icc.mp ht).2
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have ht0 : t ≠ 0 := by omega
      change t ∣ d
      rw [← Nat.factorization_le_iff_dvd ht0 hd0]
      intro p
      by_cases hfp : t.factorization p = 0
      · simp [hfp]
      · have hpk_dvd_prod : p ^ (t.factorization p) ∣
            ∏ i ∈ (t.factorization : ℕ →₀ ℕ).support, i ^ ((t.factorization : ℕ →₀ ℕ) i) := by
          exact Finset.dvd_prod_of_mem (f := fun i => i ^ ((t.factorization : ℕ →₀ ℕ) i)) (by
            rw [Finsupp.mem_support_iff]
            exact hfp)
        have hprod_eq : (∏ i ∈ (t.factorization : ℕ →₀ ℕ).support, i ^ ((t.factorization : ℕ →₀ ℕ) i)) = t := by
          simpa using (Nat.prod_factorization_pow_eq_self ht0)
        have hpk_dvd_t : p ^ (t.factorization p) ∣ t := by
          rwa [hprod_eq] at hpk_dvd_prod
        have hpk_le : p ^ (t.factorization p) ≤ N := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hpk_dvd_t) htN
        have hp_prime : p.Prime := by
          exact Nat.prime_of_mem_primeFactors (by
            change p ∈ (t.factorization : ℕ →₀ ℕ).support
            rw [Finsupp.mem_support_iff]
            exact hfp)
        have hpp : IsPrimePow (p ^ (t.factorization p)) := by
          exact IsPrimePow.pow (Nat.Prime.isPrimePow hp_prime) (by omega : t.factorization p ≠ 0)
        have hpk_dvd_d : p ^ (t.factorization p) ∣ d := h _ hpp hpk_le
        have hle : t.factorization p ≤ d.factorization p := by
          exact (Nat.Prime.pow_dvd_iff_le_factorization hp_prime hd0).mp hpk_dvd_d
        exact hle

/-- If `lcm(1,…,N) ∤ d` (with `N ≥ 2`), then there is a prime power `q` with
`q ≤ N`, `q² > N` and `q ∤ d`. (Paper §3: the "largest power of `p` not exceeding `N`".) -/
lemma exists_prime_pow_not_dvd_of_not_dvd_lcm1to {N d : ℕ} (hN : 2 ≤ N) (h : ¬ lcm1to N ∣ d) :
    ∃ q : ℕ, IsPrimePow q ∧ q ≤ N ∧ q * q > N ∧ ¬ q ∣ d := by
  have hnot : ¬ ∀ q, IsPrimePow q → q ≤ N → q ∣ d := by
    intro h'
    exact h ((dvd_lcm1to_iff_prime_pow_dvd N d).mpr h')
  push_neg at hnot
  rcases hnot with ⟨q, hq, hqN, hqd⟩
  rcases (isPrimePow_nat_iff q).mp hq with ⟨p, k, hp, hk_pos, hpq⟩
  have hpk_dvd_q : p ∣ q := by
    rw [← hpq]
    exact dvd_pow_self p (Nat.ne_of_gt hk_pos)
  have hq_pos : 0 < q := by
    rw [← hpq]
    exact pow_pos (Nat.Prime.pos hp) k
  have hp_le_N : p ≤ N := le_trans (Nat.le_of_dvd hq_pos hpk_dvd_q) hqN
  let qmax := p ^ Nat.log p N
  have hlog_pos : 0 < Nat.log p N := Nat.log_pos (Nat.Prime.one_lt hp) hp_le_N
  have hlog_ne : Nat.log p N ≠ 0 := Nat.ne_of_gt hlog_pos
  refine ⟨qmax, ?_, ?_, ?_, ?_⟩
  · dsimp [qmax]
    exact IsPrimePow.pow (Nat.Prime.isPrimePow hp) hlog_ne
  · dsimp [qmax]
    exact Nat.pow_log_le_self p (by omega : N ≠ 0)
  · dsimp [qmax]
    have hlt : N < p ^ (Nat.log p N + 1) := Nat.lt_pow_succ_log_self (Nat.Prime.one_lt hp) N
    have hpow : p ^ (Nat.log p N + 1) = p ^ Nat.log p N * p := by rw [Nat.pow_succ]
    have hp_le_qmax : p ≤ p ^ Nat.log p N := by
      exact Nat.le_self_pow (n := Nat.log p N) hlog_ne p
    have hle : p ^ Nat.log p N * p ≤ (p ^ Nat.log p N) * (p ^ Nat.log p N) := by
      exact Nat.mul_le_mul_left _ hp_le_qmax
    exact lt_of_lt_of_le (by rwa [hpow] at hlt) hle
  · dsimp [qmax]
    intro hqmax_dvd_d
    have hk_le_log : k ≤ Nat.log p N :=
      Nat.le_log_of_pow_le (Nat.Prime.one_lt hp) (by simpa [hpq] using hqN)
    have hq_dvd_qmax : q ∣ p ^ Nat.log p N := by
      rw [← hpq]
      exact Nat.pow_dvd_pow p hk_le_log
    exact hqd (dvd_trans hq_dvd_qmax hqmax_dvd_d)

/-! ### Structural consequences: `m = d` and the identity lower bound -/

/-- The order of a permutation of `N` points divides `lcm(1,…,N)` (its cycle lengths are all ≤ N). -/
lemma orderOf_dvd_lcm1to {N : ℕ} (σ : SymmetricGroup N) : orderOf σ ∣ lcm1to N := by
  rw [← Equiv.Perm.lcm_cycleType σ]
  unfold lcm1to
  apply Multiset.lcm_dvd.mpr
  intro t ht
  have ht_le : t ≤ N := le_trans (Multiset.single_le_sum (fun x _ => Nat.zero_le x) t ht) (by
    simpa [Fintype.card_fin] using (Equiv.Perm.sum_cycleType_le σ))
  have ht_mem : t ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨
    (le_trans (by norm_num : (1:ℕ) ≤ 2) (Equiv.Perm.two_le_of_mem_cycleType ht)), ht_le⟩
  exact Finset.dvd_lcm ht_mem

/-- `lcmOrderProb n d m > 0` forces the existence of `σ` with `lcm(d, ord σ) = m`. -/
lemma exists_of_lcmOrderProb_pos {n d m : ℕ} (h : 0 < lcmOrderProb n d m) :
    ∃ σ : SymmetricGroup (n-d), Nat.lcm d (orderOf σ) = m := by
  unfold lcmOrderProb lcmOrderCount at h
  have hcard : 0 < ((Finset.univ : Finset (SymmetricGroup (n-d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card := by
    have hfac_pos : 0 < (Nat.factorial (n-d) : ℝ) := by positivity
    have hfac_ne : (Nat.factorial (n-d) : ℝ) ≠ 0 := ne_of_gt hfac_pos
    have h' : 0 < (((Finset.univ : Finset (SymmetricGroup (n-d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card : ℝ) / (Nat.factorial (n-d) : ℝ) * (Nat.factorial (n-d) : ℝ) := mul_pos h hfac_pos
    rw [div_mul_cancel₀ (((Finset.univ : Finset (SymmetricGroup (n-d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card : ℝ) hfac_ne] at h'
    exact_mod_cast h'
  rcases Finset.card_pos.mp hcard with ⟨σ, hσ⟩
  exact ⟨σ, (Finset.mem_filter.mp hσ).2⟩

/-- If `lcm(1,…,n-d) | d` and there is `σ` with `lcm(d, ord σ) = m`, then `m = d`. -/
lemma m_eq_d_of_lcm1to_dvd {n d m : ℕ} (hlcm : lcm1to (n-d) ∣ d)
    (hσ : ∃ σ : SymmetricGroup (n-d), Nat.lcm d (orderOf σ) = m) : m = d := by
  rcases hσ with ⟨σ, hlcm_eq⟩
  have hord_dvd : orderOf σ ∣ d := by
    exact dvd_trans (orderOf_dvd_lcm1to σ) hlcm
  calc m = Nat.lcm d (orderOf σ) := hlcm_eq.symm
    _ = d := Nat.lcm_eq_left hord_dvd

/-- The probability that `q ∤ ord` is at least `1/N!` (the identity permutation). -/
lemma orderNotDivByProb_ge_inv_factorial (q N : ℕ) (hq : 2 ≤ q) :
    (1 : ℝ) / (Nat.factorial N : ℝ) ≤ orderNotDivByProb q N := by
  unfold orderNotDivByProb orderNotDivByCount
  have hmem : (1 : SymmetricGroup N) ∈ ((Finset.univ : Finset (SymmetricGroup N)).filter (fun σ => ¬ q ∣ orderOf σ)) := by
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · intro hq1
      have horder : orderOf (1 : SymmetricGroup N) = 1 := orderOf_one
      rw [horder] at hq1
      have hq_le : q ≤ 1 := Nat.le_of_dvd (by norm_num : (0:ℕ) < 1) hq1
      omega
  have hcard : 1 ≤ ((Finset.univ : Finset (SymmetricGroup N)).filter (fun σ => ¬ q ∣ orderOf σ)).card := by
    exact Finset.card_pos.mpr ⟨1, hmem⟩
  calc (1 : ℝ) / (Nat.factorial N : ℝ)
      ≤ (((Finset.univ : Finset (SymmetricGroup N)).filter (fun σ => ¬ q ∣ orderOf σ)).card : ℝ) / (Nat.factorial N : ℝ) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = orderNotDivByProb q N := by rfl

/-- **The q-prime-power contradiction (assembled)**: if `1 - lcmOrderProb n d m ≤ C₁ n^{-1/3}`
and `n-d ≤ B n^{1/12}` (with `n` large enough), then `lcm(1,…,n-d) | d`. (Paper §3, lines 234–246.) -/
lemma lcm1to_dvd_of_large_prob (n d m : ℕ) (C₁ B : ℝ)
    (hsub : 1 - lcmOrderProb n d m ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)))
    (hnd : ((n - d : ℕ) : ℝ) ≤ B * (n : ℝ) ^ (1 / 12 : ℝ))
    (hn_large : C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) < (1 : ℝ) / (B * (n : ℝ) ^ (1 / 12 : ℝ)))
    (hn_mid : (1 : ℝ) / 2 ≤ 1 - C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)))
    (hn_final : C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) < (1 : ℝ) / (Nat.factorial 575 : ℝ))
    : lcm1to (n - d) ∣ d := by
  by_contra hnot
  have hn_d_ge2 : 2 ≤ n - d := by
    by_contra hlt
    have hnd_le1 : n - d ≤ 1 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
    have hlcm1 : lcm1to (n - d) = 1 := by
      cases hnd : n - d with
      | zero => simp [lcm1to]
      | succ k =>
          have : k = 0 := by omega
          subst k
          simp [lcm1to]
    rw [hlcm1] at hnot
    exact hnot (one_dvd d)
  rcases exists_prime_pow_not_dvd_of_not_dvd_lcm1to (N := n - d) (d := d) hn_d_ge2 hnot with ⟨q, hq, hq_le, hq_sq, hqd⟩
  have hq_le_B : (q : ℝ) ≤ B * (n : ℝ) ^ (1 / 12 : ℝ) := by
    exact le_trans (by exact_mod_cast hq_le) hnd
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hBpos : 0 < B := by
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (IsPrimePow.two_le hq)
    have hstrict : 0 < B * (n : ℝ) ^ (1 / 12 : ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_trans hq2 hq_le_B)
    have hnpos12_nonneg : 0 ≤ (n : ℝ) ^ (1 / 12 : ℝ) := le_of_lt (Real.rpow_pos_of_pos hn_pos _)
    exact pos_of_mul_pos_left hstrict hnpos12_nonneg
  let P_E := 1 - orderNotDivByProb q (n - d)
  let P_Ec := orderNotDivByProb q (n - d)
  have hET := erdosTuran_approx_prob q (n - d) hq hq_le
  have hPE_low : (1 : ℝ) / (B * (n : ℝ) ^ (1 / 12 : ℝ)) ≤ P_E := by
    dsimp [P_E]
    have h1q : (1 : ℝ) / (q : ℝ) ≤ 1 - orderNotDivByProb q (n - d) := hET.1
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (IsPrimePow.pos hq)
    have h1 : (1 : ℝ) / (B * (n : ℝ) ^ (1 / 12 : ℝ)) ≤ (1 : ℝ) / (q : ℝ) := by
      exact one_div_le_one_div_of_le hq_pos hq_le_B
    exact le_trans h1 h1q
  have hPE_gt : C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) < P_E := lt_of_lt_of_le hn_large hPE_low
  have hmin_le : min P_E P_Ec ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc min P_E P_Ec = min (orderNotDivByProb q (n - d)) (1 - orderNotDivByProb q (n - d)) := by
          dsimp [P_E, P_Ec]; rw [min_comm]
      _ ≤ 1 - lcmOrderProb n d m := min_orderNotDivByProb_le_one_sub_lcmOrderProb n d m q hq hqd
      _ ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := hsub
  have hmin_eq : min P_E P_Ec = P_Ec := by
    apply min_eq_right
    by_contra hnot
    have hmin_eq_PE : min P_E P_Ec = P_E := min_eq_left (le_of_lt (lt_of_not_ge hnot))
    have hcontra : P_E ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by rwa [hmin_eq_PE] at hmin_le
    exact (not_lt_of_ge hcontra) hPE_gt
  have hPEc_le : P_Ec ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by rwa [hmin_eq] at hmin_le
  have hsum_ge : (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.range ((n - d) / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ)) := by
    have hPEc_low : 1 - (∑ j ∈ Finset.range ((n - d) / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))) ≤ P_Ec := by
      dsimp [P_Ec]
      have h := hET.2
      nlinarith
    have hle : 1 - (∑ j ∈ Finset.range ((n - d) / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))) ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := le_trans hPEc_low hPEc_le
    calc (1 : ℝ) / 2 ≤ 1 - C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := hn_mid
      _ ≤ ∑ j ∈ Finset.range ((n - d) / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ)) := by nlinarith
  have hq_le_24 : q ≤ 24 := by
    have hsum_le : (∑ j ∈ Finset.range ((n - d) / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))) ≤ (1 + Real.log (q : ℝ)) / (q : ℝ) := by
      apply sum_inv_jq_le_one_add_log_div_q q (n - d) (by exact le_trans (by norm_num : (1:ℕ) ≤ 2) (IsPrimePow.two_le hq)) (by
        have hq_pos : 0 < q := IsPrimePow.pos hq
        have hlt : n - d < (q + 1) * q := by
          have h : q * q ≤ (q + 1) * q := Nat.mul_le_mul_right q (Nat.le_succ q)
          exact lt_of_lt_of_le hq_sq h
        have hdiv : (n - d) / q < q + 1 := (Nat.div_lt_iff_lt_mul hq_pos).mpr hlt
        exact Nat.lt_succ_iff.mp hdiv)
    have hge : (1 : ℝ) / 2 ≤ (1 + Real.log (q : ℝ)) / (q : ℝ) := le_trans hsum_ge hsum_le
    exact le_24_of_one_add_log_div_ge_half q hge
  have hnd_le_575 : n - d ≤ 575 := by
    have hq24 : q ≤ 24 := hq_le_24
    have hq2_le : q * q ≤ 576 := by
      exact Nat.mul_le_mul hq24 hq24
    have hlt : n - d < 576 := lt_of_lt_of_le hq_sq hq2_le
    exact Nat.lt_succ_iff.mp hlt
  have hPEc_low : (1 : ℝ) / (Nat.factorial 575 : ℝ) ≤ P_Ec := by
    dsimp [P_Ec]
    have h1 : (1 : ℝ) / (Nat.factorial (n-d) : ℝ) ≤ orderNotDivByProb q (n-d) := orderNotDivByProb_ge_inv_factorial q (n-d) (IsPrimePow.two_le hq)
    have hfac : (Nat.factorial (n-d) : ℝ) ≤ (Nat.factorial 575 : ℝ) := by
      exact_mod_cast (Nat.factorial_le hnd_le_575)
    have h2 : (1 : ℝ) / (Nat.factorial 575 : ℝ) ≤ (1 : ℝ) / (Nat.factorial (n-d) : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity : 0 < (Nat.factorial (n-d) : ℝ)) hfac
    exact le_trans h2 h1
  have hcontra : (1 : ℝ) / (Nat.factorial 575 : ℝ) ≤ C₁ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := le_trans hPEc_low hPEc_le
  exact (not_lt_of_ge hcontra) hn_final

/-! ### Assembly: Theorem 1.1 (characterization half) -/

/-- `τ(m) ≤ C^{1/16} · n^{1/12}` whenever `m < n^{4/3}`. -/
lemma tau_le_rpow_twelfth (n m C : ℕ) (hn : 0 < n) (hC : (tau m)^16 ≤ C * m) (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) :
    (tau m : ℝ) ≤ (C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ) := by
  have hnonneg : 0 ≤ (tau m : ℝ) := Nat.cast_nonneg _
  have hcast : (tau m : ℝ)^16 ≤ ((C * m : ℕ) : ℝ) := by exact_mod_cast hC
  have hmono : ((tau m : ℝ)^16)^(1/16 : ℝ) ≤ ((C * m : ℕ) : ℝ)^(1/16 : ℝ) :=
    Real.rpow_le_rpow (by positivity : 0 ≤ (tau m : ℝ)^16) hcast (by norm_num : 0 ≤ (1/16 : ℝ))
  have hrew : ((tau m : ℝ)^16)^(1/16 : ℝ) = (tau m : ℝ) := by
    rw [show (tau m : ℝ)^16 = (tau m : ℝ)^(16 : ℝ) by exact (Real.rpow_natCast (tau m : ℝ) 16).symm]
    rw [← Real.rpow_mul hnonneg (16 : ℝ) (1/16 : ℝ)]
    rw [show (tau m : ℝ)^((16 : ℝ) * (1/16 : ℝ)) = (tau m : ℝ)^(1 : ℝ) by congr 1; norm_num]
    rw [Real.rpow_one]
  rw [hrew] at hmono
  have hC_nonneg : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : ((C * m : ℕ) : ℝ)^(1/16 : ℝ) = (C : ℝ)^(1/16 : ℝ) * (m : ℝ)^(1/16 : ℝ) := by
    rw [Nat.cast_mul]
    exact Real.mul_rpow hC_nonneg hm_nonneg
  rw [h1] at hmono
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have h2 : (m : ℝ)^(1/16 : ℝ) ≤ (n : ℝ)^(1/12 : ℝ) := by
    have h3 : (m : ℝ)^(1/16 : ℝ) ≤ ((n : ℝ)^(4/3 : ℝ))^(1/16 : ℝ) := by
      exact Real.rpow_le_rpow (Nat.cast_nonneg m) (le_of_lt hm) (by norm_num : 0 ≤ (1/16 : ℝ))
    have h4 : ((n : ℝ)^(4/3 : ℝ))^(1/16 : ℝ) = (n : ℝ)^(1/12 : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hnpos) (4/3 : ℝ) (1/16 : ℝ)]
      congr 1; norm_num
    rwa [h4] at h3
  have hC16_nonneg : 0 ≤ (C : ℝ)^(1/16 : ℝ) := Real.rpow_nonneg hC_nonneg _
  exact le_trans hmono (mul_le_mul_of_nonneg_left h2 hC16_nonneg)

/-- `τ(m)²/(n·√n) ≤ 2C^{1/8} n^{-4/3}` whenever `m < n^{4/3}`. -/
lemma tau_sq_div_n_sqrt_le (n m C : ℕ) (hn : 0 < n) (hC : (tau m)^16 ≤ C * m) (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) :
    (tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ)) ≤ 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) := by
  have htau := tau_sq_div_n_pow_three_half_le_rpow n m C hn hC hm
  have hn_posR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs_pos : 0 < (Nat.sqrt n : ℝ) := by exact_mod_cast (Nat.sqrt_pos.mpr hn)
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := sqrt_le_two_mul_nat_sqrt n (by omega : 1 ≤ n)
  have hsqrt_eq : (n : ℝ)^(3/2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3/2 : ℝ) = (1 : ℝ) + (1/2 : ℝ) by norm_num]
    rw [Real.rpow_add hn_posR, Real.rpow_one]
    rw [Real.sqrt_eq_rpow]
  have hratio : (n : ℝ)^(3/2 : ℝ) / ((n : ℝ) * (Nat.sqrt n : ℝ)) ≤ 2 := by
    rw [hsqrt_eq]
    field_simp [ne_of_gt hn_posR, ne_of_gt hs_pos]
    nlinarith [hsqrt_le]
  have htau_mul : (tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ)) ≤ ((tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ)) * 2 := by
    have htau_nonneg : 0 ≤ (tau m : ℝ)^2 := sq_nonneg _
    have hdenom_pos : 0 < (n : ℝ) * (Nat.sqrt n : ℝ) := mul_pos hn_posR hs_pos
    have hn32_pos : 0 < (n : ℝ)^(3/2 : ℝ) := Real.rpow_pos_of_pos hn_posR _
    have hrew : (tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ)) = ((tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ)) * ((n : ℝ)^(3/2 : ℝ) / ((n : ℝ) * (Nat.sqrt n : ℝ))) := by
      field_simp [ne_of_gt hdenom_pos, ne_of_gt hn32_pos]
    rw [hrew]
    exact mul_le_mul_of_nonneg_left hratio (div_nonneg htau_nonneg (le_of_lt hn32_pos))
  have hfinal : ((tau m : ℝ)^2 / (n : ℝ)^(3/2 : ℝ)) * 2 ≤ (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) := by
    have h := mul_le_mul_of_nonneg_right htau (by norm_num : 0 ≤ (2 : ℝ))
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  exact le_trans htau_mul hfinal

/-- From a positive large sum, extract the (unique) large divisor `d₀`. -/
lemma exists_large_divisor_of_sum_pos (n m : ℕ) (hn : 64 ≤ n) (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) (hmpos : 0 < m)
    (hlarge : 0 < ∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) :
    ∃ d₀ : ℕ, d₀ ∣ m ∧ (n - Nat.sqrt n + 1 ≤ d₀) ∧ (d₀ ≤ n) ∧
      (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) = lcmOrderProb n d₀ m := by
  have hfilter_eq := sum_large_eq_filter_dvd n m
  have hcard := card_filter_large_dvd_le_one n m hn hm hmpos
  have hfilter_ne : ((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)).Nonempty := by
    by_contra hempty
    have hfilter_empty : ((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hfilter_eq, hfilter_empty, Finset.sum_empty] at hlarge
    norm_num at hlarge
  rcases hfilter_ne with ⟨d₀, hd₀mem⟩
  refine ⟨d₀, (Finset.mem_filter.mp hd₀mem).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₀mem).1).1, (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₀mem).1).2, ?_⟩
  rw [hfilter_eq]
  have hcard_le_one := Finset.card_le_one.mp hcard
  have hsub : ((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)) ⊆ ({d₀} : Finset ℕ) := by
    intro d hd
    simp [hcard_le_one d hd d₀ hd₀mem]
  have hsub' : ({d₀} : Finset ℕ) ⊆ ((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)) := by
    intro d hd; simp at hd; subst hd; exact hd₀mem
  have hseq : ((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)) = ({d₀} : Finset ℕ) := Finset.Subset.antisymm hsub hsub'
  rw [hseq]
  simp

/-- `p n m > 0` forces the existence of a permutation of order `m`. -/
lemma exists_of_p_pos (n m : ℕ) (h : 0 < p n m) : ∃ g : SymmetricGroup n, orderOf g = m := by
  unfold p at h
  have hcard : 0 < ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = m)).card := by
    have hfac_pos : 0 < (Nat.factorial n : ℝ) := by positivity
    have hfac_ne : (Nat.factorial n : ℝ) ≠ 0 := ne_of_gt hfac_pos
    have h' : 0 < (((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = m)).card : ℝ) / (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) := mul_pos h hfac_pos
    rw [div_mul_cancel₀ (((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = m)).card : ℝ) hfac_ne] at h'
    exact_mod_cast h'
  rcases Finset.card_pos.mp hcard with ⟨g, hg⟩
  exact ⟨g, (Finset.mem_filter.mp hg).2⟩

/-- The pointwise core of Theorem 1.1: under the quantitative hypotheses, `pₙ(m) ≥ 1/n` forces
`n - m ∈ Kₙ`. -/
lemma mem_K_of_p_ge (n m : ℕ) [NeZero n] (C : ℕ)
    (hC : (tau m)^16 ≤ C * m)
    (hn64 : 64 ≤ n) (hm1 : 1 ≤ m) (hm_lt : (m : ℝ) < (n : ℝ)^(4/3 : ℝ))
    (hp : (1 : ℝ) / (n : ℝ) ≤ p n m)
    (hlarge_pos : 0 < 1 - 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)))
    (hhalf : (1 : ℝ) / 2 ≤ 1 - 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)))
    (hn_large : 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) < (1 : ℝ) / ((2 * (C : ℝ)^(1/16 : ℝ)) * (n : ℝ)^(1/12 : ℝ)))
    (hn_final : 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) < (1 : ℝ) / (Nat.factorial 575 : ℝ))
    : (n - m ∈ K n) ∧ m ≤ n := by
  let C₁ : ℝ := 2 * (C : ℝ)^(1/8 : ℝ)
  let B : ℝ := 2 * (C : ℝ)^(1/16 : ℝ)
  have hn_pos : 0 < n := NeZero.pos n
  have hn_posR : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have hs_pos : 0 < (Nat.sqrt n : ℝ) := by exact_mod_cast (Nat.sqrt_pos.mpr hn_pos)
  have hs1 : 1 ≤ Nat.sqrt n := Nat.succ_le_iff.mp (Nat.sqrt_pos.mpr hn_pos)
  have hsplit := p_le_sum_large_add_tau_sq_div n m hm1 hs1
  have htau2 := tau_sq_div_n_sqrt_le n m C hn_pos hC hm_lt
  have hnp : (1 : ℝ) ≤ (n : ℝ) * p n m := by simpa [mul_comm] using ((div_le_iff₀ hn_posR).mp hp)
  have hnp_le : (n : ℝ) * p n m ≤ (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) + (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg n)
    rw [mul_add] at h
    rw [show (n : ℝ) * ((1 / (n : ℝ)) * ∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) =
        ∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m by
          field_simp [ne_of_gt hn_posR]] at h
    rw [show (n : ℝ) * ((tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ))) = (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) by
          field_simp [ne_of_gt hn_posR, ne_of_gt hs_pos]] at h
    exact h
  have hlarge_ge : 1 - C₁ * (n : ℝ)^(-(1/3 : ℝ)) ≤ (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) := by
    have h1 : (1 : ℝ) ≤ (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) + (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) := le_trans hnp hnp_le
    have htau_s : (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) ≤ C₁ * (n : ℝ)^(-(1/3 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left htau2 (Nat.cast_nonneg n)
      have hrew : (n : ℝ) * ((tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ))) = (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) := by
        field_simp [ne_of_gt hn_posR, ne_of_gt hs_pos]
      rw [hrew] at h
      have h2 : (n : ℝ) * (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) = C₁ * (n : ℝ)^(-(1/3 : ℝ)) := by
        dsimp [C₁]
        rw [show (n : ℝ) * (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) = 2 * (C : ℝ)^(1/8 : ℝ) * ((n : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) by ring]
        rw [show (n : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) = (n : ℝ)^(-(1/3 : ℝ)) by
          calc (n : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) := by rw [Real.rpow_one]
            _ = (n : ℝ)^((1 : ℝ) + (-(4/3 : ℝ))) := by rw [Real.rpow_add hn_posR]
            _ = (n : ℝ)^(-(1/3 : ℝ)) := by congr 1; norm_num]
      rwa [h2] at h
    nlinarith
  have hlarge_pos' : 0 < (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) := by
    exact lt_of_lt_of_le hlarge_pos hlarge_ge
  have hmpos : 0 < m := by omega
  rcases exists_large_divisor_of_sum_pos n m hn64 hm_lt hmpos hlarge_pos' with ⟨d₀, hd₀m, hd₀ge, hd₀le, hlarge_eq⟩
  have hprob_ge : (1 : ℝ) / 2 ≤ lcmOrderProb n d₀ m := by
    rw [← hlarge_eq]
    exact le_trans hhalf hlarge_ge
  have hsub : 1 - lcmOrderProb n d₀ m ≤ C₁ * (n : ℝ)^(-(1/3 : ℝ)) := by
    rw [← hlarge_eq]
    nlinarith [hlarge_ge]
  have hnd_le : ((n - d₀ : ℕ) : ℝ) ≤ B * (n : ℝ)^(1/12 : ℝ) := by
    by_cases h0 : n - d₀ = 0
    · simp [h0]
      have hB_nonneg : 0 ≤ B := by
        dsimp [B]
        have hC_nonneg : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
        have hC16_nonneg : 0 ≤ (C : ℝ)^(1/16 : ℝ) := Real.rpow_nonneg hC_nonneg _
        exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hC16_nonneg
      exact mul_nonneg hB_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · have h1 : 1 ≤ n - d₀ := Nat.pos_of_ne_zero h0
      have hle : n - d₀ ≤ 2 * tau m := n_sub_d_le_two_mul_tau_of_lcmOrderProb_ge n d₀ m hm1 h1 hprob_ge
      have htau_le : (tau m : ℝ) ≤ (C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ) := tau_le_rpow_twelfth n m C hn_pos hC hm_lt
      have hleR : ((n - d₀ : ℕ) : ℝ) ≤ 2 * ((C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ)) := by
        have h1R : ((n - d₀ : ℕ) : ℝ) ≤ 2 * (tau m : ℝ) := by exact_mod_cast hle
        have h2R : 2 * (tau m : ℝ) ≤ 2 * ((C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left htau_le (by norm_num : 0 ≤ (2 : ℝ))
        exact le_trans h1R h2R
      dsimp [B]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hleR
  have hlcm_dvd : lcm1to (n - d₀) ∣ d₀ := by
    apply lcm1to_dvd_of_large_prob n d₀ m C₁ B
    · exact hsub
    · exact hnd_le
    · exact hn_large
    · exact hhalf
    · exact hn_final
  have hprob_pos : 0 < lcmOrderProb n d₀ m := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hprob_ge
  have hm_eq : m = d₀ := by
    exact m_eq_d_of_lcm1to_dvd hlcm_dvd (exists_of_lcmOrderProb_pos hprob_pos)
  have hmn : m ≤ n := by rw [hm_eq]; exact hd₀le
  refine ⟨?_, hmn⟩
  simp only [K, Finset.mem_filter, Finset.mem_range]
  constructor
  · omega
  · have hlcm : lcm1to (n - m) ∣ m := by
      rw [hm_eq]
      exact hlcm_dvd
    have h : n - (n - m) = m := Nat.sub_sub_self hmn
    simpa [h] using hlcm

/-- **Theorem 1.1 (characterization half)**: for all sufficiently large `n`, if `pₙ(m) ≥ 1/n`
then `m = n - k` for some `k ∈ Kₙ` (witnessed here as `n - m ∈ Kₙ` together with `m ≤ n`,
so that `m = n - (n-m)`). -/
theorem p_ge_one_div_n_implies_mem_K :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (1 : ℝ) / (n : ℝ) ≤ p n m → (n - m ∈ K n) ∧ m ≤ n := by
  rcases tau_pow_sixteen_le with ⟨C, hC⟩
  have hCpos : 0 < (C : ℝ) := by
    have h := hC 1
    have htau1 : tau 1 = 1 := by simp [tau]
    have h' : (1 : ℝ) ≤ (C : ℝ) := by
      have hcast : (tau 1 : ℝ)^16 ≤ (C * 1 : ℝ) := by exact_mod_cast h
      simpa [htau1] using hcast
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h'
  have hninv : Tendsto (fun n : ℕ => (n : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := (1/3 : ℝ)) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) := by
    simpa using (hninv.const_mul (2 * (C : ℝ)^(1/8 : ℝ)))
  have hhalf_ev : ∀ᶠ (n : ℕ) in atTop, (1 : ℝ) / 2 ≤ 1 - 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by
    filter_upwards [hconst.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with n hn
    nlinarith
  have hlarge_pos_ev : ∀ᶠ (n : ℕ) in atTop, 0 < 1 - 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by
    filter_upwards [hhalf_ev] with n hn
    nlinarith
  have hn_large_ev : ∀ᶠ (n : ℕ) in atTop, 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) < (1 : ℝ) / ((2 * (C : ℝ)^(1/16 : ℝ)) * (n : ℝ)^(1/12 : ℝ)) := by
    have hneg14 : Tendsto (fun n : ℕ => (n : ℝ)^(-(1/4 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := (1/4 : ℝ)) (by norm_num)).comp tendsto_natCast_atTop_atTop
    have hf : Tendsto (fun n : ℕ => (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) * (2 * (C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ))) atTop (𝓝 0) := by
      have hrew : (fun n : ℕ => (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) * (2 * (C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ))) =
          (fun n : ℕ => 4 * (C : ℝ)^(3/16 : ℝ) * (n : ℝ)^(-(1/4 : ℝ))) := by
        funext n
        by_cases hn : n = 0
        · subst n; simp
        · have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
          have hC_eq : (C : ℝ)^(1/8 : ℝ) * (C : ℝ)^(1/16 : ℝ) = (C : ℝ)^(3/16 : ℝ) := by
            rw [← Real.rpow_add hCpos (1/8 : ℝ) (1/16 : ℝ)]
            congr 1; norm_num
          have hn_eq : (n : ℝ)^(-(1/3 : ℝ)) * (n : ℝ)^(1/12 : ℝ) = (n : ℝ)^(-(1/4 : ℝ)) := by
            rw [← Real.rpow_add hn_posR (-(1/3 : ℝ)) (1/12 : ℝ)]
            congr 1; norm_num
          rw [show 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) * (2 * (C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/12 : ℝ)) =
              4 * ((C : ℝ)^(1/8 : ℝ) * (C : ℝ)^(1/16 : ℝ)) * ((n : ℝ)^(-(1/3 : ℝ)) * (n : ℝ)^(1/12 : ℝ)) by ring]
          rw [hC_eq, hn_eq]
      rw [hrew]
      simpa using hneg14.const_mul (4 * (C : ℝ)^(3/16 : ℝ))
    filter_upwards [hf.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)), Filter.eventually_ge_atTop 1] with n hn hn1
    have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hdenom_pos : 0 < (2 * (C : ℝ)^(1/16 : ℝ)) * (n : ℝ)^(1/12 : ℝ) := by positivity
    rw [lt_div_iff₀ hdenom_pos]
    exact hn
  have hn_final_ev : ∀ᶠ (n : ℕ) in atTop, 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) < (1 : ℝ) / (Nat.factorial 575 : ℝ) := by
    filter_upwards [hconst.eventually (Iio_mem_nhds (by positivity : 0 < (1 : ℝ) / (Nat.factorial 575 : ℝ)))] with n hn
    exact hn
  filter_upwards [p_ge_one_div_n_implies_not_rpow_four_third, Filter.eventually_ge_atTop 64, hhalf_ev, hlarge_pos_ev, hn_large_ev, hn_final_ev] with n h43 hn64 hhalf hlarge_pos hn_large hn_final
  intro m hp
  haveI : NeZero n := ⟨by omega⟩
  have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm1 : 1 ≤ m := by
    have hp_pos : 0 < p n m := lt_of_lt_of_le (one_div_pos.mpr hn_posR) hp
    rcases exists_of_p_pos n m hp_pos with ⟨g, hg⟩
    rw [← hg]
    exact Nat.succ_le_iff.mp (orderOf_pos g)
  have hm_lt : (m : ℝ) < (n : ℝ)^(4/3 : ℝ) := by
    exact lt_of_not_ge (h43 m hp)
  exact mem_K_of_p_ge n m C (hC m) hn64 hm1 hm_lt hp hlarge_pos hhalf hn_large hn_final

/-! ### The `M(n) ~ 1/n` part of Theorem 1.1 -/

/-- The large part of the recursion sum is `≤ 1`. -/
lemma sum_large_le_one (n m : ℕ) (hn : 64 ≤ n) (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) (hmpos : 0 < m) :
    (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) ≤ 1 := by
  rw [sum_large_eq_filter_dvd]
  have hcard := card_filter_large_dvd_le_one n m hn hm hmpos
  calc (∑ d ∈ (Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m), lcmOrderProb n d m)
      ≤ ∑ d ∈ (Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m), (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro d hd
            exact lcmOrderProb_le_one n d m
    _ = (((Finset.Icc (n - Nat.sqrt n + 1) n).filter (fun d => d ∣ m)).card : ℝ) := by simp
    _ ≤ (1 : ℝ) := by exact_mod_cast hcard

/-- `p n 0 = 0` (no permutation has order `0`). -/
lemma p_eq_zero (n : ℕ) : p n 0 = 0 := by
  unfold p
  have hfilter : ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = 0)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro g hg horder
    have hpos : 0 < orderOf g := orderOf_pos g
    omega
  rw [hfilter, Finset.card_empty]
  norm_num

/-- `p n n ≤ M n` (the value at `n` is among those maximized over). -/
lemma p_self_le_M (n : ℕ) : p n n ≤ M n := by
  unfold M
  have hn_mem : n ∈ Finset.range (Nat.factorial n + 1) := by
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Nat.self_le_factorial n) (Nat.lt_succ_self _)
  exact (Finset.le_fold_max (p n n)).mpr (Or.inr ⟨n, hn_mem, le_rfl⟩)

/-- `n·pₙ(m) ≤ (large part) + τ(m)²/√n`. -/
lemma n_mul_p_le_large_add_tau (n m : ℕ) [NeZero n] (hm1 : 1 ≤ m) (hs1 : 1 ≤ Nat.sqrt n) :
    (n : ℝ) * p n m ≤ (∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) + (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) := by
  have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hs_pos : 0 < (Nat.sqrt n : ℝ) := by exact_mod_cast (Nat.sqrt_pos.mpr (NeZero.pos n))
  have hsplit := p_le_sum_large_add_tau_sq_div n m hm1 hs1
  have h := mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg n)
  rw [mul_add] at h
  rw [show (n : ℝ) * ((1 / (n : ℝ)) * ∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m) =
      ∑ d ∈ Finset.Icc (n - Nat.sqrt n + 1) n, lcmOrderProb n d m by
        field_simp [ne_of_gt hn_posR]] at h
  rw [show (n : ℝ) * ((tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ))) = (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) by
        field_simp [ne_of_gt hn_posR, ne_of_gt hs_pos]] at h
  exact h

/-- `τ(m)²/√n ≤ 2C^{1/8} n^{-1/3}` whenever `m < n^{4/3}`. -/
lemma tau_sq_div_sqrt_le (n m C : ℕ) (hn : 0 < n) (hC : (tau m)^16 ≤ C * m) (hm : (m : ℝ) < (n : ℝ)^(4/3 : ℝ)) :
    (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) ≤ 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by
  have htau2 := tau_sq_div_n_sqrt_le n m C hn hC hm
  have hn_posR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs_pos : 0 < (Nat.sqrt n : ℝ) := by exact_mod_cast (Nat.sqrt_pos.mpr hn)
  have h := mul_le_mul_of_nonneg_left htau2 (Nat.cast_nonneg n)
  have hrew : (n : ℝ) * ((tau m : ℝ)^2 / ((n : ℝ) * (Nat.sqrt n : ℝ))) = (tau m : ℝ)^2 / (Nat.sqrt n : ℝ) := by
    field_simp [ne_of_gt hn_posR, ne_of_gt hs_pos]
  rw [hrew] at h
  have h2 : (n : ℝ) * (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) = 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by
    rw [show (n : ℝ) * (2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) = 2 * (C : ℝ)^(1/8 : ℝ) * ((n : ℝ) * (n : ℝ)^(-(4/3 : ℝ))) by ring]
    rw [show (n : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) = (n : ℝ)^(-(1/3 : ℝ)) by
      calc (n : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(-(4/3 : ℝ)) := by rw [Real.rpow_one]
        _ = (n : ℝ)^((1 : ℝ) + (-(4/3 : ℝ))) := by rw [Real.rpow_add hn_posR]
        _ = (n : ℝ)^(-(1/3 : ℝ)) := by congr 1; norm_num]
  rwa [h2] at h

/-- The uniform upper bound `n·pₙ(m) ≤ 1 + 2C^{1/8} n^{-1/3}` (eventually). -/
lemma eventually_n_mul_p_le_one_add (C : ℕ) (hC : ∀ m, (tau m)^16 ≤ C * m) :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) * p n m ≤ 1 + 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by
  filter_upwards [prop_large_orders_43, Filter.eventually_ge_atTop 64] with n h43 hn64
  intro m
  have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  haveI : NeZero n := ⟨by omega⟩
  by_cases hm0 : m = 0
  · subst m
    rw [p_eq_zero n]
    have hnonneg : 0 ≤ 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (Real.rpow_nonneg (Nat.cast_nonneg C) _)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    nlinarith
  · have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    by_cases hbig : (n : ℝ)^(4/3 : ℝ) ≤ (m : ℝ)
    · have hnp := h43 m hbig
      have hnonneg : 0 ≤ 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by positivity
      nlinarith
    · have hm_lt : (m : ℝ) < (n : ℝ)^(4/3 : ℝ) := lt_of_not_ge hbig
      have hs1 : 1 ≤ Nat.sqrt n := Nat.succ_le_iff.mp (Nat.sqrt_pos.mpr (by omega : 0 < n))
      have hnp := n_mul_p_le_large_add_tau n m hm1 hs1
      have hlarge := sum_large_le_one n m (by omega : 64 ≤ n) hm_lt (by omega : 0 < m)
      have htau := tau_sq_div_sqrt_le n m C (by omega : 0 < n) (hC m) hm_lt
      nlinarith

/-- `M(n) ≥ 1/n` (the lower bound, from `pₙ(n) ≥ 1/n`). -/
lemma one_div_le_M (n : ℕ) (hn : 2 ≤ n) : (1 : ℝ) / (n : ℝ) ≤ M n := by
  exact le_trans (one_div_le_p_self n hn) (p_self_le_M n)

/-- **Theorem 1.1, first statement**: `M(n) ∼ 1/n`, i.e. `n·M(n) → 1`. -/
theorem tendsto_n_mul_M_one : Tendsto (fun n : ℕ => (n : ℝ) * M n) atTop (𝓝 1) := by
  rcases tau_pow_sixteen_le with ⟨C, hC⟩
  have hle := eventually_n_mul_p_le_one_add C hC
  have hM_le : ∀ᶠ (n : ℕ) in atTop, (n : ℝ) * M n ≤ 1 + 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ)) := by
    filter_upwards [hle, Filter.eventually_ge_atTop 1] with n hn hn1
    have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hM : M n ≤ (1 + 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) / (n : ℝ) := by
      unfold M
      rw [Finset.fold_max_le ((1 + 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) / (n : ℝ))]
      constructor
      · exact div_nonneg (by positivity) (le_of_lt hn_posR)
      · intro m hm
        rw [le_div_iff₀ hn_posR]
        nlinarith [hn m]
    rw [le_div_iff₀ hn_posR] at hM
    nlinarith
  have hM_ge : ∀ᶠ (n : ℕ) in atTop, (1 : ℝ) ≤ (n : ℝ) * M n := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn_posR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h1 : (1 : ℝ) / (n : ℝ) ≤ M n := one_div_le_M n hn
    rw [div_le_iff₀ hn_posR] at h1
    nlinarith
  have hupper : Tendsto (fun n : ℕ => 1 + 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 1) := by
    have h := (tendsto_rpow_neg_atTop (y := (1/3 : ℝ)) (by norm_num)).comp tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun n : ℕ => 2 * (C : ℝ)^(1/8 : ℝ) * (n : ℝ)^(-(1/3 : ℝ))) atTop (𝓝 0) := by
      simpa using h.const_mul (2 * (C : ℝ)^(1/8 : ℝ))
    simpa using h'.const_add 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hM_ge hM_le

end MostProbableOrder
