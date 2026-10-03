import MostProbableOrder.Perm.LargeOrdersAsymptotic

/-!
# Proposition 3.1 with `ε = 1/3`

The paper's `prop:large_orders` is stated for every `ε > 0`; the proof of Theorem 1.1
applies it with `ε = 1/3` so that `m ≤ n^{4/3}`. The file `LargeOrdersAsymptotic` fixes the
threshold `n^{3/2}` (`ε = 1/2`), which is insufficient for the "two divisors" step of
Theorem 1.1 (there `(n-√n)²/√n ≈ n^{3/2}` is used as a *lower* bound on `m`, so one needs
`m = o(n^{3/2})`).

This file re-runs the `E₁` estimate with threshold `n^{4/3}`. Everything `E₂`/`E₃`-related is
threshold-independent and is reused from `LargeOrdersAsymptotic`; only the `E₁` estimate, the
`σ`-condition `eventually_hE2`, and the final combination change, since they carry the `n^{1+ε}`
threshold. The resulting `E₁` bound is `L₁^{ω(m)+1}/m ≤ n^{-79/72}` (instead of `n^{-5/4}`),
which still gives `n · L₁^{ω(m)+1}/m ≤ n^{-7/72} → 0`.
-/

open Filter
open scoped Real Topology

namespace MostProbableOrder

/-- `n ≤ n^(4/3)` for `n ≥ 1`. -/
lemma le_rpow_four_third_self (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) := by
  have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcuberoot : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow h1 (by norm_num : 0 ≤ (1 / 3 : ℝ))
  rw [show (n : ℝ) ^ (4 / 3 : ℝ) = (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) by
    rw [show (4 / 3 : ℝ) = (1 : ℝ) + (1 / 3 : ℝ) by norm_num]
    rw [Real.rpow_add (by exact_mod_cast (by omega : 0 < n))]
    rw [Real.rpow_one]]
  nlinarith [hcuberoot]

/-- `log log n ≤ log log m` whenever `m ≥ n^{4/3}` (eventually). -/
lemma eventually_loglog_n_le_loglog_m_43 :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (4 / 3 : ℝ) ≤ (m : ℝ) →
      Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (m : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  intro m hm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
    have hpow : (4 / 3 : ℝ) * Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hnpos (4 / 3 : ℝ)) hm
      rwa [Real.log_rpow hnpos (4 / 3 : ℝ)] at h1
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hle : Real.log (n : ℝ) ≤ (4 / 3 : ℝ) * Real.log (n : ℝ) := by nlinarith [hlogn_nonneg]
    exact le_trans hle hpow
  have hlogposn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.log_le_log hlogposn hnm

/-- The pointwise `E₁` estimate: under the eventual log conditions, `L₁^{ω(m)+1}/m ≤ n^(-79/72)`. -/
lemma E1_term_le_of_conditions_43 (n m : ℕ) (C : ℝ)
    (hn : 3 ≤ n) (hm3 : 3 ≤ m) (hm0 : m ≠ 0)
    (hL1 : 1 ≤ L1 n)
    (hCpos : 0 < C)
    (hlogL1 : Real.log (L1 n : ℝ) ≤ 100 * Real.log (Real.log (Real.log (n : ℝ))))
    (hloglog : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (m : ℝ)))
    (hdelta : 100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)) ≤ (1 : ℝ) / 12)
    (hlogloglog_le : 100 * Real.log (Real.log (Real.log (n : ℝ))) ≤ (1 / 8 : ℝ) * Real.log (n : ℝ))
    (homega : (omega m : ℝ) ≤ C * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)))
    (hm : (n : ℝ) ^ (4 / 3 : ℝ) ≤ (m : ℝ)) :
    (L1 n : ℝ) ^ (omega m + 1) / (m : ℝ) ≤ (n : ℝ) ^ (-79 / 72 : ℝ) := by
  have hloglogn_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos (by
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) hnR))
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hlogm_nonneg : 0 ≤ Real.log (m : ℝ) := le_of_lt hlogm_pos
  have hlogL1_nonneg : 0 ≤ Real.log (L1 n : ℝ) := Real.log_nonneg (by exact_mod_cast hL1)
  -- ω(m) ≤ C log m / log log n
  have homega' : (omega m : ℝ) ≤ C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ)) := by
    calc (omega m : ℝ) ≤ C * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := homega
      _ ≤ C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ)) := by
            exact div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hCpos) hlogm_nonneg)
              hloglogn_pos hloglog
  -- ω(m) · log L₁ ≤ (1/12) · log m
  have homega_mul : (omega m : ℝ) * Real.log (L1 n : ℝ) ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) := by
    have h1 : (omega m : ℝ) * Real.log (L1 n : ℝ) ≤
        (C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ))) * Real.log (L1 n : ℝ) :=
      mul_le_mul_of_nonneg_right homega' hlogL1_nonneg
    have h2 : (C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ))) * Real.log (L1 n : ℝ) ≤
        (C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ))) * (100 * Real.log (Real.log (Real.log (n : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hlogL1 (div_nonneg (mul_nonneg (le_of_lt hCpos) hlogm_nonneg) (le_of_lt hloglogn_pos))
    have h3 : (C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ))) * (100 * Real.log (Real.log (Real.log (n : ℝ)))) =
        100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)) * Real.log (m : ℝ) := by
      ring
    have h4 : 100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)) * Real.log (m : ℝ) ≤
        (1 / 12 : ℝ) * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right hdelta hlogm_nonneg
    calc (omega m : ℝ) * Real.log (L1 n : ℝ)
        ≤ (C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ))) * Real.log (L1 n : ℝ) := h1
      _ ≤ (C * Real.log (m : ℝ) / Real.log (Real.log (n : ℝ))) * (100 * Real.log (Real.log (Real.log (n : ℝ)))) := h2
      _ = 100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)) * Real.log (m : ℝ) := h3
      _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) := h4
  -- (ω(m)+1)·log L₁ - log m ≤ -(79/72) log n
  have hstep : (omega m + 1 : ℝ) * Real.log (L1 n : ℝ) - Real.log (m : ℝ) ≤ (-79 / 72 : ℝ) * Real.log (n : ℝ) := by
    have hA : (omega m + 1 : ℝ) * Real.log (L1 n : ℝ) ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + (1 / 8 : ℝ) * Real.log (n : ℝ) := by
      calc (omega m + 1 : ℝ) * Real.log (L1 n : ℝ)
          = (omega m : ℝ) * Real.log (L1 n : ℝ) + Real.log (L1 n : ℝ) := by ring
        _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + Real.log (L1 n : ℝ) := by nlinarith [homega_mul]
        _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + 100 * Real.log (Real.log (Real.log (n : ℝ))) := by
              nlinarith [hlogL1]
        _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + (1 / 8 : ℝ) * Real.log (n : ℝ) := by nlinarith [hlogloglog_le]
    have hlogm_ge : (4 / 3 : ℝ) * Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) (4 / 3 : ℝ)) hm
      rwa [Real.log_rpow (by exact_mod_cast (by omega : 0 < n)) (4 / 3 : ℝ)] at h1
    nlinarith [hA, hlogm_ge]
  -- exponentiate
  have hL1pos : 0 < (L1 n : ℝ) := by exact_mod_cast (by omega : 0 < L1 n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hpow1 : (L1 n : ℝ) ^ (omega m + 1) = Real.exp (((omega m : ℝ) + 1) * Real.log (L1 n : ℝ)) := by
    rw [← Real.rpow_natCast]
    have hcast : ((omega m + 1 : ℕ) : ℝ) = (omega m : ℝ) + 1 := by
      rw [Nat.cast_add]
      norm_num
    rw [hcast]
    rw [Real.rpow_def_of_pos hL1pos]
    exact congrArg Real.exp (mul_comm (Real.log (L1 n : ℝ)) ((omega m : ℝ) + 1))
  have hmexp : (m : ℝ)⁻¹ = Real.exp (-Real.log (m : ℝ)) := by
    rw [show (m : ℝ)⁻¹ = (Real.exp (Real.log (m : ℝ)))⁻¹ by
      exact congrArg (·⁻¹) (Real.exp_log hmpos).symm]
    rw [← Real.exp_neg]
  calc (L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)
      = Real.exp ((omega m + 1 : ℝ) * Real.log (L1 n : ℝ)) * (m : ℝ)⁻¹ := by
            rw [hpow1, div_eq_mul_inv]
    _ = Real.exp ((omega m + 1 : ℝ) * Real.log (L1 n : ℝ)) * Real.exp (-Real.log (m : ℝ)) := by
            rw [hmexp]
    _ = Real.exp (((omega m + 1 : ℝ) * Real.log (L1 n : ℝ)) + (-Real.log (m : ℝ))) := by
            rw [Real.exp_add]
    _ = Real.exp ((omega m + 1 : ℝ) * Real.log (L1 n : ℝ) - Real.log (m : ℝ)) := by ring_nf
    _ ≤ Real.exp ((-79 / 72 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hstep
    _ = (n : ℝ) ^ (-79 / 72 : ℝ) := by
          rw [Real.rpow_def_of_pos hnpos]
          exact congrArg Real.exp (mul_comm (-79 / 72 : ℝ) (Real.log (n : ℝ)))

/-- **The `E₁` uniform estimate** (threshold `n^{4/3}`):
`L₁^{ω(m)+1}/m ≤ n^(-79/72)` uniformly in `m ≥ n^{4/3}`. -/
lemma eventually_E1_term_le_43 :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (4 / 3 : ℝ) ≤ (m : ℝ) →
      (L1 n : ℝ) ^ (omega m + 1) / (m : ℝ) ≤ (n : ℝ) ^ (-79 / 72 : ℝ) := by
  rcases omega_le_log_div_loglog with ⟨C, hCpos, hC⟩
  have hdelta : Tendsto (fun n : ℕ => 100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_logloglog_div_loglog_zero.const_mul (100 * C)
    rw [show (fun n : ℕ => 100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ))) =
        (fun n : ℕ => (100 * C) * (Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)))) by
      funext n; ring]
    simpa using h
  have hdelta_le := hdelta.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 12 : ℝ)))
  have hloglog_le_log : ∀ᶠ (n : ℕ) in atTop, Real.log (Real.log (n : ℝ)) ≤ (1 / 800 : ℝ) * Real.log (n : ℝ) := by
    have h := tendsto_loglog_div_log_zero.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 800 : ℝ)))
    filter_upwards [h, Filter.eventually_ge_atTop 3] with n hn h3
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rwa [div_le_iff₀ hlogpos] at hn
  have hlogloglog_le_log : ∀ᶠ (n : ℕ) in atTop, 100 * Real.log (Real.log (Real.log (n : ℝ))) ≤ (1 / 8 : ℝ) * Real.log (n : ℝ) := by
    filter_upwards [hloglog_le_log, Filter.eventually_ge_atTop 3] with n hn h3
    have hlll : Real.log (Real.log (Real.log (n : ℝ))) ≤ Real.log (Real.log (n : ℝ)) := logloglog_le_loglog h3
    calc 100 * Real.log (Real.log (Real.log (n : ℝ)))
        ≤ 100 * Real.log (Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hlll (by norm_num : 0 ≤ (100 : ℝ))
      _ ≤ 100 * ((1 / 800 : ℝ) * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hn (by norm_num : 0 ≤ (100 : ℝ))
      _ = (1 / 8 : ℝ) * Real.log (n : ℝ) := by ring
  filter_upwards [Filter.eventually_ge_atTop 3, eventually_one_le_L1, eventually_log_L1_le,
      eventually_loglog_n_le_loglog_m_43, hdelta_le, hlogloglog_le_log] with n hn hL1 hlogL1 hloglog hdelta hlll
  intro m hm
  have hm3 : 3 ≤ m := by
    have hpow : (3 : ℝ) ≤ (m : ℝ) := by
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hle : (3 : ℝ) ^ (4 / 3 : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (by norm_num : 0 ≤ (3 : ℝ)) h3 (by norm_num : 0 ≤ (4 / 3 : ℝ))
      have hlt : (3 : ℝ) < (3 : ℝ) ^ (4 / 3 : ℝ) := by
        have h := Real.one_lt_rpow (by norm_num : 1 < (3 : ℝ)) (by norm_num : 0 < (1 / 3 : ℝ))
        have h3pow : (3 : ℝ) ^ (4 / 3 : ℝ) = (3 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) := by
          rw [show (4 / 3 : ℝ) = (1 : ℝ) + (1 / 3 : ℝ) by norm_num]
          rw [Real.rpow_add (by norm_num : 0 < (3 : ℝ))]
          rw [Real.rpow_one]
        nlinarith [h, h3pow]
      exact le_of_lt (lt_of_lt_of_le hlt (le_trans hle hm))
    exact_mod_cast hpow
  have hm0 : m ≠ 0 := by omega
  exact E1_term_le_of_conditions_43 n m C hn hm3 hm0 hL1 hCpos hlogL1 (hloglog m hm) hdelta hlll (hC m hm3) hm

/-- The `E₂` condition `2e·σ(m) ≤ L₁·m` holds eventually for `n^{4/3} ≤ m ≤ n^{L₂}`. -/
lemma eventually_hE2_43 :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (4 / 3 : ℝ) ≤ (m : ℝ) → m ≤ n ^ (L2 n) →
      2 * Real.exp 1 * (sigma m : ℝ) ≤ (L1 n : ℝ) * (m : ℝ) := by
  have hloglog_ge : ∀ᶠ (n : ℕ) in atTop, Real.log 8 ≤ Real.log (Real.log (n : ℝ)) := by
    exact (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (Ici_mem_atTop (Real.log 8))
  filter_upwards [Filter.eventually_ge_atTop 8, hloglog_ge] with n hn8 hloglog_ge
  intro m hm hmle
  have hm8 : 8 ≤ m := by
    have hn_ge : (n : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) := le_rpow_four_third_self n (by omega : 1 ≤ n)
    have hnm : (n : ℝ) ≤ (m : ℝ) := le_trans hn_ge hm
    have h8R : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    have h8m : (8 : ℝ) ≤ (m : ℝ) := le_trans h8R hnm
    exact_mod_cast h8m
  have hloglogm_nonneg : 0 ≤ Real.log (Real.log (m : ℝ)) := by
    have hlogm : 1 ≤ Real.log (m : ℝ) := by
      have h3 : (3 : ℝ) ≤ (m : ℝ) := by
        have h8mR : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm8
        exact le_trans (by norm_num : (3 : ℝ) ≤ 8) h8mR
      have hlog3m : Real.log (3 : ℝ) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by norm_num : 0 < (3 : ℝ)) h3
      exact le_trans (le_of_lt one_lt_log_three) hlog3m
    exact Real.log_nonneg hlogm
  have hsigma : (sigma m : ℝ) / (m : ℝ) ≤ 60000 * Real.log (Real.log (m : ℝ)) := by
    have h := sigma_div_le_loglog_of_large m hm8
    have hle : Real.exp (B_euler + 4) * Real.log (Real.log (m : ℝ)) ≤ 60000 * Real.log (Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_right exp_B_euler_add_four_le_60000 hloglogm_nonneg
    exact le_trans h hle
  have hloglogm_le : Real.log (Real.log (m : ℝ)) ≤ 3 * Real.log (Real.log (n : ℝ)) := by
    have hlogm : Real.log (m : ℝ) ≤ 8 * (Real.log (n : ℝ)) ^ 2 := by
      have hL2 : (L2 n : ℝ) ≤ 8 * Real.log (n : ℝ) := le_L2_eight_log n (by omega : 3 ≤ n)
      have hloglogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hmleR : (m : ℝ) ≤ (n : ℝ) ^ (L2 n) := by exact_mod_cast hmle
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have h1 : Real.log (m : ℝ) ≤ Real.log ((n : ℝ) ^ (L2 n)) := Real.log_le_log hmpos hmleR
      have h2 : Real.log ((n : ℝ) ^ (L2 n)) = (L2 n : ℝ) * Real.log (n : ℝ) := Real.log_pow (n : ℝ) (L2 n)
      calc Real.log (m : ℝ)
          ≤ Real.log ((n : ℝ) ^ (L2 n)) := h1
        _ = (L2 n : ℝ) * Real.log (n : ℝ) := h2
        _ ≤ 8 * Real.log (n : ℝ) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hL2 hloglogn_nonneg
        _ = 8 * (Real.log (n : ℝ)) ^ 2 := by ring
    have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hle_log : Real.log (Real.log (m : ℝ)) ≤ Real.log (8 * (Real.log (n : ℝ)) ^ 2) :=
      Real.log_le_log hlogm_pos hlogm
    have hlog8 : Real.log (8 * (Real.log (n : ℝ)) ^ 2) = Real.log 8 + 2 * Real.log (Real.log (n : ℝ)) := by
      have hlogpos : 0 < Real.log (n : ℝ) := by
        exact Real.log_pos (show (1 : ℝ) < (n : ℝ) by exact_mod_cast (by omega : 1 < n))
      have hlog_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogpos
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 2 hlog_ne)]
      rw [Real.log_pow]
      norm_num
    rw [hlog8] at hle_log
    nlinarith [hle_log, hloglog_ge]
  have h2e : (360000 : ℝ) * Real.exp 1 ≤ 1000000 := by
    nlinarith [Real.exp_one_lt_d9]
  have hfinal : 2 * Real.exp 1 * (sigma m : ℝ) ≤ (L1 n : ℝ) * (m : ℝ) := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hloglogn_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
      apply Real.log_nonneg
      exact le_trans (le_of_lt one_lt_log_three) (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) (by exact_mod_cast (by omega : 3 ≤ n)))
    have hle1 : 2 * Real.exp 1 * ((sigma m : ℝ) / (m : ℝ)) ≤ 2 * Real.exp 1 * (60000 * Real.log (Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hsigma (by positivity)
    have hle2 : 2 * Real.exp 1 * (60000 * Real.log (Real.log (m : ℝ))) ≤ 360000 * Real.exp 1 * Real.log (Real.log (n : ℝ)) := by
      have h1 : 2 * Real.exp 1 * (60000 * Real.log (Real.log (m : ℝ))) = 120000 * Real.exp 1 * Real.log (Real.log (m : ℝ)) := by ring
      have h2 : 120000 * Real.exp 1 * Real.log (Real.log (m : ℝ)) ≤ 120000 * Real.exp 1 * (3 * Real.log (Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hloglogm_le (by positivity : 0 ≤ 120000 * Real.exp 1)
      have h3 : 120000 * Real.exp 1 * (3 * Real.log (Real.log (n : ℝ))) = 360000 * Real.exp 1 * Real.log (Real.log (n : ℝ)) := by ring
      rw [h1]
      exact h2.trans (le_of_eq h3)
    have hle3 : 360000 * Real.exp 1 * Real.log (Real.log (n : ℝ)) ≤ 1000000 * Real.log (Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right h2e hloglogn_nonneg
    have hle4 : 1000000 * Real.log (Real.log (n : ℝ)) ≤ (L1 n : ℝ) := by
      dsimp [L1]
      exact Nat.le_ceil (1000000 * Real.log (Real.log (n : ℝ)))
    have hfrac : 2 * Real.exp 1 * ((sigma m : ℝ) / (m : ℝ)) ≤ (L1 n : ℝ) :=
      le_trans (le_trans (le_trans hle1 hle2) hle3) hle4
    have hrewrite : 2 * Real.exp 1 * ((sigma m : ℝ) / (m : ℝ)) = (2 * Real.exp 1 * (sigma m : ℝ)) / (m : ℝ) := by
      field_simp [ne_of_gt hmpos]
    rw [hrewrite] at hfrac
    exact (div_le_iff₀ hmpos).mp hfrac
  exact hfinal

/-- **Proposition 3.1** (concrete form, `ε = 1/3`): `n · p_n(m) ≤ 1/2` uniformly in
`m ≥ n^{4/3}`, i.e. `max_{m ≥ n^{4/3}} p_n(m) = o(1/n)`. -/
theorem prop_large_orders_43 :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (4 / 3 : ℝ) ≤ (m : ℝ) →
      (n : ℝ) * p n m ≤ (1 : ℝ) / 2 := by
  have hE2_decay := tendsto_L2_mul_half_pow_L1_zero.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 6 : ℝ)))
  have hE3_decay := tendsto_mul_half_pow_L2_zero.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 6 : ℝ)))
  have h_inv : ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ (-(7 / 72 : ℝ)) ≤ (1 : ℝ) / 6 := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(7 / 72 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := (7 / 72 : ℝ)) (by norm_num : 0 < (7 / 72 : ℝ))).comp tendsto_natCast_atTop_atTop
    exact h.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 6 : ℝ)))
  filter_upwards [Filter.eventually_ge_atTop 8, eventually_one_le_L1, eventually_L1_le_L2,
      eventually_E3_cond, eventually_E1_term_le_43, eventually_hE2_43, hE2_decay, hE3_decay, h_inv]
      with n hn8 hL1 hLL hE3 hE1 hE2 hE2d hE3d h_inv
  intro m hm
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by
    have hpos : 0 < (m : ℝ) := by
      have hnpos : 0 < (n : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
      exact lt_of_lt_of_le hnpos hm
    exact ne_of_gt (Nat.cast_pos.mp hpos)
  by_cases hbig : n ^ (L2 n) < m
  · have hpeq := p_eq_prob_E3_of_lt n m hn0 hLL hbig
    rw [hpeq]
    have hle := prob_E3_le n m (L2 n) hn1 hE3
    have hC : (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n ≤ (1 : ℝ) / 6 := by
      have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ L2 n := pow_nonneg (by norm_num) _
      have hle2 : (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n ≤ (n : ℝ) * (1 / 2 : ℝ) ^ L2 n :=
        mul_le_mul_of_nonneg_right h2n hpow_nonneg
      exact le_trans hle2 hE3d
    calc (n : ℝ) * prob_E3 n m (L2 n)
        ≤ (n : ℝ) * ((2 : ℝ) * (1 / 2 : ℝ) ^ L2 n / (n : ℝ)) := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg n)
      _ = (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n := by
            field_simp [ne_of_gt (by exact_mod_cast (by omega : 0 < n))]
      _ ≤ (1 : ℝ) / 6 := hC
      _ ≤ (1 : ℝ) / 2 := by norm_num
  · have hmle : m ≤ n ^ (L2 n) := by omega
    have hmaster := p_le_master n m (L1 n) (L2 n) hn1 hm0 hL1 hLL (hE2 m hm hmle) hE3
    have hnE1 : (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)) ≤ (n : ℝ) ^ (-(7 / 72 : ℝ)) := by
      have hE1' := hE1 m hm
      have h : (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)) ≤ (n : ℝ) * (n : ℝ) ^ (-79 / 72 : ℝ) :=
        mul_le_mul_of_nonneg_left hE1' (Nat.cast_nonneg n)
      have h' : (n : ℝ) * (n : ℝ) ^ (-79 / 72 : ℝ) = (n : ℝ) ^ (-(7 / 72 : ℝ)) := by
        have h1 : (n : ℝ) * (n : ℝ) ^ (-79 / 72 : ℝ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-79 / 72 : ℝ) := by
          rw [Real.rpow_one]
        rw [h1]
        rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < n))]
        ring_nf
      exact h.trans (le_of_eq h')
    have hA : (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)) ≤ (1 : ℝ) / 6 := le_trans hnE1 h_inv
    have hB : (L2 n : ℝ) * (1 / 2 : ℝ) ^ L1 n ≤ (1 : ℝ) / 6 := by simpa using hE2d
    have hC : (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n ≤ (1 : ℝ) / 6 := by
      have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ L2 n := pow_nonneg (by norm_num) _
      have hle2 : (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n ≤ (n : ℝ) * (1 / 2 : ℝ) ^ L2 n :=
        mul_le_mul_of_nonneg_right h2n hpow_nonneg
      exact le_trans hle2 hE3d
    calc (n : ℝ) * p n m
        ≤ (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ) +
              (L2 n : ℝ) * (1 / 2 : ℝ) ^ L1 n / (n : ℝ) + (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hmaster (Nat.cast_nonneg n)
      _ = (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)) +
              (L2 n : ℝ) * (1 / 2 : ℝ) ^ L1 n + (2 : ℝ) * (1 / 2 : ℝ) ^ L2 n := by
              field_simp [ne_of_gt (by exact_mod_cast (by omega : 0 < n))]
      _ ≤ (1 : ℝ) / 6 + (1 : ℝ) / 6 + (1 : ℝ) / 6 := by nlinarith [hA, hB, hC]
      _ = (1 : ℝ) / 2 := by norm_num

end MostProbableOrder
