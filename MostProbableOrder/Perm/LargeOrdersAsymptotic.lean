import MostProbableOrder.Perm.LargeOrders
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Asymptotic decay lemmas for `prop:large_orders`

These are the analytic decay facts needed to turn the master bound `p_le_master` into the
asymptotic `max_{m ≥ n^{1+ε}} p_n(m) = o(1/n)` (the paper's `prop:large_orders`). Each of the
three events `E₁`, `E₂`, `E₃` contributes a term that decays at a different rate:

* `E₃` (cycle count `> C₂ log n`): the factor `(1/2)^{L₂}` with `L₂ ≈ C₂ log n` decays like
  `(1/2)^{log n}`; see `tendsto_half_pow_log2_nat_zero`.
* `E₂` (`C₁ log log n < c ≤ C₂ log n`): the factor `L₂ (1/2)^{L₁}` needs `log n · (1/2)^{log log n} → 0`,
  i.e. `(log n)^{1 - C₁ log 2} → 0`; see `tendsto_log_div_nat_zero` and `tendsto_half_pow_log2_nat_zero`.
* `E₁` (`c ≤ C₁ log log n`): the term `L₁^{ω(m)+1}/m` is controlled by `ω(m) ≤ C log m/log log m`
  (`omega_le_log_div_loglog`) together with the limit `log log log n / log log n → 0`
  (`tendsto_logloglog_div_loglog_zero`), because `log L₁ = O(log log log n)` and `log m ≥ (1+ε) log n`.
-/

open Filter
open scoped Real Topology

namespace MostProbableOrder

/-- `log(log(log n)) / log(log n) → 0` (the limit underlying the `E₁` estimate). -/
lemma tendsto_logloglog_div_loglog_zero :
    Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hq := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp h1
  exact hq.comp h2

/-- `(1/2)^n → 0`. -/
lemma tendsto_half_pow_nat_zero : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)

/-- `log n / n → 0`. -/
lemma tendsto_log_div_nat_zero : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- `Nat.log 2 n → ∞` as `n → ∞`. -/
lemma tendsto_Natlog_atTop_nat : Tendsto (fun n : ℕ => Nat.log 2 n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro a
  refine ⟨2 ^ a, ?_⟩
  intro n hn
  exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn

/-- `(1/2)^{Nat.log 2 n} → 0` (the `E₃` decay). -/
lemma tendsto_half_pow_log2_nat_zero : Tendsto (fun n : ℕ => (1/2 : ℝ)^(Nat.log 2 n)) atTop (𝓝 0) := by
  exact tendsto_half_pow_nat_zero.comp tendsto_Natlog_atTop_nat


/-! ### Thresholds and decay bounds -/

/-- `L₁(n) = ⌈10⁶ log log n⌉`. -/
noncomputable def L1 (n : ℕ) : ℕ := Nat.ceil (1000000 * Real.log (Real.log (n : ℝ)))

/-- `L₂(n) = ⌈7 log n⌉`. -/
noncomputable def L2 (n : ℕ) : ℕ := Nat.ceil (7 * Real.log (n : ℝ))

/-- `1 < 7 log 2`. -/
lemma one_lt_seven_log_two : (1 : ℝ) < 7 * Real.log 2 := by
  rw [show (7 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 7) by
    simp [Real.log_pow]]
  rw [Real.lt_log_iff_exp_lt (by norm_num : 0 < (2 : ℝ) ^ 7)]
  exact lt_trans Real.exp_one_lt_three (by norm_num : (3 : ℝ) < 2 ^ 7)

/-- `1 < 10⁶ log 2`. -/
lemma one_lt_million_log_two : (1 : ℝ) < 1000000 * Real.log 2 := by
  rw [show (1000000 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 1000000) by
    simp [Real.log_pow]]
  rw [Real.lt_log_iff_exp_lt (by positivity : 0 < (2 : ℝ) ^ 1000000)]
  exact lt_trans Real.exp_one_lt_three (by
    calc (3 : ℝ) < (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ 1000000 := by
            exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by norm_num : 2 ≤ 1000000))

/-- `1 < log 3`. -/
lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : 0 < (3 : ℝ))]
  exact Real.exp_one_lt_three

/-- `log(1/2) = -log 2`. -/
lemma log_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  simp [Real.log_inv]

/-- `(1/2)^(7 log n) = n^(-7 log 2)`. -/
lemma half_rpow_seven_log (n : ℕ) (hn : 0 < n) :
    (1 / 2 : ℝ) ^ (7 * Real.log (n : ℝ)) = (n : ℝ) ^ (-7 * Real.log 2) := by
  have hpos : 0 < (1 / 2 : ℝ) := by norm_num
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hnpos]
  rw [log_half]
  ring_nf

/-- `(1/2)^(10⁶ log log n) = (log n)^(-10⁶ log 2)`. -/
lemma half_rpow_million_loglog (n : ℕ) (hn : 1 < n) :
    (1 / 2 : ℝ) ^ (1000000 * Real.log (Real.log (n : ℝ))) =
      (Real.log (n : ℝ)) ^ (-1000000 * Real.log 2) := by
  have hpos : 0 < (1 / 2 : ℝ) := by norm_num
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hlogpos]
  rw [log_half]
  ring_nf

/-- **E₃ decay**: `n · (1/2)^{L₂(n)} → 0`. -/
lemma tendsto_mul_half_pow_L2_zero :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ L2 n) atTop (𝓝 0) := by
  have hmain : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 7 * Real.log 2)) atTop (𝓝 0) := by
    have hy : 0 < 7 * Real.log 2 - 1 := by
      rw [sub_pos]
      exact one_lt_seven_log_two
    have h := (tendsto_rpow_neg_atTop (y := 7 * Real.log 2 - 1) hy).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    congr 1
    ring
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmain
  · exact mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (L2 n))
  · by_cases hn : n = 0
    · subst n
      simp [L2]
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (0 : ℝ)) _
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hL2 : 7 * Real.log (n : ℝ) ≤ (L2 n : ℝ) := by
        unfold L2
        exact Nat.le_ceil (7 * Real.log (n : ℝ))
      have hpow : (1 / 2 : ℝ) ^ L2 n ≤ (1 / 2 : ℝ) ^ (7 * Real.log (n : ℝ)) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 1) hL2
      calc (n : ℝ) * (1 / 2 : ℝ) ^ L2 n
          ≤ (n : ℝ) * ((1 / 2 : ℝ) ^ (7 * Real.log (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
        _ = (n : ℝ) ^ (1 - 7 * Real.log 2) := by
              rw [half_rpow_seven_log n hnpos]
              have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
              rw [show (n : ℝ) * (n : ℝ) ^ (-7 * Real.log 2) = (n : ℝ) ^ (1 - 7 * Real.log 2) by
                calc (n : ℝ) * (n : ℝ) ^ (-7 * Real.log 2)
                    = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-7 * Real.log 2) := by rw [Real.rpow_one]
                  _ = (n : ℝ) ^ ((1 : ℝ) + (-7 * Real.log 2)) := by rw [← Real.rpow_add hnposR]
                  _ = (n : ℝ) ^ (1 - 7 * Real.log 2) := by ring_nf]

/-- For `n ≥ 3`, `(L₂ n : ℝ) ≤ 8 log n`. -/
lemma le_L2_eight_log (n : ℕ) (hn : 3 ≤ n) : (L2 n : ℝ) ≤ 8 * Real.log (n : ℝ) := by
  have hceil : (L2 n : ℝ) < 7 * Real.log (n : ℝ) + 1 := by
    dsimp [L2]
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num : 0 ≤ (7 : ℝ))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))))
  have hlog1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_trans (le_of_lt one_lt_log_three) (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) h3)
  nlinarith

/-- `(1/2)^{L₁ n} ≤ (1/2)^{10⁶ log log n}`. -/
lemma pow_half_L1_le (n : ℕ) :
    (1 / 2 : ℝ) ^ L1 n ≤ (1 / 2 : ℝ) ^ (1000000 * Real.log (Real.log (n : ℝ))) := by
  have h : 1000000 * Real.log (Real.log (n : ℝ)) ≤ (L1 n : ℝ) := by
    dsimp [L1]
    exact Nat.le_ceil (1000000 * Real.log (Real.log (n : ℝ)))
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) ≤ 1) h

/-- **E₂ decay**: `L₂(n) · (1/2)^{L₁(n)} → 0`. -/
lemma tendsto_L2_mul_half_pow_L1_zero :
    Tendsto (fun n : ℕ => (L2 n : ℝ) * (1 / 2 : ℝ) ^ L1 n) atTop (𝓝 0) := by
  let g : ℕ → ℝ := fun n => 8 * (Real.log (n : ℝ)) ^ (-(1000000 * Real.log 2 - 1))
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hy : 0 < 1000000 * Real.log 2 - 1 := by
      rw [sub_pos]
      exact one_lt_million_log_two
    have hcore := (tendsto_rpow_neg_atTop (y := 1000000 * Real.log 2 - 1) hy).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    simpa [g] using hcore.const_mul 8
  refine squeeze_zero' (Filter.Eventually.of_forall ?_) ?_ hg0
  · intro n
    exact mul_nonneg (Nat.cast_nonneg (L2 n)) (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (L1 n))
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    dsimp [g]
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hL2 : (L2 n : ℝ) ≤ 8 * Real.log (n : ℝ) := le_L2_eight_log n hn
    have hpow : (1 / 2 : ℝ) ^ L1 n ≤ (1 / 2 : ℝ) ^ (1000000 * Real.log (Real.log (n : ℝ))) :=
      pow_half_L1_le n
    have hnonneg_pow : 0 ≤ (1 / 2 : ℝ) ^ L1 n := by positivity
    have hnonneg_log : 0 ≤ 8 * Real.log (n : ℝ) := by
      exact mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) (le_of_lt hlogpos)
    calc (L2 n : ℝ) * (1 / 2 : ℝ) ^ L1 n
        ≤ (8 * Real.log (n : ℝ)) * ((1 / 2 : ℝ) ^ (1000000 * Real.log (Real.log (n : ℝ)))) := by
            exact mul_le_mul hL2 hpow hnonneg_pow hnonneg_log
      _ = 8 * (Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-1000000 * Real.log 2)) := by
            rw [half_rpow_million_loglog n (by omega : 1 < n)]
            ring
      _ = 8 * (Real.log (n : ℝ)) ^ (1 - 1000000 * Real.log 2) := by
            rw [show Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-1000000 * Real.log 2) =
                (Real.log (n : ℝ)) ^ (1 - 1000000 * Real.log 2) by
              calc Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-1000000 * Real.log 2)
                  = (Real.log (n : ℝ)) ^ (1 : ℝ) * (Real.log (n : ℝ)) ^ (-1000000 * Real.log 2) := by
                      rw [Real.rpow_one]
                _ = (Real.log (n : ℝ)) ^ ((1 : ℝ) + (-1000000 * Real.log 2)) := by
                      rw [← Real.rpow_add hlogpos]
                _ = (Real.log (n : ℝ)) ^ (1 - 1000000 * Real.log 2) := by ring_nf]
      _ = 8 * (Real.log (n : ℝ)) ^ (-(1000000 * Real.log 2 - 1)) := by ring_nf

/-- `log(log n) / log n → 0`. -/
lemma tendsto_loglog_div_log_zero :
    Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  exact (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-! ### Order is bounded by `n ^ #cycles` -/

/-- `orderOf σ ≤ n ^ numCycles σ`: the order (lcm of cycle lengths) is at most the product of
the cycle lengths, which is at most `n ^ #cycles`. -/
lemma orderOf_le_pow_numCycles (σ : SymmetricGroup n) : orderOf σ ≤ n ^ numCycles σ := by
  have hlcm : orderOf σ = σ.cycleType.lcm := (Equiv.Perm.lcm_cycleType σ).symm
  have hprod_pos : 0 < σ.cycleType.prod := by
    refine Multiset.prod_pos ?_
    intro a ha
    exact lt_of_lt_of_le (by norm_num : 0 < 2) (Equiv.Perm.two_le_of_mem_cycleType ha)
  have hlcm_le_prod : σ.cycleType.lcm ≤ σ.cycleType.prod := by
    have hdvd : σ.cycleType.lcm ∣ σ.cycleType.prod := by
      rw [Multiset.lcm_dvd]
      intro b hb
      exact Multiset.dvd_prod hb
    exact Nat.le_of_dvd hprod_pos hdvd
  have hprod_le : σ.cycleType.prod ≤ n ^ σ.cycleType.card := by
    refine Multiset.prod_le_pow_card σ.cycleType n ?_
    intro a ha
    have h1 : a ≤ σ.cycleType.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) a ha
    have h2 : σ.cycleType.sum ≤ n := by
      have h := Equiv.Perm.sum_cycleType_le σ
      simpa [Fintype.card_fin] using h
    exact le_trans h1 h2
  have hcard : σ.cycleType.card ≤ numCycles σ := by
    dsimp [numCycles]
    exact Nat.le_add_right _ _
  by_cases hn0 : n = 0
  · subst n
    have hσ : σ = 1 := Subsingleton.elim σ 1
    simp [hσ, numCycles, Equiv.Perm.cycleType_one]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hpow : n ^ σ.cycleType.card ≤ n ^ numCycles σ := by
      exact pow_le_pow_right₀ hnpos hcard
    calc orderOf σ = σ.cycleType.lcm := hlcm
      _ ≤ σ.cycleType.prod := hlcm_le_prod
      _ ≤ n ^ σ.cycleType.card := hprod_le
      _ ≤ n ^ numCycles σ := hpow

/-! ### Threshold and decay conditions (eventually in `n`) -/

/-- `1 ≤ L₁ n` eventually. -/
lemma eventually_one_le_L1 : ∀ᶠ n in atTop, 1 ≤ L1 n := by
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  have hlogpos : 0 < 1000000 * Real.log (Real.log (n : ℝ)) := by
    have hlog : 1 < Real.log (n : ℝ) := by
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) h3)
    exact mul_pos (by norm_num : 0 < (1000000 : ℝ)) (Real.log_pos hlog)
  have hle : (0 : ℝ) < (L1 n : ℝ) := by
    dsimp [L1]
    exact lt_of_lt_of_le hlogpos (Nat.le_ceil (1000000 * Real.log (Real.log (n : ℝ))))
  have hpos : 0 < L1 n := by exact_mod_cast hle
  exact Nat.succ_le_iff.mpr hpos

/-- `10⁶ log log n ≤ 7 log n` eventually. -/
lemma eventually_million_loglog_le_seven_log :
    ∀ᶠ (n : ℕ) in atTop, 1000000 * Real.log (Real.log (n : ℝ)) ≤ 7 * Real.log (n : ℝ) := by
  have hle0 := tendsto_loglog_div_log_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 7 / 1000000))
  filter_upwards [hle0, Filter.eventually_ge_atTop 3] with n hn h3
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hdiv : Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ≤ 7 / 1000000 := by
    simpa using hn
  have h1 : Real.log (Real.log (n : ℝ)) ≤ (7 / 1000000) * Real.log (n : ℝ) := by
    rwa [div_le_iff₀ hlogpos] at hdiv
  calc 1000000 * Real.log (Real.log (n : ℝ))
      ≤ 1000000 * ((7 / 1000000) * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num : 0 ≤ (1000000 : ℝ))
    _ = 7 * Real.log (n : ℝ) := by ring

/-- `L₁ n ≤ L₂ n` eventually. -/
lemma eventually_L1_le_L2 : ∀ᶠ (n : ℕ) in atTop, L1 n ≤ L2 n := by
  filter_upwards [eventually_million_loglog_le_seven_log] with n hn
  have hle : 1000000 * Real.log (Real.log (n : ℝ)) ≤ (L2 n : ℝ) := by
    dsimp [L2]
    exact le_trans hn (Nat.le_ceil (7 * Real.log (n : ℝ)))
  exact Nat.ceil_le.mpr hle

/-- `2e(1 + log n) ≤ L₂ n` eventually. -/
lemma eventually_E3_cond : ∀ᶠ (n : ℕ) in atTop, 2 * Real.exp 1 * (1 + Real.log n) ≤ (L2 n : ℝ) := by
  have hlog6 : ∀ᶠ (n : ℕ) in atTop, 6 ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (Ici_mem_atTop 6)
  filter_upwards [hlog6] with n hn
  have h7 : (1 : ℝ) ≤ 7 - 2 * Real.exp 1 := by nlinarith [Real.exp_one_lt_three]
  have h2e : 2 * Real.exp 1 ≤ Real.log (n : ℝ) := by nlinarith [Real.exp_one_lt_three, hn]
  have hnonneg : 0 ≤ Real.log (n : ℝ) := by nlinarith [hn]
  have hprod : Real.log (n : ℝ) ≤ (7 - 2 * Real.exp 1) * Real.log (n : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_right h7 hnonneg)
  have h2e_le : 2 * Real.exp 1 ≤ (7 - 2 * Real.exp 1) * Real.log (n : ℝ) := le_trans h2e hprod
  have hmain : 2 * Real.exp 1 * (1 + Real.log (n : ℝ)) ≤ 7 * Real.log (n : ℝ) := by
    nlinarith [h2e_le]
  have hle : 7 * Real.log (n : ℝ) ≤ (L2 n : ℝ) := by
    dsimp [L2]
    exact Nat.le_ceil (7 * Real.log (n : ℝ))
  exact le_trans hmain hle

/-! ### The `E₁` uniform estimate -/

/-- `log log log n ≤ log log n` for `n ≥ 3`. -/
lemma logloglog_le_loglog {n : ℕ} (hn : 3 ≤ n) :
    Real.log (Real.log (Real.log (n : ℝ))) ≤ Real.log (Real.log (n : ℝ)) := by
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    have hlog : 1 < Real.log (n : ℝ) := by
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) h3)
    exact Real.log_pos hlog
  have h1 : Real.log (Real.log (Real.log (n : ℝ))) ≤ Real.log (Real.log (n : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos hloglog
  nlinarith

/-- `log(L₁ n) ≤ 100 · log log log n` eventually. -/
lemma eventually_log_L1_le :
    ∀ᶠ (n : ℕ) in atTop, Real.log (L1 n : ℝ) ≤ 100 * Real.log (Real.log (Real.log (n : ℝ))) := by
  have hll : ∀ᶠ (n : ℕ) in atTop, 1 ≤ Real.log (Real.log (n : ℝ)) := by
    exact (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (Ici_mem_atTop 1)
  have hlll : ∀ᶠ (n : ℕ) in atTop, 1 ≤ Real.log (Real.log (Real.log (n : ℝ))) := by
    exact (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually (Ici_mem_atTop 1)
  filter_upwards [hll, hlll] with n hn hn'
  have hceil : (L1 n : ℝ) < 1000000 * Real.log (Real.log (n : ℝ)) + 1 := by
    dsimp [L1]
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num : 0 ≤ (1000000 : ℝ))
      (le_of_lt (lt_of_lt_of_le (by norm_num : 0 < (1 : ℝ)) hn)))
  have hle : (L1 n : ℝ) ≤ 10000000 * Real.log (Real.log (n : ℝ)) := by
    have h1 : 1000000 * Real.log (Real.log (n : ℝ)) + 1 ≤ 10000000 * Real.log (Real.log (n : ℝ)) := by
      nlinarith [hn]
    exact le_trans (le_of_lt hceil) h1
  have hlogpos : 0 < (L1 n : ℝ) := by
    have h1 : 0 < 1000000 * Real.log (Real.log (n : ℝ)) :=
      mul_pos (by norm_num : 0 < (1000000 : ℝ)) (lt_of_lt_of_le (by norm_num : 0 < (1 : ℝ)) hn)
    exact lt_of_lt_of_le h1 (Nat.le_ceil (1000000 * Real.log (Real.log (n : ℝ))))
  have hlog_le : Real.log (L1 n : ℝ) ≤ Real.log (10000000 * Real.log (Real.log (n : ℝ))) :=
    Real.log_le_log hlogpos hle
  have hlog10 : Real.log 10 ≤ 9 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (10 : ℝ))
    nlinarith
  have hmain : Real.log (10000000 * Real.log (Real.log (n : ℝ))) ≤ 100 * Real.log (Real.log (Real.log (n : ℝ))) := by
    have hllpos : 0 < Real.log (Real.log (n : ℝ)) := lt_of_lt_of_le (by norm_num : 0 < (1 : ℝ)) hn
    rw [Real.log_mul (by norm_num : (10000000 : ℝ) ≠ 0) (ne_of_gt hllpos)]
    have h7 : Real.log 10000000 = 7 * Real.log 10 := by
      rw [show (10000000 : ℝ) = (10 : ℝ) ^ 7 by norm_num]
      simpa using (Real.log_pow (10 : ℝ) 7)
    rw [h7]
    have h7b : 7 * Real.log 10 ≤ 63 := by nlinarith [hlog10]
    nlinarith [h7b, hn']
  exact le_trans hlog_le hmain

/-- `log log n ≤ log log m` whenever `m ≥ n^{3/2}` (eventually). -/
lemma eventually_loglog_n_le_loglog_m :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) →
      Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (m : ℝ)) := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  intro m hm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
    have hpow : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hnpos (3 / 2 : ℝ)) hm
      rwa [Real.log_rpow hnpos (3 / 2 : ℝ)] at h1
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hle : Real.log (n : ℝ) ≤ (3 / 2 : ℝ) * Real.log (n : ℝ) := by nlinarith [hlogn_nonneg]
    exact le_trans hle hpow
  have hlogposn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.log_le_log hlogposn hnm

/-- The pointwise `E₁` estimate: under the eventual log conditions, `L₁^{ω(m)+1}/m ≤ n^(-5/4)`. -/
lemma E1_term_le_of_conditions (n m : ℕ) (C : ℝ)
    (hn : 3 ≤ n) (hm3 : 3 ≤ m) (hm0 : m ≠ 0)
    (hL1 : 1 ≤ L1 n)
    (hCpos : 0 < C)
    (hlogL1 : Real.log (L1 n : ℝ) ≤ 100 * Real.log (Real.log (Real.log (n : ℝ))))
    (hloglog : Real.log (Real.log (n : ℝ)) ≤ Real.log (Real.log (m : ℝ)))
    (hdelta : 100 * C * Real.log (Real.log (Real.log (n : ℝ))) / Real.log (Real.log (n : ℝ)) ≤ (1 : ℝ) / 12)
    (hlogloglog_le : 100 * Real.log (Real.log (Real.log (n : ℝ))) ≤ (1 / 8 : ℝ) * Real.log (n : ℝ))
    (homega : (omega m : ℝ) ≤ C * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)))
    (hm : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ)) :
    (L1 n : ℝ) ^ (omega m + 1) / (m : ℝ) ≤ (n : ℝ) ^ (-5 / 4 : ℝ) := by
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
  -- (ω(m)+1)·log L₁ - log m ≤ -(5/4) log n
  have hstep : (omega m + 1 : ℝ) * Real.log (L1 n : ℝ) - Real.log (m : ℝ) ≤ (-5 / 4 : ℝ) * Real.log (n : ℝ) := by
    have hA : (omega m + 1 : ℝ) * Real.log (L1 n : ℝ) ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + (1 / 8 : ℝ) * Real.log (n : ℝ) := by
      calc (omega m + 1 : ℝ) * Real.log (L1 n : ℝ)
          = (omega m : ℝ) * Real.log (L1 n : ℝ) + Real.log (L1 n : ℝ) := by ring
        _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + Real.log (L1 n : ℝ) := by nlinarith [homega_mul]
        _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + 100 * Real.log (Real.log (Real.log (n : ℝ))) := by
              nlinarith [hlogL1]
        _ ≤ (1 / 12 : ℝ) * Real.log (m : ℝ) + (1 / 8 : ℝ) * Real.log (n : ℝ) := by nlinarith [hlogloglog_le]
    have hlogm_ge : (3 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) (3 / 2 : ℝ)) hm
      rwa [Real.log_rpow (by exact_mod_cast (by omega : 0 < n)) (3 / 2 : ℝ)] at h1
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
    _ ≤ Real.exp ((-5 / 4 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hstep
    _ = (n : ℝ) ^ (-5 / 4 : ℝ) := by
          rw [Real.rpow_def_of_pos hnpos]
          exact congrArg Real.exp (mul_comm (-5 / 4 : ℝ) (Real.log (n : ℝ)))

/-- **The `E₁` uniform estimate**: `L₁^{ω(m)+1}/m ≤ n^(-5/4)` uniformly in `m ≥ n^{3/2}`. -/
lemma eventually_E1_term_le :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) →
      (L1 n : ℝ) ^ (omega m + 1) / (m : ℝ) ≤ (n : ℝ) ^ (-5 / 4 : ℝ) := by
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
      eventually_loglog_n_le_loglog_m, hdelta_le, hlogloglog_le_log] with n hn hL1 hlogL1 hloglog hdelta hlll
  intro m hm
  have hm3 : 3 ≤ m := by
    have hpow : (3 : ℝ) ≤ (m : ℝ) := by
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hle : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num : 0 ≤ (3 : ℝ)) h3 (by norm_num : 0 ≤ (3 / 2 : ℝ))
      have hlt : (3 : ℝ) < (3 : ℝ) ^ (3 / 2 : ℝ) := by
        have h := Real.one_lt_rpow (by norm_num : 1 < (3 : ℝ)) (by norm_num : 0 < (1 / 2 : ℝ))
        have h3pow : (3 : ℝ) ^ (3 / 2 : ℝ) = (3 : ℝ) * (3 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num]
          rw [Real.rpow_add (by norm_num : 0 < (3 : ℝ))]
          rw [Real.rpow_one]
        nlinarith [h, h3pow]
      exact le_of_lt (lt_of_lt_of_le hlt (le_trans hle hm))
    exact_mod_cast hpow
  have hm0 : m ≠ 0 := by omega
  exact E1_term_le_of_conditions n m C hn hm3 hm0 hL1 hCpos hlogL1 (hloglog m hm) hdelta hlll (hC m hm3) hm

/-- `n ≤ n^(3/2)` for `n ≥ 1`. -/
lemma le_rpow_three_half_self (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 1 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow h1 (by norm_num : 0 ≤ (1 / 2 : ℝ))
  rw [show (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) by
    rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num]
    rw [Real.rpow_add (by exact_mod_cast (by omega : 0 < n))]
    rw [Real.rpow_one]]
  nlinarith [hsqrt]

/-- If `n^L < m` (and `n ≠ 0`), then no permutation with `≤ L` cycles has order `m`. -/
lemma card_orderEq_numCycles_le_eq_zero (n m L : ℕ) (hn : n ≠ 0) (h : n ^ L < m) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  ext σ
  constructor
  · intro hσ
    rw [Finset.mem_filter] at hσ
    have hord : orderOf σ = m := hσ.2.1
    have hc : numCycles σ ≤ L := hσ.2.2
    have hord_le : orderOf σ ≤ n ^ numCycles σ := orderOf_le_pow_numCycles σ
    have hpow : n ^ numCycles σ ≤ n ^ L :=
      pow_le_pow_right₀ (Nat.pos_of_ne_zero hn) hc
    have hm_le : m ≤ n ^ L := by
      rw [← hord]
      exact le_trans hord_le hpow
    omega
  · intro h
    simp at h

/-- When `m > n^(L₂ n)`, only `E₃` contributes: `p n m = P(E₃)`. -/
lemma p_eq_prob_E3_of_lt (n m : ℕ) (hn : n ≠ 0) (hLL : L1 n ≤ L2 n) (h : n ^ (L2 n) < m) :
    p n m = prob_E3 n m (L2 n) := by
  have hE1 : prob_E1 n m (L1 n) = 0 := by
    unfold prob_E1
    have hL1L2 : n ^ (L1 n) ≤ n ^ (L2 n) :=
      pow_le_pow_right₀ (Nat.pos_of_ne_zero hn) hLL
    have hcard := card_orderEq_numCycles_le_eq_zero n m (L1 n) hn (lt_of_le_of_lt hL1L2 h)
    rw [hcard]
    norm_num
  have hE2 : prob_E2 n m (L1 n) (L2 n) = 0 := by
    unfold prob_E2
    have hcard := card_orderEq_numCycles_le_eq_zero n m (L2 n) hn h
    have hsub : ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => orderOf σ = m ∧ L1 n < numCycles σ ∧ numCycles σ ≤ L2 n)) ⊆
        ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L2 n)) := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ ⊢
      exact ⟨hσ.1, hσ.2.1, hσ.2.2.2⟩
    have hle : ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => orderOf σ = m ∧ L1 n < numCycles σ ∧ numCycles σ ≤ L2 n)).card ≤
        ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L2 n)).card :=
      Finset.card_le_card hsub
    have hcard2 : ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => orderOf σ = m ∧ L1 n < numCycles σ ∧ numCycles σ ≤ L2 n)).card = 0 :=
      le_antisymm (le_trans hle (le_of_eq hcard)) (Nat.zero_le _)
    rw [hcard2]
    norm_num
  rw [p_eq_E1_add_E2_add_E3 n m (L1 n) (L2 n) hLL]
  rw [hE1, hE2]
  ring

/-- The `E₂` condition `2e·σ(m) ≤ L₁·m` holds eventually for `n^{3/2} ≤ m ≤ n^{L₂}`. -/
lemma eventually_hE2 :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) → m ≤ n ^ (L2 n) →
      2 * Real.exp 1 * (sigma m : ℝ) ≤ (L1 n : ℝ) * (m : ℝ) := by
  have hloglog_ge : ∀ᶠ (n : ℕ) in atTop, Real.log 8 ≤ Real.log (Real.log (n : ℝ)) := by
    exact (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (Ici_mem_atTop (Real.log 8))
  filter_upwards [Filter.eventually_ge_atTop 8, hloglog_ge] with n hn8 hloglog_ge
  intro m hm hmle
  have hm8 : 8 ≤ m := by
    have hn_ge : (n : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := le_rpow_three_half_self n (by omega : 1 ≤ n)
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

/-- **Proposition 3.1** (concrete form): `n · p_n(m) ≤ 1/2` uniformly in `m ≥ n^{3/2}`, i.e.
`max_{m ≥ n^{3/2}} p_n(m) = o(1/n)`. -/
theorem prop_large_orders :
    ∀ᶠ (n : ℕ) in atTop, ∀ m : ℕ, (n : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) →
      (n : ℝ) * p n m ≤ (1 : ℝ) / 2 := by
  have hE2_decay := tendsto_L2_mul_half_pow_L1_zero.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 6 : ℝ)))
  have hE3_decay := tendsto_mul_half_pow_L2_zero.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 6 : ℝ)))
  have h_inv : ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (1 : ℝ) / 6 := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := (1 / 4 : ℝ)) (by norm_num : 0 < (1 / 4 : ℝ))).comp tendsto_natCast_atTop_atTop
    exact h.eventually (Iic_mem_nhds (by norm_num : 0 < (1 / 6 : ℝ)))
  filter_upwards [Filter.eventually_ge_atTop 8, eventually_one_le_L1, eventually_L1_le_L2,
      eventually_E3_cond, eventually_E1_term_le, eventually_hE2, hE2_decay, hE3_decay, h_inv]
      with n hn8 hL1 hLL hE3 hE1 hE2 hE2d hE3d h_inv
  intro m hm
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hm0 : m ≠ 0 := by
    have hpos : 0 < (m : ℝ) := by
      have hnpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
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
    have hnE1 : (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)) ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      have hE1' := hE1 m hm
      have h : (n : ℝ) * ((L1 n : ℝ) ^ (omega m + 1) / (m : ℝ)) ≤ (n : ℝ) * (n : ℝ) ^ (-5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hE1' (Nat.cast_nonneg n)
      have h' : (n : ℝ) * (n : ℝ) ^ (-5 / 4 : ℝ) = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        have h1 : (n : ℝ) * (n : ℝ) ^ (-5 / 4 : ℝ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-5 / 4 : ℝ) := by
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



