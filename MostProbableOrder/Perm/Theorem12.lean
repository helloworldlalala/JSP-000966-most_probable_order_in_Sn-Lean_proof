import MostProbableOrder.Perm.Theorem11
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 1.2 — the equality case (the mode of the order distribution)

This file formalizes the *final comparison* argument in the paper's §4
(proof of `thm:equality_case`, p. 8) and assembles Theorem 1.2.

The paper's Proposition 4.1 (`prop:exact_order`) states that for `k ∈ Kₙ`
one has

  `pₙ(n-k) = 1/(n-k) + η(n,k) + O(n^{-3+o(1)}),`

with

  `η(n,k) := 0` if `k ∈ {0,1}` or `2^{⌊log₂ k⌋+1} ∣ n-k`, and
            `2^{1-⌊log₂ k⌋}/(n-k)²` otherwise.

That proposition is an adaptation of a deep theorem of Warlimont; here it is
taken as an input (see `SORRY.md`), while everything downstream — the exact
definition of `η`, its pointwise bounds, and the final comparison
`final_ineq` — is proved completely.

The final comparison is elementary: for `k, k₀ ∈ Kₙ` with `k < k₀`,

  `(k₀-k)/((n-k₀)(n-k)) + η(n,k₀) - η(n,k) ≥ 1/(n-k)²`.
-/

open Finset
open Filter
open scoped Real Topology

namespace MostProbableOrder

/-! ### The error correction `η` -/

/-- `η(n,k)` from Proposition 4.1. Written so that the second branch reads
`2 / 2^{⌊log₂ k⌋} / (n-k)² = 2^{1-⌊log₂ k⌋}/(n-k)²` (valid since `⌊log₂ k⌋ ≥ 1`
for `k ≥ 2`). -/
noncomputable def eta (n k : ℕ) : ℝ :=
  if k = 0 ∨ k = 1 ∨ (2 ^ (Nat.log 2 k + 1)) ∣ (n - k) then 0
  else (2 : ℝ) / ((2 : ℝ) ^ Nat.log 2 k) / ((n - k : ℕ) : ℝ) ^ 2

/-- `η(n,k) = 0` when `k ≤ 1`. -/
lemma eta_eq_zero_of_le_one (n k : ℕ) (hk : k ≤ 1) : eta n k = 0 := by
  unfold eta
  have h01 : k = 0 ∨ k = 1 := by omega
  have h : k = 0 ∨ k = 1 ∨ (2 ^ (Nat.log 2 k + 1)) ∣ (n - k) := by
    rcases h01 with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
  rw [if_pos h]

/-- `η(n,k) = 0` when `2^{⌊log₂ k⌋+1} ∣ n-k`. -/
lemma eta_eq_zero_of_dvd (n k : ℕ) (h : 2 ^ (Nat.log 2 k + 1) ∣ n - k) : eta n k = 0 := by
  unfold eta
  rw [if_pos (Or.inr (Or.inr h))]

/-- `η(n,k) ≥ 0`. -/
lemma eta_nonneg (n k : ℕ) : 0 ≤ eta n k := by
  unfold eta
  by_cases h : k = 0 ∨ k = 1 ∨ (2 ^ (Nat.log 2 k + 1)) ∣ (n - k)
  · rw [if_pos h]
  · rw [if_neg h]
    positivity

/-- `η(n,k) ≤ 1/(n-k)²` for `k ≥ 2` (and `k < n` so that `n-k > 0`). -/
lemma eta_le_inv_sq (n k : ℕ) (hk : 2 ≤ k) (hk_n : k < n) : eta n k ≤ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 := by
  unfold eta
  by_cases h : k = 0 ∨ k = 1 ∨ (2 ^ (Nat.log 2 k + 1)) ∣ (n - k)
  · rw [if_pos h]
    exact div_nonneg (by norm_num : 0 ≤ (1 : ℝ)) (sq_nonneg _)
  · rw [if_neg h]
    have hlog : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) hk
    have hpow_pos : 0 < (2 : ℝ) ^ Nat.log 2 k := pow_pos (by norm_num : 0 < (2 : ℝ)) _
    have hnk_pos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk_n)
    have hX_pos : 0 < ((n - k : ℕ) : ℝ) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hnk_pos)
    have h2le_nat : 2 ≤ 2 ^ Nat.log 2 k := Nat.le_self_pow (Nat.ne_of_gt hlog) 2
    have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ Nat.log 2 k := by exact_mod_cast h2le_nat
    have hratio : (2 : ℝ) / (2 : ℝ) ^ Nat.log 2 k ≤ 1 := by
      rw [div_le_iff₀ hpow_pos]
      simpa using h2le
    calc (2 : ℝ) / ((2 : ℝ) ^ Nat.log 2 k) / ((n - k : ℕ) : ℝ) ^ 2
        = ((2 : ℝ) / (2 : ℝ) ^ Nat.log 2 k) / ((n - k : ℕ) : ℝ) ^ 2 := by
              rw [div_div]
        _ ≤ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hratio (le_of_lt hX_pos)

/-! ### The final comparison (paper, equation (15)) -/

/-- Equation (15): for `k, k₀ ∈ Kₙ` with `k < k₀`,
`(k₀-k)/((n-k₀)(n-k)) + η(n,k₀) - η(n,k) ≥ 1/(n-k)²`. -/
lemma final_ineq (n k k₀ : ℕ) (hk : k ∈ K n) (hk₀ : k₀ ∈ K n) (h : k < k₀) :
    ((k₀ - k : ℕ) : ℝ) / (((n - k₀ : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) + eta n k₀ - eta n k
      ≥ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 := by
  have hk_lt_n : k < n := mem_range.mp (mem_filter.mp hk).1
  have hk₀_lt_n : k₀ < n := mem_range.mp (mem_filter.mp hk₀).1
  have hn_k_pos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk_lt_n)
  have hn_k0_pos : 0 < ((n - k₀ : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk₀_lt_n)
  by_cases hk1 : k ≤ 1
  · -- k ∈ {0,1}: η(n,k) = 0 and η(n,k₀) ≥ 0
    have hetak : eta n k = 0 := eta_eq_zero_of_le_one n k hk1
    rw [hetak, sub_zero]
    have hetak0 : 0 ≤ eta n k₀ := eta_nonneg n k₀
    have hk0k1 : 1 ≤ k₀ - k := Nat.succ_le_iff.mp (Nat.sub_pos_of_lt h)
    have hdiv : (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 ≤
        ((k₀ - k : ℕ) : ℝ) / (((n - k₀ : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) := by
      rw [div_le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hn_k_pos)) (mul_pos hn_k0_pos hn_k_pos)]
      have hkey : ((n - k₀ : ℕ) : ℝ) ≤ ((k₀ - k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
        have hbc : ((n - k₀ : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - ((k₀ - k : ℕ) : ℝ) := by
          rw [← Nat.cast_sub (by omega : k₀ - k ≤ n - k)]
          rw [show (n - k : ℕ) - (k₀ - k) = n - k₀ by omega]
        rw [hbc]
        have ha : (1 : ℝ) ≤ ((k₀ - k : ℕ) : ℝ) := by exact_mod_cast hk0k1
        have hc_nonneg : 0 ≤ ((n - k : ℕ) : ℝ) := le_of_lt hn_k_pos
        have hmul : ((n - k : ℕ) : ℝ) ≤ ((k₀ - k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
          simpa using (mul_le_mul_of_nonneg_right ha hc_nonneg)
        nlinarith
      simpa [mul_assoc, mul_left_comm, mul_comm, sq] using
        (mul_le_mul_of_nonneg_right hkey (le_of_lt hn_k_pos))
    nlinarith
  · -- k ≥ 2: η(n,k) ≤ 1/(n-k)², and k₀ - k ≥ 2
    have hk2 : 2 ≤ k := Nat.succ_le_iff.mp (Nat.lt_of_not_ge hk1)
    have hetak_le : eta n k ≤ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 := eta_le_inv_sq n k hk2 hk_lt_n
    have hetak0 : 0 ≤ eta n k₀ := eta_nonneg n k₀
    have hk0k2 : 2 ≤ k₀ - k := by
      have hdvd_diff := K_dvd_diff hk hk₀ (le_of_lt h)
      have h2mem : 2 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by norm_num, hk2⟩
      have h2dvd : 2 ∣ lcm1to k := by
        unfold lcm1to
        exact Finset.dvd_lcm h2mem
      have h2dvd_diff : 2 ∣ k₀ - k := dvd_trans h2dvd hdvd_diff
      exact Nat.le_of_dvd (Nat.sub_pos_of_lt h) h2dvd_diff
    have hmain : ((k₀ - k : ℕ) : ℝ) / (((n - k₀ : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) -
        (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 ≥ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 := by
      have ha : (2 : ℝ) ≤ ((k₀ - k : ℕ) : ℝ) := by exact_mod_cast hk0k2
      have hk0k_le : ((n - k₀ : ℕ) : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (n - k₀ : ℕ) ≤ n - k)
      have hkey : (2 : ℝ) * ((n - k₀ : ℕ) : ℝ) ≤ ((k₀ - k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
        have h1 : (2 : ℝ) * ((n - k : ℕ) : ℝ) ≤ ((k₀ - k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right ha (le_of_lt hn_k_pos)
        have h2 : (2 : ℝ) * ((n - k₀ : ℕ) : ℝ) ≤ (2 : ℝ) * ((n - k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hk0k_le (by norm_num : 0 ≤ (2 : ℝ))
        exact le_trans h2 h1
      have hdiv : (2 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 ≤
          ((k₀ - k : ℕ) : ℝ) / (((n - k₀ : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hn_k_pos)) (mul_pos hn_k0_pos hn_k_pos)]
        simpa [mul_assoc, mul_left_comm, mul_comm, sq] using
          (mul_le_mul_of_nonneg_right hkey (le_of_lt hn_k_pos))
      have hdiv' : (2 : ℝ) * (1 / ((n - k : ℕ) : ℝ) ^ 2) ≤
          ((k₀ - k : ℕ) : ℝ) / (((n - k₀ : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) := by
        simpa [div_eq_mul_inv] using hdiv
      linarith
    nlinarith [hetak_le, hetak0, hmain]

/-! ### The key property (leading term of Proposition 4.1) -/

/-- **The key property** (paper line 96): for `k ∈ Kₙ`, if the element `0` lies in a
cycle of length `n-k`, then `ord g = n-k` (because the remaining `k` points form a
permutation whose order divides `lcm(1,…,k)`, which divides `n-k`). -/
lemma orderOf_eq_of_cycleLen {n k : ℕ} [NeZero n] {g : SymmetricGroup n} (hk : k ∈ K n)
    (h : cycleLen g = n - k) : orderOf g = n - k := by
  have hk_lt : k < n := mem_range.mp (mem_filter.mp hk).1
  apply Nat.dvd_antisymm
  · -- orderOf g | n-k
    rw [orderOf_eq_lcm_cycleLen_residual g]
    apply Nat.lcm_dvd
    · rw [h]
    · have hnk : n - cycleLen g = k := by rw [h]; omega
      have hres_lcm : orderOf (residual g) ∣ lcm1to k := by
        simpa [hnk] using (orderOf_dvd_lcm1to (residual g))
      have hdvd_nk : lcm1to k ∣ n - k := (Finset.mem_filter.mp hk).2
      exact dvd_trans hres_lcm hdvd_nk
  · -- n-k | orderOf g
    rw [← h]
    exact cycleLen_dvd_orderOf g

/-! ### The 2-adic valuation (paper lines 281–282) -/

/-- For `k ≥ 2` and `k ∈ Kₙ`, the largest power of `2` not exceeding `k` divides `n-k`
(equivalently `ν₂(n-k) ≥ ⌊log₂ k⌋`). -/
lemma two_pow_log2_dvd_of_mem_K {n k : ℕ} (hk : k ∈ K n) (hk2 : 2 ≤ k) :
    2 ^ Nat.log 2 k ∣ n - k := by
  have hle : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega : k ≠ 0)
  have hmem : 2 ^ Nat.log 2 k ∈ Finset.Icc 1 k := by
    refine Finset.mem_Icc.mpr ⟨?_, hle⟩
    exact Nat.succ_le_iff.mp (pow_pos (by norm_num : 0 < (2 : ℕ)) (Nat.log 2 k))
  have hpow_lcm : 2 ^ Nat.log 2 k ∣ lcm1to k := by
    unfold lcm1to
    exact Finset.dvd_lcm hmem
  exact dvd_trans hpow_lcm (Finset.mem_filter.mp hk).2

/-- `ν₂(t) ≤ ⌊log₂ k⌋` whenever `1 ≤ t ≤ k` (the 2-adic valuation of any `t ≤ k` is
bounded by the exponent of the largest power of 2 not exceeding `k`). -/
lemma padicValNat_two_le_log2 {k t : ℕ} (ht : 1 ≤ t) (htk : t ≤ k) :
    padicValNat 2 t ≤ Nat.log 2 k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht0 : t ≠ 0 := by omega
  have hpow_dvd : 2 ^ padicValNat 2 t ∣ t := (padicValNat_dvd_iff_le (p := 2) ht0).mpr le_rfl
  have hpow_le : 2 ^ padicValNat 2 t ≤ k := le_trans (Nat.le_of_dvd (by omega : 0 < t) hpow_dvd) htk
  exact Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hpow_le

/-- For `k ≥ 2` and `k ∈ Kₙ`, if `2^{⌊log₂ k⌋+1} ∤ n-k`, then `ν₂(n-k) = ⌊log₂ k⌋` exactly
(the "interesting" case where `η(n,k) ≠ 0`). -/
lemma padicValNat_nk_eq_log2_of_not_two_pow_succ_dvd {n k : ℕ} (hk : k ∈ K n) (hk2 : 2 ≤ k)
    (h : ¬ 2 ^ (Nat.log 2 k + 1) ∣ n - k) : padicValNat 2 (n - k) = Nat.log 2 k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk_lt : k < n := mem_range.mp (mem_filter.mp hk).1
  have hnk_pos : n - k ≠ 0 := by omega
  have hge : Nat.log 2 k ≤ padicValNat 2 (n - k) :=
    (padicValNat_dvd_iff_le (p := 2) hnk_pos).mp (two_pow_log2_dvd_of_mem_K hk hk2)
  have hlt : padicValNat 2 (n - k) < Nat.log 2 k + 1 := by
    have hnot : ¬ Nat.log 2 k + 1 ≤ padicValNat 2 (n - k) := by
      intro h'
      exact h ((padicValNat_dvd_iff_le (p := 2) hnk_pos).mpr h')
    omega
  omega

/-! ### Theorem 1.2 -/

/-- `Kₙ` is nonempty for `n > 0` (it contains `0`). -/
lemma K_nonempty (n : ℕ) (hn : 0 < n) : (K n).Nonempty := ⟨0, mem_K_zero n hn⟩

/-- `k₀(n) := max Kₙ` (defined as `0` for `n = 0`). -/
noncomputable def k0 (n : ℕ) : ℕ :=
  if h : 0 < n then (K n).max' (K_nonempty n h) else 0

/-- `k₀(n) ∈ Kₙ` for `n > 0`. -/
lemma k0_mem_K (n : ℕ) (hn : 0 < n) : k0 n ∈ K n := by
  unfold k0
  rw [dif_pos hn]
  exact Finset.max'_mem _ _

/-- `k ≤ k₀(n)` for every `k ∈ Kₙ`. -/
lemma le_k0 (n : ℕ) (hn : 0 < n) {k : ℕ} (hk : k ∈ K n) : k ≤ k0 n := by
  unfold k0
  rw [dif_pos hn]
  exact Finset.le_max' (K n) k hk

/-- `pₙ(m) ≤ M(n)` for every `m`. -/
lemma p_le_M (n m : ℕ) : p n m ≤ M n := by
  unfold M
  by_cases hm : m ∈ Finset.range (Nat.factorial n + 1)
  · exact (Finset.le_fold_max (p n m)).mpr (Or.inr ⟨m, hm, le_rfl⟩)
  · have hp : p n m = 0 := by
      unfold p
      have hfilter : ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = m)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro g hg horder
        have hdvd : orderOf g ∣ Nat.factorial n := by
          have h := orderOf_dvd_card (G := SymmetricGroup n) (x := g)
          rwa [card_symmetricGroup] at h
        have hord_le : orderOf g ≤ Nat.factorial n := Nat.le_of_dvd (Nat.factorial_pos n) hdvd
        have hlarge : Nat.factorial n < m := by
          have hnot : ¬ m < Nat.factorial n + 1 := by
            simpa [Finset.mem_range] using hm
          omega
        omega
      rw [hfilter, Finset.card_empty]
      norm_num
    rw [hp]
    exact (Finset.le_fold_max (0 : ℝ)).mpr (Or.inl le_rfl)

end MostProbableOrder
