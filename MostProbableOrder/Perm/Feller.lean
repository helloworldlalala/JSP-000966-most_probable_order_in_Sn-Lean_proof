import MostProbableOrder.Perm.RestrictedBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Feller coupling and the cycle-count upper tail

This file collects the "number of cycles" facts needed in §3 of the paper:

* `cycleLength_le`, `numCycles_le` — the cycle length / cycle count are at most `n`.
* `IsRestricted_Icc_self` — every permutation is `[1,n]`-restricted.
* `sumInv_Icc_le_one_add_log` — `Σ_{i≤n} 1/i ≤ 1 + log n` (harmonic bound).
* `numCycles_prob_le` — pointwise bound `P(c = ℓ) ≤ (1+log n)^{ℓ-1}/(n·(ℓ-1)!)`.
* `numCycles_tail_le` — the upper tail `P(c ≥ L) ≤ 2·(1/2)^{L-1}/n`.

The cycle-removal bijection (`cycleRemovalEquiv`) and the uniform cycle-length
fact (`card_cycleLen_eq_factorial_pred`) are the combinatorial content of the
Feller coupling (Fact 2.1); here we only use their counting consequences via
Lemma 2.3 (`prob_numCycles_IsRestricted_le`).
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-! ### Basic cycle-count bounds -/

/-- A multiset of naturals each at least `1` has `card ≤ sum`. -/
lemma Multiset.card_le_sum_of_pos {m : Multiset ℕ} (h : ∀ x ∈ m, 1 ≤ x) : m.card ≤ m.sum := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 1 ≤ a := h a (by simp)
      have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => h x (by simp [hx])
      have ih' : s.card ≤ s.sum := ih hs
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega

/-- The length of the cycle through `a` is at most `n`. -/
lemma cycleLength_le (σ : SymmetricGroup n) (a : Fin n) : cycleLength σ a ≤ n := by
  unfold cycleLength
  simpa using Fintype.card_subtype_le (fun y : Fin n => Equiv.Perm.SameCycle σ a y)

/-- Every permutation of `n` letters has at most `n` cycles (counting fixed points). -/
lemma numCycles_le (σ : SymmetricGroup n) : numCycles σ ≤ n := by
  classical
  unfold numCycles
  rw [Fintype.card_fin]
  have hsum_le : σ.cycleType.sum ≤ n := by
    rw [Equiv.Perm.sum_cycleType]
    exact σ.support.card_le_univ.trans_eq (by simp)
  have hcard_le : σ.cycleType.card ≤ σ.cycleType.sum := by
    exact Multiset.card_le_sum_of_pos (fun x hx => (Equiv.Perm.one_lt_of_mem_cycleType hx).le)
  have hstep1 : σ.cycleType.card + (n - σ.cycleType.sum) ≤ σ.cycleType.sum + (n - σ.cycleType.sum) :=
    Nat.add_le_add_right hcard_le _
  have hstep2 : σ.cycleType.sum + (n - σ.cycleType.sum) = n := Nat.add_sub_of_le hsum_le
  exact le_trans hstep1 (le_of_eq hstep2)

/-- Every permutation is `[1,n]`-restricted (all cycle lengths lie in `[1,n]`). -/
lemma IsRestricted_Icc_self (σ : SymmetricGroup n) : IsRestricted (Finset.Icc 1 n) σ := by
  intro a
  rw [Finset.mem_Icc]
  exact ⟨one_le_cycleLength σ a, cycleLength_le σ a⟩

/-- `#{σ | numCycles σ = ℓ} = cardNumCyclesRestricted (Icc 1 n) ℓ n`. -/
lemma cardNumCyclesRestricted_Icc_self (ℓ n : ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card =
      cardNumCyclesRestricted (Finset.Icc 1 n) ℓ n := by
  unfold cardNumCyclesRestricted
  congr 1
  ext σ
  simp [IsRestricted_Icc_self σ]

/-! ### Harmonic bound -/

/-- `sumInv (Icc 1 n) = Σ_{i=1}^n 1/i = harmonic n ≤ 1 + log n`. -/
lemma sumInv_Icc_le_one_add_log (n : ℕ) :
    sumInv (Finset.Icc 1 n) ≤ 1 + Real.log n := by
  have hharm : sumInv (Finset.Icc 1 n) = (harmonic n : ℝ) := by
    unfold sumInv
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  rw [hharm]
  simpa using harmonic_le_one_add_log n

/-! ### Pointwise cycle-count bound -/

/-- **Pointwise bound**: `P(c(πₙ) = ℓ) ≤ (1+log n)^{ℓ-1} / (n·(ℓ-1)!)`. -/
lemma numCycles_prob_le (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card /
        (Nat.factorial n : ℝ) ≤
      (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := by
  classical
  have hle := prob_numCycles_IsRestricted_le (Finset.Icc 1 n) ℓ n hℓ hn
  rw [← cardNumCyclesRestricted_Icc_self ℓ n] at hle
  have hsumInv : sumInv (Finset.Icc 1 n) ≤ 1 + Real.log n := sumInv_Icc_le_one_add_log n
  have hnonneg : 0 ≤ sumInv (Finset.Icc 1 n) := by
    unfold sumInv
    exact Finset.sum_nonneg (fun i hi => one_div_nonneg.mpr (by positivity))
  exact le_trans hle
    (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hnonneg hsumInv (ℓ - 1))
      (by positivity : 0 ≤ (n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)))

/-- **Pointwise bound (geometric form)**: if `2e(1+log n) ≤ ℓ-1`, then `P(c=ℓ) ≤ (1/2)^{ℓ-1}/n`. -/
lemma numCycles_prob_le_half (ℓ n : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (h : 2 * Real.exp 1 * (1 + Real.log n) ≤ (ℓ - 1 : ℝ)) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card /
        (Nat.factorial n : ℝ) ≤ (1 / 2 : ℝ) ^ (ℓ - 1) / (n : ℝ) := by
  classical
  have hpt := numCycles_prob_le ℓ n hℓ hn
  have hlog_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlog_pos : (0 : ℝ) < 1 + Real.log n := by linarith
  have h2e : (1 : ℝ) ≤ 2 * Real.exp 1 * (1 + Real.log n) := by
    have he : (1 : ℝ) < Real.exp 1 := by
      rw [Real.one_lt_exp_iff]
      norm_num
    nlinarith
  have hℓm1pos : 1 ≤ ℓ - 1 := by
    have h1 : (1 : ℝ) ≤ (ℓ - 1 : ℝ) := le_trans h2e h
    exact_mod_cast h1
  have hfact : ((ℓ - 1 : ℕ) / Real.exp 1) ^ (ℓ - 1) ≤ (Nat.factorial (ℓ - 1) : ℝ) :=
    pow_div_exp_le_factorial hℓm1pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hℓm1R : (0 : ℝ) < (ℓ - 1 : ℝ) := by exact_mod_cast (by omega : 0 < ℓ - 1)
  have hlog1_nonneg : 0 ≤ 1 + Real.log n := add_nonneg zero_le_one hlog_nonneg
  have hratio : Real.exp 1 * (1 + Real.log n) / (ℓ - 1 : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hℓm1R]
    nlinarith
  calc ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card /
        (Nat.factorial n : ℝ)
      ≤ (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := hpt
    _ ≤ (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * (((ℓ - 1 : ℕ) / Real.exp 1) ^ (ℓ - 1))) := by
          refine div_le_div_of_nonneg_left (pow_nonneg hlog1_nonneg _) ?_ ?_
          · exact mul_pos hnR (pow_pos (div_pos (by exact_mod_cast hℓm1pos) (Real.exp_pos 1)) _)
          · exact mul_le_mul_of_nonneg_left hfact (Nat.cast_nonneg n)
    _ = (Real.exp 1 * (1 + Real.log n) / (ℓ - 1 : ℝ)) ^ (ℓ - 1) / (n : ℝ) := by
          have halg : (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * (((ℓ - 1 : ℕ) / Real.exp 1) ^ (ℓ - 1)))
              = (Real.exp 1 * (1 + Real.log n) / (ℓ - 1 : ℝ)) ^ (ℓ - 1) / (n : ℝ) := by
            have hcast : ((ℓ - 1 : ℕ) / Real.exp 1) = ((ℓ - 1 : ℝ) / Real.exp 1) := by
              rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ ℓ)]
              norm_num
            rw [hcast]
            calc (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * (((ℓ - 1 : ℝ) / Real.exp 1) ^ (ℓ - 1)))
                = (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * ((ℓ - 1 : ℝ) ^ (ℓ - 1) / Real.exp 1 ^ (ℓ - 1))) := by
                    rw [div_pow]
              _ = (1 + Real.log n) ^ (ℓ - 1) / ((n : ℝ) * (ℓ - 1 : ℝ) ^ (ℓ - 1) / Real.exp 1 ^ (ℓ - 1)) := by ring
              _ = (1 + Real.log n) ^ (ℓ - 1) * Real.exp 1 ^ (ℓ - 1) / ((n : ℝ) * (ℓ - 1 : ℝ) ^ (ℓ - 1)) := by
                    field_simp [Real.exp_ne_zero 1]
              _ = ((1 + Real.log n) * Real.exp 1) ^ (ℓ - 1) / ((n : ℝ) * (ℓ - 1 : ℝ) ^ (ℓ - 1)) := by
                    rw [mul_pow]
              _ = (((1 + Real.log n) * Real.exp 1) ^ (ℓ - 1) / (ℓ - 1 : ℝ) ^ (ℓ - 1)) / (n : ℝ) := by
                    field_simp [ne_of_gt hnR]
              _ = (((1 + Real.log n) * Real.exp 1 / (ℓ - 1 : ℝ)) ^ (ℓ - 1)) / (n : ℝ) := by
                    rw [div_pow]
              _ = (Real.exp 1 * (1 + Real.log n) / (ℓ - 1 : ℝ)) ^ (ℓ - 1) / (n : ℝ) := by ring
          exact halg
    _ ≤ (1 / 2 : ℝ) ^ (ℓ - 1) / (n : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
          exact pow_le_pow_left₀
            (div_nonneg (mul_nonneg (Real.exp_pos 1).le hlog1_nonneg) hℓm1R.le) hratio (ℓ - 1)

/-! ### The upper tail bound -/

/-- **Upper tail**: for `L - 1 ≥ 2e(1 + log n)`,
`P(c(πₙ) ≥ L) ≤ 2·(1/2)^{L-1} / n`. -/
theorem numCycles_tail_le (L n : ℕ) (hn : 1 ≤ n)
    (hL : 2 * Real.exp 1 * (1 + Real.log n) ≤ (L - 1 : ℝ)) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => L ≤ numCycles σ)).card /
        (Nat.factorial n : ℝ) ≤
      (2 : ℝ) * (1 / 2 : ℝ) ^ (L - 1) / (n : ℝ) := by
  classical
  let s := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => L ≤ numCycles σ)
  have hpartition : s.card =
      ∑ ℓ ∈ Finset.Icc L n, ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card := by
    have hcard := Finset.card_eq_sum_card_image (f := numCycles) (s := s)
    have himg : s.image numCycles ⊆ Finset.Icc L n := by
      intro ℓ hℓ
      rcases Finset.mem_image.mp hℓ with ⟨σ, hσ, rfl⟩
      rw [Finset.mem_filter] at hσ
      exact Finset.mem_Icc.mpr ⟨hσ.2, numCycles_le σ⟩
    have hzero : ∀ ℓ ∈ Finset.Icc L n, ℓ ∉ s.image numCycles →
        (s.filter (fun σ => numCycles σ = ℓ)).card = 0 := by
      intro ℓ hℓ hnot
      apply Finset.card_eq_zero.mpr
      ext σ
      constructor
      · intro hσ
        rw [Finset.mem_filter] at hσ
        exact False.elim (hnot (Finset.mem_image.mpr ⟨σ, hσ.1, hσ.2⟩))
      · intro h
        simp at h
    have hstep1 : (∑ ℓ ∈ s.image numCycles, (s.filter (fun σ => numCycles σ = ℓ)).card) =
        ∑ ℓ ∈ Finset.Icc L n, (s.filter (fun σ => numCycles σ = ℓ)).card :=
      Finset.sum_subset himg hzero
    have hstep2 : (∑ ℓ ∈ Finset.Icc L n, (s.filter (fun σ => numCycles σ = ℓ)).card) =
        ∑ ℓ ∈ Finset.Icc L n, ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      congr 1
      ext σ
      have hLℓ : L ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      by_cases hnum : numCycles σ = ℓ
      · simp [s, hnum, hLℓ]
      · simp [s, hnum]
    rw [hcard, hstep1, hstep2]
  rw [hpartition]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  have hLpos : 1 ≤ L := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog_pos : (0 : ℝ) < 1 + Real.log n := by
      linarith [Real.log_nonneg hnR]
    have hpos : (0 : ℝ) < (L : ℝ) - 1 := lt_of_lt_of_le
      (mul_pos (mul_pos (by norm_num : 0 < (2 : ℝ)) (Real.exp_pos 1)) hlog_pos) hL
    have hLone : (1 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast hLone
  calc (∑ ℓ ∈ Finset.Icc L n,
      ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ)).card /
        (Nat.factorial n : ℝ))
      ≤ ∑ ℓ ∈ Finset.Icc L n, (1 / 2 : ℝ) ^ (ℓ - 1) / (n : ℝ) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓL : L ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
          have hℓpos : 1 ≤ ℓ := le_trans hLpos hℓL
          have hℓm1 : 2 * Real.exp 1 * (1 + Real.log n) ≤ (ℓ - 1 : ℝ) := by
            exact le_trans hL (by exact_mod_cast (Nat.sub_le_sub_right hℓL 1))
          exact numCycles_prob_le_half ℓ n hn hℓpos hℓm1
    _ = (∑ ℓ ∈ Finset.Icc L n, (1 / 2 : ℝ) ^ (ℓ - 1)) / (n : ℝ) := by rw [Finset.sum_div]
    _ ≤ (2 : ℝ) * (1 / 2 : ℝ) ^ (L - 1) / (n : ℝ) := by
          have hgeom : (∑ ℓ ∈ Finset.Icc L n, (1 / 2 : ℝ) ^ (ℓ - 1)) ≤ 2 * (1 / 2 : ℝ) ^ (L - 1) := by
            calc (∑ ℓ ∈ Finset.Icc L n, (1 / 2 : ℝ) ^ (ℓ - 1))
                = (∑ i ∈ Finset.range (n + 1 - L), (1 / 2 : ℝ) ^ (L + i - 1)) := by
                    rw [show Finset.Icc L n = Finset.Ico L (n + 1) by rfl]
                    rw [Finset.sum_Ico_eq_sum_range (fun ℓ => (1 / 2 : ℝ) ^ (ℓ - 1)) L (n + 1)]
              _ = (1 / 2 : ℝ) ^ (L - 1) * (∑ i ∈ Finset.range (n + 1 - L), (1 / 2 : ℝ) ^ i) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [show L + i - 1 = L - 1 + i by omega, pow_add]
              _ ≤ (1 / 2 : ℝ) ^ (L - 1) * (1 / (1 - 1 / 2 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left
                      (geom_sum_le_inv_one_sub (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ) < 1) (n + 1 - L))
                      (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (L - 1))
              _ = 2 * (1 / 2 : ℝ) ^ (L - 1) := by
                    rw [show (1 / (1 - 1 / 2 : ℝ)) = 2 by norm_num]
                    ring
          exact div_le_div_of_nonneg_right hgeom (Nat.cast_nonneg n)

end MostProbableOrder
