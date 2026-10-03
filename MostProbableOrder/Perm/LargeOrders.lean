import MostProbableOrder.Perm.CyclesAndPrimes
import MostProbableOrder.Perm.Feller
import MostProbableOrder.Arithmetic.DivisorBounds
import MostProbableOrder.Arithmetic.FactorialBounds

/-!
# Proposition: large orders have small probability (``prop:large_orders``)

We formalize the decomposition of the event ``orderOf π = m`` into the three events
``E₁``, ``E₂``, ``E₃`` according to the number of cycles, and prove pointwise probability
bounds for each:

* ``E₁ = {c(πₙ) ≤ C₁ log log n,  ord(πₙ) = m}`` — bounded via Lemma 2.5 (`cyclesAndPrimes_prob_le`).
* ``E₂ = {C₁ log log n < c(πₙ) ≤ C₂ log n,  ord(πₙ) = m}`` — bounded via Corollary 2.4
  (`prob_numCycles_orderOf_dvd_le`) and Stirling's bound ``k! ≥ (k/e)^k``.
* ``E₃ = {c(πₙ) > C₂ log n,  ord(πₙ) = m}`` — bounded by the cycle-count upper tail
  (`numCycles_tail_le`).
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-! ### The three events -/

/-- `P(c(πₙ) ≤ L ∧ ord(πₙ) = m)` (event `E₁`). -/
noncomputable def prob_E1 (n m L : ℕ) : ℝ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter
    (fun σ => orderOf σ = m ∧ numCycles σ ≤ L)).card / (Nat.factorial n : ℝ)

/-- `P(L₁ < c(πₙ) ≤ L₂ ∧ ord(πₙ) = m)` (event `E₂`). -/
noncomputable def prob_E2 (n m L₁ L₂ : ℕ) : ℝ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter
    (fun σ => orderOf σ = m ∧ L₁ < numCycles σ ∧ numCycles σ ≤ L₂)).card / (Nat.factorial n : ℝ)

/-- `P(L₂ < c(πₙ) ∧ ord(πₙ) = m)` (event `E₃`). -/
noncomputable def prob_E3 (n m L₂ : ℕ) : ℝ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter
    (fun σ => orderOf σ = m ∧ L₂ < numCycles σ)).card / (Nat.factorial n : ℝ)

/-! ### Decomposition -/

/-- `numCycles σ ≥ 1` provided `n ≥ 1`. -/
lemma one_le_numCycles_of_pos {n : ℕ} (hn : 1 ≤ n) (σ : SymmetricGroup n) :
    1 ≤ numCycles σ := by
  have hcard : Fintype.card (Fin n) ≠ 0 := by rw [Fintype.card_fin]; omega
  refine Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero ?_)
  intro hz
  exact hcard ((numCycles_eq_zero_iff σ).mp hz)

/-- The cardinality decomposition of ``{σ | orderOf σ = m}`` into `E₁ ⊔ E₂ ⊔ E₃` (needs `L₁ ≤ L₂`). -/
lemma card_orderEq_eq_sum_E1_E2_E3 (n m L₁ L₂ : ℕ) (hLL : L₁ ≤ L₂) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m)).card =
      ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L₁)).card +
      ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ L₁ < numCycles σ ∧ numCycles σ ≤ L₂)).card +
      ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ L₂ < numCycles σ)).card := by
  classical
  let A := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L₁)
  let B := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ L₁ < numCycles σ ∧ numCycles σ ≤ L₂)
  let C := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ L₂ < numCycles σ)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro σ hσA hσB
    rw [Finset.mem_filter] at hσA hσB
    have h1 : numCycles σ ≤ L₁ := hσA.2.2
    have h2 : L₁ < numCycles σ := hσB.2.2.1
    omega
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro σ hσB hσC
    rw [Finset.mem_filter] at hσB hσC
    have h1 : numCycles σ ≤ L₂ := hσB.2.2.2
    have h2 : L₂ < numCycles σ := hσC.2.2
    omega
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro σ hσA hσC
    rw [Finset.mem_filter] at hσA hσC
    have h1 : numCycles σ ≤ L₁ := hσA.2.2
    have h2 : L₂ < numCycles σ := hσC.2.2
    omega
  have hA_BC : Disjoint A (B ∪ C) := by
    apply Finset.disjoint_left.mpr
    intro σ hσA hσBC
    rw [Finset.mem_union] at hσBC
    rcases hσBC with hσB | hσC
    · exact (Finset.disjoint_left.mp hAB) hσA hσB
    · exact (Finset.disjoint_left.mp hAC) hσA hσC
  have hfull : A ∪ (B ∪ C) = (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m) := by
    ext σ
    constructor
    · intro hσ
      rw [Finset.mem_union] at hσ
      rw [Finset.mem_filter]
      rcases hσ with hσA | hσBC
      · rw [Finset.mem_filter] at hσA
        exact ⟨Finset.mem_univ σ, hσA.2.1⟩
      · rw [Finset.mem_union] at hσBC
        rcases hσBC with hσB | hσC
        · rw [Finset.mem_filter] at hσB
          exact ⟨Finset.mem_univ σ, hσB.2.1⟩
        · rw [Finset.mem_filter] at hσC
          exact ⟨Finset.mem_univ σ, hσC.2.1⟩
    · intro hσ
      rw [Finset.mem_filter] at hσ
      rw [Finset.mem_union, Finset.mem_union]
      by_cases h1 : numCycles σ ≤ L₁
      · left
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ σ, ⟨hσ.2, h1⟩⟩
      · by_cases h2 : numCycles σ ≤ L₂
        · right; left
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ σ, ⟨hσ.2, by omega, h2⟩⟩
        · right; right
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ σ, ⟨hσ.2, by omega⟩⟩
  calc ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m)).card
      = (A ∪ (B ∪ C)).card := by rw [hfull]
    _ = A.card + (B ∪ C).card := by rw [Finset.card_union_of_disjoint hA_BC]
    _ = A.card + (B.card + C.card) := by rw [Finset.card_union_of_disjoint hBC]
    _ = A.card + B.card + C.card := by omega

/-- `pₙ(m) = P(E₁) + P(E₂) + P(E₃)` (the probability decomposition). -/
lemma p_eq_E1_add_E2_add_E3 (n m L₁ L₂ : ℕ) (hLL : L₁ ≤ L₂) :
    p n m = prob_E1 n m L₁ + prob_E2 n m L₁ L₂ + prob_E3 n m L₂ := by
  unfold p prob_E1 prob_E2 prob_E3
  rw [card_orderEq_eq_sum_E1_E2_E3 n m L₁ L₂ hLL]
  rw [Nat.cast_add, Nat.cast_add]
  ring

/-! ### The `E₃` bound (cycle-count upper tail) -/

/-- `P(E₃) ≤ 2·(1/2)^{L₂}/n` provided `2e(1 + log n) ≤ L₂`. -/
lemma prob_E3_le (n m L₂ : ℕ) (hn : 1 ≤ n)
    (h : 2 * Real.exp 1 * (1 + Real.log n) ≤ (L₂ : ℝ)) :
    prob_E3 n m L₂ ≤ (2 : ℝ) * (1 / 2 : ℝ) ^ L₂ / (n : ℝ) := by
  classical
  unfold prob_E3
  have hsub : ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ L₂ < numCycles σ)) ⊆
      ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => L₂ + 1 ≤ numCycles σ)) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨Finset.mem_univ σ, by omega⟩
  have hcard : ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ L₂ < numCycles σ)).card ≤
      ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => L₂ + 1 ≤ numCycles σ)).card :=
    Finset.card_le_card hsub
  have htail := numCycles_tail_le (L₂ + 1) n hn (by simpa [Nat.succ_sub_one] using h)
  calc ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => orderOf σ = m ∧ L₂ < numCycles σ)).card / (Nat.factorial n : ℝ)
      ≤ ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => L₂ + 1 ≤ numCycles σ)).card / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) * (1 / 2 : ℝ) ^ L₂ / (n : ℝ) := by
          simpa [Nat.succ_sub_one] using htail

/-! ### The `E₁` bound (Lemma 2.5) -/

/-- `∑_{ℓ∈Icc 1 L} ℓ^k ≤ L^(k+1)` for `L ≥ 1`. -/
lemma sum_Icc_pow_le (L k : ℕ) (hL : 1 ≤ L) :
    (∑ ℓ ∈ Finset.Icc 1 L, (ℓ : ℝ) ^ k) ≤ (L : ℝ) ^ (k + 1) := by
  classical
  have hcard : (Finset.Icc 1 L).card = L := by
    rw [Nat.card_Icc]
    omega
  have hle : ∀ ℓ ∈ Finset.Icc 1 L, (ℓ : ℝ) ^ k ≤ (L : ℝ) ^ k := by
    intro ℓ hℓ
    have hℓL : ℓ ≤ L := (Finset.mem_Icc.mp hℓ).2
    exact pow_le_pow_left₀ (Nat.cast_nonneg ℓ) (Nat.cast_le.mpr hℓL) k
  calc (∑ ℓ ∈ Finset.Icc 1 L, (ℓ : ℝ) ^ k)
      ≤ (Finset.Icc 1 L).card • (L : ℝ) ^ k := Finset.sum_le_card_nsmul _ _ _ hle
    _ = (L : ℝ) ^ (k + 1) := by
          rw [hcard, nsmul_eq_mul, pow_succ]
          ring

/-- Fiber partition of `{σ | orderOf σ = m ∧ numCycles σ ≤ L}` over `ℓ ∈ Icc 1 L`. -/
lemma card_orderEq_numCycles_le_fiber (n m L : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L)).card =
      ∑ ℓ ∈ Finset.Icc 1 L, ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ numCycles σ = ℓ)).card := by
  classical
  let s := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ numCycles σ ≤ L)
  have hpart := Finset.card_eq_sum_card_image (f := numCycles) (s := s)
  rw [hpart]
  have himg : s.image numCycles ⊆ Finset.Icc 1 L := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨σ, hσ, rfl⟩
    rw [Finset.mem_filter] at hσ
    exact Finset.mem_Icc.mpr ⟨one_le_numCycles_of_pos hn σ, hσ.2.2⟩
  have hzero : ∀ ℓ ∈ Finset.Icc 1 L, ℓ ∉ s.image numCycles → (s.filter (fun σ => numCycles σ = ℓ)).card = 0 := by
    intro ℓ hℓ hnot
    apply Finset.card_eq_zero.mpr
    ext σ
    constructor
    · intro hσ
      rw [Finset.mem_filter] at hσ
      exact False.elim (hnot (Finset.mem_image.mpr ⟨σ, hσ.1, hσ.2⟩))
    · intro h
      simp at h
  rw [Finset.sum_subset himg hzero]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hℓL : ℓ ≤ L := (Finset.mem_Icc.mp hℓ).2
  congr 1
  ext σ
  simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ⟨h.1.1, h.2⟩
  · intro h; exact ⟨⟨h.1, by rw [h.2]; exact hℓL⟩, h.2⟩

/-- **The `E₁` bound**: `P(E₁) ≤ L^{ω(m)+1}/m`. -/
lemma prob_E1_le (n m L₁ : ℕ) (hn : 1 ≤ n) (hm : m ≠ 0) (hL : 1 ≤ L₁) :
    prob_E1 n m L₁ ≤ (L₁ : ℝ) ^ (omega m + 1) / (m : ℝ) := by
  classical
  unfold prob_E1
  rw [card_orderEq_numCycles_le_fiber n m L₁ hn]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  calc (∑ ℓ ∈ Finset.Icc 1 L₁, ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => orderOf σ = m ∧ numCycles σ = ℓ)).card / (Nat.factorial n : ℝ))
      ≤ ∑ ℓ ∈ Finset.Icc 1 L₁, ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => numCycles σ = ℓ ∧ m ∣ orderOf σ)).card / (Nat.factorial n : ℝ) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hsub : ((Finset.univ : Finset (SymmetricGroup n)).filter
              (fun σ => orderOf σ = m ∧ numCycles σ = ℓ)) ⊆
            ((Finset.univ : Finset (SymmetricGroup n)).filter
              (fun σ => numCycles σ = ℓ ∧ m ∣ orderOf σ)) := by
            intro σ hσ
            rw [Finset.mem_filter] at hσ ⊢
            exact ⟨Finset.mem_univ σ, hσ.2.2, by rw [hσ.2.1]⟩
          exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) (Nat.cast_nonneg _)
      _ ≤ ∑ ℓ ∈ Finset.Icc 1 L₁, (ℓ : ℝ) ^ omega m / (m : ℝ) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          exact cyclesAndPrimes_prob_le ℓ m n hm
      _ = (∑ ℓ ∈ Finset.Icc 1 L₁, (ℓ : ℝ) ^ omega m) / (m : ℝ) := by
          rw [Finset.sum_div]
      _ ≤ (L₁ : ℝ) ^ (omega m + 1) / (m : ℝ) := by
          exact div_le_div_of_nonneg_right (sum_Icc_pow_le L₁ (omega m) hL) (Nat.cast_nonneg m)


/-! ### The `E₂` bound (Corollary 2.4 + Stirling) -/

/-- **Stirling**: `1/k! ≤ (e/k)^k` for `k ≥ 1`. -/
lemma inv_factorial_le (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / (Nat.factorial k : ℝ) ≤ (Real.exp 1 / (k : ℝ)) ^ k := by
  have h := pow_div_exp_le_factorial (k := k) hk
  have hkposR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : k ≠ 0))
  have hfacpos : (0 : ℝ) < Nat.factorial k := by positivity
  have hkpowpos : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkposR k
  have hepowpos : (0 : ℝ) < Real.exp 1 ^ k := pow_pos (Real.exp_pos 1) k
  have hkk : (k : ℝ) ^ k ≤ (Nat.factorial k : ℝ) * Real.exp 1 ^ k := by
    exact (div_le_iff₀ hepowpos).mp (by simpa [div_pow] using h)
  rw [div_pow]
  rw [div_le_div_iff₀ hfacpos hkpowpos]
  simpa [mul_comm] using hkk

/-- `σ(m)/m ≥ 0`. -/
lemma sigma_div_nonneg (m : ℕ) : 0 ≤ (sigma m : ℝ) / (m : ℝ) := by
  by_cases hm : m = 0
  · simp [hm]
  · exact div_nonneg (by exact_mod_cast (Nat.zero_le (sigma m))) (Nat.cast_nonneg m)

/-- The `E₂` summand bound: `(σ(m)/m)^{ℓ-1}/(n·(ℓ-1)!) ≤ (1/2)^{L₁}/n` provided
`2e·σ(m) ≤ L₁·m` and `L₁ + 1 ≤ ℓ`. -/
lemma E2_summand_le (n m ℓ L₁ : ℕ) (hn : 1 ≤ n) (hm : m ≠ 0) (hℓpos : 1 ≤ ℓ)
    (hL₁ : 1 ≤ L₁) (hL₁ℓ : L₁ + 1 ≤ ℓ)
    (h : 2 * Real.exp 1 * (sigma m : ℝ) ≤ (L₁ : ℝ) * (m : ℝ)) :
    ((sigma m : ℝ) / (m : ℝ)) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) ≤
      (1 / 2 : ℝ) ^ L₁ / (n : ℝ) := by
  let a : ℝ := (sigma m : ℝ) / (m : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; exact sigma_div_nonneg m
  have hℓm1pos : 1 ≤ ℓ - 1 := by omega
  have hL₁m1 : L₁ ≤ ℓ - 1 := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : n ≠ 0))
  have hℓm1posR : 0 < (((ℓ - 1 : ℕ) : ℝ)) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : ℓ - 1 ≠ 0))
  have hL₁posR : 0 < (L₁ : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : L₁ ≠ 0))
  have hae_le : a * Real.exp 1 ≤ (L₁ : ℝ) / 2 := by
    dsimp [a]
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    field_simp [ne_of_gt hmpos]
    unfold sigma at h
    nlinarith [h]
  have hae_div : a * Real.exp 1 / (L₁ : ℝ) ≤ (1 : ℝ) / 2 := by
    rw [div_le_div_iff₀ hL₁posR (by norm_num : 0 < (2:ℝ))]
    nlinarith [hae_le]
  have h_inv : (((ℓ - 1 : ℕ) : ℝ))⁻¹ ≤ (L₁ : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hℓm1posR hL₁posR).mpr (by exact_mod_cast hL₁m1)
  have h_e_div : Real.exp 1 / (((ℓ - 1 : ℕ) : ℝ)) ≤ Real.exp 1 / (L₁ : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h_inv (Real.exp_pos 1).le
  have hae_div_ℓ : a * (Real.exp 1 / (((ℓ - 1 : ℕ) : ℝ))) ≤ (1 : ℝ) / 2 := by
    calc a * (Real.exp 1 / (((ℓ - 1 : ℕ) : ℝ)))
        = (a * Real.exp 1) / (((ℓ - 1 : ℕ) : ℝ)) := by field_simp [ne_of_gt hℓm1posR]
      _ ≤ (a * Real.exp 1) / (L₁ : ℝ) := by
            exact div_le_div_of_nonneg_left (mul_nonneg ha (Real.exp_pos 1).le) hL₁posR (by exact_mod_cast hL₁m1)
      _ ≤ (1 : ℝ) / 2 := hae_div
  calc a ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ))
      = a ^ (ℓ - 1) * (1 / (Nat.factorial (ℓ - 1) : ℝ)) / (n : ℝ) := by
          have hfacpos : 0 < (Nat.factorial (ℓ - 1) : ℝ) := by positivity
          field_simp [ne_of_gt hnpos, ne_of_gt hfacpos]
    _ ≤ a ^ (ℓ - 1) * (Real.exp 1 / (((ℓ - 1 : ℕ) : ℝ))) ^ (ℓ - 1) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (inv_factorial_le (ℓ - 1) hℓm1pos) (pow_nonneg ha (ℓ - 1)))
            (Nat.cast_nonneg n)
    _ = (a * (Real.exp 1 / (((ℓ - 1 : ℕ) : ℝ)))) ^ (ℓ - 1) / (n : ℝ) := by
          rw [mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ (ℓ - 1) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (mul_nonneg ha (div_nonneg (Real.exp_pos 1).le hℓm1posR.le)) hae_div_ℓ (ℓ - 1))
            (Nat.cast_nonneg n)
    _ ≤ (1 / 2 : ℝ) ^ L₁ / (n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (pow_le_pow_of_le_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ) ≤ 1) hL₁m1)
            (Nat.cast_nonneg n)

/-- Fiber partition of `{σ | orderOf σ = m ∧ L₁ < numCycles σ ∧ numCycles σ ≤ L₂}` over `ℓ ∈ Icc (L₁+1) L₂`. -/
lemma card_orderEq_numCycles_between_fiber (n m L₁ L₂ : ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ L₁ < numCycles σ ∧ numCycles σ ≤ L₂)).card =
      ∑ ℓ ∈ Finset.Icc (L₁ + 1) L₂, ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => orderOf σ = m ∧ numCycles σ = ℓ)).card := by
  classical
  let s := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => orderOf σ = m ∧ L₁ < numCycles σ ∧ numCycles σ ≤ L₂)
  have hpart := Finset.card_eq_sum_card_image (f := numCycles) (s := s)
  rw [hpart]
  have himg : s.image numCycles ⊆ Finset.Icc (L₁ + 1) L₂ := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨σ, hσ, rfl⟩
    rw [Finset.mem_filter] at hσ
    exact Finset.mem_Icc.mpr ⟨by omega, hσ.2.2.2⟩
  have hzero : ∀ ℓ ∈ Finset.Icc (L₁ + 1) L₂, ℓ ∉ s.image numCycles → (s.filter (fun σ => numCycles σ = ℓ)).card = 0 := by
    intro ℓ hℓ hnot
    apply Finset.card_eq_zero.mpr
    ext σ
    constructor
    · intro hσ
      rw [Finset.mem_filter] at hσ
      exact False.elim (hnot (Finset.mem_image.mpr ⟨σ, hσ.1, hσ.2⟩))
    · intro h
      simp at h
  rw [Finset.sum_subset himg hzero]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hℓL : L₁ < ℓ ∧ ℓ ≤ L₂ := by
    have := Finset.mem_Icc.mp hℓ
    constructor <;> omega
  congr 1
  ext σ
  simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ⟨h.1.1, h.2⟩
  · intro h; exact ⟨⟨h.1, by rw [h.2]; exact hℓL.1, by rw [h.2]; exact hℓL.2⟩, h.2⟩

/-- **The `E₂` bound**: `P(E₂) ≤ L₂·(1/2)^{L₁}/n` provided `2e·σ(m) ≤ L₁·m`. -/
lemma prob_E2_le (n m L₁ L₂ : ℕ) (hn : 1 ≤ n) (hm : m ≠ 0) (hL₁ : 1 ≤ L₁)
    (h : 2 * Real.exp 1 * (sigma m : ℝ) ≤ (L₁ : ℝ) * (m : ℝ)) :
    prob_E2 n m L₁ L₂ ≤ (L₂ : ℝ) * (1 / 2 : ℝ) ^ L₁ / (n : ℝ) := by
  classical
  unfold prob_E2
  rw [card_orderEq_numCycles_between_fiber n m L₁ L₂]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  calc (∑ ℓ ∈ Finset.Icc (L₁ + 1) L₂, ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => orderOf σ = m ∧ numCycles σ = ℓ)).card / (Nat.factorial n : ℝ))
      ≤ ∑ ℓ ∈ Finset.Icc (L₁ + 1) L₂, ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun σ => numCycles σ = ℓ ∧ orderOf σ ∣ m)).card / (Nat.factorial n : ℝ) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hsub : ((Finset.univ : Finset (SymmetricGroup n)).filter
              (fun σ => orderOf σ = m ∧ numCycles σ = ℓ)) ⊆
            ((Finset.univ : Finset (SymmetricGroup n)).filter
              (fun σ => numCycles σ = ℓ ∧ orderOf σ ∣ m)) := by
            intro σ hσ
            rw [Finset.mem_filter] at hσ ⊢
            exact ⟨Finset.mem_univ σ, hσ.2.2, by rw [hσ.2.1]⟩
          exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) (Nat.cast_nonneg _)
      _ ≤ ∑ ℓ ∈ Finset.Icc (L₁ + 1) L₂, ((sigma m : ℝ) / (m : ℝ)) ^ (ℓ - 1) /
          ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓpos : 1 ≤ ℓ := by
            have hmem := Finset.mem_Icc.mp hℓ
            omega
          exact prob_numCycles_orderOf_dvd_le ℓ n m hℓpos hn hm
      _ ≤ ∑ ℓ ∈ Finset.Icc (L₁ + 1) L₂, (1 / 2 : ℝ) ^ L₁ / (n : ℝ) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓpos : 1 ≤ ℓ := by
            have hmem := Finset.mem_Icc.mp hℓ
            omega
          have hL₁ℓ : L₁ + 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
          exact E2_summand_le n m ℓ L₁ hn hm hℓpos hL₁ hL₁ℓ h
      _ = ((Finset.Icc (L₁ + 1) L₂).card : ℝ) * ((1 / 2 : ℝ) ^ L₁ / (n : ℝ)) := by
          rw [Finset.sum_const]
          rw [nsmul_eq_mul]
      _ ≤ (L₂ : ℝ) * ((1 / 2 : ℝ) ^ L₁ / (n : ℝ)) := by
          have hcard_le : (Finset.Icc (L₁ + 1) L₂).card ≤ L₂ := by
            rw [Nat.card_Icc]
            omega
          have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ L₁ / (n : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_le) hnonneg
      _ = (L₂ : ℝ) * (1 / 2 : ℝ) ^ L₁ / (n : ℝ) := by ring


/-! ### The master bound -/

/-- **Master bound**: for , , thresholds , with
 and ,
. -/
lemma p_le_master (n m L₁ L₂ : ℕ) (hn : 1 ≤ n) (hm : m ≠ 0) (hL₁ : 1 ≤ L₁) (hLL : L₁ ≤ L₂)
    (hE2 : 2 * Real.exp 1 * (sigma m : ℝ) ≤ (L₁ : ℝ) * (m : ℝ))
    (hE3 : 2 * Real.exp 1 * (1 + Real.log n) ≤ (L₂ : ℝ)) :
    p n m ≤ (L₁ : ℝ) ^ (omega m + 1) / (m : ℝ) +
        (L₂ : ℝ) * (1 / 2 : ℝ) ^ L₁ / (n : ℝ) +
        (2 : ℝ) * (1 / 2 : ℝ) ^ L₂ / (n : ℝ) := by
  rw [p_eq_E1_add_E2_add_E3 n m L₁ L₂ hLL]
  exact add_le_add (add_le_add (prob_E1_le n m L₁ hn hm hL₁)
      (prob_E2_le n m L₁ L₂ hn hm hL₁ hE2)) (prob_E3_le n m L₂ hn hE3)

end MostProbableOrder


