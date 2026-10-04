import MostProbableOrder.Perm.Theorem12
import Mathlib.NumberTheory.Chebyshev
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Warlimont's theorem — the `Tᵢ` decomposition of Proposition 4.1

This file formalizes the proof of Proposition 4.1 (`prop:exact_order`), the
deep input of Theorem 1.2, following the paper's §4 sketch and the method of
Warlimont [1978].

The starting point is **Cauchy's formula** (Ford's *Cycle Type of Random
Permutations: a Toolkit*, Theorem 1.2, = mathlib `Equiv.Perm.card_of_cycleType`):

  `#{g : cycleType g = λ} = n! / ((n-|λ|)! · λ.prod · ∏_{d} (count λ d)!)`.

Consequently the probability that a uniformly random permutation of `[n]` has
order exactly `m` is the sum of the *cycle-type weights*

  `w_n(λ) = 1 / ((n-|λ|)! · λ.prod · ∏_{d} (count λ d)!)`

over all cycle types `λ` (multisets of cycle lengths ≥ 2, summing to ≤ n) with
`lcm λ = m`.
-/

open Finset
open Filter
open scoped Real Topology

namespace MostProbableOrder

/-! ### The cycle-type weight and Cauchy's formula -/

/-- The set of cycle types that occur in `Sₙ` (the image of `cycleType`). -/
def cycleTypes (n : ℕ) : Finset (Multiset ℕ) :=
  (Finset.univ : Finset (SymmetricGroup n)).image (fun g => g.cycleType)

/-- The cycle-type probability weight: the probability that a random
permutation of `[n]` has cycle type `lam` (Cauchy's formula). Valid when
`lam.sum ≤ n` and all entries of `lam` are ≥ 2. -/
noncomputable def cycleTypeWeight (n : ℕ) (lam : Multiset ℕ) : ℝ :=
  (1 : ℝ) / (((Nat.factorial (n - lam.sum) : ℝ) * (lam.prod : ℝ)) *
    (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)))

/-- The probability that a random permutation of `[n]` has cycle type `lam` is
`cycleTypeWeight n lam` (for a valid cycle type `lam ∈ cycleTypes n`). -/
lemma cycleTypeWeight_eq_prob (n : ℕ) (lam : Multiset ℕ) (hlam : lam ∈ cycleTypes n) :
    cycleTypeWeight n lam =
      (((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => g.cycleType = lam)).card : ℝ) /
        (Nat.factorial n : ℝ) := by
  have hsum : lam.sum ≤ n := by
    rcases (Finset.mem_image.mp hlam) with ⟨g, _, hg⟩
    have := Equiv.Perm.sum_cycleType_le g
    rw [hg, Fintype.card_fin] at this
    exact this
  have h2 : ∀ a ∈ lam, 2 ≤ a := by
    rcases (Finset.mem_image.mp hlam) with ⟨g, _, hg⟩
    intro a ha
    rw [← hg] at ha
    exact Equiv.Perm.two_le_of_mem_cycleType ha
  have hvalid : lam.sum ≤ n ∧ ∀ a ∈ lam, 2 ≤ a := ⟨hsum, h2⟩
  have hcard_mul := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin n) lam
  rw [show #({g : SymmetricGroup n | g.cycleType = lam} : Finset (SymmetricGroup n))
        = ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => g.cycleType = lam)).card from rfl] at hcard_mul
  rw [Fintype.card_fin, if_pos hvalid] at hcard_mul
  have hcard_mulR : (((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => g.cycleType = lam)).card : ℝ) *
        (((Nat.factorial (n - lam.sum) : ℝ) * (lam.prod : ℝ) *
          (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)))) = (Nat.factorial n : ℝ) := by
    rw [← Nat.cast_mul]
    exact_mod_cast hcard_mul
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hden : ((Nat.factorial (n - lam.sum) : ℝ) * (lam.prod : ℝ) *
      (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · positivity
    · have hprod_pos : 0 < (lam.prod : ℝ) := by
        exact_mod_cast (Multiset.prod_pos (fun a ha => Nat.succ_le_iff.mp (by
          have := h2 a ha; omega)))
      exact ne_of_gt hprod_pos
    · have hprod_pos : 0 < (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)) := by
        exact Finset.prod_pos (fun d hd => by positivity)
      exact ne_of_gt hprod_pos
  unfold cycleTypeWeight
  rw [div_eq_div_iff hden hfac]
  -- goal: 1 * (n!) = (filter card) * den
  simpa only [one_mul] using hcard_mulR.symm

/-- The fiber of `cycleType` over `lam`, intersected with the order-`m` event, has
cardinality `#{g : cycleType g = lam}` if `lcm lam = m`, and `0` otherwise. -/
lemma card_filter_orderOf_cycleType (n m : ℕ) (lam : Multiset ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun g => orderOf g = m ∧ g.cycleType = lam)).card =
      if lam.lcm = m then
        ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => g.cycleType = lam)).card
      else 0 := by
  by_cases h : lam.lcm = m
  · have hset : ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun g => orderOf g = m ∧ g.cycleType = lam)) =
        ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => g.cycleType = lam)) := by
      apply Finset.ext
      intro g
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro hg; exact hg.2
      · intro hg
        exact ⟨by rw [← Equiv.Perm.lcm_cycleType g, hg, h], hg⟩
    rw [hset, if_pos h]
  · have hset : ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun g => orderOf g = m ∧ g.cycleType = lam)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro g _ hg
      have hct := hg.2
      have ho := hg.1
      have h' : lam.lcm = m := by
        rw [← hct, Equiv.Perm.lcm_cycleType g, ho]
      exact h h'
    rw [hset, Finset.card_empty, if_neg h]

/-- The number of permutations of order `m` is the sum, over cycle types `lam`
with `lcm lam = m`, of the number of permutations of cycle type `lam`. -/
lemma card_orderEq_eq_sum_fiber (n m : ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = m)).card =
      ∑ lam ∈ cycleTypes n, if lam.lcm = m then
        ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => g.cycleType = lam)).card
      else 0 := by
  classical
  let s : Finset (SymmetricGroup n) := Finset.univ.filter (fun g => orderOf g = m)
  let t : Finset (Multiset ℕ) := cycleTypes n
  have hMaps : Set.MapsTo (fun g : SymmetricGroup n => g.cycleType) (↑s : Set (SymmetricGroup n))
      (↑t : Set (Multiset ℕ)) := by
    intro g hg
    change g.cycleType ∈ t
    dsimp [t, cycleTypes]
    exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun g : SymmetricGroup n => g.cycleType) (s := s) (t := t) hMaps
  rw [h]
  dsimp [s, t, cycleTypes]
  apply Finset.sum_congr rfl
  intro lam hlam
  have hfiber : ((Finset.univ : Finset (SymmetricGroup n)).filter
      (fun g => orderOf g = m)).filter (fun g => g.cycleType = lam) =
      (Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = m ∧ g.cycleType = lam) := by
    apply Finset.ext
    intro g
    simp only [mem_filter, mem_univ, true_and, and_assoc]
  rw [hfiber, card_filter_orderOf_cycleType]

/-- **Cauchy's formula for the order distribution**: the probability that a
random permutation of `[n]` has order `m` is the sum of the cycle-type weights
over all cycle types `lam` with `lcm lam = m`. -/
theorem p_eq_sum_cycleType (n m : ℕ) [NeZero n] :
    p n m = ∑ lam ∈ cycleTypes n, if lam.lcm = m then cycleTypeWeight n lam else 0 := by
  unfold p
  rw [card_orderEq_eq_sum_fiber]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro lam hlam
  by_cases h : lam.lcm = m
  · simp [h]
    exact (cycleTypeWeight_eq_prob n lam hlam).symm
  · simp [h]

/-! ### The leading term `1/(n-k)`: permutations with an `(n-k)`-cycle -/

/-- A valid cycle type on `n` points has sum at most `n`. -/
lemma mem_cycleTypes_sum_le {n : ℕ} {lam : Multiset ℕ} (h : lam ∈ cycleTypes n) : lam.sum ≤ n := by
  rcases (Finset.mem_image.mp h) with ⟨g, _, hg⟩
  have := Equiv.Perm.sum_cycleType_le g
  rw [hg, Fintype.card_fin] at this
  exact this

/-- A valid cycle type on `n` points has all entries at least `2`. -/
lemma mem_cycleTypes_two_le {n : ℕ} {lam : Multiset ℕ} (h : lam ∈ cycleTypes n) :
    ∀ a ∈ lam, 2 ≤ a := by
  rcases (Finset.mem_image.mp h) with ⟨g, _, hg⟩
  intro a ha
  rw [← hg] at ha
  exact Equiv.Perm.two_le_of_mem_cycleType ha

/-- Adding an `(n-k)`-cycle (with `2 ≤ n-k`) to a valid cycle type of `Sₖ` gives a
valid cycle type of `Sₙ` (requires `k ≤ n`). -/
lemma mem_cycleTypes_cons (n k : ℕ) {μ : Multiset ℕ} (hμ : μ ∈ cycleTypes k)
    (hnk2 : 2 ≤ n - k) (hk_le : k ≤ n) : (n - k) ::ₘ μ ∈ cycleTypes n := by
  dsimp [cycleTypes]
  rw [Finset.mem_image]
  have hex : ∃ g : SymmetricGroup n, g.cycleType = (n - k) ::ₘ μ := by
    rw [Equiv.Perm.exists_with_cycleType_iff (α := Fin n)]
    constructor
    · rw [Multiset.sum_cons, Fintype.card_fin]
      calc (n - k) + μ.sum ≤ (n - k) + k := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left (mem_cycleTypes_sum_le hμ) (n - k)
        _ = n := Nat.sub_add_cancel hk_le
    · intro a ha
      rw [Multiset.mem_cons] at ha
      rcases ha with ha | ha
      · subst a; exact hnk2
      · exact mem_cycleTypes_two_le hμ a ha
  rcases hex with ⟨g, hg⟩
  exact ⟨g, Finset.mem_univ g, hg⟩

/-- Removing an `(n-k)`-cycle from a valid cycle type of `Sₙ` gives a valid cycle
type of `Sₖ` (requires `k ≤ n`). -/
lemma mem_cycleTypes_erase (n k : ℕ) {lam : Multiset ℕ} (hlam : lam ∈ cycleTypes n)
    (hnkmem : n - k ∈ lam) (hk_le : k ≤ n) : lam.erase (n - k) ∈ cycleTypes k := by
  dsimp [cycleTypes]
  rw [Finset.mem_image]
  have hex : ∃ g : SymmetricGroup k, g.cycleType = lam.erase (n - k) := by
    rw [Equiv.Perm.exists_with_cycleType_iff (α := Fin k)]
    constructor
    · rw [Fintype.card_fin]
      have hsum : (n - k) + (lam.erase (n - k)).sum = lam.sum := Multiset.sum_erase hnkmem
      have hle : (n - k) + (lam.erase (n - k)).sum ≤ n := by
        rw [hsum]
        exact mem_cycleTypes_sum_le hlam
      omega
    · intro a ha
      exact mem_cycleTypes_two_le hlam a (Multiset.mem_of_mem_erase ha)
  rcases hex with ⟨g, hg⟩
  exact ⟨g, Finset.mem_univ g, hg⟩

/-- Prepend an `(n-k)`-cycle to a cycle type `μ` of `Sₖ`: the Cauchy weight of
`μ` equals `(n-k)` times the Cauchy weight of `(n-k) ::ₘ μ` in `Sₙ`. Valid when
`n-k > k` (so `n-k ∉ μ`) and `μ.sum ≤ k`. -/
lemma cycleTypeWeight_cons_eq (n k : ℕ) (μ : Multiset ℕ)
    (hμsum : μ.sum ≤ k) (hμ2 : ∀ a ∈ μ, 2 ≤ a) (hnk_gt : k < n - k) :
    cycleTypeWeight k μ = ((n - k : ℕ) : ℝ) * cycleTypeWeight n ((n - k) ::ₘ μ) := by
  have hnk_notmem : n - k ∉ μ := by
    intro hmem
    have ha_le : n - k ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) (n - k) hmem
    omega
  unfold cycleTypeWeight
  rw [Multiset.sum_cons, Multiset.prod_cons, Multiset.toFinset_cons]
  have hn_sub : n - (n - k + μ.sum) = k - μ.sum := by omega
  rw [hn_sub]
  have htoFinset_nk : n - k ∉ μ.toFinset := by
    rw [Multiset.mem_toFinset]; exact hnk_notmem
  rw [Finset.prod_insert htoFinset_nk]
  have hcount_nk : Multiset.count (n - k) ((n - k) ::ₘ μ) = 1 := by
    rw [Multiset.count_cons]
    rw [Multiset.count_eq_zero.mpr hnk_notmem]
    simp
  rw [hcount_nk]
  simp only [Nat.factorial_one, Nat.cast_one, one_mul]
  have hprod_congr : (∏ d ∈ μ.toFinset, (Nat.factorial (Multiset.count d ((n - k) ::ₘ μ)) : ℝ)) =
      (∏ d ∈ μ.toFinset, (Nat.factorial (Multiset.count d μ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro d hd
    have hd_mem : d ∈ μ := by rwa [Multiset.mem_toFinset] at hd
    have hd_ne : d ≠ n - k := by
      intro hEq
      subst hEq
      exact hnk_notmem hd_mem
    rw [Multiset.count_cons]
    simp [hd_ne]
  rw [hprod_congr]
  have hnk_ne : (n - k : ℕ) ≠ 0 := by omega
  have hnkR : ((n - k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hnk_ne
  have hD : (((Nat.factorial (k - μ.sum) : ℝ) * (μ.prod : ℝ) *
      (∏ d ∈ μ.toFinset, (Nat.factorial (μ.count d) : ℝ)))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · positivity
    · have hprod_pos : 0 < (μ.prod : ℝ) := by
        exact_mod_cast (Multiset.prod_pos (fun a ha => Nat.succ_le_iff.mp (by
          have := hμ2 a ha; omega)))
      exact ne_of_gt hprod_pos
    · have hprod_pos : 0 < (∏ d ∈ μ.toFinset, (Nat.factorial (μ.count d) : ℝ)) := by
        exact Finset.prod_pos (fun d hd => by positivity)
      exact ne_of_gt hprod_pos
  rw [Nat.cast_mul]
  field_simp [hnkR, hD]

/-- The cycle-type weights over all cycle types of `Sₖ` sum to `1` (the total
probability of a cycle type is 1). -/
lemma sum_cycleTypeWeight_eq_one (k : ℕ) :
    (∑ μ ∈ cycleTypes k, cycleTypeWeight k μ) = 1 := by
  by_cases hk : k = 0
  · subst k
    simp [cycleTypes, cycleTypeWeight]
  · haveI : NeZero k := ⟨hk⟩
    have hfibers : (∑ μ ∈ cycleTypes k,
        ((Finset.univ : Finset (SymmetricGroup k)).filter (fun g => g.cycleType = μ)).card) =
        Fintype.card (SymmetricGroup k) := by
      let t : Finset (Multiset ℕ) := cycleTypes k
      have hMaps : Set.MapsTo (fun g : SymmetricGroup k => g.cycleType)
          (↑(Finset.univ : Finset (SymmetricGroup k)) : Set (SymmetricGroup k)) (↑t : Set (Multiset ℕ)) := by
        intro g hg
        change g.cycleType ∈ t
        dsimp [t, cycleTypes]
        exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
      have h := Finset.card_eq_sum_card_fiberwise
        (f := fun g : SymmetricGroup k => g.cycleType) (s := (Finset.univ : Finset (SymmetricGroup k)))
        (t := t) hMaps
      simpa [t, cycleTypes] using h.symm
    rw [show (∑ μ ∈ cycleTypes k, cycleTypeWeight k μ) =
        (∑ μ ∈ cycleTypes k, (((Finset.univ : Finset (SymmetricGroup k)).filter (fun g => g.cycleType = μ)).card : ℝ)) /
          (Nat.factorial k : ℝ) by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro μ hμ
      exact cycleTypeWeight_eq_prob k μ hμ]
    rw [← Nat.cast_sum, hfibers]
    rw [card_symmetricGroup]
    have hfac : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    exact div_self hfac

/-- **The leading term**: the probability that a random permutation of `[n]` has
a cycle of length `n-k` equals `1/(n-k)` (when `n-k > k`, so there is at most
one such cycle). -/
lemma sum_cycleTypeWeight_of_mem_nk (n k : ℕ) (hnk_gt : k < n - k) (hnk2 : 2 ≤ n - k) :
    (∑ lam ∈ cycleTypes n, if n - k ∈ lam then cycleTypeWeight n lam else 0) = 1 / ((n - k : ℕ) : ℝ) := by
  have hk_le : k ≤ n := by omega
  let t : Finset (Multiset ℕ) := (cycleTypes n).filter (fun lam => n - k ∈ lam)
  have hbij : (∑ μ ∈ cycleTypes k, cycleTypeWeight k μ) =
      ∑ lam ∈ t, ((n - k : ℕ) : ℝ) * cycleTypeWeight n lam := by
    refine Finset.sum_bij (fun μ _ => (n - k) ::ₘ μ) ?_ ?_ ?_ ?_
    · intro μ hμ
      dsimp [t]
      rw [Finset.mem_filter]
      constructor
      · exact mem_cycleTypes_cons n k hμ hnk2 hk_le
      · exact Multiset.mem_cons.mpr (Or.inl rfl)
    · intro μ₁ hμ₁ μ₂ hμ₂ h
      exact Multiset.cons_inj_right (n - k) |>.mp h
    · intro lam hlam
      dsimp [t] at hlam
      rw [Finset.mem_filter] at hlam
      have hnkmem : n - k ∈ lam := hlam.2
      refine ⟨lam.erase (n - k), ?_, Multiset.cons_erase hnkmem⟩
      exact mem_cycleTypes_erase n k hlam.1 hnkmem hk_le
    · intro μ hμ
      exact cycleTypeWeight_cons_eq n k μ (mem_cycleTypes_sum_le hμ) (mem_cycleTypes_two_le hμ) hnk_gt
  have hmul : (∑ lam ∈ cycleTypes n, if n - k ∈ lam then ((n - k : ℕ) : ℝ) * cycleTypeWeight n lam else 0) =
      ((n - k : ℕ) : ℝ) * (∑ lam ∈ cycleTypes n, if n - k ∈ lam then cycleTypeWeight n lam else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lam hlam
    by_cases h : n - k ∈ lam <;> simp [h]
  have hbase : (1 : ℝ) = ∑ lam ∈ t, ((n - k : ℕ) : ℝ) * cycleTypeWeight n lam := by
    rw [← sum_cycleTypeWeight_eq_one, hbij]
  have h1 : (1 : ℝ) = ((n - k : ℕ) : ℝ) *
      (∑ lam ∈ cycleTypes n, if n - k ∈ lam then cycleTypeWeight n lam else 0) := by
    rw [hbase]
    dsimp [t]
    rw [Finset.sum_filter]
    exact hmul
  have hnkR : ((n - k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : (n - k : ℕ) ≠ 0)
  rw [div_eq_mul_inv, one_mul]
  refine mul_left_cancel₀ hnkR ?_
  calc ((n - k : ℕ) : ℝ) * (∑ lam ∈ cycleTypes n, if n - k ∈ lam then cycleTypeWeight n lam else 0)
      = 1 := h1.symm
    _ = ((n - k : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hnkR]

/-! ### The `Tᵢ` decomposition: decoupling large and small cycles -/

/-- **Decoupling**: for disjoint cycle-type parts `L` (large) and `S` (small), the
Cauchy weight of `L + S` in `Sₙ` equals `1/(L.prod · ∏_{d} count_L(d)!)` times the
weight of `S` in `S_{n-|L|}`. -/
lemma cycleTypeWeight_add_eq (n : ℕ) (L S : Multiset ℕ) (hdisj : Disjoint L.toFinset S.toFinset)
    (hL2 : ∀ d ∈ L, 2 ≤ d) (hS2 : ∀ d ∈ S, 2 ≤ d) (hsum : L.sum + S.sum ≤ n) :
    cycleTypeWeight n (L + S) =
      (1 / ((L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)))) *
        cycleTypeWeight (n - L.sum) S := by
  unfold cycleTypeWeight
  rw [Multiset.sum_add, Multiset.prod_add, Multiset.toFinset_add]
  rw [show n - (L.sum + S.sum) = (n - L.sum) - S.sum by omega]
  rw [Finset.prod_union hdisj]
  have hcountL : (∏ d ∈ L.toFinset, (Nat.factorial (Multiset.count d (L + S)) : ℝ)) =
      (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro d hd
    have hdL : d ∈ L := by rwa [Multiset.mem_toFinset] at hd
    have hdS : d ∉ S := by
      intro h'
      exact (Finset.disjoint_left.mp hdisj hd) (Multiset.mem_toFinset.mpr h')
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr hdS]
    simp
  have hcountS : (∏ d ∈ S.toFinset, (Nat.factorial (Multiset.count d (L + S)) : ℝ)) =
      (∏ d ∈ S.toFinset, (Nat.factorial (S.count d) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro d hd
    have hdS : d ∈ S := by rwa [Multiset.mem_toFinset] at hd
    have hdL : d ∉ L := by
      intro h'
      exact (Finset.disjoint_left.mp hdisj (Multiset.mem_toFinset.mpr h')) hd
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr hdL]
    simp
  rw [hcountL, hcountS]
  have hLprod : (L.prod : ℝ) ≠ 0 := by
    have hpos : 0 < (L.prod : ℝ) := by
      exact_mod_cast (Multiset.prod_pos (fun d hd => Nat.succ_le_iff.mp (by
        have := hL2 d hd; omega)))
    exact ne_of_gt hpos
  have hSprod : (S.prod : ℝ) ≠ 0 := by
    have hpos : 0 < (S.prod : ℝ) := by
      exact_mod_cast (Multiset.prod_pos (fun d hd => Nat.succ_le_iff.mp (by
        have := hS2 d hd; omega)))
    exact ne_of_gt hpos
  have hLcount : (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun d hd => by positivity)
  have hScount : (∏ d ∈ S.toFinset, (Nat.factorial (S.count d) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun d hd => by positivity)
  have hfac : (Nat.factorial (n - L.sum - S.sum) : ℝ) ≠ 0 := by positivity
  field_simp [hfac, hLprod, hSprod, hLcount, hScount]
  rw [Nat.cast_mul]
  exact mul_inv_cancel₀ (mul_ne_zero hLprod hSprod)

/-- **Decoupling bound**: summing the small part `S` out, the total weight of all
cycle types with a fixed large part `L` (and a small part disjoint from `L`) is at
most `1/L.prod`. -/
lemma sum_cycleTypeWeight_add_le (n : ℕ) (L : Multiset ℕ) (hL2 : ∀ d ∈ L, 2 ≤ d)
    (hLsum : L.sum ≤ n) :
    (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
        cycleTypeWeight n (L + S)) ≤ 1 / (L.prod : ℝ) := by
  have hLprod_pos : 0 < (L.prod : ℝ) := by
    exact_mod_cast (Multiset.prod_pos (fun d hd => Nat.succ_le_iff.mp (by
      have := hL2 d hd; omega)))
  have hdec : ∀ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
      cycleTypeWeight n (L + S) ≤
        (1 / (L.prod : ℝ)) * cycleTypeWeight (n - L.sum) S := by
    intro S hS
    rw [Finset.mem_filter] at hS
    have hdisj : Disjoint L.toFinset S.toFinset := hS.2
    have hSval : S ∈ cycleTypes (n - L.sum) := hS.1
    have hS2 : ∀ d ∈ S, 2 ≤ d := mem_cycleTypes_two_le hSval
    have hSsum : S.sum ≤ n - L.sum := mem_cycleTypes_sum_le hSval
    have hsum : L.sum + S.sum ≤ n := by omega
    have hdec' := cycleTypeWeight_add_eq n L S hdisj hL2 hS2 hsum
    have hcount_ge : (1 : ℝ) ≤ (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) := by
      exact Finset.one_le_prod (fun d hd => by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos _)))
    have hLprod_nonneg : 0 ≤ (L.prod : ℝ) := Nat.cast_nonneg _
    have hle : (1 : ℝ) / ((L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ))) ≤
        1 / (L.prod : ℝ) := by
      have hprod_ge : (L.prod : ℝ) ≤ (L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) := by
        simpa [mul_comm] using (mul_le_mul_of_nonneg_left hcount_ge hLprod_nonneg)
      exact one_div_le_one_div_of_le hLprod_pos hprod_ge
    have hw_nonneg : 0 ≤ cycleTypeWeight (n - L.sum) S := by
      unfold cycleTypeWeight
      positivity
    calc cycleTypeWeight n (L + S)
        = (1 / ((L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)))) *
            cycleTypeWeight (n - L.sum) S := hdec'
      _ ≤ (1 / (L.prod : ℝ)) * cycleTypeWeight (n - L.sum) S := by
            exact mul_le_mul_of_nonneg_right hle hw_nonneg
  have hsum_le : (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
      cycleTypeWeight n (L + S)) ≤
      (1 / (L.prod : ℝ)) * (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
        cycleTypeWeight (n - L.sum) S) := by
    calc (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
          cycleTypeWeight n (L + S))
        ≤ ∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
            (1 / (L.prod : ℝ)) * cycleTypeWeight (n - L.sum) S := by
              exact Finset.sum_le_sum (fun S hS => hdec S hS)
      _ = (1 / (L.prod : ℝ)) * (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
            cycleTypeWeight (n - L.sum) S) := by rw [Finset.mul_sum]
  have hsum_all_le : (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
      cycleTypeWeight (n - L.sum) S) ≤ 1 := by
    have hsub : (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
        cycleTypeWeight (n - L.sum) S) ≤
        ∑ S ∈ cycleTypes (n - L.sum), cycleTypeWeight (n - L.sum) S := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro S hS; exact (Finset.mem_filter.mp hS).1
      · intro S hS hnot
        unfold cycleTypeWeight
        positivity
    calc (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
          cycleTypeWeight (n - L.sum) S)
        ≤ ∑ S ∈ cycleTypes (n - L.sum), cycleTypeWeight (n - L.sum) S := hsub
      _ = 1 := sum_cycleTypeWeight_eq_one (n - L.sum)
  have hnonneg : 0 ≤ 1 / (L.prod : ℝ) := by positivity
  calc (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
        cycleTypeWeight n (L + S))
      ≤ (1 / (L.prod : ℝ)) * (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset),
          cycleTypeWeight (n - L.sum) S) := hsum_le
    _ ≤ (1 / (L.prod : ℝ)) * 1 := mul_le_mul_of_nonneg_left hsum_all_le hnonneg
    _ = 1 / (L.prod : ℝ) := by ring

/-! ### The divisor bound and the threshold `n^{13/14}` (the `δ = 1/14` instance)

For the `Tᵢ` estimates we fix `δ = 1/14`: a *large* cycle is one of length
`d ≥ n^{13/14}`, contributing a factor `1/d ≤ n^{-13/14}`. The divisor function
is bounded by `τ(m) ≤ C^{1/16} m^{1/16}`, so `τ(n-k) n^{-13/14} = O(n^{-67/80}) → 0`.
-/

/-- `τ(m) ≤ C^{1/16} m^{1/16}` (the `ε = 1/16` divisor bound, from
`tau_pow_sixteen_le`). -/
lemma tau_le_rpow_sixteenth (m C : ℕ) (hC : (tau m)^16 ≤ C * m) :
    (tau m : ℝ) ≤ (C : ℝ)^(1/16 : ℝ) * (m : ℝ)^(1/16 : ℝ) := by
  have hcast : (tau m : ℝ)^16 ≤ ((C * m : ℕ) : ℝ) := by exact_mod_cast hC
  have hnonneg : 0 ≤ (tau m : ℝ) := Nat.cast_nonneg _
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
  exact hmono

/-- For a *large* cycle length `d ≥ n^{13/14}`, the reciprocal is at most
`n^{-13/14}` (the `δ = 1/14` threshold inequality). -/
lemma one_div_le_rpow_neg (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (h : (n : ℝ)^(13/14 : ℝ) ≤ (d : ℝ)) : (1 : ℝ) / (d : ℝ) ≤ (n : ℝ)^(-(13/14 : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow_pos : 0 < (n : ℝ)^(13/14 : ℝ) := Real.rpow_pos_of_pos hnR _
  have h1 : (1 : ℝ) / (d : ℝ) ≤ 1 / (n : ℝ)^(13/14 : ℝ) :=
    one_div_le_one_div_of_le hpow_pos h
  have hrew : 1 / (n : ℝ)^(13/14 : ℝ) = (n : ℝ)^(-(13/14 : ℝ)) := by
    simpa [div_eq_mul_inv] using (Real.rpow_neg (le_of_lt hnR) (13/14 : ℝ)).symm
  calc (1 : ℝ) / (d : ℝ) ≤ 1 / (n : ℝ)^(13/14 : ℝ) := h1
    _ = (n : ℝ)^(-(13/14 : ℝ)) := hrew

/-- Every cycle length of a cycle type divides its lcm. -/
lemma dvd_lcm_of_mem_cycleType {n : ℕ} {lam : Multiset ℕ} {d : ℕ} (h : d ∈ lam) : d ∣ lam.lcm :=
  Multiset.dvd_lcm h

/-- For a *large* multiset `L` (each entry `≥ n^{13/14}`), the product `L.prod` is at
least `n^{(13/14)·L.card}` (i.e. the reciprocal is at most `n^{-(13/14)·L.card}`). -/
lemma prod_le_rpow_of_large (n : ℕ) (L : Multiset ℕ) (hn : 0 < n)
    (hlarge : ∀ d ∈ L, (n : ℝ)^(13/14 : ℝ) ≤ (d : ℝ)) :
    (n : ℝ)^((13/14 : ℝ) * (L.card : ℝ)) ≤ (L.prod : ℝ) := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons d L' ih =>
      have hd : (n : ℝ)^(13/14 : ℝ) ≤ (d : ℝ) := hlarge d (Multiset.mem_cons.mpr (Or.inl rfl))
      have hL' : ∀ x ∈ L', (n : ℝ)^(13/14 : ℝ) ≤ (x : ℝ) := fun x hx =>
        hlarge x (Multiset.mem_cons.mpr (Or.inr hx))
      have ih' : (n : ℝ)^((13/14 : ℝ) * (L'.card : ℝ)) ≤ (L'.prod : ℝ) := ih hL'
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hpow : (n : ℝ)^((13/14 : ℝ) * ((L'.card + 1 : ℕ) : ℝ)) =
          (n : ℝ)^(13/14 : ℝ) * (n : ℝ)^((13/14 : ℝ) * (L'.card : ℝ)) := by
        rw [Nat.cast_add, Nat.cast_one]
        rw [mul_add]
        norm_num
        rw [Real.rpow_add hnR ((13/14 : ℝ) * (L'.card : ℝ)) (13/14 : ℝ)]
        rw [mul_comm]
      rw [Multiset.card_cons, Multiset.prod_cons]
      rw [hpow]
      rw [Nat.cast_mul]
      exact mul_le_mul hd ih' (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Nat.cast_nonneg d)

/-- `1/L.prod ≤ n^{-(13/14)·L.card}` for a *large* multiset `L` (each entry `≥ n^{13/14}`). -/
lemma inv_prod_le_rpow_of_large (n : ℕ) (L : Multiset ℕ) (hn : 0 < n)
    (hlarge : ∀ d ∈ L, (n : ℝ)^(13/14 : ℝ) ≤ (d : ℝ)) (hL2 : ∀ d ∈ L, 2 ≤ d) :
    (1 : ℝ) / (L.prod : ℝ) ≤ (n : ℝ)^(-((13/14 : ℝ) * (L.card : ℝ))) := by
  have h := prod_le_rpow_of_large n L hn hlarge
  have hLprod_pos : 0 < (L.prod : ℝ) := by
    exact_mod_cast (Multiset.prod_pos (fun d hd => Nat.succ_le_iff.mp (by
      have := hL2 d hd; omega)))
  have hpow_pos : 0 < (n : ℝ)^((13/14 : ℝ) * (L.card : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have h1 : (1 : ℝ) / (L.prod : ℝ) ≤ 1 / (n : ℝ)^((13/14 : ℝ) * (L.card : ℝ)) :=
    one_div_le_one_div_of_le hpow_pos h
  have hrew : 1 / (n : ℝ)^((13/14 : ℝ) * (L.card : ℝ)) = (n : ℝ)^(-((13/14 : ℝ) * (L.card : ℝ))) := by
    simpa [div_eq_mul_inv] using (Real.rpow_neg (le_of_lt (by exact_mod_cast hn))
      ((13/14 : ℝ) * (L.card : ℝ))).symm
  calc (1 : ℝ) / (L.prod : ℝ) ≤ 1 / (n : ℝ)^((13/14 : ℝ) * (L.card : ℝ)) := h1
    _ = (n : ℝ)^(-((13/14 : ℝ) * (L.card : ℝ))) := hrew

/-- `τ(n-k) ≤ C^{1/16} n^{1/16}` (the divisor bound at `n-k`). -/
lemma tau_sub_le (n k C : ℕ) (hC : (tau (n - k))^16 ≤ C * (n - k)) :
    (tau (n - k) : ℝ) ≤ (C : ℝ)^(1/16 : ℝ) * (n : ℝ)^(1/16 : ℝ) := by
  have h := tau_le_rpow_sixteenth (n - k) C hC
  have hle : ((n - k : ℕ) : ℝ)^(1/16 : ℝ) ≤ (n : ℝ)^(1/16 : ℝ) := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg (n - k)) (by exact_mod_cast (Nat.sub_le n k))
      (by norm_num : 0 ≤ (1/16 : ℝ))
  have hC16_nonneg : 0 ≤ (C : ℝ)^(1/16 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg C) _
  exact le_trans h (mul_le_mul_of_nonneg_left hle hC16_nonneg)

/-! ### The `ε = 1/24` divisor bound and the geometric/factorial tails -/

/-- `τ(m) ≤ C^{1/24} m^{1/24}` (the `ε = 1/24` divisor bound, from `tau_pow_twentyfour_le`). -/
lemma tau_le_rpow_twentyfourth (m C : ℕ) (hC : (tau m)^24 ≤ C * m) :
    (tau m : ℝ) ≤ (C : ℝ)^(1/24 : ℝ) * (m : ℝ)^(1/24 : ℝ) := by
  have hcast : (tau m : ℝ)^24 ≤ ((C * m : ℕ) : ℝ) := by exact_mod_cast hC
  have hnonneg : 0 ≤ (tau m : ℝ) := Nat.cast_nonneg _
  have hmono : ((tau m : ℝ)^24)^(1/24 : ℝ) ≤ ((C * m : ℕ) : ℝ)^(1/24 : ℝ) :=
    Real.rpow_le_rpow (by positivity : 0 ≤ (tau m : ℝ)^24) hcast (by norm_num : 0 ≤ (1/24 : ℝ))
  have hrew : ((tau m : ℝ)^24)^(1/24 : ℝ) = (tau m : ℝ) := by
    rw [show (tau m : ℝ)^24 = (tau m : ℝ)^(24 : ℝ) by exact (Real.rpow_natCast (tau m : ℝ) 24).symm]
    rw [← Real.rpow_mul hnonneg (24 : ℝ) (1/24 : ℝ)]
    rw [show (tau m : ℝ)^((24 : ℝ) * (1/24 : ℝ)) = (tau m : ℝ)^(1 : ℝ) by congr 1; norm_num]
    rw [Real.rpow_one]
  rw [hrew] at hmono
  have hC_nonneg : 0 ≤ (C : ℝ) := Nat.cast_nonneg C
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : ((C * m : ℕ) : ℝ)^(1/24 : ℝ) = (C : ℝ)^(1/24 : ℝ) * (m : ℝ)^(1/24 : ℝ) := by
    rw [Nat.cast_mul]
    exact Real.mul_rpow hC_nonneg hm_nonneg
  rw [h1] at hmono
  exact hmono

/-- `τ(n-k) ≤ C^{1/24} n^{1/24}` (the `ε = 1/24` divisor bound at `n-k`). -/
lemma tau_sub_le_twentyfourth (n k C : ℕ) (hC : (tau (n - k))^24 ≤ C * (n - k)) :
    (tau (n - k) : ℝ) ≤ (C : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) := by
  have h := tau_le_rpow_twentyfourth (n - k) C hC
  have hle : ((n - k : ℕ) : ℝ)^(1/24 : ℝ) ≤ (n : ℝ)^(1/24 : ℝ) := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg (n - k)) (by exact_mod_cast (Nat.sub_le n k))
      (by norm_num : 0 ≤ (1/24 : ℝ))
  have hC20_nonneg : 0 ≤ (C : ℝ)^(1/24 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg C) _
  exact le_trans h (mul_le_mul_of_nonneg_left hle hC20_nonneg)

/-- The tail of the geometric series from exponent 3: `∑_{i=3}^{N} x^i ≤ 2x³` for `0 ≤ x ≤ 1/2`. -/
lemma geom_series_tail_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (N : ℕ) :
    (∑ i ∈ Finset.Icc 3 N, x ^ i) ≤ 2 * x ^ 3 := by
  have hx1 : x < 1 := by linarith
  have hden : 0 < 1 - x := by linarith
  have hIcc_eq : Finset.Icc 3 N = Finset.Ico 3 (N + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc_eq, Finset.sum_Ico_eq_sum_range (fun k => x ^ k) 3 (N + 1)]
  rw [show N + 1 - 3 = N - 2 by omega]
  have hfactor : (∑ k ∈ Finset.range (N - 2), x ^ (3 + k)) = x ^ 3 * (∑ k ∈ Finset.range (N - 2), x ^ k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_add]
  rw [hfactor]
  have hgeom := geom_sum_le_inv_one_sub hx0 hx1 (N - 2)
  have hx3 : 0 ≤ x ^ 3 := by positivity
  have hle2 : x ^ 3 * (∑ k ∈ Finset.range (N - 2), x ^ k) ≤ x ^ 3 * (1 / (1 - x)) :=
    mul_le_mul_of_nonneg_left hgeom hx3
  have hle3 : x ^ 3 * (1 / (1 - x)) ≤ 2 * x ^ 3 := by
    have h1 : 1 / (1 - x) ≤ 2 := by
      rw [div_le_iff₀ hden]
      linarith
    have h := mul_le_mul_of_nonneg_left h1 hx3
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  exact le_trans hle2 hle3

/-- For large cycles `d₁, d₂, d₃ ≥ n^{13/14}`, `1/(d₁d₂d₃) ≤ (n^{-13/14})³`. -/
lemma one_div_mul_three_le_rpow_neg_three (n d₁ d₂ d₃ : ℕ) (hn : 0 < n)
    (h₁ : (n : ℝ)^(13/14 : ℝ) ≤ (d₁ : ℝ)) (h₂ : (n : ℝ)^(13/14 : ℝ) ≤ (d₂ : ℝ))
    (h₃ : (n : ℝ)^(13/14 : ℝ) ≤ (d₃ : ℝ)) :
    (1 : ℝ) / ((d₁ * d₂ * d₃ : ℕ) : ℝ) ≤ ((n : ℝ)^(-(13/14 : ℝ))) ^ 3 := by
  have hd₁ : 0 < d₁ := by
    have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) h₁
    exact_mod_cast (Nat.pos_of_ne_zero (by
      intro hz; subst d₁; norm_num at h))
  have hd₂ : 0 < d₂ := by
    have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) h₂
    exact_mod_cast (Nat.pos_of_ne_zero (by intro hz; subst d₂; norm_num at h))
  have hd₃ : 0 < d₃ := by
    have h := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hn) _) h₃
    exact_mod_cast (Nat.pos_of_ne_zero (by intro hz; subst d₃; norm_num at h))
  have hi₁ := one_div_le_rpow_neg n d₁ hn hd₁ h₁
  have hi₂ := one_div_le_rpow_neg n d₂ hn hd₂ h₂
  have hi₃ := one_div_le_rpow_neg n d₃ hn hd₃ h₃
  have hprod : (1 : ℝ) / ((d₁ * d₂ * d₃ : ℕ) : ℝ) = ((1 : ℝ) / (d₁ : ℝ)) * ((1 : ℝ) / (d₂ : ℝ)) * ((1 : ℝ) / (d₃ : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [one_div_mul_one_div, one_div_mul_one_div]
  rw [hprod]
  have hnpow_nonneg : 0 ≤ (n : ℝ)^(-(13/14 : ℝ)) :=
    Real.rpow_nonneg (by exact_mod_cast (le_of_lt hn)) _
  have hle12 : ((1 : ℝ) / (d₁ : ℝ)) * ((1 : ℝ) / (d₂ : ℝ)) ≤
      ((n : ℝ)^(-(13/14 : ℝ))) * ((n : ℝ)^(-(13/14 : ℝ))) :=
    mul_le_mul hi₁ hi₂ (by positivity : 0 ≤ (1 : ℝ) / (d₂ : ℝ)) hnpow_nonneg
  have hle123 : ((1 : ℝ) / (d₁ : ℝ)) * ((1 : ℝ) / (d₂ : ℝ)) * ((1 : ℝ) / (d₃ : ℝ)) ≤
      ((n : ℝ)^(-(13/14 : ℝ))) * ((n : ℝ)^(-(13/14 : ℝ))) * ((n : ℝ)^(-(13/14 : ℝ))) :=
    mul_le_mul hle12 hi₃ (by positivity : 0 ≤ (1 : ℝ) / (d₃ : ℝ)) (mul_nonneg hnpow_nonneg hnpow_nonneg)
  simpa [pow_three, mul_assoc] using hle123

/-! ### The main-term separation `p(n,n-k) = 1/(n-k) + (rest)` -/

/-! ### The main-term separation `p(n,n-k) = 1/(n-k) + (rest)` -/

/-- The lcm of a valid cycle type of `Sₖ` divides `lcm(1,…,k)`. -/
lemma lcm_dvd_lcm1to_of_cycleTypes {k : ℕ} {μ : Multiset ℕ} (hμ : μ ∈ cycleTypes k) :
    μ.lcm ∣ lcm1to k := by
  rcases (Finset.mem_image.mp hμ) with ⟨g, _, hg⟩
  rw [← hg]
  rw [Equiv.Perm.lcm_cycleType g]
  exact orderOf_dvd_lcm1to g

/-- For `k ∈ Kₙ`, a cycle type of `Sₙ` that contains an `(n-k)`-cycle has lcm exactly
`n-k` (the *key property* at the level of cycle types). -/
lemma lcm_eq_of_mem_nk_cycleType {n k : ℕ} (hk : k ∈ K n) {lam : Multiset ℕ} (hlam : lam ∈ cycleTypes n)
    (hmem : n - k ∈ lam) : lam.lcm = n - k := by
  have hk_lt_n : k < n := mem_range.mp (mem_filter.mp hk).1
  let μ : Multiset ℕ := lam.erase (n - k)
  have hμ : μ ∈ cycleTypes k := mem_cycleTypes_erase n k hlam hmem (by omega : k ≤ n)
  have hμ_lcm : μ.lcm ∣ lcm1to k := lcm_dvd_lcm1to_of_cycleTypes hμ
  have hlcm1 : lcm1to k ∣ n - k := (mem_filter.mp hk).2
  have hμ_dvd : μ.lcm ∣ n - k := dvd_trans hμ_lcm hlcm1
  have hcons : lam = (n - k) ::ₘ μ := by
    dsimp [μ]
    exact (Multiset.cons_erase hmem).symm
  rw [hcons, Multiset.lcm_cons]
  exact Nat.lcm_eq_left hμ_dvd

/-- The "rest" term: the probability that `ord = n-k` *without* an `(n-k)`-cycle. -/
noncomputable def restProb (n k : ℕ) : ℝ :=
  ∑ lam ∈ (cycleTypes n).filter (fun lam => n - k ∉ lam),
    if lam.lcm = n - k then cycleTypeWeight n lam else 0

/-- **The main-term separation**: for `k ∈ Kₙ` (and `n ≥ 5`),
`pₙ(n-k) = 1/(n-k) + restProb(n,k)`. -/
lemma p_eq_one_div_add_rest (n k : ℕ) (hk : k ∈ K n) (hn : 5 ≤ n) [NeZero n] :
    p n (n - k) = (1 : ℝ) / ((n - k : ℕ) : ℝ) + restProb n k := by
  have hk_lt_sub : k < n - k := k_lt_sub_of_mem_K hk hn
  have hnk2 : 2 ≤ n - k := by omega
  rw [p_eq_sum_cycleType n (n - k)]
  have hsplit : (∑ lam ∈ cycleTypes n, if lam.lcm = n - k then cycleTypeWeight n lam else 0) =
      (∑ lam ∈ cycleTypes n, if n - k ∈ lam then cycleTypeWeight n lam else 0) + restProb n k := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := cycleTypes n) (p := fun lam => n - k ∈ lam)
      (f := fun lam => if lam.lcm = n - k then cycleTypeWeight n lam else 0)]
    congr 1
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro lam hlam
      by_cases hmem : n - k ∈ lam
      · have hlcm : lam.lcm = n - k := lcm_eq_of_mem_nk_cycleType hk hlam hmem
        simp [hmem, hlcm]
      · simp [hmem]
  rw [hsplit]
  rw [sum_cycleTypeWeight_of_mem_nk n k hk_lt_sub hnk2]

/-! ### The `η`-numerator: a cycle of length `2^⌊log₂ k⌋` in `Sₖ` -/

/-- The probability that a random permutation of `Sₖ` has a cycle of length `2^⌊log₂ k⌋`
is exactly `1/2^⌊log₂ k⌋` (for `k ≥ 2`; since `2^⌊log₂ k⌋ > k/2`, there is at most one such
cycle, so the probability equals the expected number of such cycles). -/
lemma sum_cycleTypeWeight_of_mem_two_pow_log2 (k : ℕ) (hk : 2 ≤ k) :
    (∑ μ ∈ cycleTypes k, if 2 ^ Nat.log 2 k ∈ μ then cycleTypeWeight k μ else 0) =
      (1 : ℝ) / ((2 ^ Nat.log 2 k : ℕ) : ℝ) := by
  have hpow_le : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega : k ≠ 0)
  have hpow2 : 2 ≤ 2 ^ Nat.log 2 k := by
    exact Nat.le_self_pow (Nat.ne_of_gt (Nat.log_pos (by norm_num : 1 < (2 : ℕ)) hk)) 2
  have hgt : k - 2 ^ Nat.log 2 k < 2 ^ Nat.log 2 k := by
    have hlt : k < 2 ^ (Nat.log 2 k).succ := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) k
    have hlt' : k < 2 * 2 ^ Nat.log 2 k := by
      simpa [pow_succ, mul_comm] using hlt
    omega
  have hgt' : k - 2 ^ Nat.log 2 k < k - (k - 2 ^ Nat.log 2 k) := by
    simpa [Nat.sub_sub_self hpow_le] using hgt
  have hpow2' : 2 ≤ k - (k - 2 ^ Nat.log 2 k) := by
    simpa [Nat.sub_sub_self hpow_le] using hpow2
  have h := sum_cycleTypeWeight_of_mem_nk k (k - 2 ^ Nat.log 2 k) hgt' hpow2'
  simpa [Nat.sub_sub_self hpow_le] using h

/-! ### The special `η` term (paper eq. `special_terms`): two `(n-k)/2`-cycles -/

/-- Decoupling for `L = {a, a}` (two cycles of the same length `a`): the Cauchy weight of
`{a, a} + μ` equals `1/(2a²)` times the weight of `μ` on `n - 2a` points. -/
lemma cycleTypeWeight_two_eq (n a : ℕ) (μ : Multiset ℕ)
    (ha2 : 2 ≤ a) (hμ2 : ∀ d ∈ μ, 2 ≤ d) (hsum : 2 * a + μ.sum ≤ n) (ha_notmem : a ∉ μ) :
    cycleTypeWeight n (a ::ₘ a ::ₘ μ) =
      (1 / ((2 : ℝ) * ((a : ℕ) : ℝ) ^ 2)) * cycleTypeWeight (n - 2 * a) μ := by
  let L : Multiset ℕ := a ::ₘ a ::ₘ 0
  have hLsum : L.sum = 2 * a := by simp [L, two_mul]
  have hL2 : ∀ d ∈ L, 2 ≤ d := by
    intro d hd
    simp [L] at hd
    rw [hd]
    exact ha2
  have hdisj : Disjoint L.toFinset μ.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxL hxμ
    have hx_mem_L : x ∈ L := by
      simpa [L] using (Multiset.mem_toFinset.mp hxL)
    have hx_a : x = a := by
      simp [L] at hx_mem_L
      exact hx_mem_L
    apply ha_notmem
    exact Multiset.mem_toFinset.mp (by simpa [hx_a] using hxμ)
  have hsum' : L.sum + μ.sum ≤ n := by
    rw [hLsum]
    exact hsum
  have hdec := cycleTypeWeight_add_eq n L μ hdisj hL2 hμ2 hsum'
  have hfactor : (1 / ((L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)))) =
      1 / ((2 : ℝ) * ((a : ℕ) : ℝ) ^ 2) := by
    have hLprod : (L.prod : ℝ) = ((a : ℕ) : ℝ) ^ 2 := by
      have h : L.prod = a * a := by simp [L]
      rw [h, Nat.cast_mul, pow_two]
    have hLcount : (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) = (2 : ℝ) := by
      have hLtoFinset : L.toFinset = {a} := by
        ext x; simp [L]
      rw [hLtoFinset, Finset.prod_singleton]
      have hca : L.count a = 2 := by simp [L]
      rw [hca]
      norm_num
    rw [hLprod, hLcount]
    ring
  rw [show L + μ = a ::ₘ a ::ₘ μ by simp [L]] at hdec
  rw [hLsum] at hdec
  rw [hfactor] at hdec
  simpa using hdec

/-- **The special-term contribution**: two cycles of length `(n-k)/2` together with a
`2^⌊log₂ k⌋`-cycle in the residual `Sₖ` contribute `1/(2((n-k)/2)² · 2^⌊log₂ k⌋)`. -/
lemma special_cycleTypeWeight_sum (n k : ℕ) (hk2 : 2 ≤ k) (hdiv : 2 ∣ n - k)
    (ha2 : 2 ≤ (n - k) / 2) (hgt : k < (n - k) / 2) :
    (∑ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ),
        cycleTypeWeight n (((n - k) / 2) ::ₘ ((n - k) / 2) ::ₘ μ)) =
      (1 : ℝ) / (2 * (((n - k) / 2 : ℕ) : ℝ) ^ 2) * (1 / ((2 ^ Nat.log 2 k : ℕ) : ℝ)) := by
  classical
  let a := (n - k) / 2
  have h2a : 2 * a = n - k := by
    dsimp [a]
    have h := Nat.div_mul_cancel hdiv
    simpa [Nat.mul_comm] using h
  have hdec : ∀ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ),
      cycleTypeWeight n (a ::ₘ a ::ₘ μ) =
        (1 / ((2 : ℝ) * ((a : ℕ) : ℝ) ^ 2)) * cycleTypeWeight k μ := by
    intro μ hμ
    have hμct : μ ∈ cycleTypes k := (Finset.mem_filter.mp hμ).1
    have hμ2 : ∀ d ∈ μ, 2 ≤ d := mem_cycleTypes_two_le hμct
    have hμsum : μ.sum ≤ k := mem_cycleTypes_sum_le hμct
    have ha_notmem : a ∉ μ := by
      intro hmem
      have ha_le : a ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) a hmem
      omega
    have hsum' : 2 * a + μ.sum ≤ n := by omega
    rw [cycleTypeWeight_two_eq n a μ ha2 hμ2 hsum' ha_notmem]
    rw [show n - 2 * a = k by omega]
  have hsum_eq : (∑ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ),
        cycleTypeWeight n (a ::ₘ a ::ₘ μ)) =
      (1 / ((2 : ℝ) * ((a : ℕ) : ℝ) ^ 2)) *
        (∑ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ), cycleTypeWeight k μ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ hμ
    exact hdec μ hμ
  rw [hsum_eq]
  have hinner : (∑ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ), cycleTypeWeight k μ) =
      (1 : ℝ) / ((2 ^ Nat.log 2 k : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    exact sum_cycleTypeWeight_of_mem_two_pow_log2 k hk2
  rw [hinner]

/-- In the "interesting" case (`k ≥ 2`, `2^⌊log₂ k⌋+1 ∤ n-k`), the special-term contribution
(two `(n-k)/2`-cycles plus a `2^⌊log₂ k⌋`-cycle) equals exactly `η(n,k)`. -/
lemma special_cycleTypeWeight_sum_eq_eta (n k : ℕ) (hk2 : 2 ≤ k) (hdiv : 2 ∣ n - k)
    (ha2 : 2 ≤ (n - k) / 2) (hgt : k < (n - k) / 2) (hnot : ¬ 2 ^ (Nat.log 2 k + 1) ∣ n - k) :
    (∑ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ),
        cycleTypeWeight n (((n - k) / 2) ::ₘ ((n - k) / 2) ::ₘ μ)) = eta n k := by
  rw [special_cycleTypeWeight_sum n k hk2 hdiv ha2 hgt]
  unfold eta
  rw [if_neg (by
    rintro (h0 | h1 | hdvd)
    · omega
    · omega
    · exact hnot hdvd)]
  have h2x : (2 : ℝ) * (((n - k) / 2 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) := by
    have h : 2 * ((n - k) / 2) = n - k := by
      have hc := Nat.div_mul_cancel hdiv
      simpa [Nat.mul_comm] using hc
    exact_mod_cast h
  have hpow : ((2 : ℝ) ^ Nat.log 2 k) = ((2 ^ Nat.log 2 k : ℕ) : ℝ) := by
    simpa using (Nat.cast_pow (2 : ℕ) (Nat.log 2 k)).symm
  rw [hpow]
  have ha : (((n - k) / 2 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) / 2 := by
    rw [eq_div_iff (show (2 : ℝ) ≠ 0 by norm_num)]
    rw [mul_comm]
    exact h2x
  rw [ha]
  have hnk_pos : 0 < n - k := by omega
  field_simp [show ((n - k : ℕ) : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hnk_pos),
    show ((2 ^ Nat.log 2 k : ℕ) : ℝ) ≠ 0 by positivity,
    show (2 : ℝ) ≠ 0 by norm_num]

/-! ### The "no long cycles" bound (real-point coefficient estimate)

We bound the probability that a random permutation of `[n]` has *no* cycle of
length exceeding `r` by a real-point ("saddle at a real point") coefficient
estimate: for every `x ≥ 1`,

  `ν(n,r) ≤ x⁻ⁿ · exp(∑_{j=1}^r xʲ/j)`.

The proof is elementary: enumerate cycle types by their *count vector*
`(c₁,…,cᵣ)` (with `c₁` = number of fixed points), use that the Cauchy weight of a
cycle type equals `∏ⱼ 1/(j^{cⱼ}cⱼ!)`, and factor the resulting sum over all count
vectors as a product of exponential partial sums, each `≤ exp(xʲ/j)`.
-/

/-- `s.count d ≤ s.sum` whenever `1 ≤ d`. -/
lemma count_le_sum (s : Multiset ℕ) (d : ℕ) (hd : 1 ≤ d) : s.count d ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.count_cons, Multiset.sum_cons]
      by_cases h : d = a
      · subst d
        rw [if_pos rfl]
        have hih : s.count a ≤ s.sum := ih
        omega
      · rw [if_neg h]
        have hih : s.count d ≤ s.sum := ih
        omega

/-- `lam.sum = ∑ d ∈ lam.toFinset, lam.count d * d`. -/
lemma sum_eq_sum_count_mul (lam : Multiset ℕ) : lam.sum = ∑ d ∈ lam.toFinset, lam.count d * d := by
  have hsum : (∑ a ∈ lam.toFinset, (lam.count a • ({a} : Multiset ℕ))).sum = lam.sum :=
    congrArg Multiset.sum (Multiset.toFinset_sum_count_nsmul_eq lam)
  rw [← hsum]
  rw [Multiset.sum_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_eq_mul]
  rfl

/-- `lam.prod = ∏ d ∈ lam.toFinset, d ^ (lam.count d)`. -/
lemma prod_eq_prod_count_pow (lam : Multiset ℕ) : lam.prod = ∏ d ∈ lam.toFinset, d ^ (lam.count d) := by
  have hprod : (∑ a ∈ lam.toFinset, (lam.count a • ({a} : Multiset ℕ))).prod = lam.prod :=
    congrArg Multiset.prod (Multiset.toFinset_sum_count_nsmul_eq lam)
  rw [← hprod]
  rw [Multiset.prod_sum]
  apply Finset.prod_congr rfl
  intro a ha
  rw [Multiset.prod_nsmul, Multiset.prod_singleton]

/-- The full count vector of a cycle type: `countVec n r lam j` records the number of
cycles of length `j.val + 1` (with `n - lam.sum` fixed points at index `0`). -/
def countVec (n r : ℕ) (lam : Multiset ℕ) : Fin r → ℕ :=
  fun j => if j.val = 0 then n - lam.sum else lam.count (j.val + 1)

/-- The per-length term `(x^{j.val+1}/(j.val+1))^c / c!` in the coefficient estimate. -/
noncomputable def nuTerm (r : ℕ) (x : ℝ) (j : Fin r) (c : ℕ) : ℝ :=
  (x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ^ c / (Nat.factorial c : ℝ)

/-- `countVec` is injective on multisets whose entries all lie in `[2, r]`. -/
lemma countVec_injective (n r : ℕ) {lam₁ lam₂ : Multiset ℕ}
    (h₁ : ∀ d ∈ lam₁, 2 ≤ d ∧ d ≤ r) (h₂ : ∀ d ∈ lam₂, 2 ≤ d ∧ d ≤ r)
    (h : countVec n r lam₁ = countVec n r lam₂) : lam₁ = lam₂ := by
  apply Multiset.ext.mpr
  intro d
  by_cases hd01 : d = 0 ∨ d = 1
  · -- d ∈ {0,1}: not in either multiset
    have hc1 : lam₁.count d = 0 := Multiset.count_eq_zero.mpr (by
      intro hmem
      have := (h₁ d hmem).1
      omega)
    have hc2 : lam₂.count d = 0 := Multiset.count_eq_zero.mpr (by
      intro hmem
      have := (h₂ d hmem).1
      omega)
    rw [hc1, hc2]
  · by_cases hdr : d ≤ r
    · have hd2 : 2 ≤ d := by omega
      have hlt : d - 1 < r := by omega
      let j : Fin r := ⟨d - 1, hlt⟩
      have hjval : j.val = d - 1 := rfl
      have hjne : j.val ≠ 0 := by omega
      have hdsub : (d - 1) + 1 = d := Nat.sub_add_cancel (by omega : 1 ≤ d)
      have heq := congrFun h j
      unfold countVec at heq
      rw [hjval, if_neg hjne, if_neg hjne] at heq
      rwa [hdsub] at heq
    · -- d > r: not in either multiset
      have hc1 : lam₁.count d = 0 := Multiset.count_eq_zero.mpr (by
        intro hmem
        have := (h₁ d hmem).2
        omega)
      have hc2 : lam₂.count d = 0 := Multiset.count_eq_zero.mpr (by
        intro hmem
        have := (h₂ d hmem).2
        omega)
      rw [hc1, hc2]

/-- `countVec n r lam j ≤ n` for a cycle type `lam` with `lam.sum ≤ n`. -/
lemma countVec_mem_range (n r : ℕ) (lam : Multiset ℕ) (hsum : lam.sum ≤ n) (j : Fin r) :
    countVec n r lam j ∈ Finset.range (n + 1) := by
  unfold countVec
  by_cases h : j.val = 0
  · rw [if_pos h]
    exact Finset.mem_range.mpr (by omega)
  · rw [if_neg h]
    have hd : 1 ≤ j.val + 1 := by omega
    have hc : lam.count (j.val + 1) ≤ lam.sum := count_le_sum lam (j.val + 1) hd
    exact Finset.mem_range.mpr (by omega)

/-- For a cycle type with entries in `[2, r]`, `∑_{j : Fin (r-1)} (j.val+2)·count(j.val+2) = lam.sum`. -/
lemma sum_count_mul_eq_sum (r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) :
    (∑ j : Fin (r - 1), (j.val + 2) * lam.count (j.val + 2)) = lam.sum := by
  have hbij : (∑ j : Fin (r - 1), (j.val + 2) * lam.count (j.val + 2)) =
      ∑ d ∈ Finset.Icc 2 r, d * lam.count d := by
    refine Finset.sum_bij (fun j _ => j.val + 2) ?hi ?hinj ?hsurj ?h
    · intro j hj
      change j.val + 2 ∈ Finset.Icc 2 r
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j₁ hj₁ j₂ hj₂ h
      apply Fin.ext
      dsimp at h
      omega
    · intro d hd
      rcases Finset.mem_Icc.mp hd with ⟨hd2, hdr⟩
      refine ⟨⟨d - 2, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega
    · intro j hj
      rfl
  rw [hbij]
  calc (∑ d ∈ Finset.Icc 2 r, d * lam.count d)
      = ∑ d ∈ lam.toFinset, d * lam.count d := by
          symm
          apply Finset.sum_subset
          · intro d hd
            exact Finset.mem_Icc.mpr ⟨h2 d (Multiset.mem_toFinset.mp hd), hr d (Multiset.mem_toFinset.mp hd)⟩
          · intro d hd hnot
            have hc : lam.count d = 0 := Multiset.count_eq_zero.mpr (by
              simpa [Multiset.mem_toFinset] using hnot)
            simp [hc]
    _ = lam.sum := by
          simpa [mul_comm] using (sum_eq_sum_count_mul lam).symm

/-- `∑_{j : Fin r} (j.val+1)·countVec n r lam j = n` (total points = fixed points + cycles). -/
lemma sum_mul_countVec_eq (n r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) (hsum : lam.sum ≤ n) (hrpos : 1 ≤ r) :
    (∑ j : Fin r, (j.val + 1) * countVec n r lam j) = n := by
  cases r with
  | zero => omega
  | succ r' =>
      rw [Fin.sum_univ_succ]
      have hterm0 : ((0 : Fin (r' + 1)).val + 1) * countVec n (r' + 1) lam 0 = n - lam.sum := by
        unfold countVec
        simp
      rw [hterm0]
      have htermsucc : (∑ j : Fin r',
          ((j.succ : Fin (r' + 1)).val + 1) * countVec n (r' + 1) lam (j.succ)) =
          ∑ j : Fin r', (j.val + 2) * lam.count (j.val + 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold countVec
        simp only [Fin.val_succ]
        have hjne : j.val + 1 ≠ 0 := by omega
        simp only [if_neg hjne]
      rw [htermsucc]
      have hsum' : (∑ j : Fin r', (j.val + 2) * lam.count (j.val + 2)) = lam.sum := by
        simpa [Nat.succ_sub_one] using (sum_count_mul_eq_sum (r' + 1) lam h2 hr)
      rw [hsum']
      omega

/-- `∏_{j : Fin (r-1)} (j.val+2)^(count(j.val+2)) = lam.prod`. -/
lemma prod_count_pow_eq_prod (r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) :
    (∏ j : Fin (r - 1), (j.val + 2) ^ (lam.count (j.val + 2))) = lam.prod := by
  have hbij : (∏ j : Fin (r - 1), (j.val + 2) ^ (lam.count (j.val + 2))) =
      ∏ d ∈ Finset.Icc 2 r, d ^ lam.count d := by
    refine Finset.prod_bij (fun j _ => j.val + 2) ?hi ?hinj ?hsurj ?h
    · intro j hj
      change j.val + 2 ∈ Finset.Icc 2 r
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j₁ hj₁ j₂ hj₂ h
      apply Fin.ext
      dsimp at h
      omega
    · intro d hd
      rcases Finset.mem_Icc.mp hd with ⟨hd2, hdr⟩
      refine ⟨⟨d - 2, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega
    · intro j hj
      rfl
  rw [hbij]
  calc (∏ d ∈ Finset.Icc 2 r, d ^ lam.count d)
      = ∏ d ∈ lam.toFinset, d ^ lam.count d := by
          symm
          apply Finset.prod_subset
          · intro d hd
            exact Finset.mem_Icc.mpr ⟨h2 d (Multiset.mem_toFinset.mp hd), hr d (Multiset.mem_toFinset.mp hd)⟩
          · intro d hd hnot
            have hc : lam.count d = 0 := Multiset.count_eq_zero.mpr (by
              simpa [Multiset.mem_toFinset] using hnot)
            simp [hc]
    _ = lam.prod := by
          simpa using (prod_eq_prod_count_pow lam).symm

/-- `∏_{j : Fin (r-1)} (count(j.val+2))! = ∏_{d ∈ lam.toFinset} (count d)!`. -/
lemma prod_count_factorial_eq (r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) :
    (∏ j : Fin (r - 1), Nat.factorial (lam.count (j.val + 2))) =
      ∏ d ∈ lam.toFinset, Nat.factorial (lam.count d) := by
  have hbij : (∏ j : Fin (r - 1), Nat.factorial (lam.count (j.val + 2))) =
      ∏ d ∈ Finset.Icc 2 r, Nat.factorial (lam.count d) := by
    refine Finset.prod_bij (fun j _ => j.val + 2) ?hi ?hinj ?hsurj ?h
    · intro j hj
      change j.val + 2 ∈ Finset.Icc 2 r
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j₁ hj₁ j₂ hj₂ h
      apply Fin.ext
      dsimp at h
      omega
    · intro d hd
      rcases Finset.mem_Icc.mp hd with ⟨hd2, hdr⟩
      refine ⟨⟨d - 2, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp
      omega
    · intro j hj
      rfl
  rw [hbij]
  calc (∏ d ∈ Finset.Icc 2 r, Nat.factorial (lam.count d))
      = ∏ d ∈ lam.toFinset, Nat.factorial (lam.count d) := by
          symm
          apply Finset.prod_subset
          · intro d hd
            exact Finset.mem_Icc.mpr ⟨h2 d (Multiset.mem_toFinset.mp hd), hr d (Multiset.mem_toFinset.mp hd)⟩
          · intro d hd hnot
            have hc : lam.count d = 0 := Multiset.count_eq_zero.mpr (by
              simpa [Multiset.mem_toFinset] using hnot)
            simp [hc]

/-- `∏_{j : Fin (r-1)} 1/((j.val+2)^(count)·count!) = 1/(lam.prod · ∏_{d} count!)`. -/
lemma prod_inv_count_eq (r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) :
    (∏ j : Fin (r - 1), (1 : ℝ) / (((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2) *
      (Nat.factorial (lam.count (j.val + 2)) : ℝ))) =
      1 / ((lam.prod : ℝ) * (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ))) := by
  have hpow : (∏ j : Fin (r - 1), ((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2)) = (lam.prod : ℝ) := by
    have h := prod_count_pow_eq_prod r lam h2 hr
    exact_mod_cast h
  have hfac : (∏ j : Fin (r - 1), (Nat.factorial (lam.count (j.val + 2)) : ℝ)) =
      (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)) := by
    have h := prod_count_factorial_eq r lam h2 hr
    exact_mod_cast h
  calc (∏ j : Fin (r - 1), (1 : ℝ) / (((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2) *
        (Nat.factorial (lam.count (j.val + 2)) : ℝ)))
      = (∏ j : Fin (r - 1), (((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2) *
          (Nat.factorial (lam.count (j.val + 2)) : ℝ))⁻¹) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [one_div]
    _ = ((∏ j : Fin (r - 1), (((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2) *
          (Nat.factorial (lam.count (j.val + 2)) : ℝ))))⁻¹ := by
          rw [Finset.prod_inv_distrib]
    _ = (((∏ j : Fin (r - 1), ((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2)) *
          (∏ j : Fin (r - 1), (Nat.factorial (lam.count (j.val + 2)) : ℝ))))⁻¹ := by
          rw [Finset.prod_mul_distrib]
    _ = 1 / ((lam.prod : ℝ) * (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ))) := by
          rw [hpow, hfac, one_div]

/-- ℝ version of `prod_count_pow_eq_prod`. -/
lemma prod_count_pow_eq_prod_real (r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) :
    (∏ j : Fin (r - 1), ((j.val + 2 : ℕ) : ℝ) ^ lam.count (j.val + 2)) = (lam.prod : ℝ) := by
  have h := prod_count_pow_eq_prod r lam h2 hr
  exact_mod_cast h

/-- **Combinatorial identity**: the Cauchy weight of a cycle type equals
`∏_{j : Fin r} 1/((j.val+1)^(count_j) · count_j!)`. -/
lemma cycleTypeWeight_eq_prod_countVec (n r : ℕ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) (hsum : lam.sum ≤ n) (hrpos : 1 ≤ r) :
    cycleTypeWeight n lam = ∏ j : Fin r, (1 : ℝ) /
      (((j.val + 1 : ℕ) : ℝ) ^ (countVec n r lam j) * (Nat.factorial (countVec n r lam j) : ℝ)) := by
  cases r with
  | zero => omega
  | succ r' =>
      rw [Fin.prod_univ_succ]
      simp [countVec, Fin.val_zero, Fin.val_succ]
      ring_nf
      have hprod : (∏ x : Fin r', (↑(Multiset.count (2 + x.val) lam).factorial)⁻¹ *
            ((2 : ℝ) + (x.val : ℝ))⁻¹ ^ Multiset.count (2 + x.val) lam) =
          ((lam.prod : ℝ) * (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)))⁻¹ := by
        calc (∏ x : Fin r', (↑(Multiset.count (2 + x.val) lam).factorial)⁻¹ *
              ((2 : ℝ) + (x.val : ℝ))⁻¹ ^ Multiset.count (2 + x.val) lam)
            = (∏ x : Fin r', (↑(Multiset.count (2 + x.val) lam).factorial)⁻¹ *
                (((2 : ℝ) + (x.val : ℝ)) ^ Multiset.count (2 + x.val) lam)⁻¹) := by
                apply Finset.prod_congr rfl
                intro x hx
                rw [inv_pow]
          _ = ((∏ x : Fin r', (↑(Multiset.count (2 + x.val) lam).factorial)) *
                (∏ x : Fin r', ((2 : ℝ) + (x.val : ℝ)) ^ Multiset.count (2 + x.val) lam))⁻¹ := by
                rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
                rw [mul_inv_rev]
                rw [mul_comm]
          _ = ((∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)) * (lam.prod : ℝ))⁻¹ := by
                congr 1
                congr 1
                · simpa [Nat.succ_sub_one, add_comm] using
                    (by exact_mod_cast (prod_count_factorial_eq (r' + 1) lam h2 hr))
                · calc (∏ x : Fin r', ((2 : ℝ) + (x.val : ℝ)) ^ Multiset.count (2 + x.val) lam)
                      = ∏ x : Fin r', ((2 + x.val : ℕ) : ℝ) ^ Multiset.count (2 + x.val) lam := by
                          apply Finset.prod_congr rfl
                          intro x hx
                          norm_num [Nat.cast_add]
                    _ = (lam.prod : ℝ) := by
                          simpa [Nat.succ_sub_one, add_comm] using
                            (prod_count_pow_eq_prod_real (r' + 1) lam h2 hr)
          _ = ((lam.prod : ℝ) * (∏ d ∈ lam.toFinset, (Nat.factorial (lam.count d) : ℝ)))⁻¹ := by
                rw [mul_comm]
      rw [hprod]
      unfold cycleTypeWeight
      rw [one_div]
      ring_nf

/-- **The `xⁿ`-weighted identity**: `xⁿ·w(λ) = ∏ⱼ (x^{j+1}/(j+1))^(count_j)/count_j!`. -/
lemma pow_mul_cycleTypeWeight_eq_prod (n r : ℕ) (x : ℝ) (lam : Multiset ℕ)
    (h2 : ∀ d ∈ lam, 2 ≤ d) (hr : ∀ d ∈ lam, d ≤ r) (hsum : lam.sum ≤ n) (hrpos : 1 ≤ r) :
    x ^ n * cycleTypeWeight n lam = ∏ j : Fin r, nuTerm r x j (countVec n r lam j) := by
  rw [cycleTypeWeight_eq_prod_countVec n r lam h2 hr hsum hrpos]
  calc x ^ n * (∏ j : Fin r, (1 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ countVec n r lam j *
        (Nat.factorial (countVec n r lam j) : ℝ)))
      = (∏ j : Fin r, x ^ ((j.val + 1) * countVec n r lam j)) *
          (∏ j : Fin r, (1 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ countVec n r lam j *
            (Nat.factorial (countVec n r lam j) : ℝ))) := by
          congr 1
          conv_lhs => rw [← sum_mul_countVec_eq n r lam h2 hr hsum hrpos]
          rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ j : Fin r, nuTerm r x j (countVec n r lam j) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro j hj
          have hterm : nuTerm r x j (countVec n r lam j) =
              x ^ ((j.val + 1) * countVec n r lam j) /
                (((j.val + 1 : ℕ) : ℝ) ^ countVec n r lam j *
                  (Nat.factorial (countVec n r lam j) : ℝ)) := by
            unfold nuTerm
            rw [div_pow]
            rw [← pow_mul]
            rw [div_div]
          rw [hterm, mul_one_div]

/-- The probability that a random permutation of `[n]` has no cycle longer than `r`. -/
noncomputable def nuNoLong (n r : ℕ) : ℝ :=
  ∑ lam ∈ (cycleTypes n).filter (fun lam => ∀ d ∈ lam, d ≤ r), cycleTypeWeight n lam

/-- **The "no long cycles" bound**: `ν(n,r) ≤ x⁻ⁿ · exp(∑_{j : Fin r} x^{j.val+1}/(j.val+1))`
for `x ≥ 1`. -/
lemma nuNoLong_le_exp_bound (n r : ℕ) (x : ℝ) (hx : 1 ≤ x) (hrpos : 1 ≤ r) :
    nuNoLong n r ≤ x⁻¹ ^ n * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := by
  let s : Finset (Multiset ℕ) := (cycleTypes n).filter (fun lam => ∀ d ∈ lam, d ≤ r)
  let C : Finset (Fin r → ℕ) := Fintype.piFinset (fun _ : Fin r => Finset.range (n + 1))
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hstep1 : x ^ n * nuNoLong n r = ∑ lam ∈ s, ∏ j : Fin r, nuTerm r x j (countVec n r lam j) := by
    unfold nuNoLong
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lam hlam
    have hsmall : ∀ d ∈ lam, d ≤ r := (Finset.mem_filter.mp hlam).2
    have hct : lam ∈ cycleTypes n := (Finset.mem_filter.mp hlam).1
    have h2 : ∀ d ∈ lam, 2 ≤ d := mem_cycleTypes_two_le hct
    have hsum : lam.sum ≤ n := mem_cycleTypes_sum_le hct
    rw [pow_mul_cycleTypeWeight_eq_prod n r x lam h2 hsmall hsum hrpos]
  have hinj : Set.InjOn (countVec n r) (↑s : Set (Multiset ℕ)) := by
    intro lam₁ hlam₁ lam₂ hlam₂ h
    apply countVec_injective n r
    · intro d hd
      exact ⟨mem_cycleTypes_two_le (Finset.mem_filter.mp hlam₁).1 d hd, (Finset.mem_filter.mp hlam₁).2 d hd⟩
    · intro d hd
      exact ⟨mem_cycleTypes_two_le (Finset.mem_filter.mp hlam₂).1 d hd, (Finset.mem_filter.mp hlam₂).2 d hd⟩
    · exact h
  have hmemC : ∀ lam ∈ s, countVec n r lam ∈ C := by
    intro lam hlam
    rw [Fintype.mem_piFinset]
    intro j
    exact countVec_mem_range n r lam (mem_cycleTypes_sum_le (Finset.mem_filter.mp hlam).1) j
  have himage_subset : s.image (countVec n r) ⊆ C := by
    rw [Finset.image_subset_iff]
    intro lam hlam
    exact hmemC lam hlam
  have hle : x ^ n * nuNoLong n r ≤ Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := by
    calc x ^ n * nuNoLong n r
        = ∑ lam ∈ s, ∏ j : Fin r, nuTerm r x j (countVec n r lam j) := hstep1
      _ = ∑ c ∈ s.image (countVec n r), ∏ j : Fin r, nuTerm r x j (c j) := by
            rw [Finset.sum_image]
            exact hinj
      _ ≤ ∑ c ∈ C, ∏ j : Fin r, nuTerm r x j (c j) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg himage_subset (fun c hc hnot =>
              Finset.prod_nonneg (fun j hj => by unfold nuTerm; positivity))
      _ = ∏ j : Fin r, ∑ c ∈ Finset.range (n + 1), nuTerm r x j c := by
            dsimp [C]
            rw [← Finset.prod_univ_sum]
      _ ≤ ∏ j : Fin r, Real.exp (x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := by
            apply Finset.prod_le_prod
            · intro j hj
              exact Finset.sum_nonneg (fun c hc => by unfold nuTerm; positivity)
            · intro j hj
              unfold nuTerm
              exact Real.sum_le_exp_of_nonneg (by positivity) (n + 1)
      _ = Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := by
            rw [Real.exp_sum]
  have hxneg_nonneg : 0 ≤ x⁻¹ ^ n := by positivity
  have hle2 : x⁻¹ ^ n * (x ^ n * nuNoLong n r) ≤ x⁻¹ ^ n * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hle hxneg_nonneg
  have hxinv : x⁻¹ ^ n * x ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hxpos), one_pow]
  have hsimp : x⁻¹ ^ n * (x ^ n * nuNoLong n r) = nuNoLong n r := by
    rw [← mul_assoc, hxinv, one_mul]
  rwa [hsimp] at hle2

/-! ### Harmonic bound and the concrete `ν = O(n⁻³)` instantiation -/

/-- `∑_{j=1}^r 1/j ≤ 1 + log r` for `r ≥ 1`. -/
lemma harmonic_le_log (r : ℕ) (hr : 1 ≤ r) :
    (∑ j ∈ Finset.Icc 1 r, (1 : ℝ) / (j : ℝ)) ≤ 1 + Real.log (r : ℝ) := by
  have hle : ∀ j ∈ Finset.Icc 2 r, (1 : ℝ) / (j : ℝ) ≤
      Real.log (j : ℝ) - Real.log ((j - 1 : ℕ) : ℝ) := by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj2, hjr⟩
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hjm1pos : 0 < ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j - 1)
    have hjm1eq : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      norm_num [Nat.cast_sub (by omega : 1 ≤ j)]
    have hx : 0 < (j : ℝ) / ((j - 1 : ℕ) : ℝ) := div_pos hjpos hjm1pos
    have h := Real.one_sub_inv_le_log_of_pos hx
    have h1 : 1 - ((j : ℝ) / ((j - 1 : ℕ) : ℝ))⁻¹ = (1 : ℝ) / (j : ℝ) := by
      rw [hjm1eq]
      have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
      field_simp [hjne]
      ring
    have h2 : Real.log ((j : ℝ) / ((j - 1 : ℕ) : ℝ)) = Real.log (j : ℝ) - Real.log ((j - 1 : ℕ) : ℝ) := by
      exact Real.log_div (ne_of_gt hjpos) (ne_of_gt hjm1pos)
    rw [← h2, ← h1]
    exact h
  have htelescope : (∑ j ∈ Finset.Icc 2 r, (Real.log (j : ℝ) - Real.log ((j - 1 : ℕ) : ℝ))) = Real.log (r : ℝ) := by
    rw [show Finset.Icc 2 r = Finset.Ico 2 (r + 1) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
    rw [Finset.sum_Ico_eq_sum_range (fun j => Real.log (j : ℝ) - Real.log ((j - 1 : ℕ) : ℝ)) 2 (r + 1)]
    rw [show r + 1 - 2 = r - 1 by omega]
    have hsummand : (∑ k ∈ Finset.range (r - 1),
        (Real.log ((2 + k : ℕ) : ℝ) - Real.log (((2 + k - 1 : ℕ) : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range (r - 1), (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (2 + k : ℕ) = k + 2 by omega]
      rw [show (k + 2 - 1 : ℕ) = k + 1 by omega]
    rw [hsummand]
    rw [Finset.sum_range_sub (fun i => Real.log ((i + 1 : ℕ) : ℝ)) (r - 1)]
    simp [Nat.sub_add_cancel hr]
  have hmain : (∑ j ∈ Finset.Icc 2 r, (1 : ℝ) / (j : ℝ)) ≤ Real.log (r : ℝ) := by
    calc (∑ j ∈ Finset.Icc 2 r, (1 : ℝ) / (j : ℝ))
        ≤ ∑ j ∈ Finset.Icc 2 r, (Real.log (j : ℝ) - Real.log ((j - 1 : ℕ) : ℝ)) := by
            exact Finset.sum_le_sum hle
      _ = Real.log (r : ℝ) := htelescope
  calc (∑ j ∈ Finset.Icc 1 r, (1 : ℝ) / (j : ℝ))
      = 1 + ∑ j ∈ Finset.Icc 2 r, (1 : ℝ) / (j : ℝ) := by
          rw [show Finset.Icc 1 r = insert 1 (Finset.Icc 2 r) by
            ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
          rw [Finset.sum_insert]
          · norm_num
          · simp
    _ ≤ 1 + Real.log (r : ℝ) := add_le_add_right hmain 1

set_option maxHeartbeats 800000

lemma tendsto_rpow_neg_nat_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
  have hpos : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ a)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hpos
  refine hinv.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℕ)] with n hn
  have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  exact (Real.rpow_neg hnR a).symm

lemma log_le_c_mul_pow15 :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) := by
  have h := ((isLittleO_log_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp_tendsto tendsto_natCast_atTop_atTop).def
    (by norm_num : 0 < (1/100 : ℝ))
  filter_upwards [h, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  change ‖Real.log (n : ℝ)‖ ≤ (1/100 : ℝ) * ‖(n : ℝ) ^ (1/15 : ℝ)‖ at hn
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ (1/15 : ℝ) := Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le n)) _
  rw [Real.norm_of_nonneg hlog_nonneg] at hn
  rw [Real.norm_of_nonneg hrpow_nonneg] at hn
  exact hn

lemma exp_two_pow_neg_le_two :
    ∀ᶠ n : ℕ in atTop, Real.exp (2 * (n : ℝ) ^ (-(1/210 : ℝ))) ≤ 2 := by
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1/210 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_nat_atTop (1/210 : ℝ) (by norm_num)
  have htwo : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (-(1/210 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hneg.const_mul 2)
  have hexp : Tendsto (fun n : ℕ => Real.exp (2 * (n : ℝ) ^ (-(1/210 : ℝ)))) atTop (𝓝 1) := by
    have h : Tendsto Real.exp (𝓝 0) (𝓝 (Real.exp 0)) := Real.continuous_exp.tendsto 0
    simpa [Real.exp_zero] using h.comp htwo
  have hlt : ∀ᶠ n : ℕ in atTop, Real.exp (2 * (n : ℝ) ^ (-(1/210 : ℝ))) < 2 := by
    exact hexp (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  exact hlt.mono (fun n hn => le_of_lt hn)

lemma exp_neg_half_pow15_le :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) ≤ (2^45 : ℝ) / (n : ℝ) ^ 3 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hhalf : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ) / 2) atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro b
    let b' : ℝ := max (b * 2) 1
    have hb' : ∀ᶠ n : ℕ in atTop, b' ≤ (n : ℝ) ^ (1/15 : ℝ) := (tendsto_atTop.mp hpow) b'
    refine hb'.mono (fun n hn => ?_)
    have hb2 : b * 2 ≤ b' := le_max_left _ _
    have hle : b * 2 ≤ (n : ℝ) ^ (1/15 : ℝ) := le_trans hb2 hn
    nlinarith
  have h45 : (fun x : ℝ => x ^ (45 : ℝ)) =o[atTop] Real.exp := isLittleO_rpow_exp_atTop 45
  have h45c : (fun n : ℕ => ((n : ℝ) ^ (1/15 : ℝ) / 2) ^ (45 : ℝ)) =o[atTop]
      (fun n : ℕ => Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2)) := h45.comp_tendsto hhalf
  have hge : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ (1/15 : ℝ) / 2) ^ (45 : ℝ) ≤
      Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2) := by
    have h := (h45c.def (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnonneg1 : 0 ≤ ((n : ℝ) ^ (1/15 : ℝ) / 2) ^ (45 : ℝ) := by
      exact Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hnR _) (by norm_num : 0 ≤ (2 : ℝ))) _
    have hnonneg2 : 0 ≤ Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2) := Real.exp_nonneg _
    rw [Real.norm_of_nonneg hnonneg1] at hn
    rw [Real.norm_of_nonneg hnonneg2] at hn
    simpa [one_mul] using hn
  filter_upwards [hge, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hpow45 : ((n : ℝ) ^ (1/15 : ℝ) / 2) ^ (45 : ℝ) = (n : ℝ) ^ 3 / (2^45 : ℝ) := by
    rw [Real.div_rpow (Real.rpow_nonneg hnR _) (by norm_num : 0 ≤ (2 : ℝ)) (45 : ℝ)]
    rw [← Real.rpow_natCast (n : ℝ) 3]
    rw [← Real.rpow_mul hnR (1/15 : ℝ) (45 : ℝ)]
    congr 1
    · norm_num
    · norm_num
  have hnpos : 0 < (n : ℝ) ^ 3 := by positivity
  have hden : 0 < (2^45 : ℝ) := by positivity
  have hle : (n : ℝ) ^ 3 ≤ Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2) * (2^45 : ℝ) := by
    rw [hpow45] at hn
    rwa [div_le_iff₀ hden] at hn
  rw [Real.exp_neg ((n : ℝ) ^ (1/15 : ℝ) / 2)]
  rw [le_div_iff₀ hnpos]
  rw [inv_mul_le_iff₀ (Real.exp_pos _)]
  exact hle

lemma one_add_log_two_le_pow15_div_eight :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) + Real.log 2 ≤ (n : ℝ) ^ (1/15 : ℝ) / 8 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hge := (tendsto_atTop.mp hpow) (8 * ((1 : ℝ) + Real.log 2))
  exact hge.mono (fun n hn => by nlinarith)

lemma sum_fin_inv_add_one_eq (r : ℕ) :
    (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) = (∑ t ∈ Finset.Icc 1 r, (1 : ℝ) / (t : ℝ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (1 : ℝ) / ((i + 1 : ℕ) : ℝ)) r]
  rw [show Finset.Icc 1 r = Finset.Ico 1 (r + 1) by
    ext t; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range (fun t => (1 : ℝ) / (t : ℝ)) 1 (r + 1)]
  rw [show r + 1 - 1 = r by omega]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (1 + i : ℕ) = i + 1 by omega]


lemma exp_sum_fin_le_half_pow15 :
    ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin (⌈(n : ℝ)^(13/14 : ℝ)⌉₊),
        Real.exp ((n : ℝ) ^ (-(14/15 : ℝ))) ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 2 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), exp_two_pow_neg_le_two,
      log_le_c_mul_pow15, one_add_log_two_le_pow15_div_eight] with n hn1 hexp2 hlog hconst
  let x : ℝ := Real.exp ((n : ℝ) ^ (-(14/15 : ℝ)))
  let r : ℕ := ⌈(n : ℝ) ^ (13/14 : ℝ)⌉₊
  have hnR0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (Real.rpow_nonneg hnR0 _)
  have hr_le : (r : ℝ) ≤ (n : ℝ) ^ (13/14 : ℝ) + 1 := by
    dsimp [r]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hnR0 _))
  have hpow910_ge1 : 1 ≤ (n : ℝ) ^ (13/14 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hnR1 (by norm_num : 0 ≤ (13/14 : ℝ))
    simpa [Real.one_rpow] using h
  have hr_le2 : (r : ℝ) ≤ 2 * (n : ℝ) ^ (13/14 : ℝ) := by
    nlinarith [hr_le, hpow910_ge1]
  have hnpow_nonneg : 0 ≤ (n : ℝ) ^ (-(14/15 : ℝ)) := Real.rpow_nonneg hnR0 _
  have hpowadd : (n : ℝ)^(13/14 : ℝ) * (n : ℝ)^(-(14/15 : ℝ)) = (n : ℝ)^(-(1/210 : ℝ)) := by
    rw [← Real.rpow_add hnRpos (13/14 : ℝ) (-(14/15 : ℝ))]
    congr 1
    norm_num
  have hnpow_le : (n : ℝ)^(-(14/15 : ℝ)) ≤ (n : ℝ)^(-(1/210 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hnR1 ?_
    norm_num
  have hr_npow : (r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) ≤ 2 * (n : ℝ) ^ (-(1/210 : ℝ)) := by
    have h1 : (r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) ≤
        ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) :=
      mul_le_mul_of_nonneg_right hr_le hnpow_nonneg
    have h2 : ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) ≤
        2 * (n : ℝ)^(-(1/210 : ℝ)) := by
      have h' : ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) =
          (n : ℝ)^(-(1/210 : ℝ)) + (n : ℝ)^(-(14/15 : ℝ)) := by
        rw [add_mul, hpowadd, one_mul]
      rw [h']
      nlinarith [hnpow_le]
    exact le_trans h1 h2
  have hxr_le : x ^ r ≤ 2 := by
    have hxr : x ^ r = Real.exp ((r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) := by
      dsimp [x]
      rw [Real.exp_nat_mul]
    rw [hxr]
    have hle : Real.exp ((r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) ≤
        Real.exp (2 * (n : ℝ) ^ (-(1/210 : ℝ))) := by
      exact Real.exp_le_exp.mpr hr_npow
    exact le_trans hle hexp2
  have hfin_le : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 4 := by
    have hharm := harmonic_le_log r (by
      dsimp [r]
      exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr (by
        exact Real.rpow_pos_of_pos hnRpos _)))
    have hreidx := sum_fin_inv_add_one_eq r
    have hlogr : Real.log (r : ℝ) ≤ Real.log 2 + (13/14 : ℝ) * Real.log (n : ℝ) := by
      have hrpos : 0 < (r : ℝ) := by
        exact_mod_cast (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _))
      have h1 : (r : ℝ) ≤ 2 * (n : ℝ) ^ (13/14 : ℝ) := hr_le2
      have h2 : Real.log (r : ℝ) ≤ Real.log (2 * (n : ℝ) ^ (13/14 : ℝ)) :=
        Real.log_le_log hrpos (le_trans h1 (by nlinarith))
      have h3 : Real.log (2 * (n : ℝ) ^ (13/14 : ℝ)) = Real.log 2 + (13/14 : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact ne_of_gt (Real.rpow_pos_of_pos hnRpos _))]
        rw [Real.log_rpow hnRpos (13/14 : ℝ)]
      exact le_trans h2 (le_of_eq h3)
    have hlog_le := (log_le_c_mul_pow15)
    have hsum_le : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤ 1 + Real.log (r : ℝ) := by
      rw [hreidx]
      exact hharm
    have hmain : 1 + Real.log (r : ℝ) ≤ (n : ℝ) ^ (1/15 : ℝ) / 4 := by
      have hlog_n : Real.log (n : ℝ) ≤ (1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) := hlog
      have h910log : (13/14 : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1/15 : ℝ) / 8 := by
        have hcoef : (13/14 : ℝ) * (1/100 : ℝ) ≤ (1/8 : ℝ) := by norm_num
        have h := mul_le_mul_of_nonneg_left hlog_n (by norm_num : 0 ≤ (13/14 : ℝ))
        calc (13/14 : ℝ) * Real.log (n : ℝ)
            ≤ (13/14 : ℝ) * ((1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ)) := h
          _ = ((13/14 : ℝ) * (1/100 : ℝ)) * (n : ℝ) ^ (1/15 : ℝ) := by ring
          _ ≤ (1/8 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) :=
                mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hnR0 _)
          _ = (n : ℝ) ^ (1/15 : ℝ) / 8 := by ring
      nlinarith [hlogr, h910log, hconst]
    exact le_trans hsum_le hmain
  -- now bound the actual sum
  have hsum_bound : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 2 := by
    have hpoint : ∀ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ) ≤
        x ^ r / ((j.val + 1 : ℕ) : ℝ) := by
      intro j
      have hjr : j.val + 1 ≤ r := by omega
      have hpow : x ^ (j.val + 1) ≤ x ^ r := pow_le_pow_right₀ hx1 hjr
      exact div_le_div_of_nonneg_right hpow (by positivity)
    have hsum_le' : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
        ∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ) := by
      exact Finset.sum_le_sum (fun j hj => hpoint j)
    have hfactor : (∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ)) =
        x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_eq_mul_inv, one_div]
    have hxr_nonneg : 0 ≤ x ^ r := pow_nonneg (le_of_lt (Real.exp_pos _)) _
    have hle : x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
        2 * ((n : ℝ) ^ (1/15 : ℝ) / 4) := by
      have h1 : x ^ r ≤ 2 := hxr_le
      have h2 : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1/15 : ℝ) / 4 := hfin_le
      have h3 : x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
          2 * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : 2 * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
          2 * ((n : ℝ) ^ (1/15 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num : 0 ≤ (2 : ℝ))
      exact le_trans h3 h4
    calc (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ))
        ≤ ∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ) := hsum_le'
      _ = x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) := hfactor
      _ ≤ 2 * ((n : ℝ) ^ (1/15 : ℝ) / 4) := hle
      _ ≤ (n : ℝ) ^ (1/15 : ℝ) / 2 := by nlinarith
  simpa [x, r] using hsum_bound



lemma nuNoLong_bound :
    ∀ᶠ n : ℕ in atTop, nuNoLong n (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (2^45 : ℝ) / (n : ℝ)^3 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), exp_sum_fin_le_half_pow15,
      exp_neg_half_pow15_le] with n hn1 hsum hexpdecay
  let x : ℝ := Real.exp ((n : ℝ) ^ (-(14/15 : ℝ)))
  let r : ℕ := ⌈(n : ℝ) ^ (13/14 : ℝ)⌉₊
  have hnR0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (Real.rpow_nonneg hnR0 _)
  have hrpos : 1 ≤ r := by
    dsimp [r]
    exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _))
  have hbound := nuNoLong_le_exp_bound n r x hx1 hrpos
  -- hbound : nuNoLong n r ≤ x⁻¹^n * exp(Σ x^{j+1}/(j+1))
  have hsum' : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 2 := by
    simpa [x, r] using hsum
  have hexp_le : Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2) := by
    exact Real.exp_le_exp.mpr hsum'
  have hxinv : x⁻¹ ^ n = Real.exp (-(n : ℝ) ^ (1/15 : ℝ)) := by
    dsimp [x]
    rw [← Real.exp_neg]
    rw [← Real.exp_nat_mul]
    congr 1
    have hpow : (n : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) = (n : ℝ) ^ (1/15 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hnRpos (1 : ℝ) (-(14/15 : ℝ))]
      congr 1
      norm_num
    calc (n : ℝ) * (-(n : ℝ) ^ (-(14/15 : ℝ)))
        = -((n : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) := by ring
      _ = -(n : ℝ) ^ (1/15 : ℝ) := by rw [hpow]
  have hmul_le : x⁻¹ ^ n * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) := by
    rw [hxinv]
    have h : Real.exp (-(n : ℝ) ^ (1/15 : ℝ)) *
        Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2) = Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-(n : ℝ) ^ (1/15 : ℝ)) *
            Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ))
        ≤ Real.exp (-(n : ℝ) ^ (1/15 : ℝ)) * Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 2) := by
              exact mul_le_mul_of_nonneg_left hexp_le (Real.exp_nonneg _)
      _ = Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) := h
  have hdecay : Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) ≤ (2^45 : ℝ) / (n : ℝ) ^ 3 := hexpdecay
  calc nuNoLong n r
      ≤ x⁻¹ ^ n * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := hbound
    _ ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) := hmul_le
    _ ≤ (2^45 : ℝ) / (n : ℝ) ^ 3 := hdecay

lemma exp_neg_quarter_pow15_le :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 4)) ≤ (4^45 : ℝ) / (n : ℝ) ^ 3 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hquart : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ) / 4) atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro b
    let b' : ℝ := max (b * 4) 1
    have hb' : ∀ᶠ n : ℕ in atTop, b' ≤ (n : ℝ) ^ (1/15 : ℝ) := (tendsto_atTop.mp hpow) b'
    refine hb'.mono (fun n hn => ?_)
    have hb2 : b * 4 ≤ b' := le_max_left _ _
    have hle : b * 4 ≤ (n : ℝ) ^ (1/15 : ℝ) := le_trans hb2 hn
    nlinarith
  have h45 : (fun x : ℝ => x ^ (45 : ℝ)) =o[atTop] Real.exp := isLittleO_rpow_exp_atTop 45
  have h45c : (fun n : ℕ => ((n : ℝ) ^ (1/15 : ℝ) / 4) ^ (45 : ℝ)) =o[atTop]
      (fun n : ℕ => Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4)) := h45.comp_tendsto hquart
  have hge : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ (1/15 : ℝ) / 4) ^ (45 : ℝ) ≤
      Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4) := by
    have h := (h45c.def (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnonneg1 : 0 ≤ ((n : ℝ) ^ (1/15 : ℝ) / 4) ^ (45 : ℝ) := by
      exact Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hnR _) (by norm_num : 0 ≤ (4 : ℝ))) _
    have hnonneg2 : 0 ≤ Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4) := Real.exp_nonneg _
    rw [Real.norm_of_nonneg hnonneg1] at hn
    rw [Real.norm_of_nonneg hnonneg2] at hn
    simpa [one_mul] using hn
  filter_upwards [hge, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hpow45 : ((n : ℝ) ^ (1/15 : ℝ) / 4) ^ (45 : ℝ) = (n : ℝ) ^ 3 / (4^45 : ℝ) := by
    rw [Real.div_rpow (Real.rpow_nonneg hnR _) (by norm_num : 0 ≤ (4 : ℝ)) (45 : ℝ)]
    rw [← Real.rpow_natCast (n : ℝ) 3]
    rw [← Real.rpow_mul hnR (1/15 : ℝ) (45 : ℝ)]
    congr 1
    · norm_num
    · norm_num
  have hnpos : 0 < (n : ℝ) ^ 3 := by positivity
  have hden : 0 < (4^45 : ℝ) := by positivity
  have hle : (n : ℝ) ^ 3 ≤ Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4) * (4^45 : ℝ) := by
    rw [hpow45] at hn
    rwa [div_le_iff₀ hden] at hn
  rw [Real.exp_neg ((n : ℝ) ^ (1/15 : ℝ) / 4)]
  rw [le_div_iff₀ hnpos]
  rw [inv_mul_le_iff₀ (Real.exp_pos _)]
  exact hle

lemma one_add_log_two_le_pow15_div_sixteen :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) + Real.log 2 ≤ (n : ℝ) ^ (1/15 : ℝ) / 16 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hge := (tendsto_atTop.mp hpow) (16 * ((1 : ℝ) + Real.log 2))
  exact hge.mono (fun n hn => by nlinarith)


lemma exp_sum_fin_le_quarter_pow15 :
    ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin (⌈(n : ℝ)^(13/14 : ℝ)⌉₊),
        Real.exp ((n : ℝ) ^ (-(14/15 : ℝ))) ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 4 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), exp_two_pow_neg_le_two,
      log_le_c_mul_pow15, one_add_log_two_le_pow15_div_sixteen] with n hn1 hexp2 hlog hconst
  let x : ℝ := Real.exp ((n : ℝ) ^ (-(14/15 : ℝ)))
  let r : ℕ := ⌈(n : ℝ) ^ (13/14 : ℝ)⌉₊
  have hnR0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (Real.rpow_nonneg hnR0 _)
  have hr_le : (r : ℝ) ≤ (n : ℝ) ^ (13/14 : ℝ) + 1 := by
    dsimp [r]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hnR0 _))
  have hpow910_ge1 : 1 ≤ (n : ℝ) ^ (13/14 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hnR1 (by norm_num : 0 ≤ (13/14 : ℝ))
    simpa [Real.one_rpow] using h
  have hnpow_nonneg : 0 ≤ (n : ℝ) ^ (-(14/15 : ℝ)) := Real.rpow_nonneg hnR0 _
  have hpowadd : (n : ℝ)^(13/14 : ℝ) * (n : ℝ)^(-(14/15 : ℝ)) = (n : ℝ)^(-(1/210 : ℝ)) := by
    rw [← Real.rpow_add hnRpos (13/14 : ℝ) (-(14/15 : ℝ))]
    congr 1
    norm_num
  have hnpow_le : (n : ℝ)^(-(14/15 : ℝ)) ≤ (n : ℝ)^(-(1/210 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hnR1 ?_
    norm_num
  have hr_npow : (r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) ≤ 2 * (n : ℝ) ^ (-(1/210 : ℝ)) := by
    have h1 : (r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) ≤
        ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) :=
      mul_le_mul_of_nonneg_right hr_le hnpow_nonneg
    have h2 : ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) ≤
        2 * (n : ℝ)^(-(1/210 : ℝ)) := by
      have h' : ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) =
          (n : ℝ)^(-(1/210 : ℝ)) + (n : ℝ)^(-(14/15 : ℝ)) := by
        rw [add_mul, hpowadd, one_mul]
      rw [h']
      nlinarith [hnpow_le]
    exact le_trans h1 h2
  have hxr_le : x ^ r ≤ 2 := by
    have hxr : x ^ r = Real.exp ((r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) := by
      dsimp [x]
      rw [Real.exp_nat_mul]
    rw [hxr]
    have hle : Real.exp ((r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) ≤
        Real.exp (2 * (n : ℝ) ^ (-(1/210 : ℝ))) :=
      Real.exp_le_exp.mpr hr_npow
    exact le_trans hle hexp2
  have hfin_le : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 8 := by
    have hharm := harmonic_le_log r (by
      dsimp [r]
      exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _)))
    have hreidx := sum_fin_inv_add_one_eq r
    have hlogr : Real.log (r : ℝ) ≤ Real.log 2 + (13/14 : ℝ) * Real.log (n : ℝ) := by
      have hrpos : 0 < (r : ℝ) := by
        exact_mod_cast (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _))
      have h2 : Real.log (r : ℝ) ≤ Real.log (2 * (n : ℝ) ^ (13/14 : ℝ)) :=
        Real.log_le_log hrpos (by
          have h1 : (r : ℝ) ≤ (n : ℝ) ^ (13/14 : ℝ) + 1 := hr_le
          nlinarith [h1, hpow910_ge1])
      have h3 : Real.log (2 * (n : ℝ) ^ (13/14 : ℝ)) = Real.log 2 + (13/14 : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact ne_of_gt (Real.rpow_pos_of_pos hnRpos _))]
        rw [Real.log_rpow hnRpos (13/14 : ℝ)]
      exact le_trans h2 (le_of_eq h3)
    have hsum_le : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤ 1 + Real.log (r : ℝ) := by
      rw [hreidx]
      exact hharm
    have hmain : 1 + Real.log (r : ℝ) ≤ (n : ℝ) ^ (1/15 : ℝ) / 8 := by
      have hlog_n : Real.log (n : ℝ) ≤ (1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) := hlog
      have h910log : (13/14 : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1/15 : ℝ) / 16 := by
        have hcoef : (13/14 : ℝ) * (1/100 : ℝ) ≤ (1/16 : ℝ) := by norm_num
        have h := mul_le_mul_of_nonneg_left hlog_n (by norm_num : 0 ≤ (13/14 : ℝ))
        calc (13/14 : ℝ) * Real.log (n : ℝ)
            ≤ (13/14 : ℝ) * ((1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ)) := h
          _ = ((13/14 : ℝ) * (1/100 : ℝ)) * (n : ℝ) ^ (1/15 : ℝ) := by ring
          _ ≤ (1/16 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) :=
                mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hnR0 _)
          _ = (n : ℝ) ^ (1/15 : ℝ) / 16 := by ring
      nlinarith [hlogr, h910log, hconst]
    exact le_trans hsum_le hmain
  have hsum_bound : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 4 := by
    have hpoint : ∀ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ) ≤
        x ^ r / ((j.val + 1 : ℕ) : ℝ) := by
      intro j
      have hjr : j.val + 1 ≤ r := by omega
      have hpow : x ^ (j.val + 1) ≤ x ^ r := pow_le_pow_right₀ hx1 hjr
      exact div_le_div_of_nonneg_right hpow (by positivity)
    have hsum_le' : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
        ∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j hj => hpoint j)
    have hfactor : (∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ)) =
        x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_eq_mul_inv, one_div]
    have hle : x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
        2 * ((n : ℝ) ^ (1/15 : ℝ) / 8) := by
      have h1 : x ^ r ≤ 2 := hxr_le
      have h2 : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1/15 : ℝ) / 8 := hfin_le
      have h3 : x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
          2 * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : 2 * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
          2 * ((n : ℝ) ^ (1/15 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num : 0 ≤ (2 : ℝ))
      exact le_trans h3 h4
    calc (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ))
        ≤ ∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ) := hsum_le'
      _ = x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) := hfactor
      _ ≤ 2 * ((n : ℝ) ^ (1/15 : ℝ) / 8) := hle
      _ ≤ (n : ℝ) ^ (1/15 : ℝ) / 4 := by nlinarith
  simpa [x, r] using hsum_bound



lemma nuNoLong_le_const_div_cube_uniform :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (n : ℝ) ≤ 2 * (m : ℝ) → m ≤ n →
      nuNoLong m (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (4^45 : ℝ) / (n : ℝ)^3 := by
  filter_upwards [exp_sum_fin_le_quarter_pow15, exp_neg_quarter_pow15_le,
      Filter.eventually_ge_atTop (1 : ℕ)] with n hsum hdecay hn1
  intro m hnm hmn
  let x : ℝ := Real.exp ((n : ℝ) ^ (-(14/15 : ℝ)))
  let r : ℕ := ⌈(n : ℝ) ^ (13/14 : ℝ)⌉₊
  have hnR0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (Real.rpow_nonneg hnR0 _)
  have hrpos : 1 ≤ r := by
    dsimp [r]
    exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _))
  have hbound := nuNoLong_le_exp_bound m r x hx1 hrpos
  have hsum' : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 4 := by
    simpa [x, r] using hsum
  have hexp_le : Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4) := Real.exp_le_exp.mpr hsum'
  have hxinv_le : x⁻¹ ^ m ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) := by
    have hxinv : x⁻¹ ^ m = Real.exp (-((m : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)))) := by
      dsimp [x]
      rw [← Real.exp_neg]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hxinv]
    apply Real.exp_le_exp.mpr
    have hmge : (n : ℝ) / 2 ≤ (m : ℝ) := by nlinarith [hnm]
    have hnpow_nonneg : 0 ≤ (n : ℝ) ^ (-(14/15 : ℝ)) := Real.rpow_nonneg hnR0 _
    have h1 : (n : ℝ) / 2 * (n : ℝ) ^ (-(14/15 : ℝ)) ≤ (m : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) :=
      mul_le_mul_of_nonneg_right hmge hnpow_nonneg
    have h2 : (n : ℝ) / 2 * (n : ℝ) ^ (-(14/15 : ℝ)) = (n : ℝ) ^ (1/15 : ℝ) / 2 := by
      have hpow : (n : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) = (n : ℝ) ^ (1/15 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnRpos (1 : ℝ) (-(14/15 : ℝ))]
        congr 1
        norm_num
      calc (n : ℝ) / 2 * (n : ℝ) ^ (-(14/15 : ℝ))
          = ((n : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) / 2 := by ring
        _ = (n : ℝ) ^ (1/15 : ℝ) / 2 := by rw [hpow]
    nlinarith [h1, h2]
  have hmul_le : x⁻¹ ^ m * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 4)) := by
    have hexp_prod : Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) * Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4) =
        Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc x⁻¹ ^ m * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ))
        ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 2)) * Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 4) :=
            mul_le_mul hxinv_le hexp_le (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 4)) := hexp_prod
  have hdecay' : Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 4)) ≤ (4^45 : ℝ) / (n : ℝ) ^ 3 := hdecay
  calc nuNoLong m r
      ≤ x⁻¹ ^ m * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := hbound
    _ ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 4)) := hmul_le
    _ ≤ (4^45 : ℝ) / (n : ℝ) ^ 3 := hdecay'

lemma exp_neg_div_pow15_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / c)) ≤ (c ^ 45) / (n : ℝ) ^ 3 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ) / c) atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro b
    let b' : ℝ := max (b * c) 1
    have hb' : ∀ᶠ n : ℕ in atTop, b' ≤ (n : ℝ) ^ (1/15 : ℝ) := (tendsto_atTop.mp hpow) b'
    refine hb'.mono (fun n hn => ?_)
    have hb2 : b * c ≤ b' := le_max_left _ _
    have hle : b * c ≤ (n : ℝ) ^ (1/15 : ℝ) := le_trans hb2 hn
    rw [le_div_iff₀ hc]
    exact hle
  have h45 : (fun x : ℝ => x ^ (45 : ℝ)) =o[atTop] Real.exp := isLittleO_rpow_exp_atTop 45
  have h45c : (fun n : ℕ => ((n : ℝ) ^ (1/15 : ℝ) / c) ^ (45 : ℝ)) =o[atTop]
      (fun n : ℕ => Real.exp ((n : ℝ) ^ (1/15 : ℝ) / c)) := h45.comp_tendsto hdiv
  have hge : ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ (1/15 : ℝ) / c) ^ (45 : ℝ) ≤
      Real.exp ((n : ℝ) ^ (1/15 : ℝ) / c) := by
    have h := (h45c.def (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnonneg1 : 0 ≤ ((n : ℝ) ^ (1/15 : ℝ) / c) ^ (45 : ℝ) := by
      exact Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hnR _) (le_of_lt hc)) _
    have hnonneg2 : 0 ≤ Real.exp ((n : ℝ) ^ (1/15 : ℝ) / c) := Real.exp_nonneg _
    rw [Real.norm_of_nonneg hnonneg1] at hn
    rw [Real.norm_of_nonneg hnonneg2] at hn
    simpa [one_mul] using hn
  filter_upwards [hge, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hpow45 : ((n : ℝ) ^ (1/15 : ℝ) / c) ^ (45 : ℝ) = (n : ℝ) ^ 3 / (c ^ 45) := by
    rw [Real.div_rpow (Real.rpow_nonneg hnR _) (le_of_lt hc) (45 : ℝ)]
    rw [← Real.rpow_natCast (n : ℝ) 3]
    rw [← Real.rpow_mul hnR (1/15 : ℝ) (45 : ℝ)]
    congr 1
    · norm_num
    · norm_num
  have hnpos : 0 < (n : ℝ) ^ 3 := by positivity
  have hden : 0 < c ^ 45 := pow_pos hc _
  have hle : (n : ℝ) ^ 3 ≤ Real.exp ((n : ℝ) ^ (1/15 : ℝ) / c) * (c ^ 45) := by
    rw [hpow45] at hn
    rwa [div_le_iff₀ hden] at hn
  rw [Real.exp_neg ((n : ℝ) ^ (1/15 : ℝ) / c)]
  rw [le_div_iff₀ hnpos]
  rw [inv_mul_le_iff₀ (Real.exp_pos _)]
  exact hle


lemma one_add_log_two_le_pow15_div_thirtytwo :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) + Real.log 2 ≤ (n : ℝ) ^ (1/15 : ℝ) / 32 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1/15 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hge := (tendsto_atTop.mp hpow) (32 * ((1 : ℝ) + Real.log 2))
  exact hge.mono (fun n hn => by nlinarith)

lemma exp_sum_fin_le_eighth_pow15 :
    ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin (⌈(n : ℝ)^(13/14 : ℝ)⌉₊),
        Real.exp ((n : ℝ) ^ (-(14/15 : ℝ))) ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 8 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), exp_two_pow_neg_le_two,
      log_le_c_mul_pow15, one_add_log_two_le_pow15_div_thirtytwo] with n hn1 hexp2 hlog hconst
  let x : ℝ := Real.exp ((n : ℝ) ^ (-(14/15 : ℝ)))
  let r : ℕ := ⌈(n : ℝ) ^ (13/14 : ℝ)⌉₊
  have hnR0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (Real.rpow_nonneg hnR0 _)
  have hr_le : (r : ℝ) ≤ (n : ℝ) ^ (13/14 : ℝ) + 1 := by
    dsimp [r]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hnR0 _))
  have hpow910_ge1 : 1 ≤ (n : ℝ) ^ (13/14 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hnR1 (by norm_num : 0 ≤ (13/14 : ℝ))
    simpa [Real.one_rpow] using h
  have hnpow_nonneg : 0 ≤ (n : ℝ) ^ (-(14/15 : ℝ)) := Real.rpow_nonneg hnR0 _
  have hpowadd : (n : ℝ)^(13/14 : ℝ) * (n : ℝ)^(-(14/15 : ℝ)) = (n : ℝ)^(-(1/210 : ℝ)) := by
    rw [← Real.rpow_add hnRpos (13/14 : ℝ) (-(14/15 : ℝ))]
    congr 1
    norm_num
  have hnpow_le : (n : ℝ)^(-(14/15 : ℝ)) ≤ (n : ℝ)^(-(1/210 : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le hnR1 ?_
    norm_num
  have hr_npow : (r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) ≤ 2 * (n : ℝ) ^ (-(1/210 : ℝ)) := by
    have h1 : (r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) ≤
        ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) :=
      mul_le_mul_of_nonneg_right hr_le hnpow_nonneg
    have h2 : ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) ≤
        2 * (n : ℝ)^(-(1/210 : ℝ)) := by
      have h' : ((n : ℝ)^(13/14 : ℝ) + 1) * (n : ℝ)^(-(14/15 : ℝ)) =
          (n : ℝ)^(-(1/210 : ℝ)) + (n : ℝ)^(-(14/15 : ℝ)) := by
        rw [add_mul, hpowadd, one_mul]
      rw [h']
      nlinarith [hnpow_le]
    exact le_trans h1 h2
  have hxr_le : x ^ r ≤ 2 := by
    have hxr : x ^ r = Real.exp ((r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) := by
      dsimp [x]
      rw [Real.exp_nat_mul]
    rw [hxr]
    have hle : Real.exp ((r : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) ≤
        Real.exp (2 * (n : ℝ) ^ (-(1/210 : ℝ))) :=
      Real.exp_le_exp.mpr hr_npow
    exact le_trans hle hexp2
  have hfin_le : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 16 := by
    have hharm := harmonic_le_log r (by
      dsimp [r]
      exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _)))
    have hreidx := sum_fin_inv_add_one_eq r
    have hlogr : Real.log (r : ℝ) ≤ Real.log 2 + (13/14 : ℝ) * Real.log (n : ℝ) := by
      have hrpos : 0 < (r : ℝ) := by
        exact_mod_cast (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _))
      have h2 : Real.log (r : ℝ) ≤ Real.log (2 * (n : ℝ) ^ (13/14 : ℝ)) :=
        Real.log_le_log hrpos (by
          have h1 : (r : ℝ) ≤ (n : ℝ) ^ (13/14 : ℝ) + 1 := hr_le
          nlinarith [h1, hpow910_ge1])
      have h3 : Real.log (2 * (n : ℝ) ^ (13/14 : ℝ)) = Real.log 2 + (13/14 : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact ne_of_gt (Real.rpow_pos_of_pos hnRpos _))]
        rw [Real.log_rpow hnRpos (13/14 : ℝ)]
      exact le_trans h2 (le_of_eq h3)
    have hsum_le : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤ 1 + Real.log (r : ℝ) := by
      rw [hreidx]
      exact hharm
    have hmain : 1 + Real.log (r : ℝ) ≤ (n : ℝ) ^ (1/15 : ℝ) / 16 := by
      have hlog_n : Real.log (n : ℝ) ≤ (1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) := hlog
      have h910log : (13/14 : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) ^ (1/15 : ℝ) / 32 := by
        have hcoef : (13/14 : ℝ) * (1/100 : ℝ) ≤ (1/32 : ℝ) := by norm_num
        have h := mul_le_mul_of_nonneg_left hlog_n (by norm_num : 0 ≤ (13/14 : ℝ))
        calc (13/14 : ℝ) * Real.log (n : ℝ)
            ≤ (13/14 : ℝ) * ((1/100 : ℝ) * (n : ℝ) ^ (1/15 : ℝ)) := h
          _ = ((13/14 : ℝ) * (1/100 : ℝ)) * (n : ℝ) ^ (1/15 : ℝ) := by ring
          _ ≤ (1/32 : ℝ) * (n : ℝ) ^ (1/15 : ℝ) :=
                mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hnR0 _)
          _ = (n : ℝ) ^ (1/15 : ℝ) / 32 := by ring
      nlinarith [hlogr, h910log, hconst]
    exact le_trans hsum_le hmain
  have hsum_bound : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 8 := by
    have hpoint : ∀ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ) ≤
        x ^ r / ((j.val + 1 : ℕ) : ℝ) := by
      intro j
      have hjr : j.val + 1 ≤ r := by omega
      have hpow : x ^ (j.val + 1) ≤ x ^ r := pow_le_pow_right₀ hx1 hjr
      exact div_le_div_of_nonneg_right hpow (by positivity)
    have hsum_le' : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
        ∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j hj => hpoint j)
    have hfactor : (∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ)) =
        x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_eq_mul_inv, one_div]
    have hle : x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
        2 * ((n : ℝ) ^ (1/15 : ℝ) / 16) := by
      have h1 : x ^ r ≤ 2 := hxr_le
      have h2 : (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1/15 : ℝ) / 16 := hfin_le
      have h3 : x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
          2 * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : 2 * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) ≤
          2 * ((n : ℝ) ^ (1/15 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num : 0 ≤ (2 : ℝ))
      exact le_trans h3 h4
    calc (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ))
        ≤ ∑ j : Fin r, x ^ r / ((j.val + 1 : ℕ) : ℝ) := hsum_le'
      _ = x ^ r * (∑ j : Fin r, (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ)) := hfactor
      _ ≤ 2 * ((n : ℝ) ^ (1/15 : ℝ) / 16) := hle
      _ ≤ (n : ℝ) ^ (1/15 : ℝ) / 8 := by nlinarith
  simpa [x, r] using hsum_bound



lemma nuNoLong_le_const_div_cube_uniform_sixth :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (n : ℝ) ≤ 6 * (m : ℝ) → m ≤ n →
      nuNoLong m (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (24 : ℝ) ^ 45 / (n : ℝ)^3 := by
  filter_upwards [exp_sum_fin_le_eighth_pow15, (exp_neg_div_pow15_le 24 (by norm_num)),
      Filter.eventually_ge_atTop (1 : ℕ)] with n hsum hdecay hn1
  intro m hnm hmn
  let x : ℝ := Real.exp ((n : ℝ) ^ (-(14/15 : ℝ)))
  let r : ℕ := ⌈(n : ℝ) ^ (13/14 : ℝ)⌉₊
  have hnR0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_exp (Real.rpow_nonneg hnR0 _)
  have hrpos : 1 ≤ r := by
    dsimp [r]
    exact Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnRpos _))
  have hbound := nuNoLong_le_exp_bound m r x hx1 hrpos
  have hsum' : (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      (n : ℝ) ^ (1/15 : ℝ) / 8 := by
    simpa [x, r] using hsum
  have hexp_le : Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 8) := Real.exp_le_exp.mpr hsum'
  have hxinv_le : x⁻¹ ^ m ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 6)) := by
    have hxinv : x⁻¹ ^ m = Real.exp (-((m : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)))) := by
      dsimp [x]
      rw [← Real.exp_neg]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hxinv]
    apply Real.exp_le_exp.mpr
    have hmge : (n : ℝ) / 6 ≤ (m : ℝ) := by nlinarith [hnm]
    have hnpow_nonneg : 0 ≤ (n : ℝ) ^ (-(14/15 : ℝ)) := Real.rpow_nonneg hnR0 _
    have h1 : (n : ℝ) / 6 * (n : ℝ) ^ (-(14/15 : ℝ)) ≤ (m : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) :=
      mul_le_mul_of_nonneg_right hmge hnpow_nonneg
    have h2 : (n : ℝ) / 6 * (n : ℝ) ^ (-(14/15 : ℝ)) = (n : ℝ) ^ (1/15 : ℝ) / 6 := by
      have hpow : (n : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ)) = (n : ℝ) ^ (1/15 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnRpos (1 : ℝ) (-(14/15 : ℝ))]
        congr 1
        norm_num
      calc (n : ℝ) / 6 * (n : ℝ) ^ (-(14/15 : ℝ))
          = ((n : ℝ) * (n : ℝ) ^ (-(14/15 : ℝ))) / 6 := by ring
        _ = (n : ℝ) ^ (1/15 : ℝ) / 6 := by rw [hpow]
    nlinarith [h1, h2]
  have hmul_le : x⁻¹ ^ m * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) ≤
      Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 24)) := by
    have hexp_prod : Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 6)) * Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 8) =
        Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 24)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc x⁻¹ ^ m * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ))
        ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 6)) * Real.exp ((n : ℝ) ^ (1/15 : ℝ) / 8) :=
            mul_le_mul hxinv_le hexp_le (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 24)) := hexp_prod
  have hdecay' : Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 24)) ≤ (24 : ℝ) ^ 45 / (n : ℝ) ^ 3 := hdecay
  calc nuNoLong m r
      ≤ x⁻¹ ^ m * Real.exp (∑ j : Fin r, x ^ (j.val + 1) / ((j.val + 1 : ℕ) : ℝ)) := hbound
    _ ≤ Real.exp (-((n : ℝ) ^ (1/15 : ℝ) / 24)) := hmul_le
    _ ≤ (24 : ℝ) ^ 45 / (n : ℝ) ^ 3 := hdecay'

/-- A *large* cycle: length `d ≥ n^{13/14}` (the `δ = 1/14` threshold). -/
def large (n d : ℕ) : Prop := (n : ℝ)^(13/14 : ℝ) ≤ (d : ℝ)

/-- Refined decoupling: summing the small part (disjoint, all cycles `≤ r`) out, the
total weight of all cycle types with fixed large part `L` is at most
`(1/L.prod) · ν(n-L.sum, r)`. -/
lemma sum_cycleTypeWeight_add_le_nu (n r : ℕ) (L : Multiset ℕ) (hL2 : ∀ d ∈ L, 2 ≤ d)
    (hLsum : L.sum ≤ n) :
    (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
        cycleTypeWeight n (L + S)) ≤ (1 / (L.prod : ℝ)) * nuNoLong (n - L.sum) r := by
  have hLprod_pos : 0 < (L.prod : ℝ) := by
    exact_mod_cast (Multiset.prod_pos (fun d hd => Nat.succ_le_iff.mp (by
      have := hL2 d hd; omega)))
  have hdec : ∀ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
      cycleTypeWeight n (L + S) ≤
        (1 / (L.prod : ℝ)) * cycleTypeWeight (n - L.sum) S := by
    intro S hS
    rw [Finset.mem_filter] at hS
    have hdisj : Disjoint L.toFinset S.toFinset := hS.2.1
    have hSval : S ∈ cycleTypes (n - L.sum) := hS.1
    have hS2 : ∀ d ∈ S, 2 ≤ d := mem_cycleTypes_two_le hSval
    have hSsum : S.sum ≤ n - L.sum := mem_cycleTypes_sum_le hSval
    have hsum : L.sum + S.sum ≤ n := by omega
    have hdec' := cycleTypeWeight_add_eq n L S hdisj hL2 hS2 hsum
    have hcount_ge : (1 : ℝ) ≤ (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) := by
      exact Finset.one_le_prod (fun d hd => by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos _)))
    have hLprod_nonneg : 0 ≤ (L.prod : ℝ) := Nat.cast_nonneg _
    have hle : (1 : ℝ) / ((L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ))) ≤
        1 / (L.prod : ℝ) := by
      have hprod_ge : (L.prod : ℝ) ≤ (L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)) := by
        simpa [mul_comm] using (mul_le_mul_of_nonneg_left hcount_ge hLprod_nonneg)
      exact one_div_le_one_div_of_le hLprod_pos hprod_ge
    have hw_nonneg : 0 ≤ cycleTypeWeight (n - L.sum) S := by
      unfold cycleTypeWeight
      positivity
    calc cycleTypeWeight n (L + S)
        = (1 / ((L.prod : ℝ) * (∏ d ∈ L.toFinset, (Nat.factorial (L.count d) : ℝ)))) *
            cycleTypeWeight (n - L.sum) S := hdec'
      _ ≤ (1 / (L.prod : ℝ)) * cycleTypeWeight (n - L.sum) S :=
            mul_le_mul_of_nonneg_right hle hw_nonneg
  have hsum_le : (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
      cycleTypeWeight n (L + S)) ≤
      (1 / (L.prod : ℝ)) * (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
        cycleTypeWeight (n - L.sum) S) := by
    calc (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
          cycleTypeWeight n (L + S))
        ≤ ∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
            (1 / (L.prod : ℝ)) * cycleTypeWeight (n - L.sum) S := by
              exact Finset.sum_le_sum (fun S hS => hdec S hS)
      _ = (1 / (L.prod : ℝ)) * (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
            cycleTypeWeight (n - L.sum) S) := by rw [Finset.mul_sum]
  have hsum_all_le : (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
      cycleTypeWeight (n - L.sum) S) ≤ nuNoLong (n - L.sum) r := by
    have hsub : (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
        cycleTypeWeight (n - L.sum) S) ≤
        ∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => ∀ d ∈ S, d ≤ r), cycleTypeWeight (n - L.sum) S := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro S hS
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2.2⟩
      · intro S hS hnot
        unfold cycleTypeWeight
        positivity
    simpa [nuNoLong] using hsub
  have hnonneg : 0 ≤ 1 / (L.prod : ℝ) := by positivity
  calc (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
        cycleTypeWeight n (L + S))
      ≤ (1 / (L.prod : ℝ)) * (∑ S ∈ (cycleTypes (n - L.sum)).filter (fun S => Disjoint L.toFinset S.toFinset ∧ ∀ d ∈ S, d ≤ r),
          cycleTypeWeight (n - L.sum) S) := hsum_le
    _ ≤ (1 / (L.prod : ℝ)) * nuNoLong (n - L.sum) r := mul_le_mul_of_nonneg_left hsum_all_le hnonneg

open Classical

noncomputable def largeDivs (n k : ℕ) : Finset ℕ :=
  ((n - k).divisors).filter (fun d => d < n - k ∧ large n d)

lemma largeDivs_card_le_tau (n k : ℕ) : (largeDivs n k).card ≤ tau (n - k) := by
  unfold largeDivs tau
  exact Finset.card_filter_le _ _

lemma mem_largeDivs_dvd {n k d : ℕ} (h : d ∈ largeDivs n k) : d ∣ n - k := by
  unfold largeDivs at h
  exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp h).1

lemma mem_largeDivs_lt {n k d : ℕ} (h : d ∈ largeDivs n k) : d < n - k := by
  unfold largeDivs at h
  exact (Finset.mem_filter.mp h).2.1

lemma mem_largeDivs_large {n k d : ℕ} (h : d ∈ largeDivs n k) : large n d := by
  unfold largeDivs at h
  exact (Finset.mem_filter.mp h).2.2

lemma not_large_le_ceil (n d : ℕ) (h : ¬ large n d) :
    d ≤ ⌈(n : ℝ)^(13/14 : ℝ)⌉₊ := by
  unfold large at h
  have hlt : (d : ℝ) < (n : ℝ)^(13/14 : ℝ) := lt_of_not_ge h
  have hceil : (n : ℝ)^(13/14 : ℝ) ≤ (⌈(n : ℝ)^(13/14 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hlt2 : (d : ℝ) < (⌈(n : ℝ)^(13/14 : ℝ)⌉₊ : ℝ) := lt_of_lt_of_le hlt hceil
  have hd_lt : d < ⌈(n : ℝ)^(13/14 : ℝ)⌉₊ := by
    exact_mod_cast hlt2
  omega

lemma proper_divisor_le_half {m d : ℕ} (hd : d ∣ m) (hdlt : d < m) : d ≤ m / 2 := by
  rcases hd with ⟨a, rfl⟩
  have ha : 2 ≤ a := by
    by_contra ha'
    have hle : a ≤ 1 := by omega
    have hmul : d * a ≤ d := by
      have h : d * a ≤ d * 1 := Nat.mul_le_mul_left d hle
      simpa using h
    exact (Nat.not_lt_of_ge hmul) hdlt
  have hmul : d * 2 ≤ d * a := Nat.mul_le_mul_left d ha
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  exact hmul

lemma divisor_lt_half_le_third {m d : ℕ} (hd : d ∣ m) (hdlt : d < m / 2) : d ≤ m / 3 := by
  rcases hd with ⟨a, rfl⟩
  have ha : 3 ≤ a := by
    by_contra ha'
    have hle : a ≤ 2 := by omega
    have hmul : d * a ≤ d * 2 := Nat.mul_le_mul_left d hle
    have hdiv : d * a / 2 ≤ d := by
      exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)
    have h' : d < d * a / 2 := by simpa using hdlt
    exact (Nat.not_lt_of_ge hdiv) h'
  have hmul : 3 * d ≤ d * a := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left d ha)
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
  simpa [Nat.mul_comm] using hmul

lemma divisor_gt_third_eq_two_mul {m d : ℕ} (hd : d ∣ m) (hdlt : d < m) (hgt : m / 3 < d) : m = 2 * d := by
  rcases hd with ⟨a, rfl⟩
  have ha2 : 2 ≤ a := by
    by_contra ha'
    have hle : a ≤ 1 := by omega
    have hmul : d * a ≤ d := by
      have h : d * a ≤ d * 1 := Nat.mul_le_mul_left d hle
      simpa using h
    exact (Nat.not_lt_of_ge hmul) hdlt
  have ha_lt3 : a < 3 := by
    have hgt' : d * a / 3 < d := by simpa using hgt
    have hlt : d * a < d * 3 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp hgt'
    exact Nat.lt_of_mul_lt_mul_left hlt
  have ha : a = 2 := by omega
  subst a
  ring

lemma six_mul_add_le_five_mul {m d₁ d₂ : ℕ} (h₁ : d₁ ∣ m) (h₂ : d₂ ∣ m)
    (hd₁ : d₁ < m) (hd₂ : d₂ < m) (hsum : d₁ + d₂ < m) :
    6 * (d₁ + d₂) ≤ 5 * m := by
  have hd1_le_half : d₁ ≤ m / 2 := proper_divisor_le_half h₁ hd₁
  have hd2_le_half : d₂ ≤ m / 2 := proper_divisor_le_half h₂ hd₂
  by_cases hd1_le_third : d₁ ≤ m / 3
  · have hsum_le : d₁ + d₂ ≤ m / 3 + m / 2 := add_le_add hd1_le_third hd2_le_half
    have hkey : 6 * (m / 3 + m / 2) ≤ 5 * m := by omega
    exact le_trans (Nat.mul_le_mul_left 6 hsum_le) hkey
  · have hd1_gt_third : m / 3 < d₁ := Nat.lt_of_not_ge hd1_le_third
    have h2d1 : m = 2 * d₁ := divisor_gt_third_eq_two_mul h₁ hd₁ hd1_gt_third
    have hd2_lt_half : d₂ < m / 2 := by
      have h : d₂ < m - d₁ := by omega
      rw [h2d1] at h
      have h' : d₂ < d₁ := by omega
      rw [h2d1, Nat.mul_div_right d₁ (by norm_num : 0 < 2)]
      exact h'
    have hd2_le_third : d₂ ≤ m / 3 := divisor_lt_half_le_third h₂ hd2_lt_half
    have hd1_eq : d₁ = m / 2 := by
      rw [h2d1, Nat.mul_div_right d₁ (by norm_num : 0 < 2)]
    have hsum_le : d₁ + d₂ ≤ m / 2 + m / 3 := by
      rw [hd1_eq]
      exact add_le_add le_rfl hd2_le_third
    have hkey : 6 * (m / 2 + m / 3) ≤ 5 * m := by omega
    exact le_trans (Nat.mul_le_mul_left 6 hsum_le) hkey

/-- The T₀ term (no large cycle) is bounded by `ν(n, ⌈n^{13/14}⌉)`. -/
lemma sum_cycleTypeWeight_no_large_le_nu (n : ℕ) :
    (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0),
      cycleTypeWeight n lam) ≤ nuNoLong n (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) := by
  let r : ℕ := ⌈(n : ℝ)^(13/14 : ℝ)⌉₊
  have hsub : (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0) ⊆
      (cycleTypes n).filter (fun lam => ∀ d ∈ lam, d ≤ r) := by
    intro lam hlam
    rw [Finset.mem_filter]
    have hcard : (lam.filter (large n)).card = 0 := (Finset.mem_filter.mp hlam).2
    have hno_large : ∀ d ∈ lam, ¬ large n d := by
      intro d hd
      intro hlarge
      have hmem : d ∈ lam.filter (large n) := by
        rw [Multiset.mem_filter]; exact ⟨hd, hlarge⟩
      have hpos : 0 < (lam.filter (large n)).card := by
        have hcount : 0 < (lam.filter (large n)).count d := Multiset.count_pos.mpr hmem
        exact lt_of_lt_of_le hcount (Multiset.count_le_card d (lam.filter (large n)))
      omega
    have hle : ∀ d ∈ lam, d ≤ r := by
      intro d hd
      dsimp [r]
      exact not_large_le_ceil n d (hno_large d hd)
    exact ⟨(Finset.mem_filter.mp hlam).1, hle⟩
  have hle1 : (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0),
      cycleTypeWeight n lam) ≤
      ∑ lam ∈ (cycleTypes n).filter (fun lam => ∀ d ∈ lam, d ≤ r), cycleTypeWeight n lam := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro lam hlam hnot
    unfold cycleTypeWeight
    positivity
  calc (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0),
        cycleTypeWeight n lam)
      ≤ ∑ lam ∈ (cycleTypes n).filter (fun lam => ∀ d ∈ lam, d ≤ r), cycleTypeWeight n lam := hle1
    _ = nuNoLong n (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) := by
        simp [nuNoLong, r]

lemma cycleTypeWeight_cons_le (n d : ℕ) (S : Multiset ℕ) (hd2 : 2 ≤ d) (hS2 : ∀ x ∈ S, 2 ≤ x) (hsum : d + S.sum ≤ n) :
    cycleTypeWeight n (d ::ₘ S) ≤ (1 / (d : ℝ)) * cycleTypeWeight (n - d) S := by
  unfold cycleTypeWeight
  rw [Multiset.sum_cons, Multiset.prod_cons, Nat.cast_mul]
  rw [show n - (d + S.sum) = (n - d) - S.sum by omega]
  have hprod_le : (∏ x ∈ S.toFinset, (Nat.factorial (Multiset.count x S) : ℝ)) ≤
      (∏ x ∈ (d ::ₘ S).toFinset, (Nat.factorial (Multiset.count x (d ::ₘ S)) : ℝ)) := by
    have hstep1 : (∏ x ∈ S.toFinset, (Nat.factorial (Multiset.count x S) : ℝ)) ≤
        (∏ x ∈ S.toFinset, (Nat.factorial (Multiset.count x (d ::ₘ S)) : ℝ)) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro x hx; positivity
      · intro x hx
        exact_mod_cast (Nat.factorial_le (by
          rw [Multiset.count_cons]
          exact Nat.le_add_right _ _))
    have hstep2 : (∏ x ∈ S.toFinset, (Nat.factorial (Multiset.count x (d ::ₘ S)) : ℝ)) ≤
        (∏ x ∈ (d ::ₘ S).toFinset, (Nat.factorial (Multiset.count x (d ::ₘ S)) : ℝ)) := by
      rw [Multiset.toFinset_cons]
      refine Finset.prod_le_prod_of_subset_of_one_le ?_ ?_ ?_
      · intro x hx
        exact Finset.mem_insert.mpr (Or.inr hx)
      · intro x hx
        positivity
      · intro x hx hxnot
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos _))
    exact le_trans hstep1 hstep2
  rw [one_div_mul_one_div]
  refine one_div_le_one_div_of_le ?_ ?_
  · have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hSprod : 0 < (S.prod : ℝ) := by
      exact_mod_cast (Multiset.prod_pos (fun x hx => Nat.succ_le_iff.mp (by have := hS2 x hx; omega)))
    positivity
  · have hnonneg : 0 ≤ (d : ℝ) * ((Nat.factorial ((n - d) - S.sum) : ℝ)) * (S.prod : ℝ) := by positivity
    have h1 : (d : ℝ) * ((Nat.factorial ((n - d) - S.sum) : ℝ)) * (S.prod : ℝ) *
        (∏ x ∈ S.toFinset, (Nat.factorial (Multiset.count x S) : ℝ)) ≤
        (d : ℝ) * ((Nat.factorial ((n - d) - S.sum) : ℝ)) * (S.prod : ℝ) *
        (∏ x ∈ (d ::ₘ S).toFinset, (Nat.factorial (Multiset.count x (d ::ₘ S)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod_le hnonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1

lemma sum_cycleTypeWeight_cons_le_nu (n d r : ℕ) (hd2 : 2 ≤ d) (hd_le : d ≤ n) :
    (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight n (d ::ₘ S)) ≤
      (1 / (d : ℝ)) * nuNoLong (n - d) r := by
  have hdec : ∀ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r),
      cycleTypeWeight n (d ::ₘ S) ≤ (1 / (d : ℝ)) * cycleTypeWeight (n - d) S := by
    intro S hS
    have hSval : S ∈ cycleTypes (n - d) := (Finset.mem_filter.mp hS).1
    have hS2 : ∀ x ∈ S, 2 ≤ x := mem_cycleTypes_two_le hSval
    have hSsum : S.sum ≤ n - d := mem_cycleTypes_sum_le hSval
    have hsum : d + S.sum ≤ n := by omega
    exact cycleTypeWeight_cons_le n d S hd2 hS2 hsum
  have hsum_le : (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight n (d ::ₘ S)) ≤
      (1 / (d : ℝ)) * (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight (n - d) S) := by
    calc (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight n (d ::ₘ S))
        ≤ ∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), (1 / (d : ℝ)) * cycleTypeWeight (n - d) S :=
            Finset.sum_le_sum (fun S hS => hdec S hS)
      _ = (1 / (d : ℝ)) * (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight (n - d) S) := by rw [Finset.mul_sum]
  calc (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight n (d ::ₘ S))
      ≤ (1 / (d : ℝ)) * (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight (n - d) S) := hsum_le
    _ = (1 / (d : ℝ)) * nuNoLong (n - d) r := by rw [show (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight (n - d) S) = nuNoLong (n - d) r by rfl]

/-- The unique large cycle of `lam` (when it has exactly one). -/
noncomputable def uniqueLarge (n : ℕ) (lam : Multiset ℕ) : ℕ :=
  if h : (lam.filter (large n)).card = 1 then Classical.choose (Multiset.card_eq_one.mp h) else 0

lemma uniqueLarge_filter_eq {n : ℕ} {lam : Multiset ℕ} (h : (lam.filter (large n)).card = 1) :
    lam.filter (large n) = {uniqueLarge n lam} := by
  unfold uniqueLarge
  rw [dif_pos h]
  exact Classical.choose_spec (Multiset.card_eq_one.mp h)

lemma uniqueLarge_mem {n : ℕ} {lam : Multiset ℕ} (h : (lam.filter (large n)).card = 1) :
    uniqueLarge n lam ∈ lam := by
  have hmem : uniqueLarge n lam ∈ lam.filter (large n) := by
    rw [uniqueLarge_filter_eq h]; simp
  exact (Multiset.mem_filter.mp hmem).1

lemma uniqueLarge_large {n : ℕ} {lam : Multiset ℕ} (h : (lam.filter (large n)).card = 1) :
    large n (uniqueLarge n lam) := by
  have hmem : uniqueLarge n lam ∈ lam.filter (large n) := by
    rw [uniqueLarge_filter_eq h]; simp
  exact (Multiset.mem_filter.mp hmem).2

/-- The T₁ term (exactly one large cycle) is bounded by `∑_d (1/d)·ν(n-d, r)`. -/
lemma sum_cycleTypeWeight_one_large_le (n k : ℕ) (hn : 3 ≤ n) (hk : k < n) :
    (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1),
      cycleTypeWeight n lam) ≤
    ∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * nuNoLong (n - d) (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) := by
  let r : ℕ := ⌈(n : ℝ)^(13/14 : ℝ)⌉₊
  let s : Finset (Multiset ℕ) := (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1)
  let t : Finset (Σ d : ℕ, Multiset ℕ) := (largeDivs n k).sigma (fun d => (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r))
  let f : Multiset ℕ → (Σ d : ℕ, Multiset ℕ) := fun lam => ⟨uniqueLarge n lam, lam.erase (uniqueLarge n lam)⟩
  let w' : (Σ d : ℕ, Multiset ℕ) → ℝ := fun p => cycleTypeWeight n (p.1 ::ₘ p.2)
  have hf_mem : ∀ lam ∈ s, f lam ∈ t := by
    intro lam hlam
    have hcond := (Finset.mem_filter.mp hlam).2
    have hlcm : lam.lcm = n - k := hcond.1
    have hnk : n - k ∉ lam := hcond.2.1
    have hcard : (lam.filter (large n)).card = 1 := hcond.2.2
    let d : ℕ := uniqueLarge n lam
    have hdlarge : large n d := by dsimp [d]; exact uniqueLarge_large hcard
    have hdmem : d ∈ lam := by dsimp [d]; exact uniqueLarge_mem hcard
    have hd_dvd : d ∣ n - k := dvd_trans (Multiset.dvd_lcm hdmem) (by rw [hlcm])
    have hd2 : 2 ≤ d := mem_cycleTypes_two_le (Finset.mem_filter.mp hlam).1 d hdmem
    have hd_lt : d < n - k := by
      by_contra hge
      have hn_sub_pos : 0 < n - k := by omega
      have hd_le : d ≤ n - k := Nat.le_of_dvd hn_sub_pos hd_dvd
      have hd_eq : d = n - k := by omega
      exact hnk (by rwa [← hd_eq])
    have hd_divs : d ∈ largeDivs n k := by
      unfold largeDivs
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨hd_dvd, by omega⟩, ⟨hd_lt, hdlarge⟩⟩
    have hS_val : lam.erase d ∈ cycleTypes (n - d) := by
      have hd_le_n : d ≤ n := by omega
      have hmem' : n - (n - d) ∈ lam := by
        rw [Nat.sub_sub_self hd_le_n]
        exact hdmem
      have hres := mem_cycleTypes_erase n (n - d) (Finset.mem_filter.mp hlam).1 hmem' (by omega)
      rw [Nat.sub_sub_self hd_le_n] at hres
      exact hres
    have hS_small : ∀ x ∈ lam.erase d, x ≤ r := by
      intro x hx
      have hxnot : ¬ large n x := by
        intro hlarge
        have hx_lam : x ∈ lam := Multiset.mem_of_mem_erase hx
        have hx_filter : x ∈ lam.filter (large n) := by rw [Multiset.mem_filter]; exact ⟨hx_lam, hlarge⟩
        have hfilter : lam.filter (large n) = {d} := by dsimp [d]; exact uniqueLarge_filter_eq hcard
        rw [hfilter] at hx_filter
        have hxd : x = d := by simpa using hx_filter
        have hd_erase : d ∈ lam.erase d := by simpa [hxd] using hx
        have hcount_lam : Multiset.count d lam = 1 := by
          have h := congrArg (Multiset.count d) hfilter
          have h' := (Multiset.count_filter_of_pos (s := lam) (p := large n) (a := d) hdlarge)
          rw [h'] at h
          simpa using h
        have hcount_erase : Multiset.count d (lam.erase d) = 0 := by
          rw [Multiset.count_erase_self, hcount_lam]
        have hcount_pos : 0 < Multiset.count d (lam.erase d) := Multiset.count_pos.mpr hd_erase
        omega
      dsimp [r]
      exact not_large_le_ceil n x hxnot
    rw [Finset.mem_sigma]
    exact ⟨hd_divs, by rw [Finset.mem_filter]; exact ⟨hS_val, hS_small⟩⟩
  have hf_inj : Set.InjOn f (↑s : Set (Multiset ℕ)) := by
    intro lam₁ hlam₁ lam₂ hlam₂ h
    have hcard₁ : (lam₁.filter (large n)).card = 1 := (Finset.mem_filter.mp hlam₁).2.2.2
    have hcard₂ : (lam₂.filter (large n)).card = 1 := (Finset.mem_filter.mp hlam₂).2.2.2
    dsimp [f] at h
    have hd_eq : uniqueLarge n lam₁ = uniqueLarge n lam₂ := congrArg (fun p : Σ d : ℕ, Multiset ℕ => p.1) h
    have hS_eq : lam₁.erase (uniqueLarge n lam₁) = lam₂.erase (uniqueLarge n lam₂) := congrArg (fun p : Σ d : ℕ, Multiset ℕ => p.2) h
    have hmem₁ : uniqueLarge n lam₁ ∈ lam₁ := uniqueLarge_mem hcard₁
    have hmem₂ : uniqueLarge n lam₂ ∈ lam₂ := uniqueLarge_mem hcard₂
    calc lam₁ = uniqueLarge n lam₁ ::ₘ (lam₁.erase (uniqueLarge n lam₁)) := (Multiset.cons_erase hmem₁).symm
      _ = uniqueLarge n lam₂ ::ₘ (lam₂.erase (uniqueLarge n lam₂)) := by
            rw [hd_eq]
            simpa [hd_eq] using hS_eq
      _ = lam₂ := Multiset.cons_erase hmem₂
  have hw_eq : ∀ lam ∈ s, cycleTypeWeight n lam = w' (f lam) := by
    intro lam hlam
    have hcard : (lam.filter (large n)).card = 1 := (Finset.mem_filter.mp hlam).2.2.2
    have hmem : uniqueLarge n lam ∈ lam := uniqueLarge_mem hcard
    dsimp [w', f]
    rw [Multiset.cons_erase hmem]
  have hsum_image : (∑ p ∈ s.image f, w' p) = ∑ lam ∈ s, cycleTypeWeight n lam := by
    rw [Finset.sum_image hf_inj]
    apply Finset.sum_congr rfl
    intro lam hlam
    exact (hw_eq lam hlam).symm
  have himage_subset : s.image f ⊆ t := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨lam, hlam, rfl⟩
    exact hf_mem lam hlam
  have hstep : ∑ lam ∈ s, cycleTypeWeight n lam ≤ ∑ p ∈ t, w' p := by
    rw [← hsum_image]
    refine Finset.sum_le_sum_of_subset_of_nonneg himage_subset ?_
    intro p hp hnot
    unfold w' cycleTypeWeight
    positivity
  have hsum_sigma : (∑ p ∈ t, w' p) = ∑ d ∈ largeDivs n k, ∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight n (d ::ₘ S) := by
    rw [Finset.sum_sigma]
  have hdec : ∀ d ∈ largeDivs n k,
      (∑ S ∈ (cycleTypes (n - d)).filter (fun S => ∀ x ∈ S, x ≤ r), cycleTypeWeight n (d ::ₘ S)) ≤
        (1 / (d : ℝ)) * nuNoLong (n - d) r := by
    intro d hd
    have hd2 : 2 ≤ d := by
      have hlarge : large n d := mem_largeDivs_large hd
      unfold large at hlarge
      have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h3pow_gt1 : (1 : ℝ) < (3 : ℝ)^(13/14 : ℝ) := by
        have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < (3 : ℝ))
          (by norm_num : (0 : ℝ) < (13/14 : ℝ))
        simpa [Real.one_rpow] using h
      have hnpow_gt1 : (1 : ℝ) < (n : ℝ)^(13/14 : ℝ) := by
        exact lt_of_lt_of_le h3pow_gt1 (Real.rpow_le_rpow (by norm_num : 0 ≤ (3:ℝ)) hnR
          (by norm_num : 0 ≤ (13/14:ℝ)))
      have hd_gt1 : (1 : ℝ) < (d : ℝ) := lt_of_lt_of_le hnpow_gt1 hlarge
      have hd_pos : 0 < d := by
        have : (0 : ℝ) < (d : ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hd_gt1
        exact_mod_cast this
      have hd_ne1 : d ≠ 1 := by
        intro h
        have : (d : ℝ) = 1 := by
          rw [h]
          norm_num
        linarith
      omega
    have hd_le_n : d ≤ n := by
      have hd_lt : d < n - k := mem_largeDivs_lt hd
      omega
    exact sum_cycleTypeWeight_cons_le_nu n d r hd2 hd_le_n
  have hfinal : (∑ p ∈ t, w' p) ≤ ∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * nuNoLong (n - d) r := by
    rw [hsum_sigma]
    refine Finset.sum_le_sum ?_
    intro d hd
    exact hdec d hd
  calc (∑ lam ∈ s, cycleTypeWeight n lam)
      ≤ ∑ p ∈ t, w' p := hstep
    _ ≤ ∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * nuNoLong (n - d) r := hfinal

/-- `p^t ∣ lcm a b ↔ p^t ∣ a ∨ p^t ∣ b` for a prime `p` (both nonzero). -/
lemma pow_dvd_lcm_iff (p a b t : ℕ) [Fact (Nat.Prime p)] (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ t ∣ a.lcm b ↔ p ^ t ∣ a ∨ p ^ t ∣ b := by
  have hlab_ne : a.lcm b ≠ 0 := Nat.lcm_ne_zero ha hb
  have h1 : p ^ t ∣ a.lcm b ↔ t ≤ padicValNat p (a.lcm b) :=
    padicValNat_dvd_iff_le (p := p) (a := a.lcm b) (n := t) hlab_ne
  have h2 : p ^ t ∣ a ↔ t ≤ padicValNat p a :=
    padicValNat_dvd_iff_le (p := p) (a := a) (n := t) ha
  have h3 : p ^ t ∣ b ↔ t ≤ padicValNat p b :=
    padicValNat_dvd_iff_le (p := p) (a := b) (n := t) hb
  rw [h1, h2, h3]
  have hval : padicValNat p (a.lcm b) = max (padicValNat p a) (padicValNat p b) := by
    have hp : Nat.Prime p := (inferInstance : Fact (Nat.Prime p)).out
    calc padicValNat p (a.lcm b) = (a.lcm b).factorization p := (Nat.factorization_def _ hp).symm
      _ = (a.factorization ⊔ b.factorization) p := by rw [Nat.factorization_lcm ha hb]
      _ = a.factorization p ⊔ b.factorization p := Finsupp.sup_apply _ _ _
      _ = max (padicValNat p a) (padicValNat p b) := by
          rw [Nat.factorization_def a hp, Nat.factorization_def b hp]
  rw [hval]
  exact le_max_iff

/-- If `2^t ∣ s.lcm` (with `t ≥ 1` and all elements nonzero), some element of `s` is
divisible by `2^t`. -/
lemma exists_dvd_of_dvd_lcm_two_pow {s : Multiset ℕ} (hs : ∀ d ∈ s, d ≠ 0) :
    ∀ {t : ℕ}, 1 ≤ t → 2 ^ t ∣ s.lcm → ∃ d ∈ s, 2 ^ t ∣ d := by
  intro t ht hdvd
  induction s using Multiset.induction_on with
  | empty =>
      have hpow_ge : 2 ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) ht
      have hle1 : 2 ^ t ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hdvd
      omega
  | cons a s ih =>
      by_cases ha0 : a = 0
      · exfalso
        exact hs a (by simp) ha0
      · have hs' : ∀ d ∈ s, d ≠ 0 := by
          intro d hd
          exact hs d (by simp [hd])
        have hslcm_ne : s.lcm ≠ 0 := by
          intro h0
          rw [Multiset.lcm_eq_zero_iff] at h0
          exact (hs' 0 h0) rfl
        have hlab : 2 ^ t ∣ Nat.lcm a s.lcm := by
          simpa [Multiset.lcm_cons] using hdvd
        have hcases := (pow_dvd_lcm_iff (2 : ℕ) a s.lcm t ha0 hslcm_ne).mp hlab
        rcases hcases with (ha_dvd | hs_dvd)
        · exact ⟨a, by simp, ha_dvd⟩
        · rcases ih hs' hs_dvd with ⟨d, hd, hddvd⟩
          exact ⟨d, by simp [hd], hddvd⟩

/-- In the interesting case (`k ∈ Kₙ`, `2^⌊log₂ k⌋+1 ∤ n-k`), `lcm((n-k)/2, μ.lcm) = n-k`
forces `2^⌊log₂ k⌋ ∈ μ`. -/
lemma mem_two_pow_log2_of_lcm_eq_two_mul (n k : ℕ) (hk : k ∈ K n) (hk2 : 2 ≤ k)
    (hdiv : 2 ∣ n - k) (hnot : ¬ 2 ^ (Nat.log 2 k + 1) ∣ n - k) {μ : Multiset ℕ}
    (hμ : μ ∈ cycleTypes k) :
    Nat.lcm ((n - k) / 2) μ.lcm = n - k → 2 ^ Nat.log 2 k ∈ μ := by
  intro hlcm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk_lt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hnk_pos : n - k ≠ 0 := by omega
  have hge2 : 2 ≤ n - k := by
    have hd := two_pow_log2_dvd_of_mem_K hk hk2
    have hs : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) (by omega : 2 ≤ k)
    have hpow : 2 ≤ 2 ^ Nat.log 2 k := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hs
    exact le_trans hpow (Nat.le_of_dvd (by omega : 0 < n - k) hd)
  have ha_pos : (n - k) / 2 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos hge2 (by norm_num : 0 < (2 : ℕ)))
  have hμ_ne : ∀ d ∈ μ, d ≠ 0 := by
    intro d hd
    have hd2 : 2 ≤ d := mem_cycleTypes_two_le hμ d hd
    omega
  have hμ_lcm_ne : μ.lcm ≠ 0 := by
    intro h0
    rw [Multiset.lcm_eq_zero_iff] at h0
    exact (hμ_ne 0 h0) rfl
  have hs : padicValNat 2 (n - k) = Nat.log 2 k :=
    padicValNat_nk_eq_log2_of_not_two_pow_succ_dvd hk hk2 hnot
  have hva : padicValNat 2 ((n - k) / 2) = Nat.log 2 k - 1 := by
    rw [padicValNat.div (p := 2) hdiv, hs]
  have hvlcm : padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm) = Nat.log 2 k := by
    rw [hlcm, hs]
  have hfac : padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm) =
      max (padicValNat 2 ((n - k) / 2)) (padicValNat 2 μ.lcm) := by
    have hp : Nat.Prime 2 := Nat.prime_two
    calc padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm)
        = (Nat.lcm ((n - k) / 2) μ.lcm).factorization 2 := (Nat.factorization_def _ hp).symm
      _ = (((n - k) / 2).factorization ⊔ μ.lcm.factorization) 2 := by
          rw [Nat.factorization_lcm ha_pos hμ_lcm_ne]
      _ = ((n - k) / 2).factorization 2 ⊔ μ.lcm.factorization 2 := Finsupp.sup_apply _ _ _
      _ = max (padicValNat 2 ((n - k) / 2)) (padicValNat 2 μ.lcm) := by
          rw [Nat.factorization_def ((n-k)/2) hp, Nat.factorization_def μ.lcm hp]
  have hmax : max (Nat.log 2 k - 1) (padicValNat 2 μ.lcm) = Nat.log 2 k := by
    rw [hva] at hfac
    rw [← hfac, hvlcm]
  have hvμ : padicValNat 2 μ.lcm = Nat.log 2 k := by omega
  have hdvd : 2 ^ Nat.log 2 k ∣ μ.lcm := by
    rw [padicValNat_dvd_iff_le (p := 2) hμ_lcm_ne]
    rw [hvμ]
  have ht : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) (by omega : 2 ≤ k)
  rcases exists_dvd_of_dvd_lcm_two_pow hμ_ne ht hdvd with ⟨d, hdmem, hddvd⟩
  have hd2 : 2 ≤ d := mem_cycleTypes_two_le hμ d hdmem
  have hd_le_sum : d ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) d hdmem
  have hd_le_k : d ≤ k := le_trans hd_le_sum (mem_cycleTypes_sum_le hμ)
  have hle : 2 ^ Nat.log 2 k ≤ d := Nat.le_of_dvd (by positivity) hddvd
  have hlt : d < 2 ^ (Nat.log 2 k + 1) := by
    calc d ≤ k := hd_le_k
      _ < 2 ^ (Nat.log 2 k).succ := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) k
      _ = 2 ^ (Nat.log 2 k + 1) := by rw [Nat.succ_eq_add_one]
  have hd_eq : d = 2 ^ Nat.log 2 k := by
    rcases hddvd with ⟨c, hc⟩
    rw [hc] at hle hlt
    have hpowpos : 0 < 2 ^ Nat.log 2 k := pow_pos (by norm_num) _
    have hc_ge1 : 1 ≤ c := by
      have hle' : 2 ^ Nat.log 2 k * 1 ≤ 2 ^ Nat.log 2 k * c := by
        simpa [one_mul, Nat.mul_comm] using hle
      exact Nat.le_of_mul_le_mul_left hle' hpowpos
    have hc_lt : c < 2 := by
      have hlt' : 2 ^ Nat.log 2 k * c < 2 ^ Nat.log 2 k * 2 := by
        simpa [show 2 ^ (Nat.log 2 k + 1) = 2 ^ Nat.log 2 k * 2 by rw [pow_succ]] using hlt
      exact Nat.lt_of_mul_lt_mul_left hlt'
    have hc_eq : c = 1 := Nat.eq_of_le_of_lt_succ hc_ge1 hc_lt
    subst c
    simpa using hc
  rwa [← hd_eq]


/-- In the trivial case `2^{⌊log₂ k⌋+1} ∣ n-k`, no `μ ∈ cycleTypes k` satisfies
`lcm((n-k)/2, μ.lcm) = n-k` (2-adic valuations cannot match). -/
lemma no_special_of_dvd_two_pow_succ (n k : ℕ) (hk2 : 2 ≤ k) (hdiv : 2 ∣ n - k)
    (hk_lt_n : k < n) (hdvd : 2 ^ (Nat.log 2 k + 1) ∣ n - k) {μ : Multiset ℕ}
    (hμ : μ ∈ cycleTypes k) :
    Nat.lcm ((n - k) / 2) μ.lcm ≠ n - k := by
  intro hlcm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnk_pos : n - k ≠ 0 := by omega
  have ha_pos : (n - k) / 2 ≠ 0 := by
    have hge2 : 2 ≤ n - k := by
      have hdvd' : 2 ∣ n - k := dvd_trans (by norm_num : (2 : ℕ) ∣ 2 ^ (Nat.log 2 k + 1)) hdvd
      exact Nat.le_of_dvd (by omega : 0 < n - k) hdvd'
    exact Nat.ne_of_gt (Nat.div_pos hge2 (by norm_num : 0 < (2 : ℕ)))
  have hμ_ne : ∀ d ∈ μ, d ≠ 0 := by
    intro d hd
    have hd2 : 2 ≤ d := mem_cycleTypes_two_le hμ d hd
    omega
  have hμ_lcm_ne : μ.lcm ≠ 0 := by
    intro h0
    rw [Multiset.lcm_eq_zero_iff] at h0
    exact (hμ_ne 0 h0) rfl
  have hs_ge : Nat.log 2 k + 1 ≤ padicValNat 2 (n - k) :=
    (padicValNat_dvd_iff_le (p := 2) (a := n - k) (n := Nat.log 2 k + 1) hnk_pos).mp hdvd
  have hva : padicValNat 2 ((n - k) / 2) = padicValNat 2 (n - k) - 1 :=
    padicValNat.div (p := 2) hdiv
  have hvμ_le : padicValNat 2 μ.lcm ≤ Nat.log 2 k := by
    by_contra h
    have hge : Nat.log 2 k + 1 ≤ padicValNat 2 μ.lcm := by omega
    have hdvdμ : 2 ^ (Nat.log 2 k + 1) ∣ μ.lcm :=
      (padicValNat_dvd_iff_le (p := 2) (a := μ.lcm) (n := Nat.log 2 k + 1) hμ_lcm_ne).mpr hge
    have ht : 1 ≤ Nat.log 2 k + 1 := by omega
    rcases exists_dvd_of_dvd_lcm_two_pow hμ_ne ht hdvdμ with ⟨d, hdmem, hddvd⟩
    have hd2 : 2 ≤ d := mem_cycleTypes_two_le hμ d hdmem
    have hd_le_sum : d ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) d hdmem
    have hd_le_k : d ≤ k := le_trans hd_le_sum (mem_cycleTypes_sum_le hμ)
    have hle : 2 ^ (Nat.log 2 k + 1) ≤ d := Nat.le_of_dvd (by positivity) hddvd
    have hlt : k < 2 ^ (Nat.log 2 k + 1) := by
      calc k < 2 ^ (Nat.log 2 k).succ := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) k
        _ = 2 ^ (Nat.log 2 k + 1) := by rw [Nat.succ_eq_add_one]
    omega
  have hfac : padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm) =
      max (padicValNat 2 ((n - k) / 2)) (padicValNat 2 μ.lcm) := by
    have hp : Nat.Prime 2 := Nat.prime_two
    calc padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm)
        = (Nat.lcm ((n - k) / 2) μ.lcm).factorization 2 := (Nat.factorization_def _ hp).symm
      _ = (((n - k) / 2).factorization ⊔ μ.lcm.factorization) 2 := by
          rw [Nat.factorization_lcm ha_pos hμ_lcm_ne]
      _ = ((n - k) / 2).factorization 2 ⊔ μ.lcm.factorization 2 := Finsupp.sup_apply _ _ _
      _ = max (padicValNat 2 ((n - k) / 2)) (padicValNat 2 μ.lcm) := by
          rw [Nat.factorization_def ((n-k)/2) hp, Nat.factorization_def μ.lcm hp]
  have hval_eq : padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm) = padicValNat 2 ((n - k) / 2) := by
    rw [hfac]
    have hge2 : Nat.log 2 k ≤ padicValNat 2 ((n - k) / 2) := by
      rw [hva]
      omega
    omega
  have hcontra : padicValNat 2 (n - k) = padicValNat 2 ((n - k) / 2) := by
    calc padicValNat 2 (n - k) = padicValNat 2 (Nat.lcm ((n - k) / 2) μ.lcm) := by rw [hlcm]
      _ = padicValNat 2 ((n - k) / 2) := hval_eq
  rw [hva] at hcontra
  have hnk_val_pos : 1 ≤ padicValNat 2 (n - k) := by
    exact (padicValNat_dvd_iff_le (p := 2) (a := n - k) (n := 1) hnk_pos).mp (by
      have : (2 : ℕ) ∣ n - k := dvd_trans (by norm_num : (2 : ℕ) ∣ 2 ^ (Nat.log 2 k + 1)) hdvd
      simpa using this)
  omega

/-- In the case `k ≤ 1`, the special sum is also empty (lcm cannot double). -/
lemma no_special_of_le_one (n k : ℕ) (hdiv : 2 ∣ n - k) (ha2 : 2 ≤ (n - k) / 2)
    (hk : k ≤ 1) {μ : Multiset ℕ} (hμ : μ ∈ cycleTypes k) :
    Nat.lcm ((n - k) / 2) μ.lcm ≠ n - k := by
  intro hlcm
  have hμ0 : μ = 0 := by
    ext d
    by_cases hdmem : d ∈ μ
    · have hd2 : 2 ≤ d := mem_cycleTypes_two_le hμ d hdmem
      have hd_le_sum : d ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) d hdmem
      have hd_le_k : d ≤ k := le_trans hd_le_sum (mem_cycleTypes_sum_le hμ)
      omega
    · simp [hdmem]
  rw [hμ0] at hlcm
  rw [Multiset.lcm_zero, Nat.lcm_one_right] at hlcm
  have hhalf_lt : (n - k) / 2 < n - k := by
    have h2 : 2 * ((n - k) / 2) = n - k := by
      have hc := Nat.div_mul_cancel hdiv
      simpa [Nat.mul_comm] using hc
    have hgt : (n - k) / 2 < 2 * ((n - k) / 2) := by
      have hpos : 0 < (n - k) / 2 := by omega
      nlinarith
    calc (n - k) / 2 < 2 * ((n - k) / 2) := hgt
      _ = n - k := h2
  exact (lt_irrefl ((n - k) / 2)) (by simpa [hlcm] using hhalf_lt)



/-- For `k ∈ Kₙ` with `n ≥ 10` in the interesting case, `k < (n-k)/2` (the gap needed for
the special-term decoupling). -/
lemma k_lt_half_of_mem_K {n k : ℕ} (hn10 : 10 ≤ n) (hk : k ∈ K n) (hk2 : 2 ≤ k)
    (hnot : ¬ 2 ^ (Nat.log 2 k + 1) ∣ n - k) : k < (n - k) / 2 := by
  have hk_lt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hlcm_dvd : lcm1to k ∣ n - k := (Finset.mem_filter.mp hk).2
  have hkpos : 0 < k := by omega
  have h2a : 2 * ((n - k) / 2) = n - k := by
    have h2dvd : 2 ∣ n - k := by
      have hs : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) (by omega : 2 ≤ k)
      have hpow_dvd : 2 ^ Nat.log 2 k ∣ n - k := two_pow_log2_dvd_of_mem_K hk hk2
      exact dvd_trans (pow_dvd_pow 2 hs) hpow_dvd
    have hc := Nat.div_mul_cancel h2dvd
    simpa [Nat.mul_comm] using hc
  by_cases hk_eq_two : k = 2
  · -- k = 2: s = 1, m = 2a, 4 ∤ m → a odd ≥ 3
    subst k
    have hm_even : 2 ∣ n - 2 := by
      have h2mem : 2 ∈ Finset.Icc 1 2 := by simp
      have h2dvd : 2 ∣ lcm1to 2 := by
        unfold lcm1to
        exact Finset.dvd_lcm h2mem
      exact dvd_trans h2dvd hlcm_dvd
    have hm_odd_a : (n - 2) / 2 % 2 = 1 := by
      have hnot4 : ¬ 4 ∣ n - 2 := by
        intro h
        apply hnot
        simpa [show Nat.log 2 2 + 1 = 2 by norm_num] using h
      rcases hm_even with ⟨q, hq⟩
      have hqodd : ¬ 2 ∣ q := by
        intro h
        rcases h with ⟨r, hr⟩
        apply hnot4
        use r
        rw [hq, hr]
        ring
      have hqa : q = (n - 2) / 2 := by
        rw [hq]
        rw [Nat.mul_div_right q (by norm_num : 0 < (2 : ℕ))]
      rw [← hqa]
      have hq_even_iff : Even q ↔ 2 ∣ q := even_iff_two_dvd
      have hq_odd : Odd q := Nat.not_even_iff_odd.mp (by simpa [hq_even_iff] using hqodd)
      exact (Nat.odd_iff.mp hq_odd)
    have ha_ge3 : 3 ≤ (n - 2) / 2 := by
      have ha_pos : 0 < (n - 2) / 2 := by
        have h2n : 2 ≤ n - 2 := by omega
        exact Nat.div_pos h2n (by norm_num : 0 < (2 : ℕ))
      have ha_odd : (n - 2) / 2 % 2 = 1 := hm_odd_a
      omega
    exact lt_of_lt_of_le (by norm_num : (2 : ℕ) < 3) ha_ge3
  · -- k ≥ 3
    have hk3 : 3 ≤ k := by omega
    have hkk1_dvd : k * (k - 1) ∣ n - k := by
      have hd : k * (k - 1) ∣ lcm1to k := by
        simpa [Nat.mul_comm] using (lcm1to_dvd_mul_pred_self (by omega : 2 ≤ k))
      exact dvd_trans hd hlcm_dvd
    have hkk1_le : k * (k - 1) ≤ n - k := Nat.le_of_dvd (by omega : 0 < n - k) hkk1_dvd
    have hkk1_le_2a : k * (k - 1) ≤ 2 * ((n - k) / 2) := by
      simpa [h2a] using hkk1_le
    have h2k_le_kk1 : 2 * k ≤ k * (k - 1) := by
      have : 2 ≤ k - 1 := by omega
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_left k this)
    have hk_le_a : k ≤ (n - k) / 2 := by
      have h : 2 * k ≤ 2 * ((n - k) / 2) := le_trans h2k_le_kk1 hkk1_le_2a
      exact Nat.le_of_mul_le_mul_left h (by norm_num : 0 < (2 : ℕ))
    -- k = a would force k = 3, m = 6, n = 9 < 10
    by_contra hnotlt
    have hk_eq_a : k = (n - k) / 2 := by omega
    have hkk1_le_2k : k * (k - 1) ≤ 2 * k := by
      calc k * (k - 1) ≤ 2 * ((n - k) / 2) := hkk1_le_2a
        _ = 2 * k := congrArg (fun x => 2 * x) hk_eq_a.symm
    have hk_le3 : k ≤ 3 := by
      have h : k - 1 ≤ 2 := by
        exact Nat.le_of_mul_le_mul_left (by
          simpa [Nat.mul_comm] using hkk1_le_2k) (by omega : 0 < k)
      omega
    have hk3' : k = 3 := by omega
    subst k
    have hn9 : n = 9 := by
      have h : 2 * ((n - 3) / 2) = n - 3 := by simpa using h2a
      rw [show (n - 3) / 2 = 3 by omega] at h
      omega
    omega

/-- The "special pair" configuration: the large cycles of `lam` are exactly two cycles of
length `(n-k)/2`. -/
def specialPair (n k : ℕ) (lam : Multiset ℕ) : Prop :=
  lam.filter (large n) = (n - k) / 2 ::ₘ (n - k) / 2 ::ₘ 0

lemma specialPair_card_two (n k : ℕ) {lam : Multiset ℕ} (h : specialPair n k lam) :
    (lam.filter (large n)).card = 2 := by
  rw [h]
  norm_num

lemma specialPair_mem_half {n k : ℕ} {lam : Multiset ℕ} (h : specialPair n k lam) :
    (n - k) / 2 ∈ lam := by
  have hmem : (n - k) / 2 ∈ lam.filter (large n) := by
    rw [h]
    simp
  exact (Multiset.mem_filter.mp hmem).1

/-- From a special pair, the second `a` survives in `lam.erase a`, and the remaining
multiset lies in `cycleTypes k`. -/
lemma mem_cycleTypes_erase_half_of_specialPair {n k : ℕ} {lam : Multiset ℕ}
    (hlam : lam ∈ cycleTypes n) (hpair : specialPair n k lam) (hdiv : 2 ∣ n - k) :
    (lam.erase ((n - k) / 2)).erase ((n - k) / 2) ∈ cycleTypes k := by
  let a := (n - k) / 2
  have ha_mem : a ∈ lam := by simpa [a] using (specialPair_mem_half hpair)
  have h2a : 2 * a = n - k := by
    dsimp [a]
    have hc := Nat.div_mul_cancel hdiv
    simpa [Nat.mul_comm] using hc
  have hlarge_a : large n a := by
    have hfilter : lam.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using hpair
    have hmem : a ∈ lam.filter (large n) := by
      rw [hfilter]
      simp
    exact (Multiset.mem_filter.mp hmem).2
  have ha_mem_erase : a ∈ lam.erase a := by
    have hfilter : lam.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using hpair
    have h := hfilter
    rw [← Multiset.cons_erase ha_mem] at h
    rw [Multiset.filter_cons_of_pos (s := lam.erase a) hlarge_a] at h
    have h' : a ::ₘ (lam.erase a).filter (large n) = a ::ₘ (a ::ₘ 0) := by simpa using h
    exact (Multiset.mem_filter.mp (by
      rw [(Multiset.cons_inj_right a).mp h']
      simp)).1
  have h1 := mem_cycleTypes_erase n (n - a) hlam (by
    rw [Nat.sub_sub_self (by omega : a ≤ n)]
    exact ha_mem) (by omega)
  have h2 := mem_cycleTypes_erase (n - a) (n - 2 * a) h1 (by
    have hsub1 : n - (n - a) = a := by omega
    have hsub : (n - a) - (n - 2 * a) = a := by omega
    rwa [hsub1, hsub]) (by omega)
  have h2' : (lam.erase a).erase a ∈ cycleTypes k := by
    have hsub1 : n - (n - a) = a := by omega
    have hsub2 : (n - a) - (n - 2 * a) = a := by omega
    have hk_le_n : k ≤ n := by
      have ha2' : 2 ≤ a := mem_cycleTypes_two_le hlam a ha_mem
      have hsum_le : a ≤ lam.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) a ha_mem
      have hlam_sum : lam.sum ≤ n := mem_cycleTypes_sum_le hlam
      omega
    have hk' : n - 2 * a = k := by
      calc n - 2 * a = n - (n - k) := by rw [h2a]
        _ = k := Nat.sub_sub_self hk_le_n
    rwa [hsub1, hsub2, hk'] at h2
  simpa [a] using h2'

/-- From a special pair, `lam.lcm = lcm(a, (lam.erase a .erase a).lcm)` where `a = (n-k)/2`. -/
lemma lcm_eq_of_specialPair {n k : ℕ} {lam : Multiset ℕ}
    (hpair : specialPair n k lam) :
    lam.lcm = Nat.lcm ((n - k) / 2) ((lam.erase ((n - k) / 2)).erase ((n - k) / 2)).lcm := by
  let a := (n - k) / 2
  have ha_mem : a ∈ lam := by simpa [a] using (specialPair_mem_half hpair)
  have hlarge_a : large n a := by
    have hfilter : lam.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using hpair
    have hmem : a ∈ lam.filter (large n) := by
      rw [hfilter]
      simp
    exact (Multiset.mem_filter.mp hmem).2
  have ha_mem_erase : a ∈ lam.erase a := by
    have hfilter : lam.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using hpair
    have h := hfilter
    rw [← Multiset.cons_erase ha_mem] at h
    rw [Multiset.filter_cons_of_pos (s := lam.erase a) hlarge_a] at h
    have h' : a ::ₘ (lam.erase a).filter (large n) = a ::ₘ (a ::ₘ 0) := by simpa using h
    exact (Multiset.mem_filter.mp (by
      rw [(Multiset.cons_inj_right a).mp h']
      simp)).1
  have hlam_eq : lam = a ::ₘ a ::ₘ ((lam.erase a).erase a) := by
    calc lam = a ::ₘ lam.erase a := (Multiset.cons_erase ha_mem).symm
      _ = a ::ₘ a ::ₘ ((lam.erase a).erase a) := by
          exact congrArg (fun x => a ::ₘ x) (Multiset.cons_erase ha_mem_erase).symm
  calc lam.lcm = (a ::ₘ a ::ₘ ((lam.erase a).erase a)).lcm :=
        congrArg Multiset.lcm hlam_eq
    _ = Nat.lcm a (Nat.lcm a ((lam.erase a).erase a).lcm) := by
          rw [Multiset.lcm_cons, Multiset.lcm_cons]
          rfl
    _ = Nat.lcm a ((lam.erase a).erase a).lcm := by
          rw [← Nat.lcm_assoc a a ((lam.erase a).erase a).lcm, Nat.lcm_self]
    _ = Nat.lcm ((n - k) / 2) ((lam.erase ((n - k) / 2)).erase ((n - k) / 2)).lcm := by
          dsimp [a]

/-- The sum over the special pair is bounded by `η` (equal to it in the interesting case,
zero in the trivial cases). -/
lemma sum_cycleTypeWeight_two_large_special_le (n k : ℕ) (hk : k ∈ K n) (hn10 : 10 ≤ n) :
    (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam),
      cycleTypeWeight n lam) ≤ eta n k := by
  classical
  by_cases hdiv : 2 ∣ n - k
  · by_cases hk2 : 2 ≤ k
    · by_cases hdvd : 2 ^ (Nat.log 2 k + 1) ∣ n - k
      · -- trivial case 2^{s+1} | n-k: filter empty
        have hempty : (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro lam hlam h
          rcases h with ⟨hlcm, hnk, hpair⟩
          have hμct := mem_cycleTypes_erase_half_of_specialPair hlam hpair hdiv
          have hlcm' : Nat.lcm ((n - k) / 2) ((lam.erase ((n - k) / 2)).erase ((n - k) / 2)).lcm = n - k := by
            rw [← lcm_eq_of_specialPair hpair, hlcm]
          have hk_lt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          have hne := no_special_of_dvd_two_pow_succ n k hk2 hdiv hk_lt hdvd hμct
          exact hne hlcm'
        rw [hempty, Finset.sum_empty]
        exact eta_nonneg n k
      · -- interesting case
        let a := (n - k) / 2
        let s' : Finset (Multiset ℕ) := (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam)
        let t' : Finset (Multiset ℕ) := (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)
        let f : Multiset ℕ → Multiset ℕ := fun lam => (lam.erase a).erase a
        have hgt : k < a := by
          dsimp [a]
          exact k_lt_half_of_mem_K hn10 hk hk2 hdvd
        have ha2 : 2 ≤ a := by omega
        have hf_mem : ∀ lam ∈ s', f lam ∈ t' := by
          intro lam hlam
          rcases Finset.mem_filter.mp hlam with ⟨hlamct, hlcm, hnk, hpair⟩
          have hμct : (lam.erase a).erase a ∈ cycleTypes k := by
            simpa [a] using (mem_cycleTypes_erase_half_of_specialPair hlamct hpair hdiv)
          have hlcm' : Nat.lcm a ((lam.erase a).erase a).lcm = n - k := by
            have h : Nat.lcm ((n-k)/2) ((lam.erase ((n-k)/2)).erase ((n-k)/2)).lcm = n - k := by
              rw [← lcm_eq_of_specialPair hpair, hlcm]
            simpa [a] using h
          have hmem_pow : 2 ^ Nat.log 2 k ∈ (lam.erase a).erase a :=
            mem_two_pow_log2_of_lcm_eq_two_mul n k hk hk2 hdiv hdvd hμct hlcm'
          rw [Finset.mem_filter]
          exact ⟨hμct, hmem_pow⟩
        have hf_inj : Set.InjOn f (↑s' : Set (Multiset ℕ)) := by
          intro lam₁ hlam₁ lam₂ hlam₂ h
          rcases Finset.mem_filter.mp hlam₁ with ⟨h₁ct, h₁lcm, h₁nk, h₁pair⟩
          rcases Finset.mem_filter.mp hlam₂ with ⟨h₂ct, h₂lcm, h₂nk, h₂pair⟩
          dsimp [f] at h
          have ha_mem₁ : a ∈ lam₁ := by simpa [a] using (specialPair_mem_half h₁pair)
          have ha_mem₂ : a ∈ lam₂ := by simpa [a] using (specialPair_mem_half h₂pair)
          have hlarge_a₁ : large n a := by
            have hfilter : lam₁.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using h₁pair
            have hmem : a ∈ lam₁.filter (large n) := by
              rw [hfilter]
              simp
            exact (Multiset.mem_filter.mp hmem).2
          have hlarge_a₂ : large n a := by
            have hfilter : lam₂.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using h₂pair
            have hmem : a ∈ lam₂.filter (large n) := by
              rw [hfilter]
              simp
            exact (Multiset.mem_filter.mp hmem).2
          have ha_mem_erase₁ : a ∈ lam₁.erase a := by
            have hfilter : lam₁.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using h₁pair
            have hf := hfilter
            rw [← Multiset.cons_erase ha_mem₁] at hf
            rw [Multiset.filter_cons_of_pos (s := lam₁.erase a) hlarge_a₁] at hf
            have h' : a ::ₘ (lam₁.erase a).filter (large n) = a ::ₘ (a ::ₘ 0) := by simpa using hf
            exact (Multiset.mem_filter.mp (by
              rw [(Multiset.cons_inj_right a).mp h']
              simp)).1
          have ha_mem_erase₂ : a ∈ lam₂.erase a := by
            have hfilter : lam₂.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using h₂pair
            have hf := hfilter
            rw [← Multiset.cons_erase ha_mem₂] at hf
            rw [Multiset.filter_cons_of_pos (s := lam₂.erase a) hlarge_a₂] at hf
            have h' : a ::ₘ (lam₂.erase a).filter (large n) = a ::ₘ (a ::ₘ 0) := by simpa using hf
            exact (Multiset.mem_filter.mp (by
              rw [(Multiset.cons_inj_right a).mp h']
              simp)).1
          calc lam₁ = a ::ₘ lam₁.erase a := (Multiset.cons_erase ha_mem₁).symm
            _ = a ::ₘ a ::ₘ ((lam₁.erase a).erase a) := by
                  exact congrArg (fun x => a ::ₘ x) (Multiset.cons_erase ha_mem_erase₁).symm
            _ = a ::ₘ a ::ₘ ((lam₂.erase a).erase a) := by rw [h]
            _ = lam₂ := by
                  have h2' : a ::ₘ a ::ₘ ((lam₂.erase a).erase a) = a ::ₘ lam₂.erase a := by
                    exact congrArg (fun x => a ::ₘ x) (Multiset.cons_erase ha_mem_erase₂)
                  rw [h2', Multiset.cons_erase ha_mem₂]
        have hw_eq : ∀ lam ∈ s', cycleTypeWeight n lam = cycleTypeWeight n (a ::ₘ a ::ₘ f lam) := by
          intro lam hlam
          rcases Finset.mem_filter.mp hlam with ⟨hlamct, hlcm, hnk, hpair⟩
          have ha_mem : a ∈ lam := by simpa [a] using (specialPair_mem_half hpair)
          have hlarge_a : large n a := by
            have hfilter : lam.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using hpair
            have hmem : a ∈ lam.filter (large n) := by
              rw [hfilter]
              simp
            exact (Multiset.mem_filter.mp hmem).2
          have ha_mem_erase : a ∈ lam.erase a := by
            have hfilter : lam.filter (large n) = a ::ₘ a ::ₘ 0 := by simpa [a] using hpair
            have hf := hfilter
            rw [← Multiset.cons_erase ha_mem] at hf
            rw [Multiset.filter_cons_of_pos (s := lam.erase a) hlarge_a] at hf
            have h' : a ::ₘ (lam.erase a).filter (large n) = a ::ₘ (a ::ₘ 0) := by simpa using hf
            exact (Multiset.mem_filter.mp (by
              rw [(Multiset.cons_inj_right a).mp h']
              simp)).1
          dsimp [f]
          calc cycleTypeWeight n lam = cycleTypeWeight n (a ::ₘ lam.erase a) :=
                congrArg (fun s => cycleTypeWeight n s) (Multiset.cons_erase ha_mem).symm
            _ = cycleTypeWeight n (a ::ₘ a ::ₘ ((lam.erase a).erase a)) :=
                congrArg (fun s => cycleTypeWeight n (a ::ₘ s)) (Multiset.cons_erase ha_mem_erase).symm
        have hsum_image : (∑ μ ∈ s'.image f, cycleTypeWeight n (a ::ₘ a ::ₘ μ)) = ∑ lam ∈ s', cycleTypeWeight n lam := by
          rw [Finset.sum_image hf_inj]
          apply Finset.sum_congr rfl
          intro lam hlam
          exact (hw_eq lam hlam).symm
        have himage_subset : s'.image f ⊆ t' := by
          intro μ hμ
          rcases Finset.mem_image.mp hμ with ⟨lam, hlam, rfl⟩
          exact hf_mem lam hlam
        have hstep : ∑ lam ∈ s', cycleTypeWeight n lam ≤ ∑ μ ∈ t', cycleTypeWeight n (a ::ₘ a ::ₘ μ) := by
          rw [← hsum_image]
          refine Finset.sum_le_sum_of_subset_of_nonneg himage_subset ?_
          intro μ hμ hnot
          unfold cycleTypeWeight
          positivity
        have heta : (∑ μ ∈ t', cycleTypeWeight n (a ::ₘ a ::ₘ μ)) = eta n k := by
          dsimp [t', a]
          exact special_cycleTypeWeight_sum_eq_eta n k hk2 hdiv ha2 hgt hdvd
        exact le_trans hstep (le_of_eq heta)
    · -- k ≤ 1: filter empty
      have hempty : (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro lam hlam h
        rcases h with ⟨hlcm, hnk, hpair⟩
        have hμct := mem_cycleTypes_erase_half_of_specialPair hlam hpair hdiv
        have ha_mem : (n - k) / 2 ∈ lam := specialPair_mem_half hpair
        have ha2' : 2 ≤ (n - k) / 2 := mem_cycleTypes_two_le hlam ((n - k) / 2) ha_mem
        have hne := no_special_of_le_one n k hdiv ha2' (by omega : k ≤ 1) hμct
        have hlcm' : Nat.lcm ((n - k) / 2) ((lam.erase ((n - k) / 2)).erase ((n - k) / 2)).lcm = n - k := by
          rw [← lcm_eq_of_specialPair hpair, hlcm]
        exact hne hlcm'
      rw [hempty, Finset.sum_empty]
      exact eta_nonneg n k
  · -- ¬ 2 ∣ n-k: filter empty (a ∣ n-k would force 2 ∣ n-k)
    have hempty : (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro lam hlam h
      rcases h with ⟨hlcm, hnk, hpair⟩
      let a := (n - k) / 2
      have ha_mem : a ∈ lam := by simpa [a] using (specialPair_mem_half hpair)
      have ha2' : 2 ≤ a := mem_cycleTypes_two_le hlam a ha_mem
      have ha_dvd : a ∣ n - k := by
        have hd : a ∣ lam.lcm := Multiset.dvd_lcm ha_mem
        rwa [hlcm] at hd
      have hodd : n - k = 2 * a + 1 := by
        dsimp [a]
        have hodd' : Odd (n - k) := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hdiv)
        have hmod : (n - k) % 2 = 1 := Nat.odd_iff.mp hodd'
        have hdivmod := Nat.div_add_mod (n - k) 2
        calc n - k = 2 * ((n - k) / 2) + (n - k) % 2 := hdivmod.symm
          _ = 2 * ((n - k) / 2) + 1 := by rw [hmod]
      have ha_eq_one : a = 1 := by
        rcases ha_dvd with ⟨c, hc⟩
        have hc2 : 2 ≤ c := by
          by_contra h'
          have hle1 : c ≤ 1 := by omega
          have hmul : a * c ≤ a := by
            have h1 : a * c ≤ a * 1 := Nat.mul_le_mul_left a hle1
            simpa using h1
          have : a * c = 2 * a + 1 := by rw [← hc, hodd]
          omega
        by_cases hc2' : c = 2
        · subst c
          have : a * 2 = 2 * a + 1 := by rw [← hc, hodd]
          omega
        · have hc3 : 3 ≤ c := by omega
          have hmul : 3 * a ≤ a * c := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left a hc3
          have : 3 * a ≤ 2 * a + 1 := by
            rw [← hc, hodd] at hmul
            simpa [Nat.mul_comm] using hmul
          omega
      omega
    rw [hempty, Finset.sum_empty]
    exact eta_nonneg n k

/-- If `filter (large n) lam = {x, y}` then `y ∈ lam.erase x`. -/
lemma mem_erase_of_filter_eq_two {n : ℕ} {lam : Multiset ℕ} {x y : ℕ}
    (hlarge_x : large n x) (h : lam.filter (large n) = {x, y}) : y ∈ lam.erase x := by
  by_cases hyx : y = x
  · subst y
    have hfilter_count : Multiset.count x (lam.filter (large n)) = 2 := by rw [h]; simp
    have hcount_lam : Multiset.count x lam = 2 := by
      rw [Multiset.count_filter_of_pos (s := lam) (p := large n) hlarge_x] at hfilter_count
      exact hfilter_count
    have hcount_erase : Multiset.count x (lam.erase x) = 1 := by
      rw [Multiset.count_erase_self, hcount_lam]
    exact Multiset.count_pos.mp (by omega : 0 < Multiset.count x (lam.erase x))
  · have hy_filter_mem : y ∈ lam.filter (large n) := by rw [h]; simp
    have hyl : y ∈ lam := (Multiset.mem_filter.mp hy_filter_mem).1
    have hcount_y : 0 < Multiset.count y lam := Multiset.count_pos.mpr hyl
    have hcount_erase : 0 < Multiset.count y (lam.erase x) := by
      rw [Multiset.count_erase_of_ne (by exact hyx) lam]
      exact hcount_y
    exact Multiset.count_pos.mp hcount_erase

/-- Extract the two large cycles of `lam` (witness of `card = 2`). -/
noncomputable def twoLarge (n : ℕ) (lam : Multiset ℕ) (h : (lam.filter (large n)).card = 2) :
    ℕ × ℕ := ⟨((Multiset.card_eq_two (s := lam.filter (large n))).mp h).choose,
  ((Multiset.card_eq_two (s := lam.filter (large n))).mp h).choose_spec.choose⟩

lemma twoLarge_spec (n : ℕ) (lam : Multiset ℕ) (h : (lam.filter (large n)).card = 2) :
    lam.filter (large n) = {(twoLarge n lam h).1, (twoLarge n lam h).2} := by
  unfold twoLarge
  exact ((Multiset.card_eq_two (s := lam.filter (large n))).mp h).choose_spec.choose_spec

/-- The two large cycles are members of `lam` with the required divisibility data. -/
lemma twoLarge_data {n k : ℕ} {lam : Multiset ℕ} (hlam : lam ∈ cycleTypes n)
    (hlcm : lam.lcm = n - k) (hnk : n - k ∉ lam) (hcard : (lam.filter (large n)).card = 2) :
    (twoLarge n lam hcard).1 ∈ lam ∧ (twoLarge n lam hcard).2 ∈ lam ∧
      large n ((twoLarge n lam hcard).1) ∧ large n ((twoLarge n lam hcard).2) ∧
      (twoLarge n lam hcard).1 ∣ n - k ∧ (twoLarge n lam hcard).2 ∣ n - k ∧
      (twoLarge n lam hcard).1 < n - k ∧ (twoLarge n lam hcard).2 < n - k := by
  let hspec := twoLarge_spec n lam hcard
  have hx : (twoLarge n lam hcard).1 ∈ lam.filter (large n) := by
    rw [hspec]
    simp
  have hy : (twoLarge n lam hcard).2 ∈ lam.filter (large n) := by
    rw [hspec]
    simp
  have hxl : (twoLarge n lam hcard).1 ∈ lam := (Multiset.mem_filter.mp hx).1
  have hyl : (twoLarge n lam hcard).2 ∈ lam := (Multiset.mem_filter.mp hy).1
  have hxd : (twoLarge n lam hcard).1 ∣ n - k := by
    have hd : (twoLarge n lam hcard).1 ∣ lam.lcm := Multiset.dvd_lcm hxl
    rwa [hlcm] at hd
  have hyd : (twoLarge n lam hcard).2 ∣ n - k := by
    have hd : (twoLarge n lam hcard).2 ∣ lam.lcm := Multiset.dvd_lcm hyl
    rwa [hlcm] at hd
  have hx2 : 2 ≤ (twoLarge n lam hcard).1 := mem_cycleTypes_two_le hlam ((twoLarge n lam hcard).1) hxl
  have hy2 : 2 ≤ (twoLarge n lam hcard).2 := mem_cycleTypes_two_le hlam ((twoLarge n lam hcard).2) hyl
  have hlcm_ne : lam.lcm ≠ 0 := by
    intro h0
    rw [Multiset.lcm_eq_zero_iff] at h0
    have hd2 : 2 ≤ 0 := mem_cycleTypes_two_le hlam 0 h0
    omega
  have hnk_pos : 0 < n - k := by
    have : n - k ≠ 0 := by
      rwa [hlcm] at hlcm_ne
    omega
  have hxlt : (twoLarge n lam hcard).1 < n - k := by
    by_contra hge
    have hle : (twoLarge n lam hcard).1 ≤ n - k := Nat.le_of_dvd hnk_pos hxd
    have heq : (twoLarge n lam hcard).1 = n - k := by omega
    exact hnk (by rwa [← heq])
  have hylt : (twoLarge n lam hcard).2 < n - k := by
    by_contra hge
    have hle : (twoLarge n lam hcard).2 ≤ n - k := Nat.le_of_dvd hnk_pos hyd
    have heq : (twoLarge n lam hcard).2 = n - k := by omega
    exact hnk (by rwa [← heq])
  exact ⟨hxl, hyl, (Multiset.mem_filter.mp hx).2, (Multiset.mem_filter.mp hy).2, hxd, hyd, hxlt, hylt⟩

/-- The residual after removing the two large cycles: lies in `cycleTypes (n-x-y)` and
has no large cycles. -/
lemma erase_twoLarge_data {n : ℕ} {lam : Multiset ℕ} (hlam : lam ∈ cycleTypes n)
    (hcard : (lam.filter (large n)).card = 2) :
    (lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2) ∈
        cycleTypes (n - (twoLarge n lam hcard).1 - (twoLarge n lam hcard).2) ∧
      ∀ z ∈ (lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2),
        ¬ large n z := by
  let hspec := twoLarge_spec n lam hcard
  have hx : (twoLarge n lam hcard).1 ∈ lam.filter (large n) := by
    rw [hspec]
    simp
  have hy : (twoLarge n lam hcard).2 ∈ lam.filter (large n) := by
    rw [hspec]
    simp
  have hxl : (twoLarge n lam hcard).1 ∈ lam := (Multiset.mem_filter.mp hx).1
  have hyl : (twoLarge n lam hcard).2 ∈ lam := (Multiset.mem_filter.mp hy).1
  have hyl_erase : (twoLarge n lam hcard).2 ∈ lam.erase ((twoLarge n lam hcard).1) := by
    exact mem_erase_of_filter_eq_two (Multiset.mem_filter.mp hx).2 hspec
  have hct : (lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2) ∈
      cycleTypes (n - (twoLarge n lam hcard).1 - (twoLarge n lam hcard).2) := by
    have hx_le_sum : (twoLarge n lam hcard).1 ≤ lam.sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) ((twoLarge n lam hcard).1) hxl
    have hy_le_sum : (twoLarge n lam hcard).2 ≤ lam.sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) ((twoLarge n lam hcard).2) hyl
    have hsum_le : lam.sum ≤ n := mem_cycleTypes_sum_le hlam
    have hxy_le_sum : (twoLarge n lam hcard).1 + (twoLarge n lam hcard).2 ≤ lam.sum := by
      have h1 := Multiset.sum_erase hxl
      have h2 := Multiset.sum_erase (s := lam.erase ((twoLarge n lam hcard).1)) hyl_erase
      rw [← h1]
      rw [← h2]
      omega
    have hxy_le : (twoLarge n lam hcard).1 + (twoLarge n lam hcard).2 ≤ n := by omega
    have hx_le_n : (twoLarge n lam hcard).1 ≤ n := by omega
    have hsub0 : n - (n - (twoLarge n lam hcard).1) = (twoLarge n lam hcard).1 := by omega
    have h1 := mem_cycleTypes_erase n (n - (twoLarge n lam hcard).1) hlam (by
      rwa [hsub0]) (by omega)
    have hsub1 : n - (twoLarge n lam hcard).1 - (n - (twoLarge n lam hcard).1 - (twoLarge n lam hcard).2) = (twoLarge n lam hcard).2 := by
      exact Nat.sub_sub_self (by omega : (twoLarge n lam hcard).2 ≤ n - (twoLarge n lam hcard).1)
    have h2 := mem_cycleTypes_erase (n - (twoLarge n lam hcard).1)
      (n - (twoLarge n lam hcard).1 - (twoLarge n lam hcard).2) h1 (by
        rwa [hsub0, hsub1]) (by omega)
    simpa [hsub0, hsub1] using h2
  have hno_large : ∀ z ∈ (lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2),
      ¬ large n z := by
    intro z hz
    intro hlarge
    have hz_lam : z ∈ lam := Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hz)
    have hz_filter : z ∈ lam.filter (large n) := by
      rw [Multiset.mem_filter]
      exact ⟨hz_lam, hlarge⟩
    rw [hspec] at hz_filter
    have hz_xy : z = (twoLarge n lam hcard).1 ∨ z = (twoLarge n lam hcard).2 := by
      simpa using hz_filter
    rcases hz_xy with (hzx | hzy)
    · subst z
      have hcount_pos : 0 < Multiset.count ((twoLarge n lam hcard).1) ((lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2)) :=
        Multiset.count_pos.mpr hz
      have hcount_filter : Multiset.count ((twoLarge n lam hcard).1) (lam.filter (large n)) =
          if (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2 then 2 else 1 := by
        rw [hspec]
        by_cases hxy : (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2 <;> simp [hxy]
      have hcount_lam : Multiset.count ((twoLarge n lam hcard).1) lam =
          if (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2 then 2 else 1 := by
        rwa [Multiset.count_filter_of_pos (s := lam) (p := large n)
          (Multiset.mem_filter.mp hx).2] at hcount_filter
      have hcount_final : Multiset.count ((twoLarge n lam hcard).1) ((lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2)) = 0 := by
        by_cases hxy : (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2
        · rw [hxy] at hcount_lam
          rw [hxy, Multiset.count_erase_self, Multiset.count_erase_self, hcount_lam]
          simp [hxy]
        · rw [Multiset.count_erase_of_ne (a := (twoLarge n lam hcard).1) (b := (twoLarge n lam hcard).2)
              (by exact hxy) (s := lam.erase ((twoLarge n lam hcard).1)),
            Multiset.count_erase_self, hcount_lam]
          simp [hxy]
      omega
    · subst z
      have hcount_pos : 0 < Multiset.count ((twoLarge n lam hcard).2) ((lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2)) :=
        Multiset.count_pos.mpr hz
      have hcount_filter : Multiset.count ((twoLarge n lam hcard).2) (lam.filter (large n)) =
          if (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2 then 2 else 1 := by
        rw [hspec]
        by_cases hxy : (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2 <;> simp [hxy]
      have hcount_lam : Multiset.count ((twoLarge n lam hcard).2) lam =
          if (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2 then 2 else 1 := by
        rwa [Multiset.count_filter_of_pos (s := lam) (p := large n)
          (Multiset.mem_filter.mp hy).2] at hcount_filter
      have hcount_final : Multiset.count ((twoLarge n lam hcard).2) ((lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2)) = 0 := by
        by_cases hxy : (twoLarge n lam hcard).1 = (twoLarge n lam hcard).2
        · rw [hxy] at hcount_lam
          rw [hxy, Multiset.count_erase_self, Multiset.count_erase_self, hcount_lam]
          simp [hxy]
        · rw [Multiset.count_erase_self, Multiset.count_erase_of_ne (a := (twoLarge n lam hcard).2)
              (b := (twoLarge n lam hcard).1) (by exact fun h => hxy h.symm) lam, hcount_lam]
          simp [hxy]
      omega
  exact ⟨hct, hno_large⟩

/-- The T₂ "rest" term: two large cycles but not the special pair. -/
lemma sum_cycleTypeWeight_two_large_rest_le (n k : ℕ) (hk : k ∈ K n) (hn3 : 3 ≤ n)
    (hν : ∀ m : ℕ, (n : ℝ) ≤ 6 * (m : ℝ) → m ≤ n →
      nuNoLong m (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (24 : ℝ)^45 / (n : ℝ)^3) :
    (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧
        (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam),
      cycleTypeWeight n lam) ≤
    ∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k,
      (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := by
  classical
  let r : ℕ := ⌈(n : ℝ)^(13/14 : ℝ)⌉₊
  let s' : Finset (Multiset ℕ) := (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧
      (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam)
  let t : Finset (Σ d₁ : ℕ, Σ d₂ : ℕ, Multiset ℕ) := (largeDivs n k).sigma (fun d₁ =>
    ((largeDivs n k).filter (fun d₂ => ¬ (d₁ = (n - k) / 2 ∧ d₂ = (n - k) / 2))).sigma (fun d₂ =>
      (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r)))
  let f : Multiset ℕ → (Σ d₁ : ℕ, Σ d₂ : ℕ, Multiset ℕ) := fun lam =>
    if h : (lam.filter (large n)).card = 2 then
      ⟨(twoLarge n lam h).1,
        ⟨(twoLarge n lam h).2, (lam.erase ((twoLarge n lam h).1)).erase ((twoLarge n lam h).2)⟩⟩
    else
      ⟨0, ⟨0, 0⟩⟩
  let w' : (Σ d₁ : ℕ, Σ d₂ : ℕ, Multiset ℕ) → ℝ := fun p => cycleTypeWeight n (p.1 ::ₘ p.2.1 ::ₘ p.2.2)
  have hf_mem : ∀ lam ∈ s', f lam ∈ t := by
    intro lam hlam
    rcases Finset.mem_filter.mp hlam with ⟨hlamct, hlcm, hnk, hcard, hnotpair⟩
    have hres := erase_twoLarge_data hlamct hcard
    have hcard2 : (lam.filter (large n)).card = 2 := hcard
    rcases twoLarge_data hlamct hlcm hnk hcard2 with
      ⟨hxl2, hyl2, hlargex, hlargey, hxdvd, hydvd, hxlt2, hylt2⟩
    have hf : f lam = ⟨(twoLarge n lam hcard2).1,
        ⟨(twoLarge n lam hcard2).2, (lam.erase ((twoLarge n lam hcard2).1)).erase ((twoLarge n lam hcard2).2)⟩⟩ := by
      dsimp [f]
      rw [dif_pos hcard2]
    rw [hf]
    have hx_divs : (twoLarge n lam hcard2).1 ∈ largeDivs n k := by
      unfold largeDivs
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨hxdvd, by omega⟩, ⟨hxlt2, hlargex⟩⟩
    have hy_divs : (twoLarge n lam hcard2).2 ∈ largeDivs n k := by
      unfold largeDivs
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨hydvd, by omega⟩, ⟨hylt2, hlargey⟩⟩
    have hnot_pair : ¬ ((twoLarge n lam hcard2).1 = (n - k) / 2 ∧ (twoLarge n lam hcard2).2 = (n - k) / 2) := by
      intro h
      apply hnotpair
      dsimp [specialPair]
      rw [twoLarge_spec n lam hcard2, h.1, h.2]
      rfl
    have hy_filter : (twoLarge n lam hcard2).2 ∈
        (largeDivs n k).filter (fun d₂ => ¬ ((twoLarge n lam hcard2).1 = (n - k) / 2 ∧ d₂ = (n - k) / 2)) := by
      rw [Finset.mem_filter]
      exact ⟨hy_divs, hnot_pair⟩
    have hres_small : ∀ x ∈ (lam.erase ((twoLarge n lam hcard2).1)).erase ((twoLarge n lam hcard2).2), x ≤ r := by
      intro z hz
      dsimp [r]
      exact not_large_le_ceil n z (hres.2 z hz)
    rw [Finset.mem_sigma]
    refine ⟨hx_divs, ?_⟩
    rw [Finset.mem_sigma]
    exact ⟨hy_filter, by
      rw [Finset.mem_filter]
      exact ⟨hres.1, hres_small⟩⟩
  have hf_inj : Set.InjOn f (↑s' : Set (Multiset ℕ)) := by
    intro lam₁ hlam₁ lam₂ hlam₂ h
    rcases Finset.mem_filter.mp hlam₁ with ⟨h₁ct, h₁lcm, h₁nk, h₁card, h₁nsp⟩
    rcases Finset.mem_filter.mp hlam₂ with ⟨h₂ct, h₂lcm, h₂nk, h₂card, h₂nsp⟩
    have hf₁ : f lam₁ = ⟨(twoLarge n lam₁ h₁card).1,
        ⟨(twoLarge n lam₁ h₁card).2, (lam₁.erase ((twoLarge n lam₁ h₁card).1)).erase ((twoLarge n lam₁ h₁card).2)⟩⟩ := by
      dsimp [f]
      rw [dif_pos h₁card]
    have hf₂ : f lam₂ = ⟨(twoLarge n lam₂ h₂card).1,
        ⟨(twoLarge n lam₂ h₂card).2, (lam₂.erase ((twoLarge n lam₂ h₂card).1)).erase ((twoLarge n lam₂ h₂card).2)⟩⟩ := by
      dsimp [f]
      rw [dif_pos h₂card]
    rw [hf₁, hf₂] at h
    have hx_eq : (twoLarge n lam₁ h₁card).1 = (twoLarge n lam₂ h₂card).1 := congrArg (fun p : Σ d₁ : ℕ, Σ d₂ : ℕ, Multiset ℕ => p.1) h
    have hy_eq : (twoLarge n lam₁ h₁card).2 = (twoLarge n lam₂ h₂card).2 := congrArg (fun p : Σ d₁ : ℕ, Σ d₂ : ℕ, Multiset ℕ => p.2.1) h
    have hr_eq : (lam₁.erase ((twoLarge n lam₁ h₁card).1)).erase ((twoLarge n lam₁ h₁card).2) =
        (lam₂.erase ((twoLarge n lam₂ h₂card).1)).erase ((twoLarge n lam₂ h₂card).2) :=
      congrArg (fun p : Σ d₁ : ℕ, Σ d₂ : ℕ, Multiset ℕ => p.2.2) h
    have hx₁_mem : (twoLarge n lam₁ h₁card).1 ∈ lam₁ := (twoLarge_data h₁ct h₁lcm h₁nk h₁card).1
    have hx₂_mem : (twoLarge n lam₂ h₂card).1 ∈ lam₂ := (twoLarge_data h₂ct h₂lcm h₂nk h₂card).1
    have hy₁_mem : (twoLarge n lam₁ h₁card).2 ∈ lam₁.erase ((twoLarge n lam₁ h₁card).1) := by
      have hfilter := twoLarge_spec n lam₁ h₁card
      have hx : (twoLarge n lam₁ h₁card).1 ∈ lam₁.filter (large n) := by
        rw [hfilter]
        simp
      exact mem_erase_of_filter_eq_two (Multiset.mem_filter.mp hx).2 hfilter
    have hy₂_mem : (twoLarge n lam₂ h₂card).2 ∈ lam₂.erase ((twoLarge n lam₂ h₂card).1) := by
      have hfilter := twoLarge_spec n lam₂ h₂card
      have hx : (twoLarge n lam₂ h₂card).1 ∈ lam₂.filter (large n) := by
        rw [hfilter]
        simp
      exact mem_erase_of_filter_eq_two (Multiset.mem_filter.mp hx).2 hfilter
    calc lam₁ = (twoLarge n lam₁ h₁card).1 ::ₘ lam₁.erase ((twoLarge n lam₁ h₁card).1) :=
          (Multiset.cons_erase hx₁_mem).symm
      _ = (twoLarge n lam₁ h₁card).1 ::ₘ ((twoLarge n lam₁ h₁card).2 ::ₘ
          (lam₁.erase ((twoLarge n lam₁ h₁card).1)).erase ((twoLarge n lam₁ h₁card).2)) := by
          exact congrArg (fun s => (twoLarge n lam₁ h₁card).1 ::ₘ s) (Multiset.cons_erase hy₁_mem).symm
      _ = (twoLarge n lam₂ h₂card).1 ::ₘ ((twoLarge n lam₂ h₂card).2 ::ₘ
          (lam₂.erase ((twoLarge n lam₂ h₂card).1)).erase ((twoLarge n lam₂ h₂card).2)) := by
          rw [hx_eq, hy_eq] at hr_eq
          rw [hx_eq, hy_eq, hr_eq]
      _ = (twoLarge n lam₂ h₂card).1 ::ₘ lam₂.erase ((twoLarge n lam₂ h₂card).1) := by
          exact congrArg (fun s => (twoLarge n lam₂ h₂card).1 ::ₘ s) (Multiset.cons_erase hy₂_mem)
      _ = lam₂ := Multiset.cons_erase hx₂_mem
  have hw_eq : ∀ lam ∈ s', cycleTypeWeight n lam = w' (f lam) := by
    intro lam hlam
    rcases Finset.mem_filter.mp hlam with ⟨hlamct, hlcm, hnk, hcard, hnotpair⟩
    have hdata := twoLarge_data hlamct hlcm hnk hcard
    have hx_mem : (twoLarge n lam hcard).1 ∈ lam := hdata.1
    have hy_mem : (twoLarge n lam hcard).2 ∈ lam.erase ((twoLarge n lam hcard).1) := by
      have hfilter := twoLarge_spec n lam hcard
      have hx : (twoLarge n lam hcard).1 ∈ lam.filter (large n) := by
        rw [hfilter]
        simp
      exact mem_erase_of_filter_eq_two (Multiset.mem_filter.mp hx).2 hfilter
    have hf : f lam = ⟨(twoLarge n lam hcard).1,
        ⟨(twoLarge n lam hcard).2, (lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2)⟩⟩ := by
      dsimp [f]
      rw [dif_pos hcard]
    rw [hf]
    dsimp [w']
    calc cycleTypeWeight n lam
        = cycleTypeWeight n ((twoLarge n lam hcard).1 ::ₘ lam.erase ((twoLarge n lam hcard).1)) := by
            exact congrArg (fun s => cycleTypeWeight n s) (Multiset.cons_erase hx_mem).symm
      _ = cycleTypeWeight n ((twoLarge n lam hcard).1 ::ₘ (twoLarge n lam hcard).2 ::ₘ
          (lam.erase ((twoLarge n lam hcard).1)).erase ((twoLarge n lam hcard).2)) := by
            exact congrArg (fun s => cycleTypeWeight n ((twoLarge n lam hcard).1 ::ₘ s))
              (Multiset.cons_erase hy_mem).symm
  have hsum_image : (∑ p ∈ s'.image f, w' p) = ∑ lam ∈ s', cycleTypeWeight n lam := by
    rw [Finset.sum_image hf_inj]
    apply Finset.sum_congr rfl
    intro lam hlam
    exact (hw_eq lam hlam).symm
  have himage_subset : s'.image f ⊆ t := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨lam, hlam, rfl⟩
    exact hf_mem lam hlam
  have hstep : ∑ lam ∈ s', cycleTypeWeight n lam ≤ ∑ p ∈ t, w' p := by
    rw [← hsum_image]
    refine Finset.sum_le_sum_of_subset_of_nonneg himage_subset ?_
    intro p hp hnot
    unfold w' cycleTypeWeight
    positivity
  have hsum_sigma : (∑ p ∈ t, w' p) = ∑ d₁ ∈ largeDivs n k,
      ∑ d₂ ∈ (largeDivs n k).filter (fun d₂ => ¬ (d₁ = (n - k) / 2 ∧ d₂ = (n - k) / 2)),
        ∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
          cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    rw [Finset.sum_sigma]
  have hdec : ∀ d₁ ∈ largeDivs n k, ∀ d₂ ∈ (largeDivs n k).filter (fun d₂ => ¬ (d₁ = (n - k) / 2 ∧ d₂ = (n - k) / 2)),
      (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
        cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam)) ≤
      (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := by
    intro d₁ hd₁ d₂ hd₂'
    have hd₂ : d₂ ∈ largeDivs n k := (Finset.mem_filter.mp hd₂').1
    have hnot_pair : ¬ (d₁ = (n - k) / 2 ∧ d₂ = (n - k) / 2) := (Finset.mem_filter.mp hd₂').2
    have hd₁_dvd : d₁ ∣ n - k := mem_largeDivs_dvd hd₁
    have hd₂_dvd : d₂ ∣ n - k := mem_largeDivs_dvd hd₂
    have hd₁_lt : d₁ < n - k := mem_largeDivs_lt hd₁
    have hd₂_lt : d₂ < n - k := mem_largeDivs_lt hd₂
    have hd₁_le_half : d₁ ≤ (n - k) / 2 := proper_divisor_le_half hd₁_dvd hd₁_lt
    have hd₂_le_half : d₂ ≤ (n - k) / 2 := proper_divisor_le_half hd₂_dvd hd₂_lt
    have hd_sum_le : d₁ + d₂ ≤ n - k := by omega
    have hd_sum_le_n : d₁ + d₂ ≤ n := by omega
    have hd₁_2 : 2 ≤ d₁ := by
      have hlarge : large n d₁ := mem_largeDivs_large hd₁
      unfold large at hlarge
      have hnR : (1 : ℝ) < (n : ℝ)^(13/14 : ℝ) := by
        have hn2 : 2 ≤ n := by omega
        have h1 : (1 : ℝ) < (2 : ℝ)^(13/14 : ℝ) := by
          have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < (2 : ℝ))
            (by norm_num : (0 : ℝ) < (13/14 : ℝ))
          simpa [Real.one_rpow] using h
        have h2 : (2 : ℝ)^(13/14 : ℝ) ≤ (n : ℝ)^(13/14 : ℝ) := by
          exact Real.rpow_le_rpow (by norm_num : 0 ≤ (2:ℝ)) (by exact_mod_cast hn2) (by norm_num : 0 ≤ (13/14:ℝ))
        exact lt_of_lt_of_le h1 h2
      have hd_gt1 : (1 : ℝ) < (d₁ : ℝ) := lt_of_lt_of_le hnR hlarge
      have hd_pos : 0 < d₁ := by
        have : (0 : ℝ) < (d₁ : ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hd_gt1
        exact_mod_cast this
      have hd_ne1 : d₁ ≠ 1 := by
        intro h
        have : (d₁ : ℝ) = 1 := by rw [h]; norm_num
        linarith
      omega
    have hd₂_2 : 2 ≤ d₂ := by
      have hlarge : large n d₂ := mem_largeDivs_large hd₂
      unfold large at hlarge
      have hnR : (1 : ℝ) < (n : ℝ)^(13/14 : ℝ) := by
        have hn2 : 2 ≤ n := by omega
        have h1 : (1 : ℝ) < (2 : ℝ)^(13/14 : ℝ) := by
          have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < (2 : ℝ))
            (by norm_num : (0 : ℝ) < (13/14 : ℝ))
          simpa [Real.one_rpow] using h
        have h2 : (2 : ℝ)^(13/14 : ℝ) ≤ (n : ℝ)^(13/14 : ℝ) := by
          exact Real.rpow_le_rpow (by norm_num : 0 ≤ (2:ℝ)) (by exact_mod_cast hn2) (by norm_num : 0 ≤ (13/14:ℝ))
        exact lt_of_lt_of_le h1 h2
      have hd_gt1 : (1 : ℝ) < (d₂ : ℝ) := lt_of_lt_of_le hnR hlarge
      have hd_pos : 0 < d₂ := by
        have : (0 : ℝ) < (d₂ : ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hd_gt1
        exact_mod_cast this
      have hd_ne1 : d₂ ≠ 1 := by
        intro h
        have : (d₂ : ℝ) = 1 := by rw [h]; norm_num
        linarith
      omega
    have hdec_point : ∀ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
        cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam) ≤
          (1 / ((d₁ * d₂ : ℕ) : ℝ)) * cycleTypeWeight (n - d₁ - d₂) lam := by
      intro lam hlam
      have hlamct : lam ∈ cycleTypes (n - d₁ - d₂) := (Finset.mem_filter.mp hlam).1
      have hlam2 : ∀ x ∈ lam, 2 ≤ x := mem_cycleTypes_two_le hlamct
      have hlamsum : lam.sum ≤ n - d₁ - d₂ := mem_cycleTypes_sum_le hlamct
      have h1 := cycleTypeWeight_cons_le n d₁ (d₂ ::ₘ lam) hd₁_2
        (by intro x hx
            rcases Multiset.mem_cons.mp hx with (hxd | hxl)
            · rw [hxd]
              exact hd₂_2
            · exact hlam2 x hxl)
        (by
          have h : d₁ + (d₂ + lam.sum) ≤ n := by omega
          simpa [Multiset.sum_cons] using h)
      have hsum₂' : d₂ + lam.sum ≤ n - d₁ := by omega
      have h2 := cycleTypeWeight_cons_le (n - d₁) d₂ lam hd₂_2 hlam2 hsum₂'
      calc cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam)
          ≤ (1 / (d₁ : ℝ)) * cycleTypeWeight (n - d₁) (d₂ ::ₘ lam) := h1
        _ ≤ (1 / (d₁ : ℝ)) * ((1 / (d₂ : ℝ)) * cycleTypeWeight (n - d₁ - d₂) lam) := by
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (1 / ((d₁ * d₂ : ℕ) : ℝ)) * cycleTypeWeight (n - d₁ - d₂) lam := by
              rw [Nat.cast_mul]
              rw [← one_div_mul_one_div]
              rw [mul_assoc]
    have hsum_le : (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
        cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam)) ≤
        (1 / ((d₁ * d₂ : ℕ) : ℝ)) *
          (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
            cycleTypeWeight (n - d₁ - d₂) lam) := by
      calc (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
            cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam))
          ≤ ∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
              (1 / ((d₁ * d₂ : ℕ) : ℝ)) * cycleTypeWeight (n - d₁ - d₂) lam := by
              exact Finset.sum_le_sum (fun lam hlam => hdec_point lam hlam)
        _ = (1 / ((d₁ * d₂ : ℕ) : ℝ)) *
            (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
              cycleTypeWeight (n - d₁ - d₂) lam) := by rw [Finset.mul_sum]
    have hnu : (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
        cycleTypeWeight (n - d₁ - d₂) lam) ≤ (24 : ℝ)^45 / (n : ℝ)^3 := by
      have hν' : nuNoLong (n - d₁ - d₂) r ≤ (24 : ℝ)^45 / (n : ℝ)^3 := by
        apply hν (n - d₁ - d₂)
        · -- n ≤ 6 * (n - d₁ - d₂)
          have hsum_lt : d₁ + d₂ < n - k := by
            by_contra hge
            have hsum_eq : d₁ + d₂ = n - k := by omega
            have hd₁_eq : d₁ = (n - k) / 2 := by omega
            have hd₂_eq : d₂ = (n - k) / 2 := by omega
            exact hnot_pair ⟨hd₁_eq, hd₂_eq⟩
          have hsix := six_mul_add_le_five_mul hd₁_dvd hd₂_dvd hd₁_lt hd₂_lt hsum_lt
          have hsix' : 6 * (d₁ + d₂) ≤ 5 * n := le_trans hsix (Nat.mul_le_mul_left 5 (Nat.sub_le n k))
          have hbound_nat : n ≤ 6 * (n - d₁ - d₂) := by omega
          exact_mod_cast hbound_nat
        · -- n - d₁ - d₂ ≤ n
          omega
      simpa [nuNoLong, r] using hν'
    have hnonneg : 0 ≤ (1 / ((d₁ * d₂ : ℕ) : ℝ)) := by positivity
    calc (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
          cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam))
        ≤ (1 / ((d₁ * d₂ : ℕ) : ℝ)) *
            (∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
              cycleTypeWeight (n - d₁ - d₂) lam) := hsum_le
      _ ≤ (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) :=
            mul_le_mul_of_nonneg_left hnu hnonneg
  have hfinal : (∑ p ∈ t, w' p) ≤ ∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k,
      (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := by
    rw [hsum_sigma]
    refine Finset.sum_le_sum ?_
    intro d₁ hd₁
    calc (∑ d₂ ∈ (largeDivs n k).filter (fun d₂ => ¬ (d₁ = (n - k) / 2 ∧ d₂ = (n - k) / 2)),
          ∑ lam ∈ (cycleTypes (n - d₁ - d₂)).filter (fun lam => ∀ x ∈ lam, x ≤ r),
            cycleTypeWeight n (d₁ ::ₘ d₂ ::ₘ lam))
        ≤ ∑ d₂ ∈ (largeDivs n k).filter (fun d₂ => ¬ (d₁ = (n - k) / 2 ∧ d₂ = (n - k) / 2)),
            (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := by
              exact Finset.sum_le_sum (fun d₂ hd₂ => hdec d₁ hd₁ d₂ hd₂)
      _ ≤ ∑ d₂ ∈ largeDivs n k, (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro d₂ hd₂
                exact (Finset.mem_filter.mp hd₂).1
              · intro d₂ hd₂ hnot
                positivity
  calc (∑ lam ∈ s', cycleTypeWeight n lam)
      ≤ ∑ p ∈ t, w' p := hstep
    _ ≤ ∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k,
        (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := hfinal

/-- A multiset of cardinality at least 3 has three elements `x, y, z` with
`x ∈ s`, `y ∈ s.erase x`, `z ∈ (s.erase x).erase y`. -/
lemma exists_three_mem_of_card_ge_three {s : Multiset ℕ} (h : 3 ≤ s.card) :
    ∃ x : ℕ, ∃ y : ℕ, ∃ z : ℕ, x ∈ s ∧ y ∈ s.erase x ∧ z ∈ (s.erase x).erase y := by
  have hne : s ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  rcases Multiset.exists_mem_of_ne_zero hne with ⟨x, hx⟩
  have hcard_erase : 2 ≤ (s.erase x).card := by
    rw [Multiset.card_erase_of_mem hx]
    simpa [Nat.pred_eq_sub_one] using (Nat.sub_le_sub_right h (1 : ℕ))
  have hne2 : s.erase x ≠ 0 := by
    intro h0
    rw [h0] at hcard_erase
    norm_num at hcard_erase
  rcases Multiset.exists_mem_of_ne_zero hne2 with ⟨y, hy⟩
  have hcard_erase2 : 1 ≤ ((s.erase x).erase y).card := by
    rw [Multiset.card_erase_of_mem hy]
    simpa [Nat.pred_eq_sub_one] using (Nat.sub_le_sub_right hcard_erase (1 : ℕ))
  have hne3 : (s.erase x).erase y ≠ 0 := by
    intro h0
    rw [h0] at hcard_erase2
    norm_num at hcard_erase2
  rcases Multiset.exists_mem_of_ne_zero hne3 with ⟨z, hz⟩
  exact ⟨x, y, z, hx, hy, hz⟩

/-- Extract three large cycles of `lam` (witness of `3 ≤ card`). -/
noncomputable def threeLarge (n : ℕ) (lam : Multiset ℕ) (h : 3 ≤ (lam.filter (large n)).card) :
    ℕ × ℕ × ℕ :=
  let w := Classical.choose (exists_three_mem_of_card_ge_three h)
  let hspec := Classical.choose_spec (exists_three_mem_of_card_ge_three h)
  let w2 := hspec.choose
  ⟨w, w2, hspec.choose_spec.choose⟩

lemma threeLarge_spec (n : ℕ) (lam : Multiset ℕ) (h : 3 ≤ (lam.filter (large n)).card) :
    let s := lam.filter (large n)
    (threeLarge n lam h).1 ∈ s ∧ (threeLarge n lam h).2.1 ∈ s.erase (threeLarge n lam h).1 ∧
      (threeLarge n lam h).2.2 ∈ (s.erase (threeLarge n lam h).1).erase (threeLarge n lam h).2.1 := by
  unfold threeLarge
  let w := Classical.choose (exists_three_mem_of_card_ge_three h)
  let hspec := Classical.choose_spec (exists_three_mem_of_card_ge_three h)
  let w2 := hspec.choose
  have hspec2 := hspec.choose_spec
  have hspec3 := hspec2.choose_spec
  simpa [w, w2] using hspec3

/-- The three large cycles: membership and divisibility data. -/
lemma threeLarge_data {n k : ℕ} {lam : Multiset ℕ} (hlam : lam ∈ cycleTypes n)
    (hlcm : lam.lcm = n - k) (hnk : n - k ∉ lam) (hcard : 3 ≤ (lam.filter (large n)).card) :
    (threeLarge n lam hcard).1 ∈ lam ∧ (threeLarge n lam hcard).2.1 ∈ lam ∧
      (threeLarge n lam hcard).2.2 ∈ lam ∧
      large n (threeLarge n lam hcard).1 ∧ large n (threeLarge n lam hcard).2.1 ∧
      large n (threeLarge n lam hcard).2.2 ∧
      (threeLarge n lam hcard).1 ∣ n - k ∧ (threeLarge n lam hcard).2.1 ∣ n - k ∧
      (threeLarge n lam hcard).2.2 ∣ n - k ∧
      (threeLarge n lam hcard).1 < n - k ∧ (threeLarge n lam hcard).2.1 < n - k ∧
      (threeLarge n lam hcard).2.2 < n - k := by
  let hspec := threeLarge_spec n lam hcard
  have hx : (threeLarge n lam hcard).1 ∈ lam.filter (large n) := hspec.1
  have hy : (threeLarge n lam hcard).2.1 ∈ (lam.filter (large n)).erase (threeLarge n lam hcard).1 := hspec.2.1
  have hz : (threeLarge n lam hcard).2.2 ∈ ((lam.filter (large n)).erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1 := hspec.2.2
  have hy_filter : (threeLarge n lam hcard).2.1 ∈ lam.filter (large n) :=
    Multiset.mem_of_mem_erase hy
  have hz_filter : (threeLarge n lam hcard).2.2 ∈ lam.filter (large n) :=
    Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hz)
  have hxl : (threeLarge n lam hcard).1 ∈ lam := (Multiset.mem_filter.mp hx).1
  have hyl : (threeLarge n lam hcard).2.1 ∈ lam := (Multiset.mem_filter.mp hy_filter).1
  have hzl : (threeLarge n lam hcard).2.2 ∈ lam := (Multiset.mem_filter.mp hz_filter).1
  have hxd : (threeLarge n lam hcard).1 ∣ n - k := by
    have hd : (threeLarge n lam hcard).1 ∣ lam.lcm := Multiset.dvd_lcm hxl
    rwa [hlcm] at hd
  have hyd : (threeLarge n lam hcard).2.1 ∣ n - k := by
    have hd : (threeLarge n lam hcard).2.1 ∣ lam.lcm := Multiset.dvd_lcm hyl
    rwa [hlcm] at hd
  have hzd : (threeLarge n lam hcard).2.2 ∣ n - k := by
    have hd : (threeLarge n lam hcard).2.2 ∣ lam.lcm := Multiset.dvd_lcm hzl
    rwa [hlcm] at hd
  have hlcm_ne : lam.lcm ≠ 0 := by
    intro h0
    rw [Multiset.lcm_eq_zero_iff] at h0
    have hd2 : 2 ≤ 0 := mem_cycleTypes_two_le hlam 0 h0
    omega
  have hnk_pos : 0 < n - k := by
    have : n - k ≠ 0 := by
      rwa [hlcm] at hlcm_ne
    omega
  have hxlt : (threeLarge n lam hcard).1 < n - k := by
    by_contra hge
    have hle : (threeLarge n lam hcard).1 ≤ n - k := Nat.le_of_dvd hnk_pos hxd
    have heq : (threeLarge n lam hcard).1 = n - k := by omega
    exact hnk (by rwa [← heq])
  have hylt : (threeLarge n lam hcard).2.1 < n - k := by
    by_contra hge
    have hle : (threeLarge n lam hcard).2.1 ≤ n - k := Nat.le_of_dvd hnk_pos hyd
    have heq : (threeLarge n lam hcard).2.1 = n - k := by omega
    exact hnk (by rwa [← heq])
  have hzlt : (threeLarge n lam hcard).2.2 < n - k := by
    by_contra hge
    have hle : (threeLarge n lam hcard).2.2 ≤ n - k := Nat.le_of_dvd hnk_pos hzd
    have heq : (threeLarge n lam hcard).2.2 = n - k := by omega
    exact hnk (by rwa [← heq])
  exact ⟨hxl, hyl, hzl, (Multiset.mem_filter.mp hx).2, (Multiset.mem_filter.mp hy_filter).2,
    (Multiset.mem_filter.mp hz_filter).2, hxd, hyd, hzd, hxlt, hylt, hzlt⟩

/-- `(if a = b then 2 else 1) ≤ count a s` forces `a ∈ s.erase b`. -/
lemma mem_erase_of_count_ge {s : Multiset ℕ} {a b : ℕ}
    (h : (if a = b then 2 else 1) ≤ Multiset.count a s) : a ∈ s.erase b := by
  by_cases hab : a = b
  · subst b
    have h' : 1 ≤ Multiset.count a (s.erase a) := by
      rw [Multiset.count_erase_self]
      have h2 : 2 ≤ Multiset.count a s := by simpa using h
      omega
    exact Multiset.count_pos.mp h'
  · have h' : 1 ≤ Multiset.count a (s.erase b) := by
      rw [Multiset.count_erase_of_ne (by exact hab) s]
      simpa [hab] using h
    exact Multiset.count_pos.mp h'

/-- `(if a=c then 1 else 0) + (if a=b then 1 else 0) + 1 ≤ count a s` forces
`a ∈ (s.erase b).erase c`. -/
lemma mem_erase_erase_of_count_ge {s : Multiset ℕ} {a b c : ℕ}
    (h : (if a = c then 1 else 0) + (if a = b then 1 else 0) + 1 ≤ Multiset.count a s) :
    a ∈ (s.erase b).erase c := by
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      have h' : 1 ≤ Multiset.count a ((s.erase a).erase a) := by
        rw [Multiset.count_erase_self, Multiset.count_erase_self]
        norm_num at h
        omega
      exact Multiset.count_pos.mp h'
    · have h' : 1 ≤ Multiset.count a ((s.erase a).erase c) := by
        rw [Multiset.count_erase_of_ne (by exact hac) (s.erase a)]
        rw [Multiset.count_erase_self]
        simp only [if_neg hac] at h
        norm_num at h
        omega
      exact Multiset.count_pos.mp h'
  · by_cases hac : a = c
    · subst c
      have h' : 1 ≤ Multiset.count a ((s.erase b).erase a) := by
        rw [Multiset.count_erase_self]
        rw [Multiset.count_erase_of_ne (by exact hab) s]
        simp only [if_neg hab] at h
        norm_num at h
        omega
      exact Multiset.count_pos.mp h'
    · have h' : 1 ≤ Multiset.count a ((s.erase b).erase c) := by
        rw [Multiset.count_erase_of_ne (by exact hac) (s.erase b)]
        rw [Multiset.count_erase_of_ne (by exact hab) s]
        simp only [if_neg hac, if_neg hab] at h
        norm_num at h
        exact h
      exact Multiset.count_pos.mp h'

/-- `y ∈ lam.erase x` for the second large cycle. -/
lemma threeLarge_second_mem_erase {n : ℕ} {lam : Multiset ℕ}
    (hcard : 3 ≤ (lam.filter (large n)).card) :
    (threeLarge n lam hcard).2.1 ∈ lam.erase (threeLarge n lam hcard).1 := by
  have hspec := threeLarge_spec n lam hcard
  have hy : (threeLarge n lam hcard).2.1 ∈ (lam.filter (large n)).erase (threeLarge n lam hcard).1 := hspec.2.1
  have hy_filter : (threeLarge n lam hcard).2.1 ∈ lam.filter (large n) := Multiset.mem_of_mem_erase hy
  have hy_large : large n (threeLarge n lam hcard).2.1 := (Multiset.mem_filter.mp hy_filter).2
  have hcount_erase : 1 ≤ Multiset.count (threeLarge n lam hcard).2.1 ((lam.filter (large n)).erase (threeLarge n lam hcard).1) :=
    Multiset.count_pos.mpr hy
  have hcount_filter_eq : Multiset.count (threeLarge n lam hcard).2.1 (lam.filter (large n)) =
      Multiset.count (threeLarge n lam hcard).2.1 lam := by
    rw [Multiset.count_filter_of_pos (s := lam) (p := large n) hy_large]
  have hge : (if (threeLarge n lam hcard).2.1 = (threeLarge n lam hcard).1 then 2 else 1) ≤
      Multiset.count (threeLarge n lam hcard).2.1 lam := by
    by_cases hyx : (threeLarge n lam hcard).2.1 = (threeLarge n lam hcard).1
    · rw [← hyx] at hcount_erase
      have hc := Multiset.count_erase_self (threeLarge n lam hcard).2.1 (lam.filter (large n))
      rw [hc] at hcount_erase
      rw [← hcount_filter_eq]
      have h2 : 2 ≤ Multiset.count (threeLarge n lam hcard).2.1 (lam.filter (large n)) := by
        omega
      simpa [hyx] using h2
    · rw [← hcount_filter_eq]
      rw [← Multiset.count_erase_of_ne (by exact hyx) (lam.filter (large n))]
      simpa [hyx] using hcount_erase
  exact mem_erase_of_count_ge hge

/-- `z ∈ (lam.erase x).erase y` for the third large cycle. -/
lemma threeLarge_third_mem_erase {n : ℕ} {lam : Multiset ℕ}
    (hcard : 3 ≤ (lam.filter (large n)).card) :
    (threeLarge n lam hcard).2.2 ∈ (lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1 := by
  have hspec := threeLarge_spec n lam hcard
  have hz : (threeLarge n lam hcard).2.2 ∈ ((lam.filter (large n)).erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1 := hspec.2.2
  have hz_erasex : (threeLarge n lam hcard).2.2 ∈ (lam.filter (large n)).erase (threeLarge n lam hcard).1 :=
    Multiset.mem_of_mem_erase hz
  have hz_filter : (threeLarge n lam hcard).2.2 ∈ lam.filter (large n) :=
    Multiset.mem_of_mem_erase hz_erasex
  have hz_large : large n (threeLarge n lam hcard).2.2 := (Multiset.mem_filter.mp hz_filter).2
  have hcount_erase_erase : 1 ≤ Multiset.count (threeLarge n lam hcard).2.2
      (((lam.filter (large n)).erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1) :=
    Multiset.count_pos.mpr hz
  have hcount_erasex : 1 ≤ Multiset.count (threeLarge n lam hcard).2.2 ((lam.filter (large n)).erase (threeLarge n lam hcard).1) :=
    Multiset.count_pos.mpr hz_erasex
  have hcount_filter_eq : Multiset.count (threeLarge n lam hcard).2.2 (lam.filter (large n)) =
      Multiset.count (threeLarge n lam hcard).2.2 lam := by
    rw [Multiset.count_filter_of_pos (s := lam) (p := large n) hz_large]
  have hge : (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).2.1 then 1 else 0) +
        (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).1 then 1 else 0) + 1 ≤
      Multiset.count (threeLarge n lam hcard).2.2 lam := by
    rw [← hcount_filter_eq]
    have hc1 : Multiset.count (threeLarge n lam hcard).2.2 ((lam.filter (large n)).erase (threeLarge n lam hcard).1) =
        Multiset.count (threeLarge n lam hcard).2.2 (lam.filter (large n)) -
          (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).1 then 1 else 0) := by
      by_cases hzx : (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).1
      · rw [hzx]
        rw [Multiset.count_erase_self]
        simp [hzx]
      · rw [Multiset.count_erase_of_ne (by exact hzx) (lam.filter (large n))]
        simp [hzx]
    have hc2 : Multiset.count (threeLarge n lam hcard).2.2
        (((lam.filter (large n)).erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1) =
        Multiset.count (threeLarge n lam hcard).2.2 ((lam.filter (large n)).erase (threeLarge n lam hcard).1) -
          (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).2.1 then 1 else 0) := by
      by_cases hzy : (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).2.1
      · rw [hzy]
        rw [Multiset.count_erase_self]
        simp [hzy]
      · rw [Multiset.count_erase_of_ne (by exact hzy) ((lam.filter (large n)).erase (threeLarge n lam hcard).1)]
        simp [hzy]
    have h1' : (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).1 then 1 else 0) + 1 ≤
        Multiset.count (threeLarge n lam hcard).2.2 (lam.filter (large n)) := by
      rw [hc1] at hcount_erasex
      omega
    have h2' : (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).2.1 then 1 else 0) +
          (if (threeLarge n lam hcard).2.2 = (threeLarge n lam hcard).1 then 1 else 0) + 1 ≤
        Multiset.count (threeLarge n lam hcard).2.2 (lam.filter (large n)) := by
      rw [hc2] at hcount_erase_erase
      rw [hc1] at hcount_erase_erase
      omega
    exact h2'
  exact mem_erase_erase_of_count_ge hge

/-- The residual after removing the three large cycles: in `cycleTypes (n-x-y-z)`. -/
lemma erase_threeLarge_data {n : ℕ} {lam : Multiset ℕ} (hlam : lam ∈ cycleTypes n)
    (hcard : 3 ≤ (lam.filter (large n)).card) :
    (((lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1).erase
        (threeLarge n lam hcard).2.2) ∈
      cycleTypes (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 - (threeLarge n lam hcard).2.2) := by
  have hspec := threeLarge_spec n lam hcard
  have hx : (threeLarge n lam hcard).1 ∈ lam.filter (large n) := hspec.1
  have hxl : (threeLarge n lam hcard).1 ∈ lam := (Multiset.mem_filter.mp hx).1
  have hyl_erase := threeLarge_second_mem_erase (n := n) (lam := lam) hcard
  have hzl_erase := threeLarge_third_mem_erase (n := n) (lam := lam) hcard
  have hsum_le : (threeLarge n lam hcard).1 + (threeLarge n lam hcard).2.1 + (threeLarge n lam hcard).2.2 ≤ n := by
    have h1 := Multiset.sum_erase hxl
    have h2 := Multiset.sum_erase (s := lam.erase ((threeLarge n lam hcard).1)) hyl_erase
    have h3 := Multiset.sum_erase (s := (lam.erase ((threeLarge n lam hcard).1)).erase ((threeLarge n lam hcard).2.1)) hzl_erase
    have hxyz_le_sum : (threeLarge n lam hcard).1 + (threeLarge n lam hcard).2.1 + (threeLarge n lam hcard).2.2 ≤ lam.sum := by
      rw [← h1]
      rw [← h2]
      rw [← h3]
      omega
    have hsum_le' : lam.sum ≤ n := mem_cycleTypes_sum_le hlam
    omega
  have hct : (((lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1).erase
        (threeLarge n lam hcard).2.2) ∈
      cycleTypes (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 - (threeLarge n lam hcard).2.2) := by
    have h1 := mem_cycleTypes_erase n (n - (threeLarge n lam hcard).1) hlam (by
      rw [Nat.sub_sub_self (by omega : (threeLarge n lam hcard).1 ≤ n)]
      exact hxl) (by omega)
    have h2 := mem_cycleTypes_erase (n - (threeLarge n lam hcard).1)
      (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1) h1 (by
        have hsub1 : n - (threeLarge n lam hcard).1 - (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1) = (threeLarge n lam hcard).2.1 := by
          exact Nat.sub_sub_self (by omega : (threeLarge n lam hcard).2.1 ≤ n - (threeLarge n lam hcard).1)
        rw [Nat.sub_sub_self (by omega : (threeLarge n lam hcard).1 ≤ n), hsub1]
        exact hyl_erase) (by omega)
    have h3 := mem_cycleTypes_erase (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1)
      (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 - (threeLarge n lam hcard).2.2) h2 (by
        have hsub2 : n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 -
            (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 - (threeLarge n lam hcard).2.2) = (threeLarge n lam hcard).2.2 := by
          exact Nat.sub_sub_self (by omega : (threeLarge n lam hcard).2.2 ≤ n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1)
        rw [Nat.sub_sub_self (by omega : (threeLarge n lam hcard).1 ≤ n),
          Nat.sub_sub_self (by omega : (threeLarge n lam hcard).2.1 ≤ n - (threeLarge n lam hcard).1), hsub2]
        exact hzl_erase) (by omega)
    have hsub1 : n - (n - (threeLarge n lam hcard).1) = (threeLarge n lam hcard).1 := by omega
    have hsub2 : n - (threeLarge n lam hcard).1 - (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1) = (threeLarge n lam hcard).2.1 := by
      exact Nat.sub_sub_self (by omega : (threeLarge n lam hcard).2.1 ≤ n - (threeLarge n lam hcard).1)
    have hsub3 : n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 -
        (n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1 - (threeLarge n lam hcard).2.2) = (threeLarge n lam hcard).2.2 := by
      exact Nat.sub_sub_self (by omega : (threeLarge n lam hcard).2.2 ≤ n - (threeLarge n lam hcard).1 - (threeLarge n lam hcard).2.1)
    simpa [hsub1, hsub2, hsub3] using h3
  exact hct

/-- The T₃₊ term: at least three large cycles. -/
lemma sum_cycleTypeWeight_ge_three_large_le (n k : ℕ) (hk : k ∈ K n) (hn3 : 3 ≤ n) :
    (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧
        3 ≤ (lam.filter (large n)).card),
      cycleTypeWeight n lam) ≤
    ∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k,
      (1 / ((x * y * z : ℕ) : ℝ)) := by
  classical
  let s' : Finset (Multiset ℕ) := (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧
      3 ≤ (lam.filter (large n)).card)
  let t : Finset (Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ) := (largeDivs n k).sigma (fun x =>
    (largeDivs n k).sigma (fun y =>
      ((largeDivs n k).filter (fun z => x + y + z ≤ n)).sigma (fun z =>
        cycleTypes (n - x - y - z))))
  let f : Multiset ℕ → (Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ) := fun lam =>
    if h : 3 ≤ (lam.filter (large n)).card then
      ⟨(threeLarge n lam h).1, ⟨(threeLarge n lam h).2.1,
        ⟨(threeLarge n lam h).2.2,
          (((lam.erase (threeLarge n lam h).1).erase (threeLarge n lam h).2.1).erase (threeLarge n lam h).2.2)⟩⟩⟩
    else
      ⟨0, ⟨0, ⟨0, 0⟩⟩⟩
  let w' : (Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ) → ℝ := fun p =>
    cycleTypeWeight n (p.1 ::ₘ p.2.1 ::ₘ p.2.2.1 ::ₘ p.2.2.2)
  have hf_mem : ∀ lam ∈ s', f lam ∈ t := by
    intro lam hlam
    rcases Finset.mem_filter.mp hlam with ⟨hlamct, hlcm, hnk, hcard⟩
    have hres := erase_threeLarge_data hlamct hcard
    rcases threeLarge_data hlamct hlcm hnk hcard with
      ⟨hxl, hyl, hzl, hlx, hly, hlz, hxd, hyd, hzd, hxlt, hylt, hzlt⟩
    have hf : f lam = ⟨(threeLarge n lam hcard).1, ⟨(threeLarge n lam hcard).2.1,
        ⟨(threeLarge n lam hcard).2.2,
          (((lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1).erase (threeLarge n lam hcard).2.2)⟩⟩⟩ := by
      dsimp [f]
      rw [dif_pos hcard]
    rw [hf]
    have hx_divs : (threeLarge n lam hcard).1 ∈ largeDivs n k := by
      unfold largeDivs
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨hxd, by omega⟩, ⟨hxlt, hlx⟩⟩
    have hy_divs : (threeLarge n lam hcard).2.1 ∈ largeDivs n k := by
      unfold largeDivs
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨hyd, by omega⟩, ⟨hylt, hly⟩⟩
    have hz_divs : (threeLarge n lam hcard).2.2 ∈ largeDivs n k := by
      unfold largeDivs
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_divisors.mpr ⟨hzd, by omega⟩, ⟨hzlt, hlz⟩⟩
    have hxyz_le : (threeLarge n lam hcard).1 + (threeLarge n lam hcard).2.1 + (threeLarge n lam hcard).2.2 ≤ n := by
      have h1 := Multiset.sum_erase hxl
      have h2 := Multiset.sum_erase (s := lam.erase ((threeLarge n lam hcard).1)) (threeLarge_second_mem_erase (n := n) (lam := lam) hcard)
      have h3 := Multiset.sum_erase (s := (lam.erase ((threeLarge n lam hcard).1)).erase ((threeLarge n lam hcard).2.1)) (threeLarge_third_mem_erase (n := n) (lam := lam) hcard)
      have hxyz_le_sum : (threeLarge n lam hcard).1 + (threeLarge n lam hcard).2.1 + (threeLarge n lam hcard).2.2 ≤ lam.sum := by
        rw [← h1]
        rw [← h2]
        rw [← h3]
        omega
      have hsum_le' : lam.sum ≤ n := mem_cycleTypes_sum_le hlamct
      omega
    have hz_filter : (threeLarge n lam hcard).2.2 ∈
        (largeDivs n k).filter (fun z => (threeLarge n lam hcard).1 + (threeLarge n lam hcard).2.1 + z ≤ n) := by
      rw [Finset.mem_filter]
      exact ⟨hz_divs, hxyz_le⟩
    rw [Finset.mem_sigma]
    refine ⟨hx_divs, ?_⟩
    rw [Finset.mem_sigma]
    refine ⟨hy_divs, ?_⟩
    rw [Finset.mem_sigma]
    exact ⟨hz_filter, hres⟩
  have hf_inj : Set.InjOn f (↑s' : Set (Multiset ℕ)) := by
    intro lam₁ hlam₁ lam₂ hlam₂ h
    rcases Finset.mem_filter.mp hlam₁ with ⟨h₁ct, h₁lcm, h₁nk, h₁card⟩
    rcases Finset.mem_filter.mp hlam₂ with ⟨h₂ct, h₂lcm, h₂nk, h₂card⟩
    have hf₁ : f lam₁ = ⟨(threeLarge n lam₁ h₁card).1, ⟨(threeLarge n lam₁ h₁card).2.1,
        ⟨(threeLarge n lam₁ h₁card).2.2,
          (((lam₁.erase (threeLarge n lam₁ h₁card).1).erase (threeLarge n lam₁ h₁card).2.1).erase (threeLarge n lam₁ h₁card).2.2)⟩⟩⟩ := by
      dsimp [f]
      rw [dif_pos h₁card]
    have hf₂ : f lam₂ = ⟨(threeLarge n lam₂ h₂card).1, ⟨(threeLarge n lam₂ h₂card).2.1,
        ⟨(threeLarge n lam₂ h₂card).2.2,
          (((lam₂.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1).erase (threeLarge n lam₂ h₂card).2.2)⟩⟩⟩ := by
      dsimp [f]
      rw [dif_pos h₂card]
    rw [hf₁, hf₂] at h
    have hx_eq : (threeLarge n lam₁ h₁card).1 = (threeLarge n lam₂ h₂card).1 :=
      congrArg (fun p : Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ => p.1) h
    have hy_eq : (threeLarge n lam₁ h₁card).2.1 = (threeLarge n lam₂ h₂card).2.1 :=
      congrArg (fun p : Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ => p.2.1) h
    have hz_eq : (threeLarge n lam₁ h₁card).2.2 = (threeLarge n lam₂ h₂card).2.2 :=
      congrArg (fun p : Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ => p.2.2.1) h
    have hr_eq : (((lam₁.erase (threeLarge n lam₁ h₁card).1).erase (threeLarge n lam₁ h₁card).2.1).erase (threeLarge n lam₁ h₁card).2.2) =
        (((lam₂.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1).erase (threeLarge n lam₂ h₂card).2.2) :=
      congrArg (fun p : Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ => p.2.2.2) h
    have hx₁_mem : (threeLarge n lam₁ h₁card).1 ∈ lam₁ := (threeLarge_data h₁ct h₁lcm h₁nk h₁card).1
    have hx₂_mem : (threeLarge n lam₂ h₂card).1 ∈ lam₂ := (threeLarge_data h₂ct h₂lcm h₂nk h₂card).1
    have hy₁_mem := threeLarge_second_mem_erase (n := n) (lam := lam₁) h₁card
    have hy₂_mem := threeLarge_second_mem_erase (n := n) (lam := lam₂) h₂card
    have hz₁_mem := threeLarge_third_mem_erase (n := n) (lam := lam₁) h₁card
    have hz₂_mem := threeLarge_third_mem_erase (n := n) (lam := lam₂) h₂card
    rw [hx_eq, hy_eq] at hr_eq
    calc lam₁ = (threeLarge n lam₁ h₁card).1 ::ₘ lam₁.erase (threeLarge n lam₁ h₁card).1 :=
          (Multiset.cons_erase hx₁_mem).symm
      _ = (threeLarge n lam₁ h₁card).1 ::ₘ ((threeLarge n lam₁ h₁card).2.1 ::ₘ
          (lam₁.erase (threeLarge n lam₁ h₁card).1).erase (threeLarge n lam₁ h₁card).2.1) := by
          exact congrArg (fun s => (threeLarge n lam₁ h₁card).1 ::ₘ s) (Multiset.cons_erase hy₁_mem).symm
      _ = (threeLarge n lam₁ h₁card).1 ::ₘ ((threeLarge n lam₁ h₁card).2.1 ::ₘ
          ((threeLarge n lam₁ h₁card).2.2 ::ₘ
            ((lam₁.erase (threeLarge n lam₁ h₁card).1).erase (threeLarge n lam₁ h₁card).2.1).erase (threeLarge n lam₁ h₁card).2.2)) := by
          exact congrArg (fun s => (threeLarge n lam₁ h₁card).1 ::ₘ (threeLarge n lam₁ h₁card).2.1 ::ₘ s)
            (Multiset.cons_erase hz₁_mem).symm
      _ = (threeLarge n lam₂ h₂card).1 ::ₘ ((threeLarge n lam₂ h₂card).2.1 ::ₘ
          ((threeLarge n lam₂ h₂card).2.2 ::ₘ
            ((lam₂.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1).erase (threeLarge n lam₂ h₂card).2.2)) := by
          have hrest : (((lam₁.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1).erase (threeLarge n lam₂ h₂card).2.2) =
              (((lam₂.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1).erase (threeLarge n lam₂ h₂card).2.2) := by
            have h0 := congrArg (fun p : Σ x : ℕ, Σ y : ℕ, Σ z : ℕ, Multiset ℕ => p.2.2.2) h
            rw [hx_eq, hy_eq, hz_eq] at h0
            exact h0
          rw [hx_eq, hy_eq, hz_eq]
          exact congrArg (fun r => (threeLarge n lam₂ h₂card).1 ::ₘ (threeLarge n lam₂ h₂card).2.1 ::ₘ
            (threeLarge n lam₂ h₂card).2.2 ::ₘ r) hrest
      _ = lam₂ := by
          symm
          calc lam₂ = (threeLarge n lam₂ h₂card).1 ::ₘ lam₂.erase (threeLarge n lam₂ h₂card).1 :=
              (Multiset.cons_erase hx₂_mem).symm
            _ = (threeLarge n lam₂ h₂card).1 ::ₘ ((threeLarge n lam₂ h₂card).2.1 ::ₘ
                (lam₂.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1) := by
                  exact congrArg (fun s => (threeLarge n lam₂ h₂card).1 ::ₘ s) (Multiset.cons_erase hy₂_mem).symm
            _ = (threeLarge n lam₂ h₂card).1 ::ₘ ((threeLarge n lam₂ h₂card).2.1 ::ₘ
                ((threeLarge n lam₂ h₂card).2.2 ::ₘ
                  ((lam₂.erase (threeLarge n lam₂ h₂card).1).erase (threeLarge n lam₂ h₂card).2.1).erase (threeLarge n lam₂ h₂card).2.2)) := by
                  exact congrArg (fun s => (threeLarge n lam₂ h₂card).1 ::ₘ (threeLarge n lam₂ h₂card).2.1 ::ₘ s)
                    (Multiset.cons_erase hz₂_mem).symm
  have hw_eq : ∀ lam ∈ s', cycleTypeWeight n lam = w' (f lam) := by
    intro lam hlam
    rcases Finset.mem_filter.mp hlam with ⟨hlamct, hlcm, hnk, hcard⟩
    have hx_mem : (threeLarge n lam hcard).1 ∈ lam := (threeLarge_data hlamct hlcm hnk hcard).1
    have hy_mem := threeLarge_second_mem_erase (n := n) (lam := lam) hcard
    have hz_mem := threeLarge_third_mem_erase (n := n) (lam := lam) hcard
    have hf : f lam = ⟨(threeLarge n lam hcard).1, ⟨(threeLarge n lam hcard).2.1,
        ⟨(threeLarge n lam hcard).2.2,
          (((lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1).erase (threeLarge n lam hcard).2.2)⟩⟩⟩ := by
      dsimp [f]
      rw [dif_pos hcard]
    rw [hf]
    dsimp [w']
    calc cycleTypeWeight n lam
        = cycleTypeWeight n ((threeLarge n lam hcard).1 ::ₘ lam.erase (threeLarge n lam hcard).1) := by
            exact congrArg (fun s => cycleTypeWeight n s) (Multiset.cons_erase hx_mem).symm
      _ = cycleTypeWeight n ((threeLarge n lam hcard).1 ::ₘ (threeLarge n lam hcard).2.1 ::ₘ
          (lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1) := by
            exact congrArg (fun s => cycleTypeWeight n ((threeLarge n lam hcard).1 ::ₘ s))
              (Multiset.cons_erase hy_mem).symm
      _ = cycleTypeWeight n ((threeLarge n lam hcard).1 ::ₘ (threeLarge n lam hcard).2.1 ::ₘ (threeLarge n lam hcard).2.2 ::ₘ
          ((lam.erase (threeLarge n lam hcard).1).erase (threeLarge n lam hcard).2.1).erase (threeLarge n lam hcard).2.2) := by
            exact congrArg (fun s => cycleTypeWeight n ((threeLarge n lam hcard).1 ::ₘ (threeLarge n lam hcard).2.1 ::ₘ s))
              (Multiset.cons_erase hz_mem).symm
  have hsum_image : (∑ p ∈ s'.image f, w' p) = ∑ lam ∈ s', cycleTypeWeight n lam := by
    rw [Finset.sum_image hf_inj]
    apply Finset.sum_congr rfl
    intro lam hlam
    exact (hw_eq lam hlam).symm
  have himage_subset : s'.image f ⊆ t := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨lam, hlam, rfl⟩
    exact hf_mem lam hlam
  have hstep : ∑ lam ∈ s', cycleTypeWeight n lam ≤ ∑ p ∈ t, w' p := by
    rw [← hsum_image]
    refine Finset.sum_le_sum_of_subset_of_nonneg himage_subset ?_
    intro p hp hnot
    unfold w' cycleTypeWeight
    positivity
  have hsum_sigma : (∑ p ∈ t, w' p) = ∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k,
      ∑ z ∈ (largeDivs n k).filter (fun z => x + y + z ≤ n),
        ∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.sum_sigma]
  have hdec : ∀ x ∈ largeDivs n k, ∀ y ∈ largeDivs n k,
      ∀ z ∈ (largeDivs n k).filter (fun z => x + y + z ≤ n),
      (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam)) ≤
      (1 / ((x * y * z : ℕ) : ℝ)) := by
    intro x hx y hy z hz'
    have hz : z ∈ largeDivs n k := (Finset.mem_filter.mp hz').1
    have hxyz_le : x + y + z ≤ n := (Finset.mem_filter.mp hz').2
    have hx2 : 2 ≤ x := by
      have hlarge : large n x := mem_largeDivs_large hx
      unfold large at hlarge
      have hnR : (1 : ℝ) < (n : ℝ)^(13/14 : ℝ) := by
        have hn2 : 2 ≤ n := by omega
        have h1 : (1 : ℝ) < (2 : ℝ)^(13/14 : ℝ) := by
          have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < (2 : ℝ))
            (by norm_num : (0 : ℝ) < (13/14 : ℝ))
          simpa [Real.one_rpow] using h
        have h2 : (2 : ℝ)^(13/14 : ℝ) ≤ (n : ℝ)^(13/14 : ℝ) := by
          exact Real.rpow_le_rpow (by norm_num : 0 ≤ (2:ℝ)) (by exact_mod_cast hn2) (by norm_num : 0 ≤ (13/14:ℝ))
        exact lt_of_lt_of_le h1 h2
      have hd_gt1 : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le hnR hlarge
      have hd_pos : 0 < x := by
        have : (0 : ℝ) < (x : ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hd_gt1
        exact_mod_cast this
      have hd_ne1 : x ≠ 1 := by
        intro h
        have : (x : ℝ) = 1 := by rw [h]; norm_num
        linarith
      omega
    have hy2 : 2 ≤ y := by
      have hlarge : large n y := mem_largeDivs_large hy
      unfold large at hlarge
      have hnR : (1 : ℝ) < (n : ℝ)^(13/14 : ℝ) := by
        have hn2 : 2 ≤ n := by omega
        have h1 : (1 : ℝ) < (2 : ℝ)^(13/14 : ℝ) := by
          have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < (2 : ℝ))
            (by norm_num : (0 : ℝ) < (13/14 : ℝ))
          simpa [Real.one_rpow] using h
        have h2 : (2 : ℝ)^(13/14 : ℝ) ≤ (n : ℝ)^(13/14 : ℝ) := by
          exact Real.rpow_le_rpow (by norm_num : 0 ≤ (2:ℝ)) (by exact_mod_cast hn2) (by norm_num : 0 ≤ (13/14:ℝ))
        exact lt_of_lt_of_le h1 h2
      have hd_gt1 : (1 : ℝ) < (y : ℝ) := lt_of_lt_of_le hnR hlarge
      have hd_pos : 0 < y := by
        have : (0 : ℝ) < (y : ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hd_gt1
        exact_mod_cast this
      have hd_ne1 : y ≠ 1 := by
        intro h
        have : (y : ℝ) = 1 := by rw [h]; norm_num
        linarith
      omega
    have hz2 : 2 ≤ z := by
      have hlarge : large n z := mem_largeDivs_large hz
      unfold large at hlarge
      have hnR : (1 : ℝ) < (n : ℝ)^(13/14 : ℝ) := by
        have hn2 : 2 ≤ n := by omega
        have h1 : (1 : ℝ) < (2 : ℝ)^(13/14 : ℝ) := by
          have h := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < (2 : ℝ))
            (by norm_num : (0 : ℝ) < (13/14 : ℝ))
          simpa [Real.one_rpow] using h
        have h2 : (2 : ℝ)^(13/14 : ℝ) ≤ (n : ℝ)^(13/14 : ℝ) := by
          exact Real.rpow_le_rpow (by norm_num : 0 ≤ (2:ℝ)) (by exact_mod_cast hn2) (by norm_num : 0 ≤ (13/14:ℝ))
        exact lt_of_lt_of_le h1 h2
      have hd_gt1 : (1 : ℝ) < (z : ℝ) := lt_of_lt_of_le hnR hlarge
      have hd_pos : 0 < z := by
        have : (0 : ℝ) < (z : ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hd_gt1
        exact_mod_cast this
      have hd_ne1 : z ≠ 1 := by
        intro h
        have : (z : ℝ) = 1 := by rw [h]; norm_num
        linarith
      omega
    have hdec_point : ∀ lam ∈ cycleTypes (n - x - y - z),
        cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam) ≤
          (1 / ((x * y * z : ℕ) : ℝ)) * cycleTypeWeight (n - x - y - z) lam := by
      intro lam hlam
      have hlam2 : ∀ a ∈ lam, 2 ≤ a := mem_cycleTypes_two_le hlam
      have hlamsum : lam.sum ≤ n - x - y - z := mem_cycleTypes_sum_le hlam
      have h1 := cycleTypeWeight_cons_le n x (y ::ₘ z ::ₘ lam) hx2
        (by intro a ha
            rcases Multiset.mem_cons.mp ha with (hay | hazlam)
            · rw [hay]; exact hy2
            · rcases Multiset.mem_cons.mp hazlam with (haz | hal)
              · rw [haz]; exact hz2
              · exact hlam2 a hal)
        (by
          have h : x + (y + (z + lam.sum)) ≤ n := by omega
          simpa [Multiset.sum_cons] using h)
      have h2 := cycleTypeWeight_cons_le (n - x) y (z ::ₘ lam) hy2
        (by intro a ha
            rcases Multiset.mem_cons.mp ha with (haz | hal)
            · rw [haz]; exact hz2
            · exact hlam2 a hal)
        (by
          have h : y + (z + lam.sum) ≤ n - x := by omega
          simpa [Multiset.sum_cons] using h)
      have h3 := cycleTypeWeight_cons_le (n - x - y) z lam hz2 hlam2 (by omega : z + lam.sum ≤ n - x - y)
      calc cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam)
          ≤ (1 / (x : ℝ)) * cycleTypeWeight (n - x) (y ::ₘ z ::ₘ lam) := h1
        _ ≤ (1 / (x : ℝ)) * ((1 / (y : ℝ)) * cycleTypeWeight (n - x - y) (z ::ₘ lam)) := by
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (1 / (x : ℝ)) * ((1 / (y : ℝ)) * ((1 / (z : ℝ)) * cycleTypeWeight (n - x - y - z) lam)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (1 / ((x * y * z : ℕ) : ℝ)) * cycleTypeWeight (n - x - y - z) lam := by
              rw [Nat.cast_mul, Nat.cast_mul]
              field_simp [show (x : ℝ) ≠ 0 by positivity, show (y : ℝ) ≠ 0 by positivity,
                show (z : ℝ) ≠ 0 by positivity]
    have hsum_le : (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam)) ≤
        (1 / ((x * y * z : ℕ) : ℝ)) *
          (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight (n - x - y - z) lam) := by
      calc (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam))
          ≤ ∑ lam ∈ cycleTypes (n - x - y - z),
              (1 / ((x * y * z : ℕ) : ℝ)) * cycleTypeWeight (n - x - y - z) lam := by
              exact Finset.sum_le_sum (fun lam hlam => hdec_point lam hlam)
        _ = (1 / ((x * y * z : ℕ) : ℝ)) *
            (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight (n - x - y - z) lam) := by
              rw [Finset.mul_sum]
    have hsum_eq_one : (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight (n - x - y - z) lam) = 1 :=
      sum_cycleTypeWeight_eq_one (n - x - y - z)
    calc (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam))
        ≤ (1 / ((x * y * z : ℕ) : ℝ)) *
            (∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight (n - x - y - z) lam) := hsum_le
      _ = (1 / ((x * y * z : ℕ) : ℝ)) * 1 := by rw [hsum_eq_one]
      _ = (1 / ((x * y * z : ℕ) : ℝ)) := by ring
  have hfinal : (∑ p ∈ t, w' p) ≤ ∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k,
      (1 / ((x * y * z : ℕ) : ℝ)) := by
    rw [hsum_sigma]
    refine Finset.sum_le_sum ?_
    intro x hx
    refine Finset.sum_le_sum ?_
    intro y hy
    calc (∑ z ∈ (largeDivs n k).filter (fun z => x + y + z ≤ n),
          ∑ lam ∈ cycleTypes (n - x - y - z), cycleTypeWeight n (x ::ₘ y ::ₘ z ::ₘ lam))
        ≤ ∑ z ∈ (largeDivs n k).filter (fun z => x + y + z ≤ n), (1 / ((x * y * z : ℕ) : ℝ)) := by
            exact Finset.sum_le_sum (fun z hz => hdec x hx y hy z hz)
      _ ≤ ∑ z ∈ largeDivs n k, (1 / ((x * y * z : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro z hz
              exact (Finset.mem_filter.mp hz).1
            · intro z hz hnot
              positivity
  calc (∑ lam ∈ s', cycleTypeWeight n lam)
      ≤ ∑ p ∈ t, w' p := hstep
    _ ≤ ∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k,
        (1 / ((x * y * z : ℕ) : ℝ)) := hfinal

/-- Splitting a sum by the number of large cycles: `card = 0`, `= 1`, `= 2`, `≥ 3`. -/
lemma sum_eq_filter_card_parts (n : ℕ) {s : Finset (Multiset ℕ)} (w : Multiset ℕ → ℝ) :
    (∑ lam ∈ s, w lam) =
      (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) +
      (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 1), w lam) +
      (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 2), w lam) +
      (∑ lam ∈ s.filter (fun lam => 3 ≤ (lam.filter (large n)).card), w lam) := by
  have h2 := Finset.sum_filter_add_sum_filter_not (s := s.filter (fun lam => ¬ (lam.filter (large n)).card = 0))
    (p := fun lam => (lam.filter (large n)).card = 1) (f := w)
  have h3 := Finset.sum_filter_add_sum_filter_not
    (s := (s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter (fun lam => ¬ (lam.filter (large n)).card = 1))
    (p := fun lam => (lam.filter (large n)).card = 2) (f := w)
  have hf1 : (s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter (fun lam => (lam.filter (large n)).card = 1) =
      s.filter (fun lam => (lam.filter (large n)).card = 1) := by
    ext lam
    simp only [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨⟨hmem, h0⟩, h1⟩
      exact ⟨hmem, h1⟩
    · intro h
      rcases h with ⟨hmem, h1⟩
      exact ⟨⟨hmem, by omega⟩, h1⟩
  have hf2 : ((s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter (fun lam => ¬ (lam.filter (large n)).card = 1)).filter (fun lam => (lam.filter (large n)).card = 2) =
      s.filter (fun lam => (lam.filter (large n)).card = 2) := by
    ext lam
    simp only [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨⟨⟨hmem, h0⟩, h1⟩, h2⟩
      exact ⟨hmem, h2⟩
    · intro h
      rcases h with ⟨hmem, h2⟩
      exact ⟨⟨⟨hmem, by omega⟩, by omega⟩, h2⟩
  have hf3 : ((s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter (fun lam => ¬ (lam.filter (large n)).card = 1)).filter (fun lam => ¬ (lam.filter (large n)).card = 2) =
      s.filter (fun lam => 3 ≤ (lam.filter (large n)).card) := by
    ext lam
    simp only [Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨⟨⟨hmem, h0⟩, h1⟩, h2⟩
      exact ⟨hmem, by omega⟩
    · intro h
      rcases h with ⟨hmem, h3⟩
      exact ⟨⟨⟨hmem, by omega⟩, by omega⟩, by omega⟩
  calc (∑ lam ∈ s, w lam)
      = (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) +
          (∑ lam ∈ s.filter (fun lam => ¬ (lam.filter (large n)).card = 0), w lam) := by
            exact (Finset.sum_filter_add_sum_filter_not (s := s)
              (p := fun lam => (lam.filter (large n)).card = 0) (f := w)).symm
    _ = (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) +
          ((∑ lam ∈ (s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter
            (fun lam => (lam.filter (large n)).card = 1), w lam) +
          (∑ lam ∈ (s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter
            (fun lam => ¬ (lam.filter (large n)).card = 1), w lam)) := by
            exact congrArg (fun t => (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) + t) h2.symm
    _ = (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) +
          ((∑ lam ∈ (s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter
            (fun lam => (lam.filter (large n)).card = 1), w lam) +
          ((∑ lam ∈ ((s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter
            (fun lam => ¬ (lam.filter (large n)).card = 1)).filter
            (fun lam => (lam.filter (large n)).card = 2), w lam) +
          (∑ lam ∈ ((s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter
            (fun lam => ¬ (lam.filter (large n)).card = 1)).filter
            (fun lam => ¬ (lam.filter (large n)).card = 2), w lam))) := by
            exact congrArg (fun t => (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) +
                ((∑ lam ∈ (s.filter (fun lam => ¬ (lam.filter (large n)).card = 0)).filter
                  (fun lam => (lam.filter (large n)).card = 1), w lam) + t)) h3.symm
    _ = (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) +
          (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 1), w lam) +
          (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 2), w lam) +
          (∑ lam ∈ s.filter (fun lam => 3 ≤ (lam.filter (large n)).card), w lam) := by
            rw [hf1, hf2, hf3]
            simp [add_assoc]

/-- `∑_{d ∈ largeDivs n k} 1/d ≤ τ(n-k) · n^(-13/14)`. -/
lemma sum_inv_largeDivs_le (n k : ℕ) (hn : 0 < n) :
    (∑ d ∈ largeDivs n k, (1 : ℝ) / (d : ℝ)) ≤
      (tau (n - k) : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) := by
  have hpoint : ∀ d ∈ largeDivs n k, (1 : ℝ) / (d : ℝ) ≤ (n : ℝ)^(-(13/14 : ℝ)) := by
    intro d hd
    have hlarge : large n d := mem_largeDivs_large hd
    unfold large at hlarge
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnpow_pos : 0 < (n : ℝ)^(13/14 : ℝ) := Real.rpow_pos_of_pos hnR _
    have hdpos : 0 < (d : ℝ) := by
      have hdlt : d < n - k := mem_largeDivs_lt hd
      have hd_dvd : d ∣ n - k := mem_largeDivs_dvd hd
      have hd_ne : d ≠ 0 := by
        intro h0
        rw [h0] at hdlt
        have hmem : d ∈ (n - k).divisors := by
          unfold largeDivs at hd
          exact (Finset.mem_filter.mp hd).1
        rw [h0] at hmem
        have : 0 ∉ (n - k).divisors := by
          rw [Nat.mem_divisors]
          omega
        exact this hmem
      exact_mod_cast (by omega : 0 < d)
    have hle : 1 / (d : ℝ) ≤ 1 / (n : ℝ)^(13/14 : ℝ) := by
      exact one_div_le_one_div_of_le hnpow_pos hlarge
    rw [one_div]
    have hrpow : 1 / (n : ℝ)^(13/14 : ℝ) = (n : ℝ)^(-(13/14 : ℝ)) := by
      rw [one_div, Real.rpow_neg (by exact_mod_cast (Nat.zero_le n)) (13/14 : ℝ)]
    simpa [hrpow] using hle
  have hsum : (∑ d ∈ largeDivs n k, (1 : ℝ) / (d : ℝ)) ≤
      ∑ d ∈ largeDivs n k, (n : ℝ)^(-(13/14 : ℝ)) :=
    Finset.sum_le_sum (fun d hd => hpoint d hd)
  calc (∑ d ∈ largeDivs n k, (1 : ℝ) / (d : ℝ))
      ≤ ∑ d ∈ largeDivs n k, (n : ℝ)^(-(13/14 : ℝ)) := hsum
    _ = (largeDivs n k).card * (n : ℝ)^(-(13/14 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (tau (n - k) : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (largeDivs_card_le_tau n k))
            (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le n)) _)

/-- The reverse direction: in the interesting case (`k ∈ Kₙ`, `2^⌊log₂ k⌋+1 ∤ n-k`),
`2^⌊log₂ k⌋ ∈ μ` forces `lcm((n-k)/2, μ.lcm) = n-k`. -/
lemma lcm_eq_two_mul_of_mem_two_pow_log2 (n k : ℕ) (hk : k ∈ K n) (hk2 : 2 ≤ k)
    (hdiv : 2 ∣ n - k) (hnot : ¬ 2 ^ (Nat.log 2 k + 1) ∣ n - k) {μ : Multiset ℕ}
    (hμ : μ ∈ cycleTypes k) (hmem : 2 ^ Nat.log 2 k ∈ μ) :
    Nat.lcm ((n - k) / 2) μ.lcm = n - k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk_lt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hs_pos : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) (by omega : 2 ≤ k)
  have h2s_dvd : 2 ^ Nat.log 2 k ∣ n - k := two_pow_log2_dvd_of_mem_K hk hk2
  have hs_val : padicValNat 2 (n - k) = Nat.log 2 k :=
    padicValNat_nk_eq_log2_of_not_two_pow_succ_dvd hk hk2 hnot
  have hnk_pos : n - k ≠ 0 := by omega
  let m : ℕ := (n - k) / 2 ^ Nat.log 2 k
  have h2sm : 2 ^ Nat.log 2 k * m = n - k := by
    dsimp [m]
    have hc := Nat.div_mul_cancel h2s_dvd
    simpa [Nat.mul_comm] using hc
  have hpow_ne : 2 ^ Nat.log 2 k ≠ 0 := by positivity
  have hm_ne : m ≠ 0 := by
    intro h0
    rw [h0] at h2sm
    have : n - k = 0 := by simpa using h2sm.symm
    omega
  have hm_odd : Odd m := by
    have hval := padicValNat.mul (p := 2) hpow_ne hm_ne
    rw [h2sm, hs_val] at hval
    have hval2s : padicValNat 2 (2 ^ Nat.log 2 k) = Nat.log 2 k := by
      rw [padicValNat.pow (p := 2) (a := 2) (n := Nat.log 2 k) (by norm_num : (2 : ℕ) ≠ 0)]
      rw [padicValNat_self]
      ring
    rw [hval2s] at hval
    have hval_m : padicValNat 2 m = 0 := by omega
    have hnot2 : ¬ 2 ∣ m := by
      intro h2m
      have h1 : 1 ≤ padicValNat 2 m := (padicValNat_dvd_iff_le (p := 2) (a := m) (n := 1) hm_ne).mp h2m
      omega
    exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hnot2)
  have hcop : Nat.Coprime (2 ^ Nat.log 2 k) m := by
    have h2cop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm_odd
    exact Nat.Coprime.pow_left (m := 2) (k := m) (Nat.log 2 k) h2cop
  have h2s_dvd_lcm : 2 ^ Nat.log 2 k ∣ Nat.lcm ((n - k) / 2) μ.lcm := by
    have h2s_dvd_μ : 2 ^ Nat.log 2 k ∣ μ.lcm := Multiset.dvd_lcm hmem
    exact dvd_trans h2s_dvd_μ (dvd_lcm_right _ _)
  have ha : (n - k) / 2 = 2 ^ (Nat.log 2 k - 1) * m := by
    have hsub : Nat.log 2 k - 1 + 1 = Nat.log 2 k := Nat.sub_add_cancel hs_pos
    have h2sm' : 2 * (2 ^ (Nat.log 2 k - 1) * m) = n - k := by
      calc 2 * (2 ^ (Nat.log 2 k - 1) * m) = (2 * 2 ^ (Nat.log 2 k - 1)) * m := by rw [mul_assoc]
        _ = (2 ^ (Nat.log 2 k - 1) * 2) * m := by rw [Nat.mul_comm 2 (2 ^ (Nat.log 2 k - 1))]
        _ = 2 ^ (Nat.log 2 k - 1 + 1) * m := by rw [pow_succ]
        _ = 2 ^ Nat.log 2 k * m := by rw [hsub]
        _ = n - k := h2sm
    calc (n - k) / 2 = (2 * (2 ^ (Nat.log 2 k - 1) * m)) / 2 := by rw [h2sm']
      _ = 2 ^ (Nat.log 2 k - 1) * m := by
          exact Nat.mul_div_right (2 ^ (Nat.log 2 k - 1) * m) (by norm_num : 0 < (2 : ℕ))
  have hm_dvd_lcm : m ∣ Nat.lcm ((n - k) / 2) μ.lcm := by
    rw [ha]
    exact dvd_trans (dvd_mul_left m (2 ^ (Nat.log 2 k - 1))) (dvd_lcm_left _ _)
  have hnk_dvd_lcm : 2 ^ Nat.log 2 k * m ∣ Nat.lcm ((n - k) / 2) μ.lcm :=
    hcop.mul_dvd_of_dvd_of_dvd h2s_dvd_lcm hm_dvd_lcm
  have hlcm_dvd_nk : Nat.lcm ((n - k) / 2) μ.lcm ∣ n - k := by
    apply Nat.lcm_dvd
    · have ha_dvd : (n - k) / 2 ∣ n - k := by
        refine ⟨2, ?_⟩
        have hc := Nat.div_mul_cancel hdiv
        exact hc.symm
      exact ha_dvd
    · have hμ_lcm_dvd : μ.lcm ∣ lcm1to k := lcm_dvd_lcm1to_of_cycleTypes hμ
      exact dvd_trans hμ_lcm_dvd (Finset.mem_filter.mp hk).2
  exact Nat.dvd_antisymm hlcm_dvd_nk (by
    have h : n - k ∣ Nat.lcm ((n - k) / 2) μ.lcm := by
      simpa [h2sm] using hnk_dvd_lcm
    exact h)

/-- `n^(13/14) ≤ n/4` for `n ≥ 2^28` (so `a = (n-k)/2` is large when `k ≤ n/2`). -/
lemma rpow_nine_tenth_le_div_four {n : ℕ} (hn : 2^28 ≤ n) : (n : ℝ)^(13/14 : ℝ) ≤ (n : ℝ) / 4 := by
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [le_div_iff₀ (by norm_num : 0 < (4 : ℝ))]
  have h4 : (4 : ℝ) ≤ (n : ℝ)^(1/14 : ℝ) := by
    by_contra h
    have hlt : (n : ℝ)^(1/14 : ℝ) < 4 := lt_of_not_ge h
    have hpow10 : ((n : ℝ)^(1/14 : ℝ))^14 < (4 : ℝ)^14 := by
      exact pow_lt_pow_left₀ hlt (Real.rpow_nonneg hn0 _) (by norm_num : (14 : ℕ) ≠ 0)
    have h10 : ((n : ℝ)^(1/14 : ℝ))^14 = (n : ℝ) := by
      rw [show ((n : ℝ)^(1/14 : ℝ))^14 = ((n : ℝ)^(1/14 : ℝ))^(14 : ℝ) by
        exact (Real.rpow_natCast ((n : ℝ)^(1/14 : ℝ)) 14).symm]
      rw [show ((n : ℝ)^(1/14 : ℝ))^(14 : ℝ) = (n : ℝ)^((1/14 : ℝ) * 14) by
        exact (Real.rpow_mul hn0 (1/14 : ℝ) 14).symm]
      norm_num
    rw [h10] at hpow10
    norm_num at hpow10
    have hn20' : (2 : ℝ)^28 ≤ (n : ℝ) := by exact_mod_cast hn
    norm_num at hn20'
    linarith
  have hmain : 4 * (n : ℝ)^(13/14 : ℝ) ≤ (n : ℝ)^(1/14 : ℝ) * (n : ℝ)^(13/14 : ℝ) := by
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hn0 _)
  have hprod : (n : ℝ)^(1/14 : ℝ) * (n : ℝ)^(13/14 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnpos (1/14 : ℝ) (13/14 : ℝ)]
    norm_num
  calc (n : ℝ)^(13/14 : ℝ) * 4 ≤ (n : ℝ)^(1/14 : ℝ) * (n : ℝ)^(13/14 : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    _ = (n : ℝ) := hprod

/-- `η ≤ T₂s + T₃`: each `2^⌊log₂ k⌋`-cycle contribution lands either in the special pair
(`2^⌊log₂ k⌋` not large) or in the `≥ 3` large-cycles term (otherwise). -/
lemma eta_le_special_add_ge_three (n k : ℕ) (hk : k ∈ K n) (hn20 : 2^28 ≤ n) :
    eta n k ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam),
        cycleTypeWeight n lam) +
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card),
        cycleTypeWeight n lam) := by
  classical
  have hn10 : 10 ≤ n := by omega
  by_cases hdiv : 2 ∣ n - k
  · by_cases hk2 : 2 ≤ k
    · by_cases hdvd : 2 ^ (Nat.log 2 k + 1) ∣ n - k
      · -- η = 0
        rw [eta_eq_zero_of_dvd n k hdvd]
        have h1 : 0 ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) := by
          exact Finset.sum_nonneg (by intro lam hlam; unfold cycleTypeWeight; positivity)
        have h2 : 0 ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
          exact Finset.sum_nonneg (by intro lam hlam; unfold cycleTypeWeight; positivity)
        exact add_nonneg h1 h2
      · -- interesting case
        let a := (n - k) / 2
        have hgt : k < a := by
          dsimp [a]
          exact k_lt_half_of_mem_K hn10 hk hk2 hdvd
        have ha2 : 2 ≤ a := by omega
        have h2a : 2 * a = n - k := by
          dsimp [a]
          have hc := Nat.div_mul_cancel hdiv
          simpa [Nat.mul_comm] using hc
        have hη := special_cycleTypeWeight_sum_eq_eta n k hk2 hdiv ha2 hgt hdvd
        have halarge : large n a := by
          dsimp [a, large]
          have h1 : (n : ℝ)^(13/14 : ℝ) ≤ (n : ℝ) / 4 := rpow_nine_tenth_le_div_four hn20
          have h2 : (n : ℝ) / 4 ≤ (a : ℝ) := by
            have hnk : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by
              have hk_lt_sub : k < n - k := k_lt_sub_of_mem_K hk (by omega : 5 ≤ n)
              exact_mod_cast (by omega : n ≤ 2 * (n - k))
            have h2a' : 2 * (a : ℝ) = ((n - k : ℕ) : ℝ) := by
              exact_mod_cast h2a
            nlinarith
          exact le_trans h1 h2
        -- split t' into no-large and has-large parts
        have hsplit : (∑ μ ∈ (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ), cycleTypeWeight n (a ::ₘ a ::ₘ μ)) =
            (∑ μ ∈ ((cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)).filter (fun μ => (μ.filter (large n)).card = 0),
              cycleTypeWeight n (a ::ₘ a ::ₘ μ)) +
            (∑ μ ∈ ((cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)).filter (fun μ => ¬ (μ.filter (large n)).card = 0),
              cycleTypeWeight n (a ::ₘ a ::ₘ μ)) := by
          exact (Finset.sum_filter_add_sum_filter_not
            (s := (cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ))
            (p := fun μ => (μ.filter (large n)).card = 0)
            (f := fun μ => cycleTypeWeight n (a ::ₘ a ::ₘ μ))).symm
        have hle0 : (∑ μ ∈ ((cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)).filter (fun μ => (μ.filter (large n)).card = 0),
            cycleTypeWeight n (a ::ₘ a ::ₘ μ)) ≤
            (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) := by
          let g : Multiset ℕ → Multiset ℕ := fun μ => a ::ₘ a ::ₘ μ
          let s₀ : Finset (Multiset ℕ) := ((cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)).filter (fun μ => (μ.filter (large n)).card = 0)
          have hg_mem : ∀ μ ∈ s₀, g μ ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam) := by
            intro μ hμ
            rcases Finset.mem_filter.mp hμ with ⟨hμt', hμ0⟩
            rcases Finset.mem_filter.mp hμt' with ⟨hμct, hmem⟩
            rw [Finset.mem_filter]
            have hμsum : μ.sum ≤ k := mem_cycleTypes_sum_le hμct
            have hct : a ::ₘ a ::ₘ μ ∈ cycleTypes n := by
              have hk_eq : k = n - 2 * a := by omega
              have h3 := mem_cycleTypes_cons (n - a) (n - 2 * a)
                (by simpa [hk_eq] using hμct : μ ∈ cycleTypes (n - 2 * a))
                (by omega : 2 ≤ n - a - (n - 2 * a)) (by omega : n - 2 * a ≤ n - a)
              have h4 := mem_cycleTypes_cons n (n - a) h3 (by omega : 2 ≤ n - (n - a)) (by omega : n - a ≤ n)
              have hsub : n - a - (n - 2 * a) = a := by omega
              simpa [Nat.sub_sub_self (by omega : a ≤ n), hsub] using h4
            have hlcm : (a ::ₘ a ::ₘ μ).lcm = n - k := by
              rw [Multiset.lcm_cons, Multiset.lcm_cons]
              rw [show lcm a (lcm a μ.lcm) = lcm (lcm a a) μ.lcm by
                exact (lcm_assoc a a μ.lcm).symm]
              rw [show lcm a a = a by exact Nat.lcm_self a]
              simpa [a] using (lcm_eq_two_mul_of_mem_two_pow_log2 n k hk hk2 hdiv hdvd hμct hmem)
            have hnk : n - k ∉ a ::ₘ a ::ₘ μ := by
              intro h
              rcases Multiset.mem_cons.mp h with (h1 | h2)
              · have : a = n - k := by simpa [h1]
                omega
              · rcases Multiset.mem_cons.mp h2 with (h3 | h4)
                · have : a = n - k := by simpa [h3]
                  omega
                · have hle : n - k ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) (n - k) h4
                  have hlt : k < n - k := k_lt_sub_of_mem_K hk (by omega : 5 ≤ n)
                  omega
            have hpair : specialPair n k (a ::ₘ a ::ₘ μ) := by
              dsimp [specialPair]
              have hfilter : (a ::ₘ a ::ₘ μ).filter (large n) = a ::ₘ a ::ₘ μ.filter (large n) := by
                rw [Multiset.filter_cons_of_pos (s := a ::ₘ μ) halarge]
                rw [Multiset.filter_cons_of_pos (s := μ) halarge]
              have hμ0' : μ.filter (large n) = 0 := by
                have hcard : (μ.filter (large n)).card = 0 := hμ0
                exact Multiset.card_eq_zero.mp hcard
              rw [hfilter, hμ0']
              simp [a]
            exact ⟨hct, hlcm, hnk, hpair⟩
          have hg_inj : Set.InjOn g (↑s₀ : Set (Multiset ℕ)) := by
            intro μ₁ hμ₁ μ₂ hμ₂ h
            dsimp [g] at h
            have h1 : a ::ₘ μ₁ = a ::ₘ μ₂ := (Multiset.cons_inj_right a).mp h
            exact (Multiset.cons_inj_right a).mp h1
          have hsum_image : (∑ lam ∈ s₀.image g, cycleTypeWeight n lam) = ∑ μ ∈ s₀, cycleTypeWeight n (a ::ₘ a ::ₘ μ) := by
            rw [Finset.sum_image hg_inj]
          have himage_subset : s₀.image g ⊆ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam) := by
            intro lam hlam
            rcases Finset.mem_image.mp hlam with ⟨μ, hμ, rfl⟩
            exact hg_mem μ hμ
          calc (∑ μ ∈ s₀, cycleTypeWeight n (a ::ₘ a ::ₘ μ))
              = ∑ lam ∈ s₀.image g, cycleTypeWeight n lam := hsum_image.symm
            _ ≤ ∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg himage_subset ?_
                  intro lam hlam hnot
                  unfold cycleTypeWeight
                  positivity
        have hlePlus : (∑ μ ∈ ((cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)).filter (fun μ => ¬ (μ.filter (large n)).card = 0),
            cycleTypeWeight n (a ::ₘ a ::ₘ μ)) ≤
            (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
          let g : Multiset ℕ → Multiset ℕ := fun μ => a ::ₘ a ::ₘ μ
          let sPlus : Finset (Multiset ℕ) := ((cycleTypes k).filter (fun μ => 2 ^ Nat.log 2 k ∈ μ)).filter (fun μ => ¬ (μ.filter (large n)).card = 0)
          have hg_mem : ∀ μ ∈ sPlus, g μ ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card) := by
            intro μ hμ
            rcases Finset.mem_filter.mp hμ with ⟨hμt', hμne0⟩
            rcases Finset.mem_filter.mp hμt' with ⟨hμct, hmem⟩
            rw [Finset.mem_filter]
            have hμsum : μ.sum ≤ k := mem_cycleTypes_sum_le hμct
            have hct : a ::ₘ a ::ₘ μ ∈ cycleTypes n := by
              have hk_eq : k = n - 2 * a := by omega
              have h3 := mem_cycleTypes_cons (n - a) (n - 2 * a)
                (by simpa [hk_eq] using hμct : μ ∈ cycleTypes (n - 2 * a))
                (by omega : 2 ≤ n - a - (n - 2 * a)) (by omega : n - 2 * a ≤ n - a)
              have h4 := mem_cycleTypes_cons n (n - a) h3 (by omega : 2 ≤ n - (n - a)) (by omega : n - a ≤ n)
              have hsub : n - a - (n - 2 * a) = a := by omega
              simpa [Nat.sub_sub_self (by omega : a ≤ n), hsub] using h4
            have hlcm : (a ::ₘ a ::ₘ μ).lcm = n - k := by
              rw [Multiset.lcm_cons, Multiset.lcm_cons]
              rw [show lcm a (lcm a μ.lcm) = lcm (lcm a a) μ.lcm by
                exact (lcm_assoc a a μ.lcm).symm]
              rw [show lcm a a = a by exact Nat.lcm_self a]
              simpa [a] using (lcm_eq_two_mul_of_mem_two_pow_log2 n k hk hk2 hdiv hdvd hμct hmem)
            have hnk : n - k ∉ a ::ₘ a ::ₘ μ := by
              intro h
              rcases Multiset.mem_cons.mp h with (h1 | h2)
              · have : a = n - k := by simpa [h1]
                omega
              · rcases Multiset.mem_cons.mp h2 with (h3 | h4)
                · have : a = n - k := by simpa [h3]
                  omega
                · have hle : n - k ≤ μ.sum := Multiset.single_le_sum (fun x _ => Nat.zero_le x) (n - k) h4
                  have hlt : k < n - k := k_lt_sub_of_mem_K hk (by omega : 5 ≤ n)
                  omega
            have hcard : 3 ≤ ((a ::ₘ a ::ₘ μ).filter (large n)).card := by
              have hfilter : (a ::ₘ a ::ₘ μ).filter (large n) = a ::ₘ a ::ₘ μ.filter (large n) := by
                rw [Multiset.filter_cons_of_pos (s := a ::ₘ μ) halarge]
                rw [Multiset.filter_cons_of_pos (s := μ) halarge]
              rw [hfilter]
              have hcardpos : 0 < (μ.filter (large n)).card := by
                exact Multiset.card_pos.mpr (by
                  intro h0
                  have hcard0 : (μ.filter (large n)).card = 0 := by simpa using h0
                  exact hμne0 hcard0)
              simp only [Multiset.card_cons]
              omega
            exact ⟨hct, hlcm, hnk, hcard⟩
          have hg_inj : Set.InjOn g (↑sPlus : Set (Multiset ℕ)) := by
            intro μ₁ hμ₁ μ₂ hμ₂ h
            dsimp [g] at h
            have h1 : a ::ₘ μ₁ = a ::ₘ μ₂ := (Multiset.cons_inj_right a).mp h
            exact (Multiset.cons_inj_right a).mp h1
          have hsum_image : (∑ lam ∈ sPlus.image g, cycleTypeWeight n lam) = ∑ μ ∈ sPlus, cycleTypeWeight n (a ::ₘ a ::ₘ μ) := by
            rw [Finset.sum_image hg_inj]
          have himage_subset : sPlus.image g ⊆ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card) := by
            intro lam hlam
            rcases Finset.mem_image.mp hlam with ⟨μ, hμ, rfl⟩
            exact hg_mem μ hμ
          calc (∑ μ ∈ sPlus, cycleTypeWeight n (a ::ₘ a ::ₘ μ))
              = ∑ lam ∈ sPlus.image g, cycleTypeWeight n lam := hsum_image.symm
            _ ≤ ∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg himage_subset ?_
                  intro lam hlam hnot
                  unfold cycleTypeWeight
                  positivity
        rw [← hη]
        dsimp [a] at hsplit ⊢
        rw [hsplit]
        nlinarith [hle0, hlePlus]
    · -- k ≤ 1: η = 0
      rw [eta_eq_zero_of_le_one n k (by omega : k ≤ 1)]
      have h1 : 0 ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) := by
        exact Finset.sum_nonneg (by intro lam hlam; unfold cycleTypeWeight; positivity)
      have h2 : 0 ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
        exact Finset.sum_nonneg (by intro lam hlam; unfold cycleTypeWeight; positivity)
      exact add_nonneg h1 h2
  · -- ¬ 2 ∣ n-k: k ≤ 1, η = 0
    have hk_le1 : k ≤ 1 := by
      by_contra h
      have hk2 : 2 ≤ k := by omega
      have h2s_dvd : 2 ^ Nat.log 2 k ∣ n - k := two_pow_log2_dvd_of_mem_K hk hk2
      have hs : 1 ≤ Nat.log 2 k := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) (by omega : 2 ≤ k)
      have h2dvd : 2 ∣ 2 ^ Nat.log 2 k := pow_dvd_pow 2 hs
      exact hdiv (dvd_trans h2dvd h2s_dvd)
    rw [eta_eq_zero_of_le_one n k hk_le1]
    have h1 : 0 ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) := by
      exact Finset.sum_nonneg (by intro lam hlam; unfold cycleTypeWeight; positivity)
    have h2 : 0 ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
      exact Finset.sum_nonneg (by intro lam hlam; unfold cycleTypeWeight; positivity)
    exact add_nonneg h1 h2

/-- The Tᵢ-decomposition of `restProb`: `restProb n k ≤ T₀ + T₁ + T₂s + T₂r + T₃₊`. -/
lemma restProb_le_T_parts (n k : ℕ) :
    restProb n k ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0), cycleTypeWeight n lam) +
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1), cycleTypeWeight n lam) +
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) +
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam), cycleTypeWeight n lam) +
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
  let s : Finset (Multiset ℕ) := ((cycleTypes n).filter (fun lam => n - k ∉ lam)).filter (fun lam => lam.lcm = n - k)
  let w : Multiset ℕ → ℝ := cycleTypeWeight n
  have hrest : restProb n k = ∑ lam ∈ s, w lam := by
    dsimp [restProb, s, w]
    rw [← Finset.sum_filter]
  rw [hrest]
  have hparts := sum_eq_filter_card_parts n (s := s) (w := w)
  rw [hparts]
  have hsplit2 : (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 2), w lam) =
      (∑ lam ∈ (s.filter (fun lam => (lam.filter (large n)).card = 2)).filter (fun lam => specialPair n k lam), w lam) +
      (∑ lam ∈ (s.filter (fun lam => (lam.filter (large n)).card = 2)).filter (fun lam => ¬ specialPair n k lam), w lam) := by
    exact (Finset.sum_filter_add_sum_filter_not (s := s.filter (fun lam => (lam.filter (large n)).card = 2))
      (p := fun lam => specialPair n k lam) (f := w)).symm
  rw [hsplit2]
  have h0 : (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 0), w lam) ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0), cycleTypeWeight n lam) := by
    dsimp [w]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro lam hlam
      rcases Finset.mem_filter.mp hlam with ⟨hmem, hcard⟩
      rcases Finset.mem_filter.mp hmem with ⟨hmem', hlcm⟩
      rcases Finset.mem_filter.mp hmem' with ⟨hcyc, hnk⟩
      rw [Finset.mem_filter]
      exact ⟨hcyc, hcard⟩
    · intro lam hlam hnot
      unfold cycleTypeWeight
      positivity
  have h1 : (∑ lam ∈ s.filter (fun lam => (lam.filter (large n)).card = 1), w lam) ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1), cycleTypeWeight n lam) := by
    dsimp [w]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro lam hlam
      rcases Finset.mem_filter.mp hlam with ⟨hmem, hcard⟩
      rcases Finset.mem_filter.mp hmem with ⟨hmem', hlcm⟩
      rcases Finset.mem_filter.mp hmem' with ⟨hcyc, hnk⟩
      rw [Finset.mem_filter]
      exact ⟨hcyc, hlcm, hnk, hcard⟩
    · intro lam hlam hnot
      unfold cycleTypeWeight
      positivity
  have h2s : (∑ lam ∈ (s.filter (fun lam => (lam.filter (large n)).card = 2)).filter (fun lam => specialPair n k lam), w lam) ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) := by
    dsimp [w]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro lam hlam
      rcases Finset.mem_filter.mp hlam with ⟨hmem, hsp⟩
      rcases Finset.mem_filter.mp hmem with ⟨hmem', hcard⟩
      rcases Finset.mem_filter.mp hmem' with ⟨hmem'', hlcm⟩
      rcases Finset.mem_filter.mp hmem'' with ⟨hcyc, hnk⟩
      rw [Finset.mem_filter]
      exact ⟨hcyc, hlcm, hnk, hsp⟩
    · intro lam hlam hnot
      unfold cycleTypeWeight
      positivity
  have h2r : (∑ lam ∈ (s.filter (fun lam => (lam.filter (large n)).card = 2)).filter (fun lam => ¬ specialPair n k lam), w lam) ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam), cycleTypeWeight n lam) := by
    dsimp [w]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro lam hlam
      rcases Finset.mem_filter.mp hlam with ⟨hmem, hnsp⟩
      rcases Finset.mem_filter.mp hmem with ⟨hmem', hcard⟩
      rcases Finset.mem_filter.mp hmem' with ⟨hmem'', hlcm⟩
      rcases Finset.mem_filter.mp hmem'' with ⟨hcyc, hnk⟩
      rw [Finset.mem_filter]
      exact ⟨hcyc, hlcm, hnk, hcard, hnsp⟩
    · intro lam hlam hnot
      unfold cycleTypeWeight
      positivity
  have h3 : (∑ lam ∈ s.filter (fun lam => 3 ≤ (lam.filter (large n)).card), w lam) ≤
      (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
    dsimp [w]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro lam hlam
      rcases Finset.mem_filter.mp hlam with ⟨hmem, hcard⟩
      rcases Finset.mem_filter.mp hmem with ⟨hmem', hlcm⟩
      rcases Finset.mem_filter.mp hmem' with ⟨hcyc, hnk⟩
      rw [Finset.mem_filter]
      exact ⟨hcyc, hlcm, hnk, hcard⟩
    · intro lam hlam hnot
      unfold cycleTypeWeight
      positivity
  nlinarith [h0, h1, h2s, h2r, h3]

/-- **Proposition 4.1** (`prop:exact_order`): for `k ∈ Kₙ`,
`pₙ(n-k) = 1/(n-k) + η(n,k) + O(n^{-149/56})`. -/
theorem prop_exact_order :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ∈ K n →
      |p n (n - k) - ((1 : ℝ) / ((n - k : ℕ) : ℝ) + eta n k)| ≤ C / (n : ℝ) ^ (149 / 56 : ℝ) := by
  rcases tau_pow_twentyfour_le with ⟨Cτ, hCτ⟩
  have huniform2 := nuNoLong_le_const_div_cube_uniform
  have huniform6 := nuNoLong_le_const_div_cube_uniform_sixth
  have hnunl := nuNoLong_bound
  rcases Filter.eventually_atTop.mp huniform2 with ⟨N₁, hN₁⟩
  rcases Filter.eventually_atTop.mp huniform6 with ⟨N₂, hN₂⟩
  rcases Filter.eventually_atTop.mp hnunl with ⟨N₃, hN₃⟩
  let N₀ : ℕ := max (max (max 10 (2^28)) (max N₁ N₂)) N₃
  let C₀ : ℝ := (4 : ℝ)^45 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 +
    (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 + 2 * (Cτ : ℝ)^(1/8 : ℝ)
  refine ⟨C₀, ?hC₀, N₀, ?_⟩
  · dsimp [C₀]
    have hpos : 0 < (4 : ℝ)^45 := by norm_num
    have h2 : 0 ≤ (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/24 : ℝ)) (by norm_num : 0 ≤ (4 : ℝ)^45)
    have h3 : 0 ≤ (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/12 : ℝ)) (by norm_num : 0 ≤ (24 : ℝ)^45)
    have h4 : 0 ≤ 2 * (Cτ : ℝ)^(1/8 : ℝ) :=
      mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/8 : ℝ))
    nlinarith
  · intro n hn k hk
    have hn10 : 10 ≤ n := by
      have hN₀ : N₀ ≤ n := hn
      dsimp [N₀] at hN₀
      have h1 : max (max 10 (2^28)) (max N₁ N₂) ≤ n := le_trans (le_max_left _ _) hN₀
      have h2 : max 10 (2^28) ≤ n := le_trans (le_max_left _ _) h1
      exact le_trans (le_max_left _ _) h2
    have hn20 : 2^28 ≤ n := by
      have hN₀ : N₀ ≤ n := hn
      dsimp [N₀] at hN₀
      have h1 : max (max 10 (2^28)) (max N₁ N₂) ≤ n := le_trans (le_max_left _ _) hN₀
      have h2 : max 10 (2^28) ≤ n := le_trans (le_max_left _ _) h1
      exact le_trans (le_max_right _ _) h2
    have hn3 : 3 ≤ n := by omega
    have hn5 : 5 ≤ n := by omega
    have hnpos : 0 < n := by omega
    have hk_lt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hnRnn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hτ : (tau (n - k) : ℝ) ≤ (Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) :=
      tau_sub_le_twentyfourth n k Cτ (hCτ (n - k))
    have hsum_inv : (∑ d ∈ largeDivs n k, (1 / (d : ℝ))) ≤
        (Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) := by
      have hnpow : 0 ≤ (n : ℝ)^(-(13/14 : ℝ)) := Real.rpow_nonneg hnRnn _
      exact le_trans (sum_inv_largeDivs_le n k hnpos)
        (mul_le_mul_of_nonneg_right hτ hnpow)
    have hν2 : ∀ m : ℕ, (n : ℝ) ≤ 2 * (m : ℝ) → m ≤ n →
        nuNoLong m (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (4 : ℝ)^45 / (n : ℝ)^3 := by
      intro m hm hmle
      have hN₁n : N₁ ≤ n := by
        have hN₀ : N₀ ≤ n := hn
        dsimp [N₀] at hN₀
        have h1 : max (max 10 (2^28)) (max N₁ N₂) ≤ n := le_trans (le_max_left _ _) hN₀
        have h2 : max N₁ N₂ ≤ n := le_trans (le_max_right _ _) h1
        exact le_trans (le_max_left _ _) h2
      exact hN₁ n hN₁n m hm hmle
    have hν6 : ∀ m : ℕ, (n : ℝ) ≤ 6 * (m : ℝ) → m ≤ n →
        nuNoLong m (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (24 : ℝ)^45 / (n : ℝ)^3 := by
      intro m hm hmle
      have hN₂n : N₂ ≤ n := by
        have hN₀ : N₀ ≤ n := hn
        dsimp [N₀] at hN₀
        have h1 : max (max 10 (2^28)) (max N₁ N₂) ≤ n := le_trans (le_max_left _ _) hN₀
        have h2 : max N₁ N₂ ≤ n := le_trans (le_max_right _ _) h1
        exact le_trans (le_max_right _ _) h2
      exact hN₂ n hN₂n m hm hmle
    have hν₀ : nuNoLong n (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (2^45 : ℝ) / (n : ℝ)^3 := by
      have hN₃n : N₃ ≤ n := by
        have hN₀ : N₀ ≤ n := hn
        dsimp [N₀] at hN₀
        exact le_trans (le_max_right _ _) hN₀
      exact hN₃ n hN₃n
    have hmain : p n (n - k) = (1 : ℝ) / ((n - k : ℕ) : ℝ) + restProb n k := by
      haveI : NeZero n := ⟨by omega⟩
      exact p_eq_one_div_add_rest n k hk hn5
    rw [hmain]
    have hsimp : (1 : ℝ) / ((n - k : ℕ) : ℝ) + restProb n k -
        ((1 : ℝ) / ((n - k : ℕ) : ℝ) + eta n k) = restProb n k - eta n k := by
      ring
    rw [hsimp]
    -- T0
    have hT0 : (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0), cycleTypeWeight n lam) ≤
        (2^45 : ℝ) / (n : ℝ)^3 := by
      exact le_trans (sum_cycleTypeWeight_no_large_le_nu n) hν₀
    -- T1
    have hT1 : (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1), cycleTypeWeight n lam) ≤
        (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
      have h1 := sum_cycleTypeWeight_one_large_le n k hn3 hk_lt
      have hν_d : ∀ d ∈ largeDivs n k, nuNoLong (n - d) (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) ≤ (4 : ℝ)^45 / (n : ℝ)^3 := by
        intro d hd
        apply hν2 (n - d)
        · have hd_le_half : d ≤ (n - k) / 2 := proper_divisor_le_half (mem_largeDivs_dvd hd) (mem_largeDivs_lt hd)
          have h2d_le : 2 * d ≤ n := by
            have h1' : 2 * ((n - k) / 2) ≤ n - k := by
              rw [Nat.mul_comm]
              exact Nat.div_mul_le_self (n - k) 2
            omega
          exact_mod_cast (by omega : n ≤ 2 * (n - d))
        · omega
      have hsum_le : (∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * nuNoLong (n - d) (⌈(n : ℝ)^(13/14 : ℝ)⌉₊)) ≤
          (∑ d ∈ largeDivs n k, (1 / (d : ℝ))) * ((4 : ℝ)^45 / (n : ℝ)^3) := by
        calc (∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * nuNoLong (n - d) (⌈(n : ℝ)^(13/14 : ℝ)⌉₊))
            ≤ ∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * ((4 : ℝ)^45 / (n : ℝ)^3) := by
                exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hν_d d hd) (by positivity))
          _ = (∑ d ∈ largeDivs n k, (1 / (d : ℝ))) * ((4 : ℝ)^45 / (n : ℝ)^3) := by
                rw [Finset.sum_mul]
      calc (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1), cycleTypeWeight n lam)
          ≤ ∑ d ∈ largeDivs n k, (1 / (d : ℝ)) * nuNoLong (n - d) (⌈(n : ℝ)^(13/14 : ℝ)⌉₊) := h1
        _ ≤ (∑ d ∈ largeDivs n k, (1 / (d : ℝ))) * ((4 : ℝ)^45 / (n : ℝ)^3) := hsum_le
        _ ≤ ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ))) * ((4 : ℝ)^45 / (n : ℝ)^3) := by
              exact mul_le_mul_of_nonneg_right hsum_inv (by positivity)
        _ = (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 * ((n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) / (n : ℝ)^3) := by
              ring
        _ ≤ (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
              have hpow : (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) / (n : ℝ)^3 =
                  (n : ℝ)^(-(653/168 : ℝ)) := by
                have h1' : (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) = (n : ℝ)^(-(149/168 : ℝ)) := by
                  rw [← Real.rpow_add hnRpos (1/24 : ℝ) (-(13/14 : ℝ))]
                  congr 1
                  norm_num
                rw [h1']
                rw [div_eq_mul_inv (a := (n : ℝ)^(-(149/168 : ℝ))) (b := (n : ℝ)^3)]
                have h3r : (n : ℝ)^3 = (n : ℝ)^(3 : ℝ) := (Real.rpow_natCast (n : ℝ) 3).symm
                rw [h3r]
                have hinv : ((n : ℝ)^(3 : ℝ))⁻¹ = (n : ℝ)^(-(3 : ℝ)) := by
                  rw [Real.rpow_neg (le_of_lt hnRpos) 3]
                rw [hinv]
                rw [← Real.rpow_add hnRpos (-(149/168 : ℝ)) (-(3 : ℝ))]
                congr 1
                norm_num
              rw [hpow]
              have hle : (n : ℝ)^(-(653/168 : ℝ)) ≤ (n : ℝ)^(-(149/56 : ℝ)) := by
                refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
                · exact by exact_mod_cast (by omega : 1 ≤ n)
                · norm_num
              have hnonneg : 0 ≤ (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 :=
                mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/24 : ℝ)) (by norm_num : 0 ≤ (4 : ℝ)^45)
              have h3' : (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 * (n : ℝ)^(-(653/168 : ℝ)) ≤
                  (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 * (n : ℝ)^(-(149/56 : ℝ)) :=
                mul_le_mul_of_nonneg_left hle hnonneg
              rw [div_eq_mul_inv (a := (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45) (b := (n : ℝ)^(149/56 : ℝ))]
              rw [← Real.rpow_neg hnRnn (149/56 : ℝ)]
              exact h3'
    -- T2 special
    have hT2s : (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) ≤
        eta n k := by
      exact sum_cycleTypeWeight_two_large_special_le n k hk hn10
    have hηle : eta n k ≤
        (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) +
        (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
      exact eta_le_special_add_ge_three n k hk hn20
    -- T2 rest
    have hT2r : (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam), cycleTypeWeight n lam) ≤
        (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
      have h1 := sum_cycleTypeWeight_two_large_rest_le n k hk hn3 hν6
      have hsum_inv2 : (∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k, (1 / ((d₁ * d₂ : ℕ) : ℝ))) ≤
          ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 := by
        have hsum₁_nn : 0 ≤ (∑ d₁ ∈ largeDivs n k, (1 / (d₁ : ℝ))) := by
          refine Finset.sum_nonneg (fun d hd => ?_)
          positivity
        have hsum₂_nn : 0 ≤ (∑ d₂ ∈ largeDivs n k, (1 / (d₂ : ℝ))) := by
          refine Finset.sum_nonneg (fun d hd => ?_)
          positivity
        have hX : 0 ≤ (Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) := by
          exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/24 : ℝ))
            (Real.rpow_nonneg hnRnn (1/24 : ℝ))) (Real.rpow_nonneg hnRnn (-(13/14 : ℝ)))
        calc (∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k, (1 / ((d₁ * d₂ : ℕ) : ℝ)))
            = (∑ d₁ ∈ largeDivs n k, (1 / (d₁ : ℝ))) * (∑ d₂ ∈ largeDivs n k, (1 / (d₂ : ℝ))) := by
                rw [Finset.sum_mul_sum]
                apply Finset.sum_congr rfl
                intro d₁ hd₁
                apply Finset.sum_congr rfl
                intro d₂ hd₂
                rw [Nat.cast_mul]
                rw [one_div_mul_one_div]
          _ ≤ ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 := by
                simpa only [pow_two] using (mul_le_mul hsum_inv hsum_inv hsum₂_nn hX)
      calc (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam), cycleTypeWeight n lam)
          ≤ ∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k, (1 / ((d₁ * d₂ : ℕ) : ℝ)) * ((24 : ℝ)^45 / (n : ℝ)^3) := h1
        _ = (∑ d₁ ∈ largeDivs n k, ∑ d₂ ∈ largeDivs n k, (1 / ((d₁ * d₂ : ℕ) : ℝ))) * ((24 : ℝ)^45 / (n : ℝ)^3) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d₁ hd₁
              exact (Finset.sum_mul (largeDivs n k) (fun d₂ => (1 / ((d₁ * d₂ : ℕ) : ℝ))) ((24 : ℝ)^45 / (n : ℝ)^3)).symm
        _ ≤ ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 * ((24 : ℝ)^45 / (n : ℝ)^3) := by
              exact mul_le_mul_of_nonneg_right hsum_inv2 (by positivity)
        _ ≤ (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
              have hnonneg : 0 ≤ (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 :=
                mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/12 : ℝ)) (by norm_num : 0 ≤ (24 : ℝ)^45)
              have hpow : ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 *
                  ((24 : ℝ)^45 / (n : ℝ)^3) =
                  (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 * (((n : ℝ)^(-(149/168 : ℝ)))^2 / (n : ℝ)^3) := by
                have h1' : ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 =
                    (Cτ : ℝ)^(1/12 : ℝ) * ((n : ℝ)^(-(149/168 : ℝ)))^2 := by
                  have h2' : (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) = (n : ℝ)^(-(149/168 : ℝ)) := by
                    rw [← Real.rpow_add hnRpos (1/24 : ℝ) (-(13/14 : ℝ))]
                    congr 1
                    norm_num
                  rw [show ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 =
                      ((Cτ : ℝ)^(1/24 : ℝ) * ((n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ))))^2 by ring]
                  rw [mul_pow]
                  rw [h2']
                  have h3' : ((Cτ : ℝ)^(1/24 : ℝ))^2 = (Cτ : ℝ)^(1/12 : ℝ) := by
                    rw [← Real.rpow_natCast ((Cτ : ℝ)^(1/24 : ℝ)) 2]
                    rw [← Real.rpow_mul (Nat.cast_nonneg Cτ) (1/24 : ℝ) ((2 : ℕ) : ℝ)]
                    congr 1
                    norm_num
                  rw [h3']
                rw [h1']
                rw [div_eq_mul_inv (a := (24 : ℝ)^45) (b := (n : ℝ)^3)]
                rw [div_eq_mul_inv (a := ((n : ℝ)^(-(149/168 : ℝ)))^2) (b := (n : ℝ)^3)]
                ring
              rw [hpow]
              have hpow2 : ((n : ℝ)^(-(149/168 : ℝ)))^2 = (n : ℝ)^(-(149/84 : ℝ)) := by
                rw [← Real.rpow_natCast ((n : ℝ)^(-(149/168 : ℝ))) 2]
                rw [← Real.rpow_mul hnRnn (-(149/168 : ℝ)) ((2 : ℕ) : ℝ)]
                congr 1
                norm_num
              rw [hpow2]
              have hfrac : (n : ℝ)^(-(149/84 : ℝ)) / (n : ℝ)^3 = (n : ℝ)^(-(401/84 : ℝ)) := by
                rw [div_eq_mul_inv (a := (n : ℝ)^(-(149/84 : ℝ))) (b := (n : ℝ)^3)]
                have h3r : (n : ℝ)^3 = (n : ℝ)^(3 : ℝ) := (Real.rpow_natCast (n : ℝ) 3).symm
                rw [h3r]
                have hinv : ((n : ℝ)^(3 : ℝ))⁻¹ = (n : ℝ)^(-(3 : ℝ)) := by
                  rw [Real.rpow_neg (le_of_lt hnRpos) 3]
                rw [hinv]
                rw [← Real.rpow_add hnRpos (-(149/84 : ℝ)) (-(3 : ℝ))]
                congr 1
                norm_num
              rw [hfrac]
              have hle2 : (n : ℝ)^(-(401/84 : ℝ)) ≤ (n : ℝ)^(-(149/56 : ℝ)) := by
                refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
                · exact by exact_mod_cast (by omega : 1 ≤ n)
                · norm_num
              have h3' : (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 * (n : ℝ)^(-(401/84 : ℝ)) ≤
                  (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 * (n : ℝ)^(-(149/56 : ℝ)) :=
                mul_le_mul_of_nonneg_left hle2 hnonneg
              rw [div_eq_mul_inv (a := (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45) (b := (n : ℝ)^(149/56 : ℝ))]
              rw [← Real.rpow_neg hnRnn (149/56 : ℝ)]
              exact h3'
    -- T3
    have hT3 : (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) ≤
        (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
      have h1 := sum_cycleTypeWeight_ge_three_large_le n k hk hn3
      have hsum_inv3 : (∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k, (1 / ((x * y * z : ℕ) : ℝ))) ≤
          ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^3 := by
        have hsum₁_nn : 0 ≤ (∑ x ∈ largeDivs n k, (1 / (x : ℝ))) := by
          refine Finset.sum_nonneg (fun d hd => ?_)
          positivity
        have hsum₂_nn : 0 ≤ (∑ y ∈ largeDivs n k, (1 / (y : ℝ))) := by
          refine Finset.sum_nonneg (fun d hd => ?_)
          positivity
        have hsum₃_nn : 0 ≤ (∑ z ∈ largeDivs n k, (1 / (z : ℝ))) := by
          refine Finset.sum_nonneg (fun d hd => ?_)
          positivity
        have hX : 0 ≤ (Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) := by
          exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/24 : ℝ))
            (Real.rpow_nonneg hnRnn (1/24 : ℝ))) (Real.rpow_nonneg hnRnn (-(13/14 : ℝ)))
        have htriple : (∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k, (1 / ((x * y * z : ℕ) : ℝ))) =
            (∑ x ∈ largeDivs n k, (1 / (x : ℝ))) * (∑ y ∈ largeDivs n k, (1 / (y : ℝ))) *
              (∑ z ∈ largeDivs n k, (1 / (z : ℝ))) := by
          calc (∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k, (1 / ((x * y * z : ℕ) : ℝ)))
              = (∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, (1 / ((x * y : ℕ) : ℝ))) *
                  (∑ z ∈ largeDivs n k, (1 / (z : ℝ))) := by
                  rw [Finset.sum_mul_sum]
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro y hy
                  rw [Nat.cast_mul, Nat.cast_mul]
                  rw [one_div_mul_one_div]
            _ = (∑ x ∈ largeDivs n k, (1 / (x : ℝ))) * (∑ y ∈ largeDivs n k, (1 / (y : ℝ))) *
                (∑ z ∈ largeDivs n k, (1 / (z : ℝ))) := by
                  have htwo : (∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, (1 / ((x * y : ℕ) : ℝ))) =
                      (∑ x ∈ largeDivs n k, (1 / (x : ℝ))) * (∑ y ∈ largeDivs n k, (1 / (y : ℝ))) := by
                    rw [Finset.sum_mul_sum]
                    apply Finset.sum_congr rfl
                    intro x hx
                    apply Finset.sum_congr rfl
                    intro y hy
                    rw [Nat.cast_mul]
                    rw [one_div_mul_one_div]
                  exact congrArg (fun t => t * (∑ z ∈ largeDivs n k, (1 / (z : ℝ)))) htwo
        rw [htriple]
        have hXX : 0 ≤ ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 := by
          simpa only [pow_two] using (mul_nonneg hX hX)
        have h₁₂ : (∑ x ∈ largeDivs n k, (1 / (x : ℝ))) * (∑ y ∈ largeDivs n k, (1 / (y : ℝ))) ≤
            ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^2 := by
          simpa only [pow_two] using (mul_le_mul hsum_inv hsum_inv hsum₂_nn hX)
        have h123 : ((∑ x ∈ largeDivs n k, (1 / (x : ℝ))) * (∑ y ∈ largeDivs n k, (1 / (y : ℝ)))) *
            (∑ z ∈ largeDivs n k, (1 / (z : ℝ))) ≤
            ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^3 := by
          exact mul_le_mul h₁₂ hsum_inv hsum₃_nn hXX
        exact h123
      calc (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam)
          ≤ ∑ x ∈ largeDivs n k, ∑ y ∈ largeDivs n k, ∑ z ∈ largeDivs n k, (1 / ((x * y * z : ℕ) : ℝ)) := h1
        _ ≤ ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^3 := hsum_inv3
        _ ≤ (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
              have hnonneg : 0 ≤ (Cτ : ℝ)^(1/8 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/8 : ℝ)
              have hpow : ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^3 =
                  (Cτ : ℝ)^(1/8 : ℝ) * ((n : ℝ)^(-(149/168 : ℝ)))^3 := by
                have h2' : (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)) = (n : ℝ)^(-(149/168 : ℝ)) := by
                  rw [← Real.rpow_add hnRpos (1/24 : ℝ) (-(13/14 : ℝ))]
                  congr 1
                  norm_num
                rw [show ((Cτ : ℝ)^(1/24 : ℝ) * (n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ)))^3 =
                    ((Cτ : ℝ)^(1/24 : ℝ) * ((n : ℝ)^(1/24 : ℝ) * (n : ℝ)^(-(13/14 : ℝ))))^3 by ring]
                rw [mul_pow]
                rw [h2']
                have h1' : ((Cτ : ℝ)^(1/24 : ℝ))^3 = (Cτ : ℝ)^(1/8 : ℝ) := by
                  rw [← Real.rpow_natCast ((Cτ : ℝ)^(1/24 : ℝ)) 3]
                  rw [← Real.rpow_mul (Nat.cast_nonneg Cτ) (1/24 : ℝ) ((3 : ℕ) : ℝ)]
                  congr 1
                  norm_num
                rw [h1']
              rw [hpow]
              have hpow3 : ((n : ℝ)^(-(149/168 : ℝ)))^3 = (n : ℝ)^(-(149/56 : ℝ)) := by
                rw [← Real.rpow_natCast ((n : ℝ)^(-(149/168 : ℝ))) 3]
                rw [← Real.rpow_mul hnRnn (-(149/168 : ℝ)) ((3 : ℕ) : ℝ)]
                congr 1
                norm_num
              rw [hpow3]
              rw [div_eq_mul_inv (a := (Cτ : ℝ)^(1/8 : ℝ)) (b := (n : ℝ)^(149/56 : ℝ))]
              rw [← Real.rpow_neg hnRnn (149/56 : ℝ)]
    -- assemble |restProb - η|
    have hpos3 : 0 < (n : ℝ)^3 := pow_pos hnRpos 3
    have hpos5 : 0 < (n : ℝ)^(149/56 : ℝ) := Real.rpow_pos_of_pos hnRpos _
    have hX0 : 0 ≤ (2^45 : ℝ) / (n : ℝ)^3 := div_nonneg (by norm_num : 0 ≤ (2^45 : ℝ)) (le_of_lt hpos3)
    have hX1 : 0 ≤ (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
      refine div_nonneg ?_ (le_of_lt hpos5)
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/24 : ℝ)) (by norm_num : 0 ≤ (4 : ℝ)^45)
    have hX2 : 0 ≤ (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
      refine div_nonneg ?_ (le_of_lt hpos5)
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/12 : ℝ)) (by norm_num : 0 ≤ (24 : ℝ)^45)
    have hX3 : 0 ≤ (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
      refine div_nonneg ?_ (le_of_lt hpos5)
      exact Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/8 : ℝ)
    have hrest : restProb n k ≤
        (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + eta n k +
        (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
      have hparts := restProb_le_T_parts n k
      calc restProb n k
          ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => (lam.filter (large n)).card = 0), cycleTypeWeight n lam) +
            (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 1), cycleTypeWeight n lam) +
            (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) +
            (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ (lam.filter (large n)).card = 2 ∧ ¬ specialPair n k lam), cycleTypeWeight n lam) +
            (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := hparts
        _ ≤ (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + eta n k +
            (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
              nlinarith [hT0, hT1, hT2s, hT2r, hT3]
    have hdiff_le : restProb n k - eta n k ≤
        (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) +
        (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
      nlinarith [hrest]
    have hdiff_ge : -(restProb n k - eta n k) ≤
        (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) +
        (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + 2 * (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
      have hrest_ge_T2s : (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ specialPair n k lam), cycleTypeWeight n lam) ≤ restProb n k := by
        unfold restProb
        rw [← Finset.sum_filter]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro lam hlam
          rcases Finset.mem_filter.mp hlam with ⟨hmem, hlcm, hnk, hpair⟩
          rw [Finset.mem_filter]
          rw [Finset.mem_filter]
          exact ⟨⟨hmem, hnk⟩, hlcm⟩
        · intro lam hlam hnot
          unfold cycleTypeWeight
          positivity
      have hη_rest : eta n k - restProb n k ≤
          (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := by
        nlinarith [hηle, hrest_ge_T2s]
      calc -(restProb n k - eta n k)
          = eta n k - restProb n k := by ring
        _ ≤ (∑ lam ∈ (cycleTypes n).filter (fun lam => lam.lcm = n - k ∧ n - k ∉ lam ∧ 3 ≤ (lam.filter (large n)).card), cycleTypeWeight n lam) := hη_rest
        _ ≤ (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := hT3
        _ ≤ (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) +
            (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + 2 * (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
              have hX3le : (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) ≤
                  2 * (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
                rw [div_le_div_iff₀ hpos5 hpos5]
                have hC3 : (Cτ : ℝ)^(1/8 : ℝ) ≤ 2 * (Cτ : ℝ)^(1/8 : ℝ) := by
                  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/8 : ℝ)]
                exact mul_le_mul_of_nonneg_right hC3 (le_of_lt hpos5)
              nlinarith [hX0, hX1, hX2, hX3le]
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h1' : (n : ℝ)^(149/56 : ℝ) ≤ (n : ℝ)^3 := by
      have h3r : (n : ℝ)^3 = (n : ℝ)^(3 : ℝ) := (Real.rpow_natCast (n : ℝ) 3).symm
      rw [h3r]
      refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
      norm_num
    have h2' : (2^45 : ℝ) / (n : ℝ)^3 ≤ (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) := by
      rw [div_le_div_iff₀ hpos3 hpos5]
      have hnum : (2^45 : ℝ) * (n : ℝ)^(149/56 : ℝ) ≤ (4 : ℝ)^45 * (n : ℝ)^3 := by
        have h23 : (2^45 : ℝ) ≤ (4 : ℝ)^45 := by norm_num
        exact mul_le_mul h23 h1' (le_of_lt hpos5) (by norm_num : 0 ≤ (4 : ℝ)^45)
      exact hnum
    have hX3le : (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) ≤
        2 * (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := by
      rw [div_le_div_iff₀ hpos5 hpos5]
      have hC3 : (Cτ : ℝ)^(1/8 : ℝ) ≤ 2 * (Cτ : ℝ)^(1/8 : ℝ) := by
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg Cτ) (1/8 : ℝ)]
      exact mul_le_mul_of_nonneg_right hC3 (le_of_lt hpos5)
    rw [abs_le]
    constructor
    · -- -(C₀/n^{149/56}) ≤ restProb - η
      rw [neg_le]
      calc -(restProb n k - eta n k)
          ≤ (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) +
            (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + 2 * (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := hdiff_ge
        _ ≤ C₀ / (n : ℝ)^(149/56 : ℝ) := by
              dsimp [C₀]
              rw [add_div, add_div, add_div]
              nlinarith [h2']
    · -- restProb - η ≤ C₀/n^{149/56}
      calc restProb n k - eta n k
          ≤ (2^45 : ℝ) / (n : ℝ)^3 + (Cτ : ℝ)^(1/24 : ℝ) * (4 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) +
            (Cτ : ℝ)^(1/12 : ℝ) * (24 : ℝ)^45 / (n : ℝ)^(149/56 : ℝ) + (Cτ : ℝ)^(1/8 : ℝ) / (n : ℝ)^(149/56 : ℝ) := hdiff_le
        _ ≤ C₀ / (n : ℝ)^(149/56 : ℝ) := by
              dsimp [C₀]
              rw [add_div, add_div, add_div]
              nlinarith [h2', hX3le]

/-! ### The strict dominance of the mode (Theorem 1.2, first half) -/

/-- For all sufficiently large `n`, the mode `n - k₀(n)` strictly dominates every
other candidate `n - k` with `k ∈ Kₙ` (`k < k₀`): `pₙ(n-k) < pₙ(n-k₀)`.
(Paper §4: Proposition 4.1 + equation (15) `final_ineq`.) -/
lemma p_k0_gt_p_k :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ∈ K n → k < k0 n →
      p n (n - k) < p n (n - k0 n) := by
  rcases prop_exact_order with ⟨C, hCpos, N, hN⟩
  filter_upwards [Filter.eventually_ge_atTop (max N (Nat.ceil ((16 : ℝ) * C ^ 2)) + 1)] with n hn
  intro k hk hlt
  have hnN : N ≤ n := by
    have : max N (Nat.ceil ((16 : ℝ) * C ^ 2)) + 1 ≤ n := hn
    omega
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnRnn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hk0mem : k0 n ∈ K n := k0_mem_K n (by omega : 0 < n)
  have hk_lt_n : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hk0_lt_n : k0 n < n := Finset.mem_range.mp (Finset.mem_filter.mp hk0mem).1
  have hnk_pos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk_lt_n)
  have hnk0_pos : 0 < ((n - k0 n : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk0_lt_n)
  have habs_k := hN n hnN k hk
  have habs_k0 := hN n hnN (k0 n) hk0mem
  have hpk_le : p n (n - k) ≤ (1 : ℝ) / ((n - k : ℕ) : ℝ) + eta n k + C / (n : ℝ) ^ (149/56 : ℝ) := by
    have h := (abs_le.mp habs_k).2
    nlinarith
  have hpk0_ge : (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n) - C / (n : ℝ) ^ (149/56 : ℝ) ≤ p n (n - k0 n) := by
    have h := (abs_le.mp habs_k0).1
    nlinarith
  have halg : (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / ((n - k : ℕ) : ℝ) =
      ((k0 n - k : ℕ) : ℝ) / (((n - k0 n : ℕ) : ℝ) * ((n - k : ℕ) : ℝ)) := by
    rw [show ((k0 n - k : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) - ((n - k0 n : ℕ) : ℝ) by
      rw [Nat.cast_sub (Nat.le_of_lt hlt)]
      rw [Nat.cast_sub (Nat.le_of_lt hk_lt_n), Nat.cast_sub (Nat.le_of_lt hk0_lt_n)]
      ring]
    field_simp [ne_of_gt hnk_pos, ne_of_gt hnk0_pos]
  have hmain' : (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n) -
      ((1 : ℝ) / ((n - k : ℕ) : ℝ) + eta n k) ≥ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 := by
    nlinarith [final_ineq n k (k0 n) hk hk0mem hlt, halg]
  have hdiff : p n (n - k0 n) - p n (n - k) ≥
      (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 - (C / (n : ℝ) ^ (149/56 : ℝ) + C / (n : ℝ) ^ (149/56 : ℝ)) := by
    nlinarith [hpk_le, hpk0_ge, hmain']
  have h16 : (16 : ℝ) * C ^ 2 ≤ (n : ℝ) := by
    have hceil_lt : Nat.ceil ((16 : ℝ) * C ^ 2) < n := by omega
    exact le_trans (Nat.le_ceil ((16 : ℝ) * C ^ 2)) (by exact_mod_cast (le_of_lt hceil_lt))
  have hsqrt : (4 : ℝ) * C ≤ (n : ℝ) ^ (1/2 : ℝ) := by
    have h4C : 0 ≤ (4 : ℝ) * C := by nlinarith [hCpos]
    have hmono : ((16 : ℝ) * C ^ 2) ^ (1/2 : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow (by nlinarith [sq_nonneg C] : 0 ≤ (16 : ℝ) * C ^ 2) h16 (by norm_num : 0 ≤ (1/2 : ℝ))
    have hleft : ((16 : ℝ) * C ^ 2) ^ (1/2 : ℝ) = (4 : ℝ) * C := by
      rw [show (4 : ℝ) * C = ((4 : ℝ) * C) ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [show (16 : ℝ) * C ^ 2 = ((4 : ℝ) * C) ^ 2 by ring]
      rw [show (((4 : ℝ) * C) ^ 2 : ℝ) = ((4 : ℝ) * C) ^ (2 : ℝ) by exact (Real.rpow_natCast ((4 : ℝ) * C) 2).symm]
      rw [← Real.rpow_mul h4C (2 : ℝ) (1/2 : ℝ)]
      congr 1
      norm_num
    rwa [← hleft]
  have hC_le : C / (n : ℝ) ^ (149/56 : ℝ) + C / (n : ℝ) ^ (149/56 : ℝ) ≤ (1 : ℝ) / 2 / (n : ℝ) ^ 2 := by
    have hnpos149 : 0 < (n : ℝ) ^ (149/56 : ℝ) := Real.rpow_pos_of_pos hnRpos _
    have hn2pos : 0 < (n : ℝ) ^ 2 := pow_pos hnRpos 2
    have h2C : (2 : ℝ) * C ≤ (1 / 2) * (n : ℝ) ^ (1/2 : ℝ) := by nlinarith [hsqrt]
    have h3 : (2 : ℝ) * C * (n : ℝ) ^ 2 ≤ ((1 / 2) * (n : ℝ) ^ (1/2 : ℝ)) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h2C (by positivity : 0 ≤ (n : ℝ) ^ 2)
    have h4 : ((1 / 2) * (n : ℝ) ^ (1/2 : ℝ)) * (n : ℝ) ^ 2 = (1 / 2) * (n : ℝ) ^ (5/2 : ℝ) := by
      rw [mul_assoc]
      rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by exact (Real.rpow_natCast (n : ℝ) 2).symm]
      rw [← Real.rpow_add hnRpos (1/2 : ℝ) (2 : ℝ)]
      congr 1
      norm_num
    have h4b : (1 / 2) * (n : ℝ) ^ (5/2 : ℝ) ≤ (1 / 2) * (n : ℝ) ^ (149/56 : ℝ) := by
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have h52r : (n : ℝ) ^ (5/2 : ℝ) = (n : ℝ) ^ ((5/2 : ℝ)) := rfl
      have hpow_le : (n : ℝ) ^ (5/2 : ℝ) ≤ (n : ℝ) ^ (149/56 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
        norm_num
      exact mul_le_mul_of_nonneg_left hpow_le (by norm_num : 0 ≤ (1/2 : ℝ))
    have hdiv : C / (n : ℝ) ^ (149/56 : ℝ) + C / (n : ℝ) ^ (149/56 : ℝ) = 2 * C / (n : ℝ) ^ (149/56 : ℝ) := by
      field_simp [ne_of_gt hnpos149]
      ring
    rw [hdiv]
    rw [div_le_div_iff₀ hnpos149 hn2pos]
    calc (2 : ℝ) * C * (n : ℝ) ^ 2 ≤ ((1 / 2) * (n : ℝ) ^ (1/2 : ℝ)) * (n : ℝ) ^ 2 := h3
      _ = (1 / 2) * (n : ℝ) ^ (5/2 : ℝ) := h4
      _ ≤ (1 / 2) * (n : ℝ) ^ (149/56 : ℝ) := h4b
  have hden : (1 : ℝ) / ((n : ℝ) ^ 2) ≤ (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 := by
    have hle : ((n - k : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      refine sq_le_sq' ?_ ?_
      · nlinarith [hnk_pos, hnRnn]
      · exact_mod_cast (Nat.sub_le n k)
    exact one_div_le_one_div_of_le (sq_pos_of_ne_zero (ne_of_gt hnk_pos)) hle
  have hpos : (0 : ℝ) < (1 : ℝ) / ((n - k : ℕ) : ℝ) ^ 2 -
      (C / (n : ℝ) ^ (149/56 : ℝ) + C / (n : ℝ) ^ (149/56 : ℝ)) := by
    have hC_le' : C / (n : ℝ) ^ (149/56 : ℝ) + C / (n : ℝ) ^ (149/56 : ℝ) ≤ (1 : ℝ) / 2 * (1 / (n : ℝ) ^ 2) := by
      have h' : ((1 : ℝ) / 2) * (1 / (n : ℝ) ^ 2) = ((1 : ℝ) / 2) / (n : ℝ) ^ 2 := by
        rw [div_eq_mul_inv (a := (1 : ℝ)) (b := (n : ℝ) ^ 2)]
        rw [div_eq_mul_inv (a := (1 : ℝ) / 2) (b := (n : ℝ) ^ 2)]
        ring
      rwa [h']
    have hinv : 0 < (1 : ℝ) / ((n : ℝ) ^ 2) := one_div_pos.mpr (pow_pos hnRpos 2)
    nlinarith [hden, hC_le', hinv]
  nlinarith [hdiff, hpos]

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2** (`thm:equality_case`): for all sufficiently large `n`,
`pₙ(m) = M(n)` if and only if `m = n - k₀(n)` (the mode of the order
distribution is `n - max Kₙ`). -/
theorem theorem_equality_case :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, p n m = M n ↔ m = n - k0 n := by
  filter_upwards [p_k0_gt_p_k, p_ge_one_div_n_implies_mem_K, Filter.eventually_ge_atTop 2] with n hgt hmem hn2
  intro m
  have hnpos : 0 < n := by omega
  constructor
  · -- p n m = M n ⟹ m = n - k0 n
    intro hp
    have hp_ge : (1 : ℝ) / (n : ℝ) ≤ p n m := by
      rw [hp]
      exact one_div_le_M n hn2
    have hkm := hmem m hp_ge
    rcases hkm with ⟨hkm, hmle⟩
    have hle : n - m ≤ k0 n := le_k0 n hnpos hkm
    have hne : n - m = k0 n := by
      by_contra hne
      have hlt : n - m < k0 n := lt_of_le_of_ne hle hne
      have hstrict := hgt (n - m) hkm hlt
      have hm_eq : n - (n - m) = m := by omega
      rw [hm_eq] at hstrict
      have : p n m < p n m := by
        calc p n m < p n (n - k0 n) := hstrict
          _ ≤ M n := p_le_M n (n - k0 n)
          _ = p n m := hp.symm
      exact (lt_irrefl _ this)
    omega
  · -- m = n - k0 n ⟹ p n m = M n
    intro hm
    rw [hm]
    refine le_antisymm (p_le_M n (n - k0 n)) ?_
    have hle_fold := (Finset.le_fold_max (s := Finset.range (Nat.factorial n + 1)) (b := (0 : ℝ))
      (f := fun m => p n m) (c := M n)).mp le_rfl
    rcases hle_fold with hbad | ⟨m₀, hm₀mem, hm₀le⟩
    · have hposM : (0 : ℝ) < M n := by
        have h1n : (0 : ℝ) < (1 : ℝ) / (n : ℝ) := one_div_pos.mpr (by exact_mod_cast (by omega : 0 < n))
        exact lt_of_lt_of_le h1n (one_div_le_M n hn2)
      nlinarith
    · have hp₀ge : (1 : ℝ) / (n : ℝ) ≤ p n m₀ := le_trans (one_div_le_M n hn2) hm₀le
      have hkm := hmem m₀ hp₀ge
      rcases hkm with ⟨hkm, hm₀le_n⟩
      have hle : n - m₀ ≤ k0 n := le_k0 n hnpos hkm
      have hne : n - m₀ = k0 n := by
        by_contra hne
        have hlt : n - m₀ < k0 n := lt_of_le_of_ne hle hne
        have hstrict := hgt (n - m₀) hkm hlt
        have hm₀_eq : n - (n - m₀) = m₀ := by omega
        rw [hm₀_eq] at hstrict
        have : p n m₀ < p n m₀ := by
          calc p n m₀ < p n (n - k0 n) := hstrict
            _ ≤ M n := p_le_M n (n - k0 n)
            _ ≤ p n m₀ := hm₀le
        exact (lt_irrefl _ this)
      have hm₀_eq : m₀ = n - k0 n := by omega
      rw [hm₀_eq] at hm₀le
      exact hm₀le

/-! ### Remark `rem:sharp_asymp`: `M(n) = 1/n + O(log n/n²)` -/

/-- Our `lcm1to k` is exactly `Chebyshev.lcmUpto k`. -/
lemma lcm1to_eq_lcmUpto (k : ℕ) : lcm1to k = Nat.lcmUpto k := rfl

/-- The binomial lower bound `2^k ≤ (k+1)·lcm(1,…,k)` (Farhi, via mathlib). -/
lemma two_pow_le_mul_lcm1to (k : ℕ) : 2 ^ k ≤ (k + 1) * lcm1to k := by
  simpa [lcm1to_eq_lcmUpto] using (Chebyshev.two_pow_le_mul_lcmUpto k)

/-- `log₂(n²) ≤ 2·log₂ n + 1`. -/
lemma log_two_sq_le_two_mul_add_one {n : ℕ} (hn : 0 < n) :
    Nat.log 2 (n ^ 2) ≤ 2 * Nat.log 2 n + 1 := by
  have hb : 1 < (2 : ℕ) := by norm_num
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self hb n
  have hsq : n ^ 2 < (2 ^ (Nat.log 2 n + 1)) ^ 2 := by
    exact pow_lt_pow_left₀ hlt (by exact_mod_cast (Nat.zero_le n) : 0 ≤ n) (by norm_num : (2 : ℕ) ≠ 0)
  have hrew : (2 ^ (Nat.log 2 n + 1)) ^ 2 = 2 ^ (2 * Nat.log 2 n + 2) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hrew] at hsq
  by_contra h
  have hle : 2 * Nat.log 2 n + 2 ≤ Nat.log 2 (n ^ 2) := by
    exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
  have hpow : 2 ^ (2 * Nat.log 2 n + 2) ≤ n ^ 2 :=
    Nat.pow_le_of_le_log (pow_ne_zero 2 (Nat.ne_of_gt hn)) hle
  exact (not_lt_of_ge hpow) hsq

/-- For `k ∈ Kₙ`: `k ≤ 2·log₂ n + 1` (elementary, via the binomial bound). -/
lemma k_le_two_log2_add_one_of_mem_K {n k : ℕ} (hk : k ∈ K n) (hn : 0 < n) :
    k ≤ 2 * Nat.log 2 n + 1 := by
  have hk_lt : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hdvd : lcm1to k ∣ n - k := (Finset.mem_filter.mp hk).2
  have hlcm_le : lcm1to k ≤ n - k := Nat.le_of_dvd (Nat.sub_pos_of_lt hk_lt) hdvd
  have hlcm_le_n : lcm1to k ≤ n := le_trans hlcm_le (Nat.sub_le n k)
  have htwo : 2 ^ k ≤ (k + 1) * lcm1to k := two_pow_le_mul_lcm1to k
  have htwo_n : 2 ^ k ≤ (k + 1) * n := le_trans htwo (Nat.mul_le_mul_left (k + 1) hlcm_le_n)
  have hkn : (k + 1) * n ≤ n ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega : k + 1 ≤ n) le_rfl
  have htwo_n2 : 2 ^ k ≤ n ^ 2 := le_trans htwo_n hkn
  have hlog : k ≤ Nat.log 2 (n ^ 2) :=
    Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) htwo_n2
  exact le_trans hlog (log_two_sq_le_two_mul_add_one hn)

/-- `k₀(n) ≤ 2·log₂ n + 1` for `n ≥ 16`. -/
lemma k0_le_two_log2_add_one (n : ℕ) (hn : 16 ≤ n) : k0 n ≤ 2 * Nat.log 2 n + 1 := by
  have hk0 : k0 n ∈ K n := k0_mem_K n (by omega : 0 < n)
  by_cases h2 : 2 ≤ k0 n
  · exact k_le_two_log2_add_one_of_mem_K hk0 (by omega : 0 < n)
  · have hle1 : k0 n ≤ 1 := by omega
    have hlog : 4 ≤ Nat.log 2 n := by
      exact Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) (by simpa using hn)
    omega

/-- `4·log₂ n + 4 ≤ n` for `n ≥ 64`. -/
lemma four_mul_log2_add_four_le (n : ℕ) (hn : 64 ≤ n) : 4 * Nat.log 2 n + 4 ≤ n := by
  let m := Nat.log 2 n
  have hm6 : 6 ≤ m := by
    dsimp [m]
    exact Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) (by simpa using hn)
  have h4m : 4 * m + 4 ≤ 2 ^ m := by
    have hbase : 4 * 6 + 4 ≤ 2 ^ 6 := by norm_num
    have hstep : ∀ t (ht : 6 ≤ t), 4 * t + 4 ≤ 2 ^ t → 4 * (t + 1) + 4 ≤ 2 ^ (t + 1) := by
      intro t ht ih
      rw [show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by
        rw [pow_succ]
        ring]
      nlinarith [ih]
    exact (Nat.le_induction (m := 6) (P := fun t _ => 4 * t + 4 ≤ 2 ^ t) hbase hstep m hm6)
  have hpow_le : 2 ^ m ≤ n := by
    dsimp [m]
    exact Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  omega

/-- `2·log₂ n + 1 ≤ n/2` for `n ≥ 64`. -/
lemma two_mul_log2_add_one_le_half (n : ℕ) (hn : 64 ≤ n) :
    2 * Nat.log 2 n + 1 ≤ n / 2 := by
  have h := four_mul_log2_add_four_le n hn
  have hdiv : 2 * Nat.log 2 n + 2 ≤ n / 2 := by omega
  omega

/-- `k₀(n) ≤ n/2` for `n ≥ 64`. -/
lemma k0_le_half (n : ℕ) (hn : 64 ≤ n) : k0 n ≤ n / 2 := by
  exact le_trans (k0_le_two_log2_add_one n (by omega : 16 ≤ n)) (two_mul_log2_add_one_le_half n hn)

/-- `1/2 < log 2` (so `1/log 2 < 2`). -/
private lemma log_two_gt_one_half : (1 : ℝ) / 2 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : 0 < (2 : ℝ))]
  have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlt : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 4)
  have hsqlt : Real.exp (1 / 2) ^ 2 < (2 : ℝ) ^ 2 := by
    norm_num
    exact hsq ▸ hlt
  exact (sq_lt_sq₀ (le_of_lt (Real.exp_pos _)) (by norm_num : 0 ≤ (2 : ℝ))).mp hsqlt

/-- `Nat.log 2 n ≤ 2·log n` (over ℝ) for `n ≥ 2`. -/
lemma natLog_two_le_two_log {n : ℕ} (hn : 2 ≤ n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hlog : Real.log ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity : 0 < ((2 ^ Nat.log 2 n : ℕ) : ℝ)) (by exact_mod_cast hpow)
  rw [Nat.cast_pow] at hlog
  have hlogpow : Real.log (((2 : ℕ) : ℝ) ^ Nat.log 2 n) = (Nat.log 2 n : ℝ) * Real.log 2 :=
    Real.log_pow ((2 : ℕ) : ℝ) (Nat.log 2 n)
  rw [hlogpow] at hlog
  have h1 : (Nat.log 2 n : ℝ) * (1 / 2) ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (le_of_lt log_two_gt_one_half) (by exact_mod_cast (Nat.zero_le (Nat.log 2 n)))
  nlinarith [hlog, h1]

/-- **Remark (`rem:sharp_asymp`)**: `M(n) = 1/n + O(log n/n²)`. -/
theorem M_sub_one_div_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |M n - (1 : ℝ) / (n : ℝ)| ≤ C * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
  rcases prop_exact_order with ⟨C₁, hC₁pos, N₁, hN₁⟩
  rcases Filter.eventually_atTop.mp theorem_equality_case with ⟨N₂, hN₂⟩
  let N₀ : ℕ := max (max N₁ N₂) (max 64 (Nat.ceil (C₁ ^ 2) + 1))
  refine ⟨15, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
  have hnN₁ : N₁ ≤ n := by
    have hN₀ : N₀ ≤ n := hn
    dsimp [N₀] at hN₀
    have h1 : max N₁ N₂ ≤ n := le_trans (le_max_left _ _) hN₀
    exact le_trans (le_max_left _ _) h1
  have hnN₂ : N₂ ≤ n := by
    have hN₀ : N₀ ≤ n := hn
    dsimp [N₀] at hN₀
    have h1 : max N₁ N₂ ≤ n := le_trans (le_max_left _ _) hN₀
    exact le_trans (le_max_right _ _) h1
  have hn64 : 64 ≤ n := by
    have hN₀ : N₀ ≤ n := hn
    dsimp [N₀] at hN₀
    have h1 : max 64 (Nat.ceil (C₁ ^ 2) + 1) ≤ n := le_trans (le_max_right _ _) hN₀
    exact le_trans (le_max_left _ _) h1
  have hnpos : 0 < n := by omega
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnRnn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hk0 : k0 n ∈ K n := k0_mem_K n hnpos
  have hk0_lt : k0 n < n := Finset.mem_range.mp (Finset.mem_filter.mp hk0).1
  have hnk0_pos : 0 < ((n - k0 n : ℕ) : ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk0_lt)
  have hk0_le_half : k0 n ≤ n / 2 := k0_le_half n hn64
  have hhalf : (n : ℝ) / 2 ≤ ((n - k0 n : ℕ) : ℝ) := by
    have h2k0 : 2 * k0 n ≤ n := by
      have h1 : 2 * k0 n ≤ 2 * (n / 2) := Nat.mul_le_mul_left 2 hk0_le_half
      have h2 : 2 * (n / 2) ≤ n := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self n 2
      exact le_trans h1 h2
    have hR : 2 * (k0 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2k0
    have hsub : (n : ℝ) - (k0 n : ℝ) = ((n - k0 n : ℕ) : ℝ) := by
      rw [← Nat.cast_sub (Nat.le_of_lt hk0_lt)]
    nlinarith
  have hpEq : p n (n - k0 n) = M n := (hN₂ n hnN₂ (n - k0 n)).2 rfl
  have hpk0 := hN₁ n hnN₁ (k0 n) hk0
  -- η 界：0 ≤ η ≤ 4/n²
  have heta_nonneg : 0 ≤ eta n (k0 n) := eta_nonneg n (k0 n)
  have heta_le : eta n (k0 n) ≤ (4 : ℝ) / (n : ℝ) ^ 2 := by
    by_cases hk02 : 2 ≤ k0 n
    · have h1 := eta_le_inv_sq n (k0 n) hk02 hk0_lt
      have h2 : (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) ^ 2 ≤ (4 : ℝ) / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_ne_zero (ne_of_gt hnk0_pos)) (pow_pos hnRpos 2)]
        have hnle : (n : ℝ) ≤ 2 * ((n - k0 n : ℕ) : ℝ) := by nlinarith [hhalf]
        have hsq' : (n : ℝ) ^ 2 ≤ (2 * ((n - k0 n : ℕ) : ℝ)) ^ 2 := by
          refine sq_le_sq' ?_ ?_
          · nlinarith [hhalf, hnRnn]
          · exact hnle
        nlinarith [hsq']
      exact le_trans h1 h2
    · have hk0_le1 : k0 n ≤ 1 := by omega
      rw [eta_eq_zero_of_le_one n (k0 n) hk0_le1]
      exact div_nonneg (by norm_num : 0 ≤ (4 : ℝ)) (sq_nonneg (n : ℝ))
  -- 1/(n-k0) - 1/n 的界
  have hdiff_inv : (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ) =
      (k0 n : ℝ) / ((n : ℝ) * ((n - k0 n : ℕ) : ℝ)) := by
    rw [show (k0 n : ℝ) = (n : ℝ) - ((n - k0 n : ℕ) : ℝ) by
      rw [Nat.cast_sub (Nat.le_of_lt hk0_lt)]
      ring]
    field_simp [ne_of_gt hnRpos, ne_of_gt hnk0_pos]
  have hdiff_inv_nonneg : 0 ≤ (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ) := by
    rw [hdiff_inv]
    exact div_nonneg (by exact_mod_cast (Nat.zero_le (k0 n))) (le_of_lt (mul_pos hnRpos hnk0_pos))
  have hdiff_inv_le : (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ) ≤
      ((2 : ℝ) * ((2 * Nat.log 2 n : ℕ) : ℝ) + 2) / (n : ℝ) ^ 2 := by
    rw [hdiff_inv]
    have hk0b : (k0 n : ℝ) ≤ ((2 * Nat.log 2 n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (k0_le_two_log2_add_one n (by omega : 16 ≤ n))
    have hden : (n : ℝ) * (n : ℝ) / 2 ≤ (n : ℝ) * ((n - k0 n : ℕ) : ℝ) := by
      rw [mul_comm]
      rw [show (n : ℝ) * (n : ℝ) / 2 = (n : ℝ) * ((n : ℝ) / 2) by ring]
      exact mul_le_mul_of_nonneg_left hhalf (by exact_mod_cast (Nat.zero_le n))
    have hfrac : (k0 n : ℝ) / ((n : ℝ) * ((n - k0 n : ℕ) : ℝ)) ≤
        ((2 * Nat.log 2 n + 1 : ℕ) : ℝ) / ((n : ℝ) * (n : ℝ) / 2) := by
      rw [div_le_div_iff₀ (mul_pos hnRpos hnk0_pos) (by positivity : 0 < (n : ℝ) * (n : ℝ) / 2)]
      exact mul_le_mul hk0b hden (by positivity : 0 ≤ (n : ℝ) * (n : ℝ) / 2) (by exact_mod_cast (Nat.zero_le (2 * Nat.log 2 n + 1)))
    have halg : ((2 * Nat.log 2 n + 1 : ℕ) : ℝ) / ((n : ℝ) * (n : ℝ) / 2) =
        ((2 : ℝ) * ((2 * Nat.log 2 n : ℕ) : ℝ) + 2) / (n : ℝ) ^ 2 := by
      rw [Nat.cast_add, Nat.cast_mul]
      rw [pow_two]
      field_simp [ne_of_gt hnRpos]
      ring
    exact le_trans hfrac (le_of_eq halg)
  -- C₁ 误差截断：C₁ n^{-149/56} ≤ 1/n²
  have hnC₁ : C₁ / (n : ℝ) ^ (149/56 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by
    have hn2 : C₁ ^ 2 ≤ (n : ℝ) := by
      have hceil : Nat.ceil (C₁ ^ 2) < n := by
        have hN₀ : N₀ ≤ n := hn
        dsimp [N₀] at hN₀
        have h1 : max 64 (Nat.ceil (C₁ ^ 2) + 1) ≤ n := le_trans (le_max_right _ _) hN₀
        have h2 : Nat.ceil (C₁ ^ 2) + 1 ≤ n := le_trans (le_max_right _ _) h1
        omega
      exact le_trans (Nat.le_ceil (C₁ ^ 2)) (by exact_mod_cast (le_of_lt hceil))
    have hsqrt : C₁ ≤ (n : ℝ) ^ (1/2 : ℝ) := by
      have hmono : (C₁ ^ 2) ^ (1/2 : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow (by nlinarith [hC₁pos] : 0 ≤ C₁ ^ 2) hn2 (by norm_num : 0 ≤ (1/2 : ℝ))
      have hleft : (C₁ ^ 2) ^ (1/2 : ℝ) = C₁ := by
        calc (C₁ ^ 2) ^ (1/2 : ℝ) = ((C₁ : ℝ) ^ (2 : ℝ)) ^ (1/2 : ℝ) := by
              rw [show (C₁ ^ 2 : ℝ) = (C₁ : ℝ) ^ (2 : ℝ) by exact (Real.rpow_natCast (C₁ : ℝ) 2).symm]
          _ = (C₁ : ℝ) ^ ((2 : ℝ) * (1/2 : ℝ)) :=
              (Real.rpow_mul (le_of_lt hC₁pos) (2 : ℝ) (1/2 : ℝ)).symm
          _ = (C₁ : ℝ) ^ (1 : ℝ) := by congr 1; norm_num
          _ = C₁ := Real.rpow_one (C₁ : ℝ)
      rwa [← hleft]
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hnRpos _) (pow_pos hnRpos 2)]
    have h3 : C₁ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity : 0 ≤ (n : ℝ) ^ 2)
    have h4 : (n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ (5/2 : ℝ) := by
      rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by exact (Real.rpow_natCast (n : ℝ) 2).symm]
      rw [← Real.rpow_add hnRpos (1/2 : ℝ) (2 : ℝ)]
      congr 1
      norm_num
    have h4b : (n : ℝ) ^ (5/2 : ℝ) ≤ (n : ℝ) ^ (149/56 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact by exact_mod_cast (by omega : 1 ≤ n)
      · norm_num
    have htotal : C₁ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (149/56 : ℝ) := by
      calc C₁ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (1/2 : ℝ) * (n : ℝ) ^ 2 := h3
        _ = (n : ℝ) ^ (5/2 : ℝ) := h4
        _ ≤ (n : ℝ) ^ (149/56 : ℝ) := h4b
    simpa using htotal
  -- log 界
  have hlog' : ((2 * Nat.log 2 n : ℕ) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    rw [Nat.cast_mul]
    have h1 : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := natLog_two_le_two_log (by omega : 2 ≤ n)
    have h2 : 2 * (Nat.log 2 n : ℝ) ≤ 4 * Real.log (n : ℝ) := by
      nlinarith [h1]
    exact h2
  have hlog_pos : 1 ≤ Real.log (n : ℝ) := by
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
    have hle : Real.log (3 : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num : 0 < (3 : ℝ)) hn3
    have hlog3 : 1 ≤ Real.log (3 : ℝ) := by
      rw [← Real.log_exp (1 : ℝ)]
      exact Real.log_le_log (Real.exp_pos 1) (by
        have h := Real.exp_one_lt_d9
        exact le_trans (le_of_lt h) (by norm_num : (2.7182818286 : ℝ) ≤ 3))
    exact le_trans hlog3 hle
  -- 主分解
  have hmain1 : |M n - (1 : ℝ) / (n : ℝ)| ≤
      C₁ / (n : ℝ) ^ (149/56 : ℝ) + eta n (k0 n) +
      ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ)) := by
    rw [← hpEq]
    have habs : |(1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n) - (1 : ℝ) / (n : ℝ)| ≤
        eta n (k0 n) + ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ)) := by
      rw [show (1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n) - (1 : ℝ) / (n : ℝ) =
          eta n (k0 n) + ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ)) by ring]
      rw [abs_of_nonneg (add_nonneg heta_nonneg hdiff_inv_nonneg)]
    calc |p n (n - k0 n) - (1 : ℝ) / (n : ℝ)|
        = |(p n (n - k0 n) - ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n))) +
            (((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n)) - (1 : ℝ) / (n : ℝ))| := by
              congr 1
              ring
      _ ≤ |p n (n - k0 n) - ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n))| +
          |(1 : ℝ) / ((n - k0 n : ℕ) : ℝ) + eta n (k0 n) - (1 : ℝ) / (n : ℝ)| := abs_add_le _ _
      _ ≤ C₁ / (n : ℝ) ^ (149/56 : ℝ) + eta n (k0 n) +
          ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ)) := by
            nlinarith [hpk0, habs]
  -- 收紧
  have hsum : C₁ / (n : ℝ) ^ (149/56 : ℝ) + eta n (k0 n) +
      ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ)) ≤
      (15 : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
    have hn2pos : 0 < (n : ℝ) ^ 2 := pow_pos hnRpos 2
    have h12 : C₁ / (n : ℝ) ^ (149/56 : ℝ) + eta n (k0 n) ≤ (1 : ℝ) / (n : ℝ) ^ 2 + (4 : ℝ) / (n : ℝ) ^ 2 :=
      add_le_add hnC₁ heta_le
    have h123 : C₁ / (n : ℝ) ^ (149/56 : ℝ) + eta n (k0 n) +
        ((1 : ℝ) / ((n - k0 n : ℕ) : ℝ) - (1 : ℝ) / (n : ℝ)) ≤
        (1 : ℝ) / (n : ℝ) ^ 2 + (4 : ℝ) / (n : ℝ) ^ 2 +
        ((2 : ℝ) * ((2 * Nat.log 2 n : ℕ) : ℝ) + 2) / (n : ℝ) ^ 2 := by
      nlinarith [h12, hdiff_inv_le]
    have hnum : (1 : ℝ) / (n : ℝ) ^ 2 + (4 : ℝ) / (n : ℝ) ^ 2 +
        ((2 : ℝ) * ((2 * Nat.log 2 n : ℕ) : ℝ) + 2) / (n : ℝ) ^ 2 =
        ((1 + 4 + ((2 : ℝ) * ((2 * Nat.log 2 n : ℕ) : ℝ) + 2)) / (n : ℝ) ^ 2) := by
      rw [← add_div]
      rw [← add_div]
    rw [hnum] at h123
    have hnum_le : (1 + 4 + ((2 : ℝ) * ((2 * Nat.log 2 n : ℕ) : ℝ) + 2)) / (n : ℝ) ^ 2 ≤
        (15 : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hn2pos hn2pos]
      nlinarith [hlog', hlog_pos]
    exact le_trans h123 hnum_le
  exact le_trans hmain1 hsum

end MostProbableOrder
