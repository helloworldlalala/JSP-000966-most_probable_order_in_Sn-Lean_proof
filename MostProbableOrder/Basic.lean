import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# The most probable order of a random permutation — formalization kernel

Faithful transcription of the setup of

  Adrian Beker, *The most probable order of a random permutation*,
  arXiv:2510.11698v1 (Oct 2025).

This file transcribes the paper's definitions exactly and proves the
self-contained, elementary lemmas used in the proof of Theorem 1.2, in a
completely rigorous way: every declaration is fully proved, with no unfinished
goals and no custom assumptions introduced.

The deep analytic engine (Proposition 3.1 and Proposition 4.1), which rely
on Acan et al. [1], Erdős–Turán [4] and Warlimont [11], none currently in
mathlib, is not part of this kernel; see `docs/PROOF_MAP.md`.
-/

open Finset

namespace MostProbableOrder

/-- The symmetric group `Sₙ` on `Fin n`. -/
abbrev SymmetricGroup (n : ℕ) : Type := Equiv.Perm (Fin n)

/-- The total number of permutations, `|Sₙ| = n!`. -/
lemma card_symmetricGroup (n : ℕ) : Fintype.card (SymmetricGroup n) = Nat.factorial n := by
  have h := Fintype.card_perm (α := Fin n)
  rwa [Fintype.card_fin] at h

/-- Bridge to the paper's Fact 2.1: `ord(π)` is the lcm of the cycle lengths
of `π`. This is exactly mathlib's `lcm_cycleType`, and is what justifies
defining `p n m` by filtering on `orderOf π = m`. -/
lemma order_eq_lcm_cycleType (π : SymmetricGroup n) : π.cycleType.lcm = orderOf π :=
  Equiv.Perm.lcm_cycleType π

/-- `pₙ(m)`: the probability that a uniformly random permutation of `[n]`
has order exactly `m`. (Paper, §1.) -/
noncomputable def p (n m : ℕ) : ℝ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => orderOf π = m)).card /
    (Nat.factorial n : ℝ)

/-- `M(n) := ‖pₙ‖_{ℓ∞(ℕ)} = max_m pₙ(m)`. (Paper, §1, below (2).)
Every order divides `n!`, so the maximum is attained over `m ≤ n!`. -/
noncomputable def M (n : ℕ) : ℝ :=
  (Finset.range (Nat.factorial n + 1)).fold max 0 (fun m => p n m)

/-- `lcm(1,2,…,k)` (with the convention `lcm(∅) = 1`, i.e. `lcm(1,…,0) = 1`). -/
def lcm1to (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

/-- `Kₙ := { k ∈ {0,…,n-1} : lcm(1,2,…,k) | n-k }`. (Paper, §2.) -/
def K (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun k => lcm1to k ∣ n - k)

/-- `lcm1to` is monotone: `k ≤ k₀ ⇒ lcm(1,…,k) | lcm(1,…,k₀)`. -/
lemma lcm1to_dvd_of_le {k k₀ : ℕ} (h : k ≤ k₀) : lcm1to k ∣ lcm1to k₀ := by
  have hsub : Finset.Icc 1 k ⊆ Finset.Icc 1 k₀ := by
    simp only [subset_iff, mem_Icc]; omega
  exact Finset.lcm_mono hsub

/-- `lcm(1,…,k)` is divisible by `(k-1)·k` for `k ≥ 2` (since `gcd(k-1,k)=1`). -/
lemma lcm1to_dvd_mul_pred_self {k : ℕ} (hk : 2 ≤ k) : (k - 1) * k ∣ lcm1to k := by
  have hk1_mem : k - 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le k 1⟩
  have hk_mem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hdvd1 : k - 1 ∣ lcm1to k := by
    unfold lcm1to
    exact Finset.dvd_lcm hk1_mem
  have hdvd2 : k ∣ lcm1to k := by
    unfold lcm1to
    exact Finset.dvd_lcm hk_mem
  have hcop : Nat.Coprime (k - 1) k :=
    (Nat.coprime_self_sub_left (show 1 ≤ k by omega)).mpr (Nat.coprime_one_left k)
  exact hcop.mul_dvd_of_dvd_of_dvd hdvd1 hdvd2

/-- `lcm(1,…,k) > k` for `k ≥ 3`. -/
lemma lcm1to_gt_self {k : ℕ} (hk : 3 ≤ k) : k < lcm1to k := by
  have hdvd : (k - 1) * k ∣ lcm1to k := lcm1to_dvd_mul_pred_self (by omega : 2 ≤ k)
  have hlcm_ne : lcm1to k ≠ 0 := by
    unfold lcm1to
    intro h0
    rcases (Finset.lcm_eq_zero_iff.mp h0) with ⟨x, hx, hx0⟩
    have hx_ge : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    have hx_eq0 : x = 0 := by simpa using hx0
    omega
  have hlcm_pos : 0 < lcm1to k := Nat.pos_of_ne_zero hlcm_ne
  have hge : (k - 1) * k ≤ lcm1to k := Nat.le_of_dvd hlcm_pos hdvd
  have hkpos : 0 < k := by omega
  have h1 : k < 2 * k := by
    have := (Nat.mul_lt_mul_right hkpos).mpr (show (1 : ℕ) < 2 by norm_num)
    simpa [one_mul] using this
  have h2 : 2 * k ≤ (k - 1) * k := Nat.mul_le_mul_right k (by omega : 2 ≤ k - 1)
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 h2) hge

/-- For `k ∈ Kₙ` (and `n ≥ 5`), one has `k < n-k`: the `(n-k)`-cycle is the unique
long cycle. This is the elementary half of the paper's remark that `max Kₙ ≪ log n`
(the full `log n` bound would use the prime number theorem, but `k < n-k` already
suffices for the main-term separation in Proposition 4.1). -/
lemma k_lt_sub_of_mem_K {n k : ℕ} (hk : k ∈ K n) (hn : 5 ≤ n) : k < n - k := by
  have hk_lt_n : k < n := mem_range.mp (mem_filter.mp hk).1
  by_cases hk3 : 3 ≤ k
  · have hgt : k < lcm1to k := lcm1to_gt_self hk3
    have hle : lcm1to k ≤ n - k := Nat.le_of_dvd (by omega : 0 < n - k) (mem_filter.mp hk).2
    exact lt_of_lt_of_le hgt hle
  · -- k ≤ 2
    have hk_le : k ≤ 2 := by omega
    have hnk : 3 ≤ n - k := by omega
    exact lt_of_le_of_lt hk_le hnk

/-- `k=0` and `k=1` always belong to `Kₙ` (the paper notes `{0,1} ⊂ Kₙ`). -/
lemma mem_K_zero (n : ℕ) (hn : 0 < n) : 0 ∈ K n := by
  have h0 : lcm1to 0 = 1 := by simp [lcm1to]
  simp only [K, mem_filter, mem_range, h0]; exact ⟨hn, one_dvd n⟩

lemma mem_K_one (n : ℕ) (hn : 1 < n) : 1 ∈ K n := by
  have h1 : lcm1to 1 = 1 := by simp [lcm1to]
  simp only [K, mem_filter, mem_range, h1]; exact ⟨by omega, one_dvd (n - 1)⟩

/-- An `n`-cycle (a single cycle whose support is all of `Fin n`) has order `n`.
This is the event contributing the exact `1/n` lower bound in the paper's
equation (2). -/
lemma orderOf_fullCycle (π : SymmetricGroup n) (hπ : π.IsCycle)
    (hs : π.support = (Finset.univ : Finset (Fin n))) : orderOf π = n := by
  rw [hπ.orderOf, hs, Finset.card_univ, Fintype.card_fin]

/-! ### The explicit full cycle

mathlib's `finRotate n : Equiv.Perm (Fin n)` is the cyclic shift `i ↦ i+1`,
the cycle `(1 2 … n)`. Its cycle-theoretic properties are already available
(`isCycle_finRotate_of_le`, `support_finRotate_of_le`, `cycleType_finRotate_of_le`),
which lets us discharge the existence of an `n`-cycle without any orbit argument. -/

/-- The rotation `i ↦ i+1 mod n` on `Fin n`. -/
def rotation {n : ℕ} : SymmetricGroup n := finRotate n

/-- For `n ≥ 2`, `rotation` is a single cycle. (MP-001 discharged via mathlib.) -/
lemma rotation_isCycle {n : ℕ} (hn : 2 ≤ n) : (rotation (n := n)).IsCycle :=
  isCycle_finRotate_of_le hn

/-- For `n ≥ 2`, `rotation` has full support. -/
lemma rotation_support {n : ℕ} (hn : 2 ≤ n) :
    (rotation (n := n)).support = (Finset.univ : Finset (Fin n)) :=
  support_finRotate_of_le hn

/-- For `n ≥ 2`, `rotation` has cycle type `{n}`. -/
lemma rotation_cycleType {n : ℕ} (hn : 2 ≤ n) :
    (rotation (n := n)).cycleType = ({n} : Multiset ℕ) :=
  cycleType_finRotate_of_le hn

/-- The rotation is a permutation of order exactly `n`. -/
lemma orderOf_rotation {n : ℕ} (hn : 2 ≤ n) : orderOf (rotation (n := n)) = n :=
  orderOf_fullCycle _ (rotation_isCycle hn) (rotation_support hn)

/-! ### Counting `n`-cycles and the lower bound (2) -/

/-- The number of permutations of `Fin n` of cycle type `{n}` (i.e. single
`n`-cycles) is `(n-1)!`, for `n ≥ 2`. Instance of the Cauchy formula
`Equiv.Perm.card_of_cycleType_singleton`. -/
lemma card_cycleType_singleton (n : ℕ) (hn : 2 ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun g => g.cycleType = ({n} : Multiset ℕ))).card = Nat.factorial (n - 1) := by
  have h := Equiv.Perm.card_of_cycleType_singleton (α := Fin n) hn (le_of_eq (by simp))
  rw [show #({g : SymmetricGroup n | g.cycleType = ({n} : Multiset ℕ)}
        : Finset (SymmetricGroup n))
      = ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun g => g.cycleType = ({n} : Multiset ℕ))).card from rfl] at h
  rw [h, Fintype.card_fin, Nat.choose_self, mul_one]

/-- A permutation of cycle type `{n}` has order `n`. -/
lemma orderOf_of_cycleType_singleton {n : ℕ} {g : SymmetricGroup n}
    (hg : g.cycleType = ({n} : Multiset ℕ)) : orderOf g = n := by
  rw [← Equiv.Perm.lcm_cycleType, hg]; simp

/-- The set of permutations of cycle type `{n}` is contained in the set of
permutations of order `n`. -/
lemma cycleType_singleton_subset_orderOf (n : ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun g => g.cycleType = ({n} : Multiset ℕ)))
      ⊆ ((Finset.univ : Finset (SymmetricGroup n)).filter (fun g => orderOf g = n)) := by
  intro g hg
  rw [Finset.mem_filter] at hg ⊢
  exact ⟨Finset.mem_univ g, orderOf_of_cycleType_singleton hg.2⟩

/-- `(n-1)! ≤ #{π : orderOf π = n}` for `n ≥ 2`. -/
lemma factorial_pred_le_card_orderOf (n : ℕ) (hn : 2 ≤ n) :
    Nat.factorial (n - 1) ≤ ((Finset.univ : Finset (SymmetricGroup n)).filter
      (fun g => orderOf g = n)).card := by
  calc Nat.factorial (n - 1)
      = ((Finset.univ : Finset (SymmetricGroup n)).filter
          (fun g => g.cycleType = ({n} : Multiset ℕ))).card :=
        (card_cycleType_singleton n hn).symm
    _ ≤ _ := Finset.card_le_card (cycleType_singleton_subset_orderOf n)

/-- **Equation (2)**, lower bound: `pₙ(n) ≥ 1/n` for `n ≥ 2`. -/
theorem one_div_le_p_self (n : ℕ) (hn : 2 ≤ n) : (1 : ℝ) / n ≤ p n n := by
  unfold p
  have hfac : (Nat.factorial n : ℝ) = (Nat.factorial (n - 1) : ℝ) * (n : ℝ) := by
    have h0 : Nat.factorial n = Nat.factorial (n - 1) * n := by
      rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), mul_comm]
    rw [h0, Nat.cast_mul]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)) (by positivity), one_mul, hfac]
  have hcast : (Nat.factorial (n - 1) : ℝ) ≤
      (((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun g => orderOf g = n)).card : ℝ) := by
    exact_mod_cast factorial_pred_le_card_orderOf n hn
  exact mul_le_mul_of_nonneg_right hcast (by positivity)

/-! ### The divisibility lemma for the final comparison in Theorem 1.2 -/

/-- The elementary divisibility lemma at the heart of the final comparison
in the proof of Theorem 1.2 (paper p.7): if `k, k₀ ∈ Kₙ` and `k ≤ k₀`,
then `lcm(1,…,k) | k₀ - k`.

Proof as in the paper: `lcm(1,…,k)` divides both `n-k` (since `k ∈ Kₙ`)
and `n-k₀` (since `lcm(1,…,k) | lcm(1,…,k₀) | n-k₀`), hence divides their
difference `(n-k) - (n-k₀) = k₀ - k`. -/
lemma K_dvd_diff {n k k₀ : ℕ} (hk : k ∈ K n) (hk₀ : k₀ ∈ K n) (h : k ≤ k₀) :
    lcm1to k ∣ k₀ - k := by
  have hk_lt_n : k < n := mem_range.mp (mem_filter.mp hk).1
  have hk₀_lt_n : k₀ < n := mem_range.mp (mem_filter.mp hk₀).1
  have h1 : lcm1to k ∣ n - k := (mem_filter.mp hk).2
  have h2 : lcm1to k ∣ lcm1to k₀ := lcm1to_dvd_of_le h
  have h3 : lcm1to k₀ ∣ n - k₀ := (mem_filter.mp hk₀).2
  have h4 : lcm1to k ∣ n - k₀ := dvd_trans h2 h3
  have hle : n - k₀ ≤ n - k := by omega
  have h7 : lcm1to k ∣ (n - k) - (n - k₀) := Nat.dvd_sub h1 h4
  have heq : (n - k) - (n - k₀) = k₀ - k := by
    rw [tsub_tsub]; omega
  rw [heq] at h7; exact h7

end MostProbableOrder
