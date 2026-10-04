import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import MostProbableOrder.Arithmetic.FactorialBounds

/-!
# Divisor and prime-factor growth bounds (M2b)

Definitions of the arithmetic functions `τ`, `ω`, `σ` used by the paper
(§2, "we use the standard notation `τ(m)`, `σ(m)` and `ω(m)` for the number,
sum of positive divisors and the number of prime factors of `m`"), together
with the growth bounds feeding Proposition 3.1 and Theorem 1.1:

* `τ(m) ≤ C(ε) · m^ε`             (`tau_le_rpow`)
* `ω(m) ≤ C · log m / log log m`  (`omega_le_log_div_loglog`)
* `σ(m)/m ≤ C · log log m`        (`sigma_div_le_loglog`)
* `∑_{p ≤ x} 1/p ≤ log log x + B` (`sum_inv_primes_le`)

The elementary parts are proved here; the four deep bounds are stated with
registered temporary goals (see `SORRY.md`, MP-002..MP-005) providing the
interfaces consumed downstream.
-/

open Finset
open scoped Real Nat.Prime

namespace MostProbableOrder

/-- `τ(m)`: the number of positive divisors of `m`. (Paper §2.) -/
def tau (m : ℕ) : ℕ := m.divisors.card

/-- `ω(m)`: the number of distinct prime factors of `m`. (Paper §2.) -/
def omega (m : ℕ) : ℕ := m.primeFactors.card

/-- `σ(m)`: the sum of the positive divisors of `m`. (Paper §2.) -/
def sigma (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d

@[simp] lemma tau_eq (m : ℕ) : tau m = m.divisors.card := rfl
@[simp] lemma omega_eq (m : ℕ) : omega m = m.primeFactors.card := rfl
@[simp] lemma sigma_eq (m : ℕ) : sigma m = ∑ d ∈ m.divisors, d := rfl

/-- `σ` agrees with mathlib's `ArithmeticFunction.sigma`; this exposes the
multiplicativity API (`isMultiplicative_sigma`) downstream. -/
lemma sigma_eq_sigma_one (m : ℕ) : sigma m = ArithmeticFunction.sigma 1 m := by
  rw [ArithmeticFunction.sigma_one_apply]; rfl

/-- Every prime factor of `m` is at least `2`. -/
lemma two_le_of_mem_primeFactors {m p : ℕ} (hp : p ∈ m.primeFactors) : 2 ≤ p :=
  ((Nat.mem_primeFactors.mp hp).1).two_le

/-- `2^{ω(m)} ≤ ∏_{p | m} p`: the product of the distinct prime factors of `m`
dominates `2` to the number of prime factors. -/
lemma pow_two_omega_le_prod_primeFactors (m : ℕ) :
    (2 : ℕ) ^ omega m ≤ ∏ p ∈ m.primeFactors, p := by
  have hprod : (∏ _p ∈ m.primeFactors, (2 : ℕ)) = 2 ^ omega m := by
    rw [Finset.prod_const, omega]
  rw [← hprod]
  exact Finset.prod_le_prod (fun p _ => by norm_num)
    (fun p hp => two_le_of_mem_primeFactors hp)

/-- `∏_{p | m} p ≤ m` for `m ≠ 0`, since the product of the distinct prime
factors divides `m`. -/
lemma prod_primeFactors_le {m : ℕ} (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, p ≤ m :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-- `2^{ω(m)} ≤ m` for `m ≠ 0`. -/
lemma pow_two_omega_le {m : ℕ} (hm : m ≠ 0) : (2 : ℕ) ^ omega m ≤ m :=
  le_trans (pow_two_omega_le_prod_primeFactors m) (prod_primeFactors_le hm)

/-- Elementary bound `ω(m) ≤ log₂ m` for `m ≠ 0`. -/
lemma omega_le_log_two {m : ℕ} (hm : m ≠ 0) : omega m ≤ Nat.log 2 m :=
  (Nat.le_log_iff_pow_le (by norm_num) hm).mpr (pow_two_omega_le hm)

/-! ### Sorting: `(ω(m)+1)! ≤ ∏_{p|m} p` (ingredient of MP-003) -/

/-- The `i`-th element of a strictly increasing list of naturals, all `≥ 2`,
is at least `i + 2`. -/
private lemma list_getElem_add_two_le {l : List ℕ} (hs : l.SortedLT) (hmin : ∀ x ∈ l, 2 ≤ x) :
    ∀ i (hi : i < l.length), i + 2 ≤ l[i] := by
  intro i
  induction i with
  | zero =>
      intro hi
      exact hmin (l[0]) (List.getElem_mem hi)
  | succ i ih =>
      intro hi
      have hlt : l[i] < l[i + 1] := by
        apply hs.getElem_lt_getElem_of_lt
        omega
      have ih' : i + 2 ≤ l[i] := ih (by omega)
      omega

/-- For an order embedding `e : Fin r ↪o ℕ` whose image is `s`, the product
over `s` equals the product of `e`. -/
private lemma prod_image_orderEmbOfFin {r : ℕ} (s : Finset ℕ) (e : Fin r ↪o ℕ)
    (he : Finset.image e Finset.univ = s) : (∏ p ∈ s, p) = ∏ i : Fin r, e i := by
  rw [← he]
  exact Finset.prod_image e.injective.injOn

/-- The `i`-th element of `s` in increasing order is at least `i + 2`, when all
elements of `s` are `≥ 2`. -/
private lemma orderEmbOfFin_add_two_le (s : Finset ℕ) (hmin : ∀ p ∈ s, 2 ≤ p) :
    ∀ i : Fin s.card, (i : ℕ) + 2 ≤ s.orderEmbOfFin rfl i := by
  have hsorted : (s.sort (· ≤ ·)).SortedLT := Finset.sortedLT_sort s
  have hminl : ∀ x ∈ s.sort (· ≤ ·), 2 ≤ x := by
    intro x hx
    exact hmin x (by simpa using hx)
  intro i
  change (i : ℕ) + 2 ≤ (s.sort (· ≤ ·))[i.val]'(by rw [Finset.length_sort]; exact i.2)
  exact list_getElem_add_two_le hsorted hminl i.val (by rw [Finset.length_sort]; exact i.2)

/-- `∏_{i<r} (i+2) = (r+1)!`. -/
private lemma prod_fin_add_two (r : ℕ) : (∏ i : Fin r, ((i : ℕ) + 2)) = (r + 1).factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      exact (mul_comm _ _).trans (Nat.factorial_succ (r + 1)).symm

/-- A finset of `r` naturals, each `≥ 2`, has product at least `(r+1)!`. -/
lemma factorial_succ_le_prod {s : Finset ℕ} (hmin : ∀ p ∈ s, 2 ≤ p) :
    (s.card + 1).factorial ≤ ∏ p ∈ s, p := by
  classical
  calc (s.card + 1).factorial
      = ∏ i : Fin s.card, ((i : ℕ) + 2) := (prod_fin_add_two s.card).symm
    _ ≤ ∏ i : Fin s.card, s.orderEmbOfFin rfl i := by
        exact Finset.prod_le_prod (fun i _ => Nat.zero_le _)
          (fun i _ => orderEmbOfFin_add_two_le s hmin i)
    _ = ∏ p ∈ s, p := by
        exact (prod_image_orderEmbOfFin (r := s.card) s (s.orderEmbOfFin rfl)
          (Finset.image_orderEmbOfFin_univ s rfl)).symm

/-- `(ω(m)+1)! ≤ m` for `m ≠ 0`, the arithmetic core of the bound
`ω(m) ≪ log m / log log m`. -/
lemma omega_factorial_le {m : ℕ} (hm : m ≠ 0) : (omega m + 1).factorial ≤ m := by
  calc (omega m + 1).factorial
      ≤ ∏ p ∈ m.primeFactors, p :=
        factorial_succ_le_prod (s := m.primeFactors) (fun p hp => two_le_of_mem_primeFactors hp)
    _ ≤ m := prod_primeFactors_le hm

/-! ### Deep growth bounds (interfaces; see `SORRY.md`) -/

set_option maxHeartbeats 800000 in
private lemma succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
      calc a + 2 ≤ 2 * (a + 1) := by omega
        _ ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (a + 1) := by rw [mul_comm, pow_succ]

set_option maxHeartbeats 800000 in
private lemma succ_pow_sixteen_le_two_mul {a : ℕ} (ha : 30 ≤ a) : (a + 1)^16 ≤ 2 * a^16 := by
  have h31 : 30 * (a + 1) ≤ 31 * a := by omega
  have hpow : (30 * (a + 1))^16 ≤ (31 * a)^16 := pow_le_pow_left₀ (by positivity) h31 16
  have hle : 30^16 * (a + 1)^16 ≤ 31^16 * a^16 := by simpa [mul_pow] using hpow
  have hconst : 31^16 ≤ 2 * 30^16 := by norm_num
  have hle3 : 30^16 * (a + 1)^16 ≤ 30^16 * (2 * a^16) := by
    calc 30^16 * (a + 1)^16 ≤ 31^16 * a^16 := hle
      _ ≤ (2 * 30^16) * a^16 := Nat.mul_le_mul_right (a^16) hconst
      _ = 30^16 * (2 * a^16) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hle3 (by positivity : 0 < 30^16)

set_option maxHeartbeats 800000 in
private lemma succ_pow_sixteen_le (a : ℕ) : (a + 1)^16 ≤ 2^(a + 130) := by
  refine Nat.strong_induction_on a ?_
  intro a ih
  by_cases ha : a < 30
  · have h1 : (a + 1)^16 ≤ 30^16 := pow_le_pow_left₀ (by positivity) (by omega : a + 1 ≤ 30) 16
    have h2 : 30^16 ≤ 2^80 := by norm_num
    have h3 : 2^80 ≤ 2^(a + 130) := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (by omega)
    linarith
  · have ih' : a^16 ≤ 2^(a + 129) := by
      have h := ih (a - 1) (Nat.sub_lt (by omega : 0 < a) (by norm_num : 0 < 1))
      have h1 : a - 1 + 1 = a := by omega
      have h2 : a - 1 + 130 = a + 129 := by omega
      simpa [h1, h2] using h
    have hstep : (a + 1)^16 ≤ 2 * a^16 := succ_pow_sixteen_le_two_mul (by omega)
    calc (a + 1)^16 ≤ 2 * a^16 := hstep
      _ ≤ 2 * 2^(a + 129) := Nat.mul_le_mul_left 2 ih'
      _ = 2^(a + 130) := by rw [mul_comm, ← pow_succ]

/-- **(MP-002, discharged)** `τ(m) = m^{o(1)}`, instantiated at `ε = 1/16`:
there is an absolute constant `C` such that `τ(m)^16 ≤ C·m` for every `m`, i.e.
`τ(m) ≤ C^{1/16}·m^{1/16}`. (Paper §2 "the well-known fact τ(m) ≤ m^{o(1)}"; the
proof of Theorem 1.1 only consumes `τ(m) ≤ C·m^{1/16}` since it assumes `m ≤ n^{4/3}`.)

The proof splits the prime factors of `m` into *small* (`p ≤ 2^16`) and *large*
(`p > 2^16`) primes. For large primes, `(a+1)^16 ≤ 2^{16a} ≤ p^a`; for small primes,
`(a+1)^16 ≤ 2^{a+130} ≤ 2^{130}·p^a`. -/
theorem tau_pow_sixteen_le : ∃ C : ℕ, ∀ m : ℕ, (tau m)^16 ≤ C * m := by
  refine ⟨2 ^ (130 * (2 ^ 16 + 1)), ?_⟩
  intro m
  by_cases hm : m = 0
  · rw [hm]
    have htau0 : tau 0 = 0 := by simp [tau]
    rw [htau0]
    exact Nat.zero_le _
  · have hcard : #m.divisors = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := Nat.card_divisors hm
    have htau : tau m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by simpa [tau] using hcard
    rw [htau, ← Finset.prod_pow m.primeFactors 16 (fun p => m.factorization p + 1)]
    let small : Finset ℕ := m.primeFactors.filter (fun p => p ≤ 2 ^ 16)
    let large : Finset ℕ := m.primeFactors.filter (fun p => ¬ p ≤ 2 ^ 16)
    have hsplit : (∏ p ∈ m.primeFactors, (m.factorization p + 1)^16) =
        (∏ p ∈ small, (m.factorization p + 1)^16) * (∏ p ∈ large, (m.factorization p + 1)^16) := by
      dsimp [small, large]
      exact (Finset.prod_filter_mul_prod_filter_not m.primeFactors
        (fun p => p ≤ 2 ^ 16) (fun p => (m.factorization p + 1)^16)).symm
    rw [hsplit]
    have hsmall : (∏ p ∈ small, (m.factorization p + 1)^16) ≤
        ∏ p ∈ small, 2^130 * p^(m.factorization p) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hpf
      have hA : (m.factorization p + 1)^16 ≤ 2^(m.factorization p + 130) :=
        succ_pow_sixteen_le (m.factorization p)
      have hC : 2^(m.factorization p) ≤ p^(m.factorization p) :=
        pow_le_pow_left₀ (by positivity) hp2 _
      calc (m.factorization p + 1)^16 ≤ 2^(m.factorization p + 130) := hA
        _ = 2^130 * 2^(m.factorization p) := by rw [pow_add, mul_comm]
        _ ≤ 2^130 * p^(m.factorization p) := Nat.mul_le_mul_left _ hC
    have hlarge : (∏ p ∈ large, (m.factorization p + 1)^16) ≤
        ∏ p ∈ large, p^(m.factorization p) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hnot : ¬ p ≤ 2^16 := (Finset.mem_filter.mp hp).2
      have h1 : m.factorization p + 1 ≤ 2^(m.factorization p) := succ_le_two_pow _
      have h2 : (m.factorization p + 1)^16 ≤ (2^(m.factorization p))^16 :=
        pow_le_pow_left₀ (by positivity) h1 16
      have h4 : (2^(m.factorization p))^16 ≤ p^(m.factorization p) := by
        rw [show (2^(m.factorization p))^16 = (2^16)^(m.factorization p) by
          rw [← pow_mul, mul_comm, pow_mul]]
        exact pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℕ)^16)
          (Nat.le_of_lt (not_le.mp hnot)) _
      exact le_trans h2 h4
    have hprod : (∏ p ∈ small, 2^130 * p^(m.factorization p)) * (∏ p ∈ large, p^(m.factorization p))
        = 2^(130 * small.card) * m := by
      dsimp [small, large]
      calc (∏ p ∈ m.primeFactors.filter (fun p => p ≤ 2^16), 2^130 * p^(m.factorization p))
          * (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ 2^16), p^(m.factorization p))
        = (2^130) ^ (m.primeFactors.filter (fun p => p ≤ 2^16)).card *
            ((∏ p ∈ m.primeFactors.filter (fun p => p ≤ 2^16), p^(m.factorization p)) *
              (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ 2^16), p^(m.factorization p))) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            ac_rfl
        _ = 2^(130 * (m.primeFactors.filter (fun p => p ≤ 2^16)).card) *
            (∏ p ∈ m.primeFactors, p^(m.factorization p)) := by
            rw [← pow_mul]
            rw [Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p ≤ 2^16)
              (fun p => p^(m.factorization p))]
        _ = 2^(130 * small.card) * m := by
            rw [show (∏ p ∈ m.primeFactors, p^(m.factorization p)) = m by
              simpa [Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hm]
    have hcard_le : small.card ≤ 2^16 + 1 := by
      have hsub : small ⊆ Finset.range (2^16 + 1) := by
        intro p hp
        have hple : p ≤ 2^16 := (Finset.mem_filter.mp hp).2
        simp only [Finset.mem_range]
        omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
    calc (∏ p ∈ small, (m.factorization p + 1)^16) * (∏ p ∈ large, (m.factorization p + 1)^16)
        ≤ (∏ p ∈ small, 2^130 * p^(m.factorization p)) * (∏ p ∈ large, p^(m.factorization p)) :=
          mul_le_mul hsmall hlarge (Nat.zero_le _) (Nat.zero_le _)
      _ = 2^(130 * small.card) * m := hprod
      _ ≤ 2^(130 * (2^16 + 1)) * m := by
          apply Nat.mul_le_mul_right
          apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
          exact Nat.mul_le_mul_left 130 hcard_le

/-! #### A stronger instance `τ(m) ≤ C·m^{1/20}` (needed by Proposition 4.1)

The `ε = 1/16` instance above is insufficient for the `F(n,k) = O(n^{-3})` estimate in
`prop_exact_order` (which needs `τ ≤ n^{δ/3}` with `δ` close to `1/10`, i.e. an exponent
`< 1/18`). We repeat the identical argument with exponent `20`, threshold `30`, and the
same constant `130`. -/

set_option maxHeartbeats 800000 in
private lemma succ_pow_twenty_le_two_mul {a : ℕ} (ha : 30 ≤ a) : (a + 1)^20 ≤ 2 * a^20 := by
  have h31 : 30 * (a + 1) ≤ 31 * a := by omega
  have hpow : (30 * (a + 1))^20 ≤ (31 * a)^20 := pow_le_pow_left₀ (by positivity) h31 20
  have hle : 30^20 * (a + 1)^20 ≤ 31^20 * a^20 := by simpa [mul_pow] using hpow
  have hconst : 31^20 ≤ 2 * 30^20 := by norm_num
  have hle3 : 30^20 * (a + 1)^20 ≤ 30^20 * (2 * a^20) := by
    calc 30^20 * (a + 1)^20 ≤ 31^20 * a^20 := hle
      _ ≤ (2 * 30^20) * a^20 := Nat.mul_le_mul_right (a^20) hconst
      _ = 30^20 * (2 * a^20) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hle3 (by positivity : 0 < 30^20)

set_option maxHeartbeats 800000 in
private lemma succ_pow_twenty_le (a : ℕ) : (a + 1)^20 ≤ 2^(a + 130) := by
  refine Nat.strong_induction_on a ?_
  intro a ih
  by_cases ha : a < 30
  · have h1 : (a + 1)^20 ≤ 30^20 := pow_le_pow_left₀ (by positivity) (by omega : a + 1 ≤ 30) 20
    have h2 : 30^20 ≤ 2^100 := by norm_num
    have h3 : 2^100 ≤ 2^(a + 130) := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (by omega)
    linarith
  · have ih' : a^20 ≤ 2^(a + 129) := by
      have h := ih (a - 1) (Nat.sub_lt (by omega : 0 < a) (by norm_num : 0 < 1))
      have h1 : a - 1 + 1 = a := by omega
      have h2 : a - 1 + 130 = a + 129 := by omega
      simpa [h1, h2] using h
    have hstep : (a + 1)^20 ≤ 2 * a^20 := succ_pow_twenty_le_two_mul (by omega)
    calc (a + 1)^20 ≤ 2 * a^20 := hstep
      _ ≤ 2 * 2^(a + 129) := Nat.mul_le_mul_left 2 ih'
      _ = 2^(a + 130) := by rw [mul_comm, ← pow_succ]

/-- **(stronger instance)** `τ(m) ≤ C·m^{1/20}`: there is an absolute constant `C` with
`τ(m)^20 ≤ C·m` for every `m`. This is the `ε = 1/20` instance of `τ(m) = m^{o(1)}`, sharp
enough for Proposition 4.1's `F(n,k) = O(n^{-3})` (which needs `ε < 1/18`). -/
theorem tau_pow_twenty_le : ∃ C : ℕ, ∀ m : ℕ, (tau m)^20 ≤ C * m := by
  refine ⟨(2 ^ 130) ^ (2 ^ 20 + 1), ?_⟩
  intro m
  by_cases hm : m = 0
  · rw [hm]
    have htau0 : tau 0 = 0 := by simp [tau]
    rw [htau0]
    exact Nat.zero_le _
  · have hcard : #m.divisors = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := Nat.card_divisors hm
    have htau : tau m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by simpa [tau] using hcard
    rw [htau, ← Finset.prod_pow m.primeFactors 20 (fun p => m.factorization p + 1)]
    let small : Finset ℕ := m.primeFactors.filter (fun p => p ≤ 2 ^ 20)
    let large : Finset ℕ := m.primeFactors.filter (fun p => ¬ p ≤ 2 ^ 20)
    have hsplit : (∏ p ∈ m.primeFactors, (m.factorization p + 1)^20) =
        (∏ p ∈ small, (m.factorization p + 1)^20) * (∏ p ∈ large, (m.factorization p + 1)^20) := by
      dsimp [small, large]
      exact (Finset.prod_filter_mul_prod_filter_not m.primeFactors
        (fun p => p ≤ 2 ^ 20) (fun p => (m.factorization p + 1)^20)).symm
    rw [hsplit]
    have hsmall : (∏ p ∈ small, (m.factorization p + 1)^20) ≤
        ∏ p ∈ small, 2^130 * p^(m.factorization p) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hpf
      have hA : (m.factorization p + 1)^20 ≤ 2^(m.factorization p + 130) :=
        succ_pow_twenty_le (m.factorization p)
      have hC : 2^(m.factorization p) ≤ p^(m.factorization p) :=
        pow_le_pow_left₀ (by positivity) hp2 _
      calc (m.factorization p + 1)^20 ≤ 2^(m.factorization p + 130) := hA
        _ = 2^130 * 2^(m.factorization p) := by rw [pow_add, mul_comm]
        _ ≤ 2^130 * p^(m.factorization p) := Nat.mul_le_mul_left _ hC
    have hlarge : (∏ p ∈ large, (m.factorization p + 1)^20) ≤
        ∏ p ∈ large, p^(m.factorization p) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hnot : ¬ p ≤ 2^20 := (Finset.mem_filter.mp hp).2
      have h1 : m.factorization p + 1 ≤ 2^(m.factorization p) := succ_le_two_pow _
      have h2 : (m.factorization p + 1)^20 ≤ (2^(m.factorization p))^20 :=
        pow_le_pow_left₀ (by positivity) h1 20
      have h4 : (2^(m.factorization p))^20 ≤ p^(m.factorization p) := by
        rw [show (2^(m.factorization p))^20 = (2^20)^(m.factorization p) by
          rw [← pow_mul, mul_comm, pow_mul]]
        exact pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℕ)^20)
          (Nat.le_of_lt (not_le.mp hnot)) _
      exact le_trans h2 h4
    have hprod : (∏ p ∈ small, 2^130 * p^(m.factorization p)) * (∏ p ∈ large, p^(m.factorization p))
        = 2^(130 * small.card) * m := by
      dsimp [small, large]
      calc (∏ p ∈ m.primeFactors.filter (fun p => p ≤ 2^20), 2^130 * p^(m.factorization p))
          * (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ 2^20), p^(m.factorization p))
        = (2^130) ^ (m.primeFactors.filter (fun p => p ≤ 2^20)).card *
            ((∏ p ∈ m.primeFactors.filter (fun p => p ≤ 2^20), p^(m.factorization p)) *
              (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ 2^20), p^(m.factorization p))) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            ac_rfl
        _ = 2^(130 * (m.primeFactors.filter (fun p => p ≤ 2^20)).card) *
            (∏ p ∈ m.primeFactors, p^(m.factorization p)) := by
            rw [← pow_mul]
            rw [Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p ≤ 2^20)
              (fun p => p^(m.factorization p))]
        _ = 2^(130 * small.card) * m := by
            rw [show (∏ p ∈ m.primeFactors, p^(m.factorization p)) = m by
              simpa [Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hm]
    have hcard_le : small.card ≤ 2^20 + 1 := by
      have hsub : small ⊆ Finset.range (2^20 + 1) := by
        intro p hp
        have hple : p ≤ 2^20 := (Finset.mem_filter.mp hp).2
        simp only [Finset.mem_range]
        omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
    have hpow_le : 2 ^ (130 * small.card) ≤ (2 ^ 130) ^ (2 ^ 20 + 1) := by
      calc 2 ^ (130 * small.card) = (2 ^ 130) ^ small.card := by rw [pow_mul]
        _ ≤ (2 ^ 130) ^ (2 ^ 20 + 1) := by
              exact pow_le_pow_right₀ (Nat.one_le_pow 130 2 (by norm_num : (0 : ℕ) < 2)) hcard_le
    calc (∏ p ∈ small, (m.factorization p + 1)^20) * (∏ p ∈ large, (m.factorization p + 1)^20)
        ≤ (∏ p ∈ small, 2^130 * p^(m.factorization p)) * (∏ p ∈ large, p^(m.factorization p)) :=
          mul_le_mul hsmall hlarge (Nat.zero_le _) (Nat.zero_le _)
      _ = 2^(130 * small.card) * m := hprod
      _ ≤ (2^130)^(2^20 + 1) * m := Nat.mul_le_mul_right m hpow_le

private lemma succ_pow_twentyfour_le_two_mul {a : ℕ} (ha : 40 ≤ a) : (a + 1)^24 ≤ 2 * a^24 := by
  have h41 : 40 * (a + 1) ≤ 41 * a := by omega
  have hpow : (40 * (a + 1))^24 ≤ (41 * a)^24 := pow_le_pow_left₀ (by positivity) h41 24
  have hle : 40^24 * (a + 1)^24 ≤ 41^24 * a^24 := by simpa [mul_pow] using hpow
  have hconst : 41^24 ≤ 2 * 40^24 := by norm_num
  have hle3 : 40^24 * (a + 1)^24 ≤ 40^24 * (2 * a^24) := by
    calc 40^24 * (a + 1)^24 ≤ 41^24 * a^24 := hle
      _ ≤ (2 * 40^24) * a^24 := Nat.mul_le_mul_right (a^24) hconst
      _ = 40^24 * (2 * a^24) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hle3 (by positivity : 0 < 40^24)

set_option maxHeartbeats 800000 in
private lemma succ_pow_twentyfour_le (a : ℕ) : (a + 1)^24 ≤ 2^(a + 130) := by
  refine Nat.strong_induction_on a ?_
  intro a ih
  by_cases ha : a < 40
  · have h1 : (a + 1)^24 ≤ 40^24 := pow_le_pow_left₀ (by positivity) (by omega : a + 1 ≤ 40) 24
    have h2 : 40^24 ≤ 2^128 := by norm_num
    have h3 : 2^128 ≤ 2^(a + 130) := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) (by omega)
    linarith
  · have ih' : a^24 ≤ 2^(a + 129) := by
      have h := ih (a - 1) (Nat.sub_lt (by omega : 0 < a) (by norm_num : 0 < 1))
      have h1 : a - 1 + 1 = a := by omega
      have h2 : a - 1 + 130 = a + 129 := by omega
      simpa [h1, h2] using h
    have hstep : (a + 1)^24 ≤ 2 * a^24 := succ_pow_twentyfour_le_two_mul (by omega)
    calc (a + 1)^24 ≤ 2 * a^24 := hstep
      _ ≤ 2 * 2^(a + 129) := Nat.mul_le_mul_left 2 ih'
      _ = 2^(a + 130) := by rw [mul_comm, ← pow_succ]

/-- The absolute constant `(2^130)^(2^24+1)` used in the `τ^24` divisor bound.
Wrapped in a `def` so that tactics never attempt to reduce the huge exponent. -/
private def tau24Const : ℕ := (2 ^ 130) ^ (2 ^ 24 + 1)

/-- **(stronger instance)** `τ(m) ≤ C·m^{1/24}`: there is an absolute constant `C` with
`τ(m)^24 ≤ C·m` for every `m`. This is the `ε = 1/24` instance of `τ(m) = m^{o(1)}`, used
together with the tightened threshold `δ = 1/2^20` to reach the optimal error
`n^{-23/8 + 3/2^20}` in Proposition 4.1. -/
theorem tau_pow_twentyfour_le : ∃ C : ℕ, ∀ m : ℕ, (tau m)^24 ≤ C * m := by
  refine ⟨tau24Const, ?_⟩
  intro m
  by_cases hm : m = 0
  · rw [hm]
    have htau0 : tau 0 = 0 := by simp [tau]
    rw [htau0]
    exact Nat.zero_le _
  · have hcard : #m.divisors = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := Nat.card_divisors hm
    have htau : tau m = ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by simpa [tau] using hcard
    rw [htau, ← Finset.prod_pow m.primeFactors 24 (fun p => m.factorization p + 1)]
    let small : Finset ℕ := m.primeFactors.filter (fun p => p ≤ 2 ^ 24)
    let large : Finset ℕ := m.primeFactors.filter (fun p => ¬ p ≤ 2 ^ 24)
    have hsplit : (∏ p ∈ m.primeFactors, (m.factorization p + 1)^24) =
        (∏ p ∈ small, (m.factorization p + 1)^24) * (∏ p ∈ large, (m.factorization p + 1)^24) := by
      dsimp [small, large]
      exact (Finset.prod_filter_mul_prod_filter_not m.primeFactors
        (fun p => p ≤ 2 ^ 24) (fun p => (m.factorization p + 1)^24)).symm
    rw [hsplit]
    have hsmall : (∏ p ∈ small, (m.factorization p + 1)^24) ≤
        ∏ p ∈ small, 2^130 * p^(m.factorization p) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hpf
      have hA : (m.factorization p + 1)^24 ≤ 2^(m.factorization p + 130) :=
        succ_pow_twentyfour_le (m.factorization p)
      have hC : 2^(m.factorization p) ≤ p^(m.factorization p) :=
        pow_le_pow_left₀ (by positivity) hp2 _
      calc (m.factorization p + 1)^24 ≤ 2^(m.factorization p + 130) := hA
        _ = 2^130 * 2^(m.factorization p) := by rw [pow_add, mul_comm]
        _ ≤ 2^130 * p^(m.factorization p) := Nat.mul_le_mul_left _ hC
    have hlarge : (∏ p ∈ large, (m.factorization p + 1)^24) ≤
        ∏ p ∈ large, p^(m.factorization p) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) ?_
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hnot : ¬ p ≤ 2^24 := (Finset.mem_filter.mp hp).2
      have h1 : m.factorization p + 1 ≤ 2^(m.factorization p) := succ_le_two_pow _
      have h2 : (m.factorization p + 1)^24 ≤ (2^(m.factorization p))^24 :=
        pow_le_pow_left₀ (by positivity) h1 24
      have h4 : (2^(m.factorization p))^24 ≤ p^(m.factorization p) := by
        rw [show (2^(m.factorization p))^24 = (2^24)^(m.factorization p) by
          rw [← pow_mul, mul_comm, pow_mul]]
        exact pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℕ)^24)
          (Nat.le_of_lt (not_le.mp hnot)) _
      exact le_trans h2 h4
    have hprod : (∏ p ∈ small, 2^130 * p^(m.factorization p)) * (∏ p ∈ large, p^(m.factorization p))
        = 2^(130 * small.card) * m := by
      dsimp [small, large]
      calc (∏ p ∈ m.primeFactors.filter (fun p => p ≤ 2^24), 2^130 * p^(m.factorization p))
          * (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ 2^24), p^(m.factorization p))
        = (2^130) ^ (m.primeFactors.filter (fun p => p ≤ 2^24)).card *
            ((∏ p ∈ m.primeFactors.filter (fun p => p ≤ 2^24), p^(m.factorization p)) *
              (∏ p ∈ m.primeFactors.filter (fun p => ¬ p ≤ 2^24), p^(m.factorization p))) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
            ac_rfl
        _ = 2^(130 * (m.primeFactors.filter (fun p => p ≤ 2^24)).card) *
            (∏ p ∈ m.primeFactors, p^(m.factorization p)) := by
            rw [← pow_mul]
            rw [Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p ≤ 2^24)
              (fun p => p^(m.factorization p))]
        _ = 2^(130 * small.card) * m := by
            rw [show (∏ p ∈ m.primeFactors, p^(m.factorization p)) = m by
              simpa [Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hm]
    have hcard_le : small.card ≤ 2^24 + 1 := by
      have hsub : small ⊆ Finset.range (2^24 + 1) := by
        intro p hp
        have hple : p ≤ 2^24 := (Finset.mem_filter.mp hp).2
        simp only [Finset.mem_range]
        omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
    have hpow_le : 2 ^ (130 * small.card) ≤ (2 ^ 130) ^ (2 ^ 24 + 1) := by
      calc 2 ^ (130 * small.card) = (2 ^ 130) ^ small.card := by rw [pow_mul]
        _ ≤ (2 ^ 130) ^ (2 ^ 24 + 1) := by
              exact pow_le_pow_right₀ (Nat.one_le_pow 130 2 (by norm_num : (0 : ℕ) < 2)) hcard_le
    calc (∏ p ∈ small, (m.factorization p + 1)^24) * (∏ p ∈ large, (m.factorization p + 1)^24)
        ≤ (∏ p ∈ small, 2^130 * p^(m.factorization p)) * (∏ p ∈ large, p^(m.factorization p)) :=
          mul_le_mul hsmall hlarge (Nat.zero_le _) (Nat.zero_le _)
      _ = 2^(130 * small.card) * m := hprod
      _ ≤ (2^130)^(2^24 + 1) * m := Nat.mul_le_mul_right m hpow_le

/-- `exp 1 < 3`. -/
private lemma exp_one_lt_three : Real.exp 1 < 3 :=
  lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3)

/-- `1 < log 3`. -/
private lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact exp_one_lt_three

/-- `log t ≤ 2·√t` for `t ≥ 1`. -/
private lemma log_le_two_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hε : (0 : ℝ) < (1 / 2) := by norm_num
  have h := Real.log_le_rpow_div (x := t) (by linarith) hε
  rw [← Real.sqrt_eq_rpow] at h
  nlinarith [h]

/-- The log-inversion step: `(r+1)! ≤ n` and `100 ≤ r` force
`r ≤ 100·log n / log(log n)`. -/
private lemma log_div_loglog_le (r n : ℕ) (hr : 100 ≤ r) (h : (r + 1).factorial ≤ n) :
    (r : ℝ) ≤ 100 * Real.log n / Real.log (Real.log n) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hn3 : 3 ≤ n := le_trans (le_trans (by norm_num : 3 ≤ Nat.factorial 3)
    (Nat.factorial_le (by omega : 3 ≤ r + 1))) h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1 : (r : ℝ) * Real.log r - r ≤ Real.log n := by
    have hlr : (r : ℝ) * Real.log r - r ≤ Real.log ((r : ℕ).factorial) :=
      log_factorial_lower (by omega : 1 ≤ r)
    have hmono : ((r : ℕ).factorial : ℝ) ≤ ((r + 1).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_le (by omega : r ≤ r + 1))
    have hle : Real.log ((r : ℕ).factorial) ≤ Real.log ((r + 1).factorial) :=
      Real.log_le_log (by positivity : (0 : ℝ) < (r : ℕ).factorial) hmono
    have hfac : Real.log ((r + 1).factorial) ≤ Real.log n :=
      Real.log_le_log (by positivity : (0 : ℝ) < (r + 1).factorial) (by exact_mod_cast h)
    linarith
  have hlogr_gt2 : (2 : ℝ) < Real.log r := by
    have hlog100 : (2 : ℝ) < Real.log (100 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 100)]
      have hlt3 : Real.exp 1 < 3 := exp_one_lt_three
      calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
        _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
        _ < 3 * 3 := by nlinarith [hlt3, Real.exp_pos 1]
        _ < 100 := by norm_num
    exact lt_of_lt_of_le hlog100 (Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by exact_mod_cast hr : (100 : ℝ) ≤ (r : ℝ)))
  have hlogr_pos : (0 : ℝ) < Real.log r := by linarith
  have h3 : (r : ℝ) * Real.log r ≤ 2 * Real.log n := by
    have hle : (r : ℝ) * (Real.log r - 1) ≤ Real.log n := by linarith
    have hmul : (r : ℝ) * (Real.log r / 2) ≤ (r : ℝ) * (Real.log r - 1) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · positivity
    nlinarith [hmul, hle]
  have hll_pos : (0 : ℝ) < Real.log (Real.log n) := by
    have h1log : (1 : ℝ) < Real.log n := by
      have h3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      exact lt_of_lt_of_le log_three_gt_one (Real.log_le_log (by norm_num) h3R)
    exact Real.log_pos h1log
  have hlogn_nonneg : (0 : ℝ) ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlogn_pos : (0 : ℝ) < Real.log n := by
    have h1log : (1 : ℝ) < Real.log n := by
      have h3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      exact lt_of_lt_of_le log_three_gt_one (Real.log_le_log (by norm_num) h3R)
    linarith
  by_cases hcase : (1 / 2 : ℝ) * Real.log (Real.log n) ≤ Real.log r
  · have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) * Real.log (Real.log n) := by positivity
    have hmain : (r : ℝ) * ((1 / 2 : ℝ) * Real.log (Real.log n)) ≤ 2 * Real.log n := by
      calc (r : ℝ) * ((1 / 2 : ℝ) * Real.log (Real.log n))
          ≤ (r : ℝ) * Real.log r := mul_le_mul_of_nonneg_left hcase (by positivity)
        _ ≤ 2 * Real.log n := h3
    have hdiv : (r : ℝ) ≤ (2 * Real.log n) / ((1 / 2 : ℝ) * Real.log (Real.log n)) :=
      (le_div_iff₀ hhalf_pos).mpr hmain
    have hb : (2 * Real.log n) / ((1 / 2 : ℝ) * Real.log (Real.log n)) ≤
        100 * Real.log n / Real.log (Real.log n) := by
      have hrew : (2 * Real.log n) / ((1 / 2 : ℝ) * Real.log (Real.log n)) =
          4 * Real.log n / Real.log (Real.log n) := by field_simp; ring
      rw [hrew]
      rw [div_le_div_iff_of_pos_right hll_pos]
      nlinarith
    linarith
  · have hlt : Real.log r < (1 / 2 : ℝ) * Real.log (Real.log n) := lt_of_not_ge hcase
    have hrexp : (r : ℝ) = Real.exp (Real.log r) := (Real.exp_log hrpos).symm
    have hexp : Real.exp (Real.log r) < Real.exp ((1 / 2 : ℝ) * Real.log (Real.log n)) :=
      Real.exp_lt_exp.mpr hlt
    have hsqrt : Real.exp ((1 / 2 : ℝ) * Real.log (Real.log n)) =
        Real.sqrt (Real.log n) := by
      rw [← Real.exp_log (Real.sqrt_pos_of_pos hlogn_pos)]
      congr 1
      rw [Real.log_sqrt (by linarith : (0 : ℝ) ≤ Real.log n)]
      ring
    have hrlt : (r : ℝ) < Real.sqrt (Real.log n) := by
      rw [hrexp]; exact hsqrt ▸ hexp
    have hsqrtle : Real.sqrt (Real.log n) ≤ 2 * Real.log n / Real.log (Real.log n) := by
      have h1log : (1 : ℝ) ≤ Real.log n := by
        have h3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
        exact le_trans (le_of_lt log_three_gt_one) (Real.log_le_log (by norm_num) h3R)
      have hloglog_le : Real.log (Real.log n) ≤ 2 * Real.sqrt (Real.log n) :=
        log_le_two_sqrt h1log
      rw [le_div_iff₀ hll_pos]
      have hmul : Real.sqrt (Real.log n) * Real.log (Real.log n) ≤
          Real.sqrt (Real.log n) * (2 * Real.sqrt (Real.log n)) :=
        mul_le_mul_of_nonneg_left hloglog_le (Real.sqrt_nonneg _)
      have hsq : Real.sqrt (Real.log n) * Real.sqrt (Real.log n) = Real.log n :=
        Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ Real.log n)
      nlinarith [hmul, hsq]
    have hle2 : 2 * Real.log n / Real.log (Real.log n) ≤
        100 * Real.log n / Real.log (Real.log n) := by
      rw [div_le_div_iff_of_pos_right hll_pos]
      nlinarith
    linarith [hrlt, hsqrtle, hle2]

/-- **(MP-003)** `ω(m) ≤ C·log m / log log m` for `m ≥ 3`. (Paper §2; feeds the
`E₁` estimate in Proposition 3.1.) -/
theorem omega_le_log_div_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 3 ≤ m →
      (omega m : ℝ) ≤ C * Real.log m / Real.log (Real.log m) := by
  refine ⟨100, by norm_num, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hfac : (omega m + 1).factorial ≤ m := omega_factorial_le hm0
  by_cases hsmall : omega m < 100
  · have hr99 : (omega m : ℝ) ≤ 99 := by
      exact_mod_cast (Nat.le_of_lt_succ hsmall)
    have hll : (0 : ℝ) < Real.log (Real.log m) := by
      have h1log : (1 : ℝ) < Real.log m := by
        have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        exact lt_of_lt_of_le log_three_gt_one (Real.log_le_log (by norm_num) h3)
      exact Real.log_pos h1log
    have hloglog_le : Real.log (Real.log m) ≤ Real.log m :=
      Real.log_le_self (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m)))
    have hratio : (1 : ℝ) ≤ Real.log m / Real.log (Real.log m) := by
      rw [le_div_iff₀ hll]; simpa using hloglog_le
    have hb : (99 : ℝ) ≤ 100 * Real.log m / Real.log (Real.log m) := by
      calc (99 : ℝ) ≤ 100 * (Real.log m / Real.log (Real.log m)) := by nlinarith [hratio]
        _ = 100 * Real.log m / Real.log (Real.log m) := by rw [mul_div_assoc]
    linarith
  · exact log_div_loglog_le (omega m) m (by omega) hfac

/-! ### Gronwall bound `σ(m)/m ≤ C·log log m` (MP-004) -/

/-- `∑_{k=0}^{a} p^k ≤ p^a · p/(p-1)` in ℝ, for `p ≥ 2`. -/
private lemma geom_sum_le_pow_mul (p a : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Finset.range (a + 1), (p : ℝ) ^ k) ≤
      (p : ℝ) ^ a * ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (ne_of_gt (by omega : 1 < p))
  have hgeom := geom_sum_eq hp1 (a + 1)
  rw [hgeom]
  have hp1_pos : 0 < (p : ℝ) - 1 := by
    have h1lt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    linarith
  have hle : (p : ℝ) ^ (a + 1) - 1 ≤ (p : ℝ) ^ (a + 1) := by
    have hnonneg : 0 ≤ (p : ℝ) ^ (a + 1) := pow_nonneg (by exact_mod_cast (by omega : 0 ≤ p)) _
    linarith
  have hdiv : ((p : ℝ) ^ (a + 1) - 1) / ((p : ℝ) - 1) ≤
      (p : ℝ) ^ (a + 1) / ((p : ℝ) - 1) :=
    div_le_div_of_nonneg_right hle (le_of_lt hp1_pos)
  have hrew : (p : ℝ) ^ (a + 1) / ((p : ℝ) - 1) =
      (p : ℝ) ^ a * ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
    rw [show ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) by norm_num [Nat.cast_sub (by omega : 1 ≤ p)]]
    rw [pow_succ]
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt (by omega : 0 < p))]
  exact le_trans hdiv (le_of_eq hrew)

/-- `σ(n)/n ≤ ∏_{p|n} p/(p-1)` in ℝ, for `n ≠ 0` (the Euler product bound). -/
private lemma sigma_div_le_prod_p_div_sub_one (n : ℕ) (hn : n ≠ 0) :
    (sigma n : ℝ) / (n : ℝ) ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have hsum := Nat.sum_divisors hn
  have hcast : (sigma n : ℝ) =
      ∏ p ∈ n.primeFactors, (∑ k ∈ Finset.range (n.factorization p + 1), (p : ℝ) ^ k) := by
    rw [sigma_eq, hsum]
    norm_cast
  rw [hcast]
  have hle : (∏ p ∈ n.primeFactors, (∑ k ∈ Finset.range (n.factorization p + 1), (p : ℝ) ^ k)) ≤
      ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p) * ((p : ℝ) / ((p - 1 : ℕ) : ℝ))) := by
    refine Finset.prod_le_prod (fun p hp => by positivity) ?_
    intro p hp
    have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hp
    exact geom_sum_le_pow_mul p (n.factorization p) hp2
  have hprod : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p) * ((p : ℝ) / ((p - 1 : ℕ) : ℝ)))) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    have hfac : (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p)) = (n : ℝ) := by
      norm_cast
      simpa [Nat.support_factorization] using (Nat.prod_factorization_pow_eq_self hn)
    exact hfac
  rw [hprod] at hle
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  exact (div_le_iff₀ hn_pos).mpr (by simpa [mul_comm] using hle)

/-- `-log(1-x) ≤ x + 2x²` for `0 ≤ x ≤ 1/2`. -/
private lemma neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have h1x_pos : 0 < 1 - x := by linarith
  have h1 : -Real.log (1 - x) = Real.log (1 / (1 - x)) := by
    simpa [one_div] using (Real.log_inv (1 - x)).symm
  rw [h1]
  have hlog : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (one_div_pos.mpr h1x_pos)
  have hfrac : 1 / (1 - x) - 1 = x / (1 - x) := by
    field_simp [ne_of_gt h1x_pos]
    ring
  rw [hfrac] at hlog
  have hbound : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ h1x_pos]
    have hnonneg : 0 ≤ x ^ 2 * (1 - 2 * x) := mul_nonneg (sq_nonneg x) (by linarith)
    nlinarith
  linarith

/-- `∑_{k=2}^{n} 1/(k(k-1)) ≤ 1` in ℝ. -/
private lemma sum_inv_mul_pred_le_one (n : ℕ) :
    (∑ k ∈ Finset.Icc 2 n, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1))) ≤ 1 := by
  by_cases hn : 1 ≤ n
  · have heq : (∑ k ∈ Finset.Icc 2 n, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1))) =
        1 - (1 : ℝ) / (n : ℝ) := by
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ n hn ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
          rw [ih]
          have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
          have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
          norm_num [Nat.cast_add, Nat.cast_one] at *
          field_simp [hn0, hn1]
          ring
    rw [heq]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hle : 0 ≤ (1 : ℝ) / (n : ℝ) := le_of_lt (one_div_pos.mpr hnR)
    linarith
  · have h : Finset.Icc 2 n = ∅ := by
      ext k; simp [Finset.mem_Icc]; omega
    simp [h]

/-- `∑_{p|n} 1/p² ≤ 1` in ℝ. -/
private lemma sum_inv_sq_primes_le (n : ℕ) :
    (∑ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) ^ 2)) ≤ 1 := by
  have hterm : ∀ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) ^ 2) ≤ (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp2)
    have hsq : (p : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hdenom : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos hpR (by linarith [show (1 : ℝ) < (p : ℝ) by exact_mod_cast hp2])
    exact one_div_le_one_div_of_le hdenom hsq
  have hle : (∑ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) ^ 2)) ≤
      ∑ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
    Finset.sum_le_sum (fun p hp => hterm p hp)
  have hsub : n.primeFactors ⊆ Finset.Icc 2 n := by
    intro p hp
    have hpP : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
    exact Finset.mem_Icc.mpr ⟨hpP.two_le, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd⟩
  have hsubset : (∑ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∑ k ∈ Finset.Icc 2 n, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro k hk hnot
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hk2)
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith [show (1 : ℝ) < (k : ℝ) by exact_mod_cast hk2]
    exact le_of_lt (one_div_pos.mpr (mul_pos hkR hk1))
  exact le_trans (le_trans hle hsubset) (sum_inv_mul_pred_le_one n)

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

/-- `log(p/(p-1)) = -log(1 - 1/p)` for `p ≥ 2`. -/
private lemma log_p_div_pred_eq_neg_log_one_sub (p : ℕ) (hp : 2 ≤ p) :
    Real.log ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) = -Real.log (1 - 1 / (p : ℝ)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < p))
  have h1 : (p : ℝ) / ((p - 1 : ℕ) : ℝ) = 1 / (1 - 1 / (p : ℝ)) := by
    rw [show ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 by norm_num [Nat.cast_sub (by omega : 1 ≤ p)]]
    field_simp [hpR]
  rw [h1]
  simpa [one_div] using (Real.log_inv (1 - 1 / (p : ℝ)))

/-! ### Euler's bound `∑_{p≤x} 1/p ≤ log log x + B` (MP-005) -/

/-- The key divisibility behind Mertens' first theorem: for a prime `p ≤ x`,
`p^{⌊x/p⌋}` divides `x!` (Legendre's formula). -/
lemma pow_natDiv_dvd_factorial {x p : ℕ} (hp : p.Prime) (hpx : p ≤ x) :
    p ^ (x / p) ∣ Nat.factorial x := by
  have hpf : p ∈ (Nat.factorial x).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, Nat.dvd_factorial hp.pos hpx, Nat.factorial_ne_zero x⟩
  have hfac : p ^ ((Nat.factorial x).factorization p) ∣ Nat.factorial x := by
    have hdvd : p ^ ((Nat.factorial x).factorization p) ∣
        ∏ q ∈ (Nat.factorial x).primeFactors, q ^ ((Nat.factorial x).factorization q) :=
      Finset.dvd_prod_of_mem (fun q => q ^ ((Nat.factorial x).factorization q)) hpf
    have hprod : (∏ q ∈ (Nat.factorial x).primeFactors, q ^ ((Nat.factorial x).factorization q))
        = Nat.factorial x := by
      simpa [Nat.support_factorization] using
        (Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero x))
    rwa [hprod] at hdvd
  have hle : x / p ≤ (Nat.factorial x).factorization p := by
    have h := Nat.factorization_factorial hp (n := x) (b := p.log x + 1) (Nat.lt_succ_self _)
    rw [h]
    have hlog : 0 < p.log x := Nat.log_pos hp.one_lt hpx
    have hmem : 1 ∈ Finset.Ico 1 (p.log x + 1) := by
      rw [Finset.mem_Ico]
      exact ⟨by omega, by omega⟩
    simpa [pow_one] using (Finset.single_le_sum (s := Finset.Ico 1 (p.log x + 1))
      (f := fun i => x / p ^ i) (fun i _ => Nat.zero_le _) hmem)
  exact dvd_trans (Nat.pow_dvd_pow p hle) hfac

/-- `∏_{p≤x} p^{⌊x/p⌋}` divides `x!`. -/
lemma prod_pow_natDiv_dvd_factorial (x : ℕ) :
    (∏ p ∈ Nat.primesLE x, p ^ (x / p)) ∣ Nat.factorial x := by
  have h1 : (∏ p ∈ Nat.primesLE x, p ^ (x / p)) ∣
      ∏ p ∈ Nat.primesLE x, p ^ ((Nat.factorial x).factorization p) := by
    refine Finset.prod_dvd_prod_of_dvd (fun p => p ^ (x / p))
      (fun p => p ^ ((Nat.factorial x).factorization p)) ?_
    intro p hp
    have hpP : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hpx : p ≤ x := (Nat.mem_primesLE.mp hp).1
    have hle : x / p ≤ (Nat.factorial x).factorization p := by
      have h := Nat.factorization_factorial hpP (n := x) (b := p.log x + 1) (Nat.lt_succ_self _)
      rw [h]
      have hlog : 0 < p.log x := Nat.log_pos hpP.one_lt hpx
      have hmem : 1 ∈ Finset.Ico 1 (p.log x + 1) := by
        rw [Finset.mem_Ico]; exact ⟨by omega, by omega⟩
      simpa [pow_one] using (Finset.single_le_sum (s := Finset.Ico 1 (p.log x + 1))
        (f := fun i => x / p ^ i) (fun i _ => Nat.zero_le _) hmem)
    exact Nat.pow_dvd_pow p hle
  have h2 : (∏ p ∈ Nat.primesLE x, p ^ ((Nat.factorial x).factorization p)) ∣ Nat.factorial x := by
    have hsub : Nat.primesLE x ⊆ (Nat.factorial x).primeFactors := by
      intro p hp
      have hpP : p.Prime := (Nat.mem_primesLE.mp hp).2
      have hpx : p ≤ x := (Nat.mem_primesLE.mp hp).1
      rw [Nat.mem_primeFactors]
      exact ⟨hpP, Nat.dvd_factorial hpP.pos hpx, Nat.factorial_ne_zero x⟩
    have hprod : (∏ p ∈ (Nat.factorial x).primeFactors, p ^ ((Nat.factorial x).factorization p))
        = Nat.factorial x := by
      simpa [Nat.support_factorization] using
        (Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero x))
    have hdvd : (∏ p ∈ Nat.primesLE x, p ^ ((Nat.factorial x).factorization p)) ∣
        ∏ p ∈ (Nat.factorial x).primeFactors, p ^ ((Nat.factorial x).factorization p) :=
      Finset.prod_dvd_prod_of_subset (Nat.primesLE x) ((Nat.factorial x).primeFactors)
        (fun p => p ^ ((Nat.factorial x).factorization p)) hsub
    rwa [hprod] at hdvd
  exact dvd_trans h1 h2

/-- `(x : ℝ) / (p : ℝ) ≤ (x / p : ℕ) + 1` for `0 < p`. -/
lemma cast_div_le_add_one {x p : ℕ} (hp : 0 < p) :
    (x : ℝ) / (p : ℝ) ≤ ((x / p : ℕ) : ℝ) + 1 := by
  have hlt_nat : x < (x / p + 1) * p := by
    have h3 : x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
    have h1 : p * (x / p) + x % p < p * (x / p) + p :=
      Nat.add_lt_add_left (Nat.mod_lt x hp) _
    have h2 : p * (x / p) + p = (x / p + 1) * p := by
      rw [Nat.mul_comm, Nat.add_mul, Nat.one_mul]
    calc x = p * (x / p) + x % p := h3
      _ < p * (x / p) + p := h1
      _ = (x / p + 1) * p := h2
  have hlt : (x : ℝ) < (((x / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
    exact_mod_cast hlt_nat
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  exact (div_le_iff₀ hpR).mpr (le_of_lt hlt)

/-- The product of `p^(x/p)` over primes `p ≤ x`, as a real, is at most `(x!) : ℝ`. -/
lemma real_prod_pow_natDiv_le_factorial (x : ℕ) :
    (∏ p ∈ Nat.primesLE x, (p : ℝ) ^ (x / p)) ≤ (Nat.factorial x : ℝ) := by
  have hdvd : (∏ p ∈ Nat.primesLE x, p ^ (x / p)) ∣ Nat.factorial x :=
    prod_pow_natDiv_dvd_factorial x
  have hle : (∏ p ∈ Nat.primesLE x, p ^ (x / p)) ≤ Nat.factorial x :=
    Nat.le_of_dvd (Nat.factorial_pos x) hdvd
  calc (∏ p ∈ Nat.primesLE x, (p : ℝ) ^ (x / p))
      = ((∏ p ∈ Nat.primesLE x, p ^ (x / p) : ℕ) : ℝ) := by
          norm_cast
    _ ≤ (Nat.factorial x : ℝ) := by exact_mod_cast hle

/-- **Mertens' first theorem** (upper bound): for `x ≥ 2`,
`∑_{p ≤ x} (log p)/p ≤ log x + log 4`. -/
theorem sum_log_div_primes_le :
    ∀ x : ℕ, 2 ≤ x →
      ∑ p ∈ Nat.primesLE x, (Real.log (p : ℝ)) / (p : ℝ) ≤
        Real.log (x : ℝ) + Real.log 4 := by
  intro x hx
  have hxR_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  -- (1) product bound and take logs
  have hprod : (∏ p ∈ Nat.primesLE x, (p : ℝ) ^ (x / p)) ≤ (Nat.factorial x : ℝ) :=
    real_prod_pow_natDiv_le_factorial x
  have hlog : Real.log (∏ p ∈ Nat.primesLE x, (p : ℝ) ^ (x / p)) ≤
      Real.log (Nat.factorial x : ℝ) := by
    apply Real.log_le_log
    · exact Finset.prod_pos (fun p hp =>
        pow_pos (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos) _)
    · exact hprod
  -- (2) log of the product = sum over primes of (x/p) * log p
  have hlogsum : Real.log (∏ p ∈ Nat.primesLE x, (p : ℝ) ^ (x / p)) =
      ∑ p ∈ Nat.primesLE x, ((x / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Real.log_prod]
    · simp
    · intro p hp
      exact pow_ne_zero _ (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos.ne')
  -- (3) log(x!) ≤ x log x
  have hfac : Real.log (Nat.factorial x : ℝ) ≤ Real.log ((x : ℝ) ^ x) := by
    apply Real.log_le_log
    · exact_mod_cast (Nat.factorial_pos x)
    · exact_mod_cast (Nat.factorial_le_pow x)
  have hfac2 : Real.log ((x : ℝ) ^ x) = (x : ℝ) * Real.log (x : ℝ) := by
    rw [Real.log_pow]
  -- (4) combine: sum (x/p)*log p ≤ x log x
  have hmain : ∑ p ∈ Nat.primesLE x, ((x / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤
      (x : ℝ) * Real.log (x : ℝ) := by
    calc ∑ p ∈ Nat.primesLE x, ((x / p : ℕ) : ℝ) * Real.log (p : ℝ)
        = Real.log (∏ p ∈ Nat.primesLE x, (p : ℝ) ^ (x / p)) := hlogsum.symm
      _ ≤ Real.log (Nat.factorial x : ℝ) := hlog
      _ ≤ Real.log ((x : ℝ) ^ x) := hfac
      _ = (x : ℝ) * Real.log (x : ℝ) := hfac2
  -- (5) lower bound each (x/p) by (x/p - 1) in ℝ
  have hlb : ∑ p ∈ Nat.primesLE x, ((x : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤
      ∑ p ∈ Nat.primesLE x, ((x / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpPrime : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp_pos : 0 < p := hpPrime.pos
    have hd : (x : ℝ) / (p : ℝ) - 1 ≤ ((x / p : ℕ) : ℝ) := by
      have h := cast_div_le_add_one (x := x) hp_pos
      linarith
    have hlog_nonneg : 0 ≤ Real.log (p : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (Nat.le_trans (by norm_num : 1 ≤ 2) hpPrime.two_le))
    exact mul_le_mul_of_nonneg_right hd hlog_nonneg
  -- (6) combine (4) and (5)
  have hle : ∑ p ∈ Nat.primesLE x, ((x : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤
      (x : ℝ) * Real.log (x : ℝ) := le_trans hlb hmain
  -- (7) expand LHS: sum (x/p - 1)*log p = x * sum(log p / p) - theta(x)
  have hexpand : ∑ p ∈ Nat.primesLE x, ((x : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) =
      (x : ℝ) * (∑ p ∈ Nat.primesLE x, Real.log (p : ℝ) / (p : ℝ)) -
        Chebyshev.theta (x : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log x]
    calc ∑ p ∈ Nat.primesLE x, ((x : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ)
        = ∑ p ∈ Nat.primesLE x, (((x : ℝ) / (p : ℝ)) * Real.log (p : ℝ) - Real.log (p : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            ring
      _ = (∑ p ∈ Nat.primesLE x, ((x : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) -
            (∑ p ∈ Nat.primesLE x, Real.log (p : ℝ)) := by
            rw [Finset.sum_sub_distrib]
      _ = (x : ℝ) * (∑ p ∈ Nat.primesLE x, Real.log (p : ℝ) / (p : ℝ)) -
            (∑ p ∈ Nat.primesLE x, Real.log (p : ℝ)) := by
            congr 1
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro p hp
              ring
  -- (8) Chebyshev upper bound on theta
  have htheta : Chebyshev.theta (x : ℝ) ≤ Real.log 4 * (x : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (by exact_mod_cast (by omega : 0 ≤ x))
  -- (9) final arithmetic
  have hfin : (x : ℝ) * (∑ p ∈ Nat.primesLE x, Real.log (p : ℝ) / (p : ℝ)) ≤
      (x : ℝ) * (Real.log (x : ℝ) + Real.log 4) := by
    have hsub : (x : ℝ) * (∑ p ∈ Nat.primesLE x, Real.log (p : ℝ) / (p : ℝ)) -
        Chebyshev.theta (x : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) := by
      rwa [hexpand] at hle
    nlinarith [hsub, htheta]
  -- (10) divide by x
  exact le_of_mul_le_mul_left hfin hxR_pos

/-! ### Abel summation step (Mertens' second theorem upper bound) -/

/-- The weighted prime indicator `a n = (log n)/n` if `n` is prime, else `0`. -/
noncomputable def a (n : ℕ) : ℝ := if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0

/-- `∑_{n ≤ x} a n = ∑_{p ≤ x} (log p)/p`. -/
lemma sum_a_eq_sum_primes (x : ℕ) :
    (∑ n ∈ Finset.Icc 0 x, a n) = ∑ p ∈ Nat.primesLE x, (Real.log (p : ℝ)) / (p : ℝ) := by
  unfold a
  rw [← Finset.sum_filter]
  rw [Nat.primesLE_eq_filter_Icc_zero x]

/-- Mertens' first theorem in terms of `a`: `∑_{n ≤ x} a n ≤ log x + log 4`. -/
lemma sum_a_le (x : ℕ) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 0 x, a n) ≤ Real.log (x : ℝ) + Real.log 4 := by
  rw [sum_a_eq_sum_primes]
  exact sum_log_div_primes_le x hx

/-- Telescoping: `∑_{i=a..b} (f(i+1) - f i) = f(b+1) - f a` for `a ≤ b`. -/
lemma sum_Icc_sub_telescope {f : ℕ → ℝ} (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, (f (i + 1) - f i)) = f (b + 1) - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega : a ≤ b + 1), ih]
      ring

/-- For `0 < x ≤ y`: `(y - x)/y ≤ log y - log x`. -/
lemma log_sub_div_le_log_sub {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  let t := (y - x) / x
  have hpos : 0 < 1 + t := by
    dsimp [t]
    have : 0 ≤ (y - x) / x := div_nonneg (sub_nonneg.mpr hxy) (le_of_lt hx)
    positivity
  have h' : 1 - (1 + t)⁻¹ ≤ Real.log (1 + t) := Real.one_sub_inv_le_log_of_pos hpos
  have hfrac : 1 - (1 + t)⁻¹ = t / (1 + t) := by
    field_simp [hpos.ne']
    ring
  have ht_y : t / (1 + t) = (y - x) / y := by
    dsimp [t]
    field_simp [hx.ne', hy.ne']
    ring
  have ht_log : Real.log (1 + t) = Real.log y - Real.log x := by
    dsimp [t]
    have h1 : 1 + (y - x) / x = y / x := by field_simp [hx.ne']; ring
    rw [h1, Real.log_div hy.ne' hx.ne']
  calc (y - x) / y = t / (1 + t) := ht_y.symm
    _ = 1 - (1 + t)⁻¹ := hfrac.symm
    _ ≤ Real.log (1 + t) := h'
    _ = Real.log y - Real.log x := ht_log

/-- `∑_{i=2}^{x-1} (log(i+1)-log i)/log(i+1) ≤ log(log x) - log(log 2)` for `x ≥ 3`. -/
lemma sum_log_sub_div_le (x : ℕ) (hx : 3 ≤ x) :
    (∑ i ∈ Finset.Icc 2 (x - 1),
        (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) := by
  have h : (∑ i ∈ Finset.Icc 2 (x - 1),
        (Real.log (Real.log ((i + 1 : ℕ) : ℝ)) - Real.log (Real.log (i : ℝ)))) =
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) := by
    simpa [show x - 1 + 1 = x by omega] using
      (sum_Icc_sub_telescope (f := fun k => Real.log (Real.log (k : ℝ))) 2 (x - 1) (by omega))
  rw [← h]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_ge2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
  have hlog_i_pos : (0 : ℝ) < Real.log (i : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < i))
  have hlog_le : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
      (by exact_mod_cast (by omega : i ≤ i + 1))
  exact log_sub_div_le_log_sub hlog_i_pos hlog_le

/-- `(1/a - 1/b) * a = (b - a) / b` for `a, b ≠ 0`. -/
lemma inv_sub_inv_mul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (1 / a - 1 / b) * a = (b - a) / b := by
  field_simp [ha, hb]

/-- `∑_{i=2}^{x} (1/log i) * a i = ∑_{p ≤ x} 1/p`. -/
lemma sum_a_mul_inv_log_eq_sum_inv_primes (x : ℕ) :
    (∑ i ∈ Finset.Ioc 1 x, (1 / Real.log (i : ℝ)) * a i) =
      ∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ) := by
  unfold a
  have hdist : (∑ i ∈ Finset.Ioc 1 x,
      (1 / Real.log (i : ℝ)) * (if i.Prime then Real.log (i : ℝ) / (i : ℝ) else 0)) =
      ∑ i ∈ Finset.Ioc 1 x,
        (if i.Prime then (1 / Real.log (i : ℝ)) * (Real.log (i : ℝ) / (i : ℝ)) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hiP : i.Prime <;> simp [hiP]
  rw [hdist]
  rw [← Finset.sum_filter]
  have h1 : (Finset.Ioc 1 x).filter Nat.Prime = Nat.primesLE x := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
    constructor
    · intro hn
      exact ⟨hn.1.2, hn.2⟩
    · intro hn
      exact ⟨⟨hn.2.one_lt, hn.1⟩, hn.2⟩
  rw [h1]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpP : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hlog_ne : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hpP.one_lt))
  have hpR_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpP.pos)
  field_simp [hlog_ne, hpR_ne]

/-- Abel's summation formula specialized: with `A_i = ∑_{k≤i} a k`,
`∑_{i=2}^{x} f_i a_i = f_x A_x + ∑_{i=2}^{x-1} (f_i - f_{i+1}) A_i` for `f_i = 1/log i`. -/
lemma abel_identity (x : ℕ) (hx : 2 ≤ x) :
    (∑ i ∈ Finset.Ioc 1 x, (1 / Real.log (i : ℝ)) * a i) =
      (1 / Real.log (x : ℝ)) * (∑ k ∈ Finset.Icc 0 x, a k) +
        ∑ i ∈ Finset.Ioc 1 (x - 1),
          (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) *
            (∑ k ∈ Finset.Icc 0 i, a k) := by
  have h := Finset.sum_Ioc_by_parts (m := 1) (n := x)
    (f := fun i => (1 : ℝ) / Real.log (i : ℝ)) (g := a) (by omega : 1 < x)
  have h' : (∑ i ∈ Finset.Ioc 1 x, (1 / Real.log (i : ℝ)) * a i) =
      (1 / Real.log (x : ℝ)) * (∑ k ∈ Finset.range (x + 1), a k) -
        (1 / Real.log (2 : ℝ)) * (∑ k ∈ Finset.range 2, a k) -
        ∑ i ∈ Finset.Ioc 1 (x - 1),
          (1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log (i : ℝ)) * (∑ k ∈ Finset.range (i + 1), a k) := by
    simpa [smul_eq_mul] using h
  rw [h']
  have hGx : Finset.range (x + 1) = Finset.Icc 0 x := by
    rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  have hG2 : (∑ k ∈ Finset.range 2, a k) = 0 := by
    norm_num [a, Finset.sum_range_succ, Nat.Prime]
  have hGi : ∀ i, Finset.range (i + 1) = Finset.Icc 0 i := by
    intro i; rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  rw [hGx, hG2]
  simp_rw [hGi]
  simp only [mul_zero, sub_zero]
  have hneg : - (∑ i ∈ Finset.Ioc 1 (x - 1),
        (1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log (i : ℝ)) * (∑ k ∈ Finset.Icc 0 i, a k)) =
      ∑ i ∈ Finset.Ioc 1 (x - 1),
        (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (∑ k ∈ Finset.Icc 0 i, a k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  nlinarith [hneg]

/-- `∑_{i=2}^{x-1} (1/log i - 1/log(i+1)) log i ≤ log(log x) - log(log 2)` for `x ≥ 2`. -/
lemma sum_inv_log_diff_mul_log_le (x : ℕ) (hx : 2 ≤ x) :
    (∑ i ∈ Finset.Ioc 1 (x - 1),
        (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ)) ≤
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) := by
  by_cases hx3 : 3 ≤ x
  · rw [show (Finset.Ioc 1 (x - 1)) = Finset.Icc 2 (x - 1) by
        ext n; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega]
    have hle : (∑ i ∈ Finset.Icc 2 (x - 1),
        (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ)) ≤
        ∑ i ∈ Finset.Icc 2 (x - 1),
          (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
      have heq : (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ) =
          (Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ)) / Real.log ((i + 1 : ℕ) : ℝ) :=
        inv_sub_inv_mul (Real.log (i : ℝ)) (Real.log ((i + 1 : ℕ) : ℝ))
          (ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < i))))
          (ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < i + 1))))
      rw [heq]
    exact le_trans hle (sum_log_sub_div_le x hx3)
  · have hx_eq : x = 2 := by omega
    subst x
    simp

/-- Telescoping: `∑_{i=2}^{x-1} (1/log i - 1/log(i+1)) = 1/log 2 - 1/log x` for `x ≥ 3`. -/
lemma sum_inv_log_diff_eq (x : ℕ) (hx : 3 ≤ x) :
    (∑ i ∈ Finset.Icc 2 (x - 1), (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ))) =
      1 / Real.log 2 - 1 / Real.log (x : ℝ) := by
  have h := sum_Icc_sub_telescope (f := fun i => (1 : ℝ) / Real.log (i : ℝ)) 2 (x - 1) (by omega : 2 ≤ x - 1)
  rw [show x - 1 + 1 = x by omega] at h
  calc (∑ i ∈ Finset.Icc 2 (x - 1), (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)))
      = - (∑ i ∈ Finset.Icc 2 (x - 1), (1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log (i : ℝ))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = - (1 / Real.log (x : ℝ) - 1 / Real.log 2) := by
          have h' : (∑ i ∈ Finset.Icc 2 (x - 1),
              (1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log (i : ℝ))) =
              1 / Real.log (x : ℝ) - 1 / Real.log 2 := by simpa using h
          rw [h']
    _ = 1 / Real.log 2 - 1 / Real.log (x : ℝ) := by ring

/-- The Euler constant `B` in the bound `∑_{p ≤ x} 1/p ≤ log log x + B`. -/
noncomputable def B_euler : ℝ := 1 + 2 * (Real.log 4 / Real.log 2) - Real.log (Real.log 2)

/-- The Euler constant is positive. -/
lemma B_euler_pos : 0 < B_euler := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have hlog2_lt_one : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : 0 < (2 : ℝ))]
    exact Real.exp_one_gt_two
  have hloglog2_neg : Real.log (Real.log 2) < 0 := Real.log_neg hlog2_pos hlog2_lt_one
  have hlog4_pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num : 1 < (4 : ℝ))
  have hratio_pos : (0 : ℝ) < Real.log 4 / Real.log 2 := div_pos hlog4_pos hlog2_pos
  have hmain : (0 : ℝ) < 1 + 2 * (Real.log 4 / Real.log 2) := by nlinarith
  dsimp [B_euler]
  linarith

/-- **Euler's bound**: `∑_{p ≤ x} 1/p ≤ log log x + B_euler` for `x ≥ 2`. -/
theorem sum_inv_primes_le (x : ℕ) (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE x, (1 : ℝ) / (p : ℝ) ≤ Real.log (Real.log x) + B_euler := by
  rw [← sum_a_mul_inv_log_eq_sum_inv_primes x]
  rw [abel_identity x hx]
  have hAx : (∑ k ∈ Finset.Icc 0 x, a k) ≤ Real.log (x : ℝ) + Real.log 4 := sum_a_le x hx
  have hlogx_pos : (0 : ℝ) < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hb1 : (1 / Real.log (x : ℝ)) * (∑ k ∈ Finset.Icc 0 x, a k) ≤
      (1 / Real.log (x : ℝ)) * (Real.log (x : ℝ) + Real.log 4) :=
    mul_le_mul_of_nonneg_left hAx (le_of_lt (one_div_pos.mpr hlogx_pos))
  have hb1' : (1 / Real.log (x : ℝ)) * (Real.log (x : ℝ) + Real.log 4) ≤ 1 + Real.log 4 / Real.log 2 := by
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hge : Real.log 2 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by exact_mod_cast hx)
    have hinv : (1 : ℝ) / Real.log (x : ℝ) ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2_pos hge
    have hlog4_nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num : 1 ≤ (4 : ℝ))
    have hle : Real.log 4 / Real.log (x : ℝ) ≤ Real.log 4 / Real.log 2 := by
      have hinv' : (Real.log (x : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ := by simpa [one_div] using hinv
      have hmul : Real.log 4 * (Real.log (x : ℝ))⁻¹ ≤ Real.log 4 * (Real.log 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv' hlog4_nonneg
      rwa [div_eq_mul_inv]
    calc (1 / Real.log (x : ℝ)) * (Real.log (x : ℝ) + Real.log 4)
        = 1 + Real.log 4 / Real.log (x : ℝ) := by field_simp [hlogx_pos.ne']
      _ ≤ 1 + Real.log 4 / Real.log 2 := by nlinarith
  have hb1main : (1 / Real.log (x : ℝ)) * (∑ k ∈ Finset.Icc 0 x, a k) ≤
      1 + Real.log 4 / Real.log 2 := le_trans hb1 hb1'
  have hR : (∑ i ∈ Finset.Ioc 1 (x - 1),
      (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (∑ k ∈ Finset.Icc 0 i, a k)) ≤
      (Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) + Real.log 4 / Real.log 2 := by
    by_cases hx3 : 3 ≤ x
    · have hAi : ∀ i ∈ Finset.Ioc 1 (x - 1), (∑ k ∈ Finset.Icc 0 i, a k) ≤ Real.log (i : ℝ) + Real.log 4 := by
        intro i hi
        have hi2 : 2 ≤ i := (Finset.mem_Ioc.mp hi).1
        exact sum_a_le i hi2
      have hdiff : ∀ i ∈ Finset.Ioc 1 (x - 1), 0 ≤ (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) := by
        intro i hi
        have hi2 : 2 ≤ i := (Finset.mem_Ioc.mp hi).1
        have hlog_i_pos : 0 < Real.log (i : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < i))
        have hlog_le : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < i)) (by exact_mod_cast (by omega : i ≤ i + 1))
        have hinv : 1 / Real.log ((i + 1 : ℕ) : ℝ) ≤ 1 / Real.log (i : ℝ) :=
          one_div_le_one_div_of_le hlog_i_pos hlog_le
        linarith
      have hterm : (∑ i ∈ Finset.Ioc 1 (x - 1),
          (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (∑ k ∈ Finset.Icc 0 i, a k)) ≤
          ∑ i ∈ Finset.Ioc 1 (x - 1),
            (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (Real.log (i : ℝ) + Real.log 4) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_left (hAi i hi) (hdiff i hi)
      have hsplit : (∑ i ∈ Finset.Ioc 1 (x - 1),
          (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (Real.log (i : ℝ) + Real.log 4)) =
          (∑ i ∈ Finset.Ioc 1 (x - 1),
            (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ)) +
            Real.log 4 * (∑ i ∈ Finset.Ioc 1 (x - 1),
              (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ))) := by
        calc (∑ i ∈ Finset.Ioc 1 (x - 1),
            (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (Real.log (i : ℝ) + Real.log 4))
            = ∑ i ∈ Finset.Ioc 1 (x - 1),
                ((1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ) +
                  (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log 4) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = (∑ i ∈ Finset.Ioc 1 (x - 1),
                (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ)) +
                (∑ i ∈ Finset.Ioc 1 (x - 1),
                  (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log 4) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ i ∈ Finset.Ioc 1 (x - 1),
                (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ)) +
                Real.log 4 * (∑ i ∈ Finset.Ioc 1 (x - 1),
                  (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ))) := by
                congr 1
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
      have hpart1 : (∑ i ∈ Finset.Ioc 1 (x - 1),
          (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * Real.log (i : ℝ)) ≤
          Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2) :=
        sum_inv_log_diff_mul_log_le x hx
      have hpart2 : Real.log 4 * (∑ i ∈ Finset.Ioc 1 (x - 1),
          (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ))) ≤ Real.log 4 / Real.log 2 := by
        have htel : (∑ i ∈ Finset.Ioc 1 (x - 1),
            (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ))) ≤ 1 / Real.log 2 := by
          rw [show (Finset.Ioc 1 (x - 1)) = Finset.Icc 2 (x - 1) by
            ext n; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega]
          rw [sum_inv_log_diff_eq x hx3]
          have hnonneg : 0 ≤ 1 / Real.log (x : ℝ) := le_of_lt (one_div_pos.mpr hlogx_pos)
          linarith
        have hlog4_nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num : 1 ≤ (4 : ℝ))
        calc Real.log 4 * (∑ i ∈ Finset.Ioc 1 (x - 1),
            (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)))
            ≤ Real.log 4 * (1 / Real.log 2) := mul_le_mul_of_nonneg_left htel hlog4_nonneg
          _ = Real.log 4 / Real.log 2 := by rw [mul_one_div]
      nlinarith [hterm, hsplit, hpart1, hpart2]
    · have hx_eq : x = 2 := by omega
      subst x
      have hlog4_nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num : 1 ≤ (4 : ℝ))
      have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
      have hpos : (0 : ℝ) ≤ Real.log 4 / Real.log 2 := div_nonneg hlog4_nonneg (le_of_lt hlog2_pos)
      simp [hpos]
  let c : ℝ := Real.log 4 / Real.log 2
  have hb1c : (1 / Real.log (x : ℝ)) * (∑ k ∈ Finset.Icc 0 x, a k) ≤ 1 + c := by
    simpa [c] using hb1main
  have hRc : (∑ i ∈ Finset.Ioc 1 (x - 1),
      (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (∑ k ∈ Finset.Icc 0 i, a k)) ≤
      (Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) + c := by
    simpa [c] using hR
  have hmain' : (1 / Real.log (x : ℝ)) * (∑ k ∈ Finset.Icc 0 x, a k) +
      (∑ i ∈ Finset.Ioc 1 (x - 1),
        (1 / Real.log (i : ℝ) - 1 / Real.log ((i + 1 : ℕ) : ℝ)) * (∑ k ∈ Finset.Icc 0 i, a k)) ≤
      Real.log (Real.log (x : ℝ)) + (1 + 2 * c - Real.log (Real.log 2)) := by
    nlinarith [hb1c, hRc]
  simpa [c, B_euler] using hmain'


/-- **Split sum**: `∑_{p|m} 1/p ≤ log log log m + C` for `m ≥ 8`.
Threshold `M = Nat.log 2 m`; small primes use Euler's bound (MP-005), large primes
use `ω(m) ≤ M` so their total is `≤ 1`. -/
private lemma sum_inv_primes_factors_le (m : ℕ) (hm : 8 ≤ m) :
    (∑ p ∈ m.primeFactors, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log (Real.log m)) + (B_euler + 2) := by
  let M : ℕ := Nat.log 2 m
  have hm0 : m ≠ 0 := by omega
  have hM2 : 2 ≤ M := by
    dsimp [M]
    have h4 : (2 : ℕ) ^ 2 ≤ m := by norm_num; omega
    exact (Nat.le_log_iff_pow_le (by norm_num : 1 < (2 : ℕ)) (by omega : m ≠ 0)).mpr h4
  have hMpos : 0 < M := by omega
  let small : Finset ℕ := m.primeFactors.filter (fun p => p ≤ M)
  let large : Finset ℕ := m.primeFactors.filter (fun p => ¬ p ≤ M)
  have hsplit : (∑ p ∈ m.primeFactors, (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ small, (1 : ℝ) / (p : ℝ)) + (∑ p ∈ large, (1 : ℝ) / (p : ℝ)) := by
    dsimp [small, large]
    simpa [add_comm] using (Finset.sum_filter_add_sum_filter_not (s := m.primeFactors)
      (p := fun p => p ≤ M) (f := fun p => (1 : ℝ) / (p : ℝ))).symm
  rw [hsplit]
  have hsmall : (∑ p ∈ small, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log M) + B_euler := by
    have hsub : small ⊆ Nat.primesLE M := by
      intro p hp
      have hpf : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
      have hple : p ≤ M := (Finset.mem_filter.mp hp).2
      have hpP : p.Prime := (Nat.mem_primeFactors.mp hpf).1
      exact Nat.mem_primesLE.mpr ⟨hple, hpP⟩
    have hsum_le : (∑ p ∈ small, (1 : ℝ) / (p : ℝ)) ≤ ∑ p ∈ Nat.primesLE M, (1 : ℝ) / (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hp hnot
      have hpP : p.Prime := (Nat.mem_primesLE.mp hp).2
      exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hpP.pos))
    exact le_trans hsum_le (sum_inv_primes_le M hM2)
  have hlarge : (∑ p ∈ large, (1 : ℝ) / (p : ℝ)) ≤ 1 := by
    have hMposR : 0 < (M : ℝ) := by exact_mod_cast hMpos
    have hterm : ∀ p ∈ large, (1 : ℝ) / (p : ℝ) ≤ (1 : ℝ) / (M : ℝ) := by
      intro p hp
      have hnot : ¬ p ≤ M := (Finset.mem_filter.mp hp).2
      have hpgt : M < p := Nat.lt_of_not_ge hnot
      have hMle : (M : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.le_of_lt hpgt)
      exact one_div_le_one_div_of_le hMposR hMle
    have hsum : (∑ p ∈ large, (1 : ℝ) / (p : ℝ)) ≤ (∑ p ∈ large, (1 : ℝ) / (M : ℝ)) :=
      Finset.sum_le_sum (fun p hp => hterm p hp)
    have hsum_eq : (∑ p ∈ large, (1 : ℝ) / (M : ℝ)) = (large.card : ℝ) * ((1 : ℝ) / (M : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : large.card ≤ M := by
      have hle : large.card ≤ omega m := by
        dsimp [large]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have homega : omega m ≤ M := by
        dsimp [M]
        exact omega_le_log_two hm0
      exact le_trans hle homega
    have hcardR : (large.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcard
    have hfin : (large.card : ℝ) * ((1 : ℝ) / (M : ℝ)) ≤ 1 := by
      have hle : (large.card : ℝ) * (1 / (M : ℝ)) ≤ (M : ℝ) * (1 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardR (le_of_lt (one_div_pos.mpr hMposR))
      have hM : (M : ℝ) * ((1 : ℝ) / (M : ℝ)) = 1 := by
        rw [one_div, mul_inv_cancel₀ (ne_of_gt hMposR)]
      rwa [hM] at hle
    exact le_trans (le_trans hsum (le_of_eq hsum_eq)) hfin
  have hlogM_le2 : Real.log M ≤ Real.log 2 + Real.log (Real.log m) := by
    have hpow : (2 : ℕ) ^ M ≤ m := by dsimp [M]; exact Nat.pow_log_le_self 2 hm0
    have hpowR : (2 : ℝ) ^ M ≤ (m : ℝ) := by exact_mod_cast hpow
    have hlogpow : Real.log ((2 : ℝ) ^ M) ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log
      · exact pow_pos (by norm_num : 0 < (2 : ℝ)) M
      · exact hpowR
    rw [Real.log_pow] at hlogpow
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hM_le : (M : ℝ) ≤ Real.log m / Real.log 2 := (le_div_iff₀ hlog2_pos).mpr hlogpow
    have hinv_le : 1 / Real.log 2 ≤ 2 := by
      have h : (1 : ℝ) / 2 < Real.log 2 := log_two_gt_one_half
      have hmul : 1 < 2 * Real.log 2 := by nlinarith
      have hlt : 1 / Real.log 2 < 2 := (div_lt_iff₀ hlog2_pos).mpr hmul
      exact le_of_lt hlt
    have hM_le2' : (M : ℝ) ≤ 2 * Real.log m := by
      calc (M : ℝ) ≤ Real.log m / Real.log 2 := hM_le
        _ = Real.log m * (1 / Real.log 2) := by rw [div_eq_mul_one_div]
        _ ≤ Real.log m * 2 := mul_le_mul_of_nonneg_left hinv_le (le_of_lt hlogm_pos)
        _ = 2 * Real.log m := by ring
    have hlogM_pos : 0 < (M : ℝ) := by exact_mod_cast hMpos
    have hlog2logm : Real.log (2 * Real.log m) = Real.log 2 + Real.log (Real.log m) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogm_pos)]
    exact hlog2logm ▸ (Real.log_le_log hlogM_pos hM_le2')
  have hloglogM_le : Real.log (Real.log M) ≤ Real.log (Real.log (Real.log m)) + 1 := by
    have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    have ht_pos : 0 < Real.log (Real.log m) := by
      have hlogm_gt1 : 1 < Real.log m := by
        have h8R : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hlog8_gt1 : 1 < Real.log 8 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num : 0 < (8 : ℝ))]
          exact lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 8)
        exact lt_of_lt_of_le hlog8_gt1 (Real.log_le_log (by norm_num : 0 < (8 : ℝ)) h8R)
      exact Real.log_pos hlogm_gt1
    have h1 : Real.log (Real.log M) ≤ Real.log (Real.log 2 + Real.log (Real.log m)) := by
      have hpos : 0 < Real.log 2 + Real.log (Real.log m) := by positivity
      exact Real.log_le_log hlogM_pos hlogM_le2
    have hlog2_le_t : Real.log 2 ≤ Real.log (Real.log m) := by
      have hlogm_ge2 : 2 ≤ Real.log m := by
        have h8R : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hlog8_ge2 : 2 ≤ Real.log 8 := by
          rw [Real.le_log_iff_exp_le (by norm_num : 0 < (8 : ℝ))]
          have he : Real.exp 1 < 2.72 := lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) ≤ 2.72)
          have hsq : Real.exp 1 * Real.exp 1 < (2.72 : ℝ) * 2.72 :=
            mul_lt_mul he he.le (Real.exp_pos 1) (by norm_num : 0 ≤ (2.72 : ℝ))
          have h272 : (2.72 : ℝ) * 2.72 < 8 := by norm_num
          have hexp2 : Real.exp 2 < 8 := by
            calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
              _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
              _ < (2.72 : ℝ) * 2.72 := hsq
              _ < 8 := h272
          exact le_of_lt hexp2
        exact le_trans hlog8_ge2 (Real.log_le_log (by norm_num : 0 < (8 : ℝ)) h8R)
      exact Real.log_le_log (by norm_num : 0 < (2 : ℝ)) hlogm_ge2
    have h2 : Real.log (Real.log 2 + Real.log (Real.log m)) ≤ Real.log (Real.log (Real.log m)) + 1 := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
      have hrew : Real.log 2 + Real.log (Real.log m) = Real.log (Real.log m) * (1 + Real.log 2 / Real.log (Real.log m)) := by
        field_simp [ne_of_gt ht_pos]
        ring
      rw [hrew]
      rw [Real.log_mul (ne_of_gt ht_pos) (ne_of_gt (by positivity : 0 < 1 + Real.log 2 / Real.log (Real.log m)))]
      have hlog : Real.log (1 + Real.log 2 / Real.log (Real.log m)) ≤ Real.log 2 / Real.log (Real.log m) := by
        have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + Real.log 2 / Real.log (Real.log m))
        linarith
      have hfrac : Real.log 2 / Real.log (Real.log m) ≤ 1 := by
        rw [div_le_iff₀ ht_pos]
        simpa using hlog2_le_t
      linarith
    exact le_trans h1 h2
  have hsmall_bound : (∑ p ∈ small, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log (Real.log m)) + (B_euler + 1) := by
    linarith [hsmall, hloglogM_le]
  linarith [hsmall_bound, hlarge]

/-- `σ(m)/m ≤ exp(B_euler + 4) · log log m` for `m ≥ 8`. -/
lemma sigma_div_le_loglog_of_large (m : ℕ) (hm : 8 ≤ m) :
    (sigma m : ℝ) / m ≤ Real.exp (B_euler + 4) * Real.log (Real.log m) := by
  let D : ℝ := B_euler + 2
  have hm0 : m ≠ 0 := by omega
  have hprod : (sigma m : ℝ) / (m : ℝ) ≤ ∏ p ∈ m.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
    sigma_div_le_prod_p_div_sub_one m hm0
  have h1mem : 1 ∈ m.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨Nat.one_dvd m, hm0⟩
  have hsig_ge1 : 1 ≤ sigma m := Finset.single_le_sum (s := m.divisors) (f := fun d => d)
    (fun d hd => Nat.zero_le d) h1mem
  have hsig_pos : 0 < (sigma m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hsig_ge1)
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hfrac_pos : 0 < (sigma m : ℝ) / (m : ℝ) := div_pos hsig_pos hm_pos
  have hlog : Real.log ((sigma m : ℝ) / (m : ℝ)) ≤
      Real.log (∏ p ∈ m.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ))) :=
    Real.log_le_log hfrac_pos hprod
  have hlogprod : Real.log (∏ p ∈ m.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ))) =
      ∑ p ∈ m.primeFactors, Real.log ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
    rw [Real.log_prod]
    intro p hp
    have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hp
    exact div_ne_zero (by exact_mod_cast (ne_of_gt (by omega : 0 < p)))
      (by exact_mod_cast (ne_of_gt (by omega : 0 < p - 1)))
  have hlogneg : Real.log (∏ p ∈ m.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ))) =
      ∑ p ∈ m.primeFactors, (-Real.log (1 - 1 / (p : ℝ))) := by
    rw [hlogprod]
    apply Finset.sum_congr rfl
    intro p hp
    exact log_p_div_pred_eq_neg_log_one_sub p (two_le_of_mem_primeFactors hp)
  have hterm : ∀ p ∈ m.primeFactors, -Real.log (1 - 1 / (p : ℝ)) ≤ (1 : ℝ) / (p : ℝ) + 2 * ((1 : ℝ) / (p : ℝ)) ^ 2 := by
    intro p hp
    have hp2 : 2 ≤ p := two_le_of_mem_primeFactors hp
    have hpR_pos : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hx0 : 0 ≤ 1 / (p : ℝ) := le_of_lt (one_div_pos.mpr hpR_pos)
    have hxhalf : 1 / (p : ℝ) ≤ (1 : ℝ) / 2 :=
      one_div_le_one_div_of_le (by norm_num : 0 < (2 : ℝ)) (by exact_mod_cast hp2)
    simpa [div_pow, one_div] using (neg_log_one_sub_le hx0 hxhalf)
  have hsum : ∑ p ∈ m.primeFactors, (-Real.log (1 - 1 / (p : ℝ))) ≤
      ∑ p ∈ m.primeFactors, ((1 : ℝ) / (p : ℝ) + 2 * ((1 : ℝ) / (p : ℝ)) ^ 2) :=
    Finset.sum_le_sum (fun p hp => hterm p hp)
  have hsplit : ∑ p ∈ m.primeFactors, ((1 : ℝ) / (p : ℝ) + 2 * ((1 : ℝ) / (p : ℝ)) ^ 2) =
      (∑ p ∈ m.primeFactors, (1 : ℝ) / (p : ℝ)) + 2 * (∑ p ∈ m.primeFactors, ((1 : ℝ) / (p : ℝ)) ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
  have hsq : (∑ p ∈ m.primeFactors, ((1 : ℝ) / (p : ℝ)) ^ 2) ≤ 1 := by
    simpa [div_pow] using (sum_inv_sq_primes_le m)
  have hinv : (∑ p ∈ m.primeFactors, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log (Real.log m)) + D := by
    simpa [D] using sum_inv_primes_factors_le m hm
  have hchain : Real.log ((sigma m : ℝ) / (m : ℝ)) ≤ Real.log (Real.log (Real.log m)) + (D + 2) := by
    calc Real.log ((sigma m : ℝ) / (m : ℝ))
        ≤ Real.log (∏ p ∈ m.primeFactors, ((p : ℝ) / ((p - 1 : ℕ) : ℝ))) := hlog
      _ = ∑ p ∈ m.primeFactors, (-Real.log (1 - 1 / (p : ℝ))) := hlogneg
      _ ≤ ∑ p ∈ m.primeFactors, ((1 : ℝ) / (p : ℝ) + 2 * ((1 : ℝ) / (p : ℝ)) ^ 2) := hsum
      _ = (∑ p ∈ m.primeFactors, (1 : ℝ) / (p : ℝ)) + 2 * (∑ p ∈ m.primeFactors, ((1 : ℝ) / (p : ℝ)) ^ 2) := hsplit
      _ ≤ (∑ p ∈ m.primeFactors, (1 : ℝ) / (p : ℝ)) + 2 := by nlinarith [hsq]
      _ ≤ Real.log (Real.log (Real.log m)) + D + 2 := by nlinarith [hinv]
      _ = Real.log (Real.log (Real.log m)) + (D + 2) := by ring
  have hloglogm_pos : 0 < Real.log (Real.log m) := by
    have hlogm_gt1 : 1 < Real.log m := by
      have h3 : 3 ≤ m := le_trans (by norm_num : 3 ≤ 8) hm
      have h3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
      have hlog3_gt1 : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : 0 < (3 : ℝ))]
        exact lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3)
      exact lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) h3R)
    exact Real.log_pos hlogm_gt1
  have hsig_exp : (sigma m : ℝ) / (m : ℝ) = Real.exp (Real.log ((sigma m : ℝ) / (m : ℝ))) :=
    (Real.exp_log hfrac_pos).symm
  rw [hsig_exp]
  have hexp : Real.exp (Real.log ((sigma m : ℝ) / (m : ℝ))) ≤
      Real.exp (Real.log (Real.log (Real.log m)) + (D + 2)) :=
    Real.exp_le_exp.mpr hchain
  have hrew : Real.exp (Real.log (Real.log (Real.log m)) + (D + 2)) =
      Real.exp (D + 2) * Real.log (Real.log m) := by
    rw [Real.exp_add]
    rw [Real.exp_log hloglogm_pos]
    ring
  rw [hrew] at hexp
  convert hexp using 1
  dsimp [D]
  ring_nf

/-- **(MP-004)** `σ(m)/m ≤ C·log log m` for `m ≥ 3`, with the explicit constant
`C = exp(B_euler + 4) + 8/log(log 3)`. (Paper §2, standard `σ(m)/m ≪ log log m`.) -/
theorem sigma_div_le_loglog (m : ℕ) (hm : 3 ≤ m) :
    (sigma m : ℝ) / m ≤
      (Real.exp (B_euler + 4) + 8 / Real.log (Real.log 3)) * Real.log (Real.log m) := by
  have hsigma_le_m : ∀ m : ℕ, 0 < m → (sigma m : ℝ) / (m : ℝ) ≤ (m : ℝ) + 1 := by
    intro m hm
    have hsig : sigma m ≤ (m + 1) * m := by
      have hd_le : ∑ d ∈ m.divisors, d ≤ ∑ d ∈ m.divisors, m := Finset.sum_le_sum (fun d hd =>
        Nat.le_of_dvd hm (Nat.mem_divisors.mp hd).1)
      have hcard : m.divisors.card ≤ m + 1 := by
        have hsub : m.divisors ⊆ Finset.range (m + 1) := by
          intro d hd
          have hdvd := (Nat.mem_divisors.mp hd).1
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hm hdvd))
        simpa using (Finset.card_le_card hsub)
      calc sigma m = ∑ d ∈ m.divisors, d := rfl
        _ ≤ ∑ d ∈ m.divisors, m := hd_le
        _ = m.divisors.card * m := by simp [Finset.sum_const]
        _ ≤ (m + 1) * m := Nat.mul_le_mul_right m hcard
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hsigR : (sigma m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (m : ℝ) := by exact_mod_cast hsig
    rw [div_le_iff₀ hmR]
    have h : (sigma m : ℝ) ≤ ((m : ℝ) + 1) * (m : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using hsigR
    simpa [mul_add] using h
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : 0 < (3 : ℝ))]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3)
  have hloglog3_pos : 0 < Real.log (Real.log 3) := Real.log_pos hlog3_gt1
  have hloglogm_nonneg : 0 ≤ Real.log (Real.log m) := by
    have hlogm_ge1 : 1 ≤ Real.log m := by
      have h3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      exact le_trans (le_of_lt hlog3_gt1) (Real.log_le_log (by norm_num : 0 < (3 : ℝ)) h3R)
    exact Real.log_nonneg hlogm_ge1
  by_cases h8 : 8 ≤ m
  · have h := sigma_div_le_loglog_of_large m h8
    have hle : Real.exp (B_euler + 4) * Real.log (Real.log m) ≤
        (Real.exp (B_euler + 4) + 8 / Real.log (Real.log 3)) * Real.log (Real.log m) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 8) hloglog3_pos))) hloglogm_nonneg
    exact le_trans h hle
  · have hmle7 : m ≤ 7 := by omega
    have hsig : (sigma m : ℝ) / (m : ℝ) ≤ (m : ℝ) + 1 := hsigma_le_m m (by omega : 0 < m)
    have hm8 : (m : ℝ) + 1 ≤ 8 := by
      have hm7 : (m : ℝ) ≤ 7 := by exact_mod_cast hmle7
      linarith
    have h1 : (sigma m : ℝ) / (m : ℝ) ≤ 8 := le_trans hsig hm8
    have hlog3_pos : 0 < Real.log 3 := lt_trans (by norm_num : (0 : ℝ) < 1) hlog3_gt1
    have hlog3m : Real.log 3 ≤ Real.log m := Real.log_le_log (by norm_num : 0 < (3 : ℝ)) (by exact_mod_cast hm)
    have hlogmono : Real.log (Real.log 3) ≤ Real.log (Real.log m) := Real.log_le_log hlog3_pos hlog3m
    have hloglog3_ne : Real.log (Real.log 3) ≠ 0 := ne_of_gt hloglog3_pos
    have hbase : (8 / Real.log (Real.log 3)) * Real.log (Real.log 3) = 8 := by
      field_simp [hloglog3_ne]
    have h2 : 8 ≤ (8 / Real.log (Real.log 3)) * Real.log (Real.log m) := by
      calc 8 = (8 / Real.log (Real.log 3)) * Real.log (Real.log 3) := hbase.symm
        _ ≤ (8 / Real.log (Real.log 3)) * Real.log (Real.log m) :=
            mul_le_mul_of_nonneg_left hlogmono (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 8) hloglog3_pos))
    have h3 : (8 / Real.log (Real.log 3)) * Real.log (Real.log m) ≤
        (Real.exp (B_euler + 4) + 8 / Real.log (Real.log 3)) * Real.log (Real.log m) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (le_of_lt (Real.exp_pos _))) hloglogm_nonneg
    linarith

/-- The Euler constant is at most `6`. -/
lemma B_euler_le_six : B_euler ≤ 6 := by
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hratio : Real.log 4 / Real.log 2 = 2 := by
    rw [hlog4_eq]
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : 1 < (2 : ℝ)))
    field_simp [hlog2_ne]
  dsimp [B_euler]
  rw [hratio]
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := log_two_gt_one_half
  have hinv : (1 : ℝ) / Real.exp 1 < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num : 0 < (2 : ℝ)) Real.exp_one_gt_two
  have hlog2_gt_inve : (1 : ℝ) / Real.exp 1 < Real.log 2 := lt_trans hinv hlog2_gt_half
  have hloglog2_gt : -1 < Real.log (Real.log 2) := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have h1e_pos : 0 < (1 : ℝ) / Real.exp 1 := one_div_pos.mpr (Real.exp_pos 1)
    have h := Real.log_lt_log h1e_pos hlog2_gt_inve
    have h1e_log : Real.log ((1 : ℝ) / Real.exp 1) = -1 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (Real.exp_pos 1).ne']
      rw [Real.log_one, Real.log_exp]
      norm_num
    rwa [h1e_log] at h
  nlinarith

/-- `exp(B_euler + 4) ≤ 60000`. -/
lemma exp_B_euler_add_four_le_60000 : Real.exp (B_euler + 4) ≤ 60000 := by
  have hle : B_euler + 4 ≤ 10 := by nlinarith [B_euler_le_six]
  have h1 : Real.exp (B_euler + 4) ≤ Real.exp 10 := Real.exp_le_exp.mpr hle
  have h10 : Real.exp (10 : ℝ) < 60000 := by
    have hpow10 : Real.exp (10 : ℝ) = (Real.exp 1) ^ 10 := by
      simpa using (Real.exp_nat_mul 1 10)
    rw [hpow10]
    have hlt : (Real.exp 1) ^ 10 < (3 : ℝ) ^ 10 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num : 10 ≠ 0)
    exact lt_trans hlt (by norm_num : (3 : ℝ) ^ 10 < 60000)
  exact le_trans h1 (le_of_lt h10)

end MostProbableOrder
