import MostProbableOrder.Perm.ErdosTuran
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Lemma 2.5: cycles and primes

For any `ℓ, m, n ∈ ℕ`,

    P(c(πₙ) = ℓ, m ∣ ord(πₙ)) ≤ ℓ^ω(m) / m,

where `ω(m)` is the number of distinct prime factors of `m`.

This is the paper's Lemma `lm:cycles_and_primes`, proved via the Feller coupling
(`fact:markov_chain`): the first Feller cycle length is uniform on `{1,…,n}`, so the
probability that it is divisible by a prime power `q` is at most `1/q`.  We implement
this by a cycle-removal recursion tracking which prime powers of `m` have already been
"covered" by an earlier cycle, and finish with a union bound over the `ℓ^{ω(m)}` ways to
assign each prime power to one of the `ℓ` cycles (encoded as a binomial sum).
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-! ### Prime-power factorization of `m` -/

/-- The prime power `p^{m.factorization p}`. -/
def ppow (m p : ℕ) : ℕ := p ^ m.factorization p

/-- An irreducible variant of  (used to avoid non-termination in ). -/
@[irreducible] def ppowIrr (m p : ℕ) : ℕ := p ^ m.factorization p

/--  equals . -/
@[simp] lemma ppowIrr_eq (m p : ℕ) : ppowIrr m p = ppow m p := by unfold ppowIrr; rfl

/-- Product of pairwise coprime integers divides `x` iff each factor divides `x`. -/
lemma prod_dvd_iff_of_pairwise_coprime {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℕ} {x : ℕ}
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime (f a) (f b)) :
    (∏ i ∈ s, f i) ∣ x ↔ ∀ i ∈ s, f i ∣ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert hd t hhd ih =>
      rw [Finset.prod_insert hhd]
      have hcop' : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → Nat.Coprime (f a) (f b) := by
        intro c hc d hd' hne
        exact hcop c (Finset.mem_insert_of_mem hc) d (Finset.mem_insert_of_mem hd') hne
      have hcopHd : Nat.Coprime (f hd) (∏ i ∈ t, f i) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hcop hd (Finset.mem_insert_self hd t) i (Finset.mem_insert_of_mem hi)
          (by intro h; subst i; exact hhd hi)
      have ih' := ih hcop'
      constructor
      · intro h i hi
        rw [Finset.mem_insert] at hi
        rcases hi with (hid | hi')
        · subst i
          exact dvd_trans (Nat.dvd_mul_right (f hd) (∏ j ∈ t, f j)) h
        · exact (ih').1 (dvd_trans (Nat.dvd_mul_left (∏ j ∈ t, f j) (f hd)) h) i hi'
      · intro h
        exact hcopHd.mul_dvd_of_dvd_of_dvd
          (h hd (Finset.mem_insert_self hd t))
          ((ih').2 (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The Fintype version of `prod_dvd_iff_of_pairwise_coprime`. -/
lemma prod_dvd_iff_of_pairwise_coprime_univ {ι : Type*} [Fintype ι] {f : ι → ℕ} {x : ℕ}
    (hcop : Pairwise (Function.onFun Nat.Coprime f)) :
    (∏ i : ι, f i) ∣ x ↔ ∀ i : ι, f i ∣ x := by
  classical
  simpa using (prod_dvd_iff_of_pairwise_coprime (s := (Finset.univ : Finset ι)) (f := f) (x := x)
    (by intro a ha b hb hne; exact hcop hne))

/-- `ppow m p` is a prime power when `p` is a prime factor of `m`. -/
lemma isPrimePow_ppow_of_mem_primeFactors {m p : ℕ} (hp : p ∈ m.primeFactors) :
    IsPrimePow (ppow m p) := by
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  have hm0 : m ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hpos : 0 < m.factorization p := by
    have hle : 1 ≤ m.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hprime hm0).mp (by simpa using hpd)
    omega
  rw [isPrimePow_nat_iff]
  exact ⟨p, m.factorization p, hprime, hpos, rfl⟩

/-- `m ∣ N` iff every prime power `p^{m.factorization p}` (for `p ∣ m`) divides `N`. -/
lemma dvd_iff_ppow_dvd_of_primeFactors {m N : ℕ} (hm : m ≠ 0) :
    m ∣ N ↔ ∀ p : m.primeFactors, ppow m p.1 ∣ N := by
  have hfac : m = ∏ p : m.primeFactors, ppow m p.1 := by
    simpa [ppow] using (Nat.prod_pow_primeFactors_factorization hm)
  conv_lhs => rw [hfac]
  exact prod_dvd_iff_of_pairwise_coprime_univ
    (f := fun p : m.primeFactors => ppow m p.1) Nat.pairwise_coprime_pow_primeFactors_factorization

/-- For a prime factor `p` of `m`, `p^{v_p(m)} | lcm d x ↔ p^{v_p(m)} | d ∨ p^{v_p(m)} | x`. -/
lemma ppow_dvd_lcm_iff {m d x : ℕ} (p : m.primeFactors) :
    ppow m p.1 ∣ d.lcm x ↔ ppow m p.1 ∣ d ∨ ppow m p.1 ∣ x :=
  dvd_lcm_iff_of_isPrimePow (isPrimePow_ppow_of_mem_primeFactors p.2)

/-- The product of the prime powers of `m` that divide `d` divides `d`. -/
lemma prod_filter_ppow_dvd (m d : ℕ) (S : Finset (m.primeFactors)) :
    (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) ∣ d := by
  rw [prod_dvd_iff_of_pairwise_coprime
    (s := S.filter (fun p => ppow m p.1 ∣ d)) (f := fun p => ppow m p.1) (x := d)]
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro a ha b hb hne
    exact Nat.pairwise_coprime_pow_primeFactors_factorization hne

/-- If `∏_{p∈S} p^{v_p(m)} | lcm d x`, then the "uncovered" part (prime powers not dividing `d`)
divides `x`. -/
lemma uncovered_dvd_of_dvd_lcm {m d x : ℕ} (S : Finset (m.primeFactors))
    (h : (∏ p ∈ S, ppow m p.1) ∣ d.lcm x) :
    (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1) ∣ x := by
  rw [prod_dvd_iff_of_pairwise_coprime
    (s := S.filter (fun p => ¬ ppow m p.1 ∣ d)) (f := fun p => ppow m p.1) (x := x)]
  · intro p hp
    have hpp : ppow m p.1 ∣ d.lcm x :=
      dvd_trans (Finset.dvd_prod_of_mem (f := fun q => ppow m q.1) (Finset.mem_filter.mp hp).1) h
    have hdvd := (ppow_dvd_lcm_iff p).1 hpp
    exact hdvd.resolve_left (Finset.mem_filter.mp hp).2
  · intro a ha b hb hne
    exact Nat.pairwise_coprime_pow_primeFactors_factorization hne

/-- **The full lcm divisibility criterion**:
`∏_{p∈S} p^{v_p(m)} | lcm d x` iff the uncovered prime powers (those not dividing `d`) divide `x`. -/
lemma dvd_lcm_iff_uncovered_dvd {m d x : ℕ} (S : Finset (m.primeFactors)) :
    (∏ p ∈ S, ppow m p.1) ∣ d.lcm x ↔
      (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1) ∣ x := by
  constructor
  · exact uncovered_dvd_of_dvd_lcm S
  · intro h
    have hpart : (∏ p ∈ S, ppow m p.1) =
        (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) *
          (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1) := by
      exact (Finset.prod_filter_mul_prod_filter_not S (fun p => ppow m p.1 ∣ d) (fun p => ppow m p.1)).symm
    rw [hpart]
    have hcov : (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) ∣ d := prod_filter_ppow_dvd m d S
    have hcov_lcm : (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) ∣ d.lcm x :=
      dvd_trans hcov (Nat.dvd_lcm_left d x)
    have huncov_lcm : (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1) ∣ d.lcm x :=
      dvd_trans h (Nat.dvd_lcm_right d x)
    have hcop : Nat.Coprime
        (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1)
        (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1) := by
      rw [Nat.coprime_prod_left_iff]
      intro a ha
      rw [Nat.coprime_prod_right_iff]
      intro b hb
      exact Nat.pairwise_coprime_pow_primeFactors_factorization (by
        intro h
        have ha' : ppow m a.1 ∣ d := (Finset.mem_filter.mp ha).2
        have hb' : ¬ ppow m b.1 ∣ d := (Finset.mem_filter.mp hb).2
        exact hb' (by simpa [h] using ha'))
    exact hcop.mul_dvd_of_dvd_of_dvd hcov_lcm huncov_lcm

/-! ### Basic bounds on the prime powers -/

/-- For a prime factor `p` of `m`, `ppow m p ≥ 2`. -/
lemma ppow_two_le {m p : ℕ} (hp : p ∈ m.primeFactors) : 2 ≤ ppow m p := by
  have hpr : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  have hm0 : m ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hpos : 0 < m.factorization p := by
    have hle : 1 ≤ m.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hpr hm0).mp (by simpa using hpd)
    omega
  exact hpr.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt hpos) p)

/-- `∏_{p∈S} p^{v_p(m)} ∣ 1` iff `S` is empty (each prime power is `≥ 2`). -/
lemma prod_ppow_dvd_one_iff_empty (m : ℕ) (S : Finset (m.primeFactors)) :
    (∏ p ∈ S, ppow m p.1) ∣ 1 ↔ S = ∅ := by
  constructor
  · intro h
    have hprod : (∏ p ∈ S, ppow m p.1) = 1 := by
      apply le_antisymm
      · exact Nat.le_of_dvd (by omega : 0 < 1) h
      · exact Finset.one_le_prod (fun p hp => le_trans (by norm_num : 1 ≤ 2) (ppow_two_le p.2))
    have hall : ∀ p ∈ S, ppow m p.1 = 1 := (Finset.prod_eq_one_iff.mp hprod)
    ext p
    constructor
    · intro hp
      have h1 : ppow m p.1 = 1 := hall p hp
      have h2 : 2 ≤ ppow m p.1 := ppow_two_le p.2
      omega
    · intro hp
      simp at hp
  · intro h; subst S; simp

/-- `S.filter (fun p => ¬ ppow m p.1 ∣ 1) = S` (no prime power divides `1`). -/
lemma filter_not_ppow_dvd_one (m : ℕ) (S : Finset (m.primeFactors)) :
    S.filter (fun p => ¬ ppow m p.1 ∣ 1) = S := by
  apply Finset.filter_true_of_mem
  intro p hp
  intro h
  have h2 : 2 ≤ ppow m p.1 := ppow_two_le p.2
  have hle : ppow m p.1 ≤ 1 := Nat.le_of_dvd (by omega : 0 < 1) h
  omega

/-! ### The cycle-removal recursion for the number of cycles and order divisibility -/

/-- The number of permutations of `n` letters with `ℓ` cycles whose order is divisible by
`∏_{p∈S} p^{v_p(m)}` (for `S ⊆ m.primeFactors`). -/
noncomputable def countCyclesOrderDiv (n ℓ : ℕ) (m : ℕ) (S : Finset (m.primeFactors)) : ℕ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter
    (fun σ => numCycles σ = ℓ ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ)).card

/-- The `n = 0` value of `countCyclesOrderDiv`. -/
lemma countCyclesOrderDiv_zero (ℓ m : ℕ) (S : Finset (m.primeFactors)) :
    countCyclesOrderDiv 0 ℓ m S = if ℓ = 0 ∧ S = ∅ then 1 else 0 := by
  classical
  unfold countCyclesOrderDiv
  have huniv : (Finset.univ : Finset (SymmetricGroup 0)) = ({1} : Finset (SymmetricGroup 0)) := by
    exact (Finset.eq_univ_of_card ({1} : Finset (SymmetricGroup 0)) (by rw [Finset.card_singleton, card_symmetricGroup 0]; norm_num)).symm
  rw [huniv, Finset.filter_singleton]
  have hnum : numCycles (1 : SymmetricGroup 0) = 0 := (numCycles_eq_zero_iff (1 : SymmetricGroup 0)).mpr (by simp)
  by_cases hP : numCycles (1 : SymmetricGroup 0) = ℓ ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf (1 : SymmetricGroup 0)
  · rw [if_pos hP, Finset.card_singleton]
    have hℓ : ℓ = 0 := by omega
    have hdvd : (∏ p ∈ S, ppow m p.1) ∣ 1 := by simpa using hP.2
    have hS : S = ∅ := (prod_ppow_dvd_one_iff_empty m S).1 hdvd
    rw [if_pos (by exact ⟨hℓ, hS⟩)]
  · rw [if_neg hP, Finset.card_empty]
    have hneg : ¬ (ℓ = 0 ∧ S = ∅) := by
      intro h
      exact hP ⟨by omega, by simpa using (prod_ppow_dvd_one_iff_empty m S).2 h.2⟩
    rw [if_neg hneg]

/-- The `n = 1` value of `countCyclesOrderDiv`. -/
lemma countCyclesOrderDiv_one (ℓ m : ℕ) (S : Finset (m.primeFactors)) :
    countCyclesOrderDiv 1 ℓ m S = if ℓ = 1 ∧ S = ∅ then 1 else 0 := by
  classical
  unfold countCyclesOrderDiv
  have huniv : (Finset.univ : Finset (SymmetricGroup 1)) = ({1} : Finset (SymmetricGroup 1)) := by
    exact (Finset.eq_univ_of_card ({1} : Finset (SymmetricGroup 1)) (by rw [Finset.card_singleton, card_symmetricGroup 1]; norm_num)).symm
  rw [huniv, Finset.filter_singleton]
  have hnum : numCycles (1 : SymmetricGroup 1) = 1 := by
    unfold numCycles; simp
  by_cases hP : numCycles (1 : SymmetricGroup 1) = ℓ ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf (1 : SymmetricGroup 1)
  · rw [if_pos hP, Finset.card_singleton]
    have hℓ : ℓ = 1 := by omega
    have hdvd : (∏ p ∈ S, ppow m p.1) ∣ 1 := by simpa using hP.2
    have hS : S = ∅ := (prod_ppow_dvd_one_iff_empty m S).1 hdvd
    rw [if_pos (by exact ⟨hℓ, hS⟩)]
  · rw [if_neg hP, Finset.card_empty]
    have hneg : ¬ (ℓ = 1 ∧ S = ∅) := by
      intro h
      exact hP ⟨by omega, by simpa using (prod_ppow_dvd_one_iff_empty m S).2 h.2⟩
    rw [if_neg hneg]

/-- **Cycle-removal fiber**: for `1 ≤ d ≤ n`, `#{σ | cycleLen σ = d ∧ numCycles σ = ℓ+1 ∧
∏_{p∈S} ppow | orderOf σ} = descFactorial(n-1)(d-1) · countCyclesOrderDiv (n-d) ℓ m (S.filter (¬ ppow | d))`. -/
lemma countCyclesOrderDiv_fiber (m d ℓ : ℕ) (S : Finset (m.primeFactors)) {n : ℕ} [NeZero n]
    (hd : 1 ≤ d) (hdl : d ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
      (fun σ => cycleLen σ = d ∧ numCycles σ = ℓ + 1 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ)).card =
      Nat.descFactorial (n - 1) (d - 1) * countCyclesOrderDiv (n - d) ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ d)) := by
  classical
  rw [← Fintype.card_subtype (fun σ : SymmetricGroup n =>
    cycleLen σ = d ∧ numCycles σ = ℓ + 1 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ)]
  by_cases hn1 : n = 1
  · subst n
    have hd1 : d = 1 := by omega
    subst d
    have hL : Fintype.card {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ numCycles σ = ℓ + 1 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ} =
        countCyclesOrderDiv 1 (ℓ + 1) m S := by
      unfold countCyclesOrderDiv
      rw [Fintype.card_subtype]
      congr 1
      ext σ
      constructor
      · intro hσ
        rw [Finset.mem_filter] at hσ
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ σ, hσ.2.2.1, hσ.2.2.2⟩
      · intro hσ
        rw [Finset.mem_filter] at hσ
        rw [Finset.mem_filter]
        have hcyc : cycleLen σ = 1 := by rw [cycleLen_eq_one_iff]; exact Subsingleton.elim _ _
        exact ⟨Finset.mem_univ σ, hcyc, hσ.2.1, hσ.2.2⟩
    rw [hL]
    rw [countCyclesOrderDiv_one (ℓ + 1) m S]
    rw [Nat.descFactorial_zero]
    rw [countCyclesOrderDiv_zero ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ 1))]
    rw [filter_not_ppow_dvd_one m S]
    rw [Nat.one_mul]
    norm_num
  · cases n with
    | zero => omega
    | succ n' =>
      cases d with
      | zero => omega
      | succ d' =>
        haveI : NeZero n' := ⟨by omega⟩
        let e := cycleRemovalEquiv (n := n') (k := d')
        let source := {σ : SymmetricGroup (n' + 1) // cycleLen σ = d' + 1 ∧ numCycles σ = ℓ + 1 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ}
        let target := (Fin d' ↪ Fin n') × {τ : SymmetricGroup (n' - d') //
          numCycles τ = ℓ ∧ (∏ p' ∈ S.filter (fun p => ¬ ppow m p.1 ∣ (d' + 1)), ppow m p'.1) ∣ orderOf τ}
        let e' : source ≃ target :=
          { toFun := fun ⟨σ, hcyc, hnc, hord⟩ => ((e ⟨σ, hcyc⟩).1, ⟨(e ⟨σ, hcyc⟩).2, by
              have hnum : numCycles σ = numCycles (residualFwd σ hcyc) + 1 := numCycles_residualFwd σ hcyc
              have hres : residualFwd σ hcyc = (e ⟨σ, hcyc⟩).2 := rfl
              have hord' : (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ (d' + 1)), ppow m p.1) ∣ orderOf (residualFwd σ hcyc) := by
                have hlcm : (∏ p ∈ S, ppow m p.1) ∣ (d' + 1).lcm (orderOf (residualFwd σ hcyc)) := by
                  rw [← orderOf_eq_lcm_cycleLen_residualFwd σ hcyc]
                  exact hord
                exact (dvd_lcm_iff_uncovered_dvd S).1 hlcm
              constructor
              · rw [← hres]; omega
              · rw [← hres]; exact hord'⟩)
            invFun := fun p => ⟨e.symm ⟨p.1, p.2.1⟩, (e.symm ⟨p.1, p.2.1⟩).2, by
              have hnum : numCycles (e.symm ⟨p.1, p.2.1⟩).1 = numCycles (residualFwd (e.symm ⟨p.1, p.2.1⟩).1 (e.symm ⟨p.1, p.2.1⟩).2) + 1 := numCycles_residualFwd (e.symm ⟨p.1, p.2.1⟩).1 (e.symm ⟨p.1, p.2.1⟩).2
              have hres : residualFwd (e.symm ⟨p.1, p.2.1⟩).1 (e.symm ⟨p.1, p.2.1⟩).2 = p.2.1 := congrArg Prod.snd (e.right_inv ⟨p.1, p.2.1⟩)
              rw [hnum, hres, p.2.2.1], by
              have hord' : (∏ p' ∈ S, ppow m p'.1) ∣ (d' + 1).lcm (orderOf p.2.1) := by
                exact (dvd_lcm_iff_uncovered_dvd S).2 p.2.2.2
              have hres : residualFwd (e.symm ⟨p.1, p.2.1⟩).1 (e.symm ⟨p.1, p.2.1⟩).2 = p.2.1 := congrArg Prod.snd (e.right_inv ⟨p.1, p.2.1⟩)
              rw [orderOf_eq_lcm_cycleLen_residualFwd (e.symm ⟨p.1, p.2.1⟩).1 (e.symm ⟨p.1, p.2.1⟩).2, hres]
              exact hord'⟩
            left_inv := by
              intro ⟨σ, hcyc, hnc, hord⟩
              apply Subtype.ext
              simpa using congrArg Subtype.val (e.left_inv ⟨σ, hcyc⟩)
            right_inv := by
              rintro ⟨p1, p2⟩
              apply Prod.ext
              · simpa using congrArg Prod.fst (e.right_inv ⟨p1, p2.1⟩)
              · apply Subtype.ext
                simpa using congrArg Prod.snd (e.right_inv ⟨p1, p2.1⟩) }
        rw [Fintype.card_congr e']
        rw [Fintype.card_prod, Fintype.card_embedding_eq]
        rw [Fintype.card_fin, Fintype.card_fin]
        unfold countCyclesOrderDiv
        rw [show (n' + 1) - 1 = n' by omega]
        rw [show (d' + 1) - 1 = d' by omega]
        rw [show (n' + 1) - (d' + 1) = n' - d' by omega]
        rw [Fintype.card_subtype]

/-- **Cycle-removal recursion** for `countCyclesOrderDiv`. -/
lemma countCyclesOrderDiv_rec (m ℓ n : ℕ) (S : Finset (m.primeFactors)) [NeZero n] :
    countCyclesOrderDiv n (ℓ + 1) m S =
      ∑ d ∈ Finset.Icc 1 n, Nat.descFactorial (n - 1) (d - 1) *
        countCyclesOrderDiv (n - d) ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ d)) := by
  classical
  unfold countCyclesOrderDiv
  let s := (Finset.univ : Finset (SymmetricGroup n)).filter
    (fun σ => numCycles σ = ℓ + 1 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ)
  have hpart := Finset.card_eq_sum_card_image (f := cycleLen) (s := s)
  have himg : s.image cycleLen ⊆ Finset.Icc 1 n := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨σ, hσ, rfl⟩
    exact Finset.mem_Icc.mpr ⟨cycleLen_pos σ, cycleLen_le σ⟩
  have hzero : ∀ d ∈ Finset.Icc 1 n, d ∉ s.image cycleLen →
      (s.filter (fun σ => cycleLen σ = d)).card = 0 := by
    intro d hd hnot
    apply Finset.card_eq_zero.mpr
    ext σ
    simp
    intro hσ hcd
    exact hnot (Finset.mem_image.mpr ⟨σ, hσ, hcd⟩)
  calc s.card
      = ∑ d ∈ s.image cycleLen, (s.filter (fun σ => cycleLen σ = d)).card := by
          simpa using hpart
    _ = ∑ d ∈ Finset.Icc 1 n, (s.filter (fun σ => cycleLen σ = d)).card := by
          rw [Finset.sum_subset himg hzero]
    _ = ∑ d ∈ Finset.Icc 1 n, Nat.descFactorial (n - 1) (d - 1) *
            countCyclesOrderDiv (n - d) ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ d)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdn : d ≤ n := (Finset.mem_Icc.mp hd).2
          have hfilt : (s.filter (fun σ => cycleLen σ = d)) =
              (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ =>
                cycleLen σ = d ∧ numCycles σ = ℓ + 1 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ) := by
            ext σ
            simp [s, Finset.mem_filter, and_comm, and_left_comm]
          rw [hfilt]
          rw [countCyclesOrderDiv_fiber m d ℓ S hd1 hdn]

/-! ### The union bound / subset partition -/

/-- `#\{d ∈ [1,N] : Q ∣ d\} = N/Q` for `Q ≥ 1`. -/
lemma card_filter_dvd_Icc (Q N : ℕ) (hQ : 1 ≤ Q) :
    ((Finset.Icc 1 N).filter (fun d => Q ∣ d)).card = N / Q := by
  classical
  have hcount : (Finset.range (N / Q)).card = N / Q := Finset.card_range (N / Q)
  have hbij : (Finset.range (N / Q)).card = ((Finset.Icc 1 N).filter (fun d => Q ∣ d)).card := by
    apply Finset.card_bij (fun j _ => (j + 1) * Q)
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos j) (by omega : 0 < Q))
      · have hj' : j < N / Q := Finset.mem_range.mp hj
        have hle : (j + 1) * Q ≤ (N / Q) * Q := Nat.mul_le_mul_right Q (Nat.succ_le_of_lt hj')
        exact hle.trans (Nat.div_mul_le_self N Q)
      · simpa [Nat.mul_comm] using (Nat.dvd_mul_right Q (j + 1))
    · intro a ha b hb hab
      have hc := Nat.mul_right_cancel (by omega : 0 < Q) (by simpa [Nat.mul_comm] using hab)
      omega
    · intro d hd
      rw [Finset.mem_filter] at hd
      rcases hd.2 with ⟨c, hc⟩
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd.1).1
      have hdN : d ≤ N := (Finset.mem_Icc.mp hd.1).2
      have hcpos : 0 < c := by
        by_cases hc0 : c = 0
        · subst c; simp at hc; omega
        · exact Nat.pos_of_ne_zero hc0
      refine ⟨c - 1, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hcN : c ≤ N / Q := by
          rw [Nat.le_div_iff_mul_le (by omega : 0 < Q)]
          exact (by simpa [Nat.mul_comm, hc] using hdN)
        omega
      · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hcpos)]
        simpa [Nat.mul_comm] using hc.symm
  rw [← hbij, hcount]

set_option maxHeartbeats 400000 in
/-- `∑_{C ⊆ S} ℓ^|C| = (ℓ+1)^|S|` (the binomial theorem for the subset count). -/
lemma sum_powerset_card_pow {α : Type*} [DecidableEq α] (S : Finset α) (ℓ : ℕ) :
    (∑ C ∈ S.powerset, ℓ ^ C.card) = (ℓ + 1) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      rw [powerset_insert]
      rw [Finset.sum_union]
      · rw [Finset.sum_image]
        · have hcard : ∀ C ∈ t.powerset, (insert a C).card = C.card + 1 := by
            intro C hC
            rw [Finset.card_insert_of_notMem]
            intro ha
            exact hat ((Finset.mem_powerset.mp hC) ha)
          rw [show (∑ C ∈ t.powerset, ℓ ^ (insert a C).card) = ℓ * (∑ C ∈ t.powerset, ℓ ^ C.card) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro C hC
            rw [hcard C hC, pow_succ, Nat.mul_comm]]
          rw [ih, Finset.card_insert_of_notMem hat]
          rw [show (ℓ + 1) ^ t.card + ℓ * (ℓ + 1) ^ t.card = (ℓ + 1) * (ℓ + 1) ^ t.card by ring]
          rw [pow_succ]
          rw [Nat.mul_comm]
        · intro x hx y hy hxy
          have hax : a ∉ x := by intro ha; exact hat ((Finset.mem_powerset.mp hx) ha)
          have hay : a ∉ y := by intro ha; exact hat ((Finset.mem_powerset.mp hy) ha)
          simpa [Finset.erase_insert hax, Finset.erase_insert hay] using (congrArg (fun C => C.erase a) hxy)
      · apply Finset.disjoint_left.mpr
        intro C hC1 hC2
        rw [Finset.mem_image] at hC2
        rcases hC2 with ⟨C', hC', hC2⟩
        have haC : a ∈ C := by rw [← hC2]; simp
        have haC' : a ∉ C := by
          intro ha
          exact hat ((Finset.mem_powerset.mp hC1) ha)
        exact haC' haC

set_option maxHeartbeats 1000000 in
/-- **The subset partition**: `∑_d (covered) · ℓ^(uncovered count) ≤ n · (ℓ+1)^|S|`. -/
lemma sum_covered_mul_pow_card_le (m n ℓ : ℕ) (S : Finset (m.primeFactors)) :
    (∑ d ∈ Finset.Icc 1 n,
      (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) *
        ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) ≤
      n * (ℓ + 1) ^ S.card := by
  classical
  have hfiberIrr : (∑ C ∈ S.powerset, ∑ d ∈ (Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppowIrr m p.1 ∣ d) = C),
        (∏ p ∈ S.filter (fun p => ppowIrr m p.1 ∣ d), ppowIrr m p.1) * ℓ ^ (S.filter (fun p => ¬ ppowIrr m p.1 ∣ d)).card) =
      ∑ d ∈ Finset.Icc 1 n, (∏ p ∈ S.filter (fun p => ppowIrr m p.1 ∣ d), ppowIrr m p.1) * ℓ ^ (S.filter (fun p => ¬ ppowIrr m p.1 ∣ d)).card := by
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 n) (t := S.powerset)
      (g := fun d => S.filter (fun p => ppowIrr m p.1 ∣ d))
      (f := fun d => (∏ p ∈ S.filter (fun p => ppowIrr m p.1 ∣ d), ppowIrr m p.1) * ℓ ^ (S.filter (fun p => ¬ ppowIrr m p.1 ∣ d)).card)
      (by intro d hd; exact Finset.mem_powerset.mpr (Finset.filter_subset (fun p => ppowIrr m p.1 ∣ d) S))
  have hfiber : (∑ C ∈ S.powerset, ∑ d ∈ (Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C),
        (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) =
      ∑ d ∈ Finset.Icc 1 n, (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card := by
    simpa [ppowIrr_eq] using hfiberIrr
  rw [← hfiber]
  calc (∑ C ∈ S.powerset, ∑ d ∈ (Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C),
        (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card)
      ≤ ∑ C ∈ S.powerset, (n / (∏ p ∈ C, ppow m p.1)) * (∏ p ∈ C, ppow m p.1) * ℓ ^ (S.card - C.card) := by
          apply Finset.sum_le_sum
          intro C hC
          calc (∑ d ∈ (Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C),
                (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card)
              = (∑ d ∈ (Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C),
                  (∏ p ∈ C, ppow m p.1) * ℓ ^ (S.card - C.card)) := by
                    apply Finset.sum_congr rfl
                    intro d hd
                    rw [Finset.mem_filter] at hd
                    have hCcard : (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card = S.card - C.card := by
                      have hsd : S.filter (fun p => ¬ ppow m p.1 ∣ d) = S \ C := by
                        rw [← hd.2]
                        ext p
                        simp only [Finset.mem_filter, Finset.mem_sdiff]
                        tauto
                      rw [hsd]
                      rw [Finset.card_sdiff]
                      rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hC)]
                    rw [hd.2, hCcard]
            _ = ((Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C)).card * ((∏ p ∈ C, ppow m p.1) * ℓ ^ (S.card - C.card)) := by
                    rw [Finset.sum_const]
                    simp
            _ ≤ ((n / (∏ p ∈ C, ppow m p.1)) * (∏ p ∈ C, ppow m p.1)) * ℓ ^ (S.card - C.card) := by
                    have hcard : ((Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C)).card ≤ n / (∏ p ∈ C, ppow m p.1) := by
                      have hsub : (Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C) ⊆ (Finset.Icc 1 n).filter (fun d => (∏ p ∈ C, ppow m p.1) ∣ d) := by
                        intro d hd
                        rw [Finset.mem_filter]
                        rw [Finset.mem_filter] at hd
                        refine ⟨hd.1, ?_⟩
                        rw [prod_dvd_iff_of_pairwise_coprime (s := C) (f := fun p => ppow m p.1) (x := d)]
                        · intro p hp
                          rw [← hd.2] at hp
                          exact (Finset.mem_filter.mp hp).2
                        · intro a ha b hb hne
                          exact Nat.pairwise_coprime_pow_primeFactors_factorization hne
                      exact le_trans (Finset.card_le_card hsub) (by
                        rw [card_filter_dvd_Icc (∏ p ∈ C, ppow m p.1) n (Finset.one_le_prod (fun p hp => le_trans (by norm_num : 1 ≤ 2) (ppow_two_le p.2)))])
                    calc ((Finset.Icc 1 n).filter (fun d => S.filter (fun p => ppow m p.1 ∣ d) = C)).card * ((∏ p ∈ C, ppow m p.1) * ℓ ^ (S.card - C.card))
                        ≤ (n / (∏ p ∈ C, ppow m p.1)) * ((∏ p ∈ C, ppow m p.1) * ℓ ^ (S.card - C.card)) := by
                            exact Nat.mul_le_mul_right _ hcard
                      _ = ((n / (∏ p ∈ C, ppow m p.1)) * (∏ p ∈ C, ppow m p.1)) * ℓ ^ (S.card - C.card) := by ring
    _ ≤ ∑ C ∈ S.powerset, n * ℓ ^ (S.card - C.card) := by
          apply Finset.sum_le_sum
          intro C hC
          exact Nat.mul_le_mul_right (ℓ ^ (S.card - C.card)) (by simpa [Nat.mul_comm] using Nat.mul_div_le n (∏ p ∈ C, ppow m p.1))
    _ = n * ∑ C ∈ S.powerset, ℓ ^ (S.card - C.card) := by
          rw [Finset.mul_sum]
    _ = n * ∑ C ∈ S.powerset, ℓ ^ C.card := by
          congr 1
          symm
          apply Finset.sum_bij (fun C hC => S \ C)
          · intro C hC
            exact Finset.mem_powerset.mpr (Finset.sdiff_subset (s := S) (t := C))
          · intro C hC D hD hCD
            have hCS : C ⊆ S := Finset.mem_powerset.mp hC
            have hDS : D ⊆ S := Finset.mem_powerset.mp hD
            have hC' : S \ (S \ C) = C := by
              ext p
              simp only [Finset.mem_sdiff]
              have hpc : p ∈ C → p ∈ S := fun hp => hCS hp
              tauto
            have hD' : S \ (S \ D) = D := by
              ext p
              simp only [Finset.mem_sdiff]
              have hpd : p ∈ D → p ∈ S := fun hp => hDS hp
              tauto
            exact hC'.symm.trans ((congrArg (fun X => S \ X) hCD).trans hD')
          · intro C hC
            refine ⟨S \ C, Finset.mem_powerset.mpr (Finset.sdiff_subset (s := S) (t := C)), ?_⟩
            have hCS : C ⊆ S := Finset.mem_powerset.mp hC
            ext p
            simp only [Finset.mem_sdiff]
            have hpc : p ∈ C → p ∈ S := fun hp => hCS hp
            tauto
          · intro C hC
            rw [Finset.card_sdiff]
            rw [Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hC)]
            congr 1
            have hle : C.card ≤ S.card := Finset.card_le_card (Finset.mem_powerset.mp hC)
            omega
    _ = n * (ℓ + 1) ^ S.card := by
          rw [sum_powerset_card_pow]

/-! ### Lemma 2.5 (cycles and primes) -/

/-- **Lemma 2.5** (Nat core): `#{σ | c(σ) = ℓ ∧ ∏_{p∈S} ppow | ord(σ)} · ∏_{p∈S} ppow ≤ n! · ℓ^|S|`. -/
lemma countCyclesOrderDiv_mul_le (n ℓ : ℕ) (m : ℕ) (S : Finset (m.primeFactors)) :
    countCyclesOrderDiv n ℓ m S * (∏ p ∈ S, ppow m p.1) ≤ Nat.factorial n * ℓ ^ S.card := by
  classical
  induction n using Nat.strong_induction_on generalizing ℓ S with
  | h n ih =>
      cases ℓ with
      | zero =>
          -- ℓ = 0
          by_cases hn0 : n = 0
          · subst n
            rw [countCyclesOrderDiv_zero 0 m S]
            by_cases hS : S = ∅
            · subst S
              simp
            · have hS' : ¬ (0 = 0 ∧ S = ∅) := by intro h; exact hS h.2
              rw [if_neg hS']
              simp
          · have hcount : countCyclesOrderDiv n 0 m S = 0 := by
              unfold countCyclesOrderDiv
              have hfilter : (Finset.univ : Finset (SymmetricGroup n)).filter
                  (fun σ => numCycles σ = 0 ∧ (∏ p ∈ S, ppow m p.1) ∣ orderOf σ) = ∅ := by
                apply Finset.filter_eq_empty_iff.mpr
                intro σ hσ hmem
                have h0 : numCycles σ = 0 := hmem.1
                have hcard : Fintype.card (Fin n) = 0 := (numCycles_eq_zero_iff σ).mp h0
                rw [Fintype.card_fin] at hcard
                omega
              rw [hfilter, Finset.card_empty]
            rw [hcount]
            simp
      | succ ℓ =>
          -- ℓ = ℓ' + 1
          by_cases hn0 : n = 0
          · subst n
            rw [countCyclesOrderDiv_zero (ℓ + 1) m S]
            by_cases hS : S = ∅
            · subst S; simp
            · have hℓ : ¬ (ℓ + 1 = 0 ∧ S = ∅) := by intro h; omega
              rw [if_neg hℓ]; simp
          · haveI : NeZero n := ⟨hn0⟩
            rw [countCyclesOrderDiv_rec m ℓ n S]
            rw [Finset.sum_mul]
            calc (∑ d ∈ Finset.Icc 1 n, Nat.descFactorial (n - 1) (d - 1) *
                    countCyclesOrderDiv (n - d) ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ d)) * (∏ p ∈ S, ppow m p.1))
                ≤ ∑ d ∈ Finset.Icc 1 n, Nat.descFactorial (n - 1) (d - 1) * (Nat.factorial (n - d) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) *
                    (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) := by
                    apply Finset.sum_le_sum
                    intro d hd
                    -- descFactorial * C(n-d) * ∏_S ≤ descFactorial * (n-d)! * ℓ^uncovered * covered
                    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
                    have hih := ih (n - d) (by omega : n - d < n) ℓ (S.filter (fun p => ¬ ppow m p.1 ∣ d))
                    -- hih : C(n-d) ℓ (filter) * ∏_{filter} ppow ≤ (n-d)! * ℓ^filter.card
                    -- ∏_S = covered * uncovered
                    have hpart : (∏ p ∈ S, ppow m p.1) = (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1) := by
                      exact (Finset.prod_filter_mul_prod_filter_not S (fun p => ppow m p.1 ∣ d) (fun p => ppow m p.1)).symm
                    calc Nat.descFactorial (n - 1) (d - 1) * countCyclesOrderDiv (n - d) ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ d)) * (∏ p ∈ S, ppow m p.1)
                        = Nat.descFactorial (n - 1) (d - 1) * (countCyclesOrderDiv (n - d) ℓ m (S.filter (fun p => ¬ ppow m p.1 ∣ d)) * (∏ p ∈ S.filter (fun p => ¬ ppow m p.1 ∣ d), ppow m p.1)) * (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) := by
                            rw [hpart]; ring
                      _ ≤ Nat.descFactorial (n - 1) (d - 1) * (Nat.factorial (n - d) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) * (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) := by
                            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hih)
                _ = Nat.factorial (n - 1) * (∑ d ∈ Finset.Icc 1 n, (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro d hd
                    have hdn : d ≤ n := (Finset.mem_Icc.mp hd).2
                    calc Nat.descFactorial (n - 1) (d - 1) * (Nat.factorial (n - d) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) * (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1)
                        = (Nat.factorial (n - d) * Nat.descFactorial (n - 1) (d - 1)) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card * (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) := by ring
                      _ = Nat.factorial (n - 1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card * (∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) := by
                          have hd1' : 1 ≤ d := (Finset.mem_Icc.mp hd).1
                          have hfac : (n - d).factorial * (n - 1).descFactorial (d - 1) = (n - 1).factorial := by
                            have hsub : (n - 1 - (d - 1)) = n - d := by omega
                            simpa [hsub] using (Nat.factorial_mul_descFactorial (n := n - 1) (k := d - 1) (by omega : d - 1 ≤ n - 1))
                          rw [hfac]
                      _ = Nat.factorial (n - 1) * ((∏ p ∈ S.filter (fun p => ppow m p.1 ∣ d), ppow m p.1) * ℓ ^ (S.filter (fun p => ¬ ppow m p.1 ∣ d)).card) := by ring
                _ ≤ Nat.factorial (n - 1) * (n * (ℓ + 1) ^ S.card) := by
                    exact Nat.mul_le_mul_left _ (sum_covered_mul_pow_card_le m n ℓ S)
                _ = Nat.factorial n * (ℓ + 1) ^ S.card := by
                    have hfac : Nat.factorial n = Nat.factorial (n - 1) * n := by
                      rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), Nat.mul_comm]
                    rw [hfac]
                    ring

/-! ### Lemma 2.5 (probability form) -/

/-- **Lemma 2.5 (cycles and primes)**: `P(c(πₙ) = ℓ, m | ord(πₙ)) ≤ ℓ^ω(m)/m`. -/
theorem cyclesAndPrimes_prob_le (ℓ m n : ℕ) (hm : m ≠ 0) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ m ∣ orderOf σ)).card /
        (Nat.factorial n : ℝ) ≤ ((ℓ : ℝ) ^ omega m) / (m : ℝ) := by
  classical
  have hmprod : m = ∏ p : m.primeFactors, ppow m p.1 := by
    simpa [ppow] using (Nat.prod_pow_primeFactors_factorization hm)
  have hcount : ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ m ∣ orderOf σ)).card =
      countCyclesOrderDiv n ℓ m (Finset.univ : Finset (m.primeFactors)) := by
    unfold countCyclesOrderDiv
    congr 1
    ext σ
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1, (prod_dvd_iff_of_pairwise_coprime_univ (x := orderOf σ) (f := fun p : m.primeFactors => ppow m p.1)
        Nat.pairwise_coprime_pow_primeFactors_factorization).mpr ((dvd_iff_ppow_dvd_of_primeFactors (N := orderOf σ) hm).1 h.2.2)⟩
    · intro h
      exact ⟨h.1, h.2.1, (dvd_iff_ppow_dvd_of_primeFactors (N := orderOf σ) hm).2
        ((prod_dvd_iff_of_pairwise_coprime_univ (x := orderOf σ) (f := fun p : m.primeFactors => ppow m p.1)
          Nat.pairwise_coprime_pow_primeFactors_factorization).1 h.2.2)⟩
  rw [hcount]
  have hcore := countCyclesOrderDiv_mul_le n ℓ m (Finset.univ : Finset (m.primeFactors))
  rw [← hmprod] at hcore
  rw [show (Finset.univ : Finset (m.primeFactors)).card = omega m by
    rw [Finset.card_univ, Fintype.card_coe]
    rfl] at hcore
  have hcoreR : (countCyclesOrderDiv n ℓ m (Finset.univ : Finset (m.primeFactors)) : ℝ) * (m : ℝ) ≤
      (Nat.factorial n : ℝ) * ((ℓ : ℝ) ^ omega m) := by
    exact_mod_cast hcore
  field_simp [show (Nat.factorial n : ℝ) ≠ 0 by positivity, show (m : ℝ) ≠ 0 by exact_mod_cast hm]
  nlinarith [hcoreR]

end MostProbableOrder
