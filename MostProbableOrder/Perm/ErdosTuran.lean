import MostProbableOrder.Perm.RestrictedBound
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The Erdős–Turán exact product formula

For a prime power `q`, the probability that `q` does not divide the order of a
uniform random permutation of `n` letters equals

    ∏_{j = 1}^{⌊n/q⌋} (1 - 1/(j q)).

This is the paper's citation of Erdős–Turán *Groups II*, Lemma 1, used in the
proof of Theorem 1.1 (`eq:approx_prob`).

The proof is a cycle-removal recursion combined with a telescoping identity on
the product.  The recursion (valid only for prime powers, so that
`q ∣ lcm(d, x) ↔ q ∣ d ∨ q ∣ x`) is

    p(n) = (1/n) Σ_{d=1}^n [q ∤ d] · p(n - d),   p(0) = 1,

whose unique solution is the product above.
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-! ### Prime-power divisibility of `lcm` -/

/-- For a prime power `q`, `q` divides `lcm a b` iff `q` divides `a` or `b`. -/
lemma dvd_lcm_iff_of_isPrimePow {q a b : ℕ} (hq : IsPrimePow q) :
    q ∣ a.lcm b ↔ q ∣ a ∨ q ∣ b := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb)]
  rw [Nat.factorization_lcm ha hb]
  rw [hp.pow_dvd_iff_le_factorization ha]
  rw [hp.pow_dvd_iff_le_factorization hb]
  simp

/-- For a prime power `q`, `q ∤ lcm a b ↔ q ∤ a ∧ q ∤ b`. -/
lemma not_dvd_lcm_iff_of_isPrimePow {q a b : ℕ} (hq : IsPrimePow q) :
    (¬ q ∣ a.lcm b) ↔ ¬ q ∣ a ∧ ¬ q ∣ b := by
  rw [dvd_lcm_iff_of_isPrimePow hq]
  simp

/-! ### Count and probability -/

/-- Number of permutations of `n` letters whose order is not divisible by `q`. -/
noncomputable def orderNotDivByCount (q n : ℕ) : ℕ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => ¬ q ∣ orderOf σ)).card

/-- Probability (in `ℝ`) that `q` does not divide the order of a random permutation. -/
noncomputable def orderNotDivByProb (q n : ℕ) : ℝ :=
  (orderNotDivByCount q n : ℝ) / (Nat.factorial n : ℝ)

/-! ### The cycle-removal recursion -/

/-- **Order-filtered cycle removal** (not-divisible version).
`#{σ | cycleLen σ = d ∧ q ∤ orderOf σ}
  = (if q ∣ d then 0 else descFactorial(n-1)(d-1) · #{τ | q ∤ orderOf τ})`. -/
theorem card_cycleLen_orderNotDivBy (q d : ℕ) (hq : IsPrimePow q) {n : ℕ} [NeZero n]
    (hd : 1 ≤ d) (hdl : d ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
      (fun σ => cycleLen σ = d ∧ ¬ q ∣ orderOf σ)).card =
      (if q ∣ d then 0 else
        Nat.descFactorial (n - 1) (d - 1) * orderNotDivByCount q (n - d)) := by
  classical
  rw [← Fintype.card_subtype (fun σ : SymmetricGroup n => cycleLen σ = d ∧ ¬ q ∣ orderOf σ)]
  by_cases hn1 : n = 1
  · subst n
    have hd1 : d = 1 := by omega
    subst d
    have hord1 : ∀ σ : SymmetricGroup 1, orderOf σ = 1 := by
      intro σ
      have hσ : σ = 1 := Subsingleton.elim σ 1
      rw [hσ, orderOf_one]
    have hord0 : ∀ τ : SymmetricGroup 0, orderOf τ = 1 := by
      intro τ
      have hτ : τ = 1 := Subsingleton.elim τ 1
      rw [hτ, orderOf_one]
    have hq1 : ¬ q ∣ 1 := by
      intro h
      have hq2 : 2 ≤ q := by
        obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
        exact hp.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt hk) p)
      have : q ≤ 1 := Nat.le_of_dvd (by omega : 0 < 1) h
      omega
    have hL : Fintype.card {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ ¬ q ∣ orderOf σ} = 1 := by
      let e : {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ ¬ q ∣ orderOf σ} ≃ SymmetricGroup 1 :=
        { toFun := fun ⟨σ, _⟩ => σ
          invFun := fun σ => ⟨σ, by
              rw [cycleLen_eq_one_iff]
              exact Subsingleton.elim _ _, by
              rw [hord1 σ]
              exact hq1⟩
          left_inv := by intro ⟨σ, _⟩; rfl
          right_inv := by intro σ; rfl }
      rw [Fintype.card_congr e, card_symmetricGroup 1]
      norm_num
    have hR : (if q ∣ 1 then 0 else Nat.descFactorial 0 0 * orderNotDivByCount q 0) = 1 := by
      rw [if_neg hq1]
      rw [Nat.descFactorial_zero, Nat.one_mul]
      unfold orderNotDivByCount
      have hfilter : (Finset.univ : Finset (SymmetricGroup 0)).filter (fun σ => ¬ q ∣ orderOf σ) = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro τ
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ τ, by rw [hord0 τ]; exact hq1⟩
      rw [hfilter, Finset.card_univ, card_symmetricGroup 0]
      norm_num
    rw [hL, hR]
  · cases n with
    | zero => omega
    | succ n' =>
      cases d with
      | zero => omega
      | succ d' =>
        haveI : NeZero n' := ⟨by omega⟩
        let e := cycleRemovalEquiv (n := n') (k := d')
        let source := {σ : SymmetricGroup (n' + 1) // cycleLen σ = d' + 1 ∧ ¬ q ∣ orderOf σ}
        let target := {p : (Fin d' ↪ Fin n') × SymmetricGroup (n' - d') //
          ¬ q ∣ (d' + 1).lcm (orderOf p.2)}
        let e' : source ≃ target :=
          { toFun := fun ⟨σ, hcyc, hord⟩ => ⟨e ⟨σ, hcyc⟩, by
              dsimp [e, cycleRemovalEquiv]
              have h := orderOf_eq_lcm_cycleLen_residualFwd σ hcyc
              rw [← h]
              exact hord⟩
            invFun := fun ⟨p, hp⟩ => ⟨e.symm p, (e.symm p).2, by
              have h := orderOf_eq_lcm_cycleLen_residualFwd (e.symm p).1 (e.symm p).2
              have hres : residualFwd (e.symm p).1 (e.symm p).2 = p.2 := congrArg Prod.snd (e.right_inv p)
              rw [h, hres]
              exact hp⟩
            left_inv := by
              intro ⟨σ, hcyc, hord⟩
              apply Subtype.ext
              simpa using congrArg Subtype.val (e.left_inv ⟨σ, hcyc⟩)
            right_inv := by
              intro ⟨p, hp⟩
              apply Subtype.ext
              dsimp
              exact e.right_inv p }
        rw [Fintype.card_congr e']
        by_cases hqd : q ∣ d' + 1
        · -- q | d ⟹ target is empty (¬ q | lcm = ¬q|d ∧ ¬q|x is impossible)
          have htarget_empty : IsEmpty target := by
            refine ⟨fun ⟨p, hp⟩ => ?_⟩
            have hdvd : q ∣ (d' + 1).lcm (orderOf p.2) := by
              exact (dvd_lcm_iff_of_isPrimePow hq).mpr (Or.inl hqd)
            exact hp hdvd
          rw [Fintype.card_eq_zero_iff.mpr htarget_empty]
          rw [if_pos hqd]
        · -- q ∤ d
          have hnot : ∀ o : ℕ, (¬ q ∣ (d' + 1).lcm o) ↔ (¬ q ∣ o) := by
            intro o
            rw [not_dvd_lcm_iff_of_isPrimePow hq]
            exact Iff.intro (fun h => h.2) (fun h => ⟨hqd, h⟩)
          let e'' : target ≃ (Fin d' ↪ Fin n') × {τ : SymmetricGroup (n' - d') // ¬ q ∣ orderOf τ} :=
            { toFun := fun ⟨p, hp⟩ => (p.1, ⟨p.2, (hnot (orderOf p.2)).1 hp⟩)
              invFun := fun q' => ⟨(q'.1, q'.2.1), (hnot (orderOf q'.2.1)).2 q'.2.2⟩
              left_inv := by intro ⟨p, hp⟩; rfl
              right_inv := by intro q'; rfl }
          rw [Fintype.card_congr e'']
          rw [Fintype.card_prod, Fintype.card_embedding_eq]
          rw [Fintype.card_fin, Fintype.card_fin]
          rw [if_neg hqd]
          unfold orderNotDivByCount
          rw [← Fintype.card_subtype (fun τ : SymmetricGroup (n' + 1 - (d' + 1)) => ¬ q ∣ orderOf τ)]
          have hsub : (n' + 1 - (d' + 1)) = n' - d' := by omega
          have hcard : Fintype.card {τ : SymmetricGroup (n' + 1 - (d' + 1)) // ¬ q ∣ orderOf τ} =
              Fintype.card {τ : SymmetricGroup (n' - d') // ¬ q ∣ orderOf τ} := by
            exact Fintype.card_congr (Equiv.cast
              (congrArg (fun k => {τ : SymmetricGroup k // ¬ q ∣ orderOf τ}) hsub))
          rw [hcard]
          rfl

/-- **Cycle-removal recursion** for the order-not-divisible count:
`C(q, n) = Σ_{d=1}^n [q ∤ d] · descFactorial(n-1)(d-1) · C(q, n-d)`. -/
theorem card_orderNotDivBy_rec (q : ℕ) (hq : IsPrimePow q) {n : ℕ} [NeZero n] :
    orderNotDivByCount q n =
      ∑ d ∈ Finset.Icc 1 n, (if q ∣ d then 0 else
        Nat.descFactorial (n - 1) (d - 1) * orderNotDivByCount q (n - d)) := by
  classical
  unfold orderNotDivByCount
  let s := (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => ¬ q ∣ orderOf σ)
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
  calc orderNotDivByCount q n
      = s.card := rfl
    _ = ∑ d ∈ s.image cycleLen, (s.filter (fun σ => cycleLen σ = d)).card := by
          simpa using hpart
    _ = ∑ d ∈ Finset.Icc 1 n, (s.filter (fun σ => cycleLen σ = d)).card := by
          rw [Finset.sum_subset himg hzero]
    _ = ∑ d ∈ Finset.Icc 1 n, (if q ∣ d then 0 else
            Nat.descFactorial (n - 1) (d - 1) * orderNotDivByCount q (n - d)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdn : d ≤ n := (Finset.mem_Icc.mp hd).2
          have hfilt : (s.filter (fun σ => cycleLen σ = d)) =
              (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => cycleLen σ = d ∧ ¬ q ∣ orderOf σ) := by
            ext σ
            simp [s, Finset.mem_filter, and_comm]
          rw [hfilt]
          rw [card_cycleLen_orderNotDivBy q d hq hd1 hdn]

/-! ### The probability recursion over `ℝ` -/

/-- `descFactorial(n-1)(d-1) / n! = 1/(n · (n-d)!)` as reals. -/
lemma descFactorial_div_factorial (n d : ℕ) (hd : 1 ≤ d) (hdl : d ≤ n) :
    (Nat.descFactorial (n - 1) (d - 1) : ℝ) / (Nat.factorial n : ℝ) =
      (1 : ℝ) / ((n : ℝ) * (Nat.factorial (n - d) : ℝ)) := by
  have hdf := descFactorial_pred_cast n d hd hdl
  rw [hdf]
  have hnpos : 0 < n := by omega
  have hfac : (Nat.factorial n : ℝ) = (Nat.factorial (n - 1) : ℝ) * (n : ℝ) := by
    have : Nat.factorial n = Nat.factorial (n - 1) * n := by
      rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), mul_comm]
    rw [this, Nat.cast_mul, mul_comm]
  rw [hfac]
  field_simp [show (Nat.factorial (n - 1) : ℝ) ≠ 0 by positivity,
    show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hnpos),
    show (Nat.factorial (n - d) : ℝ) ≠ 0 by positivity]

/-- **Probability recursion**: `p(n) = (1/n) Σ_{d=1}^n [q ∤ d] · p(n-d)`. -/
lemma orderNotDivByProb_rec (q : ℕ) (hq : IsPrimePow q) {n : ℕ} (hn : 1 ≤ n) :
    orderNotDivByProb q n =
      (1 / (n : ℝ)) * ∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else orderNotDivByProb q (n - d)) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  unfold orderNotDivByProb
  rw [card_orderNotDivBy_rec q hq]
  rw [Nat.cast_sum]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdn : d ≤ n := (Finset.mem_Icc.mp hd).2
  by_cases hqd : q ∣ d
  · simp [hqd]
  · simp [hqd]
    rw [show (Nat.descFactorial (n - 1) (d - 1) : ℝ) * (orderNotDivByCount q (n - d) : ℝ) / (Nat.factorial n : ℝ)
        = ((Nat.descFactorial (n - 1) (d - 1) : ℝ) / (Nat.factorial n : ℝ)) * (orderNotDivByCount q (n - d) : ℝ) by ring]
    rw [descFactorial_div_factorial n d hd1 hdn]
    field_simp [show (n : ℝ) ≠ 0 by positivity,
      show (Nat.factorial (n - d) : ℝ) ≠ 0 by positivity]

/-! ### `Nat` division facts for the product structure -/

/-- `(j·q - 1) / q = j - 1` for `1 ≤ j` and `q ≠ 0`. -/
lemma nat_div_sub_one (q j : ℕ) (hq : q ≠ 0) (hj : 1 ≤ j) : (j * q - 1) / q = j - 1 := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  rw [Nat.div_eq_iff hqpos]
  constructor
  · rw [Nat.mul_sub_right_distrib, Nat.one_mul]
    exact Nat.sub_le_sub_left (by omega : 1 ≤ q) (j * q)
  · rw [Nat.mul_sub_right_distrib, Nat.one_mul]
    have hle : q ≤ j * q := by simpa [Nat.one_mul] using Nat.mul_le_mul_right q hj
    rw [Nat.sub_add_cancel hle]

/-- `n/q = (n-1)/q` when `q ∤ n`. -/
lemma div_eq_pred_div_of_not_dvd {n q : ℕ} (h : ¬ q ∣ n) (hn : 1 ≤ n) : n / q = (n - 1) / q := by
  have hn1 : n - 1 + 1 = n := by omega
  rw [← hn1]
  rw [Nat.succ_div (a := n - 1) (b := q)]
  simp [hn1, h]

/-- `n/q = (n-1)/q + 1` when `q ∣ n`. -/
lemma div_eq_pred_div_add_one_of_dvd {n q : ℕ} (h : q ∣ n) (hn : 1 ≤ n) : n / q = (n - 1) / q + 1 := by
  have hn1 : n - 1 + 1 = n := by omega
  rw [← hn1]
  rw [Nat.succ_div (a := n - 1) (b := q)]
  have h' : q ∣ n - 1 + 1 := by simpa [hn1] using h
  simp [h']

/-! ### The Erdős–Turán product -/

/-- Erdős–Turán's product: `∏_{j ∈ range (n/q)} (1 - 1/((j+1) q))`. -/
noncomputable def erdosTuranProd (q n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (n / q), (1 - (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ)))

/-- The single factor of the product. -/
noncomputable def erdosTuranFactor (q j : ℕ) : ℝ :=
  (1 - (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ)))

@[simp] lemma erdosTuranProd_unfold (q n : ℕ) :
    erdosTuranProd q n = ∏ j ∈ Finset.range (n / q), erdosTuranFactor q j := rfl

/-- `erdosTuranProd` is unchanged when the top index is not divisible by `q`. -/
lemma erdosTuranProd_eq_pred_of_not_dvd (q n : ℕ) (h : ¬ q ∣ n) (hn : 1 ≤ n) :
    erdosTuranProd q n = erdosTuranProd q (n - 1) := by
  unfold erdosTuranProd
  rw [div_eq_pred_div_of_not_dvd h hn]

/-- `erdosTuranProd q n = erdosTuranProd q (n-1) * (1 - 1/n)` when `q ∣ n`. -/
lemma erdosTuranProd_div (q n : ℕ) (hq : q ≠ 0) (h : q ∣ n) (hn : 1 ≤ n) :
    erdosTuranProd q n = erdosTuranProd q (n - 1) * (1 - (1 : ℝ) / (n : ℝ)) := by
  unfold erdosTuranProd
  rw [div_eq_pred_div_add_one_of_dvd h hn]
  rw [Finset.prod_range_succ]
  congr 1
  have hN : ((n - 1) / q) + 1 = n / q := by rw [div_eq_pred_div_add_one_of_dvd h hn]
  rw [hN]
  have hnq : (n / q) * q = n := by
    rcases h with ⟨k, rfl⟩
    rw [Nat.mul_div_right k (Nat.pos_of_ne_zero hq)]
    exact Nat.mul_comm k q
  rw [show ((n / q : ℕ) : ℝ) * (q : ℝ) = (n : ℝ) by exact_mod_cast hnq]

/-- **Telescoping step**: `t·P(t) - (t-1)·P(t-1) = [q ∤ t] · P(t-1)`. -/
lemma erdosTuranProd_telescope (q t : ℕ) (hq : q ≠ 0) (ht : 1 ≤ t) :
    (t : ℝ) * erdosTuranProd q t - ((t - 1 : ℕ) : ℝ) * erdosTuranProd q (t - 1) =
      (if q ∣ t then (0 : ℝ) else erdosTuranProd q (t - 1)) := by
  have htn : t ≠ 0 := by omega
  by_cases hqt : q ∣ t
  · have hP := erdosTuranProd_div q t hq hqt ht
    rw [hP]
    rw [if_pos hqt]
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    field_simp [show (t : ℝ) ≠ 0 by positivity]
    ring
  · have hP := erdosTuranProd_eq_pred_of_not_dvd q t hqt ht
    rw [hP]
    rw [if_neg hqt]
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    ring

/-- The telescoping sum: `Σ_{d=1}^n (d·P(d) - (d-1)·P(d-1)) = n·P(n)`. -/
lemma sum_telescope (q n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, ((d : ℝ) * erdosTuranProd q d - ((d - 1 : ℕ) : ℝ) * erdosTuranProd q (d - 1))) =
      (n : ℝ) * erdosTuranProd q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [ih]
      rw [show (n + 1 - 1 : ℕ) = n by omega]
      ring

/-- **Identity 1 (telescoping)**: `Σ_{d=1}^n [q ∤ d] · P(d-1) = n · P(n)`. -/
lemma sum_erdosTuranProd_pred (q n : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else erdosTuranProd q (d - 1))) =
      (n : ℝ) * erdosTuranProd q n := by
  rw [← sum_telescope q n]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  exact (erdosTuranProd_telescope q d hq hd1).symm

/-! ### The reversal (block) identity -/

/-- `∑_{d ∈ Icc 1 n} P(n-d) = ∑_{d ∈ Icc 1 n} P(d-1)`. -/
lemma sum_erdosTuranProd_full_reversal (q n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, erdosTuranProd q (n - d)) =
    (∑ d ∈ Finset.Icc 1 n, erdosTuranProd q (d - 1)) := by
  have h1 : (∑ d ∈ Finset.Icc 1 n, erdosTuranProd q (n - d)) = ∑ t ∈ Finset.range n, erdosTuranProd q t := by
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by rfl]
    rw [Finset.sum_Ico_eq_sum_range (fun d => erdosTuranProd q (n - d)) 1 (n + 1)]
    rw [show (fun k : ℕ => erdosTuranProd q (n - (1 + k))) = (fun k => erdosTuranProd q (n - 1 - k)) by
      funext k; congr 1; omega]
    change (∑ k ∈ Finset.range n, erdosTuranProd q (n - 1 - k)) = ∑ t ∈ Finset.range n, erdosTuranProd q t
    rw [Finset.sum_range_reflect (fun t => erdosTuranProd q t) n]
  have h2 : (∑ d ∈ Finset.Icc 1 n, erdosTuranProd q (d - 1)) = ∑ t ∈ Finset.range n, erdosTuranProd q t := by
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by rfl]
    rw [Finset.sum_Ico_eq_sum_range (fun d => erdosTuranProd q (d - 1)) 1 (n + 1)]
    change (∑ k ∈ Finset.range n, erdosTuranProd q ((1 + k) - 1)) = ∑ t ∈ Finset.range n, erdosTuranProd q t
    rw [show (fun k : ℕ => erdosTuranProd q ((1 + k) - 1)) = (fun k => erdosTuranProd q k) by
      funext k; congr 1; omega]
  rw [h1, h2]

/-- `erdosTuranProd q (n - j*q) = erdosTuranProd q ((n/q - j) * q)`. -/
lemma erdosTuranProd_sub_mul (q n j : ℕ) (hq : q ≠ 0) :
    erdosTuranProd q (n - q * j) = erdosTuranProd q ((n / q - j) * q) := by
  unfold erdosTuranProd
  congr 1
  rw [Nat.sub_mul_div n q j]
  rw [show ((n / q - j) * q) / q = n / q - j by
    rw [Nat.mul_comm]
    exact Nat.mul_div_right (n / q - j) (Nat.pos_of_ne_zero hq)]

/-- `erdosTuranProd q (q*j - 1) = erdosTuranProd q ((j-1)*q)` for `1 ≤ j`. -/
lemma erdosTuranProd_pred_mul (q j : ℕ) (hq : q ≠ 0) (hj : 1 ≤ j) :
    erdosTuranProd q (q * j - 1) = erdosTuranProd q ((j - 1) * q) := by
  unfold erdosTuranProd
  congr 1
  have hdiv : (q * j - 1) / q = j - 1 := by
    rw [show q * j - 1 = j * q - 1 by rw [Nat.mul_comm]]
    exact nat_div_sub_one q j hq hj
  rw [hdiv]
  rw [show (j - 1) * q = q * (j - 1) by rw [Nat.mul_comm]]
  rw [Nat.mul_div_right (j - 1) (Nat.pos_of_ne_zero hq)]

/-- `∑_{d ∈ Icc 1 n} (if q ∣ d then f d else 0) = ∑_{j ∈ Icc 1 (n/q)} f (q·j)`. -/
lemma sum_if_dvd_mul {q n : ℕ} (hq : q ≠ 0) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then f d else 0)) = ∑ j ∈ Finset.Icc 1 (n / q), f (q * j) := by
  classical
  rw [← Finset.sum_filter (fun d => q ∣ d) f]
  have hreindex : (∑ d ∈ (Finset.Icc 1 n).filter (fun d => q ∣ d), f d) = ∑ j ∈ Finset.Icc 1 (n / q), f (q * j) := by
    symm
    rw [Finset.sum_bij (fun j _ => q * j)]
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc]
      rw [Finset.mem_Icc] at hj
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hq) (by omega : 0 < j))
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)).mp hj.2
      · exact Nat.dvd_mul_right q j
    · intro a ha b hb hab
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hq) hab
    · intro d hd
      rw [Finset.mem_filter] at hd
      rcases hd.2 with ⟨j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      rw [Finset.mem_Icc] at hd ⊢
      constructor
      · by_cases hj0 : j = 0
        · subst j; simp at hd
        · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
      · rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)]
        simpa [Nat.mul_comm] using hd.1.2
    · intro j hj
      rfl
  rw [hreindex]

/-- The excluded sums agree: `Σ [q ∣ d] P(n-d) = Σ [q ∣ d] P(d-1)`. -/
lemma sum_erdosTuranProd_excluded (q n : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then erdosTuranProd q (n - d) else (0 : ℝ))) =
    (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then erdosTuranProd q (d - 1) else (0 : ℝ))) := by
  classical
  rw [sum_if_dvd_mul hq (fun d => erdosTuranProd q (n - d))]
  rw [sum_if_dvd_mul hq (fun d => erdosTuranProd q (d - 1))]
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have h1 : (∑ j ∈ Finset.Icc 1 (n / q), erdosTuranProd q (n - q * j)) =
      ∑ j ∈ Finset.Icc 1 (n / q), erdosTuranProd q ((n / q - j) * q) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact erdosTuranProd_sub_mul q n j hq
  have h2 : (∑ j ∈ Finset.Icc 1 (n / q), erdosTuranProd q (q * j - 1)) =
      ∑ j ∈ Finset.Icc 1 (n / q), erdosTuranProd q ((j - 1) * q) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact erdosTuranProd_pred_mul q j hq (Finset.mem_Icc.mp hj).1
  rw [h1, h2]
  let N := n / q
  have hrefl : (∑ j ∈ Finset.Icc 1 N, erdosTuranProd q ((N - j) * q)) = ∑ j ∈ Finset.Icc 1 N, erdosTuranProd q ((j - 1) * q) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by rfl]
    rw [Finset.sum_Ico_eq_sum_range (fun j => erdosTuranProd q ((N - j) * q)) 1 (N + 1)]
    rw [show (fun k : ℕ => erdosTuranProd q ((N - (1 + k)) * q)) = (fun k => erdosTuranProd q ((N - 1 - k) * q)) by
      funext k; congr 2; omega]
    change (∑ k ∈ Finset.range N, erdosTuranProd q ((N - 1 - k) * q)) = ∑ j ∈ Finset.Ico 1 (N + 1), erdosTuranProd q ((j - 1) * q)
    rw [Finset.sum_range_reflect (fun k => erdosTuranProd q (k * q)) N]
    rw [Finset.sum_Ico_eq_sum_range (fun j => erdosTuranProd q ((j - 1) * q)) 1 (N + 1)]
    rw [show (fun k : ℕ => erdosTuranProd q (((1 + k) - 1) * q)) = (fun k => erdosTuranProd q (k * q)) by
      funext k; congr 2; omega]
    change (∑ j ∈ Finset.range N, erdosTuranProd q (j * q)) = ∑ k ∈ Finset.range N, erdosTuranProd q (k * q)
    rfl
  rw [hrefl]

/-- **Reversal**: `Σ [q ∤ d] P(n-d) = Σ [q ∤ d] P(d-1)`. -/
lemma sum_erdosTuranProd_reversal (q n : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else erdosTuranProd q (n - d))) =
    (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else erdosTuranProd q (d - 1))) := by
  classical
  have hdiff1 : (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else erdosTuranProd q (n - d))) =
      (∑ d ∈ Finset.Icc 1 n, erdosTuranProd q (n - d)) -
        (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then erdosTuranProd q (n - d) else (0 : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : q ∣ d <;> simp [h]
  have hdiff2 : (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else erdosTuranProd q (d - 1))) =
      (∑ d ∈ Finset.Icc 1 n, erdosTuranProd q (d - 1)) -
        (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then erdosTuranProd q (d - 1) else (0 : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : q ∣ d <;> simp [h]
  rw [hdiff1, hdiff2]
  rw [sum_erdosTuranProd_full_reversal q n]
  rw [sum_erdosTuranProd_excluded q n hq]

/-! ### The main theorem -/

/-- A prime power is nonzero. -/
lemma IsPrimePow.ne_zero' {q : ℕ} (hq : IsPrimePow q) : q ≠ 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  exact pow_ne_zero k (Nat.Prime.ne_zero hp)

/-- **Erdős–Turán exact formula**: for a prime power `q`,
`P(q ∤ ord(πₙ)) = ∏_{j=1}^{⌊n/q⌋}(1 - 1/(j q))`. -/
theorem orderNotDivByProb_eq_erdosTuranProd (q : ℕ) (hq : IsPrimePow q) :
    ∀ n : ℕ, orderNotDivByProb q n = erdosTuranProd q n := by
  have hq0 : q ≠ 0 := IsPrimePow.ne_zero' hq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        unfold orderNotDivByProb orderNotDivByCount
        have hq1 : ¬ q ∣ 1 := by
          intro h
          have hq2 : 2 ≤ q := by
            obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
            exact hp.two_le.trans (Nat.le_self_pow (Nat.ne_of_gt hk) p)
          have : q ≤ 1 := Nat.le_of_dvd (by omega : 0 < 1) h
          omega
        have hfilter : (Finset.univ : Finset (SymmetricGroup 0)).filter (fun σ => ¬ q ∣ orderOf σ) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro σ
          rw [Finset.mem_filter]
          constructor
          · exact Finset.mem_univ σ
          · have hσ : σ = 1 := Subsingleton.elim σ 1
            rw [hσ, orderOf_one]
            exact hq1
        rw [hfilter, Finset.card_univ, card_symmetricGroup 0]
        unfold erdosTuranProd
        norm_num
      · have hn1 : 1 ≤ n := by omega
        haveI : NeZero n := ⟨hn⟩
        rw [orderNotDivByProb_rec q hq hn1]
        rw [show (∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else orderNotDivByProb q (n - d))) =
            ∑ d ∈ Finset.Icc 1 n, (if q ∣ d then (0 : ℝ) else erdosTuranProd q (n - d)) by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hqd : q ∣ d
          · simp [hqd]
          · simp [hqd]
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
            have hdn : d ≤ n := (Finset.mem_Icc.mp hd).2
            exact ih (n - d) (by omega : n - d < n)]
        rw [sum_erdosTuranProd_reversal q n hq0]
        rw [sum_erdosTuranProd_pred q n hq0]
        rw [show (1 / (n : ℝ)) * ((n : ℝ) * erdosTuranProd q n) = erdosTuranProd q n by
          field_simp [show (n : ℝ) ≠ 0 by positivity]]

/-! ### The bounds `1/q ≤ P(q | ord) ≤ Σ 1/(jq)` (paper's `eq:approx_prob`) -/

/-- **Weierstrass product inequality**: for `0 ≤ f i ≤ 1`,
`1 - ∏(1 - f i) ≤ Σ f i`. -/
lemma one_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ f i) (hf_le : ∀ i ∈ s, f i ≤ 1) :
    (1 : ℝ) - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      have hfa_nonneg : 0 ≤ f a := hf_nonneg a (Finset.mem_insert_self a s)
      have hprod_le_one : ∏ i ∈ s, (1 - f i) ≤ 1 := by
        refine Finset.prod_le_one ?h0 ?h1
        · intro i hi; exact sub_nonneg.mpr (hf_le i (Finset.mem_insert_of_mem hi))
        · intro i hi; exact sub_le_self (1 : ℝ) (hf_nonneg i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert has, Finset.sum_insert has]
      have ih' : (1 : ℝ) - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := ih
        (fun i hi => hf_nonneg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf_le i (Finset.mem_insert_of_mem hi))
      have hmul : f a * ∏ i ∈ s, (1 - f i) ≤ f a := mul_le_of_le_one_right hfa_nonneg hprod_le_one
      nlinarith

/-- **Single-factor lower bound**: for `a ∈ s`, `f a ≤ 1 - ∏(1 - f i)`. -/
lemma one_sub_prod_ge_single {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (a : ι) (ha : a ∈ s)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ f i) (hf_le : ∀ i ∈ s, f i ≤ 1) :
    f a ≤ (1 : ℝ) - ∏ i ∈ s, (1 - f i) := by
  classical
  have hfa_le : f a ≤ 1 := hf_le a ha
  have hprod_erase_le_one : ∏ i ∈ s.erase a, (1 - f i) ≤ 1 := by
    refine Finset.prod_le_one ?h0 ?h1
    · intro i hi; exact sub_nonneg.mpr (hf_le i (Finset.mem_of_mem_erase hi))
    · intro i hi; exact sub_le_self (1 : ℝ) (hf_nonneg i (Finset.mem_of_mem_erase hi))
  rw [← Finset.mul_prod_erase s (fun i => 1 - f i) ha]
  have hle : (1 - f a) * ∏ i ∈ s.erase a, (1 - f i) ≤ 1 - f a := by
    simpa using mul_le_mul_of_nonneg_left hprod_erase_le_one (sub_nonneg.mpr hfa_le)
  linarith

/-- The factor `1/((j+1) q)` of the Erdős–Turán product. -/
noncomputable def invMul (q j : ℕ) : ℝ := (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))

/-- `0 ≤ 1/((j+1) q)`. -/
lemma invMul_nonneg (q j : ℕ) : 0 ≤ invMul q j := by
  unfold invMul
  exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- `1/((j+1) q) ≤ 1` for `q ≠ 0`. -/
lemma invMul_le_one (q j : ℕ) (hq : q ≠ 0) : invMul q j ≤ 1 := by
  unfold invMul
  have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) * (q : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos j) (Nat.pos_of_ne_zero hq)))
  exact (div_le_one hpos).mpr h1

/-- **Upper bound**: `P(q | ord) ≤ Σ_{j=1}^{⌊n/q⌋} 1/(jq)`. -/
lemma one_sub_erdosTuranProd_le_sum_inv (q n : ℕ) (hq : q ≠ 0) :
    (1 : ℝ) - erdosTuranProd q n ≤ ∑ j ∈ Finset.range (n / q), invMul q j := by
  unfold erdosTuranProd
  exact one_sub_prod_le_sum (Finset.range (n / q)) (fun j => (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ)))
    (fun j hj => div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (fun j hj => invMul_le_one q j hq)

/-- **Lower bound**: `1/q ≤ P(q | ord)` for `q ≤ n`. -/
lemma one_div_q_le_one_sub_erdosTuranProd (q n : ℕ) (hq : q ≠ 0) (h : q ≤ n) :
    (1 : ℝ) / (q : ℝ) ≤ (1 : ℝ) - erdosTuranProd q n := by
  unfold erdosTuranProd
  have hmem : 0 ∈ Finset.range (n / q) := by
    rw [Finset.mem_range]
    exact Nat.succ_le_iff.mp ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)).mpr (by simpa using h))
  have hle := one_sub_prod_ge_single (Finset.range (n / q)) (fun j => (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ))) 0 hmem
    (fun j hj => div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (fun j hj => invMul_le_one q j hq)
  simpa using hle

/-- **`eq:approx_prob`**: for a prime power `q` with `q ≤ n`,
`1/q ≤ P(q ∣ ord(πₙ)) ≤ Σ_{j=1}^{⌊n/q⌋} 1/(jq)`. -/
theorem erdosTuran_approx_prob (q n : ℕ) (hq : IsPrimePow q) (h : q ≤ n) :
    (1 : ℝ) / (q : ℝ) ≤ 1 - orderNotDivByProb q n ∧
      1 - orderNotDivByProb q n ≤ ∑ j ∈ Finset.range (n / q), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) * (q : ℝ)) := by
  have hq0 : q ≠ 0 := IsPrimePow.ne_zero' hq
  have hmain := orderNotDivByProb_eq_erdosTuranProd q hq n
  constructor
  · rw [hmain]
    exact one_div_q_le_one_sub_erdosTuranProd q n hq0 h
  · rw [hmain]
    exact one_sub_erdosTuranProd_le_sum_inv q n hq0

end MostProbableOrder
