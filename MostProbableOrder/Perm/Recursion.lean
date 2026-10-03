import MostProbableOrder.Perm.Decompose

/-!
# Corollary 2.2 — the recursion for `pₙ(m)`

Faithful transcription of the paper's **Corollary 2.2 (first statement)**:

  `P(ord(πₙ) = m) = (1/n) · Σ_{0 ≤ k < n} P(lcm(ord(πₖ), n-k) = m)`.

We state it in the equivalent "cycle length" form (summing over the length
`d = n-k` of the cycle through `0`, which ranges over `1 ≤ d ≤ n`):

  `pₙ(m) = (1/n) · Σ_{1 ≤ d ≤ n} #{σ ∈ S_{n-d} | lcm(d, ord σ) = m} / (n-d)!`.

The proof is an immediate consequence of the order-filtered cycle-removal
counting identity `card_cycleLen_orderOf_eq` (MP-007) together with the
fiberwise partition of permutations by their `cycleLen`.
-/

open Finset

namespace MostProbableOrder

/-- `#{σ ∈ S_{n-d} | lcm(d, ord σ) = m}`. -/
noncomputable def lcmOrderCount (n d m : ℕ) : ℕ :=
  ((Finset.univ : Finset (SymmetricGroup (n - d))).filter (fun σ => Nat.lcm d (orderOf σ) = m)).card

/-- Probability that for a uniformly random `σ ∈ S_{n-d}`, `lcm(d, ord σ) = m`. -/
noncomputable def lcmOrderProb (n d m : ℕ) : ℝ :=
  (lcmOrderCount n d m : ℝ) / (Nat.factorial (n - d) : ℝ)

/-- The algebraic coefficient identity behind the recursion:
`descFactorial(n-1)(d-1)·X / n! = (1/n) · X/(n-d)!`. -/
lemma descFactorial_mul_div_factorial_eq (n d X : ℕ) [NeZero n] (hd : 1 ≤ d) (hdl : d ≤ n) :
    ((Nat.descFactorial (n-1) (d-1) * X : ℕ) : ℝ) / (Nat.factorial n : ℝ)
      = (1 / (n : ℝ)) * ((X : ℝ) / (Nat.factorial (n-d) : ℝ)) := by
  have hnpos : 0 < n := NeZero.pos n
  have hnd : (n - 1) - (d - 1) = n - d := by omega
  have hfac_mul : Nat.factorial (n - d) * Nat.descFactorial (n-1) (d-1) = Nat.factorial (n-1) := by
    simpa [hnd] using (Nat.factorial_mul_descFactorial (n := n-1) (k := d-1) (by omega : d-1 ≤ n-1))
  have hfac_n : Nat.factorial n = n * Nat.factorial (n-1) := by
    rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), Nat.mul_comm]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hnd0 : (Nat.factorial (n-d) : ℝ) ≠ 0 := by positivity
  have hdesc0 : (Nat.descFactorial (n-1) (d-1) : ℝ) ≠ 0 := by
    have hpos : 0 < Nat.descFactorial (n-1) (d-1) := (Nat.descFactorial_pos).mpr (by omega : d-1 ≤ n-1)
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [Nat.cast_mul]
  rw [show (Nat.factorial n : ℝ) = (n : ℝ) * (Nat.factorial (n-1) : ℝ) by
    rw [hfac_n, Nat.cast_mul]]
  rw [show (Nat.factorial (n-1) : ℝ) = (Nat.factorial (n-d) : ℝ) * (Nat.descFactorial (n-1) (d-1) : ℝ) by
    rw [← hfac_mul, Nat.cast_mul]]
  field_simp [hn0, hnd0, hdesc0]

section recursion

variable {n : ℕ} [NeZero n]

/-- **Corollary 2.2, first statement — counting form.** The number of
permutations of order `m` is the sum over cycle lengths `d ∈ [1,n]` of
`descFactorial(n-1)(d-1) · #{σ ∈ S_{n-d} | lcm(d, ord σ) = m}`. -/
lemma card_orderEq_eq_sum_lcm (m : ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => orderOf π = m)).card =
      ∑ d ∈ Finset.Icc 1 n, Nat.descFactorial (n - 1) (d - 1) * lcmOrderCount n d m := by
  classical
  let A := (Finset.univ : Finset (SymmetricGroup n)).filter (fun π => orderOf π = m)
  have hmap : Set.MapsTo cycleLen (↑A : Set (SymmetricGroup n)) (↑(Finset.Icc 1 n) : Set ℕ) := by
    intro π hπ
    exact Finset.mem_Icc.mpr ⟨by exact cycleLen_pos π, cycleLen_le π⟩
  have hfib : A.card = ∑ d ∈ Finset.Icc 1 n, (A.filter (fun π => cycleLen π = d)).card := by
    simpa [A] using (Finset.card_eq_sum_card_fiberwise (f := cycleLen) (s := A)
      (t := Finset.Icc 1 n) hmap)
  rw [hfib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdl : d ≤ n := (Finset.mem_Icc.mp hd).2
  calc (A.filter (fun π => cycleLen π = d)).card
      = ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => cycleLen π = d ∧ orderOf π = m)).card := by
          congr 1
          ext π
          simp [A, and_comm, and_left_comm]
    _ = Nat.descFactorial (n - 1) (d - 1) * lcmOrderCount n d m := by
          rw [card_cycleLen_orderOf_eq d m hd1 hdl]
          rfl

/-- **Corollary 2.2, first statement.** The recursion for `pₙ(m)`:
`pₙ(m) = (1/n) · Σ_{1 ≤ d ≤ n} P_{n-d}(lcm(d, ord) = m)`. -/
theorem p_eq_sum_recursion (m : ℕ) :
    p n m = (1 / (n : ℝ)) * ∑ d ∈ Finset.Icc 1 n, lcmOrderProb n d m := by
  classical
  calc p n m
      = (((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => orderOf π = m)).card : ℝ) /
            (Nat.factorial n : ℝ) := by rfl
    _ = (∑ d ∈ Finset.Icc 1 n, ((Nat.descFactorial (n - 1) (d - 1) * lcmOrderCount n d m : ℕ) : ℝ)) /
            (Nat.factorial n : ℝ) := by
          rw [card_orderEq_eq_sum_lcm m, Nat.cast_sum]
    _ = ∑ d ∈ Finset.Icc 1 n, ((Nat.descFactorial (n - 1) (d - 1) * lcmOrderCount n d m : ℕ) : ℝ) /
            (Nat.factorial n : ℝ) := by
          rw [Finset.sum_div]
    _ = ∑ d ∈ Finset.Icc 1 n, (1 / (n : ℝ)) * ((lcmOrderCount n d m : ℝ) / (Nat.factorial (n - d) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact descFactorial_mul_div_factorial_eq (n := n) (d := d) (X := lcmOrderCount n d m)
            (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    _ = (1 / (n : ℝ)) * ∑ d ∈ Finset.Icc 1 n, (lcmOrderCount n d m : ℝ) / (Nat.factorial (n - d) : ℝ) := by
          rw [Finset.mul_sum]

end recursion

end MostProbableOrder
