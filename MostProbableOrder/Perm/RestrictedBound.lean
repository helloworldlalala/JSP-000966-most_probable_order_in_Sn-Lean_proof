import MostProbableOrder.Perm.Restricted
import MostProbableOrder.Arithmetic.DivisorBounds
import Mathlib.Data.Fin.Tuple.Finset

/-!
# I-restricted cycle-count upper bound (paper §2, Lemma 2.3 and Corollary 2.4)

The proof is a cycle-removal recursion combined with an ordered-tuple
averaging argument (the "delete-one" identity `n·T_{r+1}(n) = (r+1)·U_r(n)`).
This file establishes:

* `T I r n` / `U I r n` — ordered `r`-tuples of elements of `I` whose entries sum
  to `n` (resp. whose complement `n - sum` lies in `I`), each weighted by the
  product of reciprocals `1/f₁⋯fᵣ`.
* `averaging` — `n · T I (r+1) n = (r+1) · U I r n`.
* **Lemma 2.3** — `P(c(πₙ) = ℓ, πₙ I-restricted) ≤ (∑_{i∈I} 1/i)^{ℓ-1} / (n·(ℓ-1)!)`.
* **Corollary 2.4** — `P(c(πₙ) = ℓ, ord(πₙ) ∣ m) ≤ (σ(m)/m)^{ℓ-1} / (n·(ℓ-1)!)`.
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-! ### Ordered-tuple averaging machinery -/

/-- `∏ᵢ 1/fᵢ` (equal to `0` if any entry is `0`, since `1/0 = 0` in `ℝ`). -/
noncomputable def recipProd {r : ℕ} (f : Fin r → ℕ) : ℝ :=
  ∏ i, (1 : ℝ) / (f i : ℝ)

/-- All entries of the tuple `f` lie in `I`. -/
def entriesIn (I : Finset ℕ) {r : ℕ} (f : Fin r → ℕ) : Prop :=
  ∀ i, f i ∈ I

/-- The finite set of `r`-tuples of elements of `I`. -/
noncomputable def tupleFinset (I : Finset ℕ) (r : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ : Fin r => I)

/-- `T_r(n) = ∑_{ordered r-tuples in I^r, sum = n} 1/(f₁⋯fᵣ)`. -/
noncomputable def T (I : Finset ℕ) (r n : ℕ) : ℝ :=
  ∑ f ∈ tupleFinset I r, if (∑ i, f i) = n then recipProd f else 0

/-- `U_r(n) = ∑_{ordered r-tuples in I^r, n - sum ∈ I} 1/(f₁⋯fᵣ)`. -/
noncomputable def U (I : Finset ℕ) (r n : ℕ) : ℝ :=
  ∑ f ∈ tupleFinset I r, if (n - ∑ i, f i) ∈ I then recipProd f else 0

/-- `S(I) = ∑_{i ∈ I} 1/i`. -/
noncomputable def sumInv (I : Finset ℕ) : ℝ :=
  ∑ i ∈ I, (1 : ℝ) / (i : ℝ)

/-- `c_ℓ(n) := #{σ ∈ Sₙ : numCycles σ = ℓ ∧ IsRestricted I σ}`. -/
noncomputable def cardNumCyclesRestricted (I : Finset ℕ) (ℓ n : ℕ) : ℕ :=
  ((Finset.univ : Finset (SymmetricGroup n)).filter
    (fun σ => numCycles σ = ℓ ∧ IsRestricted I σ)).card

/-- The `0`-tuple set is the singleton `{fun _ => 0}`. -/
lemma tupleFinset_zero (I : Finset ℕ) :
    tupleFinset I 0 = {fun _ : Fin 0 => (0 : ℕ)} := by
  classical
  unfold tupleFinset
  rw [Fintype.piFinset_of_isEmpty (s := fun _ : Fin 0 => I)]
  ext f
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  ext i
  exact i.elim0

/-! ### Pointwise facts about `Fin.cons` and `Fin.insertNth` -/

@[simp] lemma recipProd_cons {r : ℕ} (a : ℕ) (t : Fin r → ℕ) :
    recipProd (Fin.cons a t) = (1 : ℝ) / (a : ℝ) * recipProd t := by
  unfold recipProd
  rw [Fin.prod_univ_succ]
  simp

@[simp] lemma recipProd_empty {r : ℕ} [IsEmpty (Fin r)] (f : Fin r → ℕ) : recipProd f = 1 := by
  unfold recipProd
  simp

@[simp] lemma entriesIn_cons (I : Finset ℕ) {r : ℕ} (a : ℕ) (t : Fin r → ℕ) :
    entriesIn I (Fin.cons a t) ↔ a ∈ I ∧ entriesIn I t := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun i => by simpa using h i.succ⟩
  · rintro ⟨ha, ht⟩ i
    cases i using Fin.cases with
    | zero => simpa using ha
    | succ j => exact ht j

@[simp] lemma sum_cons {r : ℕ} (a : ℕ) (t : Fin r → ℕ) :
    (∑ i : Fin (r + 1), (Fin.cons a t) i) = a + ∑ j : Fin r, t j := by
  rw [Fin.sum_univ_succ]
  simp

@[simp] lemma recipProd_insertNth {r : ℕ} (i : Fin (r + 1)) (a : ℕ) (g : Fin r → ℕ) :
    recipProd (Fin.insertNth i a g) = (1 : ℝ) / (a : ℝ) * recipProd g := by
  unfold recipProd
  rw [Fin.prod_univ_succAbove _ i]
  simp

@[simp] lemma sum_insertNth {r : ℕ} (i : Fin (r + 1)) (a : ℕ) (g : Fin r → ℕ) :
    (∑ k : Fin (r + 1), (Fin.insertNth i a g) k) = a + ∑ j : Fin r, g j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

/-- `insertNthEquiv` as a function equality (constant codomain `ℕ`). -/
@[simp] lemma insertNthEquiv_apply_fun {r : ℕ} (i : Fin (r + 1)) (a : ℕ) (g : Fin r → ℕ) :
    (Fin.insertNthEquiv (fun _ : Fin (r + 1) => ℕ) i) (a, g) = Fin.insertNth i a g := rfl

/-! ### The finite-sum factoring helper -/

/-- `∑_{x∈s} (if p x then c · f x else 0) = c · ∑_{x∈s} (if p x then f x else 0)`. -/
lemma sum_if_mul {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (c : ℝ) (f : α → ℝ) :
    (∑ x ∈ s, (if p x then c * f x else 0)) = c * (∑ x ∈ s, (if p x then f x else 0)) := by
  classical
  calc (∑ x ∈ s, (if p x then c * f x else 0))
      = ∑ x ∈ s, (c * (if p x then f x else 0)) := by
          apply Finset.sum_congr rfl; intro x hx
          by_cases hp : p x <;> simp [hp]
    _ = c * (∑ x ∈ s, (if p x then f x else 0)) := by rw [Finset.mul_sum]

/-! ### Decomposition of the tuple set into a first entry and the tail -/

/-- `∑_{f ∈ tupleFinset I (r+1)} F f = ∑_{a ∈ I} ∑_{t ∈ tupleFinset I r} F (Fin.cons a t)`. -/
lemma sum_tupleFinset_succ (I : Finset ℕ) (r : ℕ) (F : (Fin (r + 1) → ℕ) → ℝ) :
    (∑ f ∈ tupleFinset I (r + 1), F f) = ∑ a ∈ I, ∑ t ∈ tupleFinset I r, F (Fin.cons a t) := by
  classical
  unfold tupleFinset
  have hfilter : Fintype.piFinset (fun _ : Fin (r + 1) => I) =
      (I ×ˢ Fintype.piFinset (fun _ : Fin r => I)).map
        (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).toEmbedding := by
    simpa using (Finset.filter_piFinset_eq_map_consEquiv
      (S := fun _ : Fin (r + 1) => I) (P := fun (_ : Fin r → ℕ) => True))
  rw [hfilter]
  rw [Finset.sum_map]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro t ht
  rfl

/-! ### The recursion `T` / `U` under splitting the first coordinate -/

/-- `T I (r+1) n = ∑_{a∈I} (1/a) · ∑_{t : a + sum t = n} 1/(∏ t)`. -/
lemma T_succ (I : Finset ℕ) (r n : ℕ) :
    T I (r + 1) n = ∑ a ∈ I, (1 : ℝ) / (a : ℝ) *
      (∑ t ∈ tupleFinset I r, if a + (∑ j : Fin r, t j) = n then recipProd t else 0) := by
  unfold T
  rw [sum_tupleFinset_succ I r (fun f => if (∑ i : Fin (r + 1), f i) = n then recipProd f else 0)]
  apply Finset.sum_congr rfl; intro a ha
  rw [← sum_if_mul (tupleFinset I r) (fun t => a + (∑ j : Fin r, t j) = n) ((1 : ℝ) / (a : ℝ))
    (fun t => recipProd t)]
  apply Finset.sum_congr rfl; intro t ht
  simp [recipProd_cons]

/-- `U I (r+1) n = ∑_{a∈I} (1/a) · U I r (n - a)`. -/
lemma U_succ (I : Finset ℕ) (r n : ℕ) :
    U I (r + 1) n = ∑ a ∈ I, (1 : ℝ) / (a : ℝ) * U I r (n - a) := by
  unfold U
  rw [sum_tupleFinset_succ I r (fun f => if n - (∑ i : Fin (r + 1), f i) ∈ I then recipProd f else 0)]
  apply Finset.sum_congr rfl; intro a ha
  rw [← sum_if_mul (tupleFinset I r) (fun t => (n - a) - (∑ j : Fin r, t j) ∈ I) ((1 : ℝ) / (a : ℝ))
    (fun t => recipProd t)]
  apply Finset.sum_congr rfl; intro t ht
  have hsum : (∑ i : Fin (r + 1), (Fin.cons a t) i) = a + ∑ j : Fin r, t j := by simp
  have hsub : n - (a + ∑ j : Fin r, t j) = (n - a) - ∑ j : Fin r, t j := by omega
  rw [hsum, hsub, recipProd_cons]

/-! ### Monotonicity of `U` against `(∑1/i)^r` -/

/-- `U I 0 n = [n ∈ I]`. -/
lemma U_zero (I : Finset ℕ) (n : ℕ) : U I 0 n = if n ∈ I then (1 : ℝ) else 0 := by
  classical
  unfold U tupleFinset recipProd
  simp

/-- `U I r n ≤ (∑_{i∈I} 1/i)^r`. -/
lemma U_le_sumInv_pow (I : Finset ℕ) (r : ℕ) : ∀ n : ℕ, U I r n ≤ (sumInv I) ^ r := by
  classical
  induction r with
  | zero =>
      intro n
      rw [U_zero]
      by_cases hn : n ∈ I <;> simp [hn]
  | succ r ih =>
      intro n
      rw [U_succ]
      calc (∑ a ∈ I, (1 : ℝ) / (a : ℝ) * U I r (n - a))
          ≤ ∑ a ∈ I, (1 : ℝ) / (a : ℝ) * (sumInv I) ^ r := by
              apply Finset.sum_le_sum; intro a ha
              exact mul_le_mul_of_nonneg_left (ih (n - a))
                (one_div_nonneg.mpr (by exact_mod_cast (Nat.zero_le a)))
        _ = (sumInv I) ^ r * ∑ a ∈ I, (1 : ℝ) / (a : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro a ha; ring
        _ = (sumInv I) ^ r * (sumInv I) := by rw [sumInv]
        _ = (sumInv I) ^ (r + 1) := by ring

/-! ### The averaging (delete-one) identity -/

/-- `∑_{a∈s} (if a = k then c else 0) = if k ∈ s then c else 0`. -/
lemma sum_indicator_eq_of_mem {α : Type*} [DecidableEq α] (s : Finset α) (k : α) (c : ℝ) :
    (∑ a ∈ s, (if a = k then c else 0)) = if k ∈ s then c else 0 := by
  classical
  by_cases hk : k ∈ s
  · rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b hb hne; simp [hne]
    · intro hnot; exact (hnot hk).elim
  · have hz : (∑ a ∈ s, (if a = k then c else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro b hb
      have hne : b ≠ k := by intro h; apply hk; rwa [← h]
      simp [hne]
    simp [hk, hz]

/-- `∑_{a∈I} (if a + N = n then c else 0) = if n - N ∈ I then c else 0` (for `0 ∉ I`). -/
lemma sum_indicator_add_eq (I : Finset ℕ) (hI0 : 0 ∉ I) (N n : ℕ) (c : ℝ) :
    (∑ a ∈ I, (if a + N = n then c else 0)) = (if n - N ∈ I then c else 0) := by
  classical
  by_cases hN : N ≤ n
  · have habs : ∀ a, (a + N = n) ↔ (a = n - N) := by
      intro a; omega
    calc (∑ a ∈ I, (if a + N = n then c else 0))
        = ∑ a ∈ I, (if a = n - N then c else 0) := by
            apply Finset.sum_congr rfl; intro a ha; simp [habs a]
      _ = (if n - N ∈ I then c else 0) := sum_indicator_eq_of_mem I (n - N) c
  · have hsum0 : (∑ a ∈ I, (if a + N = n then c else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro b hb
      have hne : b + N ≠ n := by omega
      simp [hne]
    have hsub : n - N = 0 := by omega
    simp [hsum0, hsub, hI0]

/-- `a · (a⁻¹ · x) = x` for `a ≠ 0`. -/
lemma mul_inv_mul_eq {a x : ℝ} (ha : a ≠ 0) : a * (a⁻¹ * x) = x := by
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- For a fixed coordinate `i`, deleting it turns `∑ (fᵢ) · recipProd f` into `U`. -/
lemma delete_one_sum (I : Finset ℕ) (hI0 : 0 ∉ I) {r : ℕ} (n : ℕ) (i : Fin (r + 1)) :
    (∑ f ∈ tupleFinset I (r + 1), if (∑ k, f k) = n then (f i : ℝ) * recipProd f else 0) =
      U I r n := by
  classical
  have hsplit : tupleFinset I (r + 1) =
      (I ×ˢ tupleFinset I r).map (Fin.insertNthEquiv (fun _ : Fin (r + 1) => ℕ) i).toEmbedding := by
    simpa using (Finset.filter_piFinset_eq_map_insertNthEquiv
      (S := fun _ : Fin (r + 1) => I) (p := i) (P := fun (_ : Fin r → ℕ) => True))
  rw [hsplit]
  rw [Finset.sum_map]
  rw [Finset.sum_product]
  simp only [Equiv.toEmbedding_apply, insertNthEquiv_apply_fun, Fin.insertNthEquiv_apply,
    sum_insertNth, Fin.insertNth_apply_same, recipProd_insertNth]
  have hmain : (∑ a ∈ I, ∑ g ∈ tupleFinset I r,
        (if a + (∑ j : Fin r, g j) = n then (a : ℝ) * ((1 : ℝ) / (a : ℝ) * recipProd g) else 0))
      = (∑ a ∈ I, ∑ g ∈ tupleFinset I r, (if a + (∑ j : Fin r, g j) = n then recipProd g else 0)) := by
    apply Finset.sum_congr rfl; intro a ha
    apply Finset.sum_congr rfl; intro g hg
    have ha_ne : a ≠ 0 := by intro hz; apply hI0; rwa [hz] at ha
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha_ne
    by_cases hsum : a + (∑ j : Fin r, g j) = n
    · simp [hsum, mul_inv_mul_eq ha0]
    · simp [hsum]
  rw [hmain]
  rw [Finset.sum_comm]
  unfold U
  apply Finset.sum_congr rfl; intro g hg
  exact sum_indicator_add_eq I hI0 (∑ j : Fin r, g j) n (recipProd g)

/-- **Averaging identity**: `n · T I (r+1) n = (r+1) · U I r n`. -/
lemma averaging (I : Finset ℕ) (hI0 : 0 ∉ I) (r n : ℕ) :
    (n : ℝ) * T I (r + 1) n = ((r + 1 : ℕ) : ℝ) * U I r n := by
  classical
  unfold T
  calc (n : ℝ) * (∑ f ∈ tupleFinset I (r + 1), if (∑ i, f i) = n then recipProd f else 0)
      = ∑ f ∈ tupleFinset I (r + 1), (if (∑ i, f i) = n then (n : ℝ) * recipProd f else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro f hf
          by_cases hn : (∑ i, f i) = n <;> simp [hn]
    _ = ∑ f ∈ tupleFinset I (r + 1), (if (∑ i, f i) = n then (∑ k : Fin (r + 1), (f k : ℝ)) * recipProd f else 0) := by
          apply Finset.sum_congr rfl; intro f hf
          by_cases hn : (∑ i, f i) = n
          · have hcast : (n : ℝ) = ∑ k : Fin (r + 1), (f k : ℝ) := by
              rw [← hn, Nat.cast_sum]
            simp [hn]
            left
            exact hcast
          · simp [hn]
    _ = ∑ f ∈ tupleFinset I (r + 1), ∑ k : Fin (r + 1), (if (∑ i, f i) = n then (f k : ℝ) * recipProd f else 0) := by
          apply Finset.sum_congr rfl; intro f hf
          by_cases hn : (∑ i, f i) = n
          · simp [hn]
            rw [Finset.sum_mul]
          · simp [hn]
    _ = ∑ k : Fin (r + 1), ∑ f ∈ tupleFinset I (r + 1), (if (∑ i, f i) = n then (f k : ℝ) * recipProd f else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin (r + 1), U I r n := by
          apply Finset.sum_congr rfl; intro k hk
          exact delete_one_sum I hI0 n k
    _ = ((r + 1 : ℕ) : ℝ) * U I r n := by simp

/-! ### Connecting the permutation count to the tuple sums -/

/-- `numCycles σ = 0` iff the domain is empty. -/
lemma numCycles_eq_zero_iff {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    numCycles σ = 0 ↔ Fintype.card α = 0 := by
  classical
  unfold numCycles
  constructor
  · intro h
    have hcard0 : σ.cycleType.card = 0 := by omega
    have hsum0 : σ.cycleType.sum = 0 := by
      have hct : σ.cycleType = 0 := Multiset.card_eq_zero.mp hcard0
      simp [hct]
    have hdiff : Fintype.card α - σ.cycleType.sum = 0 := by omega
    rw [hsum0] at hdiff
    simpa using hdiff
  · intro h
    haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp h
    have hσ : σ = 1 := Subsingleton.elim σ 1
    rw [hσ]
    have hcard : Fintype.card α = 0 := Fintype.card_eq_zero_iff.2 ‹IsEmpty α›
    simp

/-- `cardNumCyclesRestricted I 0 m = [m = 0]`. -/
lemma card_numCycles_zero (I : Finset ℕ) (m : ℕ) :
    cardNumCyclesRestricted I 0 m = if m = 0 then 1 else 0 := by
  classical
  unfold cardNumCyclesRestricted
  by_cases hm : m = 0
  · subst m
    have hfilter : ((Finset.univ : Finset (SymmetricGroup 0)).filter
        (fun σ => numCycles σ = 0 ∧ IsRestricted I σ)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro σ
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ σ
      · constructor
        · have hσ : σ = 1 := Subsingleton.elim σ 1
          simp [numCycles, hσ]
        · intro a; exact Fin.elim0 a
    rw [hfilter, Finset.card_univ, card_symmetricGroup]
    simp
  · have hfilter : ((Finset.univ : Finset (SymmetricGroup m)).filter
        (fun σ => numCycles σ = 0 ∧ IsRestricted I σ)) = ∅ := by
      ext σ
      simp
      intro h
      have hcard : Fintype.card (Fin m) = 0 := (numCycles_eq_zero_iff σ).mp h
      rw [Fintype.card_fin] at hcard
      omega
    rw [hfilter, Finset.card_empty]
    simp [hm]

/-- `Nat.descFactorial (n-1) (d-1) = (n-1)! / (n-d)!` in `ℝ`. -/
lemma descFactorial_pred_cast (n d : ℕ) (hd : 1 ≤ d) (hdl : d ≤ n) :
    (Nat.descFactorial (n - 1) (d - 1) : ℝ) =
      (Nat.factorial (n - 1) : ℝ) / (Nat.factorial (n - d) : ℝ) := by
  have hfd := Nat.factorial_mul_descFactorial (n := n - 1) (k := d - 1) (by omega : d - 1 ≤ n - 1)
  have hsub : n - 1 - (d - 1) = n - d := by omega
  rw [hsub] at hfd
  have hfac_ne : (Nat.factorial (n - d) : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hfac_ne]
  rw [mul_comm]
  exact_mod_cast hfd

/-- `T I 1 n = [n ∈ I] / n`. -/
lemma T_one (I : Finset ℕ) (n : ℕ) : T I 1 n = if n ∈ I then (1 : ℝ) / (n : ℝ) else 0 := by
  classical
  unfold T
  rw [sum_tupleFinset_succ I 0 (fun f => if (∑ i : Fin 1, f i) = n then recipProd f else 0)]
  rw [tupleFinset_zero I]
  simp [recipProd_cons]

/-- `numCycles σ = 1 ↔ cycleLen σ = n` for `n ≥ 1`. -/
lemma numCycles_eq_one_iff_cycleLen_eq [NeZero n] (σ : SymmetricGroup n) (hn : 1 ≤ n) :
    numCycles σ = 1 ↔ cycleLen σ = n := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  calc numCycles σ = 1
      ↔ numCycles (residualSubtype σ) + 1 = 1 := by rw [numCycles_residualSubtype σ]
    _ ↔ numCycles (residualSubtype σ) = 0 := by omega
    _ ↔ Fintype.card {x : Fin n // ¬ Equiv.Perm.SameCycle σ (0 : Fin n) x} = 0 :=
          numCycles_eq_zero_iff (residualSubtype σ)
    _ ↔ n - cycleLen σ = 0 := by rw [card_complement_sameCycle σ]
    _ ↔ cycleLen σ = n := by
          have hle : cycleLen σ ≤ n := cycleLen_le σ
          constructor <;> intro h <;> omega

/-- `cardNumCyclesRestricted I 1 n = (n-1)! · [n ∈ I]`. -/
lemma cardNumCyclesRestricted_one (I : Finset ℕ) (n : ℕ) (hn : 1 ≤ n) :
    cardNumCyclesRestricted I 1 n = (Nat.factorial (n - 1)) * (if n ∈ I then 1 else 0) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  unfold cardNumCyclesRestricted
  by_cases hnI : n ∈ I
  · have hfilter : ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => numCycles σ = 1 ∧ IsRestricted I σ)) =
        ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => cycleLen σ = n)) := by
      apply Finset.ext; intro σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hnc, _⟩
        exact (numCycles_eq_one_iff_cycleLen_eq σ hn).mp hnc
      · intro hcl
        constructor
        · exact (numCycles_eq_one_iff_cycleLen_eq σ hn).mpr hcl
        · intro a
          have hsc : Equiv.Perm.SameCycle σ (0 : Fin n) a := by
            have hcard : Fintype.card {y : Fin n // Equiv.Perm.SameCycle σ (0 : Fin n) y} = n := by
              rw [cycleLen_eq_card_sameCycle σ] at hcl
              exact hcl
            have hfull : (Finset.univ.filter (fun y : Fin n => Equiv.Perm.SameCycle σ (0 : Fin n) y)) = Finset.univ := by
              apply Finset.eq_univ_of_card
              calc (Finset.univ.filter (fun y : Fin n => Equiv.Perm.SameCycle σ (0 : Fin n) y)).card
                  = Fintype.card {y : Fin n // Equiv.Perm.SameCycle σ (0 : Fin n) y} :=
                      (Fintype.card_subtype (fun y : Fin n => Equiv.Perm.SameCycle σ (0 : Fin n) y)).symm
                _ = n := hcard
                _ = Fintype.card (Fin n) := (Fintype.card_fin n).symm
            exact (Finset.mem_filter.mp (by rw [hfull]; exact Finset.mem_univ a)).2
          rw [cycleLength_eq_of_sameCycle σ a hsc, hcl]
          exact hnI
    rw [hfilter]
    rw [card_cycleLen_eq_factorial_pred (n := n) (d := n) hn le_rfl]
    simp [hnI]
  · have hfilter : ((Finset.univ : Finset (SymmetricGroup n)).filter
        (fun σ => numCycles σ = 1 ∧ IsRestricted I σ)) = ∅ := by
      ext σ
      simp
      intro hnc hir
      have hcl : cycleLen σ = n := (numCycles_eq_one_iff_cycleLen_eq σ hn).mp hnc
      have hmem : n ∈ I := by
        rw [← hcl, ← cycleLength_eq_cycleLen σ]
        exact hir (0 : Fin n)
      exact hnI hmem
    rw [hfilter, Finset.card_empty]
    simp [hnI]

/-! ### The cycle-removal recursion for `cardNumCyclesRestricted` -/

/-- `cardNumCyclesRestricted I (ℓ+1) n = ∑_{d∈I} descFactorial(n-1)(d-1) · cardNumCyclesRestricted I ℓ (n-d)`. -/
lemma cardNumCyclesRestricted_succ (I : Finset ℕ) (hI0 : 0 ∉ I) (ℓ n : ℕ)
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    (cardNumCyclesRestricted I (ℓ + 1) n : ℝ) =
      ∑ d ∈ I, (Nat.descFactorial (n - 1) (d - 1) : ℝ) * (cardNumCyclesRestricted I ℓ (n - d) : ℝ) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  let s : Finset (SymmetricGroup n) :=
    (Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ + 1 ∧ IsRestricted I σ)
  have hpart := Finset.card_eq_sum_card_image (f := cycleLen) (s := s)
  have himg : s.image cycleLen ⊆ I := by
    intro d hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨σ, hσ, rfl⟩
    rw [Finset.mem_filter] at hσ
    rw [← cycleLength_eq_cycleLen σ]
    exact hσ.2.2 (0 : Fin n)
  have hzero : ∀ d ∈ I, d ∉ s.image cycleLen → (s.filter (fun σ => cycleLen σ = d)).card = 0 := by
    intro d hd hnot
    apply Finset.card_eq_zero.mpr
    ext σ
    simp
    intro hσ hcd
    apply hnot
    rw [Finset.mem_image]
    exact ⟨σ, hσ, hcd⟩
  calc (cardNumCyclesRestricted I (ℓ + 1) n : ℝ)
      = (s.card : ℝ) := by unfold cardNumCyclesRestricted; rfl
    _ = (∑ d ∈ s.image cycleLen, (s.filter (fun σ => cycleLen σ = d)).card : ℝ) := by
          exact_mod_cast hpart
    _ = (∑ d ∈ I, (s.filter (fun σ => cycleLen σ = d)).card : ℝ) := by
          exact_mod_cast (Finset.sum_subset (s₁ := s.image cycleLen) (s₂ := I) himg hzero)
    _ = ∑ d ∈ I, (Nat.descFactorial (n - 1) (d - 1) : ℝ) * (cardNumCyclesRestricted I ℓ (n - d) : ℝ) := by
          apply Finset.sum_congr rfl; intro d hd
          have hd_ne : d ≠ 0 := by intro hz; apply hI0; rwa [hz] at hd
          have hd_pos : 1 ≤ d := by omega
          by_cases hdl : d ≤ n
          · have hfilt : (s.filter (fun σ => cycleLen σ = d)) =
                ((Finset.univ : Finset (SymmetricGroup n)).filter
                  (fun σ => cycleLen σ = d ∧ numCycles σ = ℓ + 1 ∧ IsRestricted I σ)) := by
              ext σ
              simp [s, Finset.mem_filter, and_comm, and_left_comm]
            rw [hfilt]
            rw [card_cycleLen_numCycles_IsRestricted d (ℓ + 1) hd_pos hdl (by omega : 1 ≤ ℓ + 1) I]
            simp only [hd, if_true, Nat.cast_mul]
            rw [show (ℓ + 1) - 1 = ℓ by omega]
            rfl
          · have hfiber : (s.filter (fun σ => cycleLen σ = d)).card = 0 := by
              apply Finset.card_eq_zero.mpr
              ext σ
              simp
              intro hσ hcd
              have hcl_le : cycleLen σ ≤ n := cycleLen_le σ
              rw [hcd] at hcl_le
              omega
            have hdf : (Nat.descFactorial (n - 1) (d - 1)) = 0 := by
              have hlt : n - 1 < d - 1 := by omega
              exact Nat.descFactorial_eq_zero_iff_lt.mpr hlt
            simp [hfiber, hdf]

/-! ### The averaging bridge `U I r n = ∑_{d∈I} T I r (n-d)` -/

/-- `U I r n = ∑_{d∈I} T I r (n-d)` for `r ≥ 1`. -/
lemma U_eq_sum_T (I : Finset ℕ) (hI0 : 0 ∉ I) (r n : ℕ) (hr : 1 ≤ r) :
    U I r n = ∑ d ∈ I, T I r (n - d) := by
  classical
  unfold U T
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro f hf
  have hfpos : 1 ≤ ∑ i : Fin r, f i := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp (by omega : 0 < r)
    have hi : f i ∈ I := by
      unfold tupleFinset at hf
      rw [Fintype.mem_piFinset] at hf
      exact hf i
    have hfi_pos : 1 ≤ f i := by
      have : f i ≠ 0 := by intro hz; apply hI0; rwa [hz] at hi
      omega
    calc 1 ≤ f i := hfi_pos
      _ ≤ ∑ j : Fin r, f j := Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
  have hiff : ∀ d ∈ I, (d = n - ∑ i : Fin r, f i) ↔ (∑ i : Fin r, f i = n - d) := by
    intro d hd
    have hd_pos : 1 ≤ d := by
      have : d ≠ 0 := by intro hz; apply hI0; rwa [hz] at hd
      omega
    constructor <;> intro h <;> omega
  calc (if n - (∑ i : Fin r, f i) ∈ I then recipProd f else 0)
      = (∑ d ∈ I, (if d = n - ∑ i : Fin r, f i then recipProd f else 0)) := by
          rw [sum_indicator_eq_of_mem I (n - ∑ i : Fin r, f i) (recipProd f)]
    _ = ∑ d ∈ I, (if (∑ i : Fin r, f i) = n - d then recipProd f else 0) := by
          apply Finset.sum_congr rfl; intro d hd
          simp [hiff d hd]

/-! ### Auxiliary facts for the induction -/

/-- `recipProd f = 0` if some entry of `f` is `0`. -/
lemma recipProd_eq_zero_of_mem_zero {r : ℕ} (f : Fin r → ℕ) (i : Fin r) (h : f i = 0) :
    recipProd f = 0 := by
  unfold recipProd
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simp [h]

/-- `T I r 0 = 0` for `r ≥ 1`. -/
lemma T_zero_of_pos (I : Finset ℕ) (r : ℕ) (hr : 1 ≤ r) : T I r 0 = 0 := by
  classical
  unfold T
  apply Finset.sum_eq_zero
  intro f hf
  by_cases hsum : (∑ i : Fin r, f i) = 0
  · obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp (by omega : 0 < r)
    have hfi : f i = 0 := by
      have hle : f i ≤ ∑ j : Fin r, f j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
      rw [hsum] at hle
      omega
    simp [hsum, recipProd_eq_zero_of_mem_zero f i hfi]
  · simp [hsum]

/-- `cardNumCyclesRestricted I r 0 = 0` for `r ≥ 1`. -/
lemma cardNumCyclesRestricted_zero_of_pos (I : Finset ℕ) (r : ℕ) (hr : 1 ≤ r) :
    cardNumCyclesRestricted I r 0 = 0 := by
  classical
  unfold cardNumCyclesRestricted
  apply Finset.card_eq_zero.mpr
  ext σ
  have hσ : σ = 1 := Subsingleton.elim σ 1
  simp [numCycles, hσ]
  omega

/-- Factoring the descending-factorial terms out of the induction sum. -/
lemma sum_descFactorial_mul_T_eq (I : Finset ℕ) (hI0 : 0 ∉ I) (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    (∑ d ∈ I, (Nat.descFactorial (n - 1) (d - 1) : ℝ) *
        ((Nat.factorial (n - d) : ℝ) / (Nat.factorial ℓ : ℝ) * T I ℓ (n - d)))
      = (Nat.factorial (n - 1) : ℝ) / (Nat.factorial ℓ : ℝ) * (∑ d ∈ I, T I ℓ (n - d)) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro d hd
  by_cases hdl : d ≤ n
  · have hd_pos : 1 ≤ d := by
      have : d ≠ 0 := by intro hz; apply hI0; rwa [hz] at hd
      omega
    have hdf := descFactorial_pred_cast n d hd_pos hdl
    rw [hdf]
    field_simp [show (Nat.factorial (n - d) : ℝ) ≠ 0 by positivity,
      show (Nat.factorial ℓ : ℝ) ≠ 0 by positivity]
  · have hdf : (Nat.descFactorial (n - 1) (d - 1) : ℝ) = 0 := by
      have hlt : n - 1 < d - 1 := by omega
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
      norm_num
    have hT : T I ℓ (n - d) = 0 := by
      have : n - d = 0 := by omega
      rw [this]
      exact T_zero_of_pos I ℓ hℓ
    simp [hdf, hT]

/-- `(n-1)!/ℓ! · (n/(ℓ+1)) = n!/(ℓ+1)!`. -/
lemma factorial_div_mul (n ℓ : ℕ) (hn : 1 ≤ n) :
    (Nat.factorial (n - 1) : ℝ) / (Nat.factorial ℓ : ℝ) * ((n : ℝ) / ((ℓ + 1 : ℕ) : ℝ)) =
      (Nat.factorial n : ℝ) / (Nat.factorial (ℓ + 1) : ℝ) := by
  have h1 : (Nat.factorial n : ℝ) = (Nat.factorial (n - 1) : ℝ) * (n : ℝ) := by
    have : Nat.factorial n = Nat.factorial (n - 1) * n := by
      rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), mul_comm]
    rw [this, Nat.cast_mul, mul_comm]
  have h2 : (Nat.factorial (ℓ + 1) : ℝ) = (Nat.factorial ℓ : ℝ) * ((ℓ + 1 : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    ring
  rw [h1, h2]
  field_simp [show (Nat.factorial ℓ : ℝ) ≠ 0 by positivity, show ((ℓ + 1 : ℕ) : ℝ) ≠ 0 by positivity]

/-! ### The exact counting identity -/

/-- `#{σ : numCycles σ = ℓ ∧ IsRestricted I σ} = (n!/ℓ!) · T I ℓ n`. -/
lemma cardNumCyclesRestricted_eq_T (I : Finset ℕ) (hI0 : 0 ∉ I) (ℓ : ℕ) :
    ∀ n : ℕ, 1 ≤ n → (cardNumCyclesRestricted I (ℓ + 1) n : ℝ) =
      (Nat.factorial n : ℝ) / (Nat.factorial (ℓ + 1) : ℝ) * T I (ℓ + 1) n := by
  induction ℓ with
  | zero =>
      intro n hn
      rw [cardNumCyclesRestricted_one I n hn]
      rw [T_one I n]
      by_cases hnI : n ∈ I
      · simp [hnI]
        have hf : (Nat.factorial n : ℝ) = (Nat.factorial (n - 1) : ℝ) * (n : ℝ) := by
          have : Nat.factorial n = Nat.factorial (n - 1) * n := by
            rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), mul_comm]
          rw [this, Nat.cast_mul, mul_comm]
        rw [hf]
        field_simp [show (n : ℝ) ≠ 0 by positivity]
      · simp [hnI]
  | succ ℓ ih =>
      intro n hn
      have hℓpos : 1 ≤ ℓ + 1 := by omega
      rw [cardNumCyclesRestricted_succ I hI0 (ℓ + 1) n hℓpos hn]
      calc (∑ d ∈ I, (Nat.descFactorial (n - 1) (d - 1) : ℝ) * (cardNumCyclesRestricted I (ℓ + 1) (n - d) : ℝ))
          = ∑ d ∈ I, (Nat.descFactorial (n - 1) (d - 1) : ℝ) *
              ((Nat.factorial (n - d) : ℝ) / (Nat.factorial (ℓ + 1) : ℝ) * T I (ℓ + 1) (n - d)) := by
              apply Finset.sum_congr rfl; intro d hd
              by_cases hnd : 1 ≤ n - d
              · rw [ih (n - d) hnd]
              · have hnd0 : n - d = 0 := by omega
                have hc : cardNumCyclesRestricted I (ℓ + 1) (n - d) = 0 := by
                  rw [hnd0]
                  exact cardNumCyclesRestricted_zero_of_pos I (ℓ + 1) (by omega)
                have hT : T I (ℓ + 1) (n - d) = 0 := by
                  rw [hnd0]
                  exact T_zero_of_pos I (ℓ + 1) (by omega)
                simp [hc, hT]
          _ = (Nat.factorial (n - 1) : ℝ) / (Nat.factorial (ℓ + 1) : ℝ) * (∑ d ∈ I, T I (ℓ + 1) (n - d)) := by
              exact sum_descFactorial_mul_T_eq I hI0 (ℓ + 1) n hℓpos hn
          _ = (Nat.factorial (n - 1) : ℝ) / (Nat.factorial (ℓ + 1) : ℝ) * U I (ℓ + 1) n := by
              rw [U_eq_sum_T I hI0 (ℓ + 1) n hℓpos]
          _ = (Nat.factorial n : ℝ) / (Nat.factorial (ℓ + 2) : ℝ) * T I (ℓ + 2) n := by
              have hU : U I (ℓ + 1) n = ((n : ℝ) / ((ℓ + 2 : ℕ) : ℝ)) * T I (ℓ + 2) n := by
                have hc : ((ℓ + 2 : ℕ) : ℝ) ≠ 0 := by positivity
                calc U I (ℓ + 1) n
                    = ((ℓ + 2 : ℕ) : ℝ) * U I (ℓ + 1) n / ((ℓ + 2 : ℕ) : ℝ) := by
                        rw [mul_comm, mul_div_cancel_right₀ _ hc]
                  _ = ((n : ℝ) * T I (ℓ + 2) n) / ((ℓ + 2 : ℕ) : ℝ) := by
                        rw [show ((ℓ + 2 : ℕ) : ℝ) * U I (ℓ + 1) n = (n : ℝ) * T I (ℓ + 2) n by
                          exact (averaging I hI0 (ℓ + 1) n).symm]
                  _ = ((n : ℝ) / ((ℓ + 2 : ℕ) : ℝ)) * T I (ℓ + 2) n := by ring
              rw [hU]
              rw [← mul_assoc, factorial_div_mul n (ℓ + 1) hn]

/-! ### Lemma 2.3 -/

/-- Every cycle length is at least 1 (so `0` is never a cycle length). -/
lemma one_le_cycleLength {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : α) :
    1 ≤ cycleLength σ a := by
  unfold cycleLength
  rw [Fintype.card_subtype]
  have ha : a ∈ (Finset.univ.filter (fun y : α => Equiv.Perm.SameCycle σ a y)) := by
    simp [Equiv.Perm.SameCycle.refl]
  exact Finset.card_pos.mpr ⟨a, ha⟩

/-- `IsRestricted` is unchanged by removing `0` from `I`. -/
lemma IsRestricted_erase_zero {α : Type*} [Fintype α] [DecidableEq α] (I : Finset ℕ) (σ : Equiv.Perm α) :
    IsRestricted I σ ↔ IsRestricted (I.erase 0) σ := by
  constructor
  · intro h a
    have ha : cycleLength σ a ∈ I := h a
    have hpos : cycleLength σ a ≠ 0 := by
      have := one_le_cycleLength σ a
      omega
    exact Finset.mem_erase.mpr ⟨hpos, ha⟩
  · intro h a
    exact (Finset.mem_erase.mp (h a)).2

/-- `sumInv` is unchanged by removing `0` from `I` (since `1/0 = 0`). -/
lemma sumInv_erase_zero (I : Finset ℕ) : sumInv I = sumInv (I.erase 0) := by
  classical
  unfold sumInv
  by_cases h0 : 0 ∈ I
  · rw [← Finset.add_sum_erase I (fun i => (1 : ℝ) / (i : ℝ)) h0]
    simp
  · rw [Finset.erase_eq_of_notMem h0]

/-- **Lemma 2.3** (for `0 ∉ I`): `P(c(πₙ) = ℓ, I-restricted) ≤ (∑_{i∈I}1/i)^{ℓ-1}/(n·(ℓ-1)!)`. -/
lemma prob_numCycles_IsRestricted_le' (I : Finset ℕ) (hI0 : 0 ∉ I) (ℓ n : ℕ)
    (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    ((cardNumCyclesRestricted I ℓ n : ℝ) / (Nat.factorial n : ℝ)) ≤
      (sumInv I) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := by
  classical
  obtain ⟨ℓ', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
  have hct : (cardNumCyclesRestricted I (ℓ' + 1) n : ℝ) =
      (Nat.factorial n : ℝ) / (Nat.factorial (ℓ' + 1) : ℝ) * T I (ℓ' + 1) n :=
    cardNumCyclesRestricted_eq_T I hI0 ℓ' n hn
  rw [hct]
  have hprob : (Nat.factorial n : ℝ) / (Nat.factorial (ℓ' + 1) : ℝ) * T I (ℓ' + 1) n / (Nat.factorial n : ℝ)
      = T I (ℓ' + 1) n / (Nat.factorial (ℓ' + 1) : ℝ) := by
    field_simp [show (Nat.factorial n : ℝ) ≠ 0 by positivity]
  rw [hprob]
  have havg : T I (ℓ' + 1) n = ((ℓ' + 1 : ℕ) : ℝ) / (n : ℝ) * U I ℓ' n := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    calc T I (ℓ' + 1) n
        = ((n : ℝ) * T I (ℓ' + 1) n) / (n : ℝ) := by rw [mul_div_cancel_left₀ _ hn0]
      _ = ((ℓ' + 1 : ℕ) : ℝ) * U I ℓ' n / (n : ℝ) := by rw [averaging I hI0 ℓ' n]
      _ = ((ℓ' + 1 : ℕ) : ℝ) / (n : ℝ) * U I ℓ' n := by ring
  rw [havg]
  calc ((ℓ' + 1 : ℕ) : ℝ) / (n : ℝ) * U I ℓ' n / (Nat.factorial (ℓ' + 1) : ℝ)
      = U I ℓ' n / ((n : ℝ) * (Nat.factorial ℓ' : ℝ)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          field_simp [show (n : ℝ) ≠ 0 by positivity, show ((ℓ' + 1 : ℕ) : ℝ) ≠ 0 by positivity]
    _ ≤ (sumInv I) ^ ℓ' / ((n : ℝ) * (Nat.factorial ℓ' : ℝ)) := by
          exact div_le_div_of_nonneg_right (U_le_sumInv_pow I ℓ' n)
            (by positivity : 0 ≤ (n : ℝ) * (Nat.factorial ℓ' : ℝ))

/-- **Lemma 2.3**: `P(c(πₙ) = ℓ, πₙ I-restricted) ≤ (∑_{i∈I}1/i)^{ℓ-1}/(n·(ℓ-1)!)`. -/
theorem prob_numCycles_IsRestricted_le (I : Finset ℕ) (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) :
    ((cardNumCyclesRestricted I ℓ n : ℝ) / (Nat.factorial n : ℝ)) ≤
      (sumInv I) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := by
  classical
  let I' := I.erase 0
  have hI0 : 0 ∉ I' := by simp [I']
  have hsum : sumInv I = sumInv I' := by simpa [I'] using sumInv_erase_zero I
  have hcard : cardNumCyclesRestricted I ℓ n = cardNumCyclesRestricted I' ℓ n := by
    unfold cardNumCyclesRestricted
    congr 1
    ext σ
    simp [I', IsRestricted_erase_zero I σ]
  rw [hcard, hsum]
  exact prob_numCycles_IsRestricted_le' I' hI0 ℓ n hℓ hn

/-! ### Corollary 2.4 -/

/-- The length of the cycle through `a` divides the order of `σ`. -/
lemma cycleLength_dvd_orderOf (σ : SymmetricGroup n) (a : Fin n) : cycleLength σ a ∣ orderOf σ := by
  classical
  revert σ a
  refine Nat.strong_induction_on n ?_
  intro n ih σ a
  haveI : NeZero n := ⟨by intro hn0; subst n; exact Fin.elim0 a⟩
  by_cases hsc : Equiv.Perm.SameCycle σ (0 : Fin n) a
  · rw [cycleLength_eq_of_sameCycle σ a hsc]
    exact cycleLen_dvd_orderOf σ
  · have hlen : cycleLength σ a =
        cycleLength (residual σ) ((Fintype.equivFinOfCardEq (card_complement_sameCycle σ)) ⟨a, hsc⟩) := by
      calc cycleLength σ a
          = cycleLength (residualSubtype σ) ⟨a, hsc⟩ := (cycleLength_residualSubtype σ ⟨a, hsc⟩).symm
        _ = cycleLength (residual σ) ((Fintype.equivFinOfCardEq (card_complement_sameCycle σ)) ⟨a, hsc⟩) := by
              unfold residual
              exact (cycleLength_permCongr (Fintype.equivFinOfCardEq (card_complement_sameCycle σ))
                (residualSubtype σ) ⟨a, hsc⟩).symm
    rw [hlen]
    have hord : orderOf σ = Nat.lcm (cycleLen σ) (orderOf (residual σ)) := orderOf_eq_lcm_cycleLen_residual σ
    have hlt : n - cycleLen σ < n := by
      have hpos : 0 < cycleLen σ := cycleLen_pos σ
      have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      omega
    have hih : cycleLength (residual σ) ((Fintype.equivFinOfCardEq (card_complement_sameCycle σ)) ⟨a, hsc⟩) ∣
        orderOf (residual σ) :=
      ih (n - cycleLen σ) hlt (residual σ) ((Fintype.equivFinOfCardEq (card_complement_sameCycle σ)) ⟨a, hsc⟩)
    rw [hord]
    exact dvd_trans hih (Nat.dvd_lcm_right _ _)

/-- `orderOf σ ∣ m` implies every cycle length divides `m`. -/
lemma orderOf_dvd_imp_IsRestricted_divisors (σ : SymmetricGroup n) (m : ℕ) (hm : m ≠ 0) :
    orderOf σ ∣ m → IsRestricted (m.divisors) σ := by
  intro h a
  have hdvd : cycleLength σ a ∣ m := dvd_trans (cycleLength_dvd_orderOf σ a) h
  exact Nat.mem_divisors.mpr ⟨hdvd, hm⟩

/-- `1/(m/e) = e/m` for `e ∣ m`, `m ≠ 0`. -/
lemma one_div_natDiv (m e : ℕ) (hm : m ≠ 0) (he : e ∣ m) :
    (1 : ℝ) / ((m / e : ℕ) : ℝ) = (e : ℝ) / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hme_ne : m / e ≠ 0 := by
    intro h
    have : m = 0 := by rw [← Nat.div_mul_cancel he, h, Nat.zero_mul]
    exact hm this
  have hme0 : ((m / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hme_ne
  have hdiv : ((m / e : ℕ) : ℝ) * (e : ℝ) = (m : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel he]
  field_simp [hm0, hme0]
  rw [hdiv]

/-- `m / (m / d) = d` for `d ∣ m`, `m ≠ 0`. -/
lemma nat_div_div_self (m d : ℕ) (hm : m ≠ 0) (hd : d ∣ m) : m / (m / d) = d := by
  have hd' : m / d ∣ m := Nat.div_dvd_of_dvd hd
  have h1 : (m / d) * (m / (m / d)) = m := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hd']
  have h2 : (m / d) * d = m := Nat.div_mul_cancel hd
  have hm_d_ne : m / d ≠ 0 := by
    intro h
    have : m = 0 := by rw [← h2, h, Nat.zero_mul]
    exact hm this
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hm_d_ne) (h1.trans h2.symm)

/-- `sumInv (m.divisors) = σ(m)/m`. -/
lemma sumInv_divisors_eq_sigma_div (m : ℕ) (hm : m ≠ 0) :
    sumInv (m.divisors) = (sigma m : ℝ) / (m : ℝ) := by
  classical
  unfold sumInv sigma
  calc (∑ d ∈ m.divisors, (1 : ℝ) / (d : ℝ))
      = ∑ d ∈ m.divisors, (1 : ℝ) / ((m / d : ℕ) : ℝ) := by
          rw [Finset.sum_bij (fun d _ => m / d)]
          · intro d hd
            exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hm⟩
          · intro a ha b hb hab
            have ha' : a ∣ m := Nat.dvd_of_mem_divisors ha
            have hb' : b ∣ m := Nat.dvd_of_mem_divisors hb
            calc a = m / (m / a) := (nat_div_div_self m a hm ha').symm
              _ = m / (m / b) := by rw [hab]
              _ = b := nat_div_div_self m b hm hb'
          · intro b hb
            have hb' : b ∣ m := Nat.dvd_of_mem_divisors hb
            refine ⟨m / b, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hb', hm⟩, ?_⟩
            exact nat_div_div_self m b hm hb'
          · intro d hd
            rw [nat_div_div_self m d hm (Nat.dvd_of_mem_divisors hd)]
    _ = ∑ d ∈ m.divisors, (d : ℝ) / (m : ℝ) := by
          apply Finset.sum_congr rfl; intro d hd
          exact one_div_natDiv m d hm (Nat.dvd_of_mem_divisors hd)
    _ = (∑ d ∈ m.divisors, (d : ℝ)) / (m : ℝ) := by
          rw [Finset.sum_div]
    _ = (sigma m : ℝ) / (m : ℝ) := by
          rw [sigma, Nat.cast_sum]

/-- **Corollary 2.4**: `P(c(πₙ) = ℓ, ord(πₙ) ∣ m) ≤ (σ(m)/m)^{ℓ-1}/(n·(ℓ-1)!)`. -/
theorem prob_numCycles_orderOf_dvd_le (ℓ n m : ℕ) (hℓ : 1 ≤ ℓ) (hn : 1 ≤ n) (hm : m ≠ 0) :
    (((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ orderOf σ ∣ m)).card /
        (Nat.factorial n : ℝ)) ≤
      ((sigma m : ℝ) / (m : ℝ)) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := by
  classical
  have hsub : ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ orderOf σ ∣ m))
      ⊆ ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ IsRestricted (m.divisors) σ)) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨Finset.mem_univ σ, hσ.2.1, orderOf_dvd_imp_IsRestricted_divisors σ m hm hσ.2.2⟩
  have hcard : ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ orderOf σ ∣ m)).card
      ≤ ((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ IsRestricted (m.divisors) σ)).card :=
    Finset.card_le_card hsub
  have hmain := prob_numCycles_IsRestricted_le (m.divisors) ℓ n hℓ hn
  -- hmain : cardNumCyclesRestricted (m.divisors) ℓ n / n! ≤ (sumInv (m.divisors))^{ℓ-1}/(n·(ℓ-1)!)
  calc (((Finset.univ : Finset (SymmetricGroup n)).filter (fun σ => numCycles σ = ℓ ∧ orderOf σ ∣ m)).card /
        (Nat.factorial n : ℝ))
      ≤ (cardNumCyclesRestricted (m.divisors) ℓ n : ℝ) / (Nat.factorial n : ℝ) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ (sumInv (m.divisors)) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := hmain
    _ = ((sigma m : ℝ) / (m : ℝ)) ^ (ℓ - 1) / ((n : ℝ) * (Nat.factorial (ℓ - 1) : ℝ)) := by
          rw [sumInv_divisors_eq_sigma_div m hm]

end MostProbableOrder

