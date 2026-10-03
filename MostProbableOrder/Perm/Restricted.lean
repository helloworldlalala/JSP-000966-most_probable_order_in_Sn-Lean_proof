import MostProbableOrder.Basic
import MostProbableOrder.Perm.Decompose
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# I-restricted cycle counts (paper §2, Lemma 2.3 and Corollary 2.4)

Definitions and combinatorial core for the "I-restricted" cycle-count bound:
`P(c(πₙ) = ℓ, πₙ I-restricted) ≤ (∑_{i∈I} 1/i)^{ℓ-1} / (n·(ℓ-1)!)`.

* `numCycles σ` — the number of cycles of `σ` (including fixed points).
* `cycleLength σ a` — the length of the cycle through `a` (1 if `a` is fixed).
* `IsRestricted I σ` — every cycle length lies in `I`.

The proof is a cycle-removal recursion (the Feller chain) combined with an
ordered-tuple averaging argument. This file establishes the permutation-level
machinery; the averaging / induction is assembled on top.
-/

open Finset
open scoped Real

namespace MostProbableOrder

/-! ### Definitions -/

/-- Number of cycles (including fixed points) of a permutation of a finite type. -/
noncomputable def numCycles {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : ℕ :=
  σ.cycleType.card + (Fintype.card α - σ.cycleType.sum)

/-- Cycle length through `a` = size of the orbit of `a` (1 for a fixed point). -/
noncomputable def cycleLength {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (a : α) : ℕ :=
  Fintype.card {y : α // Equiv.Perm.SameCycle σ a y}

/-- `σ` is `I`-restricted if every cycle (including fixed points as 1-cycles) has length in `I`. -/
def IsRestricted {α : Type*} [Fintype α] [DecidableEq α] (I : Finset ℕ) (σ : Equiv.Perm α) : Prop :=
  ∀ a : α, cycleLength σ a ∈ I

noncomputable instance instDecidableIsRestricted {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset ℕ) (σ : Equiv.Perm α) : Decidable (IsRestricted I σ) :=
  Classical.propDecidable _

/-! ### Invariance under `permCongr` (conjugation) -/

section Invariance

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `support` is transported by `permCongr`. -/
lemma support_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support = σ.support.map e.toEmbedding := by
  ext x
  rw [Equiv.Perm.mem_support, Finset.mem_map]
  constructor
  · intro h
    refine ⟨e.symm x, ?_, ?_⟩
    · rw [Equiv.Perm.mem_support]
      intro h0
      apply h
      rw [Equiv.permCongr_apply, h0, Equiv.apply_symm_apply]
    · simp
  · rintro ⟨a, ha, rfl⟩
    intro h
    have h' : σ a = a := e.injective (by simpa [Equiv.permCongr_apply] using h)
    exact (Equiv.Perm.mem_support.mp ha) h'

/-- `support.card` is invariant under `permCongr`. -/
lemma card_support_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  rw [support_permCongr, Finset.card_map]

/-- Powers of `permCongr` commute with applying `e`. -/
lemma permCongr_zpow_apply (e : α ≃ β) (σ : Equiv.Perm α) (i : ℤ) (x : α) :
    ((e.permCongr σ) ^ i) (e x) = e ((σ ^ i) x) := by
  change ((e.permCongrHom σ) ^ i) (e x) = e ((σ ^ i) x)
  rw [← map_zpow (e.permCongrHom) σ i]
  change (e.permCongr (σ ^ i)) (e x) = e ((σ ^ i) x)
  rw [Equiv.permCongr_apply]
  rw [Equiv.symm_apply_apply]

/-- `SameCycle` is transported by `permCongr`. -/
lemma sameCycle_permCongr (e : α ≃ β) (σ : Equiv.Perm α) (x : α) (y : β) :
    Equiv.Perm.SameCycle (e.permCongr σ) (e x) y ↔ Equiv.Perm.SameCycle σ x (e.symm y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply e.injective
    calc e ((σ ^ i) x) = ((e.permCongr σ) ^ i) (e x) := (permCongr_zpow_apply e σ i x).symm
      _ = y := hi
      _ = e (e.symm y) := (Equiv.apply_symm_apply e y).symm
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    calc ((e.permCongr σ) ^ i) (e x) = e ((σ ^ i) x) := permCongr_zpow_apply e σ i x
      _ = e (e.symm y) := by rw [hi]
      _ = y := Equiv.apply_symm_apply e y

/-- `IsCycle` is preserved by `permCongr`. -/
lemma isCycle_permCongr (e : α ≃ β) {σ : Equiv.Perm α} (hσ : σ.IsCycle) :
    (e.permCongr σ).IsCycle := by
  rcases hσ with ⟨x, hx, hx'⟩
  refine ⟨e x, ?_, ?_⟩
  · intro h
    have : e (σ x) = e x := by simpa [Equiv.permCongr_apply] using h
    exact hx (e.injective this)
  · intro y hy
    have hy' : σ (e.symm y) ≠ e.symm y := by
      intro h'
      have : e (σ (e.symm y)) = y := by rw [h', Equiv.apply_symm_apply]
      exact hy (by simpa [Equiv.permCongr_apply] using this)
    exact (sameCycle_permCongr e σ x y).mpr (hx' hy')

/-- `Disjoint` is preserved by `permCongr`. -/
lemma disjoint_permCongr (e : α ≃ β) {σ τ : Equiv.Perm α} (h : Equiv.Perm.Disjoint σ τ) :
    Equiv.Perm.Disjoint (e.permCongr σ) (e.permCongr τ) := by
  intro y
  rcases h (e.symm y) with h1 | h2
  · left
    rw [Equiv.permCongr_apply, h1, Equiv.apply_symm_apply]
  · right
    rw [Equiv.permCongr_apply, h2, Equiv.apply_symm_apply]

/-- `cycleType` is invariant under `permCongr`. -/
lemma cycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one =>
      rw [Equiv.Perm.cycleType_one, Equiv.Perm.cycleType_eq_zero]
      change e.permCongr (Equiv.refl α) = Equiv.refl β
      exact Equiv.permCongr_refl e
  | base_cycles σ hσ =>
      have hσ' : (e.permCongr σ).IsCycle := isCycle_permCongr e hσ
      rw [Equiv.Perm.IsCycle.cycleType hσ, Equiv.Perm.IsCycle.cycleType hσ']
      rw [card_support_permCongr]
  | induction_disjoint σ τ hd _ hσ hτ =>
      rw [Equiv.permCongr_mul]
      rw [Equiv.Perm.Disjoint.cycleType_mul hd]
      rw [Equiv.Perm.Disjoint.cycleType_mul (disjoint_permCongr e hd)]
      rw [hσ, hτ]

/-- `numCycles` is invariant under `permCongr`. -/
lemma numCycles_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    numCycles (e.permCongr σ) = numCycles σ := by
  unfold numCycles
  rw [cycleType_permCongr e σ]
  rw [← Fintype.card_congr e]

/-- `cycleLength` is invariant under `permCongr`. -/
lemma cycleLength_permCongr (e : α ≃ β) (σ : Equiv.Perm α) (x : α) :
    cycleLength (e.permCongr σ) (e x) = cycleLength σ x := by
  unfold cycleLength
  refine Fintype.card_congr ?_
  refine Equiv.subtypeEquiv (e := e.symm) ?h
  intro y
  exact sameCycle_permCongr e σ x y

/-- `IsRestricted` is invariant under `permCongr`. -/
lemma IsRestricted_permCongr (e : α ≃ β) (σ : Equiv.Perm α) (I : Finset ℕ) :
    IsRestricted I (e.permCongr σ) ↔ IsRestricted I σ := by
  constructor
  · intro h a
    have := h (e a)
    simpa [cycleLength_permCongr e σ a] using this
  · intro h b
    have := h (e.symm b)
    have hb : cycleLength (e.permCongr σ) b = cycleLength σ (e.symm b) := by
      rw [← cycleLength_permCongr e σ (e.symm b)]
      congr 1
      simp
    rwa [hb]

end Invariance

/-! ### Decomposition under cycle removal -/

section Decomposition

variable {n : ℕ} [NeZero n]

/-- `cycleLength` through `0` equals `cycleLen`. -/
lemma cycleLength_eq_cycleLen (σ : SymmetricGroup n) : cycleLength σ (0 : Fin n) = cycleLen σ := by
  unfold cycleLength
  exact (cycleLen_eq_card_sameCycle σ).symm

/-- If `x` is in the cycle of `0`, its cycle length equals `cycleLen σ`. -/
lemma cycleLength_eq_of_sameCycle (σ : SymmetricGroup n) (x : Fin n)
    (h : Equiv.Perm.SameCycle σ (0 : Fin n) x) : cycleLength σ x = cycleLen σ := by
  unfold cycleLength
  rw [cycleLen_eq_card_sameCycle σ]
  apply Fintype.card_congr
  refine Equiv.subtypeEquivRight ?_
  intro y
  constructor
  · intro hxy
    exact Equiv.Perm.SameCycle.trans h hxy
  · intro h0y
    exact Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm h) h0y

/-- A point in the same cycle as a complement point is also in the complement. -/
lemma not_sameCycle_zero_of_sameCycle_of_complement (σ : SymmetricGroup n)
    (x : {y : Fin n // ¬ Equiv.Perm.SameCycle σ (0 : Fin n) y}) (y : Fin n)
    (h : Equiv.Perm.SameCycle σ x.1 y) : ¬ Equiv.Perm.SameCycle σ (0 : Fin n) y := by
  intro h0y
  exact x.2 (Equiv.Perm.SameCycle.trans h0y (Equiv.Perm.SameCycle.symm h))

/-- The cycle length of the residual equals that of `σ` on the complement. -/
lemma cycleLength_residualSubtype (σ : SymmetricGroup n)
    (x : {y : Fin n // ¬ Equiv.Perm.SameCycle σ (0 : Fin n) y}) :
    cycleLength (residualSubtype σ) x = cycleLength σ x.1 := by
  unfold cycleLength
  apply Fintype.card_congr
  exact
  { toFun := fun y => Subtype.mk y.1.1 (Iff.mp Equiv.Perm.sameCycle_subtypePerm y.2)
    invFun := fun y => Subtype.mk
      (Subtype.mk y.1 (not_sameCycle_zero_of_sameCycle_of_complement σ x y.1 y.2))
      (Iff.mpr Equiv.Perm.sameCycle_subtypePerm y.2)
    left_inv := by intro y; rfl
    right_inv := by intro y; rfl }

/-- The cycle type of the cycle through `0`. -/
lemma cycleType_cycleOf (σ : SymmetricGroup n) :
    (σ.cycleOf 0).cycleType = if cycleLen σ = 1 then 0 else {cycleLen σ} := by
  classical
  by_cases h : cycleLen σ = 1
  · have h0 : σ (0 : Fin n) = 0 := (cycleLen_eq_one_iff σ).mp h
    have h1 : σ.cycleOf 0 = 1 := by simpa using h0
    simp [h, h1]
  · have h0 : σ (0 : Fin n) ≠ 0 := by
      intro h0'
      exact h ((cycleLen_eq_one_iff σ).mpr h0')
    have hcyc : (σ.cycleOf 0).IsCycle := Equiv.Perm.isCycle_cycleOf σ h0
    rw [Equiv.Perm.IsCycle.cycleType hcyc]
    rw [← Equiv.Perm.IsCycle.orderOf hcyc]
    rw [orderOf_cycleOf_eq_cycleLen σ]
    simp [h]

/-- `IsRestricted` decomposes under cycle removal. -/
lemma IsRestricted_residualSubtype (σ : SymmetricGroup n) (I : Finset ℕ) :
    IsRestricted I σ ↔ cycleLen σ ∈ I ∧ IsRestricted I (residualSubtype σ) := by
  constructor
  · intro h
    constructor
    · rw [← cycleLength_eq_cycleLen σ]
      exact h (0 : Fin n)
    · intro x
      rw [cycleLength_residualSubtype σ x]
      exact h x.1
  · rintro ⟨hcyc, hr⟩ a
    by_cases hsc : Equiv.Perm.SameCycle σ (0 : Fin n) a
    · rw [cycleLength_eq_of_sameCycle σ a hsc]
      exact hcyc
    · have := hr ⟨a, hsc⟩
      rwa [cycleLength_residualSubtype σ ⟨a, hsc⟩] at this

/-- The cycle through `0` contributes exactly one cycle to `numCycles`. -/
lemma numCycles_cycleOf (σ : SymmetricGroup n) :
    (σ.cycleOf 0).cycleType.card + (cycleLen σ - (σ.cycleOf 0).cycleType.sum) = 1 := by
  rw [cycleType_cycleOf σ]
  by_cases h : cycleLen σ = 1
  · simp [h]
  · simp [h]

/-- `numCycles` decomposes under cycle removal: removing the cycle through `0` loses one cycle. -/
lemma numCycles_residualSubtype (σ : SymmetricGroup n) :
    numCycles σ = numCycles (residualSubtype σ) + 1 := by
  classical
  unfold numCycles
  have hct : σ.cycleType = (σ.cycleOf 0).cycleType + (residualSubtype σ).cycleType := by
    calc σ.cycleType
        = (Equiv.Perm.ofSubtype (cyclePerm σ) * Equiv.Perm.ofSubtype (residualSubtype σ)).cycleType :=
            congrArg Equiv.Perm.cycleType (decompose_mul σ)
      _ = (Equiv.Perm.ofSubtype (cyclePerm σ)).cycleType + (Equiv.Perm.ofSubtype (residualSubtype σ)).cycleType :=
            Equiv.Perm.Disjoint.cycleType_mul (disjoint_cyclePerm_residual σ)
      _ = (σ.cycleOf 0).cycleType + (residualSubtype σ).cycleType := by
            rw [ofSubtype_cyclePerm σ, Equiv.Perm.cycleType_ofSubtype]
  rw [hct]
  rw [Multiset.card_add, Multiset.sum_add]
  have h1 : (σ.cycleOf 0).cycleType.card + (cycleLen σ - (σ.cycleOf 0).cycleType.sum) = 1 :=
    numCycles_cycleOf σ
  have h2 : (residualSubtype σ).cycleType.sum ≤ n - cycleLen σ := by
    calc (residualSubtype σ).cycleType.sum = (residualSubtype σ).support.card :=
        Equiv.Perm.sum_cycleType _
      _ ≤ Fintype.card {x : Fin n // ¬ Equiv.Perm.SameCycle σ (0 : Fin n) x} :=
          (residualSubtype σ).support.card_le_univ
      _ = n - cycleLen σ := card_complement_sameCycle σ
  have h3 : (σ.cycleOf 0).cycleType.sum + (residualSubtype σ).cycleType.sum ≤ n := by
    have hsum := congrArg Multiset.sum hct
    rw [Multiset.sum_add] at hsum
    rw [← hsum]
    simpa using Equiv.Perm.sum_cycleType_le σ
  have h4 : (residualSubtype σ).cycleType.sum + cycleLen σ ≤ n := by
    have hcl : cycleLen σ ≤ n := cycleLen_le σ
    omega
  have h5 : (σ.cycleOf 0).cycleType.sum ≤ cycleLen σ := by
    rw [cycleType_cycleOf σ]
    by_cases h : cycleLen σ = 1 <;> simp [h]
  rw [Fintype.card_fin, card_complement_sameCycle σ]
  omega

end Decomposition

/-! ### Transport to the `Fin`-indexed residual -/

section Transport

variable {n : ℕ} [NeZero n]

/-- `numCycles` decomposes through the `Fin`-indexed residual `residualFwd`. -/
lemma numCycles_residualFwd {k : ℕ} (σ : SymmetricGroup (n + 1)) (h : cycleLen σ = k + 1) :
    numCycles σ = numCycles (residualFwd σ h) + 1 := by
  have hnc : numCycles (residualFwd σ h) = numCycles (residualSubtype σ) := by
    unfold residualFwd
    rw [Equiv.permCongr_symm]
    rw [numCycles_permCongr, numCycles_permCongr]
  rw [hnc]
  exact numCycles_residualSubtype σ

/-- `IsRestricted` decomposes through the `Fin`-indexed residual `residualFwd`. -/
lemma IsRestricted_residualFwd {k : ℕ} (σ : SymmetricGroup (n + 1)) (h : cycleLen σ = k + 1)
    (I : Finset ℕ) :
    IsRestricted I σ ↔ (k + 1 ∈ I) ∧ IsRestricted I (residualFwd σ h) := by
  have hir : IsRestricted I (residualSubtype σ) ↔ IsRestricted I (residualFwd σ h) := by
    unfold residualFwd
    rw [Equiv.permCongr_symm]
    rw [IsRestricted_permCongr, IsRestricted_permCongr]
  rw [IsRestricted_residualSubtype σ I]
  rw [h]
  rw [hir]

end Transport

/-! ### The cycle-removal counting recursion -/

section Counting

variable {n : ℕ} [NeZero n]

/-- **Cycle-removal count** for `numCycles` and `IsRestricted`:
`#{σ | cycleLen σ = d ∧ numCycles σ = ℓ ∧ IsRestricted I σ}
 = (if d ∈ I then descFactorial(n-1)(d-1) · #{τ | numCycles τ = ℓ-1 ∧ IsRestricted I τ} else 0)`. -/
theorem card_cycleLen_numCycles_IsRestricted (d ℓ : ℕ) (hd : 1 ≤ d) (hdl : d ≤ n) (hℓpos : 1 ≤ ℓ)
    (I : Finset ℕ) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter
      (fun σ => cycleLen σ = d ∧ numCycles σ = ℓ ∧ IsRestricted I σ)).card =
      (if d ∈ I then
        (Nat.descFactorial (n - 1) (d - 1)) *
          ((Finset.univ : Finset (SymmetricGroup (n - d))).filter
            (fun τ => numCycles τ = ℓ - 1 ∧ IsRestricted I τ)).card
      else 0) := by
  classical
  rw [← Fintype.card_subtype (fun σ : SymmetricGroup n => cycleLen σ = d ∧ numCycles σ = ℓ ∧ IsRestricted I σ)]
  by_cases hn1 : n = 1
  · subst n
    have hd1 : d = 1 := by omega
    subst d
    -- S₁ : the unique permutation is the identity: numCycles = 1, cycleLen = 1, IsRestricted I ⟺ 1 ∈ I
    have hnum1 : ∀ σ : SymmetricGroup 1, numCycles σ = 1 := by
      intro σ
      unfold numCycles
      have hσ : σ = 1 := Subsingleton.elim σ 1
      simp [hσ]
    have hnum0 : ∀ τ : SymmetricGroup 0, numCycles τ = 0 := by
      intro τ
      unfold numCycles
      have hτ : τ = 1 := Subsingleton.elim τ 1
      simp [hτ]
    have hir0 : ∀ τ : SymmetricGroup 0, IsRestricted I τ := by
      intro τ a
      exact Fin.elim0 a
    have hir1_iff : ∀ σ : SymmetricGroup 1, IsRestricted I σ ↔ 1 ∈ I := by
      intro σ
      constructor
      · intro h
        have hcyc : cycleLen σ = 1 := by rw [cycleLen_eq_one_iff]; exact Subsingleton.elim _ _
        rw [← hcyc, ← cycleLength_eq_cycleLen σ]
        exact h (0 : Fin 1)
      · intro h1 a
        have ha : a = 0 := Subsingleton.elim a (0 : Fin 1)
        rw [ha, cycleLength_eq_cycleLen σ]
        have hcyc : cycleLen σ = 1 := by rw [cycleLen_eq_one_iff]; exact Subsingleton.elim _ _
        rw [hcyc]
        exact h1
    by_cases hℓ : ℓ = 1
    · subst ℓ
      by_cases hI : 1 ∈ I
      · have hL : Fintype.card {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ numCycles σ = 1 ∧ IsRestricted I σ} = 1 := by
          let e : {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ numCycles σ = 1 ∧ IsRestricted I σ} ≃ SymmetricGroup 1 :=
            { toFun := fun ⟨σ, _⟩ => σ
              invFun := fun σ => ⟨σ, by rw [cycleLen_eq_one_iff]; exact Subsingleton.elim _ _, hnum1 σ,
                (hir1_iff σ).2 hI⟩
              left_inv := by intro ⟨σ, _⟩; rfl
              right_inv := by intro σ; rfl }
          rw [Fintype.card_congr e, card_symmetricGroup 1]
          norm_num
        have hresidual : ((Finset.univ : Finset (SymmetricGroup 0)).filter
            (fun τ => numCycles τ = 0 ∧ IsRestricted I τ)) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro τ
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ τ, hnum0 τ, hir0 τ⟩
        rw [hL]
        rw [if_pos hI]
        rw [hresidual, Finset.card_univ, card_symmetricGroup 0, Nat.descFactorial_zero]
        norm_num
      · have hL : Fintype.card {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ numCycles σ = 1 ∧ IsRestricted I σ} = 0 := by
          apply Fintype.card_eq_zero_iff.mpr
          refine ⟨fun ⟨σ, hcyc, _, hir⟩ => ?_⟩
          have h0 : 1 ∈ I := by
            rw [← hcyc, ← cycleLength_eq_cycleLen σ]
            exact hir (0 : Fin 1)
          exact hI h0
        rw [hL]
        rw [if_neg hI]
    · have hL : Fintype.card {σ : SymmetricGroup 1 // cycleLen σ = 1 ∧ numCycles σ = ℓ ∧ IsRestricted I σ} = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        refine ⟨fun ⟨σ, _, hnc, _⟩ => ?_⟩
        have h1 : numCycles σ = 1 := hnum1 σ
        rw [h1] at hnc
        exact hℓ hnc.symm
      rw [hL]
      by_cases hI : 1 ∈ I
      · rw [if_pos hI]
        have hfilter : ((Finset.univ : Finset (SymmetricGroup 0)).filter
            (fun τ => numCycles τ = ℓ - 1 ∧ IsRestricted I τ)) = ∅ := by
          apply Finset.filter_false_of_mem
          intro τ hτ hnc
          have h0 : numCycles τ = 0 := hnum0 τ
          have h' : numCycles τ = ℓ - 1 := hnc.1
          rw [h0] at h'
          have hℓ' : ℓ = 1 := by omega
          exact hℓ hℓ'
        rw [hfilter, Finset.card_empty]
        norm_num [Nat.descFactorial_zero]
      · rw [if_neg hI]
  · -- n ≥ 2
    cases n with
    | zero => omega
    | succ n' =>
      cases d with
      | zero => omega
      | succ d' =>
        haveI : NeZero n' := ⟨by omega⟩
        let e := cycleRemovalEquiv (n := n') (k := d')
        let source := {σ : SymmetricGroup (n' + 1) // cycleLen σ = d' + 1 ∧ numCycles σ = ℓ ∧ IsRestricted I σ}
        let target := {p : (Fin d' ↪ Fin n') × SymmetricGroup (n' - d') //
          numCycles p.2 = ℓ - 1 ∧ IsRestricted I p.2}
        -- if d' + 1 ∈ I, then source ≃ target; else source is empty
        by_cases hI : d' + 1 ∈ I
        · let e' : source ≃ target :=
            { toFun := fun ⟨σ, hcyc, hnc, hir⟩ => ⟨e ⟨σ, hcyc⟩, by
                have hnum : numCycles σ = numCycles (residualFwd σ hcyc) + 1 := numCycles_residualFwd σ hcyc
                have hres : residualFwd σ hcyc = (e ⟨σ, hcyc⟩).2 := rfl
                have hir' : IsRestricted I (residualFwd σ hcyc) :=
                  (IsRestricted_residualFwd σ hcyc I).1 hir |>.2
                constructor
                · rw [← hres]; omega
                · rwa [← hres]⟩
              invFun := fun ⟨p, hnc, hir⟩ => ⟨e.symm p, (e.symm p).2, by
                have hnum : numCycles (e.symm p).1 = numCycles (residualFwd (e.symm p).1 (e.symm p).2) + 1 :=
                  numCycles_residualFwd (e.symm p).1 (e.symm p).2
                have hres : residualFwd (e.symm p).1 (e.symm p).2 = p.2 := congrArg Prod.snd (e.right_inv p)
                have hir' : IsRestricted I ((e.symm p).1) :=
                  (IsRestricted_residualFwd (e.symm p).1 (e.symm p).2 I).2 ⟨hI, by rwa [hres]⟩
                constructor
                · rw [hnum, hres]; omega
                · exact hir'⟩
              left_inv := by
                intro ⟨σ, hcyc, hnc, hir⟩
                apply Subtype.ext
                simpa using congrArg Subtype.val (e.left_inv ⟨σ, hcyc⟩)
              right_inv := by
                intro ⟨p, hnc, hir⟩
                apply Subtype.ext
                dsimp
                exact e.right_inv p }
          rw [Fintype.card_congr e']
          let e'' : target ≃ (Fin d' ↪ Fin n') × {τ : SymmetricGroup (n' - d') // numCycles τ = ℓ - 1 ∧ IsRestricted I τ} :=
            { toFun := fun ⟨p, hnc, hir⟩ => (p.1, ⟨p.2, hnc, hir⟩)
              invFun := fun q => ⟨(q.1, q.2.1), q.2.2.1, q.2.2.2⟩
              left_inv := by intro ⟨p, hnc, hir⟩; rfl
              right_inv := by intro q; rfl }
          rw [Fintype.card_congr e'']
          rw [Fintype.card_prod, Fintype.card_embedding_eq]
          rw [Fintype.card_fin, Fintype.card_fin]
          rw [if_pos hI]
          rw [← Fintype.card_subtype (fun τ : SymmetricGroup (n' + 1 - (d' + 1)) => numCycles τ = ℓ - 1 ∧ IsRestricted I τ)]
          have hsub : (n' + 1 - (d' + 1)) = n' - d' := by omega
          have hcard : Fintype.card {τ : SymmetricGroup (n' + 1 - (d' + 1)) // numCycles τ = ℓ - 1 ∧ IsRestricted I τ} =
              Fintype.card {τ : SymmetricGroup (n' - d') // numCycles τ = ℓ - 1 ∧ IsRestricted I τ} := by
            exact Fintype.card_congr (Equiv.cast
              (congrArg (fun k => {τ : SymmetricGroup k // numCycles τ = ℓ - 1 ∧ IsRestricted I τ}) hsub))
          rw [hcard]
          simp
        · have hsource_empty : IsEmpty source := by
            refine ⟨fun ⟨σ, hcyc, hnc, hir⟩ => ?_⟩
            have h0 : d' + 1 ∈ I := by
              rw [← hcyc, ← cycleLength_eq_cycleLen σ]
              exact hir (0 : Fin (n' + 1))
            exact hI h0
          rw [Fintype.card_eq_zero_iff.mpr hsource_empty]
          rw [if_neg hI]

end Counting

end MostProbableOrder
