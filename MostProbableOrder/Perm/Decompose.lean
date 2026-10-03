import MostProbableOrder.Basic
import MostProbableOrder.Arithmetic.DivisorBounds
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Cycle-through-a-point decomposition (M3)

The recursion **Corollary 2.2** of the paper:

> P(ord(πₙ) = m) = (1/n) Σ_{0 ≤ n' < n, n−n' | m} P(lcm(ord(π_{n'}), n−n') = m).

Its combinatorial backbone is the *cycle removal* decomposition: a permutation
`π ∈ Sₙ` is determined by (i) the cycle of `π` through the point `0`, of length
`d = cycleLen π`, and (ii) the permutation induced on the remaining `n − d`
points. The cycle length is uniform in `[1, n]` (probability `1/n` each), and
`ord(π) = lcm(d, ord(σ))` where `σ` is the residual permutation.

This file establishes the foundational definitions and facts on which the
bijection (and hence Corollary 2.2) is built.
-/

open Finset

namespace MostProbableOrder

section cycleLen

variable {n : ℕ} [NeZero n]

/-- The length of the cycle of `π` through the point `0`: the size of the orbit
of `0` under `π`. It is `1` exactly when `π` fixes `0`, and otherwise equals the
cardinality of the support of `π.cycleOf 0`. -/
noncomputable def cycleLen (π : SymmetricGroup n) : ℕ := by
  classical
  exact if π (0 : Fin n) = 0 then 1 else (π.cycleOf 0).support.card

/-- `cycleLen π = 1` exactly when `π` fixes `0`. -/
lemma cycleLen_eq_one_iff (π : SymmetricGroup n) :
    cycleLen π = 1 ↔ π (0 : Fin n) = 0 := by
  classical
  unfold cycleLen
  by_cases h : π (0 : Fin n) = 0
  · simp [h]
  · have hc : (π.cycleOf 0).support.card ≠ 1 := by
      have hcyc : (π.cycleOf 0).IsCycle := Equiv.Perm.isCycle_cycleOf π h
      have hcard : 2 ≤ (π.cycleOf 0).support.card := hcyc.two_le_card_support
      omega
    simp [h, hc]

/-- The cycle through `0` always has positive length. -/
lemma cycleLen_pos (π : SymmetricGroup n) : 0 < cycleLen π := by
  classical
  unfold cycleLen
  by_cases h : π (0 : Fin n) = 0 <;> simp [h]

/-- The cycle through `0` has length at most `n`. -/
lemma cycleLen_le (π : SymmetricGroup n) : cycleLen π ≤ n := by
  classical
  unfold cycleLen
  by_cases h : π (0 : Fin n) = 0
  · simp [h]
    exact Nat.succ_le_of_lt (NeZero.pos n)
  · have hle : (π.cycleOf 0).support.card ≤ Fintype.card (Fin n) := by
      have hsub : (π.cycleOf 0).support ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
      calc (π.cycleOf 0).support.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card hsub
        _ = Fintype.card (Fin n) := by rw [Finset.card_univ]
    simpa [h] using hle

/-- The order of the cycle of `π` through `0` is exactly its length. -/
lemma orderOf_cycleOf_eq_cycleLen (π : SymmetricGroup n) :
    orderOf (π.cycleOf 0) = cycleLen π := by
  classical
  unfold cycleLen
  by_cases h : π (0 : Fin n) = 0
  · have h1 : π.cycleOf 0 = 1 := by simpa using h
    simp [h, h1]
  · have hcyc : (π.cycleOf 0).IsCycle := Equiv.Perm.isCycle_cycleOf π h
    simp [h, hcyc.orderOf]

end cycleLen

/-! ### Cycle length through an arbitrary point -/

section cycleLenAt

variable {n : ℕ}

/-- The length of the cycle of `π` through an arbitrary point `a`. -/
noncomputable def cycleLenAt (π : SymmetricGroup n) (a : Fin n) : ℕ := by
  classical
  exact if π a = a then 1 else (π.cycleOf a).support.card

/-- `cycleLenAt π a = 1` exactly when `π` fixes `a`. -/
lemma cycleLenAt_eq_one_iff (π : SymmetricGroup n) (a : Fin n) :
    cycleLenAt π a = 1 ↔ π a = a := by
  classical
  unfold cycleLenAt
  by_cases h : π a = a
  · simp [h]
  · have hc : (π.cycleOf a).support.card ≠ 1 := by
      have hcyc : (π.cycleOf a).IsCycle := Equiv.Perm.isCycle_cycleOf π h
      have hcard : 2 ≤ (π.cycleOf a).support.card := hcyc.two_le_card_support
      omega
    simp [h, hc]

/-- The order of the cycle of `π` through `a` is exactly its length. -/
lemma orderOf_cycleOf_eq_cycleLenAt (π : SymmetricGroup n) (a : Fin n) :
    orderOf (π.cycleOf a) = cycleLenAt π a := by
  classical
  unfold cycleLenAt
  by_cases h : π a = a
  · have h1 : π.cycleOf a = 1 := by simpa using h
    simp [h, h1]
  · have hcyc : (π.cycleOf a).IsCycle := Equiv.Perm.isCycle_cycleOf π h
    simp [h, hcyc.orderOf]

/-- `cycleLenAt` is always positive. -/
lemma cycleLenAt_pos (σ : SymmetricGroup n) (a : Fin n) : 0 < cycleLenAt σ a := by
  classical
  unfold cycleLenAt
  by_cases h : σ a = a <;> simp [h]

end cycleLenAt

/-! ### Feller insertion primitives

The two maps inserting the fixed point `0` into a permutation of `Fin n`,
producing a permutation of `Fin (n+1)`: as a new fixed point (`insertNone`), or
splitting an arc `k → σ k` (`insertArc`). Together they realise the Feller
"insertion" step underlying Corollary 2.2. -/

section insert

variable {n : ℕ}

/-- Forward map: insert `0` into the arc `k → σ k`. -/
def insertArcToFun [NeZero n] (k : Fin n) (σ : SymmetricGroup n) (x : Fin (n + 1)) : Fin (n + 1) :=
  if x = 0 then (σ k).succ
  else
    let i := (0 : Fin n).predAbove x
    if i = k then 0 else (σ i).succ

/-- Inverse map of `insertArcToFun`. -/
def insertArcInvFun [NeZero n] (k : Fin n) (σ : SymmetricGroup n) (y : Fin (n + 1)) : Fin (n + 1) :=
  if y = 0 then k.succ
  else
    let j := (0 : Fin n).predAbove y
    if j = σ k then 0 else (σ.symm j).succ

lemma insertArc_left_inv [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    Function.LeftInverse (insertArcInvFun k σ) (insertArcToFun k σ) := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have hne : (σ k).succ ≠ 0 := Fin.succ_ne_zero _
    simp [insertArcToFun, insertArcInvFun, hne]
  · obtain ⟨i, hxsucc⟩ : ∃ i : Fin n, x = i.succ := by
      exact ⟨(0 : Fin n).predAbove x, (Fin.succ_predAbove_zero hx).symm⟩
    rw [hxsucc]
    by_cases hik : i = k
    · subst hik
      simp [insertArcToFun, insertArcInvFun]
    · have hσne : σ i ≠ σ k := by
        intro h
        exact hik (σ.injective h)
      simp [insertArcToFun, insertArcInvFun, hik, hσne]

lemma insertArc_right_inv [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    Function.RightInverse (insertArcInvFun k σ) (insertArcToFun k σ) := by
  intro y
  by_cases hy : y = 0
  · subst y
    simp [insertArcToFun, insertArcInvFun]
  · obtain ⟨j, hysucc⟩ : ∃ j : Fin n, y = j.succ := by
      exact ⟨(0 : Fin n).predAbove y, (Fin.succ_predAbove_zero hy).symm⟩
    rw [hysucc]
    by_cases hjk : j = σ k
    · subst hjk
      simp [insertArcToFun, insertArcInvFun]
    · have hσsymm : σ.symm j ≠ k := by
        intro h
        apply hjk
        have hσ : σ (σ.symm j) = σ k := by rw [h]
        simpa [Equiv.apply_symm_apply] using hσ
      simp [insertArcToFun, insertArcInvFun, hjk, hσsymm]

/-- Insert the fixed point `0` into the arc `k → σ k`; a permutation of `Fin (n+1)`. -/
def insertArc [NeZero n] (k : Fin n) (σ : SymmetricGroup n) : SymmetricGroup (n + 1) :=
  { toFun := insertArcToFun k σ,
    invFun := insertArcInvFun k σ,
    left_inv := insertArc_left_inv k σ,
    right_inv := insertArc_right_inv k σ }

/-- `insertArc k σ` sends `0` to the successor of `σ k`. -/
@[simp] lemma insertArc_apply_zero [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    (insertArc k σ) 0 = (σ k).succ := by
  simp [insertArc, insertArcToFun]

/-- `insertArc k σ` sends `k.succ` to `0` (the arc `k → σ k` is split). -/
@[simp] lemma insertArc_apply_succ_k [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    (insertArc k σ) k.succ = 0 := by
  simp [insertArc, insertArcToFun]

/-- `insertArc k σ` sends `i.succ` to `(σ i).succ` for `i ≠ k`. -/
lemma insertArc_apply_succ [NeZero n] (k : Fin n) (σ : SymmetricGroup n) (i : Fin n) (hi : i ≠ k) :
    (insertArc k σ) i.succ = (σ i).succ := by
  simp [insertArc, insertArcToFun, hi]

/-- Forward map: insert `0` as a new fixed point. -/
def insertNoneToFun [NeZero n] (σ : SymmetricGroup n) (x : Fin (n + 1)) : Fin (n + 1) :=
  if x = 0 then 0 else (σ ((0 : Fin n).predAbove x)).succ

/-- Inverse map of `insertNoneToFun`. -/
def insertNoneInvFun [NeZero n] (σ : SymmetricGroup n) (y : Fin (n + 1)) : Fin (n + 1) :=
  if y = 0 then 0 else (σ.symm ((0 : Fin n).predAbove y)).succ

lemma insertNone_left_inv [NeZero n] (σ : SymmetricGroup n) :
    Function.LeftInverse (insertNoneInvFun σ) (insertNoneToFun σ) := by
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [insertNoneToFun, insertNoneInvFun]
  · obtain ⟨i, hxsucc⟩ : ∃ i : Fin n, x = i.succ := by
      exact ⟨(0 : Fin n).predAbove x, (Fin.succ_predAbove_zero hx).symm⟩
    rw [hxsucc]
    simp [insertNoneToFun, insertNoneInvFun]

lemma insertNone_right_inv [NeZero n] (σ : SymmetricGroup n) :
    Function.RightInverse (insertNoneInvFun σ) (insertNoneToFun σ) := by
  intro y
  by_cases hy : y = 0
  · subst y
    simp [insertNoneToFun, insertNoneInvFun]
  · obtain ⟨j, hysucc⟩ : ∃ j : Fin n, y = j.succ := by
      exact ⟨(0 : Fin n).predAbove y, (Fin.succ_predAbove_zero hy).symm⟩
    rw [hysucc]
    simp [insertNoneToFun, insertNoneInvFun]

/-- Insert the fixed point `0` as a new fixed point; a permutation of `Fin (n+1)`. -/
def insertNone [NeZero n] (σ : SymmetricGroup n) : SymmetricGroup (n + 1) :=
  { toFun := insertNoneToFun σ,
    invFun := insertNoneInvFun σ,
    left_inv := insertNone_left_inv σ,
    right_inv := insertNone_right_inv σ }

/-- `insertNone σ` fixes `0`. -/
@[simp] lemma insertNone_apply_zero [NeZero n] (σ : SymmetricGroup n) :
    (insertNone σ) 0 = 0 := by
  simp [insertNone, insertNoneToFun]

/-- `insertNone σ` sends `i.succ` to `(σ i).succ`. -/
@[simp] lemma insertNone_apply_succ [NeZero n] (σ : SymmetricGroup n) (i : Fin n) :
    (insertNone σ) i.succ = (σ i).succ := by
  simp [insertNone, insertNoneToFun]

end insert

/-! ### Feller bijection (delete/insert a point)

The map deleting the point `0` and merging its two arcs, together with its
inverses `insertNone` and `insertArc`, realises the classical Feller insertion
bijection `Perm (Fin (n+1)) ≃ Perm (Fin n) ⊕ (Fin n × Perm (Fin n))`. -/

section feller

variable {n : ℕ}

/-- Forward map: delete `0` and merge its incoming/outgoing arcs. -/
def deleteZeroToFun [NeZero n] (π : SymmetricGroup (n + 1)) (i : Fin n) : Fin n :=
  (0 : Fin n).predAbove (if π (i.succ) = 0 then π 0 else π (i.succ))

/-- Inverse map of `deleteZeroToFun`. -/
def deleteZeroInvFun [NeZero n] (π : SymmetricGroup (n + 1)) (j : Fin n) : Fin n :=
  if j.succ = π 0 then (0 : Fin n).predAbove (π.symm 0)
  else (0 : Fin n).predAbove (π.symm (j.succ))

lemma deleteZero_left_inv [NeZero n] (π : SymmetricGroup (n + 1)) :
    Function.LeftInverse (deleteZeroInvFun π) (deleteZeroToFun π) := by
  intro i
  unfold deleteZeroToFun deleteZeroInvFun
  by_cases h : π (i.succ) = 0
  · have hπ0_ne : π 0 ≠ 0 := by
      intro h0
      have hπ : π (i.succ) = π 0 := by rw [h, h0]
      exact Fin.succ_ne_zero _ (π.injective hπ)
    have hsymm : π.symm 0 = i.succ := by
      have h1 : π.symm (π (i.succ)) = i.succ := Equiv.symm_apply_apply π (i.succ)
      rwa [h] at h1
    have hcond : ((0 : Fin n).predAbove (π 0)).succ = π 0 := Fin.succ_predAbove_zero hπ0_ne
    simp [h, hcond, hsymm]
  · have hπi_neπ0 : π (i.succ) ≠ π 0 := by
      intro hh
      exact Fin.succ_ne_zero _ (π.injective hh)
    have hsymm : π.symm (π (i.succ)) = i.succ := Equiv.symm_apply_apply π (i.succ)
    simp [h, hπi_neπ0, hsymm]

lemma deleteZero_right_inv [NeZero n] (π : SymmetricGroup (n + 1)) :
    Function.RightInverse (deleteZeroInvFun π) (deleteZeroToFun π) := by
  intro j
  unfold deleteZeroToFun deleteZeroInvFun
  by_cases h : j.succ = π 0
  · have hπsymm0_ne : π.symm 0 ≠ 0 := by
      intro h0
      have hπ : π (π.symm 0) = π 0 := by rw [h0]
      have h00 : 0 = π 0 := by simpa [Equiv.apply_symm_apply] using hπ
      rw [← h] at h00
      exact Fin.succ_ne_zero _ h00.symm
    have hsucc : π.symm 0 = ((0 : Fin n).predAbove (π.symm 0)).succ := by
      exact (Fin.succ_predAbove_zero hπsymm0_ne).symm
    have hπ : π ((0 : Fin n).predAbove (π.symm 0)).succ = 0 := by
      rw [← hsucc]
      exact Equiv.apply_symm_apply π 0
    have hmain : (0 : Fin n).predAbove (π 0) = j := by
      rw [← h]
      simp
    simp [h, hπ, hmain]
  · have hπsymm_ne0 : π.symm (j.succ) ≠ 0 := by
      intro h0
      have hπ : π (π.symm (j.succ)) = π 0 := by rw [h0]
      have hjp : j.succ = π 0 := by simpa [Equiv.apply_symm_apply] using hπ
      exact h hjp
    have hsucc : π.symm (j.succ) = ((0 : Fin n).predAbove (π.symm (j.succ))).succ := by
      exact (Fin.succ_predAbove_zero hπsymm_ne0).symm
    have hπ : π ((0 : Fin n).predAbove (π.symm (j.succ))).succ = j.succ := by
      rw [← hsucc]
      exact Equiv.apply_symm_apply π (j.succ)
    have hmain : (0 : Fin n).predAbove (j.succ) = j := Fin.predAbove_zero_succ
    simp [h, hπ, hmain]

/-- Delete `0` and merge: the residual permutation of `Fin n`. -/
def deleteZero [NeZero n] (π : SymmetricGroup (n + 1)) : SymmetricGroup n :=
  { toFun := deleteZeroToFun π,
    invFun := deleteZeroInvFun π,
    left_inv := deleteZero_left_inv π,
    right_inv := deleteZero_right_inv π }

/-- `deleteZero` inverts `insertNone`. -/
lemma deleteZero_insertNone [NeZero n] (σ : SymmetricGroup n) :
    deleteZero (insertNone σ) = σ := by
  ext i
  simp [deleteZero, deleteZeroToFun, Fin.succ_ne_zero]

/-- `deleteZero` inverts `insertArc`. -/
lemma deleteZero_insertArc [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    deleteZero (insertArc k σ) = σ := by
  ext i
  by_cases hik : i = k
  · subst hik
    simp [deleteZero, deleteZeroToFun]
  · simp [deleteZero, deleteZeroToFun, insertArc_apply_succ k σ i hik, Fin.succ_ne_zero]

/-- `(insertArc k σ) 0 ≠ 0`. -/
lemma insertArc_zero_ne [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    (insertArc k σ) 0 ≠ 0 := by
  rw [insertArc_apply_zero]
  exact Fin.succ_ne_zero _

/-- `(insertArc k σ).symm 0 = k.succ`. -/
lemma insertArc_symm_zero [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    (insertArc k σ).symm 0 = k.succ := by
  apply (insertArc k σ).injective
  rw [Equiv.apply_symm_apply, insertArc_apply_succ_k]

/-- `insertNone` inverts `deleteZero` (when `π` fixes `0`). -/
lemma insertNone_deleteZero [NeZero n] (π : SymmetricGroup (n + 1)) (h : π 0 = 0) :
    insertNone (deleteZero π) = π := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp [insertNone, insertNoneToFun, h]
  · obtain ⟨i, hxsucc⟩ : ∃ i : Fin n, x = i.succ := by
      exact ⟨(0 : Fin n).predAbove x, (Fin.succ_predAbove_zero hx).symm⟩
    rw [hxsucc]
    have hπi_ne0 : π (i.succ) ≠ 0 := by
      intro h0
      have hπ : π (i.succ) = π 0 := by rw [h0, h]
      exact Fin.succ_ne_zero _ (π.injective hπ)
    simp [insertNone, insertNoneToFun, deleteZero, deleteZeroToFun, hπi_ne0]

/-- `insertArc` inverts `deleteZero` (when `π` moves `0`). -/
lemma insertArc_deleteZero [NeZero n] (π : SymmetricGroup (n + 1)) (h : π 0 ≠ 0) :
    insertArc ((0 : Fin n).predAbove (π.symm 0)) (deleteZero π) = π := by
  let k : Fin n := (0 : Fin n).predAbove (π.symm 0)
  have hsymm0_ne : π.symm 0 ≠ 0 := by
    intro h0
    have hπ : 0 = π 0 := by
      calc 0 = π (π.symm 0) := (Equiv.apply_symm_apply π 0).symm
        _ = π 0 := by rw [h0]
    exact h hπ.symm
  have hk_succ : k.succ = π.symm 0 := by
    dsimp [k]
    exact Fin.succ_predAbove_zero hsymm0_ne
  have hπk : π k.succ = 0 := by
    rw [hk_succ]
    exact Equiv.apply_symm_apply π 0
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [insertArc_apply_zero]
    have hdz : deleteZero π k = (0 : Fin n).predAbove (π 0) := by
      simp [deleteZero, deleteZeroToFun, hπk]
    rw [hdz]
    exact congrArg Fin.val (Fin.succ_predAbove_zero h)
  · obtain ⟨i, hxsucc⟩ : ∃ i : Fin n, x = i.succ := by
      exact ⟨(0 : Fin n).predAbove x, (Fin.succ_predAbove_zero hx).symm⟩
    rw [hxsucc]
    by_cases hik : i = k
    · subst hik
      rw [insertArc_apply_succ_k]
      exact congrArg Fin.val hπk.symm
    · rw [insertArc_apply_succ k (deleteZero π) i hik]
      have hπi_ne0 : π (i.succ) ≠ 0 := by
        intro h0
        have his : i.succ = π.symm 0 := by
          exact π.injective (by rw [h0, Equiv.apply_symm_apply])
        have hik' : i = k := by
          have : i.succ = k.succ := by rw [his, hk_succ]
          exact Fin.succ_injective n this
        exact hik hik'
      have hdz : deleteZero π i = (0 : Fin n).predAbove (π (i.succ)) := by
        simp [deleteZero, deleteZeroToFun, hπi_ne0]
      rw [hdz]
      exact congrArg Fin.val (Fin.succ_predAbove_zero hπi_ne0)

/-- The Feller insertion bijection: a permutation of `Fin (n+1)` is either a
permutation of `Fin n` with `0` added as a fixed point, or a permutation of
`Fin n` with `0` inserted into one of its arcs. -/
def fellerEquiv [NeZero n] :
    SymmetricGroup (n + 1) ≃ SymmetricGroup n ⊕ (Fin n × SymmetricGroup n) :=
  { toFun := fun π => if h : π 0 = 0 then Sum.inl (deleteZero π)
        else Sum.inr (⟨(0 : Fin n).predAbove (π.symm 0), deleteZero π⟩),
    invFun := fun x => Sum.elim insertNone (fun p : Fin n × SymmetricGroup n => insertArc p.1 p.2) x,
    left_inv := by
      intro π
      by_cases h : π 0 = 0
      · simp [h, insertNone_deleteZero π h]
      · simp [h, insertArc_deleteZero π h]
    right_inv := by
      intro x
      cases x with
      | inl σ => simp [deleteZero_insertNone σ]
      | inr p =>
          have hsymm : (0 : Fin n).predAbove ((insertArc p.1 p.2).symm 0) = p.1 := by
            rw [insertArc_symm_zero p.1 p.2]
            simp
          have hdz : deleteZero (insertArc p.1 p.2) = p.2 := deleteZero_insertArc p.1 p.2
          simp [hsymm, hdz] }

/-- `insertNone σ` has a cycle of length `1` through `0` (a fixed point). -/
lemma cycleLen_insertNone [NeZero n] (σ : SymmetricGroup n) :
    cycleLen (insertNone σ) = 1 := by
  rw [cycleLen_eq_one_iff]
  simp

/-- For `t` with `0 < t < cycleLenAt σ k`, the point `(σ ^ t) k` is not fixed by `σ`. -/
lemma pow_apply_ne_of_lt_cycleLenAt [NeZero n] (σ : SymmetricGroup n) (k : Fin n) :
    ∀ t, 0 < t → t < cycleLenAt σ k → (σ ^ t) k ≠ k := by
  intro t ht0 htL h
  let L := cycleLenAt σ k
  have hL : orderOf (σ.cycleOf k) = L := by
    dsimp [L]
    exact orderOf_cycleOf_eq_cycleLenAt σ k
  have hσk_eq_iff : (σ ^ t) k = k ↔ (σ.cycleOf k)^t = 1 := by
    constructor
    · intro h'
      by_cases hk : σ k = k
      · have : σ.cycleOf k = 1 := by simpa using hk
        simp [this]
      · have hcyc : (σ.cycleOf k).IsCycle := Equiv.Perm.isCycle_cycleOf σ hk
        have hx : (σ.cycleOf k) k ≠ k := by simpa using hk
        exact (hcyc.pow_eq_one_iff' hx).2 (by simpa [Equiv.Perm.cycleOf_pow_apply_self] using h')
    · intro h'
      have h'' : ((σ.cycleOf k)^t) k = k := by simp [h']
      simpa [Equiv.Perm.cycleOf_pow_apply_self] using h''
  have hcyc : (σ.cycleOf k)^t = 1 := hσk_eq_iff.1 h
  have hdvd : L ∣ t := by
    rw [← hL]
    exact (orderOf_dvd_iff_pow_eq_one).2 hcyc
  have hle : L ≤ t := Nat.le_of_dvd ht0 hdvd
  omega

/-- The cycle through `0` of `insertArc k σ` has length `cycleLenAt σ k + 1`. -/
lemma cycleLen_insertArc [NeZero n] (k : Fin n) (σ : SymmetricGroup n) :
    cycleLen (insertArc k σ) = cycleLenAt σ k + 1 := by
  let π : SymmetricGroup (n + 1) := insertArc k σ
  let L := cycleLenAt σ k
  have hL : orderOf (σ.cycleOf k) = L := by
    dsimp [L]
    exact orderOf_cycleOf_eq_cycleLenAt σ k
  have hLpos : 1 ≤ L := cycleLenAt_pos σ k
  -- π^t 0 = (σ^t k).succ for 1 ≤ t ≤ L
  have hpow_succ : ∀ t, 1 ≤ t → t ≤ L → (π ^ t) 0 = ((σ ^ t) k).succ := by
    intro t ht1 htL
    induction t with
    | zero => omega
    | succ t ih =>
        by_cases ht0 : t = 0
        · subst t
          simp [π, insertArc_apply_zero, pow_one]
        · have ht1' : 1 ≤ t := by omega
          have htL' : t ≤ L := by omega
          have hσt_ne : (σ ^ t) k ≠ k := pow_apply_ne_of_lt_cycleLenAt σ k t (by omega) (by omega)
          calc (π ^ (t + 1)) 0 = π ((π ^ t) 0) := by simp [pow_succ']
            _ = π (((σ ^ t) k).succ) := by rw [ih ht1' htL']
            _ = (σ ((σ ^ t) k)).succ := insertArc_apply_succ k σ ((σ ^ t) k) hσt_ne
            _ = ((σ ^ (t + 1)) k).succ := by simp [pow_succ']
  -- (σ ^ L) k = k
  have hσLk : (σ ^ L) k = k := by
    have h1 : (σ.cycleOf k)^L = 1 := by
      rw [← hL]
      exact pow_orderOf_eq_one (σ.cycleOf k)
    have h2 : ((σ.cycleOf k)^L) k = k := by simp [h1]
    simpa [Equiv.Perm.cycleOf_pow_apply_self] using h2
  -- π^(L+1) 0 = 0
  have hpow_zero : (π ^ (L + 1)) 0 = 0 := by
    have hpowL : (π ^ L) 0 = ((σ ^ L) k).succ := hpow_succ L hLpos le_rfl
    calc (π ^ (L + 1)) 0 = π ((π ^ L) 0) := by simp [pow_succ']
      _ = π (((σ ^ L) k).succ) := by rw [hpowL]
      _ = π k.succ := by rw [hσLk]
      _ = 0 := by simp [π, insertArc_apply_succ_k]
  -- orderOf (π.cycleOf 0) = L + 1
  have horder : orderOf (π.cycleOf 0) = L + 1 := by
    apply le_antisymm
    · apply orderOf_le_of_pow_eq_one (by omega : 0 < L + 1)
      have hcyc : (π.cycleOf 0).IsCycle := by
        apply Equiv.Perm.isCycle_cycleOf
        exact insertArc_zero_ne k σ
      have hx : (π.cycleOf 0) 0 ≠ 0 := by
        rw [Equiv.Perm.cycleOf_apply_self]
        dsimp [π]
        exact insertArc_zero_ne k σ
      exact (hcyc.pow_eq_one_iff' hx).2 (by simpa [Equiv.Perm.cycleOf_pow_apply_self] using hpow_zero)
    · by_contra h
      have hle : orderOf (π.cycleOf 0) ≤ L := by omega
      have hpos : 0 < orderOf (π.cycleOf 0) := orderOf_pos (π.cycleOf 0)
      have hpow1 : (π.cycleOf 0)^(orderOf (π.cycleOf 0)) = 1 := pow_orderOf_eq_one _
      have hπ0 : (π ^ (orderOf (π.cycleOf 0))) 0 = 0 := by
        calc (π ^ (orderOf (π.cycleOf 0))) 0
            = ((π.cycleOf 0)^(orderOf (π.cycleOf 0))) 0 :=
                (Equiv.Perm.cycleOf_pow_apply_self π 0 (orderOf (π.cycleOf 0))).symm
          _ = 0 := by simp [hpow1]
      have hpow' := hpow_succ (orderOf (π.cycleOf 0)) hpos hle
      rw [hpow'] at hπ0
      exact Fin.succ_ne_zero _ hπ0
  dsimp [L] at horder ⊢
  exact (orderOf_cycleOf_eq_cycleLen π).symm.trans horder

end feller

/-! ### Order of `insertNone` and the cycle-removal decomposition

These lemmas prepare Corollary 2.2: deleting the whole cycle of `π` through `0`
leaves a permutation of the remaining `n − cycleLen π` points, and the order of
`π` factors as the lcm of the cycle length and the order of the residual. -/

section orderInsertNone

variable {n : ℕ}

/-- Iterating `insertNone σ` on a `succ` coordinate tracks `σ`. -/
lemma insertNone_pow_succ [NeZero n] (σ : SymmetricGroup n) (i : Fin n) :
    ∀ k, (insertNone σ ^ k) i.succ = ((σ ^ k) i).succ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc (insertNone σ ^ (k + 1)) i.succ
          = (insertNone σ) ((insertNone σ ^ k) i.succ) := by simp [pow_succ']
        _ = (insertNone σ) (((σ ^ k) i).succ) := by rw [ih]
        _ = ((σ ^ (k + 1)) i).succ := by simp [insertNone_apply_succ, pow_succ']

/-- `insertNone σ` fixes `0` under all powers. -/
lemma insertNone_pow_zero [NeZero n] (σ : SymmetricGroup n) :
    ∀ k, (insertNone σ ^ k) 0 = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc (insertNone σ ^ (k + 1)) 0 = (insertNone σ) ((insertNone σ ^ k) 0) := by simp [pow_succ']
        _ = (insertNone σ) 0 := by rw [ih]
        _ = 0 := by simp

/-- `insertNone` preserves the order of a permutation. -/
lemma orderOf_insertNone [NeZero n] (σ : SymmetricGroup n) :
    orderOf (insertNone σ) = orderOf σ := by
  apply le_antisymm
  · apply orderOf_le_of_pow_eq_one (orderOf_pos σ)
    ext x
    by_cases hx : x = 0
    · subst hx
      simpa using insertNone_pow_zero σ (orderOf σ)
    · obtain ⟨i, hi⟩ : ∃ i : Fin n, x = i.succ := by
        exact ⟨(0 : Fin n).predAbove x, (Fin.succ_predAbove_zero hx).symm⟩
      rw [hi]
      rw [insertNone_pow_succ]
      simp
  · apply orderOf_le_of_pow_eq_one (orderOf_pos (insertNone σ))
    ext i
    have h := congrArg (fun f : SymmetricGroup (n + 1) => f i.succ)
      (pow_orderOf_eq_one (insertNone σ))
    have h' : ((σ ^ orderOf (insertNone σ)) i).succ = i.succ := by
      rw [← insertNone_pow_succ]
      exact h
    exact congrArg Fin.val (Fin.succ_injective n h')

end orderInsertNone

/-! ### Cycle-removal decomposition (foundation for Corollary 2.2) -/

section cycleRemoval

variable {n : ℕ} [NeZero n]

/-- `cycleLen π` equals the size of the orbit of `0` under `π` (the cycle through `0`). -/
lemma cycleLen_eq_card_sameCycle (π : SymmetricGroup n) :
    cycleLen π = Fintype.card {x : Fin n // Equiv.Perm.SameCycle π (0 : Fin n) x} := by
  classical
  rw [Fintype.card_subtype]
  unfold cycleLen
  by_cases h : π (0 : Fin n) = 0
  · have hfilter : (Finset.univ : Finset (Fin n)).filter
        (fun x => Equiv.Perm.SameCycle π (0 : Fin n) x) = {(0 : Fin n)} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hsc
        rcases hsc with ⟨i, hi⟩
        have h0 : (π ^ i) (0 : Fin n) = 0 :=
          Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (f := π) (x := (0 : Fin n)) h i
        rw [h0] at hi
        exact hi.symm
      · intro hx
        rw [hx]
    simp [h, hfilter]
  · have hfilter : (Finset.univ : Finset (Fin n)).filter
        (fun x => Equiv.Perm.SameCycle π (0 : Fin n) x) = (π.cycleOf 0).support := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      exact (Equiv.Perm.mem_support_cycleOf_iff' (f := π) (x := (0 : Fin n)) h).symm
    simp [h, hfilter]

/-- The complement of the orbit of `0` has cardinality `n - cycleLen π`. -/
lemma card_complement_sameCycle (π : SymmetricGroup n) :
    Fintype.card {x : Fin n // ¬ Equiv.Perm.SameCycle π (0 : Fin n) x} = n - cycleLen π := by
  rw [Fintype.card_subtype_compl, cycleLen_eq_card_sameCycle, Fintype.card_fin]

/-- The cycle through `0` as a permutation of the orbit of `0`. -/
noncomputable def cyclePerm (π : SymmetricGroup n) :
    Equiv.Perm {x : Fin n // Equiv.Perm.SameCycle π (0 : Fin n) x} :=
  Equiv.Perm.subtypePerm π
    (fun x => (Equiv.Perm.sameCycle_apply_right (f := π) (x := (0 : Fin n)) (y := x)))

/-- The residual permutation on the complement of the orbit of `0`. -/
noncomputable def residualSubtype (π : SymmetricGroup n) :
    Equiv.Perm {x : Fin n // ¬ Equiv.Perm.SameCycle π (0 : Fin n) x} :=
  Equiv.Perm.subtypePerm π
    (fun x => (Equiv.Perm.sameCycle_apply_right (f := π) (x := (0 : Fin n)) (y := x)).not)

/-- The residual permutation, as a permutation of `Fin (n - cycleLen π)`. -/
noncomputable def residual (π : SymmetricGroup n) : SymmetricGroup (n - cycleLen π) :=
  Equiv.permCongr (Fintype.equivFinOfCardEq (card_complement_sameCycle π)) (residualSubtype π)

end cycleRemoval

/-! ### Order decomposition `orderOf π = lcm (cycleLen π) (orderOf (residual π))`

This is the combinatorial heart of Corollary 2.2: `π` factors as the product of
its cycle through `0` (a cycle of length `cycleLen π`) and the residual
permutation on the remaining points, and the two are disjoint. -/

section cycleRemovalOrder

variable {n : ℕ} [NeZero n]

/-- `π` is the product of its cycle through `0` and its residual. -/
lemma decompose_mul (π : SymmetricGroup n) :
    π = Equiv.Perm.ofSubtype (cyclePerm π) * Equiv.Perm.ofSubtype (residualSubtype π) := by
  ext x
  change (π x).val = ((Equiv.Perm.ofSubtype (cyclePerm π))
    ((Equiv.Perm.ofSubtype (residualSubtype π)) x)).val
  by_cases hx : Equiv.Perm.SameCycle π (0 : Fin n) x
  · have hτ : Equiv.Perm.ofSubtype (residualSubtype π) x = x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem (residualSubtype π) (not_not.mpr hx)
    rw [hτ]
    have hρ : Equiv.Perm.ofSubtype (cyclePerm π) x = π x :=
      Equiv.Perm.ofSubtype_apply_of_mem (cyclePerm π) hx
    rw [hρ]
  · have hπx : ¬ Equiv.Perm.SameCycle π (0 : Fin n) (π x) := by
      intro h
      exact hx ((Equiv.Perm.sameCycle_apply_right (f := π) (x := (0 : Fin n)) (y := x)).mp h)
    have hτ : Equiv.Perm.ofSubtype (residualSubtype π) x = π x :=
      Equiv.Perm.ofSubtype_apply_of_mem (residualSubtype π) hx
    rw [hτ]
    have hρ : Equiv.Perm.ofSubtype (cyclePerm π) (π x) = π x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem (cyclePerm π) hπx
    rw [hρ]

/-- The cycle through `0` and the residual are disjoint permutations. -/
lemma disjoint_cyclePerm_residual (π : SymmetricGroup n) :
    Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype (cyclePerm π))
      (Equiv.Perm.ofSubtype (residualSubtype π)) := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
  intro x hx1
  rw [Equiv.Perm.mem_support_ofSubtype] at hx1
  rcases hx1 with ⟨hsc, _⟩
  rw [Equiv.Perm.mem_support_ofSubtype]
  intro h
  rcases h with ⟨hnot, _⟩
  exact hnot hsc

/-- `ofSubtype (cyclePerm π)` is exactly `π.cycleOf 0`. -/
lemma ofSubtype_cyclePerm (π : SymmetricGroup n) :
    Equiv.Perm.ofSubtype (cyclePerm π) = π.cycleOf 0 := by
  rfl

/-- The order of the cycle through `0` is `cycleLen π`. -/
lemma orderOf_ofSubtype_cyclePerm (π : SymmetricGroup n) :
    orderOf (Equiv.Perm.ofSubtype (cyclePerm π)) = cycleLen π := by
  rw [ofSubtype_cyclePerm]
  exact orderOf_cycleOf_eq_cycleLen π

/-- The order of `residual π` equals that of `residualSubtype π`. -/
lemma orderOf_residual (π : SymmetricGroup n) :
    orderOf (residual π) = orderOf (residualSubtype π) := by
  unfold residual
  let e := Fintype.equivFinOfCardEq (card_complement_sameCycle π)
  change orderOf (Equiv.permCongrHom e (residualSubtype π)) = orderOf (residualSubtype π)
  exact MulEquiv.orderOf_eq (Equiv.permCongrHom e) (residualSubtype π)

/-- `ofSubtype (residualSubtype π)` has the same order as `residual π`. -/
lemma orderOf_ofSubtype_residual (π : SymmetricGroup n) :
    orderOf (Equiv.Perm.ofSubtype (residualSubtype π)) = orderOf (residual π) := by
  have h := orderOf_injective Equiv.Perm.ofSubtype Equiv.Perm.ofSubtype_injective (residualSubtype π)
  rw [h]
  exact (orderOf_residual π).symm

/-- **Order decomposition**: `orderOf π = lcm (cycleLen π) (orderOf (residual π))`. -/
theorem orderOf_eq_lcm_cycleLen_residual (π : SymmetricGroup n) :
    orderOf π = Nat.lcm (cycleLen π) (orderOf (residual π)) := by
  have hord := congrArg orderOf (decompose_mul π)
  rw [hord]
  rw [(disjoint_cyclePerm_residual π).orderOf]
  rw [orderOf_ofSubtype_cyclePerm, orderOf_ofSubtype_residual]

end cycleRemovalOrder

/-! ### Cycle-through-zero from an ordered tuple (scaffolding for MP-006)

Given an embedding `t : Fin k ↪ Fin n` (an ordered `k`-tuple of distinct elements
of `Fin n`), we build the cycle through `0` in `Fin (n+1)` that walks
`0 → (t 0).succ → (t 1).succ → … → (t (k-1)).succ → 0`. This is the inverse of
the tuple map `π ↦ fun i => predAbove 0 (π^{i+1} 0)` used in the bijection
`{π | cycleLen π = k+1} ≃ (Fin k ↪ Fin n) × S_{n-k}`. -/

section cycleThroughZero

variable {n : ℕ}

/-- The orbit `{0} ∪ {(t i).succ : i}` indexed by `Fin (k+1)` via `0 ↦ 0`, `i.succ ↦ (t i).succ`. -/
noncomputable def orbitEquiv {k : ℕ} (t : Fin k ↪ Fin n) :
    Fin (k + 1) ≃ {x : Fin (n + 1) // x = 0 ∨ ∃ i : Fin k, x = (t i).succ} :=
  (finSuccEquiv k).trans
    (Equiv.ofBijective (fun o : Option (Fin k) =>
      match o with
      | none => ⟨(0 : Fin (n + 1)), Or.inl rfl⟩
      | some i => ⟨(t i).succ, Or.inr ⟨i, rfl⟩⟩) (by
      constructor
      · intro o o' h
        cases o with
        | none =>
            cases o' with
            | none => rfl
            | some i' =>
                have : (0 : Fin (n + 1)) = (t i').succ := congrArg Subtype.val h
                exact (Fin.succ_ne_zero _ this.symm).elim
        | some i =>
            cases o' with
            | none =>
                have : (t i).succ = (0 : Fin (n + 1)) := congrArg Subtype.val h
                exact (Fin.succ_ne_zero _ this).elim
            | some i' =>
                have : (t i).succ = (t i').succ := congrArg Subtype.val h
                have ht : t i = t i' := Fin.succ_injective n this
                have heq : i = i' := t.injective ht
                subst heq; rfl
      · intro x
        by_cases hx : x.1 = 0
        · refine ⟨none, ?_⟩
          apply Subtype.ext; simp [hx]
        · rcases x.2.resolve_left hx with ⟨i, hi⟩
          refine ⟨some i, ?_⟩
          apply Subtype.ext; simp [hi]))

@[simp] lemma orbitEquiv_apply_zero {k : ℕ} (t : Fin k ↪ Fin n) :
    (orbitEquiv t) (0 : Fin (k + 1)) = ⟨(0 : Fin (n + 1)), Or.inl rfl⟩ := by
  simp [orbitEquiv]

@[simp] lemma orbitEquiv_apply_succ {k : ℕ} (t : Fin k ↪ Fin n) (i : Fin k) :
    (orbitEquiv t) i.succ = ⟨(t i).succ, Or.inr ⟨i, rfl⟩⟩ := by
  simp [orbitEquiv]

/-- The cycle `(0, (t 0).succ, (t 1).succ, …, (t (k-1)).succ)` through `0`. -/
noncomputable def cycleThroughZero {k : ℕ} (t : Fin k ↪ Fin n) : SymmetricGroup (n + 1) := by
  classical
  exact (finRotate (k + 1)).extendDomain (orbitEquiv t)

/-- `cycleThroughZero t` maps `0` to `(t 0).succ` (when `k > 0`). -/
lemma cycleThroughZero_apply_zero {k : ℕ} (t : Fin k ↪ Fin n) (hk : 0 < k) :
    (cycleThroughZero t) (0 : Fin (n + 1)) = (t ⟨0, hk⟩).succ := by
  classical
  haveI : NeZero k := ⟨ne_of_gt hk⟩
  dsimp [cycleThroughZero]
  have hrot : (finRotate (k + 1)) (0 : Fin (k + 1)) = (0 : Fin k).succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (i := (0 : Fin (k + 1))) (by
      intro h
      have hval : (0 : Fin (k + 1)).val = (Fin.last k).val := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hval
      omega)]
    simp only [Fin.val_succ, Fin.val_zero]
  calc ((finRotate (k + 1)).extendDomain (orbitEquiv t)) (0 : Fin (n + 1))
      = ((finRotate (k + 1)).extendDomain (orbitEquiv t)) ((orbitEquiv t) (0 : Fin (k + 1)) : Fin (n + 1)) := by
          apply congrArg (fun x : Fin (n + 1) => ((finRotate (k + 1)).extendDomain (orbitEquiv t)) x)
          rw [orbitEquiv_apply_zero]
    _ = (orbitEquiv t) ((finRotate (k + 1)) (0 : Fin (k + 1))) := by
          exact Equiv.Perm.extendDomain_apply_image
            (e := finRotate (k + 1)) (f := orbitEquiv t) (a := (0 : Fin (k + 1)))
    _ = (orbitEquiv t) ((0 : Fin k).succ) := by
          apply congrArg (fun j : Fin (k + 1) => ((orbitEquiv t) j : Fin (n + 1)))
          exact hrot
    _ = (t ⟨0, hk⟩).succ := by
          rw [orbitEquiv_apply_succ]
          rfl

/-- `cycleThroughZero t` maps `(t i).succ` to `(t (i+1)).succ` (when `i + 1 < k`). -/
lemma cycleThroughZero_apply_succ {k : ℕ} (t : Fin k ↪ Fin n) (i : Fin k) (hi : i + 1 < k) :
    (cycleThroughZero t) (t i).succ = (t ⟨i + 1, hi⟩).succ := by
  classical
  dsimp [cycleThroughZero]
  have hrot : (finRotate (k + 1)) i.succ = (⟨i + 1, hi⟩ : Fin k).succ := by
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (i := i.succ) (by
      intro h
      have hval : (i.succ : Fin (k + 1)).val = (Fin.last k).val := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hval
      omega)]
    simp only [Fin.val_succ]
  calc ((finRotate (k + 1)).extendDomain (orbitEquiv t)) ((t i).succ : Fin (n + 1))
      = ((finRotate (k + 1)).extendDomain (orbitEquiv t)) ((orbitEquiv t) i.succ : Fin (n + 1)) := by
          apply congrArg (fun x : Fin (n + 1) => ((finRotate (k + 1)).extendDomain (orbitEquiv t)) x)
          rw [orbitEquiv_apply_succ]
    _ = (orbitEquiv t) ((finRotate (k + 1)) i.succ) := by
          exact Equiv.Perm.extendDomain_apply_image
            (e := finRotate (k + 1)) (f := orbitEquiv t) (a := i.succ)
    _ = (orbitEquiv t) ((⟨i + 1, hi⟩ : Fin k).succ) := by
          apply congrArg (fun j : Fin (k + 1) => ((orbitEquiv t) j : Fin (n + 1)))
          exact hrot
    _ = (t ⟨i + 1, hi⟩).succ := by
          rw [orbitEquiv_apply_succ]

/-- `cycleThroughZero t` maps the last point `(t (k-1)).succ` back to `0` (when `k > 0`). -/
lemma cycleThroughZero_apply_last {k : ℕ} (t : Fin k ↪ Fin n) (hk : 0 < k) :
    (cycleThroughZero t) (t ⟨k - 1, Nat.sub_one_lt_of_lt hk⟩).succ = 0 := by
  classical
  haveI : NeZero k := ⟨ne_of_gt hk⟩
  dsimp [cycleThroughZero]
  have hrot : (finRotate (k + 1)) (⟨k - 1, Nat.sub_one_lt_of_lt hk⟩ : Fin k).succ =
      (0 : Fin (k + 1)) := by
    have hlast : (⟨k - 1, Nat.sub_one_lt_of_lt hk⟩ : Fin k).succ = Fin.last k := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [hlast]
    exact finRotate_last
  calc ((finRotate (k + 1)).extendDomain (orbitEquiv t))
        ((t ⟨k - 1, Nat.sub_one_lt_of_lt hk⟩).succ : Fin (n + 1))
      = ((finRotate (k + 1)).extendDomain (orbitEquiv t))
          ((orbitEquiv t) (⟨k - 1, Nat.sub_one_lt_of_lt hk⟩ : Fin k).succ : Fin (n + 1)) := by
          apply congrArg (fun x : Fin (n + 1) => ((finRotate (k + 1)).extendDomain (orbitEquiv t)) x)
          rw [orbitEquiv_apply_succ]
    _ = (orbitEquiv t) ((finRotate (k + 1)) (⟨k - 1, Nat.sub_one_lt_of_lt hk⟩ : Fin k).succ) := by
          exact Equiv.Perm.extendDomain_apply_image
            (e := finRotate (k + 1)) (f := orbitEquiv t) (a := (⟨k - 1, Nat.sub_one_lt_of_lt hk⟩ : Fin k).succ)
    _ = (orbitEquiv t) (0 : Fin (k + 1)) := by
          apply congrArg (fun j : Fin (k + 1) => ((orbitEquiv t) j : Fin (n + 1)))
          exact hrot
    _ = 0 := by
          rw [orbitEquiv_apply_zero]

/-- `finRotate (k+1)` is a full cycle: `0` is `SameCycle` with every point. -/
lemma finRotate_sameCycle_all {k : ℕ} (x : Fin (k + 1)) :
    Equiv.Perm.SameCycle (finRotate (k + 1)) (0 : Fin (k + 1)) x := by
  refine ⟨(x.val : ℤ), ?_⟩
  rw [zpow_natCast]
  change ((finRotate (k + 1))^[x.val]) (0 : Fin (k + 1)) = x
  rw [(finCycle_eq_finRotate_iterate (k := x)).symm]
  simp

/-- The orbit of `0` under `cycleThroughZero t` is exactly `{0} ∪ {(t i).succ}`. -/
lemma sameCycle_cycleThroughZero_iff {k : ℕ} (t : Fin k ↪ Fin n) (x : Fin (n + 1)) :
    Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) x ↔
      (x = 0 ∨ ∃ i : Fin k, x = (t i).succ) := by
  classical
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    let y : Fin (k + 1) := ((finRotate (k + 1)) ^ m) (0 : Fin (k + 1))
    have hx : x = ((orbitEquiv t) y : Fin (n + 1)) := by
      have hzpow : (cycleThroughZero t ^ m) = ((finRotate (k + 1) ^ m).extendDomain (orbitEquiv t)) := by
        rw [cycleThroughZero]
        rw [← Equiv.Perm.extendDomain_zpow]
      rw [hzpow] at hm
      calc x = ((finRotate (k + 1) ^ m).extendDomain (orbitEquiv t)) (0 : Fin (n + 1)) := hm.symm
        _ = ((finRotate (k + 1) ^ m).extendDomain (orbitEquiv t)) ((orbitEquiv t) (0 : Fin (k + 1)) : Fin (n + 1)) := by
            apply congrArg (fun a : Fin (n + 1) => ((finRotate (k + 1) ^ m).extendDomain (orbitEquiv t)) a)
            rw [orbitEquiv_apply_zero]
        _ = (orbitEquiv t) y := by
            exact Equiv.Perm.extendDomain_apply_image
              (e := finRotate (k + 1) ^ m) (f := orbitEquiv t) (a := (0 : Fin (k + 1)))
    rcases ((orbitEquiv t) y).2 with h0 | hi
    · left
      exact hx.trans h0
    · right
      rcases hi with ⟨i, hi'⟩
      exact ⟨i, hx.trans hi'⟩
  · intro h
    rcases h with h0 | hi
    · simpa [h0] using (Equiv.Perm.SameCycle.rfl : Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) (0 : Fin (n + 1)))
    · rcases hi with ⟨i, rfl⟩
      have hsame : Equiv.Perm.SameCycle (finRotate (k + 1)) (0 : Fin (k + 1)) i.succ :=
        finRotate_sameCycle_all i.succ
      have h' : Equiv.Perm.SameCycle ((finRotate (k + 1)).extendDomain (orbitEquiv t))
          ((orbitEquiv t) (0 : Fin (k + 1))) ((orbitEquiv t) i.succ) :=
        (Equiv.Perm.sameCycle_extendDomain (f := orbitEquiv t)).2 hsame
      have hz : ((orbitEquiv t) (0 : Fin (k + 1)) : Fin (n + 1)) = (0 : Fin (n + 1)) := by
        rw [orbitEquiv_apply_zero]
      have hs : ((orbitEquiv t) i.succ : Fin (n + 1)) = ((t i).succ : Fin (n + 1)) := by
        rw [orbitEquiv_apply_succ]
      rw [hz] at h'
      rw [hs] at h'
      simpa [cycleThroughZero] using h'

/-- `cycleThroughZero t` is a cycle through `0` of length `k+1`. -/
lemma cycleLen_cycleThroughZero {k : ℕ} (t : Fin k ↪ Fin n) :
    cycleLen (cycleThroughZero t) = k + 1 := by
  classical
  rw [cycleLen_eq_card_sameCycle]
  have hcard : Fintype.card {x : Fin (n + 1) // Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) x} =
      Fintype.card {x : Fin (n + 1) // x = 0 ∨ ∃ i : Fin k, x = (t i).succ} := by
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => sameCycle_cycleThroughZero_iff t x))
  rw [hcard]
  rw [Fintype.card_congr (orbitEquiv t).symm]
  simp

/-- The complement of the orbit of `cycleThroughZero t` has cardinality `n - k`. -/
lemma card_complement_cycleThroughZero {k : ℕ} (t : Fin k ↪ Fin n) :
    Fintype.card {x : Fin (n + 1) // ¬ (x = 0 ∨ ∃ i : Fin k, x = (t i).succ)} = n - k := by
  classical
  rw [Fintype.card_subtype_compl]
  have hcard : Fintype.card {x : Fin (n + 1) // x = 0 ∨ ∃ i : Fin k, x = (t i).succ} = k + 1 := by
    rw [Fintype.card_congr (orbitEquiv t).symm, Fintype.card_fin]
  rw [hcard, Fintype.card_fin]
  omega

/-- The complement of the orbit, identified with `Fin (n-k)`. -/
noncomputable def complementEquiv {k : ℕ} (t : Fin k ↪ Fin n) :
    Fin (n - k) ≃ {x : Fin (n + 1) // ¬ (x = 0 ∨ ∃ i : Fin k, x = (t i).succ)} :=
  (Fintype.equivFinOfCardEq (card_complement_cycleThroughZero t)).symm

/-- Lift a permutation of `Fin (n-k)` to `Fin (n+1)` fixing the cycle `{0} ∪ {(t i).succ}`. -/
noncomputable def liftResidual {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    SymmetricGroup (n + 1) :=
  Equiv.Perm.ofSubtype ((Equiv.permCongr (complementEquiv t)) σ)

/-- `liftResidual t σ` fixes `0`. -/
lemma liftResidual_fix_zero {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    liftResidual t σ (0 : Fin (n + 1)) = 0 := by
  classical
  dsimp [liftResidual]
  apply Equiv.Perm.ofSubtype_apply_of_not_mem
  intro h
  exact h (Or.inl rfl)

/-- `liftResidual t σ` fixes every point `(t i).succ`. -/
lemma liftResidual_fix_succ {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) (i : Fin k) :
    liftResidual t σ ((t i).succ) = (t i).succ := by
  classical
  dsimp [liftResidual]
  apply Equiv.Perm.ofSubtype_apply_of_not_mem
  intro h
  exact h (Or.inr ⟨i, rfl⟩)

end cycleThroughZero

/-! ### The cycle-removal bijection (forward map: the ordered tuple) -/

section cycleBijection

variable {n : ℕ}

/-- For `0 < a < cycleLen π`, the iterate `(π^a) 0` is not `0`. -/
lemma pow_apply_ne_zero_of_lt {π : SymmetricGroup (n + 1)} {a : ℕ}
    (ha0 : 0 < a) (ha : a < cycleLen π) : (π ^ a) (0 : Fin (n + 1)) ≠ 0 :=
  pow_apply_ne_of_lt_cycleLenAt π (0 : Fin (n + 1)) a ha0 (by simpa using ha)

/-- Distinctness of the first `cycleLen π` iterates of `0` under `π` (when `π` moves `0`). -/
lemma pow_apply_eq_pow_apply_of_le {π : SymmetricGroup (n + 1)} {a b : ℕ}
    (h0 : π (0 : Fin (n + 1)) ≠ 0) (hab : a ≤ b) (hb : b < cycleLen π) :
    ((π ^ a) (0 : Fin (n + 1)) = (π ^ b) (0 : Fin (n + 1))) → a = b := by
  classical
  intro h
  have hcyc : (π.cycleOf 0).IsCycle := Equiv.Perm.isCycle_cycleOf π h0
  have hc : ((π.cycleOf 0) ^ a) (0 : Fin (n + 1)) = ((π.cycleOf 0) ^ b) (0 : Fin (n + 1)) := by
    simpa [Equiv.Perm.cycleOf_pow_apply_self] using h
  have hx : (π.cycleOf 0) (0 : Fin (n + 1)) ≠ 0 := by
    simpa [Equiv.Perm.cycleOf_apply_self] using h0
  have hpow : (π.cycleOf 0) ^ a = (π.cycleOf 0) ^ b := (hcyc.pow_eq_pow_iff).2 ⟨0, hx, hc⟩
  have hsub : (π.cycleOf 0) ^ (b - a) = 1 := by
    have hb' : (π.cycleOf 0) ^ b = (π.cycleOf 0) ^ a * (π.cycleOf 0) ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hab]
    have h' : (π.cycleOf 0) ^ a = (π.cycleOf 0) ^ a * (π.cycleOf 0) ^ (b - a) :=
      hpow.trans hb'
    have h1 := congrArg (fun g : SymmetricGroup (n + 1) => ((π.cycleOf 0) ^ a)⁻¹ * g) h'
    change ((π.cycleOf 0) ^ a)⁻¹ * (π.cycleOf 0) ^ a =
      ((π.cycleOf 0) ^ a)⁻¹ * ((π.cycleOf 0) ^ a * (π.cycleOf 0) ^ (b - a)) at h1
    rw [inv_mul_cancel] at h1
    rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
    exact h1.symm
  have hord : orderOf (π.cycleOf 0) = cycleLen π := orderOf_cycleOf_eq_cycleLen π
  have hdvd : orderOf (π.cycleOf 0) ∣ b - a := (orderOf_dvd_iff_pow_eq_one).2 hsub
  have hlt : b - a < orderOf (π.cycleOf 0) := by
    rw [hord]
    omega
  have hzero : b - a = 0 := by
    by_contra hne
    have hpos : 0 < b - a := Nat.pos_of_ne_zero hne
    have hle : orderOf (π.cycleOf 0) ≤ b - a := Nat.le_of_dvd hpos hdvd
    omega
  omega

/-- The ordered `k`-tuple of the non-zero points of the cycle of `π` through `0`. -/
noncomputable def tupleOf {k : ℕ} [NeZero n] (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    Fin k ↪ Fin n :=
  { toFun := fun i => (0 : Fin n).predAbove ((π ^ (i.val + 1)) (0 : Fin (n + 1))),
    inj' := by
      intro i j hij
      apply Fin.ext
      dsimp at hij
      have hik : i.val < k := i.isLt
      have hjk : j.val < k := j.isLt
      have h0 : π (0 : Fin (n + 1)) ≠ 0 := by
        intro h0'
        have hcycle : cycleLen π = 1 := (cycleLen_eq_one_iff π).2 h0'
        omega
      have hne_i : (π ^ (i.val + 1)) (0 : Fin (n + 1)) ≠ 0 :=
        pow_apply_ne_zero_of_lt (π := π) (by omega) (by rw [h]; omega)
      have hne_j : (π ^ (j.val + 1)) (0 : Fin (n + 1)) ≠ 0 :=
        pow_apply_ne_zero_of_lt (π := π) (by omega) (by rw [h]; omega)
      have hijeq : (π ^ (i.val + 1)) (0 : Fin (n + 1)) = (π ^ (j.val + 1)) (0 : Fin (n + 1)) := by
        have hsucc := congrArg Fin.succ hij
        rw [Fin.succ_predAbove_zero hne_i] at hsucc
        rw [Fin.succ_predAbove_zero hne_j] at hsucc
        exact hsucc
      by_cases hij' : i.val ≤ j.val
      · have hab : i.val + 1 = j.val + 1 :=
          pow_apply_eq_pow_apply_of_le (π := π) h0 (by omega) (by rw [h]; omega) hijeq
        omega
      · have hij'' : j.val ≤ i.val := le_of_not_ge hij'
        have hab : j.val + 1 = i.val + 1 :=
          pow_apply_eq_pow_apply_of_le (π := π) h0 (by omega) (by rw [h]; omega) hijeq.symm
        omega }

/-- The residual permutation, cast from `S_{(n+1) - cycleLen π}` to `S_{n-k}`. -/
noncomputable def residualOf {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    SymmetricGroup (n - k) := by
  classical
  have h' : (n + 1) - cycleLen π = n - k := by
    rw [h]
    omega
  exact h' ▸ residual π

/-- `cycleThroughZero t` and `liftResidual t σ` are disjoint. -/
lemma disjoint_cycleThroughZero_liftResidual {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    Equiv.Perm.Disjoint (cycleThroughZero t) (liftResidual t σ) := by
  classical
  intro x
  by_cases hx : x = 0 ∨ ∃ i : Fin k, x = (t i).succ
  · right
    rcases hx with h0 | hi
    · simpa [h0] using liftResidual_fix_zero t σ
    · rcases hi with ⟨i, rfl⟩
      exact liftResidual_fix_succ t σ i
  · left
    dsimp [cycleThroughZero]
    exact Equiv.Perm.extendDomain_apply_not_subtype
      (e := finRotate (k + 1)) (f := orbitEquiv t) (b := x) (h := hx)

/-- `cycleThroughZero t * liftResidual t σ` has cycle length `k+1` through `0`. -/
lemma cycleLen_mul_liftResidual {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    cycleLen (cycleThroughZero t * liftResidual t σ) = k + 1 := by
  classical
  have hdisj : Equiv.Perm.Disjoint (cycleThroughZero t) (liftResidual t σ) :=
    disjoint_cycleThroughZero_liftResidual t σ
  have hcomm : Commute (cycleThroughZero t) (liftResidual t σ) := hdisj.commute
  have hcycleOf : (cycleThroughZero t * liftResidual t σ).cycleOf (0 : Fin (n + 1)) =
      (cycleThroughZero t).cycleOf (0 : Fin (n + 1)) :=
    Equiv.Perm.cycleOf_mul_of_apply_right_eq_self (f := cycleThroughZero t) (g := liftResidual t σ)
      hcomm (0 : Fin (n + 1)) (liftResidual_fix_zero t σ)
  calc cycleLen (cycleThroughZero t * liftResidual t σ)
      = orderOf ((cycleThroughZero t * liftResidual t σ).cycleOf (0 : Fin (n + 1))) := (orderOf_cycleOf_eq_cycleLen _).symm
    _ = orderOf ((cycleThroughZero t).cycleOf (0 : Fin (n + 1))) := by rw [hcycleOf]
    _ = cycleLen (cycleThroughZero t) := orderOf_cycleOf_eq_cycleLen _
    _ = k + 1 := cycleLen_cycleThroughZero t

/-- `((tupleOf π h) i).succ = (π^{i+1}) 0`. -/
lemma tupleOf_succ_apply {k : ℕ} [NeZero n] (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) (i : Fin k) :
    ((tupleOf π h) i).succ = (π ^ (i.val + 1)) (0 : Fin (n + 1)) := by
  classical
  have hne : (π ^ (i.val + 1)) (0 : Fin (n + 1)) ≠ 0 :=
    pow_apply_ne_zero_of_lt (π := π) (by omega) (by rw [h]; omega)
  dsimp [tupleOf]
  rw [Fin.succ_predAbove_zero hne]

/-- `(π^{k+1}) 0 = 0` when `cycleLen π = k+1`. -/
lemma pow_cycleLen_apply {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    (π ^ (k + 1)) (0 : Fin (n + 1)) = 0 := by
  classical
  have hord : orderOf (π.cycleOf 0) = k + 1 := by
    rw [orderOf_cycleOf_eq_cycleLen π, h]
  have h1 : (π.cycleOf 0) ^ (k + 1) = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one (π.cycleOf 0)
  have h2 : ((π.cycleOf 0) ^ (k + 1)) (0 : Fin (n + 1)) = 0 := by simp [h1]
  simpa [Equiv.Perm.cycleOf_pow_apply_self] using h2

/-- The orbit of `0` under `π` (with `cycleLen π = k+1`) is `{0} ∪ {(π^{i+1}) 0}`. -/
lemma sameCycle_iff_cyclePoints {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) (x : Fin (n + 1)) :
    Equiv.Perm.SameCycle π (0 : Fin (n + 1)) x ↔
      (x = 0 ∨ ∃ i : Fin k, x = (π ^ (i.val + 1)) (0 : Fin (n + 1))) := by
  classical
  constructor
  · intro hsc
    by_cases h0 : π (0 : Fin (n + 1)) = 0
    · left
      rcases hsc with ⟨m, hm⟩
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (f := π) (x := (0 : Fin (n + 1))) h0 m] at hm
      exact hm.symm
    · have hsupp : (0 : Fin (n + 1)) ∈ π.support := by
        rw [Equiv.Perm.mem_support]
        exact h0
      obtain ⟨i, hi, hxi⟩ := Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support (f := π) hsc hsupp
      have hcyc : (π.cycleOf 0).IsCycle := Equiv.Perm.isCycle_cycleOf π h0
      have hcard : (π.cycleOf 0).support.card = k + 1 := by
        rw [← hcyc.orderOf, orderOf_cycleOf_eq_cycleLen π, h]
      have hik : i ≤ k := by omega
      by_cases hi0 : i = 0
      · left
        rw [hi0] at hxi
        exact hxi.symm
      · right
        refine ⟨⟨i - 1, by omega⟩, ?_⟩
        rw [show i = (i - 1) + 1 by omega] at hxi
        exact hxi.symm
  · intro h
    rcases h with h0 | hi
    · rw [h0]
    · rcases hi with ⟨i, rfl⟩
      exact ⟨(i.val + 1 : ℤ), rfl⟩

/-- `cycleThroughZero (tupleOf π h)` recovers the cycle of `π` through `0`. -/
lemma cycleThroughZero_tupleOf {k : ℕ} [NeZero n] (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    cycleThroughZero (tupleOf π h) = π.cycleOf 0 := by
  classical
  ext x
  by_cases hx : x = 0 ∨ ∃ i : Fin k, x = ((tupleOf π h) i).succ
  · rcases hx with h0 | hi
    · subst h0
      by_cases hk : k = 0
      · subst hk
        have hpi : π (0 : Fin (n + 1)) = 0 := by
          have hcycle : cycleLen π = 1 := by rw [h]
          exact (cycleLen_eq_one_iff π).1 hcycle
        simp [hpi, cycleThroughZero]
      · have hk' : 0 < k := Nat.pos_of_ne_zero hk
        haveI : NeZero k := ⟨ne_of_gt hk'⟩
        rw [cycleThroughZero_apply_zero (t := tupleOf π h) hk']
        rw [tupleOf_succ_apply π h ⟨0, hk'⟩]
        simp [Equiv.Perm.cycleOf_apply_self]
    · rcases hi with ⟨i, rfl⟩
      by_cases hil : i.val + 1 < k
      · rw [cycleThroughZero_apply_succ (t := tupleOf π h) i hil]
        rw [tupleOf_succ_apply π h ⟨i.val + 1, hil⟩]
        rw [tupleOf_succ_apply π h i]
        rw [Equiv.Perm.cycleOf_apply_apply_pow_self]
      · have hik : i.val + 1 = k := by omega
        have hik' : i = ⟨k - 1, Nat.sub_one_lt_of_lt (by omega : 0 < k)⟩ := by
          apply Fin.ext
          change i.val = k - 1
          omega
        rw [hik']
        rw [cycleThroughZero_apply_last (t := tupleOf π h) (by omega : 0 < k)]
        rw [tupleOf_succ_apply π h ⟨k - 1, Nat.sub_one_lt_of_lt (by omega : 0 < k)⟩]
        rw [show (k - 1) + 1 = k by omega]
        rw [Equiv.Perm.cycleOf_apply_apply_pow_self]
        rw [pow_cycleLen_apply π h]
  · have hnot : ¬ Equiv.Perm.SameCycle π (0 : Fin (n + 1)) x := by
      intro hsc
      have hpx := (sameCycle_iff_cyclePoints π h x).1 hsc
      rcases hpx with h0 | hi
      · exact hx (Or.inl h0)
      · rcases hi with ⟨i, hi'⟩
        exact hx (Or.inr ⟨i, hi'.trans (tupleOf_succ_apply π h i).symm⟩)
    have h1 : (π.cycleOf 0) x = x :=
      Equiv.Perm.cycleOf_apply_of_not_sameCycle (f := π) (x := (0 : Fin (n + 1))) hnot
    have h2 : (cycleThroughZero (tupleOf π h)) x = x := by
      dsimp [cycleThroughZero]
      apply Equiv.Perm.extendDomain_apply_not_subtype
        (e := finRotate (k + 1)) (f := orbitEquiv (tupleOf π h)) (b := x)
      intro hp
      rcases hp with h0 | hi
      · exact hx (Or.inl h0)
      · rcases hi with ⟨i, hi'⟩
        exact hx (Or.inr ⟨i, hi'⟩)
    rw [h1, h2]

end cycleBijection

/-! ### The cycle-removal bijection (transport + assembly; discharges MP-006/MP-007)

The bijection `{π | cycleLen π = k+1} ≃ (Fin k ↪ Fin n) × S_{n-k}` is the
combinatorial content behind Corollary 2.2. -/

section cycleRemovalBijection

variable {n : ℕ} [NeZero n]

/-- `SameCycle π 0 x` agrees with `SameCycle (π.cycleOf 0) 0 x`. -/
lemma sameCycle_cycleOf_iff (π : SymmetricGroup n) (x : Fin n) :
    Equiv.Perm.SameCycle π (0 : Fin n) x ↔
      Equiv.Perm.SameCycle (π.cycleOf 0) (0 : Fin n) x := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [Equiv.Perm.cycleOf_zpow_apply_self]
    exact hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [Equiv.Perm.cycleOf_zpow_apply_self] at hi
    exact hi

/-- `SameCycle π 0 x` agrees with `x = 0 ∨ ∃ i, x = ((tupleOf π h) i).succ`. -/
lemma sameCycle_iff_complementPred {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1)
    (x : Fin (n + 1)) :
    Equiv.Perm.SameCycle π (0 : Fin (n + 1)) x ↔
      (x = 0 ∨ ∃ i : Fin k, x = ((tupleOf π h) i).succ) := by
  rw [sameCycle_iff_cyclePoints π h]
  constructor
  · intro hx
    rcases hx with h0 | hi
    · exact Or.inl h0
    · rcases hi with ⟨i, hi'⟩
      exact Or.inr ⟨i, hi'.trans (tupleOf_succ_apply π h i).symm⟩
  · intro hx
    rcases hx with h0 | hi
    · exact Or.inl h0
    · rcases hi with ⟨i, hi'⟩
      exact Or.inr ⟨i, hi'.trans (tupleOf_succ_apply π h i)⟩

/-- The two complement subtype predicates (SameCycle vs the explicit tuple form) agree. -/
noncomputable def complementSubtypeEquiv {k : ℕ} (π : SymmetricGroup (n + 1))
    (h : cycleLen π = k + 1) :
    {x : Fin (n + 1) // ¬ Equiv.Perm.SameCycle π (0 : Fin (n + 1)) x} ≃
      {x : Fin (n + 1) // ¬ (x = 0 ∨ ∃ i : Fin k, x = ((tupleOf π h) i).succ)} :=
  Equiv.subtypeEquivRight (fun x => not_iff_not.mpr (sameCycle_iff_complementPred π h x))

/-- Transporting a permutation on a subtype along a propositional reindexing does not
change the underlying permutation of `α`. -/
lemma ofSubtype_permCongr_subtypeEquivRight {α : Type*} {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q] (H : ∀ x, P x ↔ Q x)
    (f : Equiv.Perm (Subtype P)) :
    Equiv.Perm.ofSubtype (Equiv.permCongr (Equiv.subtypeEquivRight H) f) =
      Equiv.Perm.ofSubtype f := by
  classical
  ext x
  by_cases hq : Q x
  · have hp : P x := (H x).mpr hq
    calc Equiv.Perm.ofSubtype (Equiv.permCongr (Equiv.subtypeEquivRight H) f) x
        = ((Equiv.permCongr (Equiv.subtypeEquivRight H) f) ⟨x, hq⟩ : α) := by
            rw [Equiv.Perm.ofSubtype_apply_of_mem]
      _ = (f ⟨x, hp⟩ : α) := by
            rw [Equiv.permCongr_apply]
            change ((Equiv.subtypeEquivRight H) (f ((Equiv.subtypeEquivRight H).symm ⟨x, hq⟩)) : α) =
              (f ⟨x, hp⟩ : α)
            simp [Equiv.subtypeEquivRight_symm_apply, Equiv.subtypeEquivRight_apply]
      _ = Equiv.Perm.ofSubtype f x := by
            rw [Equiv.Perm.ofSubtype_apply_of_mem]
  · have hnp : ¬ P x := fun hp => hq ((H x).mp hp)
    calc Equiv.Perm.ofSubtype (Equiv.permCongr (Equiv.subtypeEquivRight H) f) x
        = x := by
            rw [Equiv.Perm.ofSubtype_apply_of_not_mem
              (f := Equiv.permCongr (Equiv.subtypeEquivRight H) f) (ha := hq)]
      _ = Equiv.Perm.ofSubtype f x := by
            rw [Equiv.Perm.ofSubtype_apply_of_not_mem (f := f) (ha := hnp)]

/-- `(cycleThroughZero t)^{m+1} 0 = (t m).succ` for `m < k`. -/
lemma cycleThroughZero_iterate_apply {k : ℕ} (t : Fin k ↪ Fin n) :
    ∀ m (hm : m < k), ((cycleThroughZero t) ^ (m + 1)) (0 : Fin (n + 1)) = (t ⟨m, hm⟩).succ := by
  intro m hm
  induction m with
  | zero =>
      rw [pow_one]
      exact cycleThroughZero_apply_zero t (by omega : 0 < k)
  | succ m ih =>
      have hm' : m < k := by omega
      calc ((cycleThroughZero t) ^ (m + 1 + 1)) (0 : Fin (n + 1))
          = ((cycleThroughZero t) * (cycleThroughZero t) ^ (m + 1)) (0 : Fin (n + 1)) := by
              rw [pow_succ']
        _ = (cycleThroughZero t) (((cycleThroughZero t) ^ (m + 1)) (0 : Fin (n + 1))) := rfl
        _ = (cycleThroughZero t) ((t ⟨m, hm'⟩).succ) := by rw [ih hm']
        _ = (t ⟨m + 1, hm⟩).succ := by
              apply cycleThroughZero_apply_succ t ⟨m, hm'⟩ (by omega : m + 1 < k)

/-- The forward residual of `π` (on `Fin (n-k)`), using the tuple-aligned equivalence. -/
noncomputable def residualFwd {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    SymmetricGroup (n - k) :=
  (Equiv.permCongr (complementEquiv (tupleOf π h))).symm
    (Equiv.permCongr (complementSubtypeEquiv π h) (residualSubtype π))

/-- `liftResidual (tupleOf π h) (residualFwd π h)` equals the `ofSubtype` of the residual. -/
lemma liftResidual_residualFwd {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    liftResidual (tupleOf π h) (residualFwd π h) = Equiv.Perm.ofSubtype (residualSubtype π) := by
  classical
  dsimp [liftResidual, residualFwd]
  rw [← Equiv.permCongr_symm]
  rw [Equiv.apply_symm_apply]
  dsimp [complementSubtypeEquiv]
  exact ofSubtype_permCongr_subtypeEquivRight (f := residualSubtype π)
    (H := fun x => not_iff_not.mpr (sameCycle_iff_complementPred π h x))

/-- `liftResidual t σ` fixes every point of the cycle `{0} ∪ {(t i).succ}`. -/
lemma liftResidual_fix_cyclePoint {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    ∀ x : Fin (n + 1), (x = 0 ∨ ∃ i : Fin k, x = (t i).succ) → liftResidual t σ x = x := by
  intro x hx
  rcases hx with h0 | hi
  · rw [h0]; exact liftResidual_fix_zero t σ
  · rcases hi with ⟨i, hi'⟩; rw [hi']; exact liftResidual_fix_succ t σ i

/-- `liftResidual t σ` preserves the "complement of the cycle" predicate. -/
lemma liftResidual_mem_iff_mem {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) (x : Fin (n + 1)) :
    (¬ ((liftResidual t σ) x = 0 ∨ ∃ i : Fin k, (liftResidual t σ) x = (t i).succ)) ↔
      (¬ (x = 0 ∨ ∃ i : Fin k, x = (t i).succ)) := by
  classical
  dsimp [liftResidual]
  exact Equiv.Perm.ofSubtype_apply_mem_iff_mem
    (f := Equiv.permCongr (complementEquiv t) σ) (x := x)

/-- `(cycleThroughZero t * liftResidual t σ)^m 0 = (cycleThroughZero t)^m 0`. -/
lemma mul_liftResidual_pow_apply_zero {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    ∀ m, ((cycleThroughZero t * liftResidual t σ) ^ m) (0 : Fin (n + 1)) =
      ((cycleThroughZero t) ^ m) (0 : Fin (n + 1)) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      calc ((cycleThroughZero t * liftResidual t σ) ^ (m + 1)) (0 : Fin (n + 1))
          = (cycleThroughZero t * liftResidual t σ) (((cycleThroughZero t * liftResidual t σ) ^ m) (0 : Fin (n + 1))) := by
              rw [pow_succ']; rfl
        _ = (cycleThroughZero t * liftResidual t σ) (((cycleThroughZero t) ^ m) (0 : Fin (n + 1))) := by
              rw [ih]
        _ = (cycleThroughZero t) ((liftResidual t σ) (((cycleThroughZero t) ^ m) (0 : Fin (n + 1)))) := rfl
        _ = (cycleThroughZero t) (((cycleThroughZero t) ^ m) (0 : Fin (n + 1))) := by
              rw [liftResidual_fix_cyclePoint t σ (((cycleThroughZero t) ^ m) (0 : Fin (n + 1))) (by
                have hsc : Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) (((cycleThroughZero t) ^ m) (0 : Fin (n + 1))) :=
                  ⟨(m : ℤ), by simp⟩
                exact (sameCycle_cycleThroughZero_iff t (((cycleThroughZero t) ^ m) (0 : Fin (n + 1)))).1 hsc)]
        _ = ((cycleThroughZero t) ^ (m + 1)) (0 : Fin (n + 1)) := by rw [pow_succ']; rfl

/-- The tuple of the product `cycleThroughZero t * liftResidual t σ` is exactly `t`. -/
lemma tupleOf_mul_liftResidual {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    tupleOf (cycleThroughZero t * liftResidual t σ) (cycleLen_mul_liftResidual t σ) = t := by
  classical
  ext i
  dsimp [tupleOf]
  rw [mul_liftResidual_pow_apply_zero t σ (i.val + 1)]
  rw [cycleThroughZero_iterate_apply t i.val i.isLt]
  simpa using (Fin.predAbove_zero_succ (i := t i))

/-- `SameCycle` of the product agrees with `SameCycle` of `cycleThroughZero t`. -/
lemma sameCycle_mul_liftResidual_iff {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k))
    (x : Fin (n + 1)) :
    Equiv.Perm.SameCycle (cycleThroughZero t * liftResidual t σ) (0 : Fin (n + 1)) x ↔
      Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) x := by
  classical
  have hdisj := disjoint_cycleThroughZero_liftResidual t σ
  have hcomm := hdisj.commute
  have hcyc := Equiv.Perm.cycleOf_mul_of_apply_right_eq_self (f := cycleThroughZero t)
    (g := liftResidual t σ) hcomm (0 : Fin (n + 1)) (liftResidual_fix_zero t σ)
  calc Equiv.Perm.SameCycle (cycleThroughZero t * liftResidual t σ) (0 : Fin (n + 1)) x
      ↔ Equiv.Perm.SameCycle ((cycleThroughZero t * liftResidual t σ).cycleOf 0) (0 : Fin (n + 1)) x :=
          sameCycle_cycleOf_iff (n := n + 1) (cycleThroughZero t * liftResidual t σ) x
    _ ↔ Equiv.Perm.SameCycle ((cycleThroughZero t).cycleOf 0) (0 : Fin (n + 1)) x := by rw [hcyc]
    _ ↔ Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) x :=
          (sameCycle_cycleOf_iff (n := n + 1) (cycleThroughZero t) x).symm

/-- `ofSubtype (residualSubtype (product))` equals `liftResidual t σ`. -/
lemma ofSubtype_residualSubtype_mul_liftResidual {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    Equiv.Perm.ofSubtype (residualSubtype (cycleThroughZero t * liftResidual t σ)) =
      liftResidual t σ := by
  classical
  apply Equiv.ext
  intro x
  by_cases hsc : Equiv.Perm.SameCycle (cycleThroughZero t) (0 : Fin (n + 1)) x
  · -- x in the cycle: both fix x
    have hscρ : Equiv.Perm.SameCycle (cycleThroughZero t * liftResidual t σ) (0 : Fin (n + 1)) x :=
      (sameCycle_mul_liftResidual_iff t σ x).mpr hsc
    have hx : x = 0 ∨ ∃ i : Fin k, x = (t i).succ := (sameCycle_cycleThroughZero_iff t x).1 hsc
    have h1 : Equiv.Perm.ofSubtype (residualSubtype (cycleThroughZero t * liftResidual t σ)) x = x := by
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem (f := residualSubtype (cycleThroughZero t * liftResidual t σ))
        (ha := not_not.mpr hscρ)]
    rcases hx with h0 | hi
    · rw [h1]; rw [h0]; exact (liftResidual_fix_zero t σ).symm
    · rcases hi with ⟨i, hi'⟩
      rw [h1]; rw [hi']; exact (liftResidual_fix_succ t σ i).symm
  · -- x in the complement: both act as `liftResidual t σ x`
    have hscρ : ¬ Equiv.Perm.SameCycle (cycleThroughZero t * liftResidual t σ) (0 : Fin (n + 1)) x :=
      fun h => hsc ((sameCycle_mul_liftResidual_iff t σ x).1 h)
    calc Equiv.Perm.ofSubtype (residualSubtype (cycleThroughZero t * liftResidual t σ)) x
        = (cycleThroughZero t * liftResidual t σ) x := by
            rw [Equiv.Perm.ofSubtype_apply_of_mem (f := residualSubtype (cycleThroughZero t * liftResidual t σ)) (ha := hscρ)]
            rfl
      _ = (cycleThroughZero t) ((liftResidual t σ) x) := rfl
      _ = (liftResidual t σ) x := by
            have hlx : ¬ ((liftResidual t σ) x = 0 ∨ ∃ i : Fin k, (liftResidual t σ) x = (t i).succ) :=
              (liftResidual_mem_iff_mem t σ x).mpr (by
                have hnot : ¬ (x = 0 ∨ ∃ i : Fin k, x = (t i).succ) :=
                  (not_iff_not.mpr (sameCycle_cycleThroughZero_iff t x)).mp hsc
                exact hnot)
            dsimp [cycleThroughZero]
            exact Equiv.Perm.extendDomain_apply_not_subtype
              (e := finRotate (k + 1)) (f := orbitEquiv t) (b := (liftResidual t σ) x) (h := hlx)

/-- The forward residual of the product is exactly `σ`. -/
lemma residualFwd_mul_liftResidual {k : ℕ} (t : Fin k ↪ Fin n) (σ : SymmetricGroup (n - k)) :
    residualFwd (cycleThroughZero t * liftResidual t σ) (cycleLen_mul_liftResidual t σ) = σ := by
  classical
  let ρ := cycleThroughZero t * liftResidual t σ
  let hρ := cycleLen_mul_liftResidual t σ
  have htuple : tupleOf ρ hρ = t := tupleOf_mul_liftResidual t σ
  apply (Equiv.permCongr (complementEquiv (tupleOf ρ hρ))).injective
  calc Equiv.permCongr (complementEquiv (tupleOf ρ hρ)) (residualFwd ρ hρ)
      = Equiv.permCongr (complementSubtypeEquiv ρ hρ) (residualSubtype ρ) := by
          dsimp [residualFwd]
          rw [← Equiv.permCongr_symm]
          rw [Equiv.apply_symm_apply]
    _ = Equiv.permCongr (complementEquiv (tupleOf ρ hρ)) σ := by
          apply Equiv.Perm.ofSubtype_injective
          calc Equiv.Perm.ofSubtype (Equiv.permCongr (complementSubtypeEquiv ρ hρ) (residualSubtype ρ))
              = Equiv.Perm.ofSubtype (residualSubtype ρ) := by
                  dsimp [complementSubtypeEquiv]
                  exact ofSubtype_permCongr_subtypeEquivRight (f := residualSubtype ρ)
                    (H := fun x => not_iff_not.mpr (sameCycle_iff_complementPred ρ hρ x))
            _ = liftResidual t σ := ofSubtype_residualSubtype_mul_liftResidual t σ
            _ = liftResidual (tupleOf ρ hρ) σ := by rw [← htuple]
            _ = Equiv.Perm.ofSubtype (Equiv.permCongr (complementEquiv (tupleOf ρ hρ)) σ) := by
                rfl

/-- `cycleThroughZero (tupleOf π h) * liftResidual (tupleOf π h) (residualFwd π h) = π`. -/
lemma cycleThroughZero_tupleOf_lift {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    cycleThroughZero (tupleOf π h) * liftResidual (tupleOf π h) (residualFwd π h) = π := by
  classical
  calc cycleThroughZero (tupleOf π h) * liftResidual (tupleOf π h) (residualFwd π h)
      = π.cycleOf 0 * Equiv.Perm.ofSubtype (residualSubtype π) := by
          rw [cycleThroughZero_tupleOf π h, liftResidual_residualFwd π h]
    _ = Equiv.Perm.ofSubtype (cyclePerm π) * Equiv.Perm.ofSubtype (residualSubtype π) := by
          rw [← ofSubtype_cyclePerm π]
    _ = π := (decompose_mul π).symm

/-- The cycle-removal bijection
`{π | cycleLen π = k+1} ≃ (Fin k ↪ Fin n) × S_{n-k}`. -/
noncomputable def cycleRemovalEquiv {k : ℕ} :
    {π : SymmetricGroup (n + 1) // cycleLen π = k + 1} ≃ (Fin k ↪ Fin n) × SymmetricGroup (n - k) :=
  { toFun := fun ⟨π, h⟩ => (tupleOf π h, residualFwd π h),
    invFun := fun p => ⟨cycleThroughZero p.1 * liftResidual p.1 p.2, cycleLen_mul_liftResidual p.1 p.2⟩,
    left_inv := by
      intro ⟨π, h⟩
      apply Subtype.ext
      exact cycleThroughZero_tupleOf_lift π h
    right_inv := by
      intro p
      apply Prod.ext
      · exact tupleOf_mul_liftResidual p.1 p.2
      · exact residualFwd_mul_liftResidual p.1 p.2 }

/-- `orderOf (residualFwd π h)` equals `orderOf (residual π)`. -/
lemma orderOf_residualFwd {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    orderOf (residualFwd π h) = orderOf (residual π) := by
  classical
  change orderOf ((Equiv.permCongrHom ((complementEquiv (tupleOf π h)).symm))
    ((Equiv.permCongrHom (complementSubtypeEquiv π h)) (residualSubtype π))) = orderOf (residual π)
  rw [MulEquiv.orderOf_eq (Equiv.permCongrHom ((complementEquiv (tupleOf π h)).symm))]
  rw [MulEquiv.orderOf_eq (Equiv.permCongrHom (complementSubtypeEquiv π h))]
  exact (orderOf_residual π).symm

/-- `orderOf π = lcm (k+1) (orderOf (residualFwd π h))` when `cycleLen π = k+1`. -/
lemma orderOf_eq_lcm_cycleLen_residualFwd {k : ℕ} (π : SymmetricGroup (n + 1)) (h : cycleLen π = k + 1) :
    orderOf π = Nat.lcm (k + 1) (orderOf (residualFwd π h)) := by
  calc orderOf π
      = Nat.lcm (cycleLen π) (orderOf (residual π)) := orderOf_eq_lcm_cycleLen_residual π
    _ = Nat.lcm (k + 1) (orderOf (residual π)) := congrArg (fun x => Nat.lcm x (orderOf (residual π))) h
    _ = Nat.lcm (k + 1) (orderOf (residualFwd π h)) := by rw [orderOf_residualFwd π h]

end cycleRemovalBijection

/-! ### Corollary 2.2 (recurrence inputs)

The uniform cycle length and order-filtered cycle removal are the two counting
facts that assemble the paper's Corollary 2.2. Their proofs amount to the
cycle-removal bijection
`{π | cycleLen π = d} ≃ (Fin (d-1) ↪ Fin (n-1)) × S_{n-d}`; see `SORRY.md`
(MP-006 / MP-007) for the precise discharge plan. -/

section corollary22

variable {n : ℕ} [NeZero n]

/-- **Uniform cycle length** (via the bijection
`{π | cycleLen π = d} ≃ (Fin (d-1) ↪ Fin (n-1)) × S_{n-d}`).
Count: `#{π | cycleLen π = d} = (n-1)!` for `1 ≤ d ≤ n`. -/
theorem card_cycleLen_eq_factorial_pred (d : ℕ) (hd : 1 ≤ d) (hdl : d ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => cycleLen π = d)).card =
      Nat.factorial (n - 1) := by
  classical
  by_cases hn1 : n = 1
  · subst n
    have hd1 : d = 1 := by omega
    subst d
    have hcycle : ∀ π : SymmetricGroup 1, cycleLen π = 1 := by
      intro π
      rw [cycleLen_eq_one_iff]
      exact Subsingleton.elim _ _
    have hfilter : (Finset.univ : Finset (SymmetricGroup 1)).filter (fun π => cycleLen π = 1) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro π
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ π, hcycle π⟩
    rw [hfilter, Finset.card_univ, card_symmetricGroup]
    norm_num
  · rw [← Fintype.card_subtype (fun π : SymmetricGroup n => cycleLen π = d)]
    cases n with
    | zero => omega
    | succ n' =>
      cases d with
      | zero => omega
      | succ d' =>
        haveI : NeZero n' := ⟨by omega⟩
        rw [Fintype.card_congr (cycleRemovalEquiv (n := n') (k := d'))]
        rw [Fintype.card_prod, Fintype.card_embedding_eq, card_symmetricGroup]
        rw [Fintype.card_fin, Fintype.card_fin]
        rw [Nat.mul_comm]
        exact Nat.factorial_mul_descFactorial (n := n') (k := d') (by omega : d' ≤ n')

/-- **Order-filtered cycle removal** (the bijection preserving `orderOf`).
`#{π | cycleLen π = d ∧ orderOf π = m} = (n-1)!/(n-d)! · #{σ | lcm(d, orderOf σ) = m}`. -/
theorem card_cycleLen_orderOf_eq (d m : ℕ) (hd : 1 ≤ d) (hdl : d ≤ n) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => cycleLen π = d ∧ orderOf π = m)).card =
      (Nat.descFactorial (n - 1) (d - 1)) *
        ((Finset.univ : Finset (SymmetricGroup (n - d))).filter
          (fun σ => Nat.lcm d (orderOf σ) = m)).card := by
  classical
  rw [← Fintype.card_subtype (fun π : SymmetricGroup n => cycleLen π = d ∧ orderOf π = m)]
  by_cases hn1 : n = 1
  · subst n
    have hd1 : d = 1 := by omega
    subst d
    have hord1 : ∀ π : SymmetricGroup 1, orderOf π = 1 := by
      intro π
      have hπ : π = 1 := Subsingleton.elim π 1
      rw [hπ, orderOf_one]
    have hord0 : ∀ σ : SymmetricGroup 0, orderOf σ = 1 := by
      intro σ
      have hσ : σ = 1 := Subsingleton.elim σ 1
      rw [hσ, orderOf_one]
    have hlcm : ∀ x : ℕ, Nat.lcm 1 x = x := by intro x; simp
    by_cases hm : m = 1
    · subst m
      have hL : Fintype.card {π : SymmetricGroup 1 // cycleLen π = 1 ∧ orderOf π = 1} = 1 := by
        let e : {π : SymmetricGroup 1 // cycleLen π = 1 ∧ orderOf π = 1} ≃ SymmetricGroup 1 :=
          { toFun := fun ⟨π, _⟩ => π
            invFun := fun π => ⟨π, by
              rw [cycleLen_eq_one_iff]
              exact Subsingleton.elim _ _, hord1 π⟩
            left_inv := by intro ⟨π, _⟩; rfl
            right_inv := by intro π; rfl }
        rw [Fintype.card_congr e, card_symmetricGroup 1]
        norm_num
      have hR : Nat.descFactorial 0 0 *
          ((Finset.univ : Finset (SymmetricGroup 0)).filter (fun σ => Nat.lcm 1 (orderOf σ) = 1)).card = 1 := by
        have hfilter : (Finset.univ : Finset (SymmetricGroup 0)).filter (fun σ => Nat.lcm 1 (orderOf σ) = 1) = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro σ
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ σ, by rw [hord0 σ, hlcm 1]⟩
        rw [hfilter, Finset.card_univ, card_symmetricGroup 0, Nat.descFactorial_zero]
        norm_num
      rw [hL, hR]
    · have hL : Fintype.card {π : SymmetricGroup 1 // cycleLen π = 1 ∧ orderOf π = m} = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        exact ⟨fun ⟨π, hcyc, hord⟩ => by
          have hπ : orderOf π = 1 := hord1 π
          rw [hπ] at hord
          exact hm hord.symm⟩
      have hR : Nat.descFactorial 0 0 *
          ((Finset.univ : Finset (SymmetricGroup 0)).filter (fun σ => Nat.lcm 1 (orderOf σ) = m)).card = 0 := by
        rw [← Fintype.card_subtype (fun σ : SymmetricGroup 0 => Nat.lcm 1 (orderOf σ) = m)]
        rw [Fintype.card_eq_zero_iff.mpr (⟨fun ⟨σ, h⟩ => by
          rw [hord0 σ, hlcm 1] at h
          exact hm h.symm⟩ : IsEmpty {σ : SymmetricGroup 0 // Nat.lcm 1 (orderOf σ) = m})]
        rw [Nat.descFactorial_zero, Nat.mul_zero]
      rw [hL, hR]
  · cases n with
    | zero => omega
    | succ n' =>
      cases d with
      | zero => omega
      | succ d' =>
        haveI : NeZero n' := ⟨by omega⟩
        let e := cycleRemovalEquiv (n := n') (k := d')
        let source := {π : SymmetricGroup (n' + 1) // cycleLen π = d' + 1 ∧ orderOf π = m}
        let target := {p : (Fin d' ↪ Fin n') × SymmetricGroup (n' - d') //
          Nat.lcm (d' + 1) (orderOf p.2) = m}
        let e' : source ≃ target :=
          { toFun := fun ⟨π, hcyc, hord⟩ => ⟨e ⟨π, hcyc⟩, by
              dsimp [e, cycleRemovalEquiv]
              have h := orderOf_eq_lcm_cycleLen_residualFwd π hcyc
              rw [← h, hord]⟩
            invFun := fun ⟨p, hp⟩ => ⟨e.symm p, (e.symm p).2, by
              have h := orderOf_eq_lcm_cycleLen_residualFwd (e.symm p).1 (e.symm p).2
              have hres : residualFwd (e.symm p).1 (e.symm p).2 = p.2 := congrArg Prod.snd (e.right_inv p)
              rw [h, hres, hp]⟩
            left_inv := by
              intro ⟨π, hcyc, hord⟩
              apply Subtype.ext
              simpa using congrArg Subtype.val (e.left_inv ⟨π, hcyc⟩)
            right_inv := by
              intro ⟨p, hp⟩
              apply Subtype.ext
              dsimp
              exact e.right_inv p }
        rw [Fintype.card_congr e']
        let e'' : target ≃ (Fin d' ↪ Fin n') × {σ : SymmetricGroup (n' - d') // Nat.lcm (d' + 1) (orderOf σ) = m} :=
          { toFun := fun ⟨p, hp⟩ => (p.1, ⟨p.2, hp⟩)
            invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
            left_inv := by intro ⟨p, hp⟩; rfl
            right_inv := by intro q; rfl }
        rw [Fintype.card_congr e'']
        rw [Fintype.card_prod, Fintype.card_embedding_eq]
        rw [Fintype.card_fin, Fintype.card_fin]
        rw [← Fintype.card_subtype (fun σ : SymmetricGroup (n' + 1 - (d' + 1)) => Nat.lcm (d' + 1) (orderOf σ) = m)]
        have hsub_nat : (n' + 1 - (d' + 1)) = n' - d' := by omega
        have hcard : Fintype.card {σ : SymmetricGroup (n' + 1 - (d' + 1)) // Nat.lcm (d' + 1) (orderOf σ) = m} =
            Fintype.card {σ : SymmetricGroup (n' - d') // Nat.lcm (d' + 1) (orderOf σ) = m} := by
          exact Fintype.card_congr (Equiv.cast
            (congrArg (fun k => {σ : SymmetricGroup k // Nat.lcm (d' + 1) (orderOf σ) = m}) hsub_nat))
        rw [hcard]
        rfl

/-- `cycleLen π` divides `orderOf π`. -/
lemma cycleLen_dvd_orderOf (π : SymmetricGroup n) : cycleLen π ∣ orderOf π := by
  rw [orderOf_eq_lcm_cycleLen_residual]
  exact Nat.dvd_lcm_left _ _

/-- **Corollary 2.2, second statement**: `P(ord(πₙ) | m) ≤ τ(m)/n` for `m ≥ 1`. -/
theorem ord_dvd_prob_le_tau_div_n (m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π => orderOf π ∣ m)).card /
        (Nat.factorial n : ℝ) ≤ (m.divisors.card : ℝ) / (n : ℝ) := by
  classical
  let A := (Finset.univ : Finset (SymmetricGroup n)).filter (fun π => orderOf π ∣ m)
  let B := (Finset.univ : Finset (SymmetricGroup n)).filter (fun π => cycleLen π ∣ m)
  have hm0 : m ≠ 0 := by omega
  have hsub : A ⊆ B := by
    intro π hπ
    rw [Finset.mem_filter] at hπ ⊢
    exact ⟨hπ.1, dvd_trans (cycleLen_dvd_orderOf π) hπ.2⟩
  have hcardA : A.card ≤ B.card := Finset.card_le_card hsub
  have hcardB : B.card ≤ m.divisors.card * Nat.factorial (n - 1) := by
    have h := Finset.card_eq_sum_card_image (f := cycleLen) (s := B)
    rw [h]
    have hfiber : ∀ d ∈ B.image cycleLen,
        (B.filter (fun π => cycleLen π = d)).card ≤ Nat.factorial (n - 1) := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨π, hπ, hdeq⟩
      have hd1 : 1 ≤ d := by rw [← hdeq]; exact cycleLen_pos π
      have hdn : d ≤ n := by rw [← hdeq]; exact cycleLen_le π
      have hle' : (B.filter (fun π' => cycleLen π' = d)).card ≤
          ((Finset.univ : Finset (SymmetricGroup n)).filter (fun π' => cycleLen π' = d)).card := by
        refine Finset.card_le_card ?_
        intro π' hπ'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ π', (Finset.mem_filter.mp hπ').2⟩
      rwa [card_cycleLen_eq_factorial_pred d hd1 hdn] at hle'
    have hsumle : (∑ d ∈ B.image cycleLen, (B.filter (fun π => cycleLen π = d)).card) ≤
        ∑ d ∈ B.image cycleLen, Nat.factorial (n - 1) := by
      exact Finset.sum_le_sum (fun d hd => hfiber d hd)
    calc (∑ d ∈ B.image cycleLen, (B.filter (fun π => cycleLen π = d)).card)
        ≤ ∑ d ∈ B.image cycleLen, Nat.factorial (n - 1) := hsumle
      _ = (B.image cycleLen).card * Nat.factorial (n - 1) := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ m.divisors.card * Nat.factorial (n - 1) := by
          apply Nat.mul_le_mul_right
          exact Finset.card_le_card (by
            intro d hd
            rw [Finset.mem_image] at hd
            rcases hd with ⟨π, hπ, rfl⟩
            rw [Nat.mem_divisors]
            exact ⟨(Finset.mem_filter.mp hπ).2, hm0⟩)
  have hdiv : (A.card : ℝ) / (Nat.factorial n : ℝ) ≤
      ((m.divisors.card : ℝ) * (Nat.factorial (n - 1) : ℝ)) / (Nat.factorial n : ℝ) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hle : (A.card : ℝ) ≤ (m.divisors.card : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
      exact_mod_cast le_trans hcardA hcardB
    exact hle
  have hfac : (Nat.factorial n : ℝ) = (Nat.factorial (n - 1) : ℝ) * (n : ℝ) := by
    have h0 : Nat.factorial n = Nat.factorial (n - 1) * n := by
      rw [← Nat.mul_factorial_pred (n := n) (ne_of_gt (NeZero.pos n)), mul_comm]
    rw [h0, Nat.cast_mul]
  have hfinal : ((m.divisors.card : ℝ) * (Nat.factorial (n - 1) : ℝ)) / (Nat.factorial n : ℝ) =
      (m.divisors.card : ℝ) / (n : ℝ) := by
    rw [hfac]
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (NeZero.pos n))
    have hf : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by positivity
    field_simp [hn, hf]
  exact le_trans hdiv (le_of_eq hfinal)

end corollary22

end MostProbableOrder
