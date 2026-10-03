import MostProbableOrder.Basic

/-!
# Numerical sanity checks (T1–T5)

This file is **not** part of the default import chain (the root module
`MostProbableOrder.lean` does not import it). It is the only place where
`native_decide` / `#eval` are permitted, per the project's zero-`sorry`
audit rules (see `SORRY.md`, `docs/TASK_PLAN.md`).

Build explicitly with `lake build MostProbableOrder.Checks`.

Note: `orderOf` is `noncomputable`, so the checks phrase orders through the
computable `Multiset.lcm` of the cycle type; the bridge is exactly the lemma
`order_eq_lcm_cycleType`.
-/

open Finset

namespace MostProbableOrder

/-- T4a (`n = 4`): there are `(4-1)! = 6` permutations of `Fin 4` of cycle
type `{4}` (single 4-cycles). Cross-checks `card_cycleType_singleton`. -/
example :
    ((Finset.univ : Finset (SymmetricGroup 4)).filter
      (fun π => π.cycleType = ({4} : Multiset ℕ))).card = 6 := by
  native_decide

/-- T4b (`n = 4`): the number of permutations whose order (`= cycleType.lcm`)
is exactly `4`. The 4-cycles contribute 6, and the double transpositions have
order 2, so the total is 6; hence `p₄(4) = 6/24 = 1/4` (equality in (2) here). -/
example :
    ((Finset.univ : Finset (SymmetricGroup 4)).filter
      (fun π => π.cycleType.lcm = 4)).card = 6 := by
  native_decide

/-- T4c (`n = 6`): an instance where the inequality in (2) is **strict**.
Permutations of order 6 (i.e. `cycleType.lcm = 6`) are exactly those of cycle
type `{6}` (`5! = 120`) and of cycle type `{2,3}` (one 2-cycle and one 3-cycle:
`6!/(2·3) = 120`), for a total of `240`. Hence `p₆(6) = 240/720 = 1/3 > 1/6`. -/
example :
    ((Finset.univ : Finset (SymmetricGroup 6)).filter
      (fun π => π.cycleType.lcm = 6)).card = 240 := by
  native_decide

/-- T5a: `K₁₂ = {0,1,2}`. Here `lcm1to k = lcm(1,…,k)` equals
`1,1,2,6,12,60,60,420,840,2520,2520,27720` for `k = 0,…,11`, and the condition
`lcm1to k | 12 - k` holds exactly for `k = 0, 1, 2`. -/
example : K 12 = {0, 1, 2} := by
  native_decide

end MostProbableOrder
