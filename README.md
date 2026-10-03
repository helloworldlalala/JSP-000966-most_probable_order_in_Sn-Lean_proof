# JSP-000966 — The most probable order of a random permutation (Lean formalization)

A complete, `sorry`-free formalization in Lean 4 / mathlib of

> **Beker**, *The most probable order of a random permutation*,
> [arXiv:2510.11698](https://arxiv.org/abs/2510.11698) (2025).

This repository formalizes the paper's main results, including **Theorem 1.2**
(the most probable order of a random permutation of `Sₙ` is `n − max Kₙ`) and
Proposition 4.1 (the local limit law with the error term `η(n,k)`), together
with the refined asymptotic `M(n) = 1/n + O(log n/n²)` of the paper's final
remark. Theorem 1.1 (the asymptotic `M(n) ∼ 1/n` and the characterization of
orders with `pₙ(m) ≥ 1/n`) is also formalized.

This is a submission to the Justin Sun Prize problem **JSP-000966**
(“Which element order is shared by the most permutations in a symmetric group?”).

## Statement of the main results

All statements live in namespace `MostProbableOrder`.

| Theorem (paper) | Lean name | File |
| --- | --- | --- |
| §1, formula (2) | `p`, `M`, `K` (definitions) | `MostProbableOrder/Basic.lean` |
| Theorem 1.1 (first statement) | `tendsto_n_mul_M_one` | `MostProbableOrder/Perm/Theorem11.lean` |
| Theorem 1.1 (characterization) | `p_ge_one_div_n_implies_mem_K` | `MostProbableOrder/Perm/Theorem11.lean` |
| Proposition 4.1 (`prop:exact_order`) | `prop_exact_order` | `MostProbableOrder/Perm/Warlimont.lean` |
| Theorem 1.2 (`thm:equality_case`) | `theorem_equality_case` | `MostProbableOrder/Perm/Warlimont.lean` |
| Remark (`rem:sharp_asymp`) | `M_sub_one_div_le_log` | `MostProbableOrder/Perm/Warlimont.lean` |

The key theorem (Theorem 1.2, the solution of JSP-000966):

```lean
theorem theorem_equality_case :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, p n m = M n ↔ m = n - k0 n
```

where `p n m` is the probability that a uniformly random permutation of `Fin n`
has order exactly `m` (a `Finset`-card ratio over `SymmetricGroup n`, no measure
theory), `M n` is the maximum of `p n m` over all orders `m ≤ n!`, `K n` is
`{k ∈ {0,…,n−1} | lcm(1,…,k) ∣ n−k}` (as in the paper, §2), and `k0 n = max K n`.

## Correspondence to the original problem

* The paper works over `Sₙ`, permutations of `[n]`; the formalization uses
  `Equiv.Perm (Fin n)` (`SymmetricGroup n`), with the order of a permutation
  given by `orderOf` (identified with the lcm of cycle lengths via
  `Equiv.Perm.lcm_cycleType`).
* All probabilities are exact `Finset.card` ratios over `ℝ`; the asymptotics are
  `Filter.Eventually` / `Filter.Tendsto` statements at `atTop`.
* Theorem 1.2 of the paper asserts `pₙ(m) = M(n) iff m = n − max Kₙ` for all
  sufficiently large `n`; this is `theorem_equality_case` verbatim.

## Build and verification

* Lean toolchain: `leanprover/lean4:v4.30.0` (see `lean-toolchain`)
* mathlib: pinned `rev = "v4.30.0"` in `lakefile.toml`
  (`lake-manifest.json` records the resolved commit)

```bash
lake exe cache get          # fetch mathlib oleans (optional, speeds up builds)
lake build                  # builds the whole project
```

All targets build with **no `sorry`, no `admit`, no custom `axiom`**.
An axiom audit of the main targets gives only the standard Lean axioms:

```
'MostProbableOrder.theorem_equality_case' depends on axioms: [propext, Classical.choice, Quot.sound]
'MostProbableOrder.prop_exact_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'MostProbableOrder.M_sub_one_div_le_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'MostProbableOrder.p_ge_one_div_n_implies_mem_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'MostProbableOrder.tendsto_n_mul_M_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Numerical sanity checks (`native_decide` only) live in
`MostProbableOrder/Checks.lean`, outside the default import chain.

## Project layout

* `MostProbableOrder/Basic.lean` — definitions `p`, `M`, `K`, `lcm1to`, basic facts
* `MostProbableOrder/Arithmetic/` — divisor bounds (τ/ω/σ), Euler bound Σ 1/p
* `MostProbableOrder/Perm/` — the main development:
  * `Decompose.lean`, `RestrictedBound.lean`, `Recursion.lean` — §2 (Cor 2.2)
  * `ErdosTuran.lean`, `CyclesAndPrimes.lean` — the exact product formula
  * `LargeOrders.lean`, `LargeOrders43.lean`, `LargeOrdersAsymptotic.lean` — §3 (Prop 3.1)
  * `Theorem11.lean` — Theorem 1.1
  * `Theorem12.lean` — η(n,k), equation (15), the key property, ν₂ analysis
  * `Warlimont.lean` — Proposition 4.1 (the Tᵢ decomposition), Theorem 1.2,
    and the final remark `M(n) = 1/n + O(log n/n²)`
* `docs/` — proof map and task plan; `reports/` — milestone reports

## Formalization author

ZouGuangjian

## License

Apache License 2.0 (same as mathlib); see `LICENSE`. The paper
[arXiv:2510.11698](https://arxiv.org/abs/2510.11698) is by N. Beker and is the
mathematical solution being formalized here.
