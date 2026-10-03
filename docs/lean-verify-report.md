# Lean verification report — JSP-000966 (PR #4695)

*Generated with the `lean-verify` skill (pre-submission self-check), 2026-10-04 (GMT+8). Report language: English (skill default).*

## Conclusion

> **Overall verdict: Verification passed.**
>
> For JSP-000966 ("Which element order is shared by the most permutations in a symmetric group?"), the Lean submission at proof-repository commit `59e3e1eaa15d25f04eb13e917ce3c241e62f4ede` **fully solves** the original problem. Decisive reason: the target `MostProbableOrder.theorem_equality_case` is Beker's Theorem 1.2 (arXiv:2510.11698) verbatim; at the pinned commit it was rebuilt from clean source in an isolated checkout with the pinned toolchain, all 7 targets (6 submitted theorems + 1 independent auditor bridge) pass `#print axioms` with only `[propext, Classical.choice, Quot.sound]`, kernel replay via `leanchecker` succeeds, and the independent bridge connects the original problem's mode-set reading to the submitted theorem.

| Required question | Explicit judgment | Decisive evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | **Yes** | Definitions `p`/`M`/`K`/`lcm1to`/`k0` audited line-by-line against the paper (Basic.lean:31-63, Theorem12.lean:228); `theorem_equality_case` (`Warlimont.lean:5281`) matches Theorem 1.2 verbatim (quantifier `∀ᶠ` = "sufficiently large", `∀ m`, equivalence, `n − k0 n` = `n − max Kₙ`); independent bridge `intended_mode_set` proves the mode-set reading of the original question from the submitted theorem |
| Did the specified commit actually pass verification? | **Yes** | Clean rebuild at `59e3e1e…` (LF sources = commit blobs, verified SHA256-equal) with Lean 4.30.0 / Lake 5.0.0: `lake build` → 3390 jobs, exit 0; `audit.py run` → mechanical status `standard_axioms_only`, exit 0, inputs stable; `leanchecker` kernel replay of `MostProbableOrder.Perm.Warlimont`, `…Theorems.Theorem11` and the bridge oleans → exit 0 each |
| Does it fully solve the original problem? | **Yes** | All six requirements (Theorem 1.2 mode identification, Theorem 1.1 asymptotics + characterization, Prop 4.1 local law, strict dominance, final remark) are covered by checked targets; no proof gap (`sorryAx` absent), no extra/circular assumptions, no native computation in the dependency chain |
| Does it meet the Lean completeness requirements for this verification? | **Meets** | Zero `sorry`/`admit`/custom `axiom` anywhere in `MostProbableOrder/`; `native_decide` appears only in `Checks.lean`, which imports only `MostProbableOrder.Basic` and is imported by nothing (outside the default import chain); all targets transitively depend only on the standard axioms |

Per-problem summary:

| Problem ID and name | Traceability | Statement correspondence | Unmodified build/target checks | Proof completeness | Full problem coverage | Verdict |
| --- | --- | --- | --- | --- | --- | --- |
| JSP-000966 (most probable order in Sₙ) | Verified (commit pinned, ancestor of main, PR head unchanged) | Matches (verbatim Theorem 1.2 + audited definitions) | Passed (clean rebuild 3390 jobs; 7/7 targets standard_axioms_only) | Complete (no sorryAx; standard axioms only) | Full (6/6 requirements covered) | Verification passed |

**Verification levels completed:** static review; actual Lean checks (clean build + explicit module/source checks + axiom audit); kernel replay (`leanchecker` on target oleans). **Not run:** independent challenge with an external comparator (no comparator configured in this environment); this does not affect the verdict because kernel replay plus the independent bridge and the transitive axiom audit cover the corresponding trust boundaries.

## Pinned evidence

- **Awards PR:** https://github.com/TheJustinSunPrize/awards/pull/4695 (state: open)
  - base: `TheJustinSunPrize/awards` `main` @ `e9e118d00022d693151d87af0c69d180dc5e5efd`
  - head: `helloworldlalala/awards` `jsp-000966-lean-proof` @ `17b006f780f1c2957883bb9abea0f25719a5ae51` — re-checked at end of audit: unchanged.
  - changed files: `problems/README.md` (+1/−1), `problems/catalog-0901-1000.md` (+1/−1) — only the `Lean proof` field No → Yes and the contributor credit; the problem description at base and head is identical (no narrowed/rewritten problem).
  - comments/reviews/inline comments at retrieval time: none. Evidence: `evidence/pulls_4695*.json` (retrieval time in `evidence/retrieval_time.txt`).
- **JSP entry (base):** `problems/catalog-0901-1000.md#JSP-000966` @ base SHA — "Which element order is shared by the most permutations in a symmetric group?", Group theory, Solved; Publication details: Beker, arXiv:2510.11698 (2025).
- **Original mathematical source:** Beker, *The most probable order of a random permutation*, arXiv:2510.11698. Theorem 1.2 (`thm:equality_case`): *"For all sufficiently large n, we have pₙ(m) = M(n) if and only if m = n − max Kₙ."* Also Theorem 1.1 (`thm:asymp_for_max`), Proposition 4.1 (local limit law for `pₙ(n−k)`), and remark `rem:sharp_asymp` (`M(n) = 1/n + O(log n/n²)`).
- **Lean proof repository:** https://github.com/helloworldlalala/JSP-000966-most_probable_order_in_Sn-Lean_proof
  - checked commit `59e3e1eaa15d25f04eb13e917ce3c241e62f4ede` (the full SHA pinned in the PR body and in the catalog entry); project root = repository root; claimed branch `main`.
  - `git cat-file -t` = commit; checkout HEAD matches; working tree clean; the checked commit **is an ancestor of `origin/main`** (`git merge-base --is-ancestor` exit 0).
  - `lean-toolchain`: `leanprover/lean4:v4.30.0`; `lakefile.toml` pins mathlib `v4.30.0`; `lake-manifest.json` resolves mathlib to `c5ea00351c28e24afc9f0f84379aa41082b1188f` (actual local checkout HEAD verified equal).
- **Revision conflicts:** none found between PR body, catalog entry, and the proof repository.

## Mathematical statement and coverage

Original problem: characterize the element order shared by the most permutations of Sₙ, i.e. the set of `m` attaining the maximum probability `M(n)`; solved by Theorem 1.2: for all sufficiently large `n`, `pₙ(m) = M(n) ⟺ m = n − max Kₙ`, with `Kₙ = {k ∈ {0,…,n−1} : lcm(1,…,k) ∣ n−k}` (paper §1–§2).

Lean correspondence (all at the pinned commit):

| Paper | Lean | Location |
| --- | --- | --- |
| Sₙ on [n] | `SymmetricGroup n := Equiv.Perm (Fin n)` | `Basic.lean:31` |
| `ord(π)` | `orderOf π`, identified with `π.cycleType.lcm` | `Basic.lean:42` |
| `pₙ(m) = P(ord(πₙ)=m)` | `p n m := #{π : orderOf π = m}/n!` | `Basic.lean:46` |
| `M(n) = maxₘ pₙ(m)` | `M n := fold max 0 over range (n!+1)` | `Basic.lean:52` |
| `lcm(1,…,k)` | `lcm1to k := (Icc 1 k).lcm id` | `Basic.lean:56` |
| `Kₙ` | `K n := (range n).filter (fun k => lcm1to k ∣ n − k)` | `Basic.lean:59` |
| `max Kₙ` | `k0 n := (K n).max' …` (n>0), 0 at n=0 | `Theorem12.lean:228` |
| Theorem 1.2 | `theorem_equality_case : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, p n m = M n ↔ m = n − k0 n` | `Warlimont.lean:5281` |
| Theorem 1.1 (asymptotics) | `tendsto_n_mul_M_one : Tendsto (fun n => (n:ℝ) * M n) atTop (𝓝 1)` | `Theorem11.lean:1316` |
| Theorem 1.1 (characterization) | `p_ge_one_div_n_implies_mem_K : ∀ᶠ n, ∀ m, 1/n ≤ p n m → (n − m ∈ K n) ∧ m ≤ n` | `Theorem11.lean:1157` |
| Proposition 4.1 | `prop_exact_order : ∃ C>0, ∃ N, ∀ n≥N, ∀ k∈K n, |p n (n−k) − (1/(n−k) + eta n k)| ≤ C/n^{5/2}` | `Warlimont.lean:4744` |
| Strict dominance step | `p_k0_gt_p_k : ∀ᶠ n, ∀ k, k ∈ K n → k < k0 n → p n (n−k) < p n (n−k0 n)` | `Warlimont.lean:5187` |
| Final remark | `M_sub_one_div_le_log : ∃ C>0, ∀ᶠ n, |M n − 1/n| ≤ C·log n/n²` | `Warlimont.lean:5450` |

Notes on boundary cases: `∀ᶠ` is the paper's "sufficiently large"; the equivalence direction and the single equality of the mode hold verbatim. For large `n`, `k0 n ∈ K n ⊆ range n`, so `n − k0 n` is the genuine positive difference (no truncation artifact). The probability is defined as an exact `Finset.card` ratio over ℝ — no measure-theoretic discrepancy with the paper's `P(ord(πₙ)=m)`. The group model `Fin n` (0-based) is isomorphic to the paper's `[n]`; the order distribution is identical.

**Independent bridge** (auditor-created, untracked harness `MostProbableOrder/Bridge/JSP000966Bridge.lean`, NOT part of the submission): defines `ModeSet n := {m | p n m = M n}` — the set of "orders shared by the most permutations" read directly off the original problem — and proves `intended_mode_set : ∀ᶠ n in Filter.atTop, ModeSet n = {n − k0 n}` from `theorem_equality_case`. Its own `#print axioms` is `[propext, Classical.choice, Quot.sound]` and its olean passes kernel replay.

Coverage matrix (requirements → targets, `audit/targets.json`):

| Requirement (original source) | Target | Coverage | Evidence |
| --- | --- | --- | --- |
| Theorem 1.2 mode identification (main problem) | `t-equality`, `b-mode` | full | declaration verbatim + independent bridge |
| Theorem 1.1: `M(n) ∼ 1/n` | `t-asymp` | full | `tendsto_n_mul_M_one` |
| Theorem 1.1: `pₙ(m) ≥ 1/n ⟹ m = n−k, k∈Kₙ` | `t-char` | full | `p_ge_one_div_n_implies_mem_K` |
| Proposition 4.1 local limit law | `t-prop41` | full | `prop_exact_order` (with `eta n k`, the paper's η-term) |
| Strict dominance `k<k₀ ⟹ p(n−k)<p(n−k₀)` | `t-dom` | full | `p_k0_gt_p_k` (assembles the paper's eq. (15) via `final_ineq`) |
| Remark `M(n) = 1/n + O(log n/n²)` | `t-remark` | full | `M_sub_one_div_le_log` |

## Environment and execution

| Item | Observed value and evidence |
| --- | --- |
| OS/architecture/isolation | Windows x86_64; isolated checkout under `%TEMP%\lean-verify-pr4695-20261004\sources\proof` (separate from the author's working tree; no credentials in the environment). Full container/VM isolation is unavailable on this machine — disclosed limitation; execution was confined to the fresh checkout with no writes to the author's tree. |
| Toolchain | `leanprover/lean4:v4.30.0` (pin); elan toolchain `leanprover--lean4---v4.30.0`, Lean 4.30.0 commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, Lake 5.0.0-src+d024af0 (paths recorded in `audit/check-02/version-*.log`) |
| Dependencies | `lake-manifest.json` hash recorded; mathlib resolved SHA `c5ea00351c28e24afc9f0f84379aa41082b1188f` — the isolated checkout's `.lake/packages/mathlib` HEAD verified equal; mathlib oleans taken from the official mathlib cache (`~/.cache/mathlib`, .ltar provenance) and the dependency-package checkouts copied from the author's local lake cache (each HEAD re-verified); dependency SHAs in `logs/` |
| Unmodified build | `lake build` in the isolated checkout after moving stale oleans aside (forces full re-elaboration of the project's own 18 files; mathlib/other dependencies reused trusted caches): **exit 0, 3390 jobs, ~9 min** (`logs/build3.log`) |
| Explicit target checks | `audit.py run` executed, per target: `lake build +Module`, `lake env lean <source>`, `lake env lean AuditXXXX.lean` (`#check @name` / `#print name` / `#print axioms name`) — all 7 targets passed (`audit/check-02/result.json`, exit 0) |
| Semantic bridges and axiom audit | bridge `MostProbableOrder.Bridge.JSP000966Bridge.intended_mode_set` checked by the script (standard axioms only) and kernel-replayed; per-target axiom lists: `['propext', 'Classical.choice', 'Quot.sound']` for every one of the 7 targets |
| Kernel/external cross-checks | `leanchecker` (Lean 4.30.0 built-in) replayed `MostProbableOrder.Perm.Warlimont`, `MostProbableOrder.Perm.Theorem11`, `MostProbableOrder.Bridge.JSP000966Bridge` oleans — exit 0 each, no problems reported. Independent challenge/comparator: not run (no comparator configured); recorded as a non-blocking gap |
| Post-run state | `git status` unchanged except the untracked harness `MostProbableOrder/Bridge/`; `audit.py` reports `inputs_stable: true`; PR head re-checked unchanged (`17b006f…`) |

Automation (`scripts/audit.py`, sha256 recorded in `result.json`): `mechanical_status: standard_axioms_only`, exit code 0, target-result counts match the manifest, inputs stable. This is mechanical evidence only; the semantic judgments above are the auditor's.

## Proof dependencies and gaps

- Keyword scan at the pinned commit (sources): **no** `sorry`, `admit`, or custom `axiom` in `MostProbableOrder/`; **no** `ofReduceBool`, `trustCompiler`, `debug.skipKernelTC`, `implemented_by`, `extern`.
- `native_decide` occurs only in `MostProbableOrder/Checks.lean` (numeric sanity checks T1–T5), which imports only `MostProbableOrder.Basic` and is imported by **no** module — it is outside the default import chain and outside every target's dependency path. No target trusts native computation.
- `#print axioms` for every target and the bridge: `[propext, Classical.choice, Quot.sound]` — the standard classical Lean foundations, no `sorryAx`, no custom axioms.
- Repository-wide warnings (e.g. `exponentiation.threshold`, `linter.unnecessarySimpa` in `DivisorBounds.lean`) are linter/style notices on lemmas outside the targets' trusted chain of concern; none indicates a proof gap.
- Extended trust: mathlib v4.30.0 (pinned, official cache) and the standard axioms; no native computation; kernel replay performed. Comparator-level external checking not configured — does not affect the verdict.

## Findings, limitations, and next steps

1. **No defects found.** All checks passed; statement correspondence is verbatim; no proof gaps.
2. **Limitation (environment):** no container/VM isolation — execution was confined to a fresh isolated checkout; the author's tree and credentials were not involved. The mathlib/dependency oleans were reused from official/trusted local caches with SHA verification (a full from-scratch mathlib rebuild was impractical offline).
3. **Limitation (tooling):** no external comparator challenge was configured; kernel replay (`leanchecker`) plus the independent bridge and full axiom audit were performed instead.
4. **Next step for the awards maintainers:** review the PR in its normal process; nothing further is required from the verification side.

## Reproducible artifacts

- `evidence/` — PR API snapshots (`pulls_4695*.json`), PR body, retrieval time.
- `audit/targets.json` (7 targets, 6 requirements), `audit/preflight-02/`, `audit/prepared-01/`, `audit/check-02/` (full `audit.py` results incl. per-target axiom logs and the generated `AuditXXXX.lean` files).
- `sources/proof/` — isolated checkout at `59e3e1eaa15d25f04eb13e917ce3c241e62f4ede` + untracked harness `MostProbableOrder/Bridge/JSP000966Bridge.lean`.
- `logs/` — `build3.log` (clean rebuild), version logs, checker logs.
- Reproduction commands (from `sources/proof`): `lake build` (after `lake exe cache get` or cache reuse); `python3 scripts/audit.py run audit/targets.json --out audit/check-NN --lake <abs path>/lake.exe --timeout 900`; `LEAN_PATH=$(lake env printenv LEAN_PATH) leanchecker MostProbableOrder.Perm.Warlimont` (in `.lake/build/lib/lean`).
