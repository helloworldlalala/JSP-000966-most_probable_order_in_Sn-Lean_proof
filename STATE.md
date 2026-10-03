# STATE — 更新于 2026-10-03, 会话 #5

```
env: lean 4.30.0 / mathlib v4.30.0 (rev c5ea003) / 缓存完好 ✅ (lake build Mathlib.* 秒级)
milestones: [M0✅ M1✅ M2✅(5/5 sorry 清零) M3✅ M4✅ M5✅ M6✅ M7✅ M8✅ M8b✅ M8c✅ M9✅ M10a✅ M10b✅ M10c✅ M10d✅ M10e✅ M10✅]
current: 全部完成 ✅ —— 项目零 sorry，`lake build` 3390 jobs 全绿。
  **第十二轮（2026-10-03，Remark `rem:sharp_asymp`）**：**论文最后一段正式陈述 M(n)=1/n+O(log n/n²) 落地（`M_sub_one_div_le_log`，全零 sorry）**：
  `lcm1to_eq_lcmUpto`（= mathlib `Nat.lcmUpto` rfl 桥接）/`two_pow_le_mul_lcm1to`（二项式下界 2^k≤(k+1)lcm(1..k)，Farhi，**论文 PNT 的初等替代**）/`log_two_sq_le_two_mul_add_one`/`k_le_two_log2_add_one_of_mem_K`（k∈Kₙ ⟹ k≤2log₂n+1）/`k0_le_two_log2_add_one`/`four_mul_log2_add_four_le`（4log₂n+4≤2^{log₂n}≤n，归纳）/`two_mul_log2_add_one_le_half`/`k0_le_half`（k₀≤n/2）/`natLog_two_le_two_log`（Nat.log 2 n ≤ 2·Real.log n，log 2>1/2）/`M_sub_one_div_le_log`（常数 C=15，分解 M=p(n−k₀)=1/(n−k₀)+η+O(n^{−5/2})，η≤4/n²，(n−k₀)⁻¹−n⁻¹=k₀/(n(n−k₀))≤2(2log₂n+1)/n²）。
  **第十一轮（2026-10-03，收官）**：**MP-008 解除 + Theorem 1.2 完整落地（全零 sorry）**：
  `restProb_le_T_parts`（restProb ≤ T₀+T₁+T₂s+T₂r+T₃₊，经 `sum_eq_filter_card_parts` 分解 + filter 子集/相等 + `Finset.sum_filter_add_sum_filter_not`）；
  **`prop_exact_order`**（Prop 4.1：|p(n−k)−(1/(n−k)+η)|≤C·n^{−5/2}，组装 Tᵢ 界 + η 双侧（`eta_le_special_add_ge_three`）+ abs_le，常数 C₀=4⁴⁵+C^{1/20}4⁴⁵+C^{1/10}24⁴⁵+2C^{3/20}）；
  **`p_k0_gt_p_k`**（k∈Kₙ,k<k₀ ⟹ p(n−k)<p(n−k₀)：prop_exact_order + `final_ineq` + n≥16C² ⟹ 2C·n^{−5/2}≤(1/2)·n^{−2}）；
  **`theorem_equality_case`**（Theorem 1.2：`∀ᶠ n, ∀m, p n m = M n ↔ m = n−k0 n`，正反向 + `Finset.le_fold_max` 达到性 + `p_ge_one_div_n_implies_mem_K` 表征）。
  此前各轮（Tᵢ 分解全链）：
  **本轮新增（2026-10-03，第六轮）**：**「无长圈」界完整落地（T₀≤F 的深件，用初等实点系数界替代 Cauchy 围道，零 sorry）**：
  `countVec`/`nuTerm`/`countVec_injective`/`countVec_mem_range`（计数向量框架）；
  `sum_eq_sum_count_mul`/`prod_eq_prod_count_pow`/`count_le_sum`（multiset↔toFinset）；
  `sum_count_mul_eq_sum`/`prod_count_pow_eq_prod`/`prod_count_factorial_eq`/`prod_count_pow_eq_prod_real`（Fin(r-1)≃Icc 2 r 双射）；
  `prod_inv_count_eq` + **`cycleTypeWeight_eq_prod_countVec`**（组合恒等式 w(λ)=∏ 1/((j+1)^count·count!)）+ **`pow_mul_cycleTypeWeight_eq_prod`**（xⁿ·w=∏nuTerm）+ **`nuNoLong_le_exp_bound`**（ν(n,r)≤x⁻ⁿ·exp(Σ_{j:Fin r} x^{j.val+1}/(j.val+1))，主定理）。
  **第七轮**：`harmonic_le_log`（`Σ_{j=1}^r 1/j ≤ 1+log r`，逐项 `Real.one_sub_inv_le_log_of_pos` + 望远镜 `Icc 2 r = Ico 2 (r+1)` + `sum_Ico_eq_sum_range` + `sum_range_sub`）。
  **第八轮（2026-10-03）**：**ν 实例化完成（无长圈概率 = O(n⁻³) 全链零 sorry）**：
  `tendsto_rpow_neg_nat_atTop`/`log_le_c_mul_pow15`/`exp_two_pow_neg_le_two`/`exp_neg_half_pow15_le`/`one_add_log_two_le_pow15_div_eight`/`sum_fin_inv_add_one_eq`/`exp_sum_fin_le_half_pow15`（Σ_{j<r} exp(n^{-14/15})^{j+1}/(j+1) ≤ n^{1/15}/2）/**`nuNoLong_bound`**（`∀ᶠ n, nuNoLong n ⌈n^{9/10}⌉₊ ≤ 2^45/n³`）。至此 T₀≤F(n,k) 的「无长圈」深件已用**初等实点系数界**完全替代（x=exp(n^{-14/15})，不需 Cauchy 围道/复分析）。
  **第九轮（2026-10-03）**：**均匀残差 ν 界（T₁/T₂ 前置）**：`exp_neg_quarter_pow15_le`/`one_add_log_two_le_pow15_div_sixteen`/`exp_sum_fin_le_quarter_pow15`/**`nuNoLong_le_const_div_cube_uniform`**（`∀ᶠ n, ∀ m, n≤2m → m≤n → ν(m,⌈n^{9/10}⌉)≤4^45/n³`，用 x=exp(n^{-14/15}) 统一残差）。
  **第十轮（2026-10-03）**：**T₂ 残差 m≥n/6 的 ν 界 + Tᵢ 分解起点**：`exp_neg_div_pow15_le`（参数化衰减）/`exp_sum_fin_le_eighth_pow15`/**`nuNoLong_le_const_div_cube_uniform_sixth`**（m≥n/6，T₂ 非特殊项残差 n-d₁-d₂≥n/6 的界）；组合件 `large n d` + `sum_cycleTypeWeight_add_le_nu`（精化解耦 Σ_S w_n(L+S)≤(1/L.prod)ν(n-L.sum,r)）。
  剩余（纯组合组装，已全部完成）：① λ↔(filter large, filter ¬large) 分解 ✅；② T₀/T₁/T₂_rest/T_{≥3} 界 + #{大除数}≤τ ✅；③ 特殊项=η ✅；④ 组装删 MP-008 ✅（见第十一轮）。
  M10a **Cauchy 表示**：`cycleTypes`/`cycleTypeWeight`/`cycleTypeWeight_eq_prob`/`card_orderEq_eq_sum_fiber`/**`p_eq_sum_cycleType`**（P(ord=m)=Σ_{λ:lcm λ=m} w_n(λ)，Ford Thm1.2=`card_of_cycleType`）。
  M10b **主项 1/(n-k)**：`cycleTypeWeight_cons_eq`/`sum_cycleTypeWeight_eq_one`/**`sum_cycleTypeWeight_of_mem_nk`**（Σ_{λ,n-k∈λ} w_n(λ)=1/(n-k)）。
  M10c **解耦框架**：`cycleTypeWeight_add_eq` + `sum_cycleTypeWeight_add_le`（Σ_S w_n(L+S)≤1/L.prod）。
  M10d **阈值/除数界**（δ=1/10，阈值 n^{9/10}，权重 n^{-9/10}）：`tau_le_rpow_sixteenth`/`tau_sub_le`/`one_div_le_rpow_neg`/`prod_le_rpow_of_large`/`inv_prod_le_rpow_of_large`/`dvd_lcm_of_mem_cycleType`。验算：Σ_{i≥3}Tᵢ≤(C^{1/16}n^{1/16}·n^{-9/10})³=C^{3/16}n^{-201/80}<C n^{-5/2}。
  全量 lake build 3390 jobs 通过；MP-008 已于第十一轮解除，grep sorry/admit/axiom 零命中。
open_sorries: 0 ✅（MP-008 已解除；`grep sorry/admit/axiom` 零命中，`native_decide` 仅 Checks.lean 白名单）
blockers: 无
next_3: ① （已完成）Tᵢ 求和全链 + prop_exact_order + p_k0_gt_p_k + theorem_equality_case
  ② （已完成）M10 审计闸门：`lake build` 3390 jobs 全绿；SORRY.md/STATE.md 更新
  ③ 可选后续：Remark 最优性半句（n=lcm(1..k)+k 构型的 Θ 下界）、Checks.lean 小 n 反例检验扩展
conventions:
  - 概率一律 ℝ 上 Finset.card 比值；禁用 MeasureTheory
  - ω(m) := m.primeFactors.card；τ(m) := m.divisors.card；σ(m) := ∑_{d|m} d
    （另有 sigma_eq_sigma_one 桥接 ArithmeticFunction.sigma 1，以复用乘法性）
  - 定义层全 ℝ；ℕ→ℝ cast 用 (x : ℝ) 显式标注；实数幂用 Real.rpow（需 import Pow.Real）
  - 中间引理常数数值化（C₁=100 等）/ 或 ∃C 形式；顶层用 Asymptotics/Tendsto
  - 计数桥接 `#({g | p g} : Finset α) = (univ.filter p).card` 可 rfl
  - 阶 = 轮型 lcm（`Equiv.Perm.lcm_cycleType`）；n-圈计数 `Equiv.Perm.card_of_cycleType_singleton`
  - full n-圈用 `finRotate`（+`isCycle_finRotate_of_le`/`support_finRotate_of_le`）
  - factorial：`Stirling.le_factorial_stirling` / `Stirling.le_log_factorial_stirling`
  - 数值 native_decide 只准放 MostProbableOrder/Checks.lean（不进根 import 链）
  - 每个新模块必须登记到根文件 MostProbableOrder.lean（防 lake 静默漏编）
  - lakefile.toml defaultTargets=["MostProbableOrder"]（无参 lake build 可用）
  - Mertens/Abel：θ 上界用 `Chebyshev.theta_le_log4_mul_x`；`θ x = ∑_{p≤x} log p` 用 `Chebyshev.theta_eq_sum_primesLE_log`
  - 分部求和用 `Finset.sum_Ioc_by_parts`；telescoping 自证 `sum_Icc_sub_telescope`
  - `Real.log` 满足 `log(-x)=log x`，故 `Real.log_pow` 无正性假设
  - 圈删除双射已落地：`cycleRemovalEquiv`（正向 tupleOf/residualFwd，逆向 cycleThroughZero/liftResidual）
  - 子类型对齐用 `Equiv.subtypeEquivRight` + `ofSubtype_permCongr_subtypeEquivRight`；off-by-one 用 `cases n; cases d`
```

## 模块进度

- M1：`MostProbableOrder/Basic.lean`（零 sorry）。
- M2a：`MostProbableOrder/Arithmetic/FactorialBounds.lean`（零 sorry）：
  `pow_div_exp_le_factorial`（(k/e)^k≤k!）、`log_factorial_lower`、`geom_sum_le_inv_one_sub`。
- M2b：`MostProbableOrder/Arithmetic/DivisorBounds.lean`（**零 sorry，全部 5 条接口解除**）：
  定义 tau/omega/sigma；已证 `two_le_of_mem_primeFactors`、`pow_two_omega_le`、`omega_le_log_two`、
  `omega_le_log_div_loglog`（MP-003）、`tau_pow_sixteen_le`（MP-002）、
  `sum_log_div_primes_le`（Mertens 第一定理）、`sum_inv_primes_le`（MP-005，Euler Σ1/p）、
  `sigma_div_le_loglog`（MP-004，Gronwall 界，经 Euler 乘积 + 三重 log 拆分和）。
- M3：`MostProbableOrder/Perm/Decompose.lean`（**零 sorry，全部完成**）：
  `cycleLen`/`cycleLenAt`（+ `orderOf_cycleOf_eq_cycleLen`/`..._At`、`cycleLenAt_pos`）；
  Feller 插入原语 `insertArc`/`insertNone` + `deleteZero` + 反演引理 + **`fellerEquiv`（Feller 双射）**；
  `cycleLen_insertNone`、**`cycleLen_insertArc`**（轨道论证）；
  `orderOf_insertNone`；**圈删除分解** `cycleLen_eq_card_sameCycle`/`card_complement_sameCycle`/
  `cyclePerm`/`residualSubtype`/`residual`；**阶分解** `decompose_mul`/`disjoint_cyclePerm_residual`/
  `ofSubtype_cyclePerm`/`orderOf_ofSubtype_cyclePerm`/`orderOf_residual`/`orderOf_ofSubtype_residual`/
  **`orderOf_eq_lcm_cycleLen_residual`**；
  **圈双射脚手架**：`orbitEquiv`、`cycleThroughZero`（+apply 引理）、`finRotate_sameCycle_all`、
  `sameCycle_cycleThroughZero_iff`、**`cycleLen_cycleThroughZero`**；
  **圈删除双射** `cycleRemovalEquiv`（+ `sameCycle_cycleOf_iff`/`sameCycle_iff_complementPred`/
  `complementSubtypeEquiv`/`ofSubtype_permCongr_subtypeEquivRight`/`cycleThroughZero_iterate_apply`/
  `residualFwd`/`liftResidual_residualFwd`/`tupleOf_mul_liftResidual`/`residualFwd_mul_liftResidual`/
  `cycleThroughZero_tupleOf_lift`/`orderOf_residualFwd`/`orderOf_eq_lcm_cycleLen_residualFwd`）；
  **MP-006 解除** `card_cycleLen_eq_factorial_pred`（均匀圈长 #{cycleLen=d}=(n-1)!）；
  **MP-007 解除** `card_cycleLen_orderOf_eq`（阶过滤计数）；
  **Cor 2.2 两个陈述**：`cycleLen_dvd_orderOf` + `ord_dvd_prob_le_tau_div_n`（P(ord|m) ≤ τ(m)/n）。
- M4：`MostProbableOrder/Perm/Restricted.lean`（**零 sorry，第一部分完成**）：
  定义 `numCycles`/`cycleLength`/`IsRestricted`（+`instDecidableIsRestricted`）；
  permCongr 不变性 `support_permCongr`/`card_support_permCongr`/`permCongr_zpow_apply`/`sameCycle_permCongr`/
  `isCycle_permCongr`/`disjoint_permCongr`/`cycleType_permCongr`/`numCycles_permCongr`/`cycleLength_permCongr`/`IsRestricted_permCongr`；
  圈删除分解 `cycleLength_eq_cycleLen`/`cycleLength_eq_of_sameCycle`/`cycleLength_residualSubtype`/
  `cycleType_cycleOf`/`IsRestricted_residualSubtype`/`numCycles_cycleOf`/`numCycles_residualSubtype`；
  传输 `numCycles_residualFwd`/`IsRestricted_residualFwd`；
  **计数递推** `card_cycleLen_numCycles_IsRestricted`（含 `[1≤ℓ]`）。
- `MostProbableOrder/Checks.lean`（不进默认 import 链）：T4a/b/c、T5a 数值检验。
- M5：`MostProbableOrder/Perm/ErdosTuran.lean`（**零 sorry**）：
  `dvd_lcm_iff_of_isPrimePow`（素幂 q：q|lcm a b ↔ q|a ∨ q|b，经 factorization_lcm + pow_dvd_iff_le_factorization）；
  `orderNotDivByCount`/`orderNotDivByProb`；**圈删除递推** `card_cycleLen_orderNotDivBy`/`card_orderNotDivBy_rec`（cycleRemovalEquiv + orderOf_eq_lcm_cycleLen_residualFwd）；
  **概率递推** `orderNotDivByProb_rec`（p(n)=(1/n)Σ[q∤d]p(n-d)，descFactorial_div_factorial + sum_div）；
  Nat 除法 `nat_div_sub_one`/`div_eq_pred_div_of_not_dvd`（Nat.succ_div）/`div_eq_pred_div_add_one_of_dvd`；
  **乘积** `erdosTuranProd q n`（block 形式 ∏_{j∈range(n/q)}(1-1/((j+1)q))）；
  `erdosTuranProd_eq_pred_of_not_dvd`/`erdosTuranProd_div`（增量）/`erdosTuranProd_telescope`/`sum_telescope`/**Identity1** `sum_erdosTuranProd_pred`；
  **Reversal** `sum_erdosTuranProd_reversal`（full_reversal + excluded：`sum_if_dvd_mul`（sum_filter+sum_bij 反演 d↦q·j）+ `erdosTuranProd_sub_mul`/`erdosTuranProd_pred_mul`（block 平坦）+ `sum_range_reflect`）；
  **主定理** `orderNotDivByProb_eq_erdosTuranProd`（强归纳 + 递推 + reversal + Identity1）。
  **eq:approx_prob 界**：`one_sub_prod_le_sum`（Weierstrass 乘积不等式 1-∏(1-f)≤Σf，Finset 归纳 + prod_le_one）+ `one_sub_prod_ge_single`（单因子下界 f a ≤ 1-∏(1-f)，mul_prod_erase）+ `invMul`/`invMul_nonneg`/`invMul_le_one`（因子 1/((j+1)q) 的 [0,1] 性）+ `one_sub_erdosTuranProd_le_sum_inv`（上界）+ `one_div_q_le_one_sub_erdosTuranProd`（下界，n≥q）+ `erdosTuran_approx_prob`（合并 1/q ≤ P(q|ord) ≤ Σ1/(jq)）。
- M6：`MostProbableOrder/Perm/Feller.lean`（**零 sorry**）：
  `Multiset.card_le_sum_of_pos`（各元素≥1 则 card≤sum，Multiset 归纳）；`cycleLength_le`（Fintype.card_subtype_le）；`numCycles_le`（card≤sum + Nat.add_sub_of_le）；`IsRestricted_Icc_self`；`cardNumCyclesRestricted_Icc_self`（I=[1,n] 时 IsRestricted 恒真，simp）；`sumInv_Icc_le_one_add_log`（harmonic_eq_sum_Icc + harmonic_le_one_add_log）；`numCycles_prob_le`（Lemma 2.3 + I=[1,n] 逐点界）；`numCycles_prob_le_half`（几何形 (1/2)^{ℓ-1}/n，Stirling pow_div_exp_le_factorial + div_le_div_of_nonneg_left）；**`numCycles_tail_le`**（上尾 P(c≥L)≤2(1/2)^{L-1}/n，card_eq_sum_card_image 按 numCycles 划分 + sum_subset + geometric geom_sum_le_inv_one_sub）。
- M7：`MostProbableOrder/Perm/CyclesAndPrimes.lean`（**零 sorry**）：
  素幂分解 `ppow`/`ppowIrr`（@[irreducible] 防 sum_fiberwise whnf 非终止）、`prod_dvd_iff_of_pairwise_coprime`、`dvd_iff_ppow_dvd_of_primeFactors`、`dvd_lcm_iff_uncovered_dvd`（首圈未覆盖的素幂才留给剩余）；计数递推 `countCyclesOrderDiv_zero/one/fiber/rec`；子集划分 `card_filter_dvd_Icc`（#{d∈[1,N]:Q|d}=N/Q）+ `sum_powerset_card_pow`（二项式）+ `sum_covered_mul_pow_card_le`；**主定理** `countCyclesOrderDiv_mul_le`（Nat 核）与 **Lemma 2.5** `cyclesAndPrimes_prob_le`（P(c=ℓ, m|ord) ≤ ℓ^ω(m)/m）。
- M8：`MostProbableOrder/Perm/LargeOrders.lean`（**零 sorry**）：
  事件 `prob_E1/E2/E3`；`one_le_numCycles_of_pos`；**disjoint 分解** `card_orderEq_eq_sum_E1_E2_E3` + `p_eq_E1_add_E2_add_E3`（需 L₁≤L₂）；**E₃ 上尾** `prob_E3_le ≤ 2(1/2)^{L₂}/n`（M6 numCycles_tail_le）；**E₁ 界** `prob_E1_le ≤ L^{ω(m)+1}/m`（Lemma 2.5 逐项 + `sum_Icc_pow_le` + 纤维划分 `card_orderEq_numCycles_le_fiber`）；**E₂ 界** `prob_E2_le ≤ L₂(1/2)^{L₁}/n`（Cor 2.4 `prob_numCycles_orderOf_dvd_le` + Stirling `inv_factorial_le`（1/k!≤(e/k)^k）+ `E2_summand_le`，条件 2e·σ(m)≤L₁·m）；**master** `p_le_master`。
- M8b：`MostProbableOrder/Perm/LargeOrdersAsymptotic.lean`（**零 sorry，已完成**）：
  衰减引理 `tendsto_logloglog_div_loglog_zero`（logloglog n/loglog n→0，Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero 复合 log∘log）、`tendsto_half_pow_nat_zero`（(1/2)^n→0，tendsto_pow_atTop_nhds_zero_of_norm_lt_one）、`tendsto_log_div_nat_zero`（log n/n→0）、`tendsto_Natlog_atTop_nat`（Nat.log 2 n→∞，Nat.le_log_of_pow_le）、`tendsto_half_pow_log2_nat_zero`（E₃ 衰减 (1/2)^{Nat.log 2 n}→0）；**主定理 `prop_large_orders`**（ε=1/2：`n^{3/2}≤m → n·p≤1/2`）含阈值条件/E₁ 一致界 `eventually_E1_term_le`（L₁^{ω+1}/m≤n^{-5/4}）/E₂ σ 条件 `eventually_hE2`/case split `p_eq_prob_E3_of_lt`/`orderOf_le_pow_numCycles`。
- M8c（进行中）：Theorem 1.1 基础件（全零 sorry）：
  - `MostProbableOrder/Perm/Recursion.lean`：Cor 2.2 第一陈述 `p_eq_sum_recursion`（`card_orderEq_eq_sum_lcm` + `lcmOrderCount/Prob` + `descFactorial_mul_div_factorial_eq`）。
  - `MostProbableOrder/Perm/LargeOrders43.lean`：Prop 3.1 ε=1/3 版 `prop_large_orders_43`（阈值 n^{4/3}，E₁ 界 L₁^{ω+1}/m≤n^{-79/72}）。
  - `MostProbableOrder/Perm/Theorem11.lean`：`mul_le_lcm_mul_sub`/`lcm_le_of_dvd`/`rpow_four_third_lt_sq_sub_sqrt_div_sqrt`/`p_ge_one_div_n_implies_not_rpow_four_third`/`tau_sq_le_rpow_eighth`/`tau_sq_le_of_lt_rpow_four_third`/`eventually_tau_sq_div_n_pow_three_half_le`/`tau_sq_div_n_pow_three_half_le_rpow`/`nat_sqrt_le_real_sqrt`/`sqrt_le_two_mul_nat_sqrt`/`div_le_lcm_of_mul_le`/`sq_sub_sqrt_div_sqrt_lt_div`/`two_divisors_contradict`/`lcmOrderProb_le_tau_div`/`lcmOrderProb_eq_zero_of_not_dvd`/`sum_small_lcmOrderProb_le`/`lcmOrderProb_le_one`/`large_d_gt_sub_sqrt`/`card_filter_large_dvd_le_one`/`dvd_orderOf_of_lcm_eq_of_dvd`/`not_dvd_orderOf_of_lcm_eq_of_not_dvd`/`count_orderNotDiv_le_count_lcm_ne_of_dvd`/`count_orderDiv_le_count_lcm_ne_of_not_dvd`/`one_sub_lcmOrderProb_eq`/`one_sub_orderNotDivByProb_eq`/`min_orderNotDivByProb_le_one_sub_lcmOrderProb`/`p_le_sum_large_add_tau_sq_div`/`sum_large_eq_filter_dvd`/`n_sub_d_le_two_mul_tau_of_lcmOrderProb_ge`/`log_le_two_sqrt`/`sqrt_le_div_five_of_ge_25`/`one_add_log_div_lt_half_of_ge_25`/`le_24_of_one_add_log_div_ge_half`/`sum_inv_jq_le_one_add_log_div_q`/`dvd_lcm1to_iff_prime_pow_dvd`/`exists_prime_pow_not_dvd_of_not_dvd_lcm1to`/`orderOf_dvd_lcm1to`/`exists_of_lcmOrderProb_pos`/`m_eq_d_of_lcm1to_dvd`/`orderNotDivByProb_ge_inv_factorial`/`lcm1to_dvd_of_large_prob`/`tau_le_rpow_twelfth`/`tau_sq_div_n_sqrt_le`/`exists_large_divisor_of_sum_pos`/`exists_of_p_pos`/`mem_K_of_p_ge`（返回 `(n-m∈Kₙ) ∧ m≤n`）/**`p_ge_one_div_n_implies_mem_K`**（返回 `(n-m∈Kₙ) ∧ m≤n`）/`sum_large_le_one`/`p_eq_zero`/`p_self_le_M`/`n_mul_p_le_large_add_tau`/`tau_sq_div_sqrt_le`/`eventually_n_mul_p_le_one_add`/`one_div_le_M`/**`tendsto_n_mul_M_one`**。
- M9：`MostProbableOrder/Perm/Theorem12.lean`（**除 `prop_exact_order`(MP-008) 一处 sorry 外全零 sorry**）：
  `eta`（η(n,k) 定义）/`eta_eq_zero_of_le_one`/`eta_eq_zero_of_dvd`/`eta_nonneg`/`eta_le_inv_sq`；
  **`final_ineq`**（论文 (15)：`(k₀-k)/((n-k₀)(n-k)) + η(n,k₀) - η(n,k) ≥ 1/(n-k)²`）；
  **`orderOf_eq_of_cycleLen`**（论文 line 96「key property」：k∈Kₙ 时 0 所在圈长为 n-k ⟹ ord = n-k，经 `orderOf_eq_lcm_cycleLen_residual` + `orderOf_dvd_lcm1to` + `Nat.dvd_antisymm`）；
  **`two_pow_log2_dvd_of_mem_K`**/`padicValNat_two_le_log2`/`padicValNat_nk_eq_log2_of_not_two_pow_succ_dvd`（论文 line 281–282 的 ν₂ 赋值分析：ν₂(n-k)≥⌊log₂k⌋、ν₂(t)≤⌊log₂k⌋、η≠0 时 ν₂(n-k)=⌊log₂k⌋ 精确）；
  **`prop_exact_order`**（Prop 4.1，sorry，MP-008）；
  **`p_k0_gt_p_k`**（k₀ 严格支配较小 k）；`K_nonempty`/`k0`/`k0_mem_K`/`le_k0`/`p_le_M`；
  **`theorem_equality_case`**（Theorem 1.2：`∀ᶠ n, ∀m, p n m = M n ↔ m = n - k0 n`）。
- M10a/b/c：`MostProbableOrder/Perm/Warlimont.lean`（**零 sorry**，Warlimont Tᵢ 分解根基）：
  `cycleTypes`/`cycleTypeWeight`/`mem_cycleTypes_sum_le`/`mem_cycleTypes_two_le`/`mem_cycleTypes_cons`/`mem_cycleTypes_erase`/`cycleTypeWeight_eq_prob`/`card_filter_orderOf_cycleType`/`card_orderEq_eq_sum_fiber`/**`p_eq_sum_cycleType`**（Cauchy 表示）；
  `cycleTypeWeight_cons_eq`/`sum_cycleTypeWeight_eq_one`/**`sum_cycleTypeWeight_of_mem_nk`**（主项 1/(n-k)）；
  `cycleTypeWeight_add_eq`/`sum_cycleTypeWeight_add_le`（解耦框架）。
- 全量 `lake build` 3390 作业通过；`grep sorry/admit/axiom` **仅剩 `prop_exact_order`（MP-008）一处**。
