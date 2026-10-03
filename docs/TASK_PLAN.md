# 任务规划书 — most_probable_order Lean 4 形式化

总目标：完整形式化 Beker (2025) 全部证明，最终零 sorry、零自定义 axiom、`lake build` 通过。

## 执行记录

| 里程碑 | 内容 | 状态 | 报告 |
|---|---|---|---|
| M0 | 环境搭建（lakefile.toml/根文件/缓存验证/文档骨架） | ✅ 2026-09-30 | reports/阶段工作报告_#01.md |
| M1 | Basic 层修订 + p n n ≥ 1/n + PROOF_MAP 交付 | ✅ 2026-09-30 | reports/阶段工作报告_#02.md |
| M2 | 算术层（Stirling 适配 + τ/ω/σ 界 + Euler Σ1/p） | ✅ 全部（5/5 sorry 清零） | reports/阶段工作报告_#08.md |
| M3 | Perm/Decompose（含1圈分解 + Cor 2.2） | ✅ 2026-10-01 | reports/阶段工作报告_#09.md |
| M4 | Perm/Restricted（Lemma 2.3 + Cor 2.4 + 上尾） | ✅ 2026-10-02 | reports/阶段工作报告_#10.md |
| M5 | Perm/ErdosTuran（精确乘积） | ✅ | reports/阶段工作报告_#10.md |
| M6 | Perm/Feller（圈型耦合 + Lemma 2.5） | ✅ | — |
| M7 | Section3（Prop 3.1 + Thm 1.1） | ✅ | — |
| M8 | Warlimont×4（Eta + T2 锚定） | ✅ 2026-10-03 | — |
| M9 | Section4（Thm 1.2） | ✅ 2026-10-03 | — |
| M10 | 终审（三闸门）+ 清理 + 最终报告 | ✅ 2026-10-03 | reports/阶段工作报告_#11.md |

## 分解原则

- 每个里程碑：先写代码 → `lake build MostProbableOrder.<模块>` 单目标验证 → 全量 `lake build` →
  更新 STATE.md/SORRY.md → 写阶段报告 → 自动进入下一个。
- 工作量过大的里程碑（M2/M7/M8）再细分为子任务，逐一推进；M8 已预拆 4 模块。
- 上下文管理：STATE.md 为跨会话唯一权威状态；每会话末更新。

## 验收标准（M10 三闸门）

1. `grep -rn "sorry\|admit\|axiom\|native_decide" MostProbableOrder/` 零命中（Checks.lean 白名单除外）；
2. `lake build 2>&1 | grep "declaration uses 'sorry'"` 零输出；
3. `#print axioms MostProbableOrder.theorem11 / theorem12` 仅 `propext, Classical.choice, Quot.sound`。
