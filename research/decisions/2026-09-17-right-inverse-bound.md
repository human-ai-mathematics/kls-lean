# 近似右逆：秩亏路线的 R3（逐点版与邻域一致版）

2026-09-17。本轮**证明新定理**：秩亏路线义务清单上的 **`R3`**，逐点与邻域一致两个版本。
连同上一轮的 `R1`、`R2`，路线十三条编号里已兑现 **三条**。
**只证了 `R3`**；`R0`、`R4`–`R10`、`N1`、`N2` 仍未证，
**余维 m coarea 的秩亏部分仍然开着**。本轮**没有证明任何 coarea 公式、任何切片定理、任何 Sard 定理**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260917T052110.430244Z/report.json`：10 个门、216 个本地模块内核重放、
577 条目，快照
`b4e02d7478fc4364645dfdd1845bd48b7ec9b678977cbaecb4717b7826093422`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## `R3` 是干什么用的

路线要在正则分量 `v = P ∘ u` 的纤维里切片，而**纤维的弦不是切向量**：
同一纤维里的两点只给出 `‖Dv (b − a)‖ ≤ ε ‖b − a‖`，不是 `Dv (b − a) = 0`。
要把它变成 `‖Du (b − a)‖` 小，就需要「几乎被满射零化的向量离核不远」的定量陈述——
这正是满射右逆的范数界。

**邻域一致版是硬需求，不是方便。** Eilenberg 论证里 `ε → 0` 的每个尺度用的是**不同的**逼近分片，
依赖于分片的常数毫无用处；界必须在整个邻域上用同一个常数成立。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/RightInverseBound.lean`
（168 行，**仅依赖 Mathlib**，本地 import 闭包 **1 个模块**、无 WIP）。

* **`exists_mem_ker_norm_sub_le`**（核心估计）：只要 `R` 是 `L` 的右逆，
  `z − R (L z)` 就被 `L` 零化，且与 `z` 相距不超过 `‖R‖ · ‖L z‖`。
  **不用满射性、不用有限维、不用完备性**——只用右逆的存在。
* **`exists_rightInverse_bound`**（`R3` 逐点版）：满射到有限维空间的 `L` 有单一常数 `C`，
  使每个向量离核不超过 `C ‖L z‖`。Mathlib 的
  `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional` 给出连续右逆。
* **`rightInverse_comp_inverse`**（扰动引理）：若 `A ∘ R₀` 是算子环的单位，
  则 `R₀ ∘ (A ∘ R₀)⁻¹` 是 `A` 的右逆。
* **`exists_nhds_uniform_rightInverse_bound`**（`R3` 一致版）：
  在微分满射的点周围存在邻域，携带**同一个** `M` 界住微分、**同一个** `C` 供核估计。
  证明是在基点扰动单一右逆：`Units.isOpen` 给出 `A ∘ R₀` 附近仍是单位，
  `NormedRing.inverse_continuousAt` 给出逆的范数在附近不超过 `2`，于是 `C = 2‖R₀‖`。

**两条陈述都比路线要求的更强**：**不需要内积**、**不需要定义域有限维**——
定义域是任意实赋范空间，只有靶空间有限维。路线里的
`coareaJacobian (fderiv ℝ v x₀) ≠ 0` 由已证的 `coareaJacobian_ne_zero_iff` 换成满射性，
内积假设只在这一步转换里出现。

## 满射性到底是什么地方需要的——如实记下，不夸大

* **它是右逆存在的原因**：审计的 `no_right_inverse` 给出平面上秩一投影**没有右逆**，
  所以证明 `R3` 用的构造对它不可用（`proj₀_not_surjective`）。
* **但逐点版的结论并不刻画满射性。** `pointwise_conclusion_does_not_imply_surjective`：
  零映射满足该结论（取 `C = 0`，每个向量本来就在核里），而到非零靶空间的零映射不满射。
  **所以不能说「满射性对 `R3` 是必需的」**——满射性是构造右逆的充分条件，不是结论逼出来的。
  本轮**没有**证明「有限维下每个线性映射都满足逐点结论」，虽然那是真的。
* **一致版在基点的假设确实在干活**：`uniform_constant_degenerates` 给出
  沿 `t • id` 最小可用常数是 `|t|⁻¹`，当这族趋于不满射的 `0` 时炸掉，
  所以不满射的点的任何邻域都不可能携带单一常数。

## 边界情形

* **零维靶空间**：每个映射满射，`C = 0` 可用，每个向量本来就在核里（`zero_dimensional_target`）。
* **线性同构**：右逆就是逆（`linear_equiv`）。
* **常值映射**：微分恒零，一致陈述在靶空间零维时可用且平凡（`constant_map`）。
* 核心估计**不需要**满射性（`core_needs_only_a_right_inverse`）。

## 本轮没有做的事

* **没有证明 `R0`**：秩亏部分（`m ≥ 2` 的中间秩）一点没动。
* **没有证明 `R4`**——下一步就是它，而且是**不归点**：`R2 + R3` 就位后 `R4` 自足，
  它若做不出来或常数不一致，整条路线就是错的。
* 没有证明 `R5`–`R10`、`N1`、`N2`。
* **没有证明任何 coarea 公式**，也没有改进已证的余维 m coarea 的适用范围。
* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言。
* 没有修改任何既有 `.lean`（包括 `FunctionalInequalities.lean`、
  `research/audits/RankDeficientRouteStatements.lean` 与 `AreaFormulaRouteStatements.lean`，
  后两者继续**保持原字节**）；没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；
  没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句文件

`RankDeficientRouteStatements.lean` 保持原字节；`R3` 的两条命题由新客户端
`research/audits/RightInverseBoundAudit.lean` **逐字复制并证明**
（`route_R3_pointwise`、`route_R3_uniform`）。
本轮重跑 `AreaFormulaRouteStatements.lean`，**未发现新的错误**。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/RightInverseBoundAudit.lean` 的 **16 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`。
* 重跑全部 **43 个既有审计客户端**加新客户端共 **44 个**，全部严格通过，0 失败；
  公理报告 594 条，其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-right-inverse-bound.json`，
  最终核对另存 `build/audit/right-inverse-bound/final-snapshot.json`。
