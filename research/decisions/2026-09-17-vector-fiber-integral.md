# 纤维方向的 m 维换元

2026-09-17。本轮**证明新定理**，完成余维 m coarea 正则情形的**第三个子块**：
**纤维方向的 m 维换元**，以及它的直接兑现——**局部 coarea 等式的环境一侧**。
**仍然没有证明任何 coarea 公式。**
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T163322.273570Z/report.json`：10 个门、208 个本地模块内核重放、
545 条目，快照
`9f415ea90a30a962ef13bff80995e84f7d3d30c3110785b7f4b3752ace00370d`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 一处 Mathlib 缺口，必须先补

Mathlib 的换元公式 `lintegral_image_eq_lintegral_abs_det_fderiv_mul` 是**自映射**的陈述：
`f : E → E`，体积因子 `|det (f' x)|`。纤维映射 `t ↦ ψ (y, t)` 从**水平空间 `W`** 走到
**法因子 `K`**，两者是同维但**不同**的空间，那个行列式**根本不合式**。

* **`lintegral_image_eq_lintegral_normDet_fderiv_mul`**（本轮新证）：
  同维两空间之间的换元公式，体积因子是 `LinearMap.normDet`——它本来就定义在不同空间之间。
  证明把目标空间用一个线性等距等价拉回来：等距保测度、其范数行列式为 `1`，所以什么都不多出来；
  选取的等距**只出现在证明里，不进入任何陈述**。
  `f` 只需在 `s` 上逐点有 within 导数并在 `s` 上单射，权重是任意 `ℝ≥0∞` 函数，
  **无可积性、无有限性、无连续性假设**。

**同维假设不可去**：审计的 `equal_dimension_necessary` 给出反例——
`ℝ` 到平面的直线映射在单位区间上，左端为 `0`（像落在真子空间里），右端为 `1`（等距的体积因子是 `1`）。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/VectorFiberIntegral.lean`
（266 行，本地 import 闭包 18 个模块，**无 WIP**）。它是 `FiberIntegral.lean` 的余维 m 类比。

* **`fderiv_snd_eq`、`continuous_normDet_fderiv_snd`**：水平方向导数就是联合导数限制在水平因子上，
  其体积因子对两个坐标连续（被积函数可测性由此而来）。
* **`setLIntegral_image_vectorVerticalMap`**：**余维 m 的竖直换元**。对 `T (y,t) = (y, ψ (y,t))`，
  在任意单射 Borel 片上
  `∫⁻ over T''A = ∫⁻_A normDet (Dₜψ) · f ∘ T`。
  水平空间 `W` 与法因子 `K` **全程保持区分**。
* **`splitVectorEquiv`**：正交分裂作为连续线性等价，逆是两个分量收缩，显式。
* **`setLIntegral_image_levelGraphMap`**：沿着水平族的图映射的换元——
  把竖直换元用上上轮已证的**保测分裂**搬到环境空间 `V` 上。
* **`setLIntegral_coareaJacobian_levelGraphFamily`**：**局部 coarea 等式的环境一侧**。
  在水平族的任一 Borel 片上，环境 coarea 密度对任意权重的积分等于
  **图面积密度**对参数–水平域的积分——右端正是已证的归一化面积公式 `B2` 所消费的密度。
  换元是上面的竖直换元，密度的更换是上一轮纤维 Jacobian 恒等式的逐点应用。

## m = 1 退回已证结果

审计的 `codimension_one_verticalMap` 从本轮的余维 m 陈述**逐字导出**仓库已证的
`Analysis.setLIntegral_image_verticalMap`（其本身的证明是一维 Jacobian 定理），
桥梁是 `normDet_fderiv_eq_abs_deriv`：一维体积因子就是导数的绝对值。

## 本轮没有做的事

* **没有证明任何 coarea 公式**；余维 m 正则情形**仍未完成**。
* 纤维一侧的**加权**余维 m 面积公式（`setLIntegral_image_graphMap` 的类比）**没有证**——
  上一轮的纤维测度只有权重一。
* 没有做水平变量上的 Tonelli 装配，没有做局部到整体的可数拼接，
  没有做余维 m 的加权切片可测性。
* 没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* 没有增加不必要的假设：没有有界、有限体积、可积性、正则值、SFinite。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍是 `B1` 与已证伪的 `A0`；
`A5` 两侧错配一致故不为假。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 剩余工作（余维 m 正则情形）

1. **加权的余维 m 图面积公式**：`setLIntegral_image_graphMap` 的类比，
   把 `B2` 从「图的测度」升级到「图上的加权积分」；
2. 水平变量上的 Tonelli，把本轮的环境一侧与第 1 步的纤维一侧接起来，
   得到局部 coarea 等式（标量对应物 `setLIntegral_coarea_graph_family`）；
3. 可数覆盖 + 不交拼接，加上余维 m 的加权切片可测性
   （标量对应物 `OpenSliceMeasurable.lean`），得到
   `coarea_of_contDiffOn_of_coareaJacobian_ne_zero`。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorFiberIntegralAudit.lean` 的 **16 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；含零维纤维、全空间（无有限性）、
  线性等距保测度的自洽检查、m = 1 退回标量竖直换元、以及同维假设的反例。
* 重跑全部 **36 个审计客户端**（`research/audits` 29 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-fiber-integral.json`，最终核对另存
  `build/audit/vector-fiber-integral/final-snapshot.json`。
