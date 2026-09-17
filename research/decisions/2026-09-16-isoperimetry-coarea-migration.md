# 迁出 C¹ 带权 coarea：第二个 coarea 洞闭合

2026-09-16。本轮把直接洞 `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
从 `KLS/WIP/CheegerInfimum.lean` **迁出**到无洞模块 `KLS/Geometry/IsoperimetryCoarea.lean`，
`pp.all` 签名**逐字节不变**，并由上一轮证明的 L11 给出证明。直接洞由 **10（2/3/5）降到
9（2/2/5）**。**不证明任何新定理**，不提交、不推送，不改写历史决定。

起始 HEAD 为 `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`；起始 passed 回执为
`build/verification/20260915T161514.695618Z/report.json`，与起始工作区完全一致：
467 个文件，SHA256 `5994b4b4758eeb95e354bd1b081cc22919a4dea1e02ab7188bf1c035790be0bb`。
起始工作区含前两轮尚未提交的改动，本轮在其之上继续。

## 迁出的内容与签名核对

新模块 `formalization/FunctionalInequalities/KLS/Geometry/IsoperimetryCoarea.lean`：

```lean
theorem FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (coarea_of_contDiff (S := Set.univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa using h
```

**签名逐字节不变，机器核对**：迁出前在导入 WIP 的环境里以 `set_option pp.all true` 打印该常数
类型存为 `build/audit/iso-signature-before.log`，迁出后在导入新模块的环境里同样打印存为
`build/audit/iso-signature-after.log`，两者 `diff` 为空。签名包括同一 universe、
同样**七个**实例参数及其顺序（含证明**并不使用**的 `CompleteSpace V` 与
`SecondCountableTopology V`）、同样的隐式绑定 `u`、`K`、`g` 与同样的假设名 `hu`、`hK`、`hg`、
同样的结论。

为保持接口不变，未使用的 section 变量与未使用的假设名 `hK` 都原样保留，
用 `set_option linter.unusedSectionVars false in` 与 `set_option linter.unusedVariables false in`
静音两个 linter，**而不是**用 `omit` 收窄签名或把 `hK` 改成 `_`。文档注释原样保留。
声明保留 `FunctionalInequalities.KLS.Isoperimetry` 命名空间（公共名不能变），
文件放在 `KLS/Geometry/` 与它消费的 coarea 层并列，`KLS/Geometry/LevelSetMeasurable.lean`
是同样的安排。

**`hK` 这条 Lipschitz 假设完全没有参与证明**：该声明本来就假设了 `ContDiff ℝ 1 u`，
而 L11 不需要任何 Lipschitz 界。

## 对 WIP 文件的改动

`KLS/WIP/CheegerInfimum.lean` 只删除了这一条声明，并相应更新了文件头对该义务的描述；
删除后 `section Coarea` 内只剩一个空的 `namespace Isoperimetry` 与一行不再被任何声明使用的
`variable`，一并移除（纯脚手架，不含任何声明，不改变任何签名）。
**其余声明的语句、证明与位置全部不变**，迁出前的原文存为
`build/audit/iso-migration-CheegerInfimum.before.lean`。

## 洞数变化与仍然开着的洞

* `KLS/WIP/CheegerInfimum.lean`：**3 → 2** 个直接洞，剩下的两个正是两条 Cheeger 比较
  `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le` 与
  `Isoperimetry.smoothConstant_le_minkowskiConstant`。
* `KLS/WIP/AnalyticPrerequisites.lean`：2（不变）。`Energy/WIP/Cheeger.lean`：5（不变）。
* 总计 **10 → 9**。证书仍 **24**，perimeter infrastructure 仍 **missing**。

`research/audits/IsoperimetryCoareaAudit.lean` **同时导入**新模块与**两个** WIP 文件，
所以下列报告出自同一个环境，迁出的名字在其中只解析到一条声明：

* `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`：标准三条公理，
  **无 `sorryAx`**。
* `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（**Lipschitz** 情形，
  不假设 `C¹`）：仍含 `sorryAx`，仍是直接洞。**迁出的结果是它的 `C¹` 特化，不蕴含它。**
* `Analysis.sard`（尖锐 `C^(finrank)`）：仍含 `sorryAx`。
* `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`、
  `Isoperimetry.smoothConstant_le_minkowskiConstant`、
  `Isoperimetry.minkowskiConstant_eq_smoothConstant`：全部仍含 `sorryAx`。

客户端里复述 Lipschitz 情形的 `client_lipschitz_coarea_statement` 编译**但带 `sorryAx`** ——
复述不等于证明。

## 本轮没有做的事

* **没有证明任何新定理**；本轮只有一次迁出与接线。
* **没有证明 Lipschitz 情形**。它需要 **L12 → L7（精确 C¹ 分片）→ L6/L6a（闭集 Whitney
  一阶 jet 延拓与紧 jet 提取）**，全部未证明。
* 没有证明尖锐 `Analysis.sard`、两条 Cheeger 比较、两个 Cheeger 常数相等、
  Eilenberg 常数的尖锐性。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送。**

## 验证

* `KLS/Geometry/IsoperimetryCoarea.lean` 以 `-DwarningAsError=true` 单独编译通过。
* `research/audits/IsoperimetryCoareaAudit.lean` 以 `-DwarningAsError=true` 编译通过，
  8 条 `#print axioms` 给出上节的边界。
* 签名 `diff` 为空。
* 重跑其余 18 个审计客户端，全部严格编译通过，未作任何修改。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **2/2/5，总数 9**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全一致；证据 JSON 为
  `research/explorations/2026-09-16-isoperimetry-coarea-migration.json`，最终核对另存
  `build/audit/iso-migration-final-snapshot.json`。
