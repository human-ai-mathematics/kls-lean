# 迁出水平集可测性：第一个 coarea 洞闭合

2026-09-15。本轮把直接洞 `Analysis.aemeasurable_lintegral_levelSet` 从
`KLS/WIP/AnalyticPrerequisites.lean` **迁出**到无洞模块
`KLS/Geometry/LevelSetMeasurable.lean`，`pp.all` 签名**逐字节不变**，并由上一轮证明的 L5 给出
证明。直接洞由 **11（3/3/5）降到 10（2/3/5）**。不提交、不推送、不改历史决定。
起始 HEAD 为 `2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260915T033803.710026Z/report.json`（与 `build/verification/latest.json`
逐字节相同），重新计算的完整快照与回执相等：421 个文件，SHA256
`8abb1b22ab2ebac05aac28d7ac32536dba0dc2d40da4a1e1109f285d50ed60f8`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 迁出的内容与签名核对

新模块 `formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean`：

```lean
theorem FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  have h := KLS.aemeasurable_setLIntegral_inter_levelSet (S := Set.univ) hu.continuous
    hu.lipschitzOnWith MeasurableSet.univ hg
  simpa using h
```

**签名逐字节不变**，这一点是机器核对的，不是肉眼判断：迁出前在导入 WIP 的环境里以
`set_option pp.all true` 打印 `@FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet`
并存为 `build/audit/migration-signature-before.log`，迁出后在导入新模块的环境里同样打印存为
`build/audit/migration-signature-after.log`，两者 `diff` 为空。
签名包括同一个 universe、同样六个实例参数及其顺序（含**证明并不使用**的 `CompleteSpace V`）、
同样的隐式绑定 `u`、`K`、`g` 与同样的假设名 `hu`、`hg`、同样的结论。

为保持接口不变而保留未使用的 section 变量，这里按仓库既有做法（`Geometry/RegularSuperlevel.lean`
迁出 `ae_exists_superlevel` 时的写法）用 `set_option linter.unusedSectionVars false in` 静音
linter，**而不是**用 `omit` 收窄签名。文档注释也原样保留。

声明保留 `FunctionalInequalities.Analysis` 命名空间（公共名不能变），而文件放在 `KLS/Geometry/`
下，因为语句里出现 `KLS.surfaceMeasure`，不属于 KLS 无关的 `Analysis/` 层；被替换的 WIP 文件
本身就是同样的安排。

`KLS/WIP/AnalyticPrerequisites.lean` 只删除了这一条声明并相应更新了文件头注释，
**没有改动其余任何声明**：`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`、`sard`、
`ae_forall_fderiv_ne_zero` 的语句、证明与位置全部不变。

## 洞数变化与仍然开着的洞

* `AnalyticPrerequisites.lean`：**3 → 2** 个直接洞。
* `KLS/WIP/CheegerInfimum.lean`：3（不变）。`Energy/WIP/Cheeger.lean`：5（不变）。
* 总计 **11 → 10**。这是本轮唯一的数字变化；证书仍 **24**，perimeter infrastructure 仍
  **missing**。

`build/audit/LevelSetMeasurableAudit.lean` **同时导入**新模块与 WIP 文件，所以下列报告出自
同一个环境，迁出的名字在其中只解析到一条声明：

* `Analysis.aemeasurable_lintegral_levelSet`：`propext, Classical.choice, Quot.sound`，
  **无 `sorryAx`**。
* `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（加权 coarea **等式**）：
  仍含 `sorryAx`，仍是直接洞。
* `Analysis.sard`（尖锐 `C^(finrank)`）：仍含 `sorryAx`，仍是直接洞，仍无下游消费者。
* `Analysis.ae_forall_fderiv_ne_zero`：仍由 `sard` 继承 `sorryAx`。

客户端还把这两条语句各写成一条定理并分别以具名参数调用库声明：
`client_aemeasurable_lintegral_levelSet` 编译且无 `sorryAx`；`client_coarea_statement` 编译但
**带 `sorryAx`**——它只是复述那条尚未证明的等式，不是它的证明。

## 本轮没有做的事

* **没有证明加权 coarea 等式**。`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  与 `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 仍是直接洞，
  目标 T2/T3 与 L6–L12（含 L6 的 Whitney C¹ 延拓）完全未动。
* 没有证明尖锐 `C^(finrank)` 的 `Analysis.sard`。
* 没有证明 `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le` 或两个 Cheeger 常数相等。
* 没有证明 Eilenberg 常数的尖锐性。
* 没有新增数学内容：本轮不含任何新定理，只有一次迁出与接线。
* 没有扩大证书或 Blueprint `leanok` 范围。

## 验证

* `KLS/Geometry/LevelSetMeasurable.lean` 以 `-DwarningAsError=true` 单独编译通过。
* `build/audit/LevelSetMeasurableAudit.lean` 以 `-DwarningAsError=true` 编译通过，
  6 条 `#print axioms` 给出上节的边界。
* 签名 `diff` 为空（`migration-signature-before.log` 与 `migration-signature-after.log`）。
* 重跑 `BorelSliceAudit`、`CompactSliceAudit`、`EilenbergMajorantAudit`、`NullSlicingAudit`、
  `WeightedCoareaRouteStatements`、`WeightedCoareaInfrastructure`、`AreaFormulaAudit`、
  `CheegerInfimumAudit`、`MinkowskiConstantAudit`、`SuperlevelSardScope`、`SmoothSardAudit`、
  `SmoothSardRouteStatements`，全部严格编译通过，未作任何修改。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **2/3/5，总数 10**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-levelset-measurable-migration.json`，最终核对另存
  `build/audit/migration-final-snapshot.json`。`build/` 被 gitignore，故 `build/audit`
  的哈希由证据 JSON 单独绑定；迁出前的 WIP 文件原样存为
  `build/audit/migration-AnalyticPrerequisites.before.lean`。
