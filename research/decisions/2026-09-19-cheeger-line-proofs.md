# Cheeger 线证毕并注册：两洞关闭、`lem:relative-perimeter-cheeger-infimum` 成为第 25 个证书、Cheeger 不等式证出

2026-09-19，**实现 + 注册轮**。Owner 指示接手原属王浩丞的 Cheeger 线（学长那个我们接手了）。同日先写了两条路线
（[两洞路线](2026-09-19-cheeger-infimum-route.md)、[Cheeger 不等式路线](2026-09-19-cheeger-inequality-route.md)），
交两个并行的证明会话，本会话整合与注册。结果：

* **两洞关闭**：`smoothConstant_mul_lintegral_min_superlevel_le`、`smoothConstant_le_minkowskiConstant` 在
  `KLS/Geometry/CheegerEquality.lean` 证出；WIP 模块的七条公开声明以**逐字节相同的 `pp.all` 签名**迁入
  （2223 行打印 `diff` 为空），`KLS/WIP/CheegerInfimum.lean` 删除，`KLS/WIP/` 目录随之消失
  （原文冻结于 `build/audit/cheeger-line-proofs/CheegerInfimum.before.lean`）。
* **第 25 个证书**：`solutions/LemRelativePerimeterCheegerInfimum.lean` 注册 `lem:relative-perimeter-cheeger-infimum`
  （`certificate hρ : h_M = h_S`，任意带 Borell 密度的律；`intrinsic hμ hρ`：`h_μ = h_ν^{sm,rel}` 与 `Ψ_KLS(μ) = ψ_ν`，
  即 `thm:klartag-density-frontend-identification` 的两条等周子句），4 条公理守卫。
* **Cheeger 不等式**：`KLS/Geometry/CheegerInequality.lean`（含 `KLS/Geometry/Median.lean`）证出
  `C_P^smooth(ν) ≤ 4/h_M(ν)²`（任意 Borel 律，`Isoperimetry.smoothTest_constant_le`）与
  `C_P^lit(μ) ≤ 4Ψ_KLS(μ)²`（对数凹律，`LogConcave.literatureConstant_le_four_mul_inverseScale_sq`，Dirac 律两侧皆 0）。
  Buser 半 `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` **未证**，`thm:logconcave-cheeger-poincare-comparison` 加 `\lean{}` 与说明，不加 `\leanok`。

直接洞由 **7（0/2/5）降为 5（0/0/5）**，仅剩 `Energy/WIP/Cheeger.lean`；证书 **24 → 25**。不提交、不推送。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T132358.171383Z/report.json`：10 个门、234 个模块重放、638 条目，快照 `d9cd7067e18cbebc3408d8e772fc539392533db8be44e91419f2bba370a7226a`。

## 边界

Energy 的五个洞（`Energy/WIP/Cheeger.lean`，奇异测度的 `𝓔^can = 2Ch`）未触碰；无量纲 KLS 仍开。
不新增兼容 alias、不重述既有定理、不削弱已证结论；`thm:klartag-density-frontend-identification` 的文献 Poincaré 常数子句
**未在该节点认证**（节点不标 `\leanok`，只加说明）。

## 两个证明会话

规则同前（只新建文件、不 `lake build`、不改 Git、严格编译、逐字复述、不 import WIP、注释里不写转义词）。

| 路线 | 新库模块（行） | 审计客户端（行） | 兑现 |
| --- | --- | --- | --- |
| 两洞 | `KLS/Geometry/CheegerEquality.lean` 568（七条迁入 + 五条新引理 `K1`、`K2`、`K4`、`K7`、`K8`） | `CheegerEqualityAudit.lean` 354 | `K0`–`K13`；**`K7` 按字面为假**，见下 |
| Cheeger 不等式 | `KLS/Geometry/Median.lean` 167、`CheegerInequality.lean` 784（+27 整合 `P0`） | `CheegerInequalityAudit.lean` 210（+9 整合 `route_P0`） | `P1`–`P6`、`D1`；`P0` 整合时合成 |

**`K7` 按字面为假**：`B = ∅` 时 `Metric.infDist x ∅ = 0`，截断恒为 1 而厚化为空，命题读作 `1 ≤ 0`；审计里
`route_K7_empty_counterexample` 用 `EuclideanSpace ℝ (Fin 1)` 上的 Dirac 律证伪逐字形式，`route_K7` 证加 `B.Nonempty` 的版本；
`K5` 只对正质量集合用它，下游不受影响。路线语句文件保持字节不变。

**`P0` 的合成**：`Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope`（对数凹律的内禀绝对连续性）把文献常数
识别为内禀律的光滑测试常数，`Isoperimetry.constant_eq_minkowskiConstant_intrinsic` 给 `h_μ = h_M(ν)`，再用 `P1`。
`P6` 复用了仓库既有的光滑截断 `Energy.Euclidean.LipschitzApproximation.scaled`，梯度能量的收敛用 `ℝ≥0∞` 控制收敛，方差用 Fatou。

## 注册与整合动作

1. 证书文件、ledger 节点（`kind: lemma`，`meta.scope` 追加）、`research/check_blueprint.py` 的 `CERTIFICATES`、
   `lakefile.toml` 的 `Solutions` 根；Blueprint 第 60 章引理加 `\lean{…}`、`\leanok`（陈述注明 Lean 范围更强）、证明块 `\leanok`；
   第 45 章 Klartag 节点加说明（两条等周子句已认证，Poincaré 子句未），Cheeger–Buser 定理加 `\lean{…}` 与说明、不加 `\leanok`。
2. `check_ledger.py` 的转义词扫描是纯文本扫描传递导入源码：证书导入闭包中 13 个模块的 docstring 写着「contains no `sorry`」
   「admit fewer covers」之类，改写为 hole / allow，不改任何代码。
3. 三个曾 import 已删 WIP 的客户端（`research/audits` 的 `LipschitzCoareaMigrationAudit`、`IsoperimetryCoareaAudit`；
   历史客户端 `build/audit/PerimeterInterfaceAudit`）改接 `KLS/Geometry/CheegerEquality.lean`；它们原先带 `sorryAx` 的 5 条报告变为标准。
4. 聚合导入加入 `KLS.Geometry.CheegerEquality`、`KLS.Geometry.CheegerInequality`（`Median` 随之），补两段说明。
5. `research/tasks.json`：`lem:relative-perimeter-cheeger-infimum` 的 infrastructure `missing → available`，证据换成新模块、审计与证书；
   其余节点被钉住的文件哈希全部刷新；Klartag 与 Cheeger–Buser 节点注记。进度视图经临时 index 由 `research/progress/update.py` 重生成
   （`STATUS.md` 25 证书）。
6. 默认 `lake build`（3507 个作业）通过；`check_ledger.py` 25 节点 0 错误；`check_blueprint.py` 88 标签 0 错误。

## 明确没证什么

* Buser 半 `Ψ_KLS(μ)² ≤ π C_P^lit(μ)`：未证（Bakry–Émery 或 Lovász–Simonovits 局部化都不在 Mathlib）；Cheeger–Buser 节点不标 `\leanok`。
* `thm:klartag-density-frontend-identification` 的文献 Poincaré 常数子句未在该节点认证。
* Energy 五洞未触碰；无量纲 KLS 仍开。`K7` 的逐字形式为假已记录（并已形式化证伪）。

## 验证

默认 `lake build`（3507 个作业，含新证书的 `Solutions` 库）通过。全部 **62** 个审计客户端（`research/audits` 55 个 + `build/audit` 7 个活客户端）以 `-DwarningAsError=true` 重跑，**0 失败**；**791 条公理报告，0 条 `sorryAx`**——首次没有任何客户端报告洞。仅剩的 WIP 模块 `Energy/WIP/Cheeger.lean` 编译出 **5** 个 `sorry` 警告，直接洞 **5（0/0/5）**。七条迁移声明的 `pp.all` 前后 `diff` 为空。`check_ledger.py` **25** 个证书 0 错误；`check_blueprint.py` 88 标签 0 错误；`atlas.py check` 75 节点 25 证书无环；104 项单元测试通过。
`pp.all` 七条声明前后 `diff` 为空。根目录 `python3 research/verify.py` 于本轮结束时重跑，最终回执记于
`build/audit/cheeger-line-proofs/final-snapshot.json`，快照与工作区逐条重算，drift 为空。
详见 `research/explorations/2026-09-19-cheeger-line-proofs.json`。
