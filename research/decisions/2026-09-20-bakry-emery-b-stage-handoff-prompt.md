# 下一步提示词：Bakry–Émery B 阶段——Γ、凸 Hessian 与局部 Bochner 恒等式

请在 `/Users/lyuyuwei/Documents/ChatGPT/KLS` 继续 Bakry–Émery 路线。本轮目标是实际完成
`research/audits/BakryEmeryRouteStatements.lean` 中的 B0–B4，即有限维欧氏空间上光滑
凸位势的局部 Γ/Γ₂ 与 Bochner 计算。

本轮不处理半群正则性、梯度交换、一般对数凹测度逼近、小时间 BV 估计或最终 Buser
拼装；不得因为完成局部 Bochner 就把 π 比较或完整 Bakry–Émery 路线标为 proved。

## 1. 先核对当前基线

先读：

- `AGENTS.md`
- `HANDOFF.md` 顶部 `Current operational status (2026-09-20)`
- `research/decisions/2026-09-20-bakry-emery-route.md`
- `research/decisions/2026-09-20-generator-identification.md`
- `research/audits/BakryEmeryRouteStatements.lean`
- `research/audits/BakryEmeryGeneratorAudit.lean`

重点检查现有模块：

- `formalization/FunctionalInequalities/Analysis/BakryEmery/Basic.lean`
- `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/AdjointClosure.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean`

当前已证，不要重复实现：

- `weightedLaplacian U f = Δf - ⟪∇U,∇f⟫`
- G0：加权分部积分
- G1：对 `f ∈ C_c∞`，`[f] ∈ D(T̄†T̄)` 且
  `T̄†T̄[f] = [-weightedLaplacian U f]`
- B2：`bilinearIteratedFDerivTwo_symm`
- `B = I` 的闭梯度能量与 canonical energy、`2 Ch` 的桥梁
- 半群生成和当前 `L²` Markov 性

这里扩散生成元始终是

```text
ℒf = weightedLaplacian U f = Δf - ⟪∇U,∇f⟫,
```

而非负算子是 `A = T̄†T̄ = -ℒ`（只在已经识别的光滑测试函数上作此等同）。
保持符号一致，不要把 `A` 和 `ℒ` 混写。

先检查当前 dirty worktree，保留所有既有修改；不 reset、clean、覆盖或删除他人工作。
本轮不提交、不推送。

## 2. 本轮精确目标

建议新增：

- `formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean`
- `formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner.lean`
- `research/audits/BakryEmeryBochnerAudit.lean`
- `research/decisions/2026-09-20-bochner-identification.md`

并把新模块加入必要的聚合 import。不要为了方便另造一套 Laplacian、gradient 或 Hessian
定义；直接复用当前 `weightedLaplacian`、`gradient`、
`bilinearIteratedFDerivTwo` 和 `stdOrthonormalBasis`。

### B0：Γ 的乘积恒等式

定义局部 carré du champ，推荐直接采用其几何表达：

```lean
def gamma (f g : E → ℝ) (x : E) : ℝ :=
  inner ℝ (gradient f x) (gradient g x)
```

证明 `BakryEmeryRouteStatements.lean` 中 B0 的精确命题：

```text
(ℒ(fg) - f ℒg - g ℒf) / 2 = ⟪∇f,∇g⟫.
```

要求：

- `U f g ∈ C²` 的现有候选范围必须能直接实例化；
- 不添加紧支撑、可积性、凸性、正维数或非空基假设；
- 明确核对除以 `2` 的归一化，不能留下 factor `2` 偏差；
- 可以先证明 gradient product rule 和 Laplacian product rule 等可复用引理；
- 若另定义 algebraic Γ，应证明它与上述 `gamma` 相等，不能把等同性直接塞进定义。

### B1：凸性推出 Hessian 半正定

证明精确候选：

```lean
ContDiff ℝ 2 U →
ConvexOn ℝ Set.univ U →
∀ x v, 0 ≤ bilinearIteratedFDerivTwo ℝ U x v v
```

先搜索 pinned Mathlib 是否已有“二阶可微凸函数 Hessian 半正定”的可用定理。若缺失，
推荐路线：

1. 固定 `x v`，限制到直线 `t ↦ U (x + t • v)`；
2. 从 `ConvexOn ℝ Set.univ U` 得到一元函数的凸性；
3. 由一元凸函数导数单调或二阶导非负得到结论；
4. 精确连接该一元二阶导数与
   `bilinearIteratedFDerivTwo ℝ U x v v`。

不得把 Hessian 非负作为新假设，也不得只证明坐标轴方向。

### B2：复用既有 Hessian 对称性

不要重新证明另一份版本。直接使用：

```lean
Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm
```

在新审计中用它精确关闭路线 B2。

### B3：固定标准正交基下的 Bochner 恒等式

证明 `BakryEmeryRouteStatements.lean` 中 B3 的精确候选：

```text
ℒ(‖∇f‖²)/2 - ⟪∇f, ∇(ℒf)⟫
  =
Σᵢ Σⱼ (D²f(eᵢ,eⱼ))²
  + D²U(∇f,∇f).
```

其中：

- `eᵢ = stdOrthonormalBasis ℝ E i`；
- 保留候选中的 `ContDiff ℝ 3 U`、`ContDiff ℝ 3 f` 接口；
- 不添加紧支撑、积分、概率测度、凸性或正维数假设；
- 定理必须覆盖零维空间，有限和为空时自然退化；
- 正确使用 B2 处理混合导数交换；
- 第三阶导数项必须真实抵消，不能通过加强结论或隐藏假设绕过；
- 漂移项的符号必须最终给出 `+ D²U(∇f,∇f)`。

建议把证明拆为可审计的局部引理，例如：

- gradient/方向导数与 Hessian 的关系；
- `gradient (fun y ↦ ‖gradient f y‖²)` 的坐标表达；
- `Laplacian.laplacian (fun y ↦ ‖gradient f y‖²)` 的展开；
- `gradient (Laplacian.laplacian f)` 的展开；
- `gradient (fun y ↦ ⟪gradient U y, gradient f y⟫)` 的展开；
- 三阶导数交换与抵消；
- 剩余平方项和位势 Hessian 项的整理。

可以定义：

```lean
def hessianSqStdBasis (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j,
    (bilinearIteratedFDerivTwo ℝ f x
      (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E j)) ^ 2
```

但在没有证明基无关性之前，不得把它公开描述成已经构造好的 invariant
Hilbert–Schmidt norm。若本轮顺便证明任意正交基下的和相同，可以再引入不变记号；
否则明确保留 `StdBasis` 名称和限制。

### Γ₂ 定义

推荐定义：

```lean
def gammaTwo (U f : E → ℝ) (x : E) : ℝ :=
  weightedLaplacian U (fun y => gamma f f y) x / 2 -
    gamma f (weightedLaplacian U f) x
```

随后证明它等于 B3 左端以及上述坐标右端。

不要为了使用 B0 而无故把正则性提高到 `C⁴`。这里
`gamma f (weightedLaplacian U f)` 可直接按 gradient 的几何定义解释；
在 B3 的 `C³` 假设下证明所需可微性。

### B4：凸位势下 Γ₂ 非负

由 B3、B1 和平方和非负推出精确候选：

```lean
ContDiff ℝ 3 U →
ConvexOn ℝ Set.univ U →
ContDiff ℝ 3 f →
∀ x, 0 ≤ gammaTwo U f x
```

同时提供能直接关闭路线文件中“展开形式”B4 的定理。

不得把 `Γ₂ ≥ 0` 当作假设，或通过把它放进结构字段来制造结论。

## 3. 明确非目标和接口边界

本轮完成的是点态、有限维、光滑函数的微分恒等式。不得声称已经得到：

- `‖∇P_t f‖² ≤ P_t(‖∇f‖²)`；
- `‖∇P_t f‖ ≤ P_t(‖∇f‖)`；
- `P_t f` 的光滑代表；
- `D(A)` 或闭梯度域在半群下稳定；
- 对时间求导、积分与极限交换；
- 一般非光滑对数凹律、带边界支撑或低维支撑的结果；
- `C_c∞` 是 `A` 的 operator core；
- 完整 Buser 或常数 π。

尤其不要对任意 `L²` 代表直接调用经典 `gradient`。半群连接留给后续 S 阶段。

## 4. 审计要求

新增 `research/audits/BakryEmeryBochnerAudit.lean`，至少包含：

- `route_B0`
- `route_B1`
- `route_B2`
- `route_B3`
- `route_B4`

这些命题必须逐字覆盖 `research/audits/BakryEmeryRouteStatements.lean` 中的候选范围，
而不是较弱替代品。每个 route theorem 应由实际库声明直接证明。

审计还应包含少量边界检查：

- `U = 0` 时退化为欧氏 Bochner 恒等式；
- 仿射 `f` 时 Hessian 平方项为零；
- 零维空间不需要额外假设；
- B4 的非负性没有符号反转。

对所有新增公开定义和定理运行 `#print axioms`。允许的依赖仅限 Mathlib 常见基础公理，
不得出现：

- `sorryAx`
- 新 `axiom`
- `admit`
- 占位证明
- 将待证结论藏入假设、结构字段或 typeclass
- 通过改变路线候选范围来“证明”较弱命题

同步更新 `BakryEmeryRouteStatements.lean` 的 existing-interface `#check` 和 B0–B4 注释，
但保留原候选命题作为精确签名审计。

## 5. 决策记录

新增 `research/decisions/2026-09-20-bochner-identification.md`，记录：

- B0–B4 的最终公开声明；
- 实际使用的 Mathlib 微分 API；
- Γ、Γ₂ 的符号和因子归一化；
- B3 中第三阶导数如何抵消；
- 固定标准正交基与 basis-independent Hilbert–Schmidt 表述的边界；
- 零维情况；
- 公理审计与复现命令；
- 下一阶段仍缺少的半群正则性、域稳定性、时间微分和极限交换。

给出三栏表：

| 已有证明 | 仅类型检查 | 仍是非形式化方案 |
| --- | --- | --- |
| G0、G1、B2、E0，以及本轮完成的 B0、B1、B3、B4 | 尚未证明但已精确写出的后续接口 | S0、平方 Γ 估计、`L¹` 梯度交换、一般测度逼近及 Buser 拼装 |

完成后 B0–B4 可以放入“已有证明”；S0、平方 Γ 估计、`L¹` 梯度交换、
一般测度逼近及 Buser 拼装仍必须留在后两栏或非形式化栏。

不得把 `thm:logconcave-cheeger-poincare-comparison`、Buser 节点或整个
Bakry–Émery 基础设施标为 proved。若同步进度文档，必须遵守 `AGENTS.md`：
从暂存的 canonical records 运行 `python3 research/progress/update.py`，保留其他未提交修改。

## 6. 验收命令

从 `formalization/` 运行：

```bash
lake env lean -DwarningAsError=true \
  FunctionalInequalities/Analysis/BakryEmery/Gamma.lean

lake env lean -DwarningAsError=true \
  FunctionalInequalities/Analysis/BakryEmery/Bochner.lean

lake env lean -DwarningAsError=true \
  ../research/audits/BakryEmeryBochnerAudit.lean

lake env lean -DwarningAsError=true \
  ../research/audits/BakryEmeryRouteStatements.lean
```

并运行：

```bash
lake build
```

再从仓库根运行：

```bash
git diff --check
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests
python3 research/verify.py
```

严格的新文件编译应为零错误、零警告。完整 `lake build` 中
`KLS/Target.lean` 的既有目标洞警告可以保留，但不得新增其他 `sorry` 或警告。

## 7. 最终汇报

最终用中文说明：

1. B0–B4 分别由哪些声明完成；
2. Bochner 公式的符号和 factor `1/2` 是否与扩散生成元约定一致；
3. Hessian 平方目前是固定标准基表达，还是已经证明了基无关性；
4. 公理审计和全部验证结果；
5. 真正剩余的半群接口缺口；
6. 推荐的下一最小证明任务。

不要提交、不要推送。
