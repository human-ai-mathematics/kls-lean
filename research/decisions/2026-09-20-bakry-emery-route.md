# Bakry--Émery 路线：生成元识别、Bochner 接口与 Buser 出口

日期：2026-09-20。

本记录是路线审查，不是 Buser 证明。当前仓库已经从闭加权梯度
`T` 构造出 `A = T*T >= 0` 与 `P_t = exp(-tA)`，并证明了所述 `L2` Markov 性；本轮审计文件
`research/audits/BakryEmeryRouteStatements.lean` 只把下一批命题精确类型化。它没有引入
`axiom`、`sorry` 或占位证明，也没有把完整 Buser 目标藏进假设。

完整终点保持不变：对任意有限维、任意（可退化、可有边界、可不光滑）对数凹概率律 `mu`，证明

```text
Psi_KLS(mu)^2 <= pi * C_P^lit(mu).
```

光滑全维模型只是建立分析引擎的中间层，不能替换这个终点。

## 1. 已核对的仓库基线

以下结论已经是 Lean 定理。

- `heatSemigroup m B hmu hi` 是 `L2(mu)` 上由闭算子 `T` 的非负自伴随算子
  `A = T*T` 生成的 `P_t = exp(-tA)`；`heatSemigroup_generator` 在 `D(A)` 上给出右导数
  `-A`。
- `heatSemigroup_positive`、`heatSemigroup_one`、`heatSemigroup_subMarkov`、
  `integral_heatSemigroup`、`abs_heatSemigroup_le`、`abs_heatSemigroup_le_const` 已证。
  它们仍是 `L2` 结论；仓库尚未构造一个独立的全 `L1` 半群。
- `closedWeightedOperator m B hmu hi` 是加权梯度算子的闭包；
  `weighted_relaxation_of_mem` 把其范数平方识别为原始算子预能量的序列松弛。
- `SmoothGradient.relaxation_eq_two_mul_cheeger` 已把仓库的坐标规范固定为
  `E^can = SmoothGradient.relaxation = 2 Ch`。
- 文献 Poincare 常数与梯度测试类、内禀仿射支撑、Cheeger 正向不等式，以及仿射维数至多一时常数
  `12` 的 Buser 半都已分别形式化。高维常数 `pi` 仍未形式化。

因此旧交接里的半群生成、S6/S7/S8 与基础 Markov 待办已经过时；本路线从微分生成元识别开始。

## 2. 文献定位和常数核查

使用的主版本是 De Ponti--Mondino, arXiv:1902.03835v2（2020-01-14；后发表于 JGA 31
(2021), 2416--2438），而不是只依据摘要。关键定位如下。

- 定义 (2) 的 `lambda_1` 使用 `int |Df|^2 dm / int f^2 dm`，没有把 Cheeger 能量中的
  `1/2` 放入 Rayleigh 分子。
- (27) 是 Savare 型自改进梯度估计
  `|D H_t f|^(2 alpha) <= exp(-2 alpha K t) H_t(|Df|^(2 alpha))`；取
  `alpha = 1/2` 得 (28) 的 `L1` 型交换
  `|D H_t f| <= exp(-K t) H_t |Df|`。只证明平方形式 `Gamma(H_t f) <= H_t Gamma(f)`
  不足以直接替代这个输入。
- Proposition 3.1 的 (32) 是 Bakry--Gentil--Ledoux 反向估计；(33) 给出从有界函数到
  梯度 `L-infinity` 的热正则化界。这是 sharp Buser 拼装中的另一条关键估计。
- (46)--(47) 是谱隙产生的 `L2` 衰减/能量微分；(48) 是由 (28) 与 BV 对偶得到的
  `L1` 小时间估计；(49)--(51) 完成 Buser 拼装。
- Corollary 1.2 的 (12) 在 `K = 0`、概率测度情形给出
  `lambda_1 <= (4/pi) h^2 inf_{T>0} T/(1-exp(-T))^2 < pi h^2`。
  取倒数并按 Blueprint 已核对的 `h`、`Psi_KLS = h^{-1}` 与
  `C_P^lit = lambda_1^{-1}` 约定，正是 `Psi_KLS^2 <= pi C_P^lit`。

Klartag, arXiv:2303.14938v2 / Ars Inveniendi Analytica 2023 的 (1.4) 写成
`1/4 <= psi_mu^2 / C_P(mu) <= pi`；其 `C_P` 也使用 `int |grad f|^2`。Blueprint 的
`thm:logconcave-cheeger-poincare-comparison` 采用同一规范，并已另外记录 metric-BV perimeter、
Minkowski infimum 与 smooth relative-perimeter infimum之间还需要的前端转移。

结论：为了保留常数 `pi`，接口不能止于一般的 `Gamma` 收缩。至少需要能推出文献 (28)、
Proposition 3.1/(33) 以及 (48) 的强度；本轮的 Bochner 层必须按这个终点设计。

## 3. 光滑凸位势模型

先固定有限维实内积空间 `E`、Haar/Lebesgue 测度 `m` 与势函数 `U : E -> R`。要求：

1. `U` 至少 `C-infinity`（局部 Bochner 本身只用有限阶，但半群正则性宜先保留无穷光滑）；
2. `ConvexOn R univ U`；
3. `exp(-U)` 对 `m` 可积。凸性本身不蕴含这条；
4. 归一化常数 `Z = int exp(-U) dm` 满足 `0 < Z < infinity`，并取
   `mu = Z^{-1} exp(-U) m`，在 Mathlib 中可由 `m.tilted (-U)` 表达；
5. 初始测试函数取 `C_c^infinity(E)`，因而函数、梯度和有限阶导数在 `mu` 下属于所需的
   `Lp`；
6. 全维模型的支撑内点非空。对处处有限的光滑势，目标是进一步证明支撑为 `univ`，而不是
   把这一事实默认为构造字段。

记

```text
L f = Delta f - <grad U, grad f>,
T f = grad f,
A = T*T,
P_t = exp(-t A).
```

符号目标是 `A f = -L f`，所以现有半群的微分方程为 `d/dt P_t f = L P_t f`。

## 4. 生成元接口

### G0：带权分部积分

对 `f,g in C_c^infinity(E)` 先证明

```text
int <grad f, grad g> dmu = int (-L f) g dmu.
```

现有可复用 API 是 Haar 测度下的
`integral_bilinear_fderiv_right_eq_neg_left_of_integrable`、`gradient`/
`fderiv` 与 tilted-measure 定义。仍缺：

- 对 `exp(-U)` 的导数链式法则及乘积导数整理；
- 全部可积性/支撑条件的机械证明；
- 从 tilted integral 回到 Haar integral 再返回 `mu` 的封装。

*附注（2026-09-20，实施）。* `G0` 已证：`Analysis.BakryEmery.integral_mul_inner_gradient_eq_neg`（Haar 形式）、
`Analysis.BakryEmery.integral_inner_gradient_tilted`（tilted 形式）、`KLS.LogConcave.integral_inner_gradient_eq`
（概率律形式），实际只需 `U ∈ C¹`、`f ∈ C²`、`g ∈ C¹`（`g` 不必紧支撑）。见
[实施记录](2026-09-20-generator-identification.md)。

### G1：测试函数上的算子识别

从 G0 证明每个 `f in C_c^infinity(E)` 满足：

```text
-L f in L2(mu),
[f] in D(A),
A[f] = [-L f].
```

关键点是使用伴随定义：先由 G0 对闭梯度域的核证明内积恒等式，再用图范数稠密性延拓到
`D(T)`，最后把 `T f` 放进 `D(T*)`。只算出形式微分表达式不能得到 `D(T*T)`。

必须保持四层区别：

1. `C_c^infinity` 上微分表达式一致；
2. 它对一阶闭形式是 form core；
3. 它是否在 `D(A)` 的图范数下是 operator core；
4. 微分算子的闭包是否等于完整的 `A`。

现有 `closure_domRestrict_eq_of_smoothCore_le` 只提供第 2 层的一阶梯度闭包信息，不自动提供
第 3 或第 4 层。本路线只要求先完成第 1 层的 `D(A)` 包含和作用值识别。

*附注（2026-09-20，实施）。* 第 1 层已证：`KLS.LogConcave.memLp_neg_weightedLaplacian`、
`KLS.LogConcave.toLp_mem_adjointComp_domain`、`KLS.LogConcave.adjointComp_toLp_eq`
（`KLS/LogConcave/HeatSemigroup/Generator.lean`），正是按上述伴随路线：`G0` 给光滑核上的弱恒等式，
`Analysis.Semigroup.inner_eq_inner_closure_apply` 沿图闭包延拓到 `D(T̄)`，再用伴随定义。第 3、4 层仍未证明。
见[实施记录](2026-09-20-generator-identification.md)。

## 5. Gamma、Gamma2 与 Bochner

采用扩散生成元 `L` 的符号：

```text
Gamma(f,g) = (L(fg) - f Lg - g Lf)/2,
Gamma(f,g) = <grad f, grad g>,
Gamma2(f) = L(Gamma(f,f))/2 - Gamma(f,Lf).
```

### 可直接使用的 API

- `Laplacian.laplacian` 与
  `laplacian_eq_iteratedFDeriv_orthonormalBasis`；
- `bilinearIteratedFDerivTwo`；
- `stdOrthonormalBasis`；
- Mathlib 的二阶导数对称性定理可作为混合偏导交换的底层输入；本轮新增
  `Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm`，已把它封装为路线直接使用的 Hessian
  对称性定理（B2）。

### 缺失接口

- 没有现成的 `Gamma`/`Gamma2` 定义；
- 没有适合当前 Hessian 表示的命名 Hilbert--Schmidt 范数与基无关性定理；
- 没有现成的 Laplacian 乘积公式、`grad ||grad f||^2`、`Delta ||grad f||^2` 与
  Hessian contraction 的整套重写；
- 仍需把 `C2` 凸性连接到
  `bilinearIteratedFDerivTwo R U x v v >= 0`。

因此第一版 Bochner 命题应诚实地固定 `stdOrthonormalBasis`：

```text
Gamma2(f)(x)
  = sum_i sum_j (D2 f(x)(e_i,e_j))^2
    + D2 U(x)(grad f(x), grad f(x)).
```

在证明双重和的基无关性后，才能导出公开的
`||Hess f||_HS^2 + Hess U(grad f,grad f)` 写法。由每项平方非负和势的 Hessian 半正定再得
`Gamma2(f) >= 0`。审计文件中的 B0--B4 精确记录了这些接口；其中 B2 已证，B0、B1、B3、
B4 目前仅通过类型检查。

## 6. 从局部 Bochner 接到现有 `P_t`

Bochner 恒等式本身不产生半群梯度交换。还缺以下桥梁。

1. **代表与正则性。** `P_t[f]` 当前只是 `L2` 等价类。要对其使用经典 `gradient`，必须证明
   `t>0` 时存在足够光滑的代表，或者完全改用闭梯度 `T(P_t f)`。
2. **域稳定性。** 需要 `P_t` 保持 `D(T)`，并在平方 Gamma 推导中保持足够高的生成元域；
   测试函数未必被 `P_t` 保持为紧支撑函数。
3. **时间微分。** 对典型插值量
   `s -> P_s Gamma(P_{t-s}f)` 证明可微，并证明导数等于 `2 P_s Gamma2(P_{t-s}f)`。
4. **交换与极限。** 需要合法交换 `P_s`、空间导数、积分和时间极限，并把测试类结论闭包到
   Sobolev/BV 类。
5. **平方估计。** 先从 `Gamma2 >= 0` 得
   `Gamma(P_t f) <= P_t Gamma(f)`。
6. **自改进。** sharp 路线还要得到文献 (27) 的 `alpha in [1/2,1]`，特别是
   `|T P_t f| <= P_t |T f|`。不能把第 5 步自动当作第 6 步。
7. **BGL 反向估计。** 还要证明 Proposition 3.1/(32)，再推出 (33) 的
   `L-infinity -> gradient L-infinity` 热正则化。

只有在这些接口之后，才进入未列为本轮验收的小时间 BV 估计
`||f-P_t f||_1 <= J_0(t) |Df|(E)` 与最终 Buser 拼装。

## 7. 能量和时间归一化

当前闭梯度约定下：

```text
||T f||_2^2 = E^can(f) = SmoothGradient.relaxation(f) = 2 Ch(f),
A = T*T,
P_t = exp(-t A),
d/dt ||P_t f||_2^2 = -2 ||T P_t f||_2^2.
```

其中最后三项与 De Ponti--Mondino 的 Rayleigh 分子 `int |Df|^2` 相容；若误把 `Ch` 本身当作
算子二次型，时间会差因子 2，最终常数也会漂移。

本轮新增 `KLS/LogConcave/CanonicalEnergy.lean`，证明了此前缺少的命名桥梁：

- `exists_smoothGradient_localDensity` 从 Borell 密度构造 smooth-core 比较所需的局部密度包；
- `weightedRelaxation_id_eq_smoothGradient` 逐向比较两个测试域及其能量；
- `closedWeightedOperator_id_energy_eq_smoothGradient` 给出闭单位权算子的范数平方形式等于
  canonical energy；
- `closedWeightedOperator_id_energy_eq_two_mul_cheeger` 最终给出 `||Tf||^2 = 2 Ch(f)`。

因此审计文件 E0 已从候选接口变为已证命题。证明没有凭名字认定两个能量相等：一个方向使用
由 Borell 密度得到的 smooth-core recovery，另一个方向把全局 Lipschitz 算子测试嵌入
local-slope 测试类，再使用已证的 smooth/local-slope 识别。

谱隙规范为

```text
Var_mu(f) <= C_P^lit(mu) * ||T f||_2^2,
lambda_1 = 1 / C_P^lit(mu).
```

由此预期 `||P_t f||_2 <= exp(-lambda_1 t) ||f||_2`（均值零），平方范数的指数为
`exp(-2 lambda_1 t)`。

## 8. 从光滑全维模型走向任意对数凹律

推荐的主出口是**内禀仿射支撑上的凸势/闭形式逼近**，因为仓库已经有
`intrinsicMeasure`、内禀 Haar 测度、闭加权梯度和 canonical energy。直接把当前对象宣称为
RCD 空间会引入更大的未形式化黑箱；把支撑边界预先解释成经典 Neumann 边界也没有依据。

### 8.1 降维与 Dirac

- 先把任意 `mu` 推到其 affine support 的 direction space；这里内禀律全维。
- 正维时在该空间工作，再把 Poincare 常数、isoperimetric scale、能量和半群结论运回。
- 零维/Dirac 单独证明：`Psi_KLS = 0`、`C_P^lit = 0`，不通过热流极限硬编码。

### 8.2 非光滑势和边界

一般全维对数凹律可写成 `exp(-W) dx`，其中 `W` 是取值于扩展实数的下半连续凸函数；
`W = +infinity` 的区域正是支撑约束。候选逼近：

1. 用 Moreau--Yosida 包络得到有限、凸、`C1` 的势；Moreau 包络本身不是 `C-infinity`；
2. 再卷积平滑，并加 `epsilon ||x||^2` 保证可积与严格尾部；
3. 重新归一化，必要时对逼近势作常数平移；
4. 令平滑尺度和 `epsilon` 同时趋零，使概率律弱收敛到目标律，包括带凸支撑边界的情形。

边界条件应由闭形式极限产生；它可能表现为自然/反射边界，但不能先假设一个经典 Neumann
迹理论再声称与当前闭梯度相同。

### 8.3 必须证明的稳定性

- 在变化测度的 `L2(mu_n)` 上给出统一的搬运/嵌入框架；
- 闭二次型的 Mosco 收敛；
- 预解 `(I+A_n)^{-1}` 和半群 `P_t^n` 的强收敛；
- `alpha=1/2` 梯度估计与 BGL 估计在极限下稳定；
- BV 全变差/周长的下半连续及恢复序列，从而小时间估计传到目标律；
- Poincare 常数、Cheeger infimum 与最终 `pi` 常数的方向正确的半连续性；
- 仿射降维过程中上述收敛与常数保持。

若改走 RCD 路线，则还必须形式化：闭凸支撑带加权欧氏距离测度是 `RCD(0,infinity)`、当前
Cheeger 能量/半群与 RCD 对象一致、De Ponti--Mondino 的 BV perimeter 与仓库的 Minkowski/
relative-perimeter infimum一致。这个方案数学上直接引用主定理，但与当前 Lean API 的距离更远；
故不推荐作为第一实现路线。

## 9. 状态三栏

| 已有证明 | 仅通过类型检查 | 仍是非形式化方案 |
|---|---|---|
| `L2` 半群、生成元 `-T*T`、保正/保一/质量守恒/次 Markov | N0 光滑 tilted 概率模型包 | tilted 模型的完整构造与支撑证明 |
| 闭加权梯度及其算子预能量松弛；单位权闭算子能量 `= E^can = 2 Ch`；**G0 带权分部积分（2026-09-20 实施轮）** | — | — |
| `SmoothGradient.relaxation = 2 Ch`；B2 Hessian 对称性；**G1 在 `C_c^infinity` 上 `A=-L`，含 `D(A)` 成员关系（同轮）** | — | operator core / 闭包等同（第 3、4 层） |
| 文献 Poincare 测试类识别 | B0、B1、B3、B4：Gamma、凸 Hessian、坐标 Bochner、非负性 | Bochner 的代数证明和 HS 基无关性 |
| Cheeger 半与一维常数 12 | S0：`P_t f` 光滑代表候选；两种梯度交换候选 | 半群正则性、域稳定、时间微分、自改进、BGL |
| 内禀仿射支撑基础设施；E0 单位权能量桥梁 | S0 中的平方与 `L1` 梯度候选（不同强度） | Mosco/预解/半群/BV/周长/常数极限稳定性 |

“仅通过类型检查”只表示候选命题在当前 Lean/Mathlib 中可陈述，不表示命题已证。

## 10. 推荐的独立证明切口

*附注（2026-09-20，实施）。* 下面的五步已在同日完成，见[实施记录](2026-09-20-generator-identification.md)；
下一切口转为 B0/B1，然后是第 6 节的代表与域稳定性。

下一轮最小且不浪费的证明任务是 **G0 + G1 的测试函数生成元识别**：

1. 先封装 tilted smooth density 的积分改写与 `exp(-U)` 导数；
2. 证明 G0；
3. 证明 `-L f in L2(mu)`；
4. 使用现有 smooth form core 与伴随定义证明 G1；
5. 保持结论严格限于 `C_c^infinity`，不声称 operator core 或完整算子等同。

E0 与 B2 已在本轮完成。B0/B1 适合随后作为纯局部微分模块；B3 的 Bochner 展开应等
Hessian/混合导数辅助引理稳定后再做。完整 Buser 仍需要第 6--8 节的链条，
不能把任一局部 lemma 的完成误报为比较节点完成。

## 参考

- N. De Ponti and A. Mondino, *Sharp Cheeger--Buser Type Inequalities in RCD(K,infinity)
  Spaces*, arXiv:1902.03835v2, especially (2), (12), (27)--(28), Proposition 3.1,
  (46)--(51).
- B. Klartag, *Logarithmic Bounds for Isoperimetry and Slices of Convex Sets*,
  arXiv:2303.14938v2, especially (1.4).
