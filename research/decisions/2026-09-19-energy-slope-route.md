# Energy 五洞的路线探查：奇异律的 `𝓔^can = 2Ch`

2026-09-19。Cheeger 线闭合后，Owner 指示接着做 Energy 五洞——最后一个 WIP 模块 `Energy/WIP/Cheeger.lean`。
本轮是**路线探查**，**没有证明任何定理**，没有改动任何既有 `.lean`；交付物是只含 `#check` 的路线语句文件
`research/audits/EnergySlopeRouteStatements.lean`（19 条命题 + 5 条已证声明引用）。**命题通过类型检查不是证明。**
直接洞仍 **5（0/0/5）**，证书仍 **25**。不提交、不推送。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T141537.829419Z/report.json`：10 个门、237 个模块重放、650 条目，快照 `f91b06cac5cf4d62e270ae9ec48c1d6c2459fa53583be0b4f06a51d7baa3aa4c`。

## 五个洞的真实结构

WIP 模块对任意 Borel 概率律 `ν` 陈述：`E0a` 光滑梯度松弛 = 松弛平方局部斜率；`E0b` 两种 Cheeger 约定松弛相同；
`E0c` 两种 Cheeger 能量相同；`E0d` 坐标空间上 `𝓔 = 2Ch`；`E0e` Blueprint 恒等式 `thm:smooth-gradient-relaxation-two-cheeger`。
已认证的 `cor:absolutely-continuous-relaxation-two-cheeger` 在绝对连续律上证了全部五条。**真正的义务只有 `E0a`**：
`E0b` 由夹逼 `LocalSlope ≤ AsymptoticLipschitz ≤ SmoothGradient`（`A2`）在 `E0a` 压塌两端后得到（`A3`），
`E0c` 是 `E0b` 除以 2，`E0d` 是 `Cheeger.two_mul_energy`，`E0e` 是 `E0a` 用于内禀律后照抄已认证推论的搬运。
WIP 模块给 `E0b` 引 Ambrosio–Gigli–Savaré 方向引错了：奇异情形需要的是**光滑测试在局部斜率能量中的稠密性**，
即无密度假设的反向不等式 `SmoothGradient.relaxation ≤ LocalSlope.relaxation`（`C6`）。

## 路线

**A 夹逼**（`Energy/Euclidean/SlopeComparison.lean`）：光滑测试的渐近 Lipschitz 常数逐点等于梯度范数（`A1`，
下界由一动点斜率已取到，上界是小球上的中值不等式），于是光滑测试落在渐近 Lipschitz 测试类里且能量相同，
在更大的类上松弛更小（`A2`）；`A3` 记录压塌。

**B 全局 Lipschitz 测试的磨光恢复**（`Energy/Euclidean/SlopeRecovery.lean`）：以半径 `2R` 磨光全局 `K`-Lipschitz 的 `g`，
磨光在一点只看 `2R` 以内，故在半径 `δ` 球上继承 `g` 在半径 `δ+2R` 球上的 Lipschitz 常数，得
`limsup_R ‖∇(g⋆ρ_R)(x)‖ ≤ Lip_a g(x)`；全局常数一致控制被积函数，反向 Fatou 适用，得 `B1`。
**统一半径对一般测试真的不够**（`D1`：`ν = Σ2⁻ⁿδ_n` 加窄尖峰）。故需化约工具：局部 Lipschitz 乘有界全局 Lipschitz 仍局部
Lipschitz（`B2`），局部 Lipschitz 且球外为零 ⟹ 全局 Lipschitz（`B3`），两种斜率的一动点 Leibniz 界（`B4`、`B5`）。

**C 稠密性**（`Energy/Euclidean/SlopeDensity.lean`）：`C1` 连续函数的局部斜率 Borel（半径 `1/(m+1)` 的割线上确界下半连续，
可数下确界）。`C2` McShane 补丁：全局 `L`-Lipschitz 的 `f`，斜率按宽 `α` 分层、每层切成稠密序列的小球、`disjointed` 得 Borel 分割，
块上 `f` 的 Lipschitz 常数与斜率相差 `≤ 2α`；内正则性取有限个两两不交的紧核，余质量 `≤ δ`；每核上 McShane 延拓、按核间距以下的
尺度用线性截断粘合；补丁 `F` 全局 Lipschitz 常数 `9L + 8α` 与 `δ` 无关，在核上等于 `f`，核上渐近 Lipschitz 常数与 `f` 的斜率
相差 `≤ 2α`。`C4`：取 `α = δ = 1/(n+1)`，补丁在 `L²(ν)` 收敛到 `g`，`B1` 把每个补丁处的松弛压到其渐近 Lipschitz 能量，
后者 `≤ (1+4α)·LocalSlope.energy g + 4α + 4α² + M²δ`（用可测控制函数，不需要渐近常数可测），松弛下半连续收尾。
`C5`：一般可容许测试用 `scaled (n+1)` 截断，`B2`、`B3` 使截断全局 Lipschitz，控制收敛给 `L²` 收敛，`B5` 加 Young 不等式
`(a+b)² ≤ (1+θ)a² + (1+θ⁻¹)b²` 给能量界，先 `n → ∞` 再 `θ → 0`。`C6` 是 `C5` 喂给 `LocalSlope.le_relaxation_of_lowerSemicontinuous`。

最接近的文献：S. Eriksson-Bique, *Density of Lipschitz functions in energy*, Calc. Var. PDE 62 (2023), Art. 60, Thm 1.1
（一般度量测度空间），本欧氏论证是其初等特例；Ambrosio–Gigli–Savaré, Rev. Mat. Iberoam. 29 (2013) §8.3 经 Hopf–Lax 得同一结论。

## 义务清单

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `E0a`–`E0e` | **五个洞**，逐字 | 60（迁入 + 合成） | 低（由 `A`、`C` 合成） |
| `A1` | 光滑测试的渐近 Lipschitz 常数 = 梯度范数 | 80 | 低 |
| `A2` | `AsymptoticLipschitz.relaxation ≤ SmoothGradient.relaxation` | 40 | 低 |
| `A3` | 压塌 | 15 | 低 |
| `B1` | 全局 Lipschitz 测试的磨光恢复 | 250 | 中 |
| `B2`, `B3` | 化约工具（局部 Lipschitz 的乘积；球外为零 ⟹ 全局） | 80 | 低 |
| `B4`, `B5` | 一动点 Leibniz 界 | 60 | 低 |
| `C1` | 局部斜率可测 | 80 | 低–中 |
| `C2` | **McShane 补丁** | 500 | **高**（唯一的单点判据） |
| `C4` | 全局 Lipschitz 测试的稠密性 | 150 | 中 |
| `C5` | 全部可容许测试 | 150 | 中 |
| `C6` | 反向不等式 | 20 | 低 |
| `D1` | 诊断（统一半径不够），非义务 | — | 不是步骤 |

合计约 **1500 行**。推荐顺序：`A1`–`A3` 与 `B` 并行；`C1`、`C2`、`C4`、`C5`、`C6`；最后 `E0a`–`E0e` 合成并迁移注册
（`thm:smooth-gradient-relaxation-two-cheeger` 成为第 26 个证书）。

## 验证

路线文件以 `lake env lean -DwarningAsError=true` 通过，24 个 `#check`，0 错误、0 警告，不 import WIP；
日志 `build/audit/energy-slope-route/route-statements.log`。回执在紧接的实现轮绑定。

## 附记（2026-09-19，实现轮之后）

`A1`–`A3`、`B1`–`B5`、`C1`–`C6` 全部按字面证出（`Energy/Euclidean/{SlopeComparison,SlopeRecovery,SlopeDensity}.lean`），
`E0a`–`E0e` 在 `Energy/Cheeger/Identification.lean` 合成并迁入。实现修正：`C2` 的库形式多带一条一致界 `|F − f| ≤ 2L + 2α`
（`C4` 的 `L²` 收敛所必需，补丁不逐点收敛），块常数比路线紧一个 `α`；`B4` 需要路线正文略去的 `O(r)` 修正；空紧核须剔除
（`Metric.infDist x ∅ = 0`）。`D1` 未形式化。见 [实现记录](2026-09-19-energy-slope-proofs.md)。
