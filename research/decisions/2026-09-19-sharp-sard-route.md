# 尖锐有限正则 Sard 的路线探查：Morse 分解，而非超曲面降维

2026-09-19。本轮是**路线探查**，**没有证明任何定理**，没有新增任何库模块，
没有修改任何既有 `.lean`。交付物是：直接洞 `Analysis.sard` 为什么不能沿光滑版
`sard_smooth` 的降维归纳关闭的精确定位、Mathlib 与本仓库的如实检索、
带编号的义务清单（每条配精确 Lean 语句、行数与风险），以及只含 `#check` 的路线语句文件
`research/audits/SharpSardRouteStatements.lean`。
**命题通过类型检查不是证明**；下面的义务**没有一条**在本仓库中被证明。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T113053.092417Z/report.json`：10 个门、224 个本地模块内核重放、
614 条目，快照 `ab7dbfd7775b140596404611efbaa12b7b863a7c9ef3f2f86065976b79d8f80b`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。Energy 的五个洞、无量纲 KLS 也都未触碰。
本轮只针对实值靶的尖锐 `C^n` Sard；向量值靶、临界值的 Hausdorff 测度、
Whitney 反例（尖锐性本身）都不在本路线之内。

## 零、这个洞对下游意味着什么

[2026-09-15 的路线探查](2026-09-15-smooth-sard-route.md)已经查明：`Analysis.sard` 的唯一消费者
`ae_forall_fderiv_ne_zero` 的唯一消费者 `SmoothDomain.ae_exists_superlevel` 假设 `C^∞`，
而 `C^∞` 版 `sard_smooth` 与 `ae_forall_fderiv_ne_zero_of_contDiff_top` 已证。
所以这个洞**不阻塞任何 KLS 链条**；关闭它是 `Analysis/` 层分析基础本身的完成，
收益是直接洞 8 → 7（1/2/5 → 0/2/5）、`KLS/WIP/AnalyticPrerequisites.lean` 清空并按先例删除，
以及 `ae_forall_fderiv_ne_zero` 脱离 `sorryAx`。语句本身一字不改。

## 一、障碍的精确定位：降维归纳在中间层丢正则性

`Analysis/Sard/Smooth.lean` 的 `sard_smooth_pi` 按导数消失的阶数把临界集分层
（`critical_subset_layers`）：全平坦层由覆盖计数 `volume_image_flat_pow_univ_eq_zero` 处理；
第 `j` 层（`1 ≤ j < n`，`≤ j` 阶导数为零、`j+1` 阶不为零）取一个 `j` 阶导数分量 `w`
（`exists_flat_direction`），它在该层为零、微分不为零，于是层局部落在 `w` 的正则零点集上，
这是一个超曲面图像（`exists_local_graph`），把 `u` 限制到图像上再对维数归纳。

有限正则时**这一步在 `j ≥ 2` 失效**。`u ∈ C^n` 时 `w ∈ C^{n−j}`，图像映射 `C^{n−j}`，
限制 `u ∘ ψ ∈ C^{n−j}`（路线文件的 `D1` 记录了这条正则性账目：复合只保住较低的那个阶）；
而 `n−1` 维的归纳假设要 `C^{n−1}`。`j = 1` 恰好够，`j ≥ 2` 差 `j−1` 阶。
这正是 Milnor 的证明要求 `C^∞` 的原因，也是 2026-09-15 那轮把目标改成 `C^∞` 的原因
（它当时的结论「`n = 4, j = 2` 是第一个盖不住的情形」与此一致）。
**任何先限制 `u`、再降维的方案都要在这里付出正则性**，改分层方式救不了。

## 二、路线：Morse（1939）的分解——对集合归纳，不对函数降维

按 A. P. Morse, *The behavior of a function on its critical set*, Ann. of Math. 40 (1939) 62–70，
表述取 A. Norton, *The Zygmund Morse–Sard theorem*, J. Geom. Anal. 4 (1994) 403–424
从 Zygmund 类退回到 `C^k` 的版本。核心对象不是 `u`，而是**任意**集合 `A ⊆ ℝⁿ` 的 **Morse 分解**：

* **`C¹` 参数盘**：某个 `Fin p → ℝ` 到 `Fin n → ℝ` 的 `C¹` 映射 `φ`，在闭单位球上反 Lipschitz；
  本体 `φ '' closedBall 0 1`；`φ a` 到 `φ b` 的**参数线段**是直线段 `[a, b]` 的像。
* **沿盘的 `k` 阶平坦**：一致小 o 意义下，`x, y ∈ S` 足够近、`z` 在参数线段上时 `|f z| ≤ ε ‖x − z‖^k`。
* **Morse 消失引理（`M3`）**：任何 `A` 都有任意阶 `k` 的分解——可数集 `A₀` 加可数个由盘承载的片
  覆盖 `A`，使**每个**在 `A` 上为零的 `C^k` 函数在每片上沿其盘 `k` 阶平坦。
  证明是对 `(n, k)` 的双重归纳，**两个方向都不丢正则性**：
  - `k = 0`：紧本体上的一致连续；`n = 0`：平凡。
  - `k → k+1`（固定 `n`，**临界部分**）：把 `A` 分成 `U`（所有在 `A` 上为零的 `C^{k+1}` 函数都在此临界）与 `V`。
    `U` 用 `U` 自己的 `k` 阶分解：`fderiv f` 的各坐标是 `C^k`、在 `U` 上为零、故 `k` 阶平坦，
    再由沿参数线段的中值步骤 `M2` 升一阶。
  - `n → n+1`（固定 `k`，**正则部分**）：`V` 的每点附近有某个在 `A` 上为零的 `g ∈ C^k` 微分非零，
    `A`——从而 `V`——局部落在一个 `n` 个坐标的 `C^k` 函数图像上（`M1`）；
    对图像原像用 `n` 维、**同一个 `k`** 的归纳假设，再沿图像映射推前。
    图像映射 **1-反 Lipschitz**（`M1'`），所有估计常数不变。第二可数性让局部分解只需可数个。
  这就是它与降维归纳的本质区别：归纳假设量化的是**所有集合**，阶数 `k` 不变，
  所以被限制的从来不是 `u`，而是「在 `A` 上为零的函数」这一类——它在图像上仍是 `C^k`，恰好够用。
* **Morse 临界引理（`M4`）**：`C^{k+1}` 函数 `f` 的临界集被可数集加可数个有界片覆盖，
  每片上 `|f y − f x| ≤ ε ‖y − x‖^{k+1}` 一致小 o——`fderiv f` 的坐标是 `C^k`、在临界集上为零，
  `M3` 使之 `k` 阶平坦，`M2` 给出对 `f` 的估计。这一步后盘与平坦性都已消失，只剩 Mathlib 概念。
* **收尾（`M5`）**：`k + 1 = n`，每片用**已证的**覆盖计数 `volume_image_eq_zero_of_oscillation_pow`
  （有界集上一致 `o(‖y−x‖ⁿ)` 模数 ⟹ 像零测），可数集像可数，可数并零测；`n = 0` 时像是一个点。
* **搬运（`M6`）**：由 `Fin n → ℝ` 到任意有限维赋范空间沿 `ContinuousLinearEquiv.ofFinrankEq`，
  与 `sard_smooth` 的搬运逐字相同。`M6` 的语句必须与 `KLS/WIP/AnalyticPrerequisites.lean`
  中 `Analysis.sard` 的 `pp.all` 打印逐字节一致，迁移时按先例机器比对。

**没有** Whitney 扩张、**没有** Kirszbraun、**没有**流形框架、**没有**逼近分片。

## 三、Mathlib 与本仓库有什么、缺什么（如实检索）

**Mathlib 没有的**：没有 Morse–Sard 的任何版本（全库 `Morse` 零命中）；
`HausdorffDimension.lean` 里叫「Sard 的特例」的两条只给像的补集**稠密**，不给零测；
没有 Morse 分解、没有「沿盘平坦」。

**Mathlib 有的、本路线要用的**：`C^k` 反函数定理 `ContDiffAt.to_localInverse`
（`M1` 的核心，`exists_local_graph` 的光滑版正是这样用的）；`Fin.insertNth` / `Fin.removeNth`
（只有定义与逐点引理；它们的 `ContDiff` 与 1-反 Lipschitz 性质要自证，后者即 `M1'`）；`ContDiff.fderiv_right`、
`ContinuousLinearMap.apply` 的 `ContDiff`（`fderiv f` 的坐标是 `C^k`）；中值不等式
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` 一线（`M2`）；`Set.Countable` 与第二可数性
（`M3` 的可数覆盖）。

**本仓库有的**：`volume_image_eq_zero_of_oscillation_pow`（`M0`，`Analysis/QuadraticCover.lean`，已证）；
`exists_contDiff_eventuallyEq`、`exists_local_graph`（`C^∞` 版图像，`Analysis/Sard/Smooth.lean`，
`M1` 的模板）；`sard_smooth` 的搬运段（`M6` 的模板）；`sard_plane`（`n = 2` 的独立验证）。

**缺的**：`M1`–`M6` 全部。

## 四、义务清单

精确 Lean 语句在 `research/audits/SharpSardRouteStatements.lean`，按本表编号排列；
该文件只含 `#check`，无声明、无证明、无占位公理，以 `-DwarningAsError=true` 通过。
**通过类型检查不是证明。**

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `M0` | 覆盖计数：有界集上一致 `o(‖y−x‖ⁿ)` ⟹ 像零测 | — | **已证** |
| `M1` | `C^k` 正则零点集的图像刻画：`w x = 0 → x = insertNth i (θ (removeNth i x)) (removeNth i x)` | 250 | 低–中 |
| `M1'` | 图像映射 1-反 Lipschitz | 20 | 低 |
| `M2` | 中值步骤：`fderiv f` 各坐标沿盘 `k` 阶平坦 ⟹ `f` 沿盘 `k+1` 阶平坦 | 250 | 中 |
| `M3` | **Morse 消失引理**：任意集合有任意阶 Morse 分解 | 300 | **高**（双重归纳；沿图像推前分解） |
| `M4` | Morse 临界引理：`C^{k+1}` 函数的临界集被可数集加可数有界片覆盖，每片一致 `o(‖y−x‖^{k+1})` | 60 | 低（`M2`+`M3`） |
| `M5` | `Fin n → ℝ` 上 `C^n` 实值函数的 Sard | 40 | 低（`M4`+`M0`） |
| `M6` | **目标**：`Analysis.sard`，逐字 | 40 | 低（与 `sard_smooth` 同一搬运） |
| `D1` | 诊断（真，且平凡）：`C^k` 函数限制到 `C^k` 图像只剩 `C^k`——记录降维方案丢阶的账目 | — | 不是步骤 |

合计约 **1000 行**。推荐顺序：`M1'`、`M1`、`M2`、`M3`（先 `k = 0` 与 `n = 0` 两个底，再临界步、再正则步）、
`M4`、`M5`、`M6`。`M3` 是唯一高风险项，也是路线成立与否的单点判据：
它一旦证出，`M4`–`M6` 是机械的。
实现时可在 `Analysis/Sard/` 下新增模块并引入 `Disk`、`FlatAlong`、`HasDecompRel` 之类的辅助定义；
路线语句刻意**不**用这些定义书写，以便审计客户端逐字复述并 discharge。

## 五、明确没证什么

* **没有证明任何 Sard 定理**；`Analysis.sard` 仍是直接洞，语句与位置不变。
* 只讨论实值靶；向量值靶（`C^{n−m+1}`）、临界值的 Hausdorff 测度、Whitney 的 `C^{n−1}` 反例都不在路线内。
* Cheeger 两洞归王浩丞，Energy 五洞未触碰；无量纲 KLS 仍开。

## 六、验证

`research/audits/SharpSardRouteStatements.lean` 以 `lake env lean -DwarningAsError=true` 通过，
11 个 `#check`（3 个引用已证声明，8 个义务与诊断命题），0 错误、0 警告；
本地 import 闭包不含 WIP 文件。
未修改任何库源码、未改聚合导入。根目录 `python3 research/verify.py` 于本轮结束时重跑，
最终回执记于 `build/audit/sharp-sard-route/final-snapshot.json`，快照与工作区逐条重算，drift 为空。
详见 `research/explorations/2026-09-19-sharp-sard-route.json`。

## 附记（2026-09-19，实现轮之后）

* **`M2` 按字面为假。** 证明会话给出笔算反例（`n = 2, p = 1, k = 0`）：`C¹` 螺线
  `φ t = (t³ cos(1/t), t³ sin(1/t))`，`S` 取它与正 `x` 轴的交点（无穷多个尺度），`f` 在第 `m` 圈上的梯度
  约 `m^{-1/2}` 且沿螺线单调；参数线段的弧长约为弦长的 `m` 倍，两侧之比按 `m^{1/2}` 发散。
  路线记录里「`M2` 不需要 `φ` 的反 Lipschitz 常数」这句话是错的。反例**未形式化**。
* 加上盘的反 Lipschitz 界之后的 `M2`（`route_M2_antilipschitz`，`MorseSard.abs_sub_le_of_flat_fderiv`）已证，
  而 Morse 分解的每个盘都带这个界，所以 `M3`–`M6` 不受影响。路线语句文件保持字节不变（历史快照）。
* 其余七条（`M1`、`M1'`、`M3`–`M6`、`D1`）全部证出；`Analysis.sard` 已迁入 `Analysis/Sard/Sharp.lean`，
  见 [实现记录](2026-09-19-coarea-sard-proofs.md)。
