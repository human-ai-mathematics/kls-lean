# 2026-09-12 — 等周直径不等式的可行性判断，与下一步（仅陈述）的提示词

## 一、等周直径不等式在 Mathlib 里缺多少

### Mathlib 已有

- `MeasureTheory.hausdorffMeasure_pi_real`：在 `ι → ℝ` 上 `μH[card ι] = volume`。
  **但那是 sup 范数**，Hausdorff 测度依赖度量，故不能直接搬到欧氏（内积）范数上。
- `Mathlib/MeasureTheory/Measure/Hausdorff.lean` 中的实例：对任意有限维实赋范空间 `E`，
  `μH[finrank ℝ E]` **是一个可加 Haar 测度**（`IsAddHaarMeasure`）。
- Haar 唯一性（`Measure.isAddLeftInvariant_eq_smul`、`addHaarScalarFactor_pos_of_isAddHaarMeasure`），
  `LipschitzWith.hausdorffMeasure_image_le`、等距不变性、`Measure.addHaar_smul`、球体积。

因此 **`μH[n] = c • volume`（存在唯一的 `c ∈ (0,∞)`）是免费的**，本仓库这次已经用过同一套路。

### Mathlib 完全没有（全库搜索零命中）

- 等周直径不等式（isodiametric）、Steiner 对称化；
- 任意维数的 Brunn–Minkowski 与 Prékopa–Leindler（本仓库本轮只做了**一维**的，
  见 `Probability/Line/BrunnMinkowski.lean`）。

### 判断

缺口**不是**「从零建一套理论」，而是精确的一件事：**把常数钉成 `c = 2ⁿ/ωₙ`**，
即证明 `volume S ≤ ωₙ (diam S / 2)ⁿ`。两条经典路线：

1. **Steiner 对称化**：n 次对称化，需要保测性、直径不增、可测性保持。经典但在 Lean 里很重。
2. **经 Brunn–Minkowski**：`vol S ≤ vol(½(S − S)) ≤ vol(B(0, diam S / 2)) = ωₙ (diam S/2)ⁿ`，
   中间一步正是 n 维 Brunn–Minkowski。而 n 维 Brunn–Minkowski 的标准证法是对维数归纳 + n 维
   Prékopa–Leindler，**后者的一维基例本仓库本轮刚刚证完**（`Probability.Line.prekopaLeindler`，
   无有界性前提）。所以路线 2 有现成的起点，且中间产物（n 维 PL / BM）本身是 Mathlib 级的独立贡献。

### 但必须说清楚：它**不解锁**任何东西

`hausdorffNormalized_finrank_eq_volume`（`KLS/WIP/RelativePerimeter.lean:119`）
在**全仓库没有任何使用点**，模块文档自己写着它是
"an obligation recording the convention"。`relativePerimeter` 用的是
`surfaceMeasure = hausdorffNormalized (n−1)`，n 维那条从不被调用。

所以：等周直径不等式是这条链上**最自足、最可做**的一块，但也是**最不承重**的一块。
真正卡住 `lem:relative-perimeter-smoothing` → … → `thm:logconcave-cheeger-poincare-comparison`
（4 个下游节点）的是另外四条：C^∞ 超曲面上 `ℋ^{n−1}` 的局部有限性、Gauss–Green（Mathlib 的散度定理
只覆盖长方体）、加权 coarea 公式、一般维数 Sard。

（更正：上一轮口头建议「先做等周直径不等式」时，我高估了它的承重程度。以本节为准。）

## 二、下一步（仅陈述）的提示词

据此，下一步值得做的不是单挑等周，而是把这条链**全部缺失的分析前提**写成精确的 Lean 陈述，
让它们从 `tasks.json` 里的散文缺口变成有类型的义务，各自可被独立攻克（或直接作为 Mathlib PR 的目标）。
本轮**只写陈述，不写证明**。

---

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交
db584cd6d46c92f209a44c0f1c829460d327499d；Lake 根目录 formalization/）。
本机 elan 与全部 Lean 工具链已是原生 arm64，lake 调 git 正常，不需要任何 git 包装脚本。

任务（**仅陈述，不证明**）：把相对周长链条所缺的分析前提写成独立、精确的 Lean 陈述，
全部证明体为 `sorry`，放进新的 WIP 模块。这些陈述必须**与 KLS 无关、可独立成立**，
即写成一般的测度论/几何分析命题，而不是夹带本仓库对象的特化形式。

背景（先读）：
- research/decisions/2026-09-12-relative-perimeter-prerequisites-statement-prompt.md（本文件第一节：
  等周直径不等式的可行性判断，以及「哪些承重、哪些不承重」）
- research/decisions/2026-09-11-relative-perimeter-smoothing-statement.md 与 -proofs.md
- research/decisions/2026-09-11-relative-perimeter-cheeger-infimum-statement.md 与 -proofs.md
- research/decisions/2026-09-12-cheeger-infimum-sorry-progress.md（最近一轮进展与逐条卡点）
- formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean（`SmoothDomain`、
  `hausdorffNormalized`、`surfaceMeasure`、`relativePerimeter`，以及 5 条 sorry）
- formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean（9 条 sorry，含 Sard 与 coarea）
- research/verification.md（tasks.json 字段语义与 infrastructure 三种 status）
- research/naming.md

要写的陈述，五组（组名即建议的 section）：

A. 等周直径不等式
   A1. 一般有限维实内积空间 `V` 上：`volume S ≤ ENNReal.ofReal (unitBallVolume n * (diam S / 2) ^ n)`，
       `n = finrank ℝ V`，`S` 任意（外测度形式，不要求可测）。注意 `diam` 为 `Metric.diam`，
       无界集给 `0`，需在陈述里处理（限制 `Bornology.IsBounded S` 或用 `EMetric.diam`，二选一并说明）。
   A2. 由 A1 推出 `μH[(n : ℝ)] = ENNReal.ofReal (2 ^ n / unitBallVolume n) • volume`，
       或等价地本仓库已有的 `hausdorffNormalized_finrank_eq_volume`。**不要**改动
       `RelativePerimeter.lean` 中该定理的类型；在新模块里写 A2 的一般形式，并在文档里
       注明二者的关系。
   A3.（可选，若你判断路线 2 更可取）n 维 Prékopa–Leindler 与 n 维 Brunn–Minkowski 的陈述，
       并在文档里写明一维基例已是 `FunctionalInequalities.Probability.Line.prekopaLeindler`。

B. C^∞ 超曲面的面积测度局部有限
   `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` 现有类型见 RelativePerimeter.lean:418。
   本轮要写的是**它所依赖的一般命题**：局部为 C^∞ 图像（或 C^∞ 定义函数的正则零水平集）的子集，
   其 `μH[n−1]` 在紧集上有限。用 Lipschitz 图像的 `μH` 上界（`LipschitzWith.hausdorffMeasure_image_le`）
   把它归约到 `ℝ^{n−1}` 的有界集。

C. Gauss–Green / 散度定理（超出长方体）
   `SmoothDomain.enorm_gradient_mollified_le` 现有类型见 RelativePerimeter.lean:580。
   本轮要写的一般命题：对光滑域 `U` 与 C^∞ 紧支撑向量场 `F`，
   `∫ div F over U = ∫ ⟪F, ν⟫ over ∂U`（`ν` 外法向，面积测度为标准 `ℋ^{n−1}`），
   以及由此得到的「光滑域指示函数的分布梯度 = 带外法向的面积测度」形式。
   Mathlib 现有的 `MeasureTheory/Integral/DivergenceTheorem.lean` 只覆盖长方体，需在文档里点明。

D. 加权 coarea 公式
   `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 现有类型见 CheegerInfimum.lean。
   本轮要写的一般命题：对 C¹（或 Lipschitz）的 `u : V → ℝ` 与可测权 `w ≥ 0`，
   `∫ w ‖∇u‖ dvolume = ∫_ℝ (∫_{u = t} w dℋ^{n−1}) dt`。

E. Sard 定理（一般维数）
   `SmoothDomain.ae_exists_superlevel` 现有类型见 CheegerInfimum.lean。
   本轮要写的一般命题：C^∞ 映射的临界值集合是 Lebesgue 零测（本仓库只需 `V → ℝ` 的情形，
   即 a.e. `t` 是正则值）。Mathlib 只有同维数的 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`。

规则：
1. **只写陈述**。每条 `theorem`/`def` 的证明体一律 `sorry`。不要尝试证明任何一条，
   也不要为了让某条「看起来可证」而弱化它。
2. 陈述要独立于 KLS：用一般的 `V`（有限维实内积空间，Borel，第二可数）与一般假设，
   不要出现 `ProbabilityMeasure`、`IsBorellDensity`、`SmoothDomain` 之外的仓库专有对象，
   除非该组本来就是关于 `SmoothDomain` 的（B、C 两组可以用它）。
3. **不改动任何既有文件的既有声明**（包括 `RelativePerimeter.lean` 与 `CheegerInfimum.lean` 里
   那 14 条 `sorry` 的类型）。本轮只新增文件。
4. 新文件放在 `formalization/FunctionalInequalities/KLS/WIP/` 下（建议
   `AnalyticPrerequisites.lean`，或按五组拆成若干文件，由你判断）。
   **不注册**：不加进 `FunctionalInequalities.lean` 聚合导入、lakefile `Solutions` 根、
   `research/a-series/ledger.yaml`、`research/check_blueprint.py` 的 `CERTIFICATES`、
   `research/tasks.json`、Blueprint 的 `\lean{}`/`\leanok`。
5. 决定记录只追加：新建 `research/decisions/2026-09-1X-relative-perimeter-prerequisites-statement.md`，
   写明每条陈述的来源（教科书/文献）、与仓库现有 sorry 的对应关系、以及你对每条可行性的评估
   （Mathlib 已有什么、缺什么）。
6. 不 git commit、不 git push。

编译（在 formalization/ 下）：
  lake build FunctionalInequalities.KLS.WIP.<新模块名>   # 先产生 olean
  lake env lean FunctionalInequalities/KLS/WIP/<新模块>.lean
目标：除 `declaration uses 'sorry'` 外无任何输出；再跑
  lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/<新模块>.lean
确认无警告（`omit ... in` 必须放在 docstring **之前**；`unusedSectionVars` 是逐轮报告的，
需要多轮编译才收敛）。

完成后的报告请列出：五组各写了哪些陈述及其全名；每条与 `RelativePerimeter.lean` /
`CheegerInfimum.lean` 中哪条 `sorry` 对应（或说明不对应）；每条的可行性评估与建议路线；
A 组你选了 Steiner 还是 Brunn–Minkowski 路线及理由；以及若你认为某条**不应当以这种形式陈述**
（比如更适合直接向 Mathlib 提 PR、或本仓库根本不需要），请明说并给理由，不要勉强写进去。
```
