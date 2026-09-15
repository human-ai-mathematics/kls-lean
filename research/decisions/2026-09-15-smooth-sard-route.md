# Sard 中间层路线探查

2026-09-15，路线探查轮。**本轮没有证明任何新定理**，也没有改动任何 Lean 源码。
起始回执 `build/verification/latest.json`（`20260914T161103.875998Z`）为 passed，
重新计算确认工作区逐字节一致。HEAD 仍为 `2965b32`，不提交、不推送。
产出是：一条明确的目标改写、一个精确的归纳陈述、一份引理清单（全部已类型检查）、
以及一处尖锐版本的**真实障碍**的定位。

## 结论先行：目标应当从尖锐 C^n 改为 C^∞

逐条追查 `Analysis.sard` 的消费者：

* `Analysis.sard`（`WIP/AnalyticPrerequisites.lean:59`，直接洞，尖锐 `C^(finrank)`）
  唯一被 `Analysis.ae_forall_fderiv_ne_zero` 使用；
* `ae_forall_fderiv_ne_zero` 唯一被 `SmoothDomain.ae_exists_superlevel`
  （`WIP/CheegerInfimum.lean:161`）使用；
* 而 `ae_exists_superlevel` 的假设是 **`ContDiff ℝ ∞ u`**，它调用时先用
  `hu.of_le ENat.LEInfty.out` 把 ∞ 降到 `finrank`。

也就是说：**整条链上没有任何地方真的需要尖锐的 `C^n` Sard**。
证明 `C^∞` 版本并补一条 `C^∞` 的 `ae_forall_fderiv_ne_zero` 变体，
即可让 `ae_exists_superlevel` 摆脱 `sorryAx`，而不必碰尖锐版本。

这不是把义务偷换成更弱的：`Analysis.sard` 的语句与直接洞身份保持不变，
洞数仍为 11，只是链条的实际阻塞点被绕开。若将来要补尖锐版本，它仍在原处。

## 尖锐 C^n 版本的障碍，精确定位

设 `A_j := {x | 1..j 阶导数全为零}`，临界集 `= A_1 ⊇ A_2 ⊇ … ⊇ A_n`。
维数 `d`，处理层 `A_j \ A_{j+1}`，有两条路：

**（甲）初等塌陷**（本仓库平面情形用的那条）。该层局部含于某坐标上的 Lipschitz 图，
投影到 `d-1` 维；层上有固定常数的 `|u y − u x| ≤ C‖y−x‖^{j+1}`（需 `C^{j+1}`）。
`d-1` 维、固定常数、指数 `m` 的覆盖引理要求 `m > d-1`，即 **`j ≥ d-1`**。

**（乙）降维归纳**。取 `j` 阶导数 `w`（`w(x₀)=0`、`Dw(x₀)≠0`），`{w=0}` 是超曲面，
`u` 限制上去后在 `d-1` 维做 Sard。但 `w` 只有 `C^{n-j}`，图与限制函数也只有 `C^{n-j}`，
而 `d-1 = n-1` 维实值 Sard 需要 `C^{n-1}`，故要求 **`j ≤ 1`**。

两条路合起来覆盖 `j ≤ 1` 或 `j ≥ n-1`。于是：

| `n` | 需要的层 | 覆盖情况 |
|---|---|---|
| 2 | j=1 | `j ≥ n-1 = 1`，甲可；**已证**（`Analysis.sard_plane`） |
| 3 | j=1, j=2 | j=1 走乙（限制函数 `C^2`，恰好用已证的平面 `C^2` Sard）；j=2 走甲 |
| 4 | j=1,2,3 | j=1 乙、j=3 甲；**j=2 两条都不行** |

所以尖锐版本的第一处真实障碍是 **n=4, j=2**：限制到超曲面后得到 3 维上的 `C^2` 函数，
而 3 维实值 Sard 需要 `C^3`；再降一维也不行，正则性已经耗尽。
这正是 Whitney–Morse–Sard finite-smoothness 版本的难点，**本轮没有解决，也不建议现在碰**。
顺带得到一个可选的中间成果：**尖锐 3 维 Sard 现在是可达的**（按上表 n=3 一行），
如果将来需要一个纯尖锐的里程碑，那是最便宜的一个。

`C^∞` 时（乙）的正则性永不耗尽，归纳直接闭合——这就是改目标的全部理由。

## 精确的归纳陈述

全部陈述已在 `build/audit/SmoothSardRouteStatements.lean` 严格类型检查通过
（只有 `#check`，无声明、无证明、无占位公理）。

归纳要在**开集上**进行，因为归纳步能提供的正是"某开集上的 `C^∞`"：

```lean
∀ (n : ℕ) {O : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ},
    IsOpen O → ContDiffOn ℝ ∞ u O →
    (volume : Measure ℝ) (u '' {x ∈ O | fderiv ℝ u x = 0}) = 0
```

`O = univ` 即得坐标形的目标；再经线性同构传递即得一般有限维形式。
`O` 开使得 `fderivWithin = fderiv`（`fderivWithin_of_isOpen`），
`ContDiffOn` 在开集上逐点给 `ContDiffAt`（`ContDiffOn.contDiffAt` + `IsOpen.mem_nhds`），
所以陈述里可以一律用全局的 `fderiv` / `iteratedFDeriv`，不引入 `within` 版本。

归纳步（`n+1` 维，`x₀` 属于第 `j` 层，`1 ≤ j < n+1`）：

1. 由 `iteratedFDeriv (j+1) u x₀ ≠ 0` 取方向组 `m`，令 `w x := iteratedFDeriv j u x m`。
   则 `w` 是 `C^∞`，在整个 `A_j` 上为零，且 `fderiv w x₀ ≠ 0`。（L4）
2. 隐函数定理给出 `x₀` 的邻域 `U`、`ℝⁿ` 中开集 `O'` 与在 `O'` 上 `C^∞` 的 `γ`，
   使 `{x ∈ U | w x = 0} ⊆ γ '' O'`。（L5）
3. `h := u ∘ γ` 在 `O'` 上 `C^∞`；`A_j ∩ U` 的点都是 `h` 的临界点
   （因为它们本来就是 `u` 的临界点，`Dh = Du ∘ Dγ = 0`）。
4. 对 `h` 用 `n` 维归纳假设，得该邻域内该层的像零测。
5. Lindelöf（`TopologicalSpace.isOpen_iUnion_countable`）把逐点邻域取可数子覆盖，
   `measure_biUnion_null_iff` 合成——与前两轮完全相同的拼接套路。

顶层 `A_{n+1}` 由已证的覆盖引理处理（见 L3）。基例 `n = 0`：定义域是 subsingleton，像至多一点。

## 所需引理清单

| 编号 | 内容 | 现状 | 估计 |
|---|---|---|---|
| L1 | 上面的开集归纳陈述 | 待证（装配） | ~80 行 |
| L2 | 临界集按层分解 `A_n ∪ ⋃_{j∈Ico 1 n} (A_j \ A_{j+1})` | 待证，纯集合与逻辑 | ~20 行 |
| L3 | **开集版**顶层零测 | 需把已证的 `Analysis.volume_image_flat_pow_eq_zero` 从全局 `ContDiff` 放宽到开集上的 `ContDiffOn` | ~60 行 |
| L4 | 由 `(j+1)` 阶导数非零造出标量 `w` | 待证；`j=1` 的情形已在 `PlanarSard.lean` 内做过 | ~40 行 |
| L5 | 正则零集的局部 `C^∞` 图 | 待证；**Mathlib 已有全部原料** | ~100 行 |
| L6 | 有限维空间与坐标之间的传递 | 待证；`Analysis/Sard.lean` 已有一维先例 | ~30 行 |
| L7 | `C^∞` 版 `ae_forall_fderiv_ne_zero` | 待证；照抄现有 `ae_iff` 证明 | ~10 行 |

搜索结论（Mathlib，本仓库 pin 的版本）：

* **L5 的原料齐全**：`Mathlib/Analysis/Calculus/ImplicitContDiff.lean` 有
  `ContDiffAt.implicitFunction`、`ContDiffAt.contDiffAt_implicitFunction`
  （隐函数保持光滑类）与 `ContDiffAt.eventually_apply_eq_iff_implicitFunction`
  （`f v = f u ↔ ψ v.1 = v.2` 的**图刻画**，不只是包含）。
  还需要在导数非零的那个坐标处做拆分 `(Fin (n+1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ)`
  （`Equiv.funSplitAt` / `Fin.insertNthEquiv` 一族），并把 `fderiv w x₀ ≠ 0`
  翻译成 `(fderiv ℝ f u ∘L .inr).IsInvertible`。这是本路线**唯一的新基础设施**，也是主要风险点。
* **本仓库的 `Analysis/ImplicitGraph.lean` 仍然用不上**：它要求 `C^∞` **且**内积空间的
  `IsGraphSplitting`，面向的是余面积公式的图表示，接口与这里需要的不同；
  上一轮已经确认过它对 `C¹` 的 `Du` 不适用，这里改用 Mathlib 的通用版本，不重复造框架。
* **没有**现成的"邻域上光滑 ⇒ 存在全局光滑延拓"引理。这正是把归纳写成开集形式
  （而不是用 bump 函数把每个局部函数延拓成全局函数）的理由：前者只需要 L3 一处放宽，
  后者要额外造延拓引理。**建议采用开集形式**。

## 本轮的验证与边界

* `build/audit/SmoothSardRouteStatements.lean` 以 `-DwarningAsError=true` 通过，
  9 条 `#check` 全部是合法命题；文件内**没有**任何声明、证明或占位公理。
* 没有改动任何 `formalization/` 下的 Lean 源码，没有新增模块。
  既有结果与洞数完全不变：直接洞 **11**（3/3/5），证书 **24**，
  perimeter infrastructure **missing**，`Analysis.sard` 与两个消费者仍继承 `sorryAx`。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 重新通过；最终快照回执为
  `build/verification/latest.json`。证据哈希记录于
  `research/explorations/2026-09-15-smooth-sard-route.json`。

**明确不主张**：本轮没有证明 `C^∞` Sard，没有证明任何中间层，没有解除任何 `sorryAx`，
也没有缩小 `Analysis.sard` 的语句。上表中的行数是估计，不是承诺。
加权 coarea、其水平集可测性与反方向 Cheeger 比较完全未触及。
