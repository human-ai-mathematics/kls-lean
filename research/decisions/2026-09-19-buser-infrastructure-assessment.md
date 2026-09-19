# Cheeger–Buser 比较节点的基础设施评估

2026-09-19，当日第十四轮。**没有证明任何定理，没有改动任何 `.lean`。**
本轮把 `thm:logconcave-cheeger-poincare-comparison` 的 `infrastructure` 由 `unchecked` 评估为
`missing`，写下 **5 条具体缺口**与 **6 份证据**（带 sha256），针对 pinned Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`。直接洞仍 **0**，证书仍 **26**。

起点 `HEAD = origin/main = 7986adfb07e35e900e80570f495ede4cafd0a672`（当日已推送，两条 CI 皆 success）。

## 为什么做这一轮

Klartag 子句封口后，该节点是 `atlas.py ready` 里唯一的 `inspect_infrastructure`，也是 Cheeger–Buser
线仅剩的闸门。按既定原则**不在一轮里承诺 `B0`**，诚实的推进方式是把缺口写清楚，
让调度器把它归入 `develop_infrastructure`——与 `thm:cmh-recovery-affine-poincare-bound`（缺 `W₂`）、
`prop:weighted-spectator-obstruction`（缺随机积分）同一记法。

## 仍然欠的究竟是什么

**只有 `n ≥ 2` 的 Buser 半、常数 π。** 该节点的另两块都已是本地 Lean 证明：

* Cheeger 半 `C_P^lit ≤ 4Ψ_KLS²`（`KLS.LogConcave.literatureConstant_le_four_mul_inverseScale_sq`）；
* 仿射支撑维数 `≤ 1` 的 Buser 半，常数 **12**（`KLS.LogConcave.inverseScale_sq_le_of_finrank_le_one`）。

## 五条缺口（`tasks.json` 内为完整英文条目）

1. **由 Cheeger 形式生成对称 Markov 半群。** pinned Mathlib **完全没有**强连续单参数半群：
   没有 `C0Semigroup`/`OneParameterSemigroup` 类型，没有 Hille–Yosida 或 Lumer–Phillips 生成定理；
   也没有无界自伴算子的谱/Borel 泛函演算。`Analysis/InnerProductSpace/Spectrum.lean` **自己的文件头**就写明
   假设算子紧或空间有限维；`ContinuousFunctionalCalculus/` 只覆盖有界 C\*-代数元；算子 `exp` 只对
   有界 Banach 代数元存在。`LinearPMap.lean` 只给了无界稠定算子的伴随与闭性。
   **形式那一侧本仓库已经有了**——`Energy.Cheeger.energy`，以及 `KLS/LogConcave/WeightedGradient.lean`
   里稠定可闭的加权梯度算子（`weightedOperator_isClosable`、`dense_domain_weightedOperator`）——
   缺的是从闭形式过渡到 `P_t = e^{-tL}` 这一步。
2. **Dirichlet 形式与 Markov 半群理论。** 泛函分析意义上的 Dirichlet 形式没有，Markov 性
   （`L¹`/`L^∞` 上的次 Markov 压缩、保正、保质量）没有。Mathlib 里所有 `Dirichlet` 都是 Dirichlet 特征与
   L 函数，所有 `Markov` 都是 `MarkovCategory`、Chebyshev–Markov 不等式与 Riesz–Markov–Kakutani。
   没有 Markov 性，Ledoux 论证里的逐点界无从谈起。
3. **Bakry–Émery Γ 演算。** 没有 carré du champ `Γ`，没有 `Γ₂`，没有 `CD(K, ∞)`，
   特别是没有梯度交换估计 `‖∇P_t f‖ ≤ e^{-Kt} P_t‖∇f‖`。这正是 Ledoux 证明与 De Ponti–Mondino
   常数 π 的分析引擎，本仓库也没有。
4. **小时间热半群估计。** 没有热核、没有加权欧氏空间上的热半群，因而 Ledoux 证明所合成的两条不等式
   （`‖P_t f − f‖₁ ≲ √t · TV(f)` 与 `‖∇P_t f‖_∞ ≲ t^{-1/2}‖f‖_∞`）都不存在。
5. **备选路线 (b)，Lovász–Simonovits 局部化。** 没有针分解/对分，没有 Prékopa–Leindler，
   pinned Mathlib 里也没有 Brunn–Minkowski（本仓库只有自己的一维
   `Probability/Line/BrunnMinkowski.lean`）。把一维结论搬到环境等周常数的转移引理同样缺失，
   所以已证的阶段一 `Ψ_KLS² ≤ 12 C_P^lit`（维数 ≤ 1）**也无法**靠局部化升到 `n ≥ 2`。

## 证据

六份，均带 sha256：两份 Mathlib（`Spectrum.lean`、`LinearPMap.lean`，用来支撑「谱理论范围受限」
与「无界算子只有伴随」这两条断言）、三份本仓库模块（`Energy/Cheeger.lean`、
`KLS/LogConcave/WeightedGradient.lean`、`KLS/LogConcave/Line/Buser.lean`，用来支撑「形式侧已有、
阶段一已证」）、一份 Blueprint 章节。

## 效果与边界

`atlas.py ready` 中该节点由 `inspect_infrastructure` 变为 **`develop_infrastructure`**，缺口逐条可见。
这**不是**进展的倒退，而是把「未评估」换成「已评估且确实缺」。节点仍不带 `\leanok`，
`cor:tight-window-consumption` 仍 `blocked`。**本轮不排期 `B0`。**

两条路线的规模估计（来自[路线记录](2026-09-19-buser-route.md)）未变：都在数千行，且都带 Mathlib 级前置。
若要推进，理性的最小切口是缺口 1——单参数压缩半群的生成——它同时是缺口 2、3、4 的前置，
而且是可以独立于 KLS 向 Mathlib 上游贡献的一般性内容。

## 验证

`check_ledger.py` 26 节点 0 错误；`check_blueprint.py` 88 标签 0 错误；
`atlas.py check` 75 节点 26 证书无环；`research/tests` 104 项通过。
未改任何 `.lean`，故 `lake build` 与 `checkdecls` 与上一轮同。回执于本轮末重跑 `research/verify.py` 绑定。
