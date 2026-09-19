# 半群生成路线：`S5` 证出（有界非负算子的指数是压缩）

2026-09-19，紧接[`S1`–`S4` 轮](2026-09-19-semigroup-form-proofs.md)与
[交接清单](2026-09-19-semigroup-handoff.md)第二节。`S5` **证出**；`S6`–`S8` 未动。
直接洞仍 **0**，证书仍 **26**。不提交、不推送，聚合根与 `tasks.json` 均未改（见「记账」）。

起点 `HEAD = origin/main = 7986adf`（工作区含前几轮未提交的半群模块）。

## 结果

新模块 `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida.lean`，
命名空间 `FunctionalInequalities.Analysis.Semigroup`（一般实 Hilbert 空间内容，无测度、无对数凹、无 KLS 量）：

| 义务 | 声明 | 说明 |
| --- | --- | --- |
| 引理 | `hasDerivAt_exp_smul_apply` | 轨道 `t ↦ exp (t • A) f` 的导数是 `A (exp (t • A) f)` |
| 引理 | `antitone_normSq_exp_smul_neg` | `L` 非负 ⟹ `t ↦ ‖exp (t • (-L)) f‖²` 在**整个 ℝ** 上单调不增 |
| `S5` 加强版 | `norm_exp_neg_smul_apply_le` | 只假设非负性，`t ≥ 0` ⟹ `‖exp (-t • L) f‖ ≤ ‖f‖` |
| `S5` 原文 | `route_S5` | 路线语句逐字包装，接收自伴假设后丢弃 |

## 证法：与交接清单推荐一致

按交接清单的导数单调性走：令 `u t = exp (t • (-L)) f`，`φ t = ‖u t‖² = ⟪u t, u t⟫`。

* `hasDerivAt_exp_smul_const'`（**带撇的版本**，算子在左）给 `u' t = -L (u t)`，
  再用 `HasDerivAt.clm_apply` 作用到常向量 `f`。选带撇版本的好处是导数**字面上**就是 `-L (u t)`，
  不需要任何 `L` 与 `exp` 交换的引理（`Commute.exp_right` 之类）。
* `HasDerivAt.inner ℝ` 给 `φ' t = ⟪u t, -L (u t)⟫ + ⟪-L (u t), u t⟫ = -2⟪L (u t), u t⟫ ≤ 0`。
* `antitone_of_deriv_nonpos` 给 `Antitone φ`，在 `0 ≤ t` 处取值：`φ t ≤ φ 0 = ‖f‖²`
  （`NormedSpace.exp_zero`、`one_apply_eq_self`），`sq_le_sq₀` 开方。

**没走**谱半径、连续泛函演算、算子范数 `‖exp (-t • L)‖ ≤ 1`——三条交接清单标记的死路一条也没碰。
结论保持逐点形式，绕开 CLM 范数实例菱形。

### 两处小摩擦

* `convert h using 1` 在导数处留下一个 `AddCommGroup ℝ` 的实例相等目标
  （`Real.instAddCommGroup = Real.instRCLike.toDivisionRing.toAddCommGroup`），
  因为 `HasDerivAt.inner` 经 `RCLike ℝ` 取到的实例与直接的不同。改用 `HasDerivAt.congr_deriv`
  只比较导数值，问题消失。
* 该版 Mathlib 已弃用 `ContinuousLinearMap.neg_apply` 与 `ContinuousLinearMap.one_apply`，
  `-DwarningAsError` 下弃用即报错；改用根命名空间的 `neg_apply` 与 `one_apply_eq_self`。

## 路线假设未被使用：自伴性

路线假设 `∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫`。证明**一次都没用到**：`φ'` 的两项
`⟪u, -L u⟫` 与 `⟪-L u, u⟫` 都等于 `-⟪L u, u⟫`，靠的只是**实内积的对称性**（`real_inner_comm`）。
于是模块证的是严格更强的 `norm_exp_neg_smul_apply_le`（任意有界非负 `L`），
`route_S5` 与审计里的 `route_S5` 均按原样接收该假设后丢弃——**记录下来，不静默吸收**，
与 `S2` 丢 `0 < s`、`S3` 丢 `Dense` 同一处理方式。

`0 ≤ t` **是**必需的：`φ` 在整个 ℝ 上递减意味着 `t < 0` 时 `‖exp (-t • L) f‖ ≥ ‖f‖`，方向相反。

## 明确没做什么

`S6`（Yosida 指数的强收敛）、`S7`（半群律与强连续）、`S8`（生成元）未证，`S6` 风险仍标高。
本条只是半群构造中的一步；**不是** Markov 性、**不是** Bakry–Émery Γ 演算、**不是** Buser 不等式的任何一步。
`thm:logconcave-cheeger-poincare-comparison` 无 `\leanok`，`tasks.json` 的缺口条目未改动
（缺口一仍整体未填）。没有新增证书，Blueprint 未改。

## 记账（留给主会话集成）

本轮**没有**改 `formalization/FunctionalInequalities.lean`、`lakefile.toml`、`research/tasks.json`
或任何 Blueprint `.tex`，也未 `git add/commit/push`。为了让审计客户端能 import，
用 `lake build FunctionalInequalities.Analysis.Semigroup.Yosida` 单独生成了 olean，不改任何文件。

集成时需要：

1. 聚合根 `FunctionalInequalities.lean` 加 `import FunctionalInequalities.Analysis.Semigroup.Yosida`
   （否则 `lake build` 与 CI 不构建它，仓库不应再多一个游离模块）。
2. `tasks.json` 的证据条目登记 `Analysis/Semigroup/Yosida.lean` 与
   `research/audits/SemigroupYosidaAudit.lean` 的 sha256，然后跑 `verify.py`。
3. 交接清单第二节的 `S5` 条目可标「已证」，并把「自伴假设未用」记入。

## 验证

模块与审计均以 `lake env lean -DwarningAsError=true` 通过，**0 错误 0 警告**。
审计客户端 `research/audits/SemigroupYosidaAudit.lean` 把 `S5` 逐字重述为 `route_S5` 并消解，
另给不带自伴假设的 `route_S5_of_nonneg`，以及两个边界情形（`t = 0` 时是等式、`L = 0`）。
路线文件与审计里的 `S5` 文本经 `diff` 逐 token 比对一致。
**8 条 `#print axioms` 报告，全部只有 `propext, Classical.choice, Quot.sound`，0 条 `sorryAx`。**
