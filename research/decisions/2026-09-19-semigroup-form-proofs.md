# 半群生成路线：`S1`–`S4` 证出（部分实现轮）

2026-09-19，当日第十六轮，紧接[路线轮](2026-09-19-semigroup-generation-route.md)。
`S1`、`S2`、`S3`、`S4` **全部证出**；`S5`–`S8` 未动。直接洞仍 **0**，证书仍 **26**。不提交、不推送。

起点 `HEAD = origin/main = 7986adf`。

## 结果

新模块 `formalization/FunctionalInequalities/Analysis/Semigroup/Form.lean`（一般实 Hilbert 空间内容，
无测度、无对数凹、无 KLS 量）：

| 义务 | 声明 | 说明 |
| --- | --- | --- |
| `S1` | `Analysis.Semigroup.completeSpace_graph` | `T` 闭 ⟹ `T.graph` 完备 |
| `S2` | `Analysis.Semigroup.min_one_mul_graphNormSq_le` | 图范数下的强制性，常数 `min 1 s` |
| `S4` | `Analysis.Semigroup.norm_le_of_weakResolvent`、`inner_nonneg_of_weakResolvent` | 弱预解方程的解是压缩、与数据配对非负 |

外加 `WeakResolvent`（弱预解方程的谓词，不构造预解算子）与
`graphNormSq_eq_inner_of_weakResolvent`（取 `v = u` 的检验恒等式）。

## 两处与路线不同

* **`S1` 几乎是白给的。** 路线估 40 行、风险低，实际是一行：`LinearPMap.IsClosed` **按定义**就是
  图作为集合的闭性，Mathlib 的 `IsClosed.completeSpace_coe` 直接给出完备性。
* **`S2` 不需要 `s > 0`，路线写多了假设。** 模块里的版本对**任意实数 `s`** 成立：
  `s ≤ 1` 时归结为 `(s − 1)‖u‖² ≤ 0`，`s > 1` 时归结为 `‖Tu‖² ≤ s‖Tu‖²`。
  审计仍按路线原样（带 `0 < s`）重述并消解，把该假设接收后丢弃——**记录下来，不静默吸收**。
  这是严格更强的引理，不是对路线的削弱。

## 明确没做什么

`S3`（预解的存在唯一，Lax–Milgram 的实际装配）未证——这是本路线的主要工作量所在。
`S5`–`S8`（Yosida 近似、强收敛、半群律、生成元）未证，其中 `S6` 风险仍标高。
**即使 `S1`–`S8` 全部证出，Buser 半仍证不出来**：半群只是四个前置里的第一个，
缺口二（Markov 性）、三（Bakry–Émery Γ）、四（小时间热估计）原封未动。
`thm:logconcave-cheeger-poincare-comparison` 无 `\leanok`，`tasks.json` 的缺口条目**未改动**
（缺口一仍整体未填）。没有新增证书，Blueprint 未改。

## 记账

聚合根 `FunctionalInequalities.lean` 加入新模块的 import——否则 `lake build` 与 CI 不会构建它
（仓库已有 8 个不在任何 library root 导入闭包里的模块，不再增加第 9 个）。

## 验证

`lake build` 通过（3518 jobs）。模块与审计均以 `lake env lean -DwarningAsError=true` 通过，
**0 错误 0 警告**。审计客户端 `research/audits/SemigroupFormAudit.lean` 把 `S1`、`S2`、`S4`
逐字重述并消解，另两个边界情形（零算子、零数据）。
**10 条 `#print axioms` 报告，全部只有 `propext, Classical.choice, Quot.sound`，0 条 `sorryAx`**；
日志 `build/audit/semigroup-form-proofs/scope-audit.log`。


## 追加：`S3` 证出（同日，紧接上文）

新模块 `Analysis/Semigroup/Resolvent.lean`，`existsUnique_weakResolvent` 即 `S3`：

| 结果 | 声明 | 状态 |
| --- | --- | --- |
| `S3` 唯一性 | `weakResolvent_unique` | 已证，不需要闭性、稠性或 Lax–Milgram——两解之差自检即得 |
| `S3` 存在性 | `exists_weakResolvent` | 已证，**用正交投影，不用 Lax–Milgram** |
| `S3` | `existsUnique_weakResolvent` | 已证 |

**换了证法，比路线预设的省。** 路线设想的是装配 Lax–Milgram：把 `B_s` 打包成
`G →L[ℝ] G →L[ℝ] ℝ`、证 `IsCoercive`、再用 Riesz。实际用的是**正交投影**：
把第二坐标按 `√s` 重标度，`G_s = {(u, √s·Tu)}`，则

```
⟪g, h⟫ = ⟪u,v⟫ + s⟪Tu,Tv⟫,    ⟪f,v⟫ = ⟪(f,0), h⟫
```

即环境内积**就是**那个形式，于是解恰为 `(f,0)` 在 `G_s` 上的正交投影
（`Submodule.starProjection`，闭性由 `T` 闭经连续原像得到）。
**不需要** `IsCoercive`、`bilinearComp`、`innerSL` 的 `→L⋆` 对接，也不需要 Riesz——
路线里点名的那个摩擦点整个绕开了。`S2` 因此在 `S3` 的证明里**没有被用到**
（它仍是 Lax–Milgram 路线的正确前置，只是这条证法不走那里）。

**`S3` 的 `Dense (T.domain)` 假设是多余的**，与 `S2` 的 `0 < s` 同类：唯一性连闭性都不要，
存在性只要闭性。稠性只在要把解写成 `(1 + sT*T)⁻¹f`、即需要伴随算子时才用得上，本模块不做那步。
审计仍按路线原样重述 `route_S3`（带 `Dense`）并消解，把该假设接收后丢弃。
