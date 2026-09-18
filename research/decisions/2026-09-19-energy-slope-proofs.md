# Energy 五洞归零：奇异律的 `𝓔^can = 2Ch` 证毕、最后一个 WIP 模块删除、第 26 个证书

2026-09-19，**实现 + 注册轮**，接在同日的 [Energy 路线探查](2026-09-19-energy-slope-route.md)之后。两个证明会话并行
（A：夹逼；B/C：磨光恢复 + 稠密性），本会话整合、迁移与注册。结果：

* **五个洞全部证出**：`SmoothGradient.relaxation_eq_localSlope`、`LocalSlope.relaxation_eq_asymptoticLipschitz`、
  `Cheeger.energy_eq_ofAsymptoticLipschitz`、`SmoothGradient.relaxation_eq_two_mul_cheeger`、
  `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger`，在新模块 `Energy/Cheeger/Identification.lean` 中以
  **逐字节相同的 `pp.all` 签名**（978 行打印 `diff` 为空）迁入；`Energy/WIP/Cheeger.lean` 删除，`Energy/WIP/` 目录随之消失。
  **仓库不再有任何 WIP 模块，直接洞 5（0/0/5）→ 0。**
* **第 26 个证书**：`solutions/ThmSmoothGradientRelaxationTwoCheeger.lean` 注册 `thm:smooth-gradient-relaxation-two-cheeger`
  （`certificate μ`：对**任意** Borel 律，内禀律两松弛相等且 `𝓔^can_μ f = 2·Ch_μ f`；`conventions_agree ν`），4 条公理守卫。
  证书 **25 → 26**。

不提交、不推送。起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T141537.829419Z/report.json`：10 个门、237 个模块重放、650 条目，快照 `f91b06cac5cf4d62e270ae9ec48c1d6c2459fa53583be0b4f06a51d7baa3aa4c`。

## 边界

无量纲 KLS 仍开；Cheeger–Buser 的 Buser 半未证；不新增兼容 alias、不重述既有定理、不削弱已证结论。
`cor:absolutely-continuous-relaxation-two-cheeger` 原样保留为特例。

## 三个新模块

| 模块（行） | 内容 |
| --- | --- |
| `Energy/Euclidean/SlopeComparison.lean`（218） | `A1` 光滑测试的渐近 Lipschitz 常数逐点等于梯度范数（`SmoothGradient.Test.asymptoticLipschitz_apply`，一般形式 `AsymptoticLipschitz.apply_eq_norm_gradient`）；`A2` `asymptoticLipschitz_relaxation_le`；`A3` 压塌 `LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient` |
| `Energy/Euclidean/SlopeRecovery.lean`（659） | `B1` `SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith`（定半径磨光 + 局部 Lipschitz 继承 + 反向 Fatou）；`B2` `locallyLipschitz_mul`；`B3` `exists_lipschitzWith_of_eq_zero_outside_ball`；`B4`、`B5` 两种斜率的一动点 Leibniz 界 |
| `Energy/Euclidean/SlopeDensity.lean`（1202） | `C1` `LocalSlope.measurable_apply`；`C2` `LocalSlope.exists_patch`（`exists_partition` + `exists_thickening_pairwise_disjoint` + `exists_patch_of_isCompact`）；`C4` `SmoothGradient.relaxation_le_localSlope_of_lipschitzWith`；`C5` `…_of_admissible`；`C6` `SmoothGradient.relaxation_le_localSlope` |

实现中的三点修正，路线语句本身全部按字面证出：
* `C2` 的库形式多证一条结论——`|F x − f x| ≤ 2L + 2α` 对**所有** `x`；补丁并不逐点收敛，`C4` 的 `L²` 收敛靠「核上为零、核外有界、`ν Kᶜ → 0`」。
  审计里的 `route_C2` 从中投影出路线的逐字合取。块常数取 `min ((k+1)α) (L+α)`，比路线的 `(k+2)α` 紧一个 `α`。
* `B4`（两动点常数）需要路线正文略去的 `O(r)` 修正：第二个动点处 `|g z| ≤ |g x| + Lip_a g(x)·r`，半径取 `min r₁ (η/((a+η)N+1))`；`B5` 不需要。
* 内正则性给出的空紧核必须**剔除**而非保留：`Metric.infDist x ∅ = 0` 会使其截断恒为 1 而破坏构造（与 Cheeger 线 `K7` 同一陷阱）。

## 注册与整合

证书文件、ledger 节点（`kind: lemma`，`meta.scope` 追加）、`check_blueprint.py` 映射、lakefile 根；Blueprint 第 30 章定理加
`\lean{…}`、`\leanok` 与证明块（写明路线与 Eriksson-Bique / AGS 来源），其后的说明段改写；聚合导入加入四个模块并改写 Energy 段散文；
`research/tasks.json` 的 `thm:smooth-gradient-relaxation-two-cheeger` 由 `mathematics unknown` 改为 `local_argument` 并补 infrastructure 块，
全部被钉住的证据哈希刷新；进度视图经临时 index 重生成。证书导入闭包（47 个模块）事先扫描无转义词。

## 明确没证什么

无量纲 KLS；Buser 半；`thm:klartag-density-frontend-identification` 的文献 Poincaré 子句。`D1`（统一半径不够的诊断）未形式化。
不声称任何单个测试上原始斜率能量与松弛能量相等。

## 验证

默认 `lake build`（3512 个作业，含新证书的 `Solutions` 库）通过。全部 **66** 个审计客户端（`research/audits` 59 个 + `build/audit` 7 个活客户端）以 `-DwarningAsError=true` 重跑，**0 失败**；**867 条公理报告，0 条 `sorryAx`**。仓库已无 WIP 模块，直接洞 **0**。`check_ledger.py` **26** 个证书 0 错误；`check_blueprint.py` 88 标签 0 错误；`atlas.py check` 75 节点 26 证书无环；104 项单元测试通过。
五条声明 `pp.all` 前后 `diff` 为空。根目录 `python3 research/verify.py` 于本轮结束时重跑，最终回执记于
`build/audit/energy-slope-proofs/final-snapshot.json`，快照与工作区逐条重算，drift 为空。
详见 `research/explorations/2026-09-19-energy-slope-proofs.json`。
