# 2026-09-12 — 同步上游研究与文献

本轮是研究同步，不新增 Lean 定理、`sorry`、证书或已证明节点，不修改已有证明。
截至本轮开始，工作区干净；已有四条边界接口证明属于此前工作。

## 来源与版本

- 上游仓库现名为 [kls-conjecture-search](https://github.com/numina-functional-inequalities/kls-conjecture-search)。
- 旧研究固定版本：`8185e46ffb040e04fea076953e5bcaeb4157d71a`（2026-09-01）。
- 新研究固定版本：`34b5fcd57fef17089e781616005fe6d3641bd11e`（2026-09-10），本轮只读查询确认是当前 `main`。
- [六个提交的比较](https://github.com/numina-functional-inequalities/kls-conjecture-search/compare/8185e46ffb040e04fea076953e5bcaeb4157d71a...34b5fcd57fef17089e781616005fe6d3641bd11e)。包含模板迁移、两轮研究入库、手稿和网站改进；记录日期不等于合并日期。
- 账本迁移至 `research/program/ledger.yaml`，搜索路线迁移至 `research/program/portfolio.yaml`。
- 本地 route source 的稳定 ID `kls-exploration` 保留，仓库 URL、revision、ledger 和路线 provenance 路径更新。历史决定和证书的旧版本来源不改写。

读取了固定版本的数学模块、账本、portfolio、参考文献和两轮研究总结。
[选定原始账本记录](../upstream/2026-09-12-kls-research.json)保留 20 条未经改写的 YAML 记录与源账本 SHA-256；
这是可复查的来源摘录，不是第二份 Lean 账本，也不直接参与任务调度。
本轮没有对上游每份证明档重新执行独立数学审查。

## 认证语义

上游当前 138 个节点中有 86 个 `proved`、46 个 `open`、4 个 `defined`、2 个 `refuted`。
这些数量不可与本地 24 个 Lean 证书直接比较：上游包含文献、自然语言证明及带假设的蕴含。

- `proofs.mode: agent` 表示上游自然语言审查记录，不表示 Lean 核验。
- 上游 `proved` 加非空 `assumes` 表示证明了一个条件性命题。
  本地 `prop:spectral-sufficiency` 和 `cor:cmh-recovery-sequence-suffices` 继续为 `conditional`；
  其显式开放前提仍由现有 Blueprint/route 依赖表达，没有升级成无条件结果。
- 文献预印本的陈述、上游审查、数值实验、Lean 证书是不同证据。
- 四条足以推出 KLS 的路线仍是逻辑 OR；新增精确模型或短时间结果不成为关闭 KLS 的新分支。

## 文献更新

两篇均固定到 v1，并加入 Blueprint 文献表和路线章。

| 来源 | 原文陈述 | 本地边界 |
| --- | --- | --- |
| [Chen–Klartag, 2607.23307v1](https://arxiv.org/abs/2607.23307v1) | 各向同性对数凹律的 sharp thin-shell：`Var(|X|²) ≤ 8n`；另有三阶矩张量界 | 未 Lean 形式化；thin-shell 本身不解决 KLS |
| [Letwin, 2607.24164v1](https://arxiv.org/abs/2607.24164v1) | 对称二次型的 Poincaré 系数 2；`ψ_n ≤ C (log n)^(1/4)`，`n ≥ 2` | 未 Lean 形式化；按 `1/4 ≤ ψ²/C_P ≤ π`，推出 `C_P ≤ C' sqrt(log n)`，不是维数无关界 |

不把 Letwin 的 `ψ` 指数直接写成 `C_P` 指数；也不把上游条件于 Letwin 的较弱路线终点叫作新的文献最强界。

## 新增研究与剩余缺口

[Wave four 总结](https://github.com/numina-functional-inequalities/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/research/explorations/2026-08-31-orchestrator-kls-angles-wave-w4.md)
与 [wave five 数学总结](https://github.com/numina-functional-inequalities/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/research/explorations/2026-09-06-orchestrator-kls-cone-lift-wave-w5.md)
提供证明档与审查路径；最新账本优先于较早波次的暂定状态。

| 路线 | 新接入的上游记录 | 已获得的范围 | 尚未获得 |
| --- | --- | --- | --- |
| 谱局部化 | `lem:mm-restart-deweighting`、`lem:mm-smallgap-fourth-moment` | restart 去权、带既有维数界输入的小谱隙四阶矩控制 | 本地随机过程、停止时刻、特征函数和生成元基础 |
| 谱局部化 | `lem:mm-stopped-window-source`、`prop:mm-window-occupation` | **条件于 `thm:letwin-qcts`** 的短时间链与 `C_P ≤ C log² n` | 统一正时间的 occupation；KLS 仍开放 |
| Screened localization | `prop:split-screened-supply` | regular split class 上的 screened supply 估计 | 任意测度/切集的 universal gate |
| CMH | `lem:cmh-linear-spectral-resolution` | 弱 column equation 与闭形式意义的谱分解 | 一般强算子域结论；不能省掉 `Tr Q ∈ L²` 问题 |
| CMH | `lem:linear-sector-third-moment`、`cor:gate-zero-third-moment` | Stein 列能量分解为常数、方向三阶矩和正交高阶余项 | 普遍控制高阶余项的矩阵界 |
| CMH | `conj:gate-zero-sharp` | 明确提出 `E[H Σ⁻¹ H] ≼ 2Σ` | 仍为 conjecture；即使精确模型满足也不能升级 |
| 指数锥 | `def:exponential-cone`、`prop:cone-moment-map`、`prop:cone-linear-sector`、`cor:cube-cone-gate-zero` | 显式 moment map/Stein 核，轴向值 `1+n/β ≤ 2`，cube cone 的矩阵界 | 一般 gate zero、全 CMH 不等式、统一 recovery envelope |
| 条件纤维 | `lem:fiber-root-degree-two` | `m ≥ 3` 时 root-frame 的二次商空间最小值 `(m+2)(m+3)/(5m²) > 1/5` | 全 `L²` 谱隙、三次证书、普遍 frame 构造 |

上游的 264 个精确锥样本是数值/有限模型证据，不作为普遍不等式的证明。
指数锥的 sharp 线性部分也不是整个 CMH 常数。
二次多项式结果只排除该双对偶框架中的二次 refuter；不能推广为完整 frame 定理。

## 后续形式化队列

这是范围建议，不表示基础设施已就绪。本轮只给现有任务添加研究更新说明，保持原数学分类、
假设与 infrastructure 状态；新对象进入正式 Blueprint 数学节点前，先做陈述与依赖审计。

1. **继续当前周长链。** 四条外法向/边界积分接口已有证明；优先接通 Gauss–Green 和现有光滑逼近，
   再处理 coarea、Sard、恢复序列及 Cheeger 下确界比较。这些是已有形式化任务。
2. **单独评估 `lem:fiber-root-degree-two`。** 原始声明在上游 `modules/kls/45-conditional-fiber-frame.tex`；
   审查 isotropic simplex、root frame、二次多项式商空间、条件重采样归一化和有限维谱计算。
   现有纤维闭形式可复用，但上述模型不能视作已存在。
3. **CMH 先做最小定义依赖表。** moment map、canonical Stein 核、闭生成元、弱 column equation
   必须分开；不得用一个强域假设悄悄替换上游只证明的弱形式。锥模型作为独立校准任务。
4. **随机局部化作为较大独立工作包。** 先定义过程与停止时刻，再考虑 wave-four window 链；
   Letwin 输入在 Lean 中必须证明或保持显式假设，不能通过来源引用充当公理。

当前不自动创建任务、发送 Slack 消息、提交或推送。新的研究路线也不替换正在进行的周长证明。

## 本轮验证范围

执行 Blueprint/Atlas 结构检查、Python 回归检查、本地完整验证，以及更新后 Blueprint 的构建检查。
完整验证的机器回执位于 `build/verification/latest.json`；它绑定实际源码快照，本文不预先宣称通过。
生成的 Atlas 仍只调度已有本地数学节点；新增上游摘录不产生 `leanok` 或 Lean 证书。
