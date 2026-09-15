# 超水平集打包迁出 WIP 并去掉 sorryAx

2026-09-15，承接同日的[C^∞ Sard](2026-09-15-smooth-sard.md)。起始回执
`build/verification/latest.json`（`20260914T171940.461693Z`）为 passed，重新计算确认
工作区逐字节一致。HEAD 仍为 `2965b32`，不提交、不推送。

## 完成范围

新增无洞模块 `formalization/FunctionalInequalities/KLS/Geometry/RegularSuperlevel.lean`，
由 `KLS/WIP/CheegerInfimum.lean` **原样迁入**两条声明：

* `SmoothDomain.frontier_superlevel_subset`（本来就无洞，证明一字未改）；
* `SmoothDomain.ae_exists_superlevel`（**语句一字未改**，证明改接到已证明的
  `Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`）。

两条的 `pp.all` 签名迁移前后**逐字节相同**（`diff` 核对，见
`build/audit/` 中的迁移日志）。迁移后：

```
'FunctionalInequalities.KLS.SmoothDomain.ae_exists_superlevel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

即 **`ae_exists_superlevel` 不再继承 `sorryAx`**。这是 KLS 链条上第一条因 Sard 而带
`sorryAx` 的结论被真正解除。

## 放置与依赖

`Geometry/SmoothDomain.lean` 的文档明确写着"与周长恢复、coarea、Sard 无关的基础层"，
所以**没有**把打包塞回该模块，而是新开一层 `Geometry/RegularSuperlevel.lean`，
导入 `Geometry/SmoothDomain` 与 `Analysis/SmoothSard`。

`WIP/CheegerInfimum.lean` 相应地：删掉迁走的两条声明与空掉的 `namespace SmoothDomain` 块，
把 `import FunctionalInequalities.KLS.WIP.AnalyticPrerequisites` 换成
`import FunctionalInequalities.KLS.Geometry.RegularSuperlevel`。
删除该导入后模块照常编译——说明它对 `AnalyticPrerequisites` 的**唯一**实际依赖就是那条
Sard 后果。于是现在**没有任何模块导入 `KLS/WIP/AnalyticPrerequisites.lean`**，
尖锐 Sard 与 coarea 的洞被隔离在一个无人导入的文件里。

文档同步：`WIP/CheegerInfimum.lean` 的模块注释把"四个 `sorry`"改正为三个
（该数字在上一轮之前就已过时），并重写了描述 Sard 路线的整段；
`build/audit/SuperlevelSardScope.lean` 改为记录新的边界。

## 验证与公理边界

* `Geometry/RegularSuperlevel.lean` 以 `-DwarningAsError=true` 严格通过。
* `build/audit/SuperlevelSardScope.lean` 严格通过，6 条公理报告并排给出边界：
  `client_ae_superlevel`、`ae_exists_superlevel`、`frontier_superlevel_subset`、
  `Analysis.sard_smooth` 均只含标准三公理；
  `Analysis.ae_forall_fderiv_ne_zero` 与 `Analysis.sard` **仍含 `sorryAx`**。
* `SmoothSardAudit` 更新后 12 条报告全为标准三公理，无 `sorryAx`。
* `SmoothSardIngredientsAudit`、`SuperlevelDomainAudit`、`QuadraticRemainderAudit`、
  `QuadraticCoverAudit`、`PlanarSardAudit`、`HigherSardAudit`、`SardLowDimAudit`、
  `AreaFormulaAudit`、`CheegerInfimumAudit`、`MinkowskiConstantAudit`
  全部重新严格通过，**未作改动**。
* 三个 WIP 文件逐个实际编译：直接洞仍为 **3/3/5**，总数仍为 **11**。
  迁移的是一条**填体**而非直接洞，所以洞数不变——这一点必须说清楚，
  本轮减少的是 `sorryAx` 传递，不是洞数。
* 证书仍为 **24**，perimeter infrastructure 仍为 **missing**（其 gaps 由
  coarea 与反方向比较决定，本轮未触及）。
* 默认 `lake build` 通过（3393 jobs）。根目录 `python3 research/verify.py` 的最终快照回执为
  `build/verification/latest.json`。证据哈希记录于
  `research/explorations/2026-09-15-superlevel-rewire.json`。

## 明确未完成

* **尖锐 `C^(finrank)` Sard**：`Analysis.sard` 与 `Analysis.ae_forall_fderiv_ne_zero`
  仍是 `WIP/AnalyticPrerequisites.lean` 里的直接洞与带 `sorryAx` 填体，
  语句未改；`n = 4, j = 2` 障碍未触及。现在它们**没有任何下游消费者**。
* **加权 coarea** `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  与其水平集可测性，以及 `Isoperimetry` 的 `C¹` 特化：三个未触动的洞。
* **反方向 Cheeger 比较** `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le` 与常数相等：仍未证明，
  仍传递依赖 `sorryAx`；只有 `h_M ≤ h_S` 一个方向是证明过的。

整条链**没有**闭合。下一个阻塞是加权 coarea。
