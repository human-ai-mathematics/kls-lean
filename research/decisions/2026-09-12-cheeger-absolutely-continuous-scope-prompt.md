# 2026-09-12 — 交给下一个会话的提示词：把 Cheeger 识别的绝对连续范围转正并注册

前置说明。`thm:smooth-gradient-relaxation-two-cheeger` 的陈述设计见
[陈述记录](2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md)，填证明见
[证明记录](2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md)，`\notready` 的移除与分类保持 `unknown`
的理由见[元数据记录](2026-09-12-smooth-gradient-relaxation-two-cheeger-metadata.md)。
本提示词**不**要求碰那 5 条开放义务：目标是把 `Energy/WIP/Cheeger.lean` 里**已经无 `sorry`** 的绝对连续/对数凹
范围拆出来转正，立为新的 Blueprint 节点并注册为第二十四个证书。注册轮的完整模板见
[上一轮注册记录](2026-09-12-conditional-fiber-twelve-bound-registration.md)。

---

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交
db584cd6d46c92f209a44c0f1c829460d327499d；Lake 根目录 formalization/）。
本机 elan 与全部 Lean 工具链已是原生 arm64，lake 调 git 正常，**不需要**任何 git 包装脚本或 GIT_EXEC_PATH。

任务：把 formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean 中已经无 sorry 的「绝对连续 / 对数凹」
范围拆分转正，立为一个新的 Blueprint 节点，并按仓库标准流程注册为第二十四个 Lean 证书。
**不要试图证明那 5 条开放义务**（奇异测度下的 AGS 型松弛比较），它们继续留在 WIP。

要转正的数学内容（当前都已证、无 sorry）：
  Energy.SmoothGradient.relaxation_le_localSlope_of_absolutelyContinuous
  Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous
      (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) :
      relaxation ν = LocalSlope.relaxation ν
  Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous
      (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
      [m.IsAddHaarMeasure] (hac : (Probability.intrinsicMeasure μ : Measure _) ≪ m)
      (f : Lp ℝ 2 (μ : Measure E)) : energy μ f = 2 * Cheeger.Intrinsic.energy μ f
  FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger
      (hμ : LogConcave μ) (f : Lp ℝ 2 (μ : Measure E)) :
      Energy.SmoothGradient.Intrinsic.energy μ f = 2 * Energy.Cheeger.Intrinsic.energy μ f
最后一条经已认证的 lem:logconcave-intrinsic-absolute-continuity 覆盖**全部**对数凹律，是 KLS 路线真正要用的那半。

必须留在 WIP 的 5 条 sorry（位置以当前文件为准，行号会随拆分变化）：
  LocalSlope.relaxation_eq_asymptoticLipschitz          -- 真正的开放义务
  SmoothGradient.relaxation_eq_localSlope               -- 真正的开放义务
  Cheeger.energy_eq_ofAsymptoticLipschitz               -- 前者的三行推论
  SmoothGradient.relaxation_eq_two_mul_cheeger          -- 后者的三行推论
  SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger    -- 后者的三行推论（Blueprint 无条件定理本体）

先读：
- research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md
  （约定选择：局部斜率 Cheeger、Lip_a 版本另立为显式义务；文末「未做」一节已经写明转正时要做什么，照它执行）
- research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md（26 条义务逐条状态）
- research/decisions/2026-09-12-smooth-gradient-relaxation-two-cheeger-metadata.md（\notready 已移除的理由）
- research/decisions/2026-09-12-conditional-fiber-twelve-bound-registration.md（**注册轮的完整清单，照抄流程**）
- formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean（584 行，全部内容）
- research/verification.md（tasks.json 字段语义、infrastructure 记录的三种 status）
- research/naming.md（短名规则；转正要加的表行在陈述记录「未做」一节里已列好）

规则：
1. **不改任何已证声明的类型**（定理、def、structure 的签名一律不动），只搬位置与补 docstring。
2. **不碰那 5 条 sorry 的陈述**，也不要尝试证明它们。
3. 转正后的模块必须**完全无 sorry**：拆完要验证「无 sorry 部分对依赖封闭」——注册模块里任何声明都不得
   （传递地）用到那 5 条。不要凭本提示词断言，自己查。
4. **不改无条件节点** thm:smooth-gradient-relaxation-two-cheeger 的陈述，也不给它加 \lean{}/\leanok；
   它保持未认证。新节点是**另一个** label。
5. 决定记录只追加：新建 research/decisions/2026-09-1X-cheeger-absolutely-continuous-registration.md。
   不要回改任何既有决定记录。
6. 不 git commit、不 git push。

建议路线：

## A. 拆分模块
陈述记录已经定了目标布局：从 `Energy/WIP/` 移到 `Energy/Cheeger/` 与 `Energy/LocalSlope/`。建议：
  Energy/LocalSlope/Relaxation.lean   —— AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}、
                                          LocalSlope.{preEnergy,relaxation} 及其无 sorry 引理
  Energy/Cheeger/Basic.lean           —— Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}
                                          及 energy_apply、two_mul_energy、energy_eq_zero_of_subsingleton
  Energy/Cheeger/SmoothGradient.lean  —— SmoothGradient.Test.*、localSlope_relaxation_le、两条 _of_absolutelyContinuous、
                                          Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous、
                                          以及 KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger
  Energy/WIP/Cheeger.lean             —— 改为 import 上面三个，**只**保留那 5 条开放义务，模块 docstring 说明它仍是 WIP
文件切分可以调整（比如把 KLS.LogConcave 那条单独放到 KLS/LogConcave/ 下），但上面四类内容的归属与「WIP 只剩 5 条」
这一条不要变。

## B. 新 Blueprint 节点
在 formalization/blueprint/src/chapters/30-open-canonical-bridges.tex 里、无条件定理块**之后**新增一个 corollary 块。
建议 label `cor:absolutely-continuous-relaxation-two-cheeger`（你可以改，但定下后全程一致：ledger 节点 ID、
tasks.json 键、route sidecar 节点、证书文件名与命名空间都跟着它）。
内容：在内禀律对 Haar 测度绝对连续的前提下 E^can_μ = 2 Ch_μ，并点明对数凹律经
lem:logconcave-intrinsic-absolute-continuity 自动满足该前提。
\uses 至少含 def:selected-canonical-frontend 与 lem:logconcave-intrinsic-absolute-continuity。
加 \lean{...} 与 \leanok（陈述与证明块都要）。同时在无条件定理后面那段说明里补一句：绝对连续范围已单独认证，
剩下的仍是奇异情形。

## C. 证书
solutions/Cor<你选的label的驼峰形>.lean，命名空间 Solutions.Cor<同名>，照
solutions/CorConditionalFiberTwelveBound.lean 的结构：一条 `certificate` 打包 (1) 坐标层的
relaxation_eq_localSlope_of_absolutelyContinuous、(2) 内禀层的 energy_eq_two_mul_cheeger_of_absolutelyContinuous、
(3) 对数凹特例；再加若干 typed application（至少：对数凹律无需显式 hac、一点仿射支撑给 0 = 2*0、
EuclideanSpace 上以 volume 为 Haar 参考）与 #print axioms 守卫（证书 + 两条库定理）。

## D. 注册轮
照 2026-09-12-conditional-fiber-twelve-bound-registration.md 的清单逐项做：
  formalization/lakefile.toml 的 Solutions 根；formalization/FunctionalInequalities.lean 聚合导入（三个新模块）；
  research/a-series/ledger.yaml 新节点（第 24 个）+ meta.scope 追加；research/check_blueprint.py 的 CERTIFICATES；
  formalization/blueprint/route-composition.yaml 新节点 claim（proved + Lean 证据）；
  research/tasks.json（注意：被 ledger 记录的节点**不需要** task 条目，但 atlas 是 fail-closed 的，以 atlas.py check 为准；
  另外本次编辑会让若干既有节点的证据哈希过期，逐个刷新并在记录里说明为何评估不变）；
  指南：HANDOFF.md（新节 + 计数改二十四 + 证书表新行）、README.md、research/verification.md、formalization/README.md、
  formalization/FunctionalInequalities/Energy/README.md、solutions/README.md、formalization/blueprint/README.md；
  research/naming.md 按陈述记录「未做」一节列出的三组名字加表行。

坑与提示：
- `omit ... in` 必须放在 **docstring 之前**，否则报 `unexpected token 'omit'; expected 'lemma'`。
- unusedSectionVars linter 是逐轮报告的：修掉一批后下一轮才暴露下一批，需要多轮编译才收敛。
- 拆分会改变 section variable 的可见性，原来靠 `omit` 消掉的警告可能变位置，也可能出现新的；
  以 `-DwarningAsError=true` 为准。
- 本机**没装 plastex**，`blueprint/lean_decls` 是旧清单，`build.py checkdecls` 比对的是过期内容。
  新加的 \lean{} 名字请用 `lake env lean` 写个临时文件逐个 `#check` 验证（scratch 目录，别放进仓库）。
- research/verify.py 必须在**所有**指南与决定记录编辑完成之后跑，收据才是当前的。

编译与检查（在 formalization/ 下跑 lake，其余在仓库根）：
  lake build
  lake env lean -DwarningAsError=true <每个新模块与改动的模块>
  python3 research/check_ledger.py          # 期望 24 节点，0 错误
  python3 research/check_blueprint.py       # 期望 88 标签，0 错误
  python3 research/atlas.py check           # 期望 24 证书，无环
  python3 -m unittest discover -s research/tests -p 'test_*.py'
  python3 research/verify.py                # 最后跑
并对证书与两条库定理 #print axioms，只允许 propext / Classical.choice / Quot.sound。

完成后的报告请列出：拆分后的模块清单与各自的公开声明；「无 sorry 部分对依赖封闭」是怎么验证的；
新 label 与证书名；Blueprint 新块的 \lean{} 名字与验证方式；注册轮逐项完成情况；
所有检查命令的实际输出；以及若你认为某条陈述有问题（缺前提、范围写错等）给出具体理由。
```
