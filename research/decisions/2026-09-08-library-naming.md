# 全库文件、namespace 与短名整理

用户要求对整个 formalization 库落实简洁、按数学对象组织的命名。沿用已验证的未提交
工作区，不从 Git HEAD 重做迁移。基线快照为
`7151e3eb054c8f54dd8322c7fe4ea5af9093e23292179a3abcc450e22b5660b4`，
对应 `build/verification/20260908T125319.902218Z/report.json`。
HEAD 为 `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`，分支为 `main`。

## 组织与接口

本次修改 33 个公共短名，移动 12 个模块，整理 35 个库文件的声明作用域与限定路径。
完整映射见 [公共名称](../api-migration/2026-09-08-library-naming-name-map.json)和
[模块路径](../api-migration/2026-09-08-library-naming-module-map.json)。

- 局部斜率的梯度结论从 `KLS/LocalSlopeGradient.lean` 移到
  `Energy/LocalSlope/Gradient.lean`，外层改为 `namespace FunctionalInequalities.Energy.LocalSlope`；
  声明头为 `theorem apply_eq_norm_gradient`。其自身仅依赖局部斜率定义和微分工具，
  消费者显式导入需要的 Poincaré 接口。
- 光滑测试的 Basic、Optimal、Transport、Linear 以及 Comparison 同属 `Poincare/SmoothTest/`。
- 对数凹目录使用 `Covariance`、`Translation`、`ClosedForm`、`WeightedGradient`、`Isotropic`、
  `Poincare`，删除重复的 Affine 标签；Borel 集与 Borell 表示仍明确区分。
- `L2.Transport` 按 Translation、LinearIsometry、ContinuousLinearEquiv 三个 namespace 分组。
  其余跨对象比较在共同父 namespace 下按实际对象分组；全库不再有使用
  `_root_.FunctionalInequalities.…` 的声明头。
- 公共名称保持原 namespace 归属。`LogConcave` 推论仍从性质证明调用，例如
  `hμ.intrinsicCovariance_closedQuadratic`、`hμ.intrinsicSmooth_constant_eq_localSlope`、
  `hμ.intrinsicWeightedOperator m B`。`f.energy`、`f.toL2` 与 `hf.memLp` 保留。

命名保留 weighted、covariance、smooth、Lipschitz、intrinsic、ae、有限性和比较方向等
有数学作用的区别；类型与文档给出全部条件。没有改动归一化、测试类或承载空间，
没有参数泛化、兼容别名、包装、占位证明或 linter 关闭。

## 语义和来源审查

基线先核对完整源码与通过的收据一致，保存源码和解析引用位置。
完整表达式基线由已验证的 1085 项快照及随后 132 项比较改名闭包合成；旧记录读取时
先应用已验证的前次 12 项名称映射，再应用本次映射。没有回退之前已批准的改动。

- 881 个公共源码签名、189 个定义/结构主体逐项一致。
- 包含所有私有辅助、solutions、examples 在内的 969 个声明主体逐项一致。
- 从全部 881 个公共根出发的 1085 个本地声明，其原始 Lean Expr 类型与定义闭包在
  声明映射、模块路径映射和绑定变量 alpha 归一化后全部一致，无新增、缺失或未解释差异。
  宇宙、参数顺序、显隐、参数类型和依赖保持一致。匿名实例的编译器命令哈希及已声明
  模块迁移单独归一化，局部 hygiene 序号仍核对。定理证明主体另由源码对比和 Lean 检查覆盖。
- 26 项 statement golden 检查通过；golden 和其引用的原 decision 均未改动。
- 158 条基础设施来源记录先核对基线文件及旧哈希，再按上述语义对比刷新其中 58 条。
  94 份既有 decisions、explorations 和迁移记录保持原字节。

审查细节在 [review](../api-migration/2026-09-08-library-naming-review.json)与
[evidence](../api-migration/2026-09-08-library-naming-evidence.json)，原始本地审计材料在
`build/api-final-naming/`。完整当前公共名称清单由最终编译的 `.ilean` 刷新到
`build/name-inventory/current-public-names.md` 和 `.txt`。

## 验收

默认 `lake build` 已通过；全部 33 个新名可解析，旧名不可解析。
Blueprint PDF、Web、checkdecls 已通过；37 页重新渲染并与上一份验证的 PDF 逐像素对比相同，
复看第 7、29 页无排版变化。最终统一验收入口为仓库根的 `python3 research/verify.py`，
以其最终源码快照和各项 gate 收据为准，包括全部本地模块的 kernel replay。
本次工作只修改本地工作区，没有提交或推送。
