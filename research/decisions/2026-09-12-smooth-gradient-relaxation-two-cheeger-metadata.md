# 2026-09-12 — `thm:smooth-gradient-relaxation-two-cheeger`：元数据清理（不动数学）

## 背景

`python3 research/atlas.py ready` 把该节点判为 `clarify_statement`。原因是 Blueprint 块带 `\notready`，
而这一判定在 `atlas.py` 里优先于 `mathematics` 分类。但该标记的理由在
[陈述记录](2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md)里已经失效：

- Blueprint 自己的规则（`00-orientation-and-status.tex`）写明 `\notready` 只标"显式未决的陈述选择"，
  并且"An open proof or possible future API changes alone do not justify the marker"。
- 原文给的两条理由是 (i) 要形式化哪个 Cheeger 能量定义未定；(ii) 奇异测度下两种松弛的比较无文献出处。
  (i) 已在陈述记录里做出选择（局部斜率约定、`Lip_a` 版本另立为显式义务、仿射支撑传输沿用
  `def:intrinsic-affine-energy`），只剩 (ii)，而 (ii) 是开放**证明**。

## 决定

- `30-open-canonical-bridges.tex`：去掉该定理块的 `\notready`；改写其后的说明段，记录已做出的定义选择、
  `Lip_a` 版本作为独立义务、剩下的是开放证明（由缺少 `\leanok` 记录）、开发位于
  `Energy/WIP/Cheeger.lean`（未进聚合导入、无证书、不冻结公开签名）。
- `research/tasks.json`：改写该节点已失效的 `note`（原文是"Resolve local-slope versus
  asymptotic-Lipschitz conventions and singular-measure scope before proof work"），
  写清楚约定选择、WIP 模块状态（26 条义务已证 21 条，5 条 `sorry` 归约为两条真正的奇异测度义务
  `LocalSlope.relaxation_eq_asymptoticLipschitz` 与 `SmoothGradient.relaxation_eq_localSlope`）、
  以及已证完的绝对连续/对数凹范围。
- **`mathematics` 保持 `unknown`，未加 `infrastructure` 记录。** 理由见下。
- 不动 `Energy/WIP/Cheeger.lean` 的任何声明与证明；不注册、不提交、不推送。

## 为什么没有按"换成真实的基础设施评估"执行

`research/verification.md` 与 `atlas.py` 的校验规定：`infrastructure` 字段**只有** `local_argument`、
`published`（以及可选的 `definition`）才允许携带，其它分类带上即报错
（`task ...: require exactly [...]`）。因此要挂基础设施评估，就必须先把分类从 `unknown` 抬到
`local_argument` 或 `published`。

而 `local_argument` 的语义是"a proof plan or a written argument"。对**无条件**的奇异测度陈述，
Blueprint 明说没有文献出处，本仓库也没有证明计划——只有绝对连续范围有完整证明。把分类抬到
`local_argument` 等于断言我们对开放部分有论证，这是超出证据的。`published` 同理不成立。

因此本次保持 `unknown`，把全部真实状态写进 `note`（该字段的文档语义正是"Mathematical scope,
review requirement or execution guidance"）。dispatch 随之从 `clarify_statement` 变为 `review`，
含义是"请人来定这个分类"，与实际情况一致。

若 owner 认为该无条件陈述应当被断言为可由本地论证达成，再改分类并补 `infrastructure`；
或者按另一条路线，把已证完的绝对连续/对数凹范围立为独立 Blueprint 节点并注册证书
（`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` 已无 `sorry`，
经已认证的 `lem:logconcave-intrinsic-absolute-continuity` 覆盖全部对数凹律）。本次未做。

## 检查

- `python3 research/check_blueprint.py`：87 标签，0 错误。
- `python3 research/atlas.py check`：74 数学节点，23 证书，无环。
- 该节点 dispatch：`clarify_statement → review`，`statement_question: false`，无 blockers。
- `python3 research/check_ledger.py`、单元测试、`lake build`、`research/verify.py` 见下方本轮末次运行。
