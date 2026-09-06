# Lean 基础清理后的严格复核

日期：2026-09-06。用户要求“严格检查一遍”。本记录追加于
`2026-09-05-lean-foundation-cleanup.md`，不改写此前记录。

结论：没有发现本轮 Lean 重构造成的证明错误、假设加强、声明删除或额外公理依赖。
复核另发现并修正两处 Blueprint 定义不够明确的问题。基础可以继续承载 KLS statement
工作，但本次检查不把未形式化的常数比较、whitening 或路线结论升级为 Lean 证明。

## 发现与修正

### 文献常数的有限测试域与无穷值

`def:literature-poincare-constant` 原来使用“least C in [0, infinity]”，并以“finite
right-hand side”描述测试范围。这没有明确区分能量有限与乘上候选常数后有限，尤其没有
充分规定无有效有限常数的情形。

这不是可以忽略的边界：对 `μ = (δ₋₁ + δ₁)/2`，取在两个原子附近分别恒为零和一的
全局 Lipschitz 函数，其方差为 `1/4`，局部 slope 能量为零。没有有限常数有效。按照
Lean `ENNReal` 的乘法，直接把无穷当成一个满足不等式的乘数还会遇到 `∞ * 0 = 0`。

现在先固定 `L²` 中具有有限 slope 能量的 locally Lipschitz 测试域，对有限 `C ≥ 0`
定义不等式有效性，再将文献常数定义为所有有效有限常数的下确界，空集下确界为无穷。
零能量测试明确保留。`thm:klartag-density-frontend-identification` 的重复表述同步修改。
这与本地 `TestFamily` 优化器及 legacy 常数的约定一致，不要求一般 Borel 测度具有密度。

### 纤维形式的联合可测性与异常纤维

`def:conditional-fiber-form` 原先只写沿每个方向 disintegrate，没有明确外层方向积分
所需的联合可测版本。现在从 `ρ ⊗ μ` 下的联合分布，按
`(θ, P_{θ⊥} x)` 对 `T = ⟨x, θ⟩` 作 disintegration。标准 Borel 载体上的条件核由此
可联合选取；对固定 `ρ`，其唯一性只需在联合底测度几乎处处成立。

定义明确了异常纤维、零方差纤维及条件二阶矩无限的纤维贡献零，并说明有限二阶矩使
最后一类为零测集。形式值与条件核版本及 `L²` 元素的 Borel 代表无关。测试函数不会
参与条件核的选择。

本地保留任意 Borel 有限二阶矩概率律的形式定义。factor-four 定理仍在有密度的
full-dimensional log-concave 范围内，未把一般测度的定义当成所有结构定理的证明。

## Lean 基线与内部声明比较

起点 HEAD 仍为 `70ca1c19c4d207a31716c2e589c0b096521a5490`。使用上一轮清理开始前
保存的源码建立独立临时 Lake 包，仅共享版本固定的外部 dependencies，重新构建其本地
模块和四份证书。基线构建成功，共 3230 jobs；当前默认构建成功，共 3234 jobs。

分别导入两套 library aggregate 和四份 certificate，枚举项目命名空间及其私有声明。
本次比较 `reprStr ci.type`、宇宙参数和 `ci.value?` 的内部表达式，不依赖 pretty-printer
隐藏的 implicit 参数或记号。证明体允许因重构变化，由当前源码重新检查和传递公理审计
验证；可归约定义体则直接比较。

| 项目 | 结果 |
| --- | --- |
| 原有声明 | 689 个：665 个公开命名空间声明、24 个私有声明 |
| 声明删除 | 0 |
| 内部类型变化 | 0 |
| 宇宙参数变化 | 0 |
| 可归约定义体比较 | 175 个，全部相同 |
| 新增声明 | 仅两个已记录的逼近引理，合计 691 个 |
| 额外传递公理 | 0；仅出现 `propext`、`Classical.choice`、`Quot.sound` |
| unsafe / partial 声明 | 0 |

比较器要求至少 650 条非空记录并检查名字无重复，避免空解析产生假通过。本轮严格复核
没有再次修改 Lean 源码。

另逐文件运行 `lake env lean -DwarningAsError=true`：49 个 library、certificate、audit
及 example 文件全部重新 elaboration 成功。它不是只读取 `lake build` 的缓存成功状态。
12 个使用示例、八个基础公理 guards 及 Gaussian audit 均在其中。

## 数学范围与来源核对

- 逐项检查了抽取引理、有限与无限 recovery 分支、下半连续性和二次闭包的消费者。
  伪度量假设、有限能量条件以及无限能量分支需要的密度前提均保留。
- 条件纤维路线的方向是 `D ≤ 4 * gradientEnergy`，所以形式 gap 给出 `C_P ≤ 4C`。
  量词是一个有限常数对全部正维与合格测度成立，然后按测度选一个不依赖测试的 frame。
  零维直接用零方差，推广至 proper affine support 明确依赖 affine/isotropic bridge。
- 从上游固定 commit `8185e46ffb040e04fea076953e5bcaeb4157d71a` 重新读取
  `modules/kls/45-conditional-fiber-frame.tex` 和
  `solutions/conditional-fiber-frame-structure.tex`，核对了定义、最大形式域、联合可测版本、
  因子四与异常纤维约定。上游 agent review 仍只作为出处。
- 全部 `leanok`、`notready` 标记按节点与清理前快照比较保持不变。没有新增 ledger 节点，
  没有把 Blueprint 构建当作数学或 Lean 认证。

## 最终验证

- Ledger：4 nodes，0 errors。
- Blueprint：73 labels、4 active routes，0 errors。
- Python tests：63 项全部通过。
- Blueprint PDF、网页与 `checkdecls`：全部成功。
- 最终 PDF：27 页；物理页 5、17、24、25 重新渲染检查，无裁切、重叠或未解析引用。
  最终日志无 overfull、undefined references/citations 或重复 label，保留 8 条 underfull 提示。
- 对清理前 130 个源码文件逐个比较：109 个字节不变，21 个为两轮已记录修改，未删除文件。
  四份证书、ledger、版本固定文件、既有历史记录和无关 ` 2` 副本均保留。
- `git diff --check` 通过。所有工作仍是本地未提交状态，未 push 或执行远程 CI。

临时基线、内部声明快照、逐文件检查结果和渲染证据位于：

```text
/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-strict-review-20260906-0pxohkh8/
```

其中 `raw-comparison.json` 记录内部比较，`strict-all-lean.json` 记录各文件返回码，
`sha256.json` 记录证据散列。类型快照的 SHA-256：

```text
before 528310b7388c53c97badb28ddfa33cff72fb6db2e1067f3361a54abfb1424ad2
after  7529da49f7077cd088b1842a6b291327862da074f3b1cac1a7294b651f06398e
```

这次复核没有完成 KLS 主命题的 Lean 声明或其分析桥接，也没有独立证明整个上游路线。
一维 log-concave 因子四的原始 KLS 文献位置、Cheeger frontend regularization 的精确来源
等已标出的文献债务仍然存在。
