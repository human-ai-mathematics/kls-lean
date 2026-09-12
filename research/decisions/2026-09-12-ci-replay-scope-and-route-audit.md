# 2026-09-12 — 修复干净 CI 的重放构建范围，并复核数学路线

Owner 要求检查远端失败、复核数学路径，并提交当前修改。本轮包含此前未提交的研究同步。

## 远端失败的原因

提交 `d2f136f6633ddd2455b838a36732502978b37a56` 已在 `origin/main`，并非提交或推送失败。
[Lean certification 运行 34695539602](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/34695539602)
中，Python 测试、默认 Lake 构建、陈述快照和声明审计已经执行；随后准备重放输入时报错：

```text
Current source formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean has no built module
```

默认 `lake build` 只覆盖库的根模块和导入闭包；保留在源码中但未被正式入口导入的 WIP 不必被构建。
验证器却要求重放所有当前本地源码。开发机曾单独构建 WIP，已有缓存掩盖了这个不一致。
同一提交的 Blueprint CI 成功；本轮查看到的 Nicolas 上游最近检查也成功。

## 修复

`research/verify.py` 用同一个 `replay_sources` 映射决定构建与复制范围，
在复制重放输入前显式 `lake build +Module` 构建全部当前待重放模块。
这会重新检查已有构建的时效，也覆盖干净 CI 中未被导入的模块；不依赖 `.olean` 恰好存在。
保留默认构建门、缺失模块失败检查、孤儿产物过滤和严格的重放覆盖集合比较。
没有修改默认库入口或证书 import，没有把 WIP 放进认证闭包，也没有允许证书使用 `sorryAx`。

新增的真实 Lake 临时项目回归测试在无缓存环境证明：
默认构建遗漏未导入 WIP → 旧重放准备失败 → 显式范围构建成功 → 正式根模块仍不依赖 `sorryAx`。
夹具同时含已删除路径和 Dev scratch 路径，它们不能进入重放范围。
所有临时构建与验证日志均不提交。

## 数学路线复核

这是对当前命题、归一化、依赖及上游证据边界的审查，不是重新证明全部上游自然语言 dossier。
没有发现本轮同步引入新的循环依赖、把开放假设当结论、或把常数约定混用的问题。
核对对象是 Blueprint 路线章、route-composition、tasks、当前证书及固定上游的原始记录。

| 路线 | 足以推进到 KLS 的接口 | 仍需明确保留的边界 |
| --- | --- | --- |
| 条件纤维 | `Var ≤ C D` 与已认证 `D ≤ 4 E` 给 `C_P ≤ 4 C`，再经仿射/各向同性归约 | `C` 位于维数和测度量词之外；同一个 frame 不依赖测试函数；涵盖完整有限形式域。二次多项式计算不能给全 `L²` 结论 |
| 谱局部化 | universal-time full-damping occupation 的条件性充分性 | 时间与常数须一致穿过正则化。Letwin 输入下的 `log² n` 窗口仍依赖维数；不能关闭 universal-time gate |
| CMH recovery | 一条适当 `W₂` 恢复序列与一致 CMH 控制，经下半连续性和归约到 KLS | 需要控制完整形式及退化仿射支撑；弱 column equation 不能充当强算子域方程；锥模型、线性 sector 不给统一 envelope |
| Eldan | tight-prefix 吸收估计与 Riccati/survival/几何比较链 | regular split class 的 screened supply 不覆盖所有切集；已反驳的 weighted package 不能恢复成有效输入 |

共同的几何桥梁仍未全部 Lean 化：相对周长恢复、Cheeger 下确界及 Cheeger–Buser 两侧常数比较。
已认证的 `E_can = 2 Ch` 是能量识别，不替代几何等周常数与 Poincaré 常数的比较。
路线图无依赖环只是结构事实，不足以证明上游数学正确；开放路线仍需新的数学输入。

新增文献沿用 `1/4 ≤ ψ²/C_P ≤ π`：Letwin 的 `ψ_n = O((log n)^(1/4))`
对应 `C_P = O(sqrt(log n))`；thin-shell 本身仍不构成维数无关 KLS 的证明。
正式 Lean 证书为 24 个，当前 WIP 直接 hole 为 24 个；本轮没有改动数学陈述或证明。

## 验证与提交边界

运行回归测试及完整 `research/verify.py`，通过后提交；最终回执由
`build/verification/latest.json` 指向并匹配源码快照。远端 CI 是否通过需提交发布后的实际运行证明，
不能用本地通过替代。本轮用户要求提交，未要求推送，因此创建本地提交。
