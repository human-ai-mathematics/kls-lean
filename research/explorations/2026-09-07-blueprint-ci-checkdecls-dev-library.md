# Blueprint CI 回归：`checkdecls` 导入未构建的 `Dev` 库

日期：2026-09-07（Asia/Shanghai）。对象：推送到 `origin/main` 的提交 `575c82c`。

## 现象

`gh run list` 显示该提交的两个工作流结果不同：`Lean certification`（run 34136280187）成功，
`Lean Blueprint`（run 34136280179）失败。失败步骤为 "Check Blueprint declaration links"，即
`python3 formalization/blueprint/build.py checkdecls`，日志：

```text
uncaught exception: unknown module prefix 'Dev'
No directory 'Dev' or file 'Dev.olean' in the search path entries
```

## 原因

`575c82c` 在 `lakefile.toml` 新增了 `[[lean_lib]] Dev`（roots `Dev.Search`，LeanSearchClient
查询草稿），并刻意把它排除在 `defaultTargets` 之外，以免联网的查询命令进入可复现构建。
但固定版本的 `PatrickMassot/checkdecls` 的 `Main.lean` 会导入根包**全部** `lean_lib` 的根模块
（`ws.root.leanLibs.flatMap (·.config.roots)`），不区分是否为默认目标。CI 只运行 `lake build`，
`Dev.olean` 不存在，`importModules` 抛出异常。本地之前曾手动 `lake build Dev`，所以本地
`checkdecls` 不会暴露此问题。

## 处理

- 从 `lakefile.toml` 删除 `Dev` 库声明，保留 `formalization/Dev/Search.lean` 文件；在 lakefile
  与该文件的说明中记录原因，改为用 `lake env lean Dev/Search.lean` 或编辑器直接加载。
  `formalization/README.md` 的目录注释同步。
- 本地复现 CI 步骤：从 Blueprint 章节的 `\lean{}` 锚点提取 136 条声明写入临时文件，运行
  `lake exe checkdecls <file>`，退出码 0，无 "missing"。该临时清单与 plastex 生成的
  `lean_decls` 不是同一文件，只用于确认导入阶段不再失败、且当前锚点（含本日新增的十二条）
  都存在于已构建库中。
- 未重新推送；远端 CI 对 `575c82c` 的失败记录保持原样。修复随下一次推送生效。

## 边界

这是构建配置问题，不涉及任何数学声明、证书或 ledger 状态。`Lean certification` 工作流与
本地 `verify.py` 均未受影响。
