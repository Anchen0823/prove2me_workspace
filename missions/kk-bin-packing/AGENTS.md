# Karmarkar–Karp geometric grouping

先读 `status.md` 和 `scope.json`。只处理本任务及实际 import 的依赖。

- 导航：`python scripts/workspace.py files kk-bin-packing`
- 构建：`python scripts/workspace.py build kk-bin-packing`
- 研究、临时证明、平台证据放本目录；正式模块保留 `Definitions/`、`Theorems/`、`Solutions/` 路径。
- 新增正式证明后更新本任务 `scope.json`，运行 `python scripts/workspace.py check`。
- 不运行根目录全量构建，不改其他任务，不读取凭证做离线工作。
- 平台提交由主代理统一执行；子代理只在明确分配的文件写入。
