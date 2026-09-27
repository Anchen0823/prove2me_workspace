# 多任务工作区：先选择任务

根目录负责导航与共享 Lean/Mathlib 环境，不代表一个需要整体构建的任务。

- 用户指定任务时，直接进入 `missions/<slug>/AGENTS.md`，再读该任务的交接文档与 `scope.json`。任务不明确时只读 `missions/index.json` 或运行 `python scripts/workspace.py list` 来定位。
- 不要为建立背景而遍历全部 `missions/`、`Solutions/`、`examples/`、`.workbuddy/memory/`、`docs/history/` 或 `release/`。只读当前任务文件和实际需要的依赖。
- 构建使用 `python scripts/workspace.py build <slug>`。根目录 `lake build` 只检查空工作区目标；它不表示任何证明已验证。全量 `lake build Solutions` 仅在用户明确要求全量审计时运行。
- `Definitions/`、`Theorems/`、`Solutions/` 是共享平台模块目录；模块路径保持稳定。Lean 根据真实 import 自动构建依赖。
- 增加证明文件后更新所属任务 `scope.json`，运行 `python scripts/workspace.py check`，避免新文件无归属。只记录和更新当前任务的状态。
- 平台流程按需读取 `SKILL.md` 和具体 API 文档；不要把所有引用文档装入上下文。不要读取凭证来做文件整理或离线构建。
- 推荐在对应任务目录开启新聊天；指令约定不构成权限沙箱，也不能清空已有聊天上下文。
