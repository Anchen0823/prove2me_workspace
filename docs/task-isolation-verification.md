# 任务隔离验证（2026-09-27）

- `python scripts/workspace.py check`：18 个任务、40 个既有脚本迁移记录、75 个 Python 文件通过结构检查。
- `python scripts/test_workspace.py`：6 项测试通过，覆盖任务入口不重叠、dry-run 不启动构建、空清单不回退全量构建、构建错误码传递、越界及失效路径检查。
- 已安装固定版本的 `lake build`：成功，1 job；根目录不再默认构建任何任务源码。
- `python scripts/workspace.py build two-squares`：成功，2 个选定根模块；Lake 报告 909 jobs（含所需依赖）。
- `python scripts/workspace.py build no-adjacent`：成功，12 个选定根模块；Lake 报告 1008 jobs（含所需依赖）。定理镜像的既有 `sorry` 警告仍在，不能据此断言无公理漏洞或平台证明已被接受。
- 在 `missions/two-squares/` 运行 `python ../../scripts/workspace.py build two-squares --dry-run` 和 `show`：成功。
- 3 个文件移动前后的 SHA-256 一致，路径与摘要见 `task-entry-migration-2026-09-27.json`。

本次没有全量构建其他任务，没有执行平台提交或修改证明源码。整理前已有的未提交修改保留。上下文边界是 agent 指令约定；不是文件系统沙箱，旧聊天上下文也不会自动清空。

## 论文归档与提交检查

- 15 个原 PDF 路径归并为 14 份不同论文；Tao 的两个原副本 SHA-256 完全一致。所有目标文件摘要与原件一致。
- 论文索引里的本地链接全部存在，活动任务文档已更新路径；旧跨任务历史审计保留原文，旧 `referpaper/README.md` 提供跳转。
- 全部 18 个任务的交接文件、源码和论文入口已对 Git 暂存区校验，确保提交后索引不会指向未跟踪文件。
- `git -c core.whitespace=cr-at-eol diff --cached --check` 通过；已有证明及证据文件的原始换行保留。
- 此提交包含新任务清单依赖的既有本地源码与交接材料；没有重新验证所有历史数学结论或平台状态。
