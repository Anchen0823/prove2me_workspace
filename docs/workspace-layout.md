# 按任务组织的共享工作区

## 日常入口

在 `missions/<slug>/` 开启新 agent 聊天。每个任务有 `AGENTS.md`（阅读边界）、交接文档和 `scope.json`（源码与构建入口）。任务目录与平台模块目录分工明确，不复制 Lean 源码或 Mathlib。

从根目录运行：

```powershell
python scripts/workspace.py list
python scripts/workspace.py show no-adjacent
python scripts/workspace.py files no-adjacent
python scripts/workspace.py build no-adjacent --dry-run
python scripts/workspace.py build no-adjacent
python scripts/workspace.py check
```

从任务目录运行 `python ../../scripts/workspace.py build <slug>` 也可；脚本总是在仓库根目录调用 Lake。

## 目录职责

| 位置 | 内容与读取时机 |
| --- | --- |
| `missions/<slug>/` | 该任务的状态、研究、脚本、验证记录、`AGENTS.md` 和 `scope.json` |
| `Definitions/`、`Theorems/`、`Solutions/` | 平台规范要求的稳定模块路径，通过任务清单定位，不全量预读 |
| `examples/<area>/` | 试验与可复用 Lean 辅助模块；只有登记的构建入口或真实 import 才参与任务构建 |
| `scripts/` | 共享平台工具、任务导航和结构检查 |
| `.lake/`、`lean-toolchain`、`lake-manifest.json` | 所有任务共享的固定工具链、依赖和缓存 |
| `SKILL.md`、`references/`、`agent_docs/` | 按需读取的平台流程，不是每个任务的必读背景 |
| `missions/<slug>/papers/` | 按任务归属的论文；其他任务复用时链接原副本 |
| `referpaper/README.md` | 旧路径导航，PDF 已迁入对应任务 |
| `docs/history/`、`.workbuddy/memory/`、`release/` | 历史与归档，不作新任务的默认上下文 |
| `tmp/` | 临时探针，不参与构建 |

## 构建边界

根目录 `lake build` 的默认目标是无源码的 `Workspace`，不会再遍历整个 `Solutions`。任务命令把 `scope.json` 中的 `build` 模式展开成具体 Lean 文件，交给 Lake 构建它们及真实 import 依赖。魔方阵 I–V 也分别登记入口，仍可共享定义与辅助模块。

- `sources` 是源码导航范围；`build` 是构建入口，两者用途不同。
- 空构建清单表示研究/维护任务尚无登记目标，不表示验证通过。
- `zeta9` 当前只登记根目录的定理镜像；构建成功也不是这些定理已证明的证据。
- 原始平台 payload、失败实验、发布 staging 和大型 `SondowRosserMiddle*` 数值证书不默认构建；需要时显式选择和验证。
- 全量审计仍可显式运行 `lake build Solutions`；环境冒烟测试为 `lake build Solutions/SmokeTest.lean`。
- 工具优先使用本机已经安装的固定版本 Lake，避免 elan 启动器的自更新网络检查。

共享依赖可能跨任务构建，这是 import 所需的数学依赖；不会因为同在仓库就构建其他任务的全部证明。agent 的读取边界由指令约定控制，不是访问权限隔离。已经加载到旧聊天的内容不会被这些文件移除。

## 新增任务与源码

建立 `missions/<slug>/`，补充交接文档、`AGENTS.md`、`scope.json`，登记 `missions/index.json` 与 `missions/README.md`。每个根目录 `Solutions/*.lean`（冒烟测试和大型诊断证书除外）应恰好属于一个任务的构建清单；检查命令会报告遗漏或重复归属。

新增脚本放 `missions/<slug>/scripts/`，通过脚本位置定位仓库根目录，不依赖调用者的工作目录。新增平台源码继续使用原模块路径，以免破坏 import、提交脚本和已有证据。

## 整理记录

2026-09-27：补齐任务索引，增加 18 个任务的上下文与构建清单，取消默认全量构建。根目录的 Zudilin 说明和 HTML 移至 `missions/zudilin/research/`；根目录临时 Lean 探针移至 `tmp/`。既有未提交证明、历史记录、发布目录和缓存均保留。

此前的脚本移动映射仍在 [script-migration.json](script-migration.json)，历史总览在 `docs/history/`。

## 开启新对话

日常建议在 `missions/<slug>/` 开启新对话；同一个任务持续使用同一目录，更换数学目标时新开对话。根目录适合全仓整理、共享工具链维护和跨任务审计。

Codex 会从仓库根目录向当前工作目录加载 `AGENTS.md`，不会因为从根目录启动就自动加载所有任务的子目录指令。依据：[OpenAI 官方说明](https://learn.chatgpt.com/docs/agent-configuration/agents-md)。如果仍从根目录开对话，在首条消息明确任务 slug，并要求先读对应任务的 `AGENTS.md`。

目前这些任务共用同一 Lean/Mathlib 环境，用现有任务目录即可；不需要为每次聊天复制项目或创建新的 Git 仓库。未来与 Lean 无关、依赖和交付物独立的项目可另建项目根目录。
