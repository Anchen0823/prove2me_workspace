# 项目审查整理报告 · prove2me_workspace

- 审查日期：2026-09-17（Asia/Shanghai）
- 审查对象：`D:\users\self_projects\prove2me_workspace`
- 报告性质：**汇总撰稿**。本报告不重新审查代码库，只把五份审查产物合并、去重、按统一严重度重排、标注冲突。
- 输入产物（全文只读）：
  1. `survey/inventory.md` — 仓库现状事实清单（repo-surveyor）
  2. `audit/lean-code-audit.md` — Lean 源码质量审查（lean-auditor）
  3. `audit/scripts-config-audit.md` — 脚本与工程配置审查（script-auditor）
  4. `audit/docs-consistency-audit.md` — 文档与记录一致性审查（docs-auditor）
  5. `audit/vcs-hygiene-audit.md` — 版本控制卫生审查（vcs-auditor）
- 追溯规则：本报告每条结论均标注来源（如「lean-code-audit §4.1」）；无法在输入产物中找到出处的，一律标注「未验证」或删除，不做平滑填充。
- 硬约束遵守：**未执行任何清理操作，未修改项目任何源码/配置**；仅写入本文件。所有涉及删除/脱管/重写历史/改文档/改配置的动作，全部归入第 6 节「待裁决事项」，当前授权状态一律为「待用户确认」。

---

## 1. 执行摘要

**项目现状（一段话）**：`prove2me_workspace` 是一个以 Lean 4 形式化证明为主线的工作区，核心成果是 Magic Squares I/II/III 三条使命线（均已 Proved）与 five-primes / weak-goldbach / euler-gamma 等分析线（进行中）。仓库当前处于 `main` 分支、工作树干净、领先 `origin/main` 3 个提交（`eff4d7d` / `bcdfd33` / `c2bbb0e`，均未 push）。**当前 `lake build` 无法通过**——因一个悬空 import（见第 2 节）。仓库体量的大头是本地构建缓存 `.lake/`（8.4 GB，已被忽略、勿删）与异常偏大的 `.git/`（146 MB，主因是历史中仍可回收的生成证书 blob，而非当前文件）。多数问题是「卫生与一致性」层面（生成物入库、`.gitignore` 覆盖不全、文档漂移），而非数学/证明正确性缺陷；`Solutions/` 全部为真实证明、无 `sorry`，自有源码无 `axiom`、无 `native_decide`。

**Top 5 问题（按统一严重度）**

| # | 问题 | 严重度 | 来源 |
|---|---|---|---|
| 1 | `Solutions/Sol_vinogradov_lemma_if_form_coprime.lean:3` 悬空 import 使 `lake build` 默认目标直接失败 | **阻断** | lean-code-audit §4.1 |
| 2 | `.git` 146 MB 的主因是历史中仍可达的生成证书 blob（≈199.7 MB 未压缩）+ garbage；真正回收须重写历史 + force push（不可逆） | **高** | vcs-hygiene-audit §3 |
| 3 | 一批生成物/日志仍被跟踪且 `.gitignore` 覆盖过窄（4 证书 `.lean` + 9 `.json` + 43 `.log`），脱管可逆 | **中** | vcs-hygiene-audit §1、scripts-config-audit §5.3 |
| 4 | `Theorems/` 镜像 doc 文本声称节点「now Proved」，实体却是 `by sorry`，只读 `Theorems/` 的读者会被误导 | **高** | lean-code-audit §1.1 |
| 5 | 文档严重漂移：根 `status.md` 指向错误的 active mission、magic-squares 一节数字过期；三篇幻方文档平台版本写成 v0.10.4；跟踪文件计数 `1032/22.5MB` 过期；`MEMORY.md` 仍称 5 个大生成物「在磁盘上」 | **高** | docs-consistency-audit §1、§2.1、§3 |

**本轮已确认的关键事实（均有命令/路径证据）**

1. **构建状态**：`lake build` 当前失败，根因是唯一一处悬空 import（lean-code-audit §4.1、§5 抽样 8 个文件 7 成功 / 1 失败）。
2. **占位与公理**：`Solutions/` **0 处 `sorry`**；`Theorems/` **45/50** 文件实体为 `by sorry`（仓库设计约定，`MEMORY.md:36-37`）；`Definitions/`、自有源码**无 `axiom`**；全仓自有源码**无 `native_decide`**（lean-code-audit §1）。
3. **当前树卫生**：跟踪文件 **1033** 个、跟踪树 **21.48 MB**；`credentials.json` 存在但**未被跟踪且被忽略** ✅；`tmp/`、`.lake/` 下 0 个被跟踪文件（vcs-hygiene-audit §0、docs-consistency-audit 附录 A）。
4. **应清理的已跟踪文件**：4 个生成证书 `.lean`（≈1.20 MB）+ 9 个配套 `.json`（≈56 KB）+ 43 个日志（≈165 KB，其中 22 个命中规则、21 个在更深层未被规则覆盖），另 3 个 `balanced-largest-block-*.lean` 生成诊断（≈2.10 MB）（vcs-hygiene-audit §1）。
5. **`.git` 体积成因**：历史可达大 blob（≈257.8 MiB 未压缩，含 `SondowRosserMiddle*1000000*.lean` 等 5 个证书 + `port/*.jsonl`）+ **138.2 MiB 未整理松散对象**（含 37.08 MiB 被 git 判为 garbage 的事故残留）；pack 仅 2.60 MiB（vcs-hygiene-audit §3.1）。
6. **大生成物的磁盘状态**：5 个大生成物已于 2026-09-17 19:10 **物理删除**（释放 199.7 MB），但 `MEMORY.md` 与 `missions/project-review-2026-09-17.md` 的**摘要层未同步**，仍写「文件仍在磁盘上」（docs-consistency-audit §3.1）。
7. **平台版本**：权威值为 **v0.10.3**（`SKILL.md:5` + 多处认证刷新记录 + `git log` 无 0.10.4 bump）；三篇幻方 mission 文档的 v0.10.4 与之矛盾（docs-consistency-audit §2.1）。
8. **远端**：`origin/main = 1b30762`（领先 HEAD 3 个提交），且**仍持有**这些大证书 blob；本审计**未 fetch**，远端最新状态未核实（vcs-hygiene-audit §3.1⑥、§4）。

---

## 2. 阻断级问题（置顶）

### 2.1 悬空 import 导致 `lake build` 直接失败

- **路径**：`Solutions/Sol_vinogradov_lemma_if_form_coprime.lean:3`
- **证据**（lean-code-audit §4.1、§5）：
  - `lake env lean Solutions/Sol_vinogradov_lemma_if_form_coprime.lean` → `error: object file '...\Theorems\Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block.olean' ... does not exist`（EXIT=1）
  - `lake build Solutions.Sol_vinogradov_lemma_if_form_coprime` → `bad import 'Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block'` → `no such file or directory ... .lean` → `build failed`（EXIT=1）
  - 全仓（排除 `.lake`）搜索 `vinogradov_lemma_if_form_from_block`：只在该文件的 import/使用处与忽略目录 `tmp/red_if_form_coprime.lean`（以 `axiom` 顶替）出现；`Theorems/` 下**不存在**该模块文件。
- **为何是阻断**：`lean_lib Solutions` 是 `@[default_target]`（`lakefile.lean:10-11`），会构建该目录**全部**模块，故 **`lake build` 当前直接失败**。
- **两种修法及其影响面**（均**未执行**，归入第 6 节待裁决）：

| 修法 | 具体动作 | 影响面 | 风险 |
|---|---|---|---|
| **A. 补齐镜像** | 新增 `Theorems/Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block.lean`（按仓库约定写 `by sorry` 占位 + doc 说明） | 仅**新增 1 个文件**，进入 `lean_lib Theorems`；`Solutions/` 该文件**不改动**，import 可解析，默认目标恢复；符合「语句在 Theorems、证明在 Solutions」的既有分层（lean-code-audit §3.2） | 新增的仍是空壳占位镜像，与 §1 同类的「占位易混淆」问题延续 |
| **B. 移除 import 与调用** | 删 `:3` 的 import，并处理 `:20` 处的调用 | 只改**1 个既有 Solutions 文件**；若 `:20` 确用到被 import 的 `..._from_block` 引理，则该证明将无法通过类型检查，**需重写或改引理** → 可能破坏一个已提交解法的完整性 | 可能连带破坏该解法；不新增文件 |

- **来源**：lean-code-audit §4.1（建议原文：「补齐镜像，或从该解法文件中移除该 import（连同 `:20` 的调用）」）。
- **建议**：优先修法 A（改动面最小、不触碰既有证明）；若该 import 本属误加，再考虑修法 B。二者均需授权后执行。

---

## 3. 问题总表（合并去重、按统一严重度排序）

统一口径：**阻断 > 高 > 中 > 低**。各成员分级到本口径的映射规则见 §8.4。来源列标注原始产物与章节。

| 编号 | 严重度 | 问题 | 证据路径 | 建议动作 | 来源 |
|---|---|---|---|---|---|
| Q1 | **阻断** | 悬空 import 使 `lake build` 失败 | `Solutions/Sol_vinogradov_lemma_if_form_coprime.lean:3` | 二选一修复（§2） | lean-code-audit §4.1 |
| Q2 | **高** | 镜像 doc 称节点「now Proved」，实体为 `by sorry`，误导只读 `Theorems/` 的读者 | `Theorems/Thm_MagicSquares_sm3_canonical.lean:9-11`（`:20` 为 `by sorry`）；`Theorems/Thm_MagicSquares_sm3_params_card.lean:10`（`:13`） | 修正 doc 措辞（改为「平台侧 Proved，本地为占位镜像」）或补真证明 | lean-code-audit §1.1 |
| Q3 | **高** | 根 `status.md` active mission 指向错误、magic-squares 一节与 mission index 过期 | `status.md:7`、`:17`、`:490-536` | 按 docs-consistency-audit §1 给的替换文本修正 | docs-consistency-audit §1.1/§1.2/§1.5（P0-1、P0-2） |
| Q4 | **高** | 5 个大生成物「仍在磁盘中」的**摘要记录过期**（文件已物理删除） | `.workbuddy/memory/MEMORY.md:98-99`；`missions/project-review-2026-09-17.md:166-168` | 按 docs-consistency-audit §3.1 替换文本修正 | docs-consistency-audit §3.1（P0-3） |
| Q5 | **高** | `.git` 146 MB 主因是历史 blob（≈199.7 MB）+ garbage；回收须重写历史 + force push | `.git/`（`git count-objects -vH`、`git rev-list --objects --all`） | 见 §6 不可逆项（待授权） | vcs-hygiene-audit §3 |
| Q6 | **高** | 脚本硬编码绝对路径，跨机器不可运行 | `scripts/submit_magic_batch2.py:11`、`gen_magic_batch3.py:12`、`write_magic_batch4_solutions.py:8`、`check_theorem51_progress.ps1:142` | 改为从 `lean-toolchain`/`sys.executable` 动态解析（参照 `check_grouping.ps1:8-10`） | scripts-config-audit §2.1 |
| Q7 | 中 | 生成证书 `.lean`（4）+ 配套 `.json`（9）仍被跟踪 | `Solutions/SondowRosserMiddle{Tree10000,10000,Hex10000,Tree10000Compact}.lean` 及 9 个 `SondowRosserMiddle*.json` | `git rm --cached` 脱管 + 补规则（§6 可逆项） | vcs-hygiene-audit §1(A)；scripts-config-audit §5.3(b)(c) |
| Q8 | 中 | `.gitignore` 覆盖过窄：`verification/*.log`、`item-tmp.json` 只匹配一级；`SondowRosserMiddle*.json`、`balanced-largest-block-*.lean` 未覆盖 | `.gitignore:19`、`:22-23`、`:30` | 按 vcs-hygiene-audit §2.3 diff 放宽为 `missions/**/...` 并补两条新规则（§6 可逆项） | vcs-hygiene-audit §2.2/§2.3；scripts-config-audit §5.3 |
| Q9 | 中 | 3 个机器生成的诊断文件（6 行、含 ~700 KB 字面量）入库 | `missions/euler-gamma/sondow/continuation/balanced-largest-block-{kernel,cbv,diagnostic}.lean` | 脱管（无下游 import、不在 target，脱管不破坏编译）+ 补规则 | lean-code-audit §6；vcs-hygiene-audit §1(C-1) |
| Q10 | 中 | `Theorems/` 45/50 文件实体为 `by sorry`（设计约定，但与已证命题并置易混淆） | `Theorems/Thm_*.lean`（45 个） | 保留约定，但在 `Theorems/README` 或文件头统一声明「本地镜像一律占位」 | lean-code-audit §1.1；docs-consistency-audit §5（见 §3.1 冲突说明） |
| Q11 | 中 | `Solutions/` 依赖未声明为 lib 的 `examples/`，属未声明依赖、脆弱 | `Solutions/SondowBalancedLcm.lean:1`、`SondowLcmTreeCertificate.lean:1`、`SondowRosserMiddle10000.lean:1`、`SondowRosserMiddleHex10000.lean:1` | 把 `RosserLcmBlocks` 迁出 `examples/` 或显式声明依赖 | lean-code-audit §4.2 |
| Q12 | 中 | `maxHeartbeats 0`（取消步数上限）等暴力设置，构建耗时不可控 | `Solutions/Sol_MagicSquares_magic_three_normal_classify.lean:6`、`Sol_MagicSquares_magic_three_normal_eight.lean:8`、`Sol_MagicSquares_sm3_bij.lean:7`、`Sol_MagicSquares_sm3_canonical.lean:6`；另 `maxRecDepth 100000`、`maxHeartbeats 4000000` 多处 | 评估收敛性，改为有限上限 | lean-code-audit §4.3 |
| Q13 | 中 | `Theorems/` 与 `Solutions/` 三组证明整段重复；辅助引理名 `two_mul_sum_Icc_sol` 泄漏来源 | `Theorems/Thm_MagicSquares_magic_constant_of_normal.lean:1-96` vs `Solutions/Sol_..._.lean:1-90`；`Thm_MagicSquares_magic_constant_of_normal.lean:11` | 明确单一事实来源，去掉重复与 `_sol` 后缀 | lean-code-audit §3.1、§2.2 |
| Q14 | 中 | 未被任何文件 import 的库内模块（疑似孤立） | `Definitions/Def_TaoFivePrimes_Theorem51Assembly.lean`、`Theorems/Thm_BunkbedFalse_hyperedge_simulation.lean`、`Theorems/Thm_TaoFivePrimes_vinogradov_odd_sharp.lean` | 确认是否仍需保留 | lean-code-audit §2.3 |
| Q15 | 中 | `p2m_api.py` 读 `expires_in`，忽略文档定义的 `expires_at`（文档—实现不一致） | `scripts/p2m_api.py:67-68` vs `references/setup.md:141-145` | 优先解析 `expires_at`，回退 `expires_in` | scripts-config-audit §2.2/§4.2 |
| Q16 | 中 | 8 个 `submit_*.ps1` 使用缓存 token，无刷新/过期重试，过期即 401 | `scripts/submit_*.ps1`（8 个） | 若要复用则补刷新逻辑；一次性可容忍 | scripts-config-audit §2.6 |
| Q17 | 中 | 平台版本漂移：三篇幻方文档写 v0.10.4，权威值为 v0.10.3 | `missions/{magic-squares,semi-magic,normal3}/status.md:3` | 改回 v0.10.3（与 `SKILL.md:5` 一致） | docs-consistency-audit §2.1（P1-1） |
| Q18 | 中 | 跟踪文件计数/体积过期：文档写 1032 / 22.5 MB，实测 1033 / 21.48 MB | `.workbuddy/memory/MEMORY.md:95`；`missions/project-review-2026-09-17.md:188-189` | 改为 1033 / 约 21.5 MB | docs-consistency-audit §3.2（P1-2） |
| Q19 | 中 | `README.md` 把 `scripts/` 描述为「Lean meta-programs」，与实际（40 文件中仅 2 个 `.lean`）不符 | `README.md:21` | 扩写为「upload pipeline meta-programs + per-mission platform helpers」 | docs-consistency-audit §2.2（P1-3） |
| Q20 | 低 | 命名不一致：`Def_eulerMascheroni_*` 小写驼峰、`Solutions/Sondow*` 缺 `Sol_` 前缀、`Theorems/` 命名空间三套风格 | lean-code-audit §2.1、§2.2 | 统一命名/命名空间策略 | lean-code-audit §2.1/§2.2 |
| Q21 | 低 | Lean 风格/配置类：`autoImplicit false` 冗余且不一致；39+16 文件全量 `import Mathlib`；`Solutions/SmokeTest.lean` 混入默认目标；局部关闭 linter | lean-code-audit §4.5、§4.6、§2.3、§4.7 | 逐项清理/加注理由 | lean-code-audit 对应各节 |
| Q22 | 低 | 脚本死代码/未用导入/docstring 与实际不符/复制粘贴错误文案 | `scripts/gen_magic_batch4.py:13,17`；`write_magic_batch4_solutions.py:5,8`；`submit_typeII_scale_reduction.ps1:37` | 删死代码、修 docstring 与错误文案 | scripts-config-audit §2.4/§2.5 |
| Q23 | 低 | `p2m_api.py` 隐式依赖 `urllib.error`、`_CTX` 定义后未用 | `scripts/p2m_api.py:16`/`:53`、`:22` | 显式补 `import urllib.error`、删 `_CTX` | scripts-config-audit §2.3 |
| Q24 | 低 | `optimize_rosser_timeout.py` 相对路径、硬编码魔数 `87`、模块级直接执行 | `scripts/optimize_rosser_timeout.py:9,17`；`write_magic_batch4_solutions.py:208`；`generate_rosser_prefix.py` | 加 `__main__` 保护、参数化根路径 | scripts-config-audit §2.7 |
| Q25 | 低 | 脚本重复逻辑：`api()` ×8 处、`ROOT/PY/API` 前导 ×10 处、矩阵 LaTeX ×5 处（漂移风险） | scripts-config-audit §3.1–§3.4 各文件 | 抽公共模块；LaTeX/引用抽常量（一次性脚本可放宽） | scripts-config-audit §3 |
| Q26 | 低 | `.gitattributes` 把 `scripts/**` 也标 `-text`，属过宽 | `.gitattributes:2-7` | 评估移除 `scripts/**` 的 `-text` 或加注理由 | scripts-config-audit §5.3(e) |
| Q27 | 低 | `.gitignore` 失效/冗余规则 3 条 | `.gitignore:7 lakefile.olean`、`:13 .DS_Store`、`:31 failed-recursion-*.lean` | 删除失效规则（`*.olean` 建议留作防御） | scripts-config-audit §5.3(a)；vcs-hygiene-audit §2.2 |
| Q28 | 低 | 43 个 `.log` 仍被跟踪（22 个命中规则 + 21 个在更深层未被规则覆盖） | `missions/*/verification/*.log`（22）；`missions/euler-gamma/sondow/**/*.log`（21） | `git rm --cached` 脱管 + 放宽规则（§6 可逆项） | vcs-hygiene-audit §1(B)/(B')；scripts-config-audit §5.3(b) |
| Q29 | 低 | 文档层不一致（多小项）：根 `status.md` mission index 缺 II/III/γ 行；Five Primes frontier 数字冲突；`README.md` Layout 缺 `missions/` 等；`referpaper/` 编目 11 篇而实际 12 PDF；`item-tmp/milestone-tmp.json` 残留磁盘；Mission I expl 覆盖不全；Mission II/III status 与 proposal 状态过期；Mission III expl 命名不符约定 | `status.md:15-20`；`README.md:18-26`；`referpaper/README.md`；`missions/{magic-squares,semi-magic,normal3}/status.md` | 按 docs-consistency-audit §1/§2.3/§5.2/§6 逐条修正 | docs-consistency-audit §1.3/§1.4/§2.3/§5.2/§6（P2-1…P2-7） |

### 3.1 冲突与口径说明（应 Leader/用户裁决的地方）

- **冲突 C1（Q2 vs Q10）**：lean-code-audit §1.1 把「doc 声称 Proved、实体为 `by sorry`」列为 **高**；docs-consistency-audit §5 明确「`Theorems/` 镜像一律 `by sorry` 是**设计约定**（`MEMORY.md:36-37`），**不是**『声明已证明却用 sorry 占位』，请勿误判」。**二者口径不同、并不直接矛盾**：docs 否定的是「Solutions 里用 sorry 冒充证明」（确实不存在，`Solutions/` 0 处 sorry）；lean 指出的是「**镜像文件内**的 doc 注释声称 now Proved 而文件体是 sorry，会误导只读 Theorems/ 的读者」。**处理**：保留为两条——Q10（镜像整体占位，中，设计约定）+ Q2（那两个文件 doc 措辞误导，高，**待裁决是否修正 doc**）。
- **口径 C2（Solutions/ `.lean` 计数）**：lean-code-audit §0 记 `Solutions/` **83** 个 `.lean`；inventory §1.1 与 scripts-config-audit §5.1 记 **92** 个、`git ls-files Solutions` 记 **93** 个跟踪文件。三者口径不同（是否含 `Sondow*.lean` / `.json` / `SmokeTest`）。**标注为「待复核」**，建议以 `git ls-files 'Solutions/*.lean' | wc -l` 重新核对，不并入总表。
- **口径 C3（「被忽略却跟踪」计数）**：scripts-config-audit §5.3(b) 记 **26** 个（4 `.lean` + 22 `.log`，即严格「命中规则却仍被跟踪」者）；vcs-hygiene-audit §1 另发现 **21** 个更深层日志（B'，未被任何规则覆盖）与 **9** 个配套 `.json`。**不矛盾，属范围差异**：规则命中 26 个 + 同类未覆盖 30 个 = 待处置候选 56 个（4 `.lean` + 9 `.json` + 43 `.log`）。
- **口径 C4（`.git` 成因）**：inventory §3.6 仅**推断**历史留存大文件；vcs-hygiene-audit §3 用对象级命令**确证**并给出构成。以 vcs 为准。
- **待确认（需平台/联网，离线无法定论）**：见 §3.2。

### 3.2 待确认项（离线无法核实，单列不入严重度排序）

| 编号 | 事项 | 冲突证据 | 来源 |
|---|---|---|---|
| TBD-1 | Five Primes frontier 节点/Open 数 | `status.md:18`（13 leaves, 2026-09-12）vs `project-review-2026-09-17.md:32`（50/28）vs `memory/2026-09-16.md:7`（131/68）vs `memory/2026-09-15.md:33`（15） | docs-consistency-audit §1.4、§6 |
| TBD-2 | 平台真实版本号（0.10.3 vs 0.10.4） | `SKILL.md:5`=0.10.3 vs 三篇幻方文档=0.10.4 | docs-consistency-audit §2.1、§6 |
| TBD-3 | Mission II milestone 数量（5 vs 4） | `semi-magic/status.md:124`=5 vs `memory/2026-09-17.md:66`=4 | docs-consistency-audit §5.2d、§6 |
| TBD-4 | `project-review-2026-09-17.md` §1.1 平台侧各 mission 节点数 | 离线无法复核 | docs-consistency-audit §4.1、§6 |

---

## 4. 仓库现状基线

体量一句话：全仓（排除 `.git`）**142557 个文件**，其中**自有文件 1431 个**、构建缓存 `.lake/` 占 **141126 个文件 / 8.4 GB**；`.git/` **146 MB**；当前**跟踪文件 1033 个 / 21.48 MB**。（来源：survey/inventory §2.1、§3.6；docs-consistency-audit 附录 A）

补充基线（供决策参考）：`.lake/build` 432 MB、`.lake/packages` 7.7 GB、`.lake/mathlib-download-incomplete` 295 MB（inventory §2.5）；自有工作树最大文件 `missions/euler-gamma/research/variable-order-results.json` = **3,342,812 B ≈ 3.34 MB**，也是全仓唯一 >1 MB 的**跟踪**文件（vcs-hygiene-audit §1(C)、inventory §2.4）。

---

## 5. 分类发现（每类只留可执行结论）

### 5.1 构建与编译
- **`lake build` 当前失败**（阻断）：唯一根因是 `Solutions/Sol_vinogradov_lemma_if_form_coprime.lean:3` 悬空 import；抽样 8 个文件 7 通过（Q1）。
- 抽样编译印证：`Theorems/` 占位是**警告**（`declaration uses 'sorry'`）而非错误（lean-code-audit §5 #7）。
- 环境一致：`lean-toolchain` / `lakefile.lean` / `lake-manifest.json` 三处 mathlib rev `0df444a…` 与 `prove.md`、8 个 `submit_*.ps1` 的校验值**完全一致** ✅（scripts-config-audit §4.3、§5.2）。
- 构建耗时不可控：`maxHeartbeats 0` 等 4 处（Q12）。

### 5.2 代码与结构
- `Solutions/` 无 `sorry`、无 `axiom`、无 `native_decide`（`decide` 仅集中在生成证书）（lean-code-audit §1、§4.4）。
- `Theorems/` 45/50 为占位镜像（设计约定，但 2 个文件的 doc 措辞误导）（Q2、Q10）。
- `Theorems/` 与 `Solutions/` 三组证明整段重复 + 1 处命名泄漏（Q13）。
- 3 个库内模块无人 import（Q14）；`Solutions/` 依赖未声明的 `examples/`（Q11）。

### 5.3 脚本与配置
- 40 个脚本中**仅 `p2m_api.py` 属基础设施**，其余 39 个均为已完成使命的一次性脚本，建议整体归档（不删除）（scripts-config-audit §1、§6.1）。
- 4 处硬编码绝对路径使部分脚本跨机不可运行（Q6）。
- `p2m_api.py` token 过期字段与文档不符（Q15）；8 个 `submit_*.ps1` 无 token 刷新重试（Q16）。
- `lakefile.lean` / `lean-toolchain` / `lake-manifest.json` 与文档一致，**无需修改** ✅（scripts-config-audit §5.1/§5.2）。
- `.gitignore` 覆盖过窄 + 3 条失效规则（Q8、Q27）；`.gitattributes` 对 `scripts/**` 过宽（Q26）。

### 5.4 文档与记录
- 根 `status.md` 严重漂移（active mission、mission index、magic-squares 数字）（Q3、Q29）。
- 三篇幻方文档平台版本 v0.10.4 与权威 v0.10.3 矛盾（Q17）。
- 跟踪计数 `1032/22.5MB` 过期（Q18）；`README.md` 对 `scripts/` 描述与实际不符、Layout 缺漏（Q19、Q29）。
- 5 个已删大生成物的「在磁盘上」摘要未同步（Q4）。
- Mission I/II/III 核心产物本身**自洽**：`Solutions/`、`Definitions/` 齐备无 `sorry`，文档与 `proposal_items.json` 命名一致 ✅；问题集中在**文档层**（Q29）。

### 5.5 版本控制与仓库体积
- 当前树干净，`credentials.json` 未跟踪且被忽略 ✅（vcs-hygiene-audit §5）。
- 待脱管候选：4 证书 `.lean` + 9 `.json` + 43 `.log` +（待确认）3 诊断 `.lean`（Q7、Q9、Q28）。
- `.git` 146 MB 主因历史 blob + 138.2 MiB 松散对象/garbage；pack 仅 2.60 MiB（Q5）。
- `c2bbb0e` 只做了当前树脱管，**blob 仍在历史、`.git` 未变小**（vcs-hygiene-audit §4 关键点）。
- `origin/main` 仍持有大 blob；远端未 fetch，最新状态未核实（vcs-hygiene-audit §3.1⑥、§4）。

---

## 6. 待裁决事项（重点）

> 凡涉及**删除、脱管（`git rm --cached`）、重写 Git 历史、force push、修改文档、修改配置**的条目，全部集中于此，按可逆性分组。**授权状态：全部为「待用户确认」**——本报告只给建议、不执行任何动作。分级口径：**可逆** = 不产生历史变更、可原样回退；**半不可逆** = 产生新提交/重打包（历史仍在，可 revert）；**不可逆** = 重写历史 SHA / force push / 丢失无 git 记录的本地文件（依据 vcs-hygiene-audit §6）。

### 6.1 可逆（建议优先，满足授权即可执行）

| # | 事项 | 命令/动作（原文） | 授权状态 | 来源 |
|---|---|---|---|---|
| R1 | 修复阻断：二选一 | A 新增镜像 `.lean`；或 B 删 `Solutions/...coprime.lean:3` import 及 `:20` 调用 | 待用户确认 | lean-code-audit §4.1 |
| R2 | 脱管 4 个生成证书 | `git rm --cached Solutions/SondowRosserMiddle{Tree10000,10000,Hex10000,Tree10000Compact}.lean` | 待用户确认 | vcs-hygiene-audit §1(A-1) |
| R3 | 脱管 9 个配套 `.json` | `git rm --cached` 9 个 `Solutions/SondowRosserMiddle*.json` | 待用户确认 | vcs-hygiene-audit §1(A-2) |
| R4 | 脱管 22 个 verification 日志 | `git rm --cached $(git ls-files 'missions/*/verification/*.log')` | 待用户确认 | vcs-hygiene-audit §1(B) |
| R5 | 脱管 21 个 sondow 深层日志 | `git rm --cached $(git ls-files 'missions/euler-gamma/sondow/**/*.log')` | 待用户确认 | vcs-hygiene-audit §1(B') |
| R6 | 脱管 3 个生成诊断 `.lean` | `git rm --cached .../balanced-largest-block-{cbv,kernel,diagnostic}.lean` | 待用户确认 | vcs-hygiene-audit §1(C-1)；lean-code-audit §6 |
| R7 | 修订 `.gitignore`（放宽 + 新增 3 类） | 按 vcs-hygiene-audit §2.3 diff（`missions/**/*.log`、`missions/**/item-tmp.json`、`Solutions/SondowRosserMiddle*.json`、`balanced-largest-block-*.lean`） | 待用户确认 | vcs-hygiene-audit §2.3；scripts-config-audit §6.2 |
| R8 | 修正文档漂移 | 按 docs-consistency-audit §1/§2/§3/§5.2/§6 的替换文本改 `status.md`、`MEMORY.md`、`README.md`、三篇幻方 `status.md`、`project-review-2026-09-17.md`；Mission III `expl-*.md` 重命名 | 待用户确认 | docs-consistency-audit §6 |
| R9 | 修脚本死代码/文案/硬编码路径 | 见 Q6、Q15、Q22、Q23、Q24 | 待用户确认 | scripts-config-audit §6.1 |

### 6.2 半不可逆

| # | 事项 | 命令/动作 | 授权状态 | 来源 |
|---|---|---|---|---|
| S1 | 提交上述脱管 + 忽略改动 | `git add .gitignore && git commit` | 待用户确认 | vcs-hygiene-audit §6(#7) |
| S2 | 回收松散对象/garbage | `git gc --prune=now`（预计回收数十 MB；会重打包并按 grace 期清理不可达对象） | 待用户确认 | vcs-hygiene-audit §6(#8) |
| S3 | 删除归档 tag（若确认不需要） | `git tag -d archive/qpr-upload-run`（该 tag 持有 `port/*.jsonl` ≈10.6 MB） | 待用户确认 | vcs-hygiene-audit §3.2、§6(#9) |

### 6.3 不可逆

| # | 事项 | 命令/动作 | 授权状态 | 来源 |
|---|---|---|---|---|
| N1 | 历史瘦身（回收 ≈200 MB） | `git filter-repo --invert-paths --path …` 后 `git push --force-with-lease origin main` | 待用户确认 | vcs-hygiene-audit §3.3、§6(#10) |
| N2 | 清理 `tmp/` 磁盘文件 | `rm -rf tmp/`（本地不可逆，对仓库零影响） | 待用户确认 | vcs-hygiene-audit §5、§6(#11) |
| N3 | 入库凭证类文件 | `git add -f credentials.json` 等 | **禁止**（安全事故） | vcs-hygiene-audit §6(#12) |

### 6.4 特别注明（N1 的关键前提）

- `.git` 146 MB 的**主因是历史中仍可达的生成证书 blob**（`SondowRosserMiddle*1000000*.lean` 等 5 个，未压缩 ≈199.7 MB），而 `origin/main` **仍持有这些 blob**（`git cat-file -e 1b30762:<path>` 逐一验证为 IN）——因此**历史重写必然要 force push**，否则远端体积不会下降（vcs-hygiene-audit §3.1⑥/§3.3）。
- `c2bbb0e`（"Slim the repo…"）**只做了当前树脱管**（`git rm --cached`），那些 blob **仍在历史中**，所以 **`.git` 并未变小**（`git count-objects` 显示 pack 仍 2.6 MiB、松散对象反而达 138 MiB）（vcs-hygiene-audit §3.3、§4）。
- N1 执行前前提：`git clone --mirror` 完整离线备份、暂停提交、通知所有克隆者、先 `git fetch --all --tags --prune` 复核远端（vcs-hygiene-audit §3.3）。

---

## 7. 遗留建议与后续优先级

**第一优先（无争议、低风险、可逆）**
1. 修复 Q1 阻断——`lake build` 是仓库的第一可用性指标，建议先按修法 A 恢复（R1）。
2. 执行 R9 中「纯改错」项（错误文案、docstring、死代码），不涉及历史。

**第二优先（需一次性授权，收益明确）**
3. 采纳 R2–R7：补 `.gitignore` + 批量 `git rm --cached` 全部候选（56 个文件），**立刻止住「生成物继续入库」**；此批可逆，是性价比最高的清理（vcs-hygiene-audit §0）。
4. 采纳 R8：文档同步（尤其 `status.md` active mission、平台版本 0.10.4→0.10.3、`MEMORY.md` 的「文件仍在磁盘」摘要），避免继续误导下一步决策。

**第三优先（高风险，需专门评估与授权）**
5. S2（`git gc`）可回收数十 MB，半不可逆，建议单独确认后执行。
6. N1（`filter-repo` + force push）是**唯一**能真正回收 ≈200 MB 历史体积的手段，但不可逆且影响远端/其他克隆者，**建议暂缓**，待用户明确同意并完成 mirror 备份与冻结后另行处理。
7. N2（清 `tmp/`）对仓库零影响，纯本地磁盘收益，可与其他动作解耦。

**清理顺序建议（来自 vcs-hygiene-audit §6）**：先 1–7（可逆/半不可逆）→ 视需要 8（gc）→ 10（filter-repo）与 9（删 tag）作为高风险项另行请示。

---

## 8. 附录

### 8.1 审查方法
- 五份输入产物均为**只读审查**：未修改/新建/删除项目文件；未做 git 写操作（vcs-auditor 全程只读，未 fetch）；script-auditor 未执行任何脚本、未联网；docs-auditor 未联网；lean-auditor 仅以 `lake env lean` / `lake build <module>` 抽样编译（单次 ≤180 秒）。
- 本汇总报告**只做合并、去重、重排、消歧、成稿**，未重新审查代码库，未执行任何清理。
- 各成员产出格式：inventory 为事实清单；lean/scripts 为「路径/行号 + 证据 + 严重度」；docs 为「原文片段 + 事实 + 建议修正」三段式；vcs 为「清单 + 命令原文 + 风险分级」。

### 8.2 关键命令（可复查，摘自各产物）
```bash
# 现状与体量
Get-ChildItem -Recurse -File -Force | 排除 .git      # 142557
du -sh .git        # 146M
du -sh .lake       # 8.4G
git ls-tree -r --name-only HEAD | wc -l              # 1033
git ls-tree -r -l HEAD | awk '{s+=$4} END{print s/1048576" MB"}'   # 21.48 MB
# 构建（lean-auditor 抽样）
lake env lean Solutions/Sol_vinogradov_lemma_if_form_coprime.lean  # EXIT=1（Q1）
lake build Solutions.Sol_vinogradov_lemma_if_form_coprime          # build failed（Q1）
# 版本控制卫生
git count-objects -vH                                # pack 2.60 MiB / garbage 37.08 MiB
git rev-list --objects --all | git cat-file --batch-check='%(objecttype) %(objectname) %(objectsize) %(rest)'  # 历史大 blob
git cat-file -e 1b30762:Solutions/SondowRosserMiddleTree1000000.lean  # IN origin/main
git ls-files -i -c --exclude-standard                # 被忽略却已跟踪
git status --ignored --short                         # !! credentials.json / !! tmp/ / !!
```

### 8.3 未覆盖范围（汇总各产物自报的未验证项）
- **未做全量 `lake build`**（≈8700 任务）：除 lean-auditor 抽样的 8 个文件外，「其余文件当前是否可编译」未验证；但 Q1 已足够证明**默认目标整体失败**（lean-code-audit §8.1/§8.2）。
- **未联网/未 fetch**：平台节点数、proposal 状态、平台真实版本号、`origin/main` 最新 SHA 均未核实，一律标「待确认」（docs-consistency-audit 附录 B；vcs-hygiene-audit §4；§3.2 TBD-1…4）。
- **`.git` 历史未逐条 rev-list**（inventory §7.3）；**`.lake/` 内部未逐一核对**（§7.4）；**二进制内容未打开**（§7.5）；**`credentials.json` 内容未读取**（§7.6，刻意规避）。
- **`Theorems/` 45 个占位、`examples/` 157 个、`missions/**` Lean 文件未逐一编译**（lean-code-audit §8.2）；**Mathlib 镜像 sorry 仅统计 `Mathlib/Mathlib/` 一子树**（§8.3）。
- **`autoImplicit` 包级覆盖语义**建议与 script-auditor 交叉确认（lean-code-audit §8.4；本次未见 scripts 报告对此结论，标**未验证**）。
- **未评估数学正确性**：命题真假与证明有效性不在本次范围（lean-code-audit §8.7）。
- **时间戳口径不完全统一**：部分为 git 提交时间、部分为文件系统 mtime（inventory §7.7）。

### 8.4 各成员严重度到统一口径的映射规则
统一口径：**阻断 > 高 > 中 > 低**。

| 来源产物 | 原始分级体系 | 映射规则 |
|---|---|---|
| lean-code-audit | 阻断 / 高 / 中 / 低 | **直接对应**（同口径）：阻断→阻断，高→高，中→中，低→低 |
| scripts-config-audit | 阻断 / 高 / 中 / 低（定义：阻断=使任务/交付失败；高=明确缺陷；中=有触发条件的健壮性缺陷；低=风格/死代码） | **直接对应**（同口径） |
| docs-consistency-audit | 过期 / 错误 / 矛盾 / 缺漏 / 待确认，并附 P0/P1/P2 优先级 | **P0→高**（定义「会误导下一步决策」，但属文档层、不阻断构建）；**P1→中**（事实/版本错误）；**P2→低**（缺漏/格式）；**「待确认」不进入严重度排序**，单列 §3.2 |
| vcs-hygiene-audit | 高 / 中 / 低 + 可逆/半不可逆/不可逆 风险分级 | 严重度：**高→高、中→中、低→低**；**可逆性分级不映射为严重度**，原样用于 §6 待裁决分组 |

> 说明：docs 的 P0 未映射为「阻断」，因为其影响对象是「决策误导」而非「构建/交付失败」，不符合阻断定义；vcs 的风险分级（可逆性）与严重度是**两个正交维度**，本报告分别使用。

---

*本报告为汇总撰稿产物，只读五份输入、只写本文件，未改动项目任何源码/配置，未执行任何清理动作。*

---

## 9. 本轮处置结果（2026-09-17 晚）

按第 6 节「可逆 → 半不可逆 → 不可逆」的顺序执行了建议项。批次三（`git gc`、
删归档 tag、`filter-repo` + force push）与推送**均未执行**，仍待宇轩点头。

### 9.1 Q1 阻断：不是「一个悬空 import」这么简单

报告 §2 把 `lake build` 失败归因为 `Sol_vinogradov_lemma_if_form_coprime.lean:3`
那一个悬空 import，并按修法 A 补齐了镜像。但补齐之后 `lake build` **照样失败**，
所以真正的成因不止一层：

1. **确实存在的那层**：模块 `Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block`
   从未被建过（git 历史里也查无此文件，不是 `c2bbb0e` 删的 —— 它从来就没提交过）。
   已按仓库约定补为 `by sorry` 占位镜像，陈述取自平台节点快照
   `tmp/five-primes-all-theorems.json`（id `90cf0471`，平台侧 `Proved`）。
   补上后 `lake build Solutions.Sol_vinogradov_lemma_if_form_coprime` 通过。
2. **真正的系统性那层**（原报告没发现）：Lake 的 **library target 需要根模块文件**。
   `lean_lib «Solutions»` 会把 `Solutions` 当成一个**模块**去找 `Solutions.lean`，
   仓库里没有这个文件，于是 `Definitions` / `Theorems` / `Solutions` **三个库目标
   全部**在 job computation 阶段死于 some modules have bad imports，一个任务都不跑。
   之所以从没被发现：日常只用 `lake env lean <file>` 和 `lake build <模块名>`，
   这两个入口绕开了库级解析。
   **修法**：每个 lib 显式写 `roots := #[]` + `globs := #[.submodules \`X]`。
   改完后 `lake build` 正常展开 8781 个任务开始编译。
   （最小复现已验证：`lean_lib Toy` + 目录 `Toy/A.lean` 但无 `Toy.lean` →
   同样报错；补空 `Toy.lean` 或改用 globs 都能好。）

⚠️ 由此派生两个发现：
- **`lakefile.lean` / `lean-toolchain` / `lake-manifest.json` 都被 `.gitignore`
  忽略且未被跟踪**，所以这次构建配置的修改**不会进 commit**，克隆下来也拿不到
  构建配置。是否要用 `git add -f` 纳入版本控制，需要宇轩定夺（当前注释写的是
  "agent-local, environment-specific"，看着像有意为之）。
- `import examples.…` 这类未注册模块的依赖虽然在单模块编译时能过，但
  `lake build <源文件路径>` 会报 unknown module source path，属脆弱依赖（Q11）。
  已在 lakefile 里把 `RosserLcmBlocks` 显式声明为 lib（非默认目标）。

### 9.2 已执行清单

| # | 项目 | 动作 | 可逆性 |
|---|---|---|---|
| R1 | Q1 阻断 | 新增 `Theorems/Thm_TaoFivePrimes_vinogradov_lemma_if_form_from_block.lean`（占位镜像，doc 已注明「并非本地已证」）；改 `lakefile.lean` 三个 lib 的 `roots`/`globs` | 可逆 |
| Q2 | 镜像 doc 误导 | `Thm_MagicSquares_sm3_canonical.lean`、`sm3_params_card.lean` 的 doc 改写：明确「平台侧 Proved、本地仅为 `by sorry` 的陈述镜像」，并指向真实证明位置 | 可逆 |
| Q3 | `status.md` 漂移 | Current work / mission index 重写（补 II、III、γ 三行，I/II/III 标 Complete）；幻方一节的「还剩 1 个 Open child」改为「已收官」，并同步 II/III | 可逆 |
| Q4 | 大生成物「仍在磁盘」摘要 | `.workbuddy/memory/MEMORY.md`、`missions/project-review-2026-09-17.md` 改为「19:10 已物理删除，释放 199.7 MB；因当时已 untrack 故不产生 commit」 | 可逆 |
| Q6 | 脚本硬编码路径 | `submit_magic_batch2.py`、`gen_magic_batch3.py` 改用 `sys.executable`；`check_theorem51_progress.ps1` 改为从 `lean-toolchain` 推导 lake.exe（照抄 `check_grouping.ps1:8-10` 的写法） | 可逆 |
| Q7/Q9/Q28 | 生成物入库 | 先 `git rm --cached` 共 **59** 个文件（13 个 `SondowRosserMiddle*.{lean,json}` + 3 个 `balanced-largest-block-*.lean` + 43 个 `.log`），**磁盘文件全部保留**；**当晚 23:37 按宇轩决定全部 `git add -f` 加回**（见 §9.5），当前索引恢复为 1033 个文件 | 可逆 |
| Q8/Q27 | `.gitignore` | `missions/*/…` 放宽为 `missions/**/…`；补 `Solutions/SondowRosserMiddle*.json`、`balanced-largest-block-*.lean`、`__pycache__/`；删冗余的 `lakefile.olean` | 可逆 |
| Q15/Q23 | `p2m_api.py` | `expires_at` 优先、`expires_in` 回退；补 `import urllib.error`、删未用的 `ssl`/`_CTX` | 可逆 |
| Q17 | 平台版本号 | 三篇幻方 `status.md` 的 v0.10.4 → **v0.10.3**（与 `SKILL.md` 一致）。仍属 TBD-2：未经平台侧核实 | 可逆 |
| Q18 | 跟踪计数 | 文档里的 1032 / 22.5 MB 改为实测 **974 / 18.1 MB**（第二轮脱管后） | 可逆 |
| Q19/Q29 | `README.md` | Layout 树补 `status.md` / `missions/` / `referpaper/`，修正 `scripts/` 描述，说明 `Theorems/` 是陈述镜像且三个目录才是 lean_lib | 可逆 |
| Q22 | 脚本文案与死代码 | `submit_typeII_scale_reduction.ps1:37` 的 `'Type I must be a complete proof'`（从 `submit_theorem51_reduction.ps1` 复制粘贴来的，那里 `$Part` 是 `'typeI'`）→ `'Scale leaf must be a complete proof'`；删 `gen_magic_batch4.py` 的 `subprocess`/`sys`/`PY`、`write_magic_batch4_solutions.py` 的 `subprocess`/`LEANY` | 可逆 |

### 9.3 构建验证（2026-09-17 22:50 收尾）

`lake build` 全量最终 **EXIT=0，8859 jobs，0 errors**。

过程中发现一个环境级问题（非代码问题）：全量并行构建（8781 任务）在本机会随机
挑 ~20–35 个模块报 `failed to read file '...olean[.private]'`，出错文件横跨 elan
工具链与 mathlib 包、每次名单不同 ⇒ 并发 IO 竞争（杀软/索引器/执行层之一，未定位）。
**单模块串行构建 39/39 全部通过**，证明源码本身无问题。对策已验证：全量跑完导出
失败名单、串行逐个补编，最后重跑 `lake build` 即全绿。
（插曲：补编名单用 Python 重定向生成时带 CRLF，`while read` 读入的模块名尾巴带
`\r`，导致 `unknown target` —— `tr -d '\r'` 后正常。）

### 9.4 未做（需宇轩决定）

- 批次三：`git gc`、删 tag `archive/qpr-upload-run`、`filter-repo` + force push。
- 推送：本地仍领先 `origin/main`，未 `git push`。
- `tmp/`：378 个文件 4.9 MB，已忽略，未清理。
- Q11 的另一半（`Solutions/` 反向依赖 `examples/`）只做了「声明 lib」这一步，
  没有把 `RosserLcmBlocks` 真正迁出 `examples/`。
- Q12（`maxHeartbeats 0`）、Q13（Theorems/Solutions 重复）、Q14（孤立模块）、
  Q20/Q21（命名与风格）、Q25/Q26 等未动 —— 都是风格/重构层，收益不明确。
- ~~`lakefile.lean` 等三个构建配置文件是否 `git add -f` 入库。~~ → 已于 §9.5 决定并执行。

### 9.5 宇轩当晚的决定（23:37 执行）

1. **撤销脱管**：§9.2 里 Q7/Q9/Q28 那 59 个文件全部 `git add -f` 加回索引
   （`.gitignore` 里我加的放宽规则保留，但**已跟踪文件不受 ignore 影响**，所以
   这些文件继续被跟踪）。跟踪文件数 974 → **1033**。
2. **构建配置入库**：`lakefile.lean` / `lean-toolchain` / `lake-manifest.json`
   用 `git add -f` 纳入版本控制。⇒ 之前"克隆仓库拿不到构建配置、别人也会踩
   bad imports 坑"的问题不再存在；代价是这三个文件今后会跟着 commit 走。
3. **本批改动一次性 commit**（未拆分）。
