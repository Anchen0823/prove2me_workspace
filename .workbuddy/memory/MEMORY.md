# Project memory — prove2me_workspace

Lean 4 / Mathlib 打 prove2.me 众包形式化平台的工作区。细节一律写在
`missions/<slug>/status.md`，这里只放跨 mission 复用的硬规则和踩坑清单。

## 环境（本机 Windows）

- Bash 的 PATH 是坏的：**每条命令都要先**
  `export PATH="/usr/bin:/bin:/c/Windows/System32:/c/Windows:$PATH";`
  PowerShell 工具在此会话取不到输出，别用。
- Lean `leanprover/lean4:v4.33.1`（elan），Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`，已构建在 `.lake/`（约 8.4 GB，**绝不删**）。
- 单文件检查：`lake env lean <file>`；模块检查：`lake build <Module.Name>`；
  全部默认目标：`lake build`（**很慢**，100 来个自有模块合计 30–90 分钟）。
- ⚠️ **全量并行 `lake build` 在本机会随机失败 ~20–35 个模块**：
  `failed to read file '...olean[.private]'`，出错文件横跨 elan 工具链与
  mathlib 包、每次名单不同 ⇒ 并发 IO 竞争（AV/索引器/执行层之一，未定位）。
  单模块构建从不失败。对策：全量跑完导出失败名单**串行逐个补编**
  （脚本模式见 2026-09-17 日志「晚班」节）。
- `lakefile.lean` 给 `Definitions`/`Theorems`/`Solutions` 开了 `autoImplicit false`；
  `examples/` 不是 lean_lib，在那里跑 lean 是 autoImplicit ON。
  **提交前必须把证明挪进 `Solutions/` 再编译一遍。**
- ✅ **lakefile.lean / lean-toolchain / lake-manifest.json 自 `eaccd16` 起已被
  `git add -f` 纳入版本控制**（此前被 `.gitignore` 忽略、注释写 "agent-local"）。
  ⚠️ 它们仍在 `.gitignore` 规则里，所以**新增/改动这三个文件必须 `git add -f`**，
  否则 `git status` 里看不到、也进不了 commit。

## Prove2me 平台约定

- API 助手：`scripts/p2m_api.py`（`token|get|raw|post|patch|verify|patch-explain`）。
  凭据在 `credentials.json`，永不打印/提交。JSON body 传**文件**，别内联。
- `raw '<path>?a=b&c=d'`：**路径必须单引号**，否则 bash 吃掉 `&` 导致 404。
- 端点：problem 是 `/submit-problem`（**单数**，复数会返回 404 HTML）；
  definition 是 `/submit-definition`。两者都返回 `jobs[].job_id`，
  轮询 `/publish-jobs/<job_id>` 拿 id；提交轮询是 `GET /verify?submission_id=`。
  终态：`ACCEPTED` / `SKETCH_ACCEPTED` / `FAILED`。
- **发布顺序是硬依赖**：preamble 引用 `Definitions.Def_X` 时，`Def_X` 必须先到
  PUBLISHED，否则 `unknown import`。
- **入 DAG 靠 proposal items**：`POST /mission-proposals/<id>/items`
  （`{"kind":"reference","theorem_id":...}`）+ `PATCH` 设 `main_item_id`/`item_order`。
  提交时传 `mission_id` 不会让节点进图。
- **goal 节点不接受 milestone**；milestone 只挂支撑子目标。
- **自包含闸门**：本地 lake 能解析服务器上没有的模块。提交前核对 mission 节点清单，
  只 import 平台真正有的东西；没有的内联到 solution 文件里。
- 归约里 children 写成 `import Theorems.Thm_<名字里 . → _>`，且必须 sorry-free；
  孩子要先发布。Theorems/ 里的本地镜像一律 `by sorry`。
- **不要相信 `session-*.md`/`report-*.md` 里记的节点 id**，会漂移或被编造。重新拉实时列表。
- 写 deltas： `tmp/survey_missions.py`（全部 mission）、`tmp/scout_next_targets.py`
  （数值侦察候选目标，改文件里的 MISSIONS/target 即可）。

## Lean 踩坑清单（高频）

- **`∑ k in s, f k` 在本 Mathlib 版本不解析**，写 `∑ k ∈ s, f k`。
- `Finset.eq_empty_iff_forall_not_mem` 不存在 → 用 `Finset.not_nonempty_iff_eq_empty`。
- 用 `Finset.filter` + 命题谓词的 def 必须放 `noncomputable section`。
- **`Fin.cons` 是依赖类型版**，必须钉住类型族
  `Fin.cons (n := k) (α := fun _ => Fin (N+1)) x q`，否则元变量留到 ℕ 转换时炸。
  同理 `simp [Fin.cons_zero, Fin.cons_succ]` 会踩 → 用 `change` 让 definitional
  equality 展开。
- `change i + ∑ j : Fin k, ... = n` 解析会乱 → 加括号
  `change i + (∑ j : Fin k, ...) = n`。
- `Finset.single_le_sum` 被局部变量遮蔽时推断失败 → 显式 `s :=`、`f :=`。
- `Finset.sum_range_reflect f (n+1)` 给 `∑ j, f (n-j) = ∑ j, f j`，拆分递推直接用。
- `Finset.mem_filter.mp (by simpa [...] using h)` 常失败（simp 把 `< n+1` 归成 `≤ n`
  ，签名对不上）→ **先写一条显式类型的 `have h' : x ∈ (...).filter p := by simpa ...`**。
- **计数定理形如 `C(n+k-1,n)` 时把陈述写成「k+1 个部分」**，避开 `k-1` 的 Nat 截断减法。
- 新增 `Definitions/*.lean` 后必须先 `lake build Definitions.Def_X` 生成 olean。
- `omega` 对混着大字面量和 `/` 的 Nat 目标会 "maximum recursion depth" →
  拆成 `Nat.div_mul_le_self` / `calc` 显式步骤。**`omega` 原生支持 `min`**
  （`min a b = 0` 直接喂；定理名是 `Nat.min_eq_zero_iff`）。
- **`Square n α` = `Matrix (Fin n) (Fin n) α`**。造具体方阵用嵌套向量
  `![![a,b,c],![d,e,f],![g,h,i]]`；`!![a,b,c]` 是单行矩阵，类型不对。
- `ext i j` 对 `Square` 会展开到 Nat 值相等，**其后不要再加 `apply Fin.ext`**。
  跨 `Fin (t+1)` 与 `ℕ` 用 `congrArg (fun x : Fin (t+1) => (x : ℕ))`。
- `ext` 处理 `Finset (ℕ × ℕ)` 时**先 `rcases` 拆配对**，否则 `rfl` 作用在 `ac.1` 上失败。
- **`simp` 不展开 `Fin n` 上的全称量词** → 显式 `Fin.forall_fin_succ` 剥到地面实例
  再 `norm_num`。（`Fin.forall_fin_three` 不存在。）
- 具体成员资格（如 `(2,4) ∈ paramSet 5`）用 `norm_num [paramSet, IsParam3]`；
  `simp` 只展开到 range/product/filter 就停住。
- **平台禁止 `native_decide`**（"trusts compiled native code"）→ 用 `norm_num [...]`/`decide`。
- **心跳上限 200000**：solution 顶部加 `set_option maxHeartbeats 0`；别用
  `dsimp [x] at h` 展开 let（很贵），改 `have hx_def : x = ... := rfl` 再交给 omega。
- **solution 文件的 `theorem solution` 必须在 namespace 之外**（顶层）：
  `namespace X` 放辅助 → `end X` → `open X` → `theorem solution`。放里面平台报
  `Unknown identifier solution`。移动时前面的 `/-- -/` doc comment 必须一起搬走，
  否则 `end` 报 "expected 'lemma'"。
- 平台对 tactic 冗余敏感：本地能过的 `rw ...; ring` 可能报 "No goals to be solved"
  → 用 `simpa [...]`。偶发 `Import parser timed out after 5s`，重提即可。
- 🔴 **Lake library target 必须有「根模块文件」**：写 `lean_lib «Solutions» where`
  时 Lake 会把名字当成一个**模块**去找 `Solutions.lean`。我们没有这个文件，
  于是 `lake build`（以及 `lake build Solutions`，三个 lib 全一样）在 job
  computation 阶段就报 `Solutions: some modules have bad imports`，**一个任务都
  不会跑**。而 `lake build Solutions.Sol_X`（指定到模块）一直能过 —— 所以这个坑
  长期没人发现，因为大家只跑模块级/单文件级命令。
  **修法**（已改）：显式给每个 lib 写
  `roots := #[]` + `globs := #[.submodules \`Solutions]`。
  另一种可行修法是补一个空的 `Solutions.lean`，但那样会让 `import Solutions`
  意外合法，不如前者干净。
- `import examples.…`（带连字符目录要用 `examples.«five-primes».X`）在未被声明为
  lib 时，`lake build <源文件路径>` 会报 unknown module source path；单个模块能
  编译不代表它是注册过的 Lake 模块。真要用就把那个模块声明成 lib（已在 lakefile
  里为 `RosserLcmBlocks` 做了）。
- **`lake script`/lake 诊断时别用 `timeout` 掐它**：超时会 SIGTERM 掉正在编译的
  lean 子进程，报 "Lean exited with code 143"，看起来像编译错。

## 各 mission 状态指针

| mission | slug | 状态 |
|---|---|---|
| Magic Squares I（$M_3$ 计数） | `magic-squares` | goal Proved，proposal Reviewed |
| Magic Squares II（$H_3$ 半幻方） | `semi-magic` | goal Proved，proposal Reviewed |
| Magic Squares III（洛书唯一性） | `normal3` | goal Proved，proposal In review |
| Every Odd Number … Five Primes | `five-primes` | Open；50 节点 / 28 Open（含 2 个 Disproved），2026-09-17 实测 |
| Weak Goldbach | `weak-goldbach` | 目标 Open，已归约到一个筛覆盖孩子 |
| Bunkbed is False | `bunkbed` | 全部封版归档 |
| Irrationality of Euler's γ | `euler-gamma` | 部分 Proved，见 `sondow/INTEGRAL-IDENTITY-COMPLETE.md` |

## 仓库卫生（两轮瘦身，2026-09-17）

- **第一轮 `c2bbb0e`**：只做 `git rm --cached`，当前树脱管了 5 个大证书；
  blob 仍在历史里，`.git` 一点没变小。
- **第二轮（同一天）**：又脱管 59 个文件（13 个 `SondowRosserMiddle*.{lean,json}`、
  3 个 `balanced-largest-block-*.lean`、43 个 `.log`），**磁盘文件全部保留**。
  现在 **974 个跟踪文件 / 索引树 18.1 MB**（第一轮后是 1033 / 21.5 MB）。
- 5 个大生成证书已于 2026-09-17 19:10 **从磁盘物理删除**（释放 199.7 MB）。
  因为文件当时已 untrack，物理删除**不产生 commit**，git log 里看不到；
  来源信息留档在 `missions/euler-gamma/sondow/ROSSER-FINITE-CERTIFICATES.md`。
- `.gitignore` 覆盖已放宽为 `missions/**/*.log`、`missions/**/item-tmp.json`、
  `missions/**/milestone-tmp.json`，并新增
  `Solutions/SondowRosserMiddle*.json`、`balanced-largest-block-*.lean`。
  **新生成的证书产物一律写进 `tmp/`。**
- `.gitignore` 已加：
  `Solutions/SondowRosserMiddle*.lean`、
  `missions/euler-gamma/sondow/continuation/failed-recursion-*.lean`、
  `missions/*/item-tmp.json`、`missions/*/milestone-tmp.json`、`tmp/`、
  `missions/*/verification/*.log`。**新生成的证书产物一律写进 `tmp/`。**
- 剩余最大单文件 3.3 MB（`missions/euler-gamma/research/variable-order-results.json`），
  健康，不用再管。
- ⚠️ `.git` 仍是 146 MB —— 那 196 MB 还在历史里。彻底瘦身必须
  `git filter-repo` + force push（**不可逆，须宇轩明确点头**）。
- ⚠️ **别用 Bash 删 `Solutions/` 里的文件！** 2026-09-17 实测：连续三次尝试
  （`git rm`、`rm -f`、关沙箱都试过）都导致**整个 `Solutions/` 目录从磁盘消失**，
  命令拿 SIGTERM、无输出。根因未定，不是沙箱问题。
  恢复：`rm -f .git/index.lock && git checkout HEAD -- .`（多跑一遍直到 status 干净）。
  要删文件请用资源管理器或 PowerShell。
- ⚠️ **同一条消息里并行发两个 Bash 调用，其中一个会被 SIGTERM 干掉、且无输出**
  （2026-09-17 复现三次，串行就正常）。上面的「Solutions 消失」很可能同源于此。
  要跑长命令就用 `run_in_background`，但**后台跑的时候也别再发第二条 Bash**。

## 工作习惯（已确立）

## 用户偏好

- 数学/Lean/文档写英文，给他的汇报写中文。Lean 教学不要拆太碎，给完整证明任务。
- **严格区分「我确认了」和「我推测」**——数值验证了不等于形式化证明了。
- 不可逆操作（rewrite history / force push / 删历史产物）**必须先问**，默认只做
  可逆的那一版。他说「先瘦身」时，安全版（只 `--cached`）就是他想要的那一步。
