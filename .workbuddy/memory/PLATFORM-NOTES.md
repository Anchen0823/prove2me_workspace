# prove2me 平台操作笔记

从 `MEMORY.md` 拆出（2026-09-19），因为它超限被截断。这里放 API 端点、成员资格、
draft 校验、盲审、两种提交模式的细节。MEMORY.md 只留索引。

## API 助手

- `scripts/p2m_api.py`（`token|get|raw|post|patch|verify|patch-explain`）；
  凭据 `credentials.json` 永不打印/提交；JSON body 传**文件**，别内联。
- `raw '<path>?a=b&c=d'` —— **路径必须单引号**，否则 bash 吃掉 `&` 得 404。
- `/submit-problem`（**单数**，复数返回 404 HTML）、`/submit-definition`
  → 返回 `jobs[].job_id`（definition 直接 `job_id`）；轮 `GET /publish-jobs/<job_id>` 到
  PUBLISHED；提交轮 `GET /verify?submission_id=`。终态 `ACCEPTED`/`SKETCH_ACCEPTED`/`FAILED`。
- ✅ **`GET /publish-jobs/<job_id>` 的终态记录里带 `theorem_id`**（2026-09-20 实测），
  不用再去搜索找节点 id。发布耗时 ~35 s（8 次轮询 × 5 s，PENDING → COMPILING×6 → PUBLISHED）。
- 🔴 **查提交结果用 `GET /submissions/<id>`（复数）或 `/verify?submission_id=`**；
  平台回话里写的 `GET /submission/{id}`（单数）实测 **404**。返回体里 `theorem_status` 是节点
  当前状态（ACCEPTED 时即 `Proved`）。
- ⚠️ **`python` 输出在管道/重定向下会缓冲**：轮询脚本里 `print` 不带 `-u` 就看不到中间进度，
  进程被 kill 时输出全丢 ⇒ **轮询脚本一律 `python -u`**，或把进度写文件。
- **发布顺序是硬依赖**：preamble 引用 `Definitions.Def_X` 时 `Def_X` 必须先 PUBLISHED，
  否则 `unknown import`。

## 入 DAG / 成员资格

- **入 DAG 靠 proposal items**：`POST /mission-proposals/<id>/items`
  `{"kind":"reference","theorem_id":…}` + PATCH 设 `main_item_id`/`item_order`。
  提交时传 `mission_id` **不会**让节点进图。
- **goal 节点不接受 milestone**（milestone 只挂支撑子目标）。
- `PATCH /mission-proposals/<id>` 是**部分更新**（只传 `description` 不会清 `main_item_id`）。
- **成员资格是 mission 侧的属性，节点记录里没有**：`GET /theorems/<id>` 的字段只有
  `theorem_id/name/title/status/preamble/formal_statement/natural_language_statement/source/
  tags/mathlib_rev/visibility/audit/vote_count/created_at/deprecated_*`。实测：Mission IV
  提案内的 `pan_three_card` 与完全在外的 `pandiagonal_count_three` 字段表**一模一样**。
- ✅ **正确读法：`proposal items ∪ milestones` 两个来源都要取**
  - `GET /mission-proposals/<id>`（**详情**端点）返回 `items`（按 `item_order`）——
    这是能用的那条。`/mission-proposals/<id>/items` 的 **GET 不返回 JSON**（只有 POST 用）。
  - `GET /missions/<id>/milestones` → 每个 milestone 带 `theorem.theorem_name`。
  - live mission：I `6d8463b5`、II `a030a222`、III `c9b6fe9e`、IV `df1cb8cc`、
    **V `e06131f8-1bf5-47c4-b8f4-507f107269e0`**（2026-09-19 21:1x 复核：提案 `3a8476fd` 已转
    `Reviewed` ⇒ 是 mission，不再是 proposal）；
    proposal：I `c66f86f5`、II `6ceb0b04`、III `98d3dea7`、IV `7af96e14`。
  - 转 live 的判据就是 `GET /mission-proposals/<id>` 的 `mission_id` 是否非 null（`status` 变为
    `Reviewed`）；**别拿 mission IV 的 `df1cb8cc` 当 V**。
  - **不可用**：`/missions/<id>`、`/missions/<id>/items`、`/missions/<id>/theorems`（都非 JSON）；
    `/theorems?mission_id=X` 只回极少几条（I/II/III = 9/8/3），**不是全表**。
  - 工具：`tmp/orphans.py`、`tmp/dag_members.py`、`tmp/reattach.py`。
- ✅ **挂定理的唯一可用写入路径**：`POST /missions/<id>/milestones`
  `{title, milestone_description, sort_order, theorem_id}` → 201。captain 文档明说链接
  `theorem_id` **即授予 membership**，且 unlink 也**不收回**（永久）。2026-09-19 一次挂回 18 条全 201。
  **定义没有 `theorem_id` ⇒ 挂不了**，只能用 proposal 的 `{"kind":"reference","theorem_id":…}` item。
- ✅ **milestone 的改 / 删走全局路径 `/milestones/<milestone_id>`**（2026-09-20 实测）：
  `OPTIONS` → `Allow: DELETE, OPTIONS, PATCH`；`GET` → **405**；`PUT` → 405。
  `PATCH` 收 `{title, milestone_description, sort_order, theorem_id}`（部分更新，200）；
  `PATCH` 传非法 body → `400 {"error":"Request body must be valid JSON"}`。
  错路径 `/missions/<mid>/milestones/<msid>` 是 **404**。
  ⇒ 改排位：`PATCH /milestones/<id> {sort_order: N}`，逐条按**倒序**挪（先挪大的）避免撞号。
- 🔴🔴 **探测端点时永远不要把 DELETE 放进循环**（2026-09-20 血的教训）：
  为了找 milestone 的更新端点，我用 `for m in (GET, PATCH, PUT, DELETE, OPTIONS)` 逐个打，
  `DELETE /milestones/<id>` 直接回 **204 并真删了** milestone `9e912298`（Mission V 的 H_4 档）。
  靠**事先**存下的 `tmp/msv-milestones.json` 快照才恢复（`POST` 重建，**id 会变**：
  `9e912298…` → `c791e322…`）。
  **规矩**：① 探端点只用 `GET`/`OPTIONS`；② 任何写操作前先把当前状态 dump 成 JSON；
  ③ `OPTIONS` 的 `Allow` 已经足够告诉你有哪些动词，不需要真的去试。
- ✅ **mission 讨论区评论**：`GET /missions/<id>/comments?limit=50&offset=0` → `{comments:[…]}`；
  `POST /missions/<id>/comments` body `{"body_md": …, "tags": []}` → 201（`tags` 可省）。
  记录里带 `is_agent: true`（区分是 agent 发的）。
- **`GET /missions` 里只有 proposal 被 `Reviewed` 的才是 mission**。
- 🔴 **核对节点状态一律按 id 查 `GET /theorems/<id>`，别信搜索**：2026-09-19 两次假阴性
  （带点的全名查不到；`q=semi_magic` 也一度返回 0 行）。
- **proposal 只能由宇轩在网页端 Submit**；我们能建 proposal / items / milestones。
  模板照抄：`scripts/create_normal3_mission.py` + `seed_normal3_mission.py`，
  最新一版 `create_magic_squares_iv_mission.py` / `seed_magic_squares_iv_mission.py`。

## 🔴 draft item 的 `formal_statement`：必须按平台方式单独编译

- 平台编译的是 **`preamble` + 空行 + `formal_statement`** 一个文件。
  `formal_statement` **必须自己开 `namespace`**：
  ```
  namespace MagicSquares

  theorem <name> ... := by
    sorry

  end MagicSquares
  ```
  本地 `examples/.../<file>.lean` 里写了 `namespace` **不会**跟着过去 —— 2026-09-19 六个
  draft 全因缺 namespace 报 `Invalid 'end': There is no current scope to end` + `Unknown constant`，
  而**本地编译源文件是通的**。
- ⇒ **校验对象是「拼装后的那个文件」，不是本地源文件**。工具：
  `tmp/verify_mission_v_items.py`（①拼装+编译 → ②PATCH → ③**从线上拉回来再编译**，不要只看 200）。
- 改 draft 项会**清掉人工确认**，所以先把陈述定死再让人审；改完要重跑盲审。

## 提交前的盲审（read-back）——规范要求，别跳

- proposal 的每个 draft theorem/definition **都该带 read-back**：由**独立子代理**盲写，
  只给它①声明代码 + 依赖的 preamble、②`references/mission_auditor.md`；
  **绝不能**给它 mission pitch、源论文、你自己的意图或带 doc comment 的文件
  （用正则 `/-.*?-/` 剥掉所有块注释再交给它）。
- 🔴 **改了 Lean 陈述必须重跑审读**——旧 read-back 在给旧文物作证，比没有更糟。
- 🔴 **它真的会抓到东西**：2026-09-19 抓到 `semi_magic_vanishing` 把 $p(-k)=0$ 写成 $p(k)=0$
  （正负号），修完重跑才过。**凡「声称器」类陈述都走这个流程。**

## 改 proposal 描述的坑

- 🔴 **别对 Markdown 列表做逐段替换**：`split('\n\n')` 会把**整个 bullet 列表当成一个段落**，
  替换时同级条目被静默删掉（2026-09-19 Timeline 掉 4 条、Formalization scope 掉 4 条，
  词数只掉 350 所以看着「正好」）。**改完必须把整篇打印出来重读**，
  并用结构性断言（关键年份 / 关键短语 / bullet 计数）。

## 提交模式 A：完整证明（单文件内联）

把本地 `examples/<mission>/` 模块按拓扑序拼进 `Solutions/Sol_*.lean`，只 import Mathlib +
平台 `Definitions.Def_*`。`import` 必须在文件最前，正文按 `namespace … end` 块拼
（重复开同名 namespace 合法），末尾 `end` + `open` + **顶层** `theorem solution`。
生成器范式：`tmp/assemble_dyadic_bundle.py`。终态 **ACCEPTED**；
2243 行 bundle 本地 108 s（平台上限 300 s，再大要裁剪）。

## 提交模式 B：sketch / 约简

写孩子镜像 `Theorems/Thm_<名字 . → _>.lean`（原文 + `by sorry`）
→ `lake build Theorems.<module>` → `/submit-problem` 轮 PUBLISHED → 约简文件
`import Theorems.Thm_<child>` ×N + 顶层 `theorem solution <与目标逐字一致的签名>`
→ `verify <id> <file> prove <explanation.md>` → 轮 `/verify`
→ `/decompositions` 确认登记、`/open-leaves` 确认 frontier。
**孩子必须先发布**；镜像里的 `sorry` 只影响本地，平台用真实模块。

## frontier / 图

- **真 frontier 用 `/theorems/<root_id>/open-leaves`**（五素数 root `59fb46ad`，2026-09-18 为 18 条）。
  `/theorems?mission_id=X&page=N` **无视 page**（每页固定同 50 条，累加会重复）；
  `/theorems/<id>/graph` 会截断（看 `has_more_children`）。
  工具：`tmp/frontier.py`、`tmp/decomps.py`、`tmp/show_nodes.py`、`tmp/graph_node.py`。
- 🔴 **约简类提交判 `SKETCH_ACCEPTED` 不等于失败**：平台按「孩子的 status」重估节点；
  import 的孩子还在 PENDING 时会给 SKETCH_ACCEPTED，等孩子全 Proved 后目标节点
  **自动升为 `Proved`**（2026-09-18 `special_three_count` 实测）。看到 SKETCH_ACCEPTED
  先等一会儿再查 `/theorems/<id>`，别急着重提。
- **不要相信 `session-*.md`/`report-*.md` 记的节点 id**（会漂移/被编造），重新拉实时列表。
