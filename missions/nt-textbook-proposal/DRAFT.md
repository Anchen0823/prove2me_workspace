# 初等数论 · Textbook 系列 mission 提案草案

> 状态：草稿。尚未创建任何平台 proposal。
> 依据：`references/mission_captain.md`（权威规则）+ 2026-09-18 平台实测。

---

## 1. 官方形式：`mission_type: "Textbook"`

平台把「已知结果 / 习题」的载体明确定义为 `mission_type` 三选一里的
**`Textbook`** —— 原话是 *"an exercise or known result"*（`mission_captain.md` L62）。

并且它规定这个形式**不是一个大 mission，而是一个系列**（L94–100），三条硬规则：

1. **只聚焦 capstone。** 每个 mission 打一个书中"奔着去"的结果，通常一章一个。
   支撑性定义与引理按需进入，**不做逐条转录**。
2. **命名 `{书名} {序号}: {capstone}`。** 序号不必跟书中章号一致，按最能组织材料的方式排。
   书名前缀让整个系列在领域里可识别、可排序。
3. **整本书共用一个 namespace**，而不是每个 mission 一个。

---

## 2. 平台上的活样板（实测，全部真实存在）

| 系列 | mission 数 | 实测状态 |
|---|---|---|
| `Textbook Rudin PMA I` … `XI` | 11 | 9 Proved / **2 Disproved** |
| `Textbook Algorithmic Game Theory I` … `V` | 5 | 5 Proved |
| `Textbook Hatcher Algebraic Topology I` … `III` | 3 | 3 Proved |
| `Textbook Primal-Dual Online Algorithms I` … `III` | 3 | 3 Proved |
| `Textbook Cannon–Floyd–Parry: … Thompson's group F` | 3 | 3 Proved |
| `Textbook An Introduction to Chaotic Dynamical Systems I` … `II` | 2 | Open |
| Bandit Algorithms（tag `textbook`） | — | ns = `BanditAlgorithm` |

**两点值得注意：**

- ⚠️ `Rudin PMA V: Differentiation` 和 `Rudin PMA VII: Sequences and Series of Functions`
  是 **Disproved** —— 有人提交的命题被平台证伪。教科书系列不等于绝对安全，statement 必须逐字对源。
- ✅ namespace 惯例得到印证：`Rudin.ch04_uniform_continuity`、`BanditAlgorithm.…` ——
  **书名级 namespace + 章节级声明名**。

---

## 3. 数论领域的空位（本草案的机会）

实测 `number-theory` + `arithmetic-geometry` 下 `mission_type == Textbook` 的只有 **2 个**：

- `Textbook Proofs from THE BOOK`（跨领域，组合/图论/数论）
- `Textbook Freiman's maximal Hall ray`

**没有任何成系列的初等数论教科书 mission。** 对比 Rudin 已开到第 XI 卷、AGT 开到第 V 卷 ——
这个位置是空的。

---

## 4. 拟定结构（**待定：需要先确定源书**）

```
{书名} I:   {capstone}          ← 第 1 个 mission
{书名} II:  {capstone}
{书名} III: {capstone}
...
共同 namespace: <BookNs>
```

章节划分**不能凭印象拍**，要按选定教材的目录与 capstone 走。
`mission_description` 按 `references/mission_description.md` 的七段式写：
Motivation / Setting / Target / Significance / Difficulty / Formalization scope / References。

---

## 5. 单条 item 长什么样

`POST /mission-proposals/<PROPOSAL_ID>/items`，body 与 `POST /submit-problem` 完全一致，
只是多一个 `kind`，且**上传时不校验**（本地编译好再传）。

```json
{
  "kind": "theorem",
  "theorem_name": "<BookNs>.ch01_sq_sub_one_dvd_24",
  "theorem_title": "The square of a prime $p \\ge 5$ is $1$ modulo $24$",
  "formal_statement": "namespace <BookNs>\ntheorem ch01_sq_sub_one_dvd_24 (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 24 ∣ p ^ 2 - 1 := by sorry\nend <BookNs>",
  "natural_language_statement": "## Statement\n\nLet $p$ be a prime with $p \\ge 5$. Then $24$ divides $p^2-1$.\n\n## Why the hypotheses are what they are\n\nThe bounds are sharp. For $p=2$ we have $p^2-1=3$, and $3 \\nmid 24$; for $p=3$ we have $p^2-1=8$, and $8 \\nmid 24$. The statement is therefore about primes **at least 5** …\n\n## Proof sketch\n\n$p$ is odd, so $p^2 \\equiv 1 \\pmod 8$. Since $3 \\nmid p$, reduction modulo $3$ …\n",
  "preamble": "import Mathlib",
  "source": "<书>, <版次>, <章>, <定理/习题号>, p. <页码>",
  "tags": ["number-theory", "elementary-number-theory", "textbook"],
  "readback": "<由独立盲审 sub-agent 写，自己不许写>",
  "readback_model": "<写 readback 的模型名>"
}
```

**要点：**

- `formal_statement` 必须以 `:= by sorry` 结尾。
- **`source` 不许编造**。必须落到「书 + 版次 + 章 + 定理号 + 页码」，
  captain 原则第一条就是 *"Get the source, 100%"*。页码要翻实体书/PDF 核对。
- `natural_language_statement` 要写成讲义/论文风格（Markdown + KaTeX），**不是 Lean dump**，
  且要讲清边界条件为什么不能丢 —— 平台反复强调这点。
- `readback` 由**独立 sub-agent** 盲写（只给 Lean 代码 + `mission_auditor.md`，
  不给自然语言陈述、不给 source、不给意图）。改了 statement 就要重跑。

---

## 6. 里程碑长什么样

实测 `Textbook Rudin PMA IV: Continuity`（9 条里程碑），单条真实结构：

```json
{
  "title": "Theorem 4.6 — continuity and punctured limits",
  "milestone_description": "Reconcile the two definitions Rudin gives — the limit through $E \\setminus \\{p\\}$ and continuity at $p$ — at limit points of the domain. The hypothesis that $p$ is a limit point cannot be dropped: at an isolated point every function is continuous while the punctured limit is vacuous.",
  "sort_order": 0,
  "completed": true,
  "theorem": { "theorem_name": "Rudin.ch04_continuity_iff_limit", "status": "Proved" }
}
```

**写法惯例：**

- `title` 格式 = `Theorem {源编号} — {一句短描述}`，**跟随源书自己的编号**。
- `milestone_description` 写的是「这条在做什么 + 边界条件为何必要」，
  **不是**把定理陈述抄一遍。
- 里程碑只能挂 **theorem**；**goal 和 definition 不能当里程碑**。
- 尚未有人证出来的里程碑，`theorem` 字段为 `null`。

---

## 7. 流程与分工（关键：有两步只有人类能做）

1. `POST /mission-proposals` 建提案 ---- **agent 可做**，任何人都有权限
2. `POST …/items` 逐条加 draft theorem / definition / reference ---- **agent 可做**
3. `PATCH …/{main_item_id, item_order}` 定 goal 与顺序 ---- **agent 可做**
4. `POST …/milestones` 铺里程碑 ---- **agent 可做**
5. 跑独立 sub-agent 写 readback 并回填 ---- **agent 可做**
6. **人类逐条确认 + 点 Submit Proposal** ---- ⚠️ **只有宇轩能做**
7. moderator 审核 → `Reviewed` → 上线

补充规则：

- 提案在 `Draft` 状态可任意改（包括 Lean statement）；**人类一点 Submit，所有 draft item
  立刻被编译并发布成不可变 theorem**，且**任何一条编译失败则整批提交失败**。
- 想跳过审核：建提案时 `"visibility": "private"` → 直接进 private mission，无 moderator，
  但**别人看不到、也无法贡献**，且名字仍占用量命名空间。
- 发布是**单向**的：公开之后无法再私有化。

---

## 8. 待定项（需要宇轩拍板）

- [ ] **源书**：选哪本？（决定 namespace、章节切分、source 格式）
- [ ] **规模**：先做 1 卷试水，还是一口气铺 3–5 卷？
- [ ] **公开 / 私有**：直接公开走审核，还是先 private 练手再 make public？

> 在此之前不创建任何平台上的 proposal。
