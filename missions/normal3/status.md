# Mission: normal3 — 三阶幻方的完整分类（洛书唯一性）

负责人：anche（徐宇轩） · 环境：Lean 4.33.1 / Mathlib `0df444a3` · 平台：prove2.me v0.10.4

创建：2026-09-17 · 最后更新：2026-09-17 15:35（两个节点全部 Proved）

## 0. 定位

这是幻方形式化的**第三个 mission**。前两个做的是**计数**：

- Mission I：$M_3(3e)=2e^2+2e+1$（幻方计数，6 个 milestone 全 Proved）
- Mission II：$H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$（半幻方计数，5 个节点全 Proved）

计数只说"有多少"，不说"长什么样"。本 mission 把 MacMahon 参数化反过来当
**分类工具**用，证明最经典的分类结果：

> 三阶正规幻方恰有 $8$ 个，即洛书在正方形对称群 $D_4$ 下唯一。

## 1. Proposal

- **id**：`98d3dea7-dd0d-4f0c-abb0-96f8f845b808`
- **名称**：*Magic Squares III: The Complete Classification of Order-Three Magic Squares*
- **类型**：`ResearchPaper` · **字段**：Combinatorics `55eec41b-ff24-45ad-96b6-49d7a6869286`
- 状态：`Draft`，待宇轩在网页端确认后 Submit
- 已挂 3 个 item（定义 + 2 个定理），goal 为 `magic_three_normal_eight`；
  goal 不挂 milestone，只有 1 个支撑 milestone

## 2. 已发布节点

### 定义

| 平台名 | 本地文件 | id |
|---|---|---|
| `MagicSquares` | `Definitions/Def_MagicSquares.lean` | `be2f2b6a-a540-47ae-b487-ac22532a2745`（mission I 已有） |
| `MagicSquaresParam3` | `Definitions/Def_MagicSquaresParam3.lean` | `68eaae9b-d759-4a2a-83f6-741ecdbca5f8`（mission I 已有） |
| `MagicSquaresNormal3` | `Definitions/Def_MagicSquaresNormal3.lean` | PUBLISHED |

`Def_MagicSquaresNormal3`：`normalParamSet e`（可行参数对中使 `mkMagic3 e a c`
正规的那个子集）、`normalParamCount e`。因为 `IsNormal` 含
`Function.Injective`、无 Decidable 实例，这个 `filter` 必须用 `classical`
才能构造，所以单独封装成一个定义模块。

### 定理（DAG）

| theorem_name | id | 状态 |
|---|---|---|
| `MagicSquares.magic_three_normal_classify` | `c677420b-bca2-41da-b9e3-f804919a1235` | **Proved**（submission `9c158b95`，ACCEPTED） |
| `MagicSquares.magic_three_normal_eight` | `15e75fbb-7830-416b-ac11-6471accdd4e9` | **Proved**（submission `16c4750a`，ACCEPTED）— GOAL 已达成 |

```
magic_three_normal_eight (GOAL)   : normalParamCount 5 = 8
└── magic_three_normal_classify   : IsNormal (mkMagic3 5 a c) ↔ (a,c) ∈ 八个对
```

## 3. 数学方案

### 3.1 参数化

线和为 $15$ 的三阶幻方都可写成（$e=5$，中心为 $5$）

$$
\mathrm{mkMagic3}(5,a,c)=
\begin{pmatrix}
a & 15-a-c & c\\
5+c-a & 5 & 5+a-c\\
10-c & a+c-5 & 10-a
\end{pmatrix},
\qquad (a,c)\in\mathrm{paramSet}\ 5 .
$$

正规 = 九格恰好是 $1,\dots,9$ 的一个排列。

### 3.2 分类结果（Python 已验证）

$\mathrm{paramSet}\ 5$ 共 $61$ 个可行对，其中使幻方正规的恰有 **8** 个：

$$(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)$$

它们正是洛书 $\begin{pmatrix}4&9&2\\3&5&7\\8&1&6\end{pmatrix}$ 的 8 个 $D_4$ 像
（Python 枚举验证 `orbit == normal list` 为 `True`）。

角元 $a,c$ 取自 $\{2,4,6,8\}$ 且互异、并且 $a+c\ne 10$；被排除的
$a+c=10$ 那四个，其 $M_{21}=a+c-5=5$ 与中心格撞车。

## 4. 形式化要点（踩过的坑）

- **`IsNormal` 不可判定**：它用 `Function.Injective` 陈述，`decide` 用不了。
  必须先改写成两个 `Fin 3` 上的显式量词（逐格范围 + 不同位置取值不同），
  即 `isNormal_iff`。
- **`simp` 不展开 `Fin 3` 上的全称量词**：必须显式给 `Fin.forall_fin_succ`，
  把量词剥到 81 个地面实例，再由 `norm_num` 判定。这是让有限枚举跑起来的关键。
- **界要自己造**：`IsNormal` 里没有 $a,c$ 的界，先由 $a=M_{00},c=M_{02}$ 是格子
  得 $1\le a,c\le 9$，否则 `interval_cases` 启动不了。
- **截断减法**：$a+c-5$、$15-a-c$ 在零处截断，必须按截断后的实际值逐例评估。
- **平台禁止 `native_decide`**（"trusts compiled native code instead of the
  kernel"）。算具体 Finset 的基数要改用 `norm_num [eightPairs]`。
- **doc comment 不能悬空**：把 `theorem` 移到 namespace 外时，它前面的
  `/-- ... -/` 必须一起搬走，否则 `end` 处报 "expected 'lemma'"。
- `ext` 之后要 `rcases` 把配对拆成 $(a,c)$，否则 `rfl` 作用在 `ac.1` 上失败。
- 成员资格 $(2,4)\in\mathrm{paramSet}\ 5$ 要用 `norm_num [paramSet, IsParam3]`；
  `simp` 只会展开成 `range`/`product`/`filter` 就停住。

## 5. 下一步

1. 宇轩在网页端确认 proposal `98d3dea7` 并 Submit。
2. 更远：$4\times4$ 计数（Beck–van Herick，周期 6 拟多项式）、泛魔方、
   最完美幻方（Ollerenshaw–Brée）、平方数幻方（开放问题，只能做部分结果）。
