# 幻方项目评估（2026-09-18）：基建、大项目与开放问题

承接 `project-review-2026-09-17.md`。当天 Mission IV 全部 Proved、proposal `7af96e14`
进入 `In review`。本文回答：**基建到什么程度了，能不能开大 mission / 开放问题。**

方法说明：平台状态、文献陈述、4×4 计数序列都是**实测/实读**，逐条标了来源；
推测部分一律标注「推测」。

---

## 1. 一句话结论

**基建是「$n=3$ 的完整理论」，不是「一般计数理论的基础设施」。**
所以「大 mission」要往**一般 $n$ / 更高阶数**的轴上选，而**不是**再堆 $n=3$ 的变体
（那已经闭环，边际收益递减）；**开放问题不适合当 mission 目标**，但开放问题
**周边的已知结构定理**可以——而且是唯一能诚实交付的东西。

---

## 2. 基建现状（实测）

### 2.1 平台侧

全平台检索（`/theorems?q=MagicSquares|magic|panmagic|transpose|affine`，2026-09-18）：

| 项 | 数量 |
|---|---|
| 幻方相关节点总数 | **39** |
| 其中定义 | 7 |
| 其中定理 | 32，**状态全部 `Proved`** |
| 该领域 Open 节点 | **0** |
| 挂在某个 mission DAG 上的 | 25 |
| **孤儿（Proved 但不属于任何 mission DAG）** | **14** |

四个 mission：I `magic-squares`（$M_3$）、II `semi-magic`（$H_3$）、III `normal3`（洛书
唯一性）、IV `magic-squares-iv`（泛魔/对称三阶，proposal In review）。

**14 个孤儿节点**（结果是真的、但没进任何任务图，按计分口径大概率不计）：

```
Proved:  affine_preserves_magic, flipHorizontal_preserves_magic, flipVertical_preserves_magic,
         magic_constant_of_normal, magic_count_three_otherwise,
         normal_order_three_associative, normal_order_three_center_five,
         normal_order_three_constant, normal_order_two_none,
         panmagic_is_magic, total_sum_eq_n_line_sum, transpose_preserves_magic
Def:     MagicSquaresNormal3, MagicSquaresTransforms
```

其中 8 条是 `Def_MagicSquaresTransforms` 那族（转置/翻折/仿射保幻性）+ 一般 $n$ 的
`magic_constant_of_normal`。**这批是整个基建里唯一含一般 $n$ 的部分**，却没进图。

### 2.2 本地

- 定义模块 7 个 / **659 行**（`Def_MagicSquares*`）。
- 幻方相关提交文件 27 个 / **2569 行**（`Solutions/Sol_MagicSquares_*.lean`）。
- 文献库 12 篇（`referpaper/`）。

### 2.3 覆盖深度（关键）

| 阶数 | 已有内容 |
|---|---|
| 一般 $n$ | **仅 1 条**：`magic_constant_of_normal`（$2s=n(n^2+1)$）。另有定义层的 `IsNormal` / `IsBimagic` 等 |
| $n=2$ | 2 条（`normal_order_two_none`、$H_2/M_2$ 相关的零散结果） |
| $n=3$ | **完全闭环**：$H_3$ 计数、$M_3$ 计数、参数化双射、洛书唯一性、$P_3$、$S_3$、对称变换族 |
| $n\ge4$ | **零** |

结论：基建的价值在 $n=3$ 的**深度**（一个阶数从定义到彻底清点），不在 $n$ 的**宽度**。

---

## 3. 这次评估新发现的三个真实缺口（硬货）

### 3.1 🔴 定义层与文献不一致：`IsPanMagic` 比 BCCG 的 $P_n$ 强

BCCG（*Amer. Math. Monthly* 110 (2003)，即定义模块的记号基准）原文对 pandiagonal 的定义是：

> "A pandiagonal magic square is a **semi-magic** square whose diagonals parallel to the main
> diagonal from the upper left to the lower right, **wrapped around** …, add up to the line sum."

即：**只要求一个方向**（与主对角线平行的那 $n$ 条断对角，含主对角本身），
**不要求副对角、也不要求另一方向的断对角**。

而我方已发布的 `Def_MagicSquares.IsPanMagic` 要求 **两个方向**的断对角都等于线和。

实测差异（$n=3$，行枚举，`tmp/order4_counts.py` 同族脚本）：

| $t$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| 单向（BCCG $P_3$） | 1 | 3 | 6 | 10 | 15 | 21 | 28 | 36 | 45 | 55 |
| 双向（我方 `IsPanMagic`） | 1 | 0 | 0 | **1** | 0 | 0 | **1** | 0 | 0 | **1** |

单向那列正是 $\binom{t+2}{2}=\frac12t^2+\frac32t+1$，与 BCCG 定理 2 的
「$P_n$ 是 $n^2-3n+2$ 次拟多项式」（$n=3$ 即 2 次）以及其 $P_3$ 显式公式**完全吻合**。

**后果（必须处理）**：

1. **Mission IV 的泛魔结果没错**——它说的是更强的那个概念；但**不能**在任何文档里
   声称它是 BCCG 的 $P_3(t)$。`missions/magic-squares-iv/status.md` 与 proposal 的描述
   都只写了「$P_3=1$ 当且仅当 $3\mid t$」，没宣称是 BCCG，**目前没有实质错误**，但
   必须在下一步显式区分，否则以后一定会有人拿它去对 BCCG 的表。
2. 顺带一个反直觉事实：**BCCG 的单向泛魔与 magic 互不包含**（不要求副对角）。
   所以「pandiagonal ⟹ magic」在文献那个读法下**是假的**（我方 `panmagic_is_magic`
   在**我方**读法下为真，这条没错）。
3. **要让计数理论接上文献，只差一个定义 + 一个便宜的定理**：
   补 `IsPandiagonal`（单向）、$P^{BCCG}_3(t)=\binom{t+2}{2}$。成本极低，收益是把
   「$P_n$ / $S_n$」整条线接上 BCCG 的定理 2。

### 3.2 🔴 Mathlib 没有 Ehrhart / 拟多项式 / 有理生成函数

精确 grep（`grep -rn -i "Ehrhart" Mathlib/`）：**0 命中**。
`generatingFunction` 只命中 `Probability/Moments/Basic.lean`（无关）。

Mathlib **有**的是凸几何那一侧：
- `Analysis/Convex/Birkhoff.lean`、`Analysis/Convex/DoublyStochasticMatrix.lean`
- `LinearAlgebra/Matrix/Stochastic.lean`

这些给的是 Birkhoff–von Neumann（双随机矩阵 = 排列矩阵的凸包），**是凸几何不是格点计数**。
「$t$-膨胀多胞体的整点数 = 多项式/拟多项式」——这条**要自己建**。

4×4 半幻方的 9 次多项式（见 4.2）正是这条缺口的第一个试金石。

### 3.3 🔴 文献库与目标错配（含一处项目文档错误）

- **`referpaper/README.md` 与 09-17 评审把 Beck–van Herick 描述成「$4\times4$ 弱幻方计数
  $M_4(t)$」，这是错的。** 该文摘要第一句就限定 **distinct positive integers**，
  定义的是 $a_n(t)$（互异正整数、线和 $t$）与 $c_n(t)$（互异、上界 $t$），
  方法是 inside-out polytope（超平面配置 + Ehrhart）。
  与我方「非负、可重复」的弱读法**不是同一个问题**，数值不可互相对照。
- **最完美幻方（Ollerenshaw–Brée）的核心文献不在库里**：README 只在「远期」提了名字，
  `referpaper/` 里没有那本 IMA 专著，也没有相关论文。
- 库里真正对得上弱读法的是 BCCG（2003）与 Beck–Zaslavsky（2006, 2010）。

---

## 4. 大项目候选分级（带硬数据）

### 4.1 Tier 1 — 现在就能开，mission 级，不需要新机制

**(a) 定义层补齐 + 文献对齐。** 零成本，打开所有后续的门：

- `IsPandiagonal`（BCCG 单向泛魔）；
- `IsMostPerfect`（2×2 块和 + 对角互补对，见 4.2）；
- 更正 `referpaper/README.md` 与 09-17 评审里对 Beck–van Herick 的描述。

**(b) BCCG 的 $n=2,3$ 全谱对齐。** 全是现成便宜节点：
$H_2(t)=t+1$；$M_2=S_2=P_2=\mathbf 1_{2\mid t}$；
单向 $P^{BCCG}_3(t)=\binom{t+2}{2}$（本次实测确认）。
把「我们的 $S_3$ 与 BCCG 逐字一致」这件事**在平台上立成节点**，比在文档里说更有力
（我方 $S_3(3e)=2e+1$ 与 BCCG 的 $S_3(t)=\frac23t+1\ (3\mid t)$ **完全吻合**，已核对）。

**(c) 最完美幻方 $n=4$。** Ollerenshaw–Brée 的核心是**构造 + 双射**（与 reversible
squares 一一对应），**不需要 Ehrhart**。已知数据（OEIS A051235 / Royal Society / Nature 书评）：

| 阶 $n$ | 本质不同（Frénicle 标准形）个数 |
|---|---|
| 4 | 48 |
| 8 | 368 640 |
| 12 | 22 295 347 200 |

一般公式对 $n$ 的素因子指数做双重求和——**不建议**碰一般公式；$n=4$ 的 48
（或全体 384）是可做的，且这是**文献里唯一被完全数清的幻方子类**，叙事价值高。

### 4.2 Tier 2 — mission 级，但要自建机制

**(d) $H_4(t)$ 的显式多项式（9 次）。** 本次已算出并验证：

$$H_4(t)=\frac{11}{11340}t^9+\frac{11}{630}t^8+\frac{19}{135}t^7+\frac23t^6
+\frac{1109}{540}t^5+\frac{43}{10}t^4+\frac{35117}{5670}t^3+\frac{379}{63}t^2
+\frac{65}{18}t+1$$

证据强度：**我确认了**——DP 与独立穷举在 $t\le3$ 逐值一致；$t=0..14$ 共 15 个值全部
落在该多项式上；第 10 阶差分恒为 0；首项 $\frac{11}{11340}\approx0.000970$ 与
$B_4$ 体积吻合；次数 9 $=(n-1)^2$ 与 BCCG 定理 1 一致。

**但**证明它对**一切** $t$ 成立，需要多项式性定理（Ehrhart，或为这个族自建递推/生成函数）。
可拆：

1. 便宜档：证 $t\le N$ 的具体值（纯计算，平台禁止 `native_decide`，需 `norm_num` 分块）。
2. 重头档：多项式性（Tier 2 的核心）。

**(e) $M_4(t)$ 的拟多项式（7 次，周期待定）。** 本次实测 $t=0..12$：

```
1, 8, 48, 200, 675, 1904, 4736, 10608, 21925, 42328, 77328, 134680, 225351
```

差分到 9 阶仍不稳定 ⇒ 与「7 次拟多项式」一致（$n^2-2n-1=7$，BCCG 定理 2）。
**周期我判不了**：13 个点不足以定周期。要做得先补更多项 + 拟多项式理论。

**(f) 一般 $n$ 的多项式性：$H_n(t)$ 是 $(n-1)^2$ 次多项式（Ehrhart–Stanley，BCCG 定理 1）。**
这是本领域**最有价值的一条**，也是 Tier 2 的核心难点：等价于给这个具体族
（行和=列和=t 的非负整矩阵）搭「整点多胞体 Ehrhart 多项式」的机制。
BCCG 原文提到 Theorem 1 有一个**初等证明**（引 [14]），这对形式化是好消息——
初等路线比一般 Ehrhart 理论可形式化得多。**推测**（未核对 [14]）：
引 [14] 是 Anand–Dumir–Gupta 那篇猜想来源或 Stanley 之后的初等版本，
值得先把 [14] 找出来再定方案。

### 4.3 Tier 3 — 现在不要碰

**(g) Beck–van Herick 的互异口径 $a_4(t),c_4(t)$**：inside-out polytope +
超平面配置 + Ehrhart–Macdonald 互反律。工作量远超现有基建，且与我方定义不同源。

**(h) 一般 $n$ 的 $M_n,S_n,P_n$ 拟多项式性 + 互反律恒等式（BCCG 定理 2）**：需要
拟多项式 + Ehrhart 互反律，是 (f) 的超集。别一上来就碰。

**(i) 平方数幻方（Euler 1770，开放）**：只能做部分结果，且库里两篇（Rome–Yamagishi、
Flores）的已知结果偏计算型，容易做成「看起来动了一半」。
若要做，**先读这两篇挑一条陈述干净的结构定理**（如参数化/中心必要条件），
**不要**做穷尽搜索。

---

## 5. 推荐路线

| 阶段 | 内容 | 量级 |
|---|---|---|
| **P0** | 补 `IsPandiagonal` / `IsMostPerfect` 定义；BCCG $n=2,3$ 对齐节点（含 $P^{BCCG}_3=\binom{t+2}{2}$）；更正 README/评审错误；**请 captain 把 14 个孤儿节点挂回 DAG**（含 8 条保幻变换 + 一般 $n$ 的 `magic_constant_of_normal`） | 半天～一天 |
| **P1** | **Mission V =「四阶半幻方 $H_4(t)$」**：先交付「显式多项式 + 前若干项可验证」（便宜档），把多项式性列为第二个 milestone | 2–4 天 |
| **P2** | **Mission VI =「最完美幻方与 Ollerenshaw–Brée 双射（$n=4$）」**：先补文献（那本 IMA 专著 / 综述），再形式化构造与 48（或 384） | 1–2 周 |
| **P3** | 自建 Ehrhart/初等多项式性机制 → 一般 $n$ 的 $H_n$ 多项式性、$M_4$ 拟多项式 | 1–2 月 |

---

## 6. 禁忌与风险

1. **不要**把 Mission IV 的泛魔结果当作 BCCG 的 $P_3$ 去引用或对照（定义不同，见 3.1）。
2. **不要**承诺 $M_4$ 的周期数值——我只有 13 项，判不了。
3. **不要**把 Beck–van Herick 的互异计数混进弱读法。
4. **不要**在没补 P0 定义的情况下开 Mission V/VI——定义层不对齐会让后面的
   「与文献一致」claim 全部失效。
5. 平台事务：Mission IV 的 proposal 已在 `In review`，**等 moderator**，不需要再动。
6. 孤儿节点是**可见性**问题不是数学问题：那 14 条结果是对的，只是没进图。

---

## 7. 需要宇轩拍板

- **① 下一步走哪条**：P0→P1（四阶 $H_4$，稳、有硬数据）／P0→P2（最完美幻方，叙事更强但要补文献）／
  直接冲 P3（一般 $n$，价值最高、最重）。
- **② P0 里的「请 captain 挂回 14 个孤儿节点」要不要发**（结果是真的，挂回去才计入 DAG）。
- **③ 要不要为「与文献对齐」单开一个小 mission**（BCCG $n=2,3$ 全谱 + 定义区分），
  还是并进 Mission V 的前置。
