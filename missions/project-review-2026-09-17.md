# 项目审查与推进规划

审查时间：2026-09-17 18:30（Asia/Shanghai）
审查人：agent · 对象：`prove2me_workspace` 全仓 + prove2.me 平台实时状态

> 这篇文档里，「实测」= 我这次真的拉了平台 API / 跑了命令 / 跑了数值；
> 「推测」= 我的判断或估计。两者分开写。

---

## 0. 一句话结论

**仓库是健康的，但战线摊得太开。** 唯一全绿的三个 Mission（幻方 I / II / III）恰好
证明了这个环境里什么是赢法：选题小而完整 + 100% 复用已发布、已 Prove 的基础设施。
而仍在开的数论三条线（Five Primes / Weak Goldbach / Euler γ）已经进入边际收益递减
区——它们剩下的 Open 节点要么是解析数论硬骨头，要么需要大规模机器证书。

建议：**主力压到 Magic Squares IV（三阶泛魔方与对称幻方计数），其余冻结/归档。**

---

## 1. 实测事实

### 1.1 平台侧（实时拉取，不是凭记忆）

| Mission | 节点总数 | 未完成 | goal 状态 |
|---|---|---|---|
| Magic Squares I（$M_3$ 计数） | 9 | **0** | `magic_count_three_divisible` Proved |
| Magic Squares II（$H_3$ 半幻方） | 8 | **0** | `semi_magic_count_three` Proved |
| Magic Squares III（洛书唯一性） | 2 | **0** | `magic_three_normal_eight` Proved |
| The Bunkbed Conjecture Is False | 35 | **0** | 封版归档 |
| Every Odd Number … Five Primes | 50 | **28** | 未达成；另有 **2 个 Disproved** |
| Weak Goldbach Conjecture | 21 | **18** | 目标 Open |
| Irrationality of Euler's γ | 100 | ~16（去重后） | 未达成 |

Proposal 状态（实时）：I = `Reviewed`，II = `Reviewed`，III = **`In review`**
（已从 Draft 前进，说明你已经在网页端提交过了）。

幻方三线一共 **24 个定理全部 Proved**，没有一个挂在半路——这是本项目目前唯一
一条从头到尾跑通的链路。

### 1.2 本地仓库

- `git status` **干净**，`main` @ `1b30762`，远端同步。
- 1041 个跟踪文件，工作树 **222 MB**；`.git` 146 MB；`.lake/` 8.4 GB（构建缓存，别删）。
- **`Solutions/` 里 0 个 `sorry`**（全仓 grep 确认）。
- 环境可用性抽查：
  `lake env lean Solutions/Sol_MagicSquares_magic_three_normal_eight.lean`
  → **通过**，耗时 1m44s，只有 1 条 `unused simp argument: eightPairs` 警告。
  ⇒ Lean 环境、Mathlib 缓存、最新提交的 constellation 三者自洽，没有腐坏。

### 1.3 数值侦察（为下一步选题做的实证，不是 Lean 证明）

我用**两种独立方法**（3×3 矩阵暴力枚举 + MacMahon 参数化遍历）交叉验证，
结果在暴力可达范围内（$t\le 12$）完全一致，参数化侧推到 $e=5$（$t=15$）：

| $e$ | $t=3e$ | $M_3$ | $P_3$（泛魔） | $S_3$（对称） | $2e^2+2e+1$ |
|---|---|---|---|---|---|
| 0 | 0 | 1 | 1 | 1 | 1 |
| 1 | 3 | 5 | 1 | 3 | 5 |
| 2 | 6 | 13 | 1 | 5 | 13 |
| 3 | 9 | 25 | 1 | 7 | 25 |
| 4 | 12 | 41 | 1 | 9 | 41 |
| 5 | 15 | 61 | 1 | 11 | 61 |

闭形式（**这是数值确认的猜想，尚未形式化**）：

$$P_3(t)=\begin{cases}1 & 3\mid t\\ 0 & 3\nmid t\end{cases}
\qquad
S_3(3e)=2e+1,\quad S_3(t)=0\ (3\nmid t)$$

手推也对得上（待证）：把六条断对角条件加到参数化
$\mathrm{mkMagic3}(e,a,c)$ 上得 $a=c=e$，即**全常数方阵**——三阶不存在非平凡泛魔方；
把对称条件加上得 $c=e$，此时 $a$ 在 $[0,2e]$ 自由，形状是

$$\begin{pmatrix}a & 2e-a & e\\ 2e-a & e & a\\ e & a & 2e-a\end{pmatrix},\qquad a=0,\dots,2e .$$

---

## 2. 发现的问题（按优先级）

### P0 · 仓库体积失控：222 MB 里 196 MB 是 4 个自动生成物

| 大小 | 文件 |
|---|---|
| 95.7 MB | `Solutions/SondowRosserMiddleTree1000000.lean` |
| 35.7 MB | `Solutions/SondowRosserMiddleTree1000000Compact.lean` |
| **35.4 MB** | `missions/euler-gamma/sondow/continuation/failed-recursion-rosser-middle-1000000.lean` |
| 29.4 MB | `Solutions/SondowRosserMiddleBalanced1000000.lean` |

第三个文件名里就带着 `failed-recursion` —— 一个**失败实验的产物**也进了 Git。
这 4 个文件占仓库 **88%**，而且已经在提交历史里（所以 push 时报过 large-file warning）。

### P1 · 三线并行、两线半途

Five Primes 剩 28 个 Open，**其中 2 个节点状态是 `Disproved`**
（`vinogradov_block_if_form`、`vinogradov_lemma_if_form`）——说明平台上有些已陈述的
中间引理**本身是错的**。继续这条路要先返工清理错误陈述，不是单纯"再加把劲"。

### P1 · 根 `status.md` 已经漂移

- 「Current work」还写着 Five Primes Theorem 5.1，实际那件事在 9/13 就已经告一段落。
- Mission index 里 Magic Squares I 仍写「1 open child 待证」，实际全绿。
- 文档没跟上仓库。这会让下一次开会话时读到错误起点。

### P2 · 临时文件残留

`missions/semi-magic/` 与 `missions/normal3/` 下的 `item-tmp.json`、`milestone-tmp.json`
共 4 个已被 Git 跟踪。（`magic-squares/` 下的同名文件上一轮已删。）这些是脚本写载荷的
中转文件，零保留价值。

### P2 · 无待轮询的提交

所有已知 submission 都到了终态，没有悬在空中的作业——这点没问题。

---

## 3. 推荐主线：Magic Squares IV

**选题：三阶泛魔方计数 $P_3$ 与对称幻方计数 $S_3$。**

为什么是它：

1. **不需要任何新数学。** 两个结果都直接从已发布的
   `Def_MagicSquaresParam3` 参数化加条件读出，归约体和 Mission I/II 一样短
   （一行 `rw` 级别）。
2. **定义层已经白送。** `Def_MagicSquares` 里的 `panMagicCount`、`symmetricMagicCount`
   在 Mission I 就一起 PUBLISHED 了，却至今没有被任何定理用过——现成的空白产地。
3. **全部重武器已 Prove 且可直接 import：**
   `center_of_order_three`、`magic_three_param_sufficient` / `necessary`、
   `magic_count_three_otherwise`（$3\nmid t$ 时为 0）、MacMahon 的
   $M_3$ 表达式……不需要重推任何已知部分。
4. **Mission III 刚验证了套路：** 有限化到参数对集合 → 加一个 `Def_*` 定义模块封装
   filter（不可判定的就用 `classical`）→ `Finset.card_bij` → 闭形式。
   `Def_MagicSquaresNormal3` 就是这个套路的现成模板。
5. **叙事完整。** I 计数 → II 半幻方 → III 分类 → IV 特殊类（泛魔/对称），
   四个 mission 拼起来正好是"三阶幻方从定义到彻底清点完毕"的完整故事。
   对一个准备拿出去讲的形式化项目来说，这比一堆各自半截的分析学节点有说服力得多。

### 分session推进计划

| # | 内容 | 交付标准 |
|---|---|---|
| S1 | 发布 `Def_MagicSquaresSpecial3`（`symmParamSet e` / `panParamSet e`）；建 Mission IV proposal + items + milestone；证 `pan_three_card` | 定义 PUBLISHED；`panMagicCount 3 t` 的 goal Proved |
| S2 | 证 `symm_three_card`（$c=e$ 的纤维，$a\in[0,2e]$），连同 $3\nmid t$ 分支 | `symmetricMagicCount 3 t` 的 goal Proved |
| S3 | 说明文档 + `git commit` + 更新根 `status.md` | 远端 SHA 校验通过 |

每步都遵守现有约定：先在 `examples/magic-squares/` 里草稿，
定型后挪到 `Solutions/Sol_MagicSquares_*.lean` 重新编译，再提交平台，最后 Git。

### ✅ 进度（2026-09-18 晚，S1+S2 一轮做完）

计划外的加速：**不需要 `panParamSet`**。泛魔三阶的唯一成员是常数阵，直接命名
`constSquare3 e` 比造一个单点参数集更诚实；对称族的参数集就是 `range (2*e+1)`。

| 交付 | 实际 |
|---|---|
| 定义 | `MagicSquaresSpecial3` PUBLISHED（`dc7c7ce9`） |
| 定理 | **6 个节点全部 Proved**：`pan_three_card`、`symmetric_magic_three_classify`、`symm_three_bij`、`pan_three_otherwise`、`symm_three_otherwise`、goal `special_three_count` |
| 裁决 | 5 份 `ACCEPTED`；goal 先判 `SKETCH_ACCEPTED`，孩子全 Proved 后**自动升 Proved** |
| proposal | `7af96e14`（7 items / 3 milestones / main=goal），Draft —— **待宇轩 Submit** |
| 文档 | `missions/magic-squares-iv/status.md` |

修正两处选题判断：

1. 目标不是「归约到 `paramSet` 的一行 `rw`」。`pan_three_card` 的实质是「十二个线和
   等式只有常数解」（一条 `omega`，但要先把 `Fin 3` 的 `i+k` / `rev i + k` 化简），
   `symm_three_bij` 的实质是「可容许性 $a\le 2e$ 是截断减法的事实」——两者都不是
   现成引理的直接推论，各自是完整的分类定理。
2. 目标陈述用**全 `t` 的形式**（`if 3 ∣ t then …`）而不是只写 $t=3e$，这样 mission
   的 goal 是完整清点而不是半张表；代价是多两个 `otherwise` 节点（每个 3 行，
   复用 `center_of_order_three`）。

下一步：S3（文档已写，`git commit` 待宇轩确认）；之后 Magic Squares V = 四阶计数。

---

## 4. 备选线（诚实评估）

| 选项 | 内容 | 我的判断 |
|---|---|---|
| **A** | Five Primes 收官（Vaughan + 28 个解析节点） | **不推荐。** 收益确实大（Tao 定理 5.1 完整形式化），但要先翻掉 2 个 `Disproved` 的错误陈述并重建其上游。预计是几十小时量级，且失败概率不低。作为"长期爱好"（你说过 AI4Math 不是 KPI）可以留着慢慢啃，但不要让它占住"当前主线"。 |
| **B** | Weak Goldbach 筛覆盖 73e8ddac | **不推荐。** 本质是 $4\cdot10^{12}$ 个筛块的有限校验，平台自己标成 verified-computation core。既缺算力也缺可信生成管线，当前环境不适合。 |
| **C** | 四阶 $H_4$ / $M_4$ 计数（弱读法：非负、可重复） | **暂缓。** 需要先补 Ehrhart / Birkhoff 多胞体格点计数的机制，是个真正的工程量。等 IV 跑通、信心回来了再评估。合适的位置是 Magic Squares V。⚠️ **2026-09-18 更正**：这里原先注的「Beck–van Herick」是错的——那篇算的是**互异正整数**（inside-out polytope），不是弱读法；弱读法的结构定理出自 BCCG(2003) 定理 1/2。详见 `project-review-2026-09-18.md` §3.3。 |
| **D** | 平方数幻方（`referpaper/` 里那三篇开放问题） | **不合适。** 是公开未解决问题，只能做部分结果，容易做成"看起来动了一半"。 |

---

## 5. 瘦身（2026-09-17 18:55 已执行）

只做了安全的一步：`git rm --cached` + 补 `.gitignore`，**不动历史、不 force push**。
文件当时全部保留在磁盘上；这些生成物的来源信息（生成器 / 哈希 / 结论）仍完整记录在
`missions/euler-gamma/sondow/ROSSER-FINITE-CERTIFICATES.md`，不会因为移出版本控制而丢。

```bash
git rm --cached \
  Solutions/SondowRosserMiddleTree1000000.lean \
  Solutions/SondowRosserMiddleTree1000000Compact.lean \
  Solutions/SondowRosserMiddleBalanced1000000.lean \
  Solutions/SondowRosserMiddle100000.lean \
  missions/euler-gamma/sondow/continuation/failed-recursion-rosser-middle-1000000.lean \
  missions/semi-magic/item-tmp.json missions/semi-magic/milestone-tmp.json \
  missions/normal3/item-tmp.json    missions/normal3/milestone-tmp.json
# .gitignore 追加：Solutions/SondowRosserMiddle*.lean、
#                 missions/euler-gamma/sondow/continuation/failed-recursion-*.lean、
#                 missions/*/item-tmp.json、missions/*/milestone-tmp.json
```

**结果（实测）**

| | 之前 | 之后 |
|---|---|---|
| 跟踪文件数 | 1041 | 1032 |
| 工作树跟踪体积 | 222.2 MB | **22.5 MB** |
| >5 MB 的文件 | 4 个 / 196.2 MB | **0 个** |

剩下最大的单个文件是 `missions/euler-gamma/research/variable-order-results.json`
(3.3 MB)，40 个 >200 KB 的文件合计 16.8 MB —— 都在健康范围内，不需要再动。

**后续（2026-09-17 19:10 与本轮审查后）**

- 那 5 个大生成物已于 19:10 **从磁盘物理删除**，共释放 199.7 MB。因为它们当时
  已经 untrack，物理删除**不会、也无法产生新的 commit**，所以 `git log` 里看不到。
- 本轮审查后又做了一轮脱管：13 个 `SondowRosserMiddle*.{lean,json}`、
  3 个 `balanced-largest-block-*.lean`、43 个 `.log`，共 59 个文件
  （**磁盘文件全部保留**），`.gitignore` 一并放宽为 `missions/**/*.log` 等。
  实测：跟踪文件 1033 → **974**，索引树 22.5 MB → **18.1 MB**。

**还没做的**：`.git` 仍是 146 MB，因为那 196 MB 还躺在历史里。要压下来得用
`git filter-repo` 重写历史 + force push。**不可逆，等你点头再做。**

---

## 6. 需要你拍板的三件事

1. **主线选哪条？** 我推荐 Magic Squares IV；如果你想的是 Five Primes 或完全不同的方向，说一声。
2. **P0 瘦身做到哪一步？** 只 `--cached` 移除（安全、可逆），还是连历史一起 purge（不可逆）。
3. **Mission III 的 proposal 已经在 `In review`** —— 如果 moderator 通过后你希望我把它
   在根 `status.md` 里正式标成"完成"（现在是 Active 指向幻方 I），我可以顺手做掉。
