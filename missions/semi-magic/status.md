# Mission: semi-magic — 三阶半幻方计数 $H_3(t)$

负责人：anche（徐宇轩） · 环境：Lean 4.33.1 / Mathlib `0df444a3` · 平台：prove2.me v0.10.4

创建：2026-09-17 · 最后更新：2026-09-17 02:20（Asia/Shanghai）

## 0. 定位

这是幻方形式化的**第二个 mission**。Mission I（`Magic Squares I`）已经把
**magic** 计数 $M_3(3e)=2e^2+2e+1$ 全部证完（goal `magic_count_three_divisible`
已 Proved）。本 mission 攻 **semi-magic** 计数

$$H_{3}(t)=3\binom{t+3}{4}+\binom{t+2}{2},$$

即行、列和都为 $t$ 而**对角线无约束**的 $3\times3$ 非负整数矩阵个数。与 $M_3$
不同，$H_3$ 是**真多项式**（次数 $(3-1)^2=4$），没有 $3\mid t$ 的周期性。

## 1. Proposal

- **id**：`6ceb0b04-0e12-4909-a3b7-21581fe08d59`
- **名称**：*Magic Squares II: MacMahon's Enumeration of Order-Three Semi-Magic Squares*
- **类型**：`ResearchPaper` · **字段**：Combinatorics `55eec41b-ff24-45ad-96b6-49d7a6869286`
- 状态：`Draft`，需宇轩在网页端逐项确认后 Submit（平台规则：goal 不挂 milestone，
  故只提交 4 个支撑 milestone）

## 2. 已发布节点

### 定义

| 平台名 | 本地文件 | id |
|---|---|---|
| `MagicSquares` | `Definitions/Def_MagicSquares.lean` | `be2f2b6a-a540-47ae-b487-ac22532a2745`（mission I 已有） |
| `MagicSquaresSemiMagic3` | `Definitions/Def_MagicSquaresSemiMagic3.lean` | `983f535e-819e-4d18-baba-388fb3c39413` |
| `MagicSquaresCompositions` | `Definitions/Def_MagicSquaresCompositions.lean` | `73ed6522-7b76-4bfc-b852-f197b90ec3b2` |

`Def_MagicSquaresSemiMagic3`：`sm3Of`（六个置换矩阵的线性组合）、`sm3OfFun`、
`sm3Coeffs`、`sm3Of_semiMagic`（六条线和都等于系数和）、`sm3EvenMin`、
`sm3Params`（规范化系数向量的有限集）、`sm3Count`。

`Def_MagicSquaresCompositions`：`comps N k n`（装在 `Fin (N+1)` 盒子里的
$k$ 元拆分）、`compsCount`。

### 定理（DAG）

| theorem_name | id | 状态 |
|---|---|---|
| `MagicSquares.comps_card` | `65af2905-cd30-4bb9-aa15-3ea5f86790e0` | 证明已提交 `2fa100b1`（待轮询） |
| `MagicSquares.sm3_canonical` | `650b0511-bff1-4101-84b1-a49d5bef9849` | **Open**（核心难点） |
| `MagicSquares.sm3_bij` | `c4897555-460d-4fc5-8a01-732b5d8f39c9` | **Open** |
| `MagicSquares.sm3_params_card` | `7d09e267-c923-49c2-91f3-76185a464ad4` | **Open** |
| `MagicSquares.semi_magic_count_three` | `55e2191d-be25-4e6d-af7a-4635a34e5c63` | **Open** — GOAL |

```
semi_magic_count_three (GOAL)
├── sm3_bij           : semiMagicCount 3 t = sm3Count t
│   └── sm3_canonical : 典范分解存在 + 唯一（min(x,y,z)=0）
└── sm3_params_card   : sm3Count t = 3 C(t+3,4) + C(t+2,2)
    └── comps_card    : stars and bars（k+1 部分 → C(n+k, n)）
```

归约体（待提交）
```lean
theorem solution (t : ℕ) : semiMagicCount 3 t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by
  rw [sm3_bij t, sm3_params_card t]
```

## 3. 数学方案（已数值验证 t = 0..8 全部吻合）

### 3.1 六个置换矩阵

偶的三条横截（单位阵与两个 3-循环）：
$$D=\{00,11,22\},\ E=\{01,12,20\},\ F=\{02,10,21\}$$
奇的三条（三个对换）：
$$A=\{00,12,21\},\ B=\{02,11,20\},\ C=\{01,10,22\}$$

以 $u,v,w$ 为偶的重数、$x,y,z$ 为奇的重数：

$$M=\begin{pmatrix}u+x & v+z & w+y\\ w+z & u+y & v+x\\ v+y & w+x & u+z\end{pmatrix}$$

六条线和都等于 $u+v+w+x+y+z$。

### 3.2 为什么必须规范化

表示**不唯一**：$D+E+F=A+B+C=J$（全 1 阵）。取
$u=\min D,\ v=\min E,\ w=\min F$ 减掉后，剩余奇重数满足 $\min(x,y,z)=0$，
此时表示唯一。这是把计数变成**划分**而不是容斥的关键。

### 3.3 存在性（核心引理）

减去 $uD+vE+wF$ 后残阵 $M'$ 仍半幻，且三条偶横截最小值都为 0。用四参数
$(a,b,c,d)=(M'_{00},M'_{01},M'_{10},M'_{11})$ 展开，三个「最小值为 0」读作

$$\min(a,\ d,\ a+b+c+d-t')=\min(b,\ t'-c-d,\ t'-a-c)=\min(t'-a-b,\ c,\ t'-b-d)=0 .$$

若 $b>c$，则中间那个最小值为 0 的三种方式都反推出 $b\le c$：
$b=0$ 与 $b>c\ge0$ 矛盾；$t'-c-d=0$ 得 $c+d=t'$，由 $b+d\le t'$ 得 $b\le c$；
$t'-a-c=0$ 得 $a+c=t'$，由 $a+b\le t'$ 得 $b\le c$。故 $b\le c$，对称得
$c\le b$，即 $b=c$ —— 这正是 $M'$ 只由 $A,B,C$ 组合出来的条件。

（注意：只需 $a+b\le t',\ c+d\le t',\ a+c\le t',\ b+d\le t'$ 四个不等式 +
中间、右边两个 min 条件；$a+b+c+d\ge t'$ 与左边 min 条件不参与。）

### 3.4 计数

按 $(x,y,z)$ 中**第一个零点**划分：

| 情形 | 剩余五元和 | 个数 |
|---|---|---|
| $x=0$ | $t$ | $\binom{t+4}{4}$ |
| $x>0,\ y=0$ | $t-1$ | $\binom{t+3}{4}$ |
| $x,y>0,\ z=0$ | $t-2$ | $\binom{t+2}{4}$ |

两次 Pascal：
$\binom{t+4}{4}=\binom{t+3}{4}+\binom{t+3}{3}$，
$\binom{t+3}{4}=\binom{t+2}{4}+\binom{t+2}{3}$，
故总和 $=3\binom{t+3}{4}+\bigl(\binom{t+3}{3}-\binom{t+2}{3}\bigr)
=3\binom{t+3}{4}+\binom{t+2}{2}$。

## 4. 已完成 / 下一步

已完成：
- [x] 两个定义模块发布
- [x] Proposal + 8 个 items + 5 个 milestone（goal 不挂）
- [x] `comps_card` 本地证明（`examples/magic-squares/comps.lean`、`Solutions/Sol_MagicSquares_comps_card.lean`）+ 提交

下一步（按难度递增）：
1. 轮询 `comps_card` 是否 ACCEPTED
2. **证 `sm3_canonical`** —— 六情形 omega 论证，本 mission 的真正硬骨头
3. 证 `sm3_bij`（`Finset.card_bij` 双向 + `Fin (t+1)` 强制转换）
4. 证 `sm3_params_card`（三项划分 + Pascal）
5. 提交 goal 归约，`semi_magic_count_three` 自动转 Proved
6. 宇轩在网页端确认 proposal

## 5. 环境坑（本轮新增）

- 提交 problem 的端点是 **`/submit-problem`（单数）**，写成复数 `/submit-problems`
  会返回 404 的 HTML 页面而不是 JSON。
- `Fin.cons` 是**依赖类型**版本，必须显式钉住类型族
  `Fin.cons (n := k) (α := fun _ => Fin (N+1)) ...`，否则高阶合一会把类型族留成
  元变量，随后到 `ℕ` 的强制转换报 "has type ?m j but is expected to have type ℕ"。
- `change i + ∑ j : Fin k, ... = n` 在 `change` 里解析会乱，
  必须写成 `change i + (∑ j : Fin k, ...) = n`（加括号）。
- `simp [Fin.cons_zero, Fin.cons_succ]` 同样会踩上面的类型族元变量问题；
  改用 `change` 让 Lean 用 definitional equality 直接展开更稳。
- `Finset.single_le_sum` 的目标里 `f` 与局部变量同名会推断失败，
  用命名参数显式给出 `f :=` 与 `s :=`。
- `Finset.sum_range_reflect f (n+1)` 给出 $\sum_j f(n-j)=\sum_j f(j)$，
  正好是拆分递推里需要的 reindex，无需手写。
- 新加 `Definitions/*.lean` 后必须先 `lake build Definitions.Def_X` 生成 olean，
  否则 `lake env lean` 报 "object file ... does not exist"。
