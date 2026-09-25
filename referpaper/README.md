# 幻方（Magic Squares）文献库

本目录收录幻方形式化工作所依据的原始文献。所有 PDF 均下载自 arXiv / 作者主页，
用于核对定理陈述、边界条件与记号约定。

## 一、计数理论主线（Ehrhart / 多胞体）

| 文件 | 文献 | 核心内容 |
|---|---|---|
| `Beck-Cohen-Cuomo-Gribelyuk - The number of magic squares, cubes and hypercubes (2003).pdf` | M. Beck, A. Cohen, J. Cuomo, P. Gribelyuk, *Amer. Math. Monthly* **110** (2003), 707–717；arXiv:math/0201013 | 定义 $H_n(t)$（半幻方）、$M_n(t)$（幻方）、$P_n(t)$（泛魔）、$S_n(t)$（对称幻方）；证明 $H_n$ 是 $n^2-2n+1$ 次多项式、$M_n$ 是 $(n-1)^2-2$ 次拟多项式；给出 $M_3$ 的 MacMahon 公式。**本工作定义模块 `Def_MagicSquares` 的记号基准。** |
| `Beck-Zaslavsky - An enumerative geometry for magic and magilatin labellings (2006).pdf` | M. Beck, T. Zaslavsky, *Ann. Comb.* **10** (2006) | 幻标号与魔标号的几何枚举框架，把计数函数统一到「带符号图 + 内插」的拟多项式理论。 |
| `Beck-Zaslavsky - Six little squares and how their numbers grow (2010).pdf` | M. Beck, T. Zaslavsky (2010) | 六个 $2\times2$–$3\times3$ 小方块的计数，含半幻方/幻方在小阶时的显式拟多项式，给出 $H_3(t)$ 与 $M_3(t)$ 的封闭形式。 |
| `Beck-vanHerick - Enumeration of 4x4 magic squares (2011).pdf` | M. Beck, T. van Herick, *Math. Comp.* **80** (2011)；arXiv:0907.3188 | ⚠️ **不是弱读法的 $M_4(t)$。** 该文限定 entries 为 **distinct positive integers**，算的是 $a_4(t)$（互异正整数、线和 $t$）与 $c_4(t)$（互异、上界 $t$），方法是 inside-out polytope（超平面配置 + Ehrhart），**与本库其余文献的「非负可重复」读法不同源，数值不可互相对照**。弱读法的四阶结构定理见 BCCG(2003) 定理 1/2。 |
| `DeLoera-Liu-Yoshida - A generating function for all semi-magic squares and the volume of the Birkhoff polytope (2009).pdf` | J. A. De Loera, F. Liu, R. Yoshida (2009) | 半幻方的生成函数与 Birkhoff 多胞体体积，把 $H_n(t)$ 放到有理生成函数与 Ehrhart 理论的框架里。 |
| `Ahmed-DeLoera-Hemmecke - Polyhedral cones of magic cubes and squares (2003).pdf` | M. Ahmed, J. A. De Loera, R. Hemmecke (2003) | 幻方/幻立方的多面体锥表示，Hilbert 基与维数结果，说明为什么计数函数必然是拟多项式。 |

## 二、结构理论与构造

| 文件 | 文献 | 核心内容 |
|---|---|---|
| `Xin - Constructing all magic squares of order three (2008).pdf` | G. Xin, *Electron. J. Combin.* (2008) | 用 MacMahon 分拆分析给出 3 阶幻方的**完整参数化**；本工作 `magic_count_three_divisible` 的参数化 $(a,c)\mapsto M$ 即取自此思路。 |
| `Mueller - On Euler's magic matrices of sizes 3 and 8 (2025).pdf` | F. Mueller (2025) | 欧拉 $3\times3$ 与 $8\times8$ 幻矩阵，联系到四平方和恒等式。 |

## 三、开放问题方向（平方数 / 幂幻方）

| 文件 | 文献 | 核心内容 |
|---|---|---|
| `Pierrat-Thiriet-Zimmermann - Magic squares of squares.pdf` | Pierrat, Thiriet, Zimmermann | 平方数幻方：$3\times3$ 全由平方数组成的幻方是否存在仍是**开放问题**（欧拉 1770 提出）。 |
| `Rome-Yamagishi - On the existence of magic squares of powers (2024).pdf` | M. Rome, S. Yamagishi (2024) | 幂次幻方的存在性结果，给出部分阶数的构造与不存在性。 |
| `Flores - Magic squares of powers (2024).pdf` | A. Flores (2024) | 幂幻方构造与搜索证据。 |

## 四、形式化切入点（本工作采用）

1. **定义层**（`Definitions/Def_MagicSquares.lean`，已发布）：`Square n α`、行/列/主对角/副对角/断对角和、
   `IsSemiMagic` / `IsMagic` / `IsPanMagic` / `IsAssociative` / `IsCompact` / `IsNormal`、
   以及四个计数函数 $H_n, M_n, P_n, S_n$。
2. **结构层**：幻和公式 $2s = n(n^2+1)$、3 阶中心元 $3M_{11}=s$、2 阶正规幻方不存在。
3. **计数层**：MacMahon $M_3(3e)=2e^2+2e+1$ 及其在 $3\nmid t$ 时为 $0$；
   参数化把 3 阶幻方双射到 $\{(a,c)\in\mathbb N^2: e\le a+c\le 3e,\ a\le e+c,\ c\le e+a\}$，
   该集合等价于 $\ell_1$ 球 $\{(p,q)\in\mathbb Z^2: |p|+|q|\le e\}$，其格点数为 $1+4\sum_{k=1}^e k = 2e^2+2e+1$。
4. **远期**：$H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$、$4\times4$ 计数、泛魔方与最完美幻方。

## 五、⚠️ 定义对齐提醒（2026-09-18 实测补记）

读数时务必分清**三种互不等价的读法**，否则会拿错公式去对：

### 5.1 「pandiagonal / 泛魔」有两个不同定义

| 出处 | 要求 | $n=3$ 的计数 |
|---|---|---|
| **BCCG(2003)** 原文 | semi-magic + **一个方向**的断对角（与主对角平行、含主对角，绕回） | $P_3(t)=\binom{t+2}{2}=\frac12t^2+\frac32t+1$（**2 次多项式，与 $3\mid t$ 无关**） |
| **本工作 `IsPanMagic`** | semi-magic + **两个方向**的断对角都等于线和 | $1$ 当且仅当 $3\mid t$，否则 $0$（**零次**） |

实测（$t=0..9$）：单向 $1,3,6,10,15,21,28,36,45,55$；双向 $1,0,0,1,0,0,1,0,0,1$。
**两者不可互相对照。** 另外注意：BCCG 的单向泛魔**不要求副对角**，所以它与
「magic」**互不包含**——「pandiagonal ⟹ magic」在 BCCG 读法下是假的。

### 5.2 BCCG 的两条结构定理（一般 $n$ 的路线图）

- **定理 1（Ehrhart–Stanley）**：$H_n(t)$ 是 $t$ 的**多项式**，次数 $(n-1)^2$，
  且 $H_n(-n-t)=(-1)^{n-1}H_n(t)$、$H_n(-1)=\dots=H_n(-n+1)=0$。
  $n=4$ 即 9 次；实测 $H_4$ 的 10 阶差分恒为 0 ✓。
- **定理 2**：$M_n,S_n,P_n$ 是**拟多项式**，次数分别为 $n^2-2n-1$、$n^2/2-n/2-2$、
  $n^2-3n+2$，并带相应的互反律恒等式。
- 显式小阶（逐字）：$H_2=t+1$；$M_2=S_2=P_2=\mathbf 1_{2\mid t}$；
  $H_3=3\binom{t+3}{4}+\binom{t+2}{2}$；$M_3=\frac29t^2+\frac23t+1\ (3\mid t)$；
  $S_3=\frac23t+1\ (3\mid t)$ ——**$S_3$ 与本工作 Mission IV 的结果逐字吻合**。
- 定理 1 原文说存在**初等证明**（引其文献 [14]）；若要攻一般 $n$，先找 [14]。

### 5.3 库里缺的关键文献

**最完美幻方（Ollerenshaw–Brée）的核心文献不在本目录**：README 只在「远期」提过名字，
既没有 1998 年 IMA 专著 *Most-perfect Pan-diagonal Magic Squares: Their Construction and
Enumeration*，也没有相关论文或综述。要开这条路必须**先补文献**。

已知事实（供评估用，来自 OEIS A051235 / Royal Society / Nature 1998 书评）：
最完美幻方只存在于 $n\equiv0\pmod 4$；本质不同（Frénicle 标准形）个数为
$n=4$:**48**、$n=8$:**368640**、$n=12$:**22295347200**。
一般公式对 $n$ 的素因子指数做双重求和；核心方法是**构造 + 与 reversible squares 的双射**，
**不需要 Ehrhart 机制**——这一点对本项目的可行性判断很关键。
