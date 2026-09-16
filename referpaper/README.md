# 幻方（Magic Squares）文献库

本目录收录幻方形式化工作所依据的原始文献。所有 PDF 均下载自 arXiv / 作者主页，
用于核对定理陈述、边界条件与记号约定。

## 一、计数理论主线（Ehrhart / 多胞体）

| 文件 | 文献 | 核心内容 |
|---|---|---|
| `Beck-Cohen-Cuomo-Gribelyuk - The number of magic squares, cubes and hypercubes (2003).pdf` | M. Beck, A. Cohen, J. Cuomo, P. Gribelyuk, *Amer. Math. Monthly* **110** (2003), 707–717；arXiv:math/0201013 | 定义 $H_n(t)$（半幻方）、$M_n(t)$（幻方）、$P_n(t)$（泛魔）、$S_n(t)$（对称幻方）；证明 $H_n$ 是 $n^2-2n+1$ 次多项式、$M_n$ 是 $(n-1)^2-2$ 次拟多项式；给出 $M_3$ 的 MacMahon 公式。**本工作定义模块 `Def_MagicSquares` 的记号基准。** |
| `Beck-Zaslavsky - An enumerative geometry for magic and magilatin labellings (2006).pdf` | M. Beck, T. Zaslavsky, *Ann. Comb.* **10** (2006) | 幻标号与魔标号的几何枚举框架，把计数函数统一到「带符号图 + 内插」的拟多项式理论。 |
| `Beck-Zaslavsky - Six little squares and how their numbers grow (2010).pdf` | M. Beck, T. Zaslavsky (2010) | 六个 $2\times2$–$3\times3$ 小方块的计数，含半幻方/幻方在小阶时的显式拟多项式，给出 $H_3(t)$ 与 $M_3(t)$ 的封闭形式。 |
| `Beck-vanHerick - Enumeration of 4x4 magic squares (2011).pdf` | M. Beck, T. van Herick, *Math. Comp.* **80** (2011)；arXiv:0907.3188 | $4\times4$ 弱幻方计数 $M_4(t)$，维度 9 的拟多项式（周期 6），是「小阶显式化」路线的代表作。 |
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
