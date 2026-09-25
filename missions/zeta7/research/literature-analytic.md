# 与 ζ(7) 正矩行列式方案相邻的文献

检索范围截至 2026-09-24。以下以论文原文、作者稿或期刊正文为依据。结论是：已有方法充分说明“正的 Gram/Hankel 行列式很小”可以怎样服务于无理性证明，但没有一篇为这里的单一常数 ζ(7) 同时给出所需的非零性、整系数归一化及严格胜出的渐近不等式。

## 1. Brown：多参数 Mellin 积分与超限直径（2026）

Francis Brown, *Mellin transforms, transfinite diameter and rational approximations of integrals*, [arXiv:2604.20741（正文）](https://arxiv.org/html/2604.20741)，2026-04-22 提交；[期刊 DOI](https://doi.org/10.1080/10586458.2026.2695605)，*Experimental Mathematics* 2026 在线发表。

论文把参数化 Mellin 积分的多个函数组成模，再把它们的乘积积分排成正定 Gram 矩阵；矩阵行列式由广义 Vandermonde 行列式及多变量超限直径控制。Minkowski 定理随后从清分母后的矩阵抽取非零的整数系数线性形式。第 9 节用 $\mathcal M_{0,5}$ 上五参数的 $\zeta(2)$ 积分做验证案例，**没有给出 $\zeta(7)$ 的无理性结论**。作者还指出，分母估计与实数侧衰减可以因使用整个参数族而分别优化；以 $p$ 进上同调系统解释分母改进仍属研究方向。见[引言的构造与边界](https://arxiv.org/html/2604.20741#S1.SS2)及[第 9 节](https://arxiv.org/html/2604.20741#S9)。

**可迁移处。** 我们的一元 $\mu_7$ 正矩本来就是 Gram 结构，可以尝试扩大整数多项式模，而不是只变动单一 Hankel 维数；对每种模分别证明 Vandermonde/势能上界与行列、列或整个行列式的 $p$ 进分母节省。这里的“多参数”是寻找更好模的启发，并不自动产生更小的 ζ(7) 分母。

**判据核对。** [arXiv 所示 Criterion 1.3 与其前式](https://arxiv.org/html/2604.20741#S1.SS2)之间有量化疑点：前式所得线性形式上界为 $(t_N^2\delta_N)^{1/N}$，但 Criterion 1.3 只写 $t_N^2\delta_N\to0$；后者本身不能保证前者趋零。第 7.5 节 [Lemma 7.8](https://arxiv.org/html/2604.20741#S7.SS5) 按其任意矩阵的字面表述也需要谨慎：令 $\xi=1/2$、$Q_N=\xi I_N$、$d_N=1$，便有 $d_N\det Q_N=\xi^N\in\mathbb Z[\xi]$、正定且趋零，却不能推出 $\xi$ 无理。这不否定论文的具体五参数构造，但不能把两个宽泛表述直接当作本项目的充分条件。可安全使用的 Minkowski 型条件是 $(t_N^2\delta_N)^{1/N}\to0$；论文 [Criterion 1.4 / Corollary 7.3](https://arxiv.org/html/2604.20741#S7.SS3) 的归一化严格小于 $1$，在其常用模满足 $e_n/N_n\to\infty$ 时确能给出这一点。若改走整数行列式多项式路线，假设 $\xi=a/b$ 时还须把多项式的次数造成的 $b^{\deg_X}$ 计入归一化。期刊正文是否已修订上述字面疑点，这次未能核实；此处仅评价所链接 arXiv 文本。

## 2. Brown–Zudilin：$\zeta(5)$ 的 cellular 积分与分母对称（2022／2026 修订）

Francis Brown, Wadim Zudilin, *On cellular rational approximations to $\zeta(5)$*, [arXiv:2210.03391v3（正文）](https://arxiv.org/html/2210.03391v3)。初稿为 2022 年，所核对 v3 于 2026-01-29 上载；称“2025 论文”会掩盖版本差别。

这是 $\mathcal M_{0,8}$ 上五重 cellular 积分。原积分同时含 $1,\zeta(2),\zeta(3)\zeta(2),\zeta(5)$ 等项；通过有几何根据的投影“令 $\zeta(2)$ 为零”，得到 $Q\zeta(5)-P$，并利用阶为 $7!=5040$ 的参数变换群改进分母。[Theorem 1](https://arxiv.org/html/2210.03391v3#S1.Thm1) 给出有效无限列

$$0<\left|\zeta(5)-p/q\right|<q^{-0.86}.$$

作者明确指出指数 $0.86<1$，**不能据此推出 $\zeta(5)$ 无理**；更谈不上 $\zeta(7)$。相比之下，同文完全对称参数的未经群优化的指数约为 $0.77796$，表明分母对称可以实质改善算术侧，但仍未越过无理性阈值。见[周期分解与群作用](https://arxiv.org/html/2210.03391v3#S1)及[对称情形](https://arxiv.org/html/2210.03391v3#S2)。

**可迁移处。** 在我们的 $\mu_7$ 行列式中寻找参数置换或留数表示的恒等式，以证明某些素数幂不必出现在整化因子中；必须对实际的行列式系数证明节省，不能把 $\zeta(5)$ 积分的 $5040$ 阶群原样移植。该文也解释了为什么机械照搬 Apéry–Beukers 的二重、三重积分到更高权困难：高权的周期分解会出现“寄生”周期，消去它们与控制分母、实数衰减须同时完成；这是一项已知障碍，而非不可能性定理。[原文引言](https://arxiv.org/html/2210.03391v3#S1) 对此有明确说明。

## 3. Zudilin：以正矩 Hankel 行列式放宽单个线性形式的要求（2017）

Wadim Zudilin, *A determinantal approach to irrationality*, *Constructive Approximation* **45** (2017), 301–310；[作者预印本 PDF](https://arxiv.org/pdf/1507.05697)，[期刊 DOI](https://doi.org/10.1007/s00365-016-9333-7)。

设 $r_n=a_n\xi-b_n=\int_\gamma z(x)^n\omega(x)$，其中测度为正、$z$ 非常数，并有相容的分母序列。经典线性形式条件为 $\varepsilon\Delta<1$；其 Proposition 2 利用 Hankel 行列式及 Vandermonde 平方，改为 $\varepsilon\Delta^{3/2}/4<1$，并用于重新证明 $\log 3$ 与 $\pi$ 的无理性。正测度直接保证行列式非零；$1/4$ 则反映区间的超限直径。[论文第 1–2 节](https://arxiv.org/pdf/1507.05697)。

**可迁移处。** 这篇与我们的单变量正矩路线在结构上最接近：单项近似失败时，整个正定行列式仍可能足够小。**不能推出的结论：** 其具体 $\varepsilon,\Delta$ 条件只适用于论文的矩型积分及所述分母假设；论文没有建立 $\zeta(7)$ 所需的 $p$ 进整化或胜出的常数。第 6 节的未解决常数例子也强调，行列式衰减可能被分母增长抵消。

## 4. Haynes–Zudilin：不同 ζ 值的 Hankel 行列式（2015）

Alan Haynes, Wadim Zudilin, *Hankel Determinants of Zeta Values*, *SIGMA* **11** (2015), 101；[期刊原文 PDF](https://sigma-journal.com/2015/101/sigma15-101.pdf)，[DOI](https://doi.org/10.3842/SIGMA.2015.101)。

对正整数 $a,b$，他们给出 $H_n=\det_{1\le i,j\le n}\zeta(a(i+j)+b)$ 的衰减上界 $\log|H_n|\le-(a/2)n^2\log n+O(n^2)$。其 Theorem 1 的算术结论是二择一：数列 $\zeta(an+b)$ 中有无限多个无理数，或其中有理值的共同分母超指数增长，即 $q_n^{1/n}\to\infty$。[定理与证明](https://sigma-journal.com/2015/101/sigma15-101.pdf)。

**可迁移处。** 离散测度的 Vandermonde 展开使小行列式与正性、非零性直观且可量化。**边界：** 此矩阵的各项是不同的 $\zeta$ 值；我们则需要所有条目都是同一个 $X=\zeta(7)$ 的有理仿射函数。前者的二择一结论不能挑出 $\zeta(7)$，也不提供我们的整系数多项式归一化。

## 5. Fischler–Sprang–Zudilin：多奇 ζ 值的消元行列式（2018／2019）

Stéphane Fischler, Johannes Sprang, Wadim Zudilin, *Many odd zeta values are irrational*, [2018 年预印本](https://arxiv.org/abs/1803.08905)，*Compositio Mathematica* **155** (2019), 938–952；[作者 PDF](https://www.imo.universite-paris-saclay.fr/~stephane.fischler/zeta.pdf)，[期刊 DOI](https://doi.org/10.1112/S0010437X1900722X)。

论文构造系数相关的多个奇 ζ 线性形式，证明：给定 $\epsilon>0$，充分大的 $s$ 下，$3$ 到 $s$ 之间至少 $2^{(1-\epsilon)\log s/\log\log s}$ 个奇 ζ 值无理。[摘要与定理](https://arxiv.org/abs/1803.08905)。消元环节使用的是广义 Vandermonde 矩阵 $[x_j^{\alpha_i}]$ 的非零性，**不是**由一个固定常数的矩组成的 Hankel 行列式；“Fischler 2018 Hankel 行列式”应与上面两篇区分。

**可迁移处。** 多个相关线性形式及系数消元可启发怎样利用更多独立矩或参数。**边界：** 定理仅保证某些奇 ζ 值无理，既未指明 $\zeta(7)$，也没有补上我们所需的单变量整数多项式估计。

## 对当前证明任务的直接含义

我们的 $\zeta(7)$ 正矩构造已具有解析侧的正性、非零性及势能上界框架；这里最可借鉴的是 Zudilin 2017 的单变量行列式思想、Brown 2026 的模选择与归一化视角，以及 Brown–Zudilin 的群对称分母节省。剩余的实际证明责任仍是：对选择好的矩阵族证明**精确**的 $X=\zeta(7)$ 整系数归一化（包括有理假设下 $\deg_X$ 对分母的影响），并以认证的渐近上界证明归一化后非零行列式趋于零。只得到能量上的负数、未认证数值结果、或只得到 $\det Q_N\to0$，均不足以宣布无理性。
