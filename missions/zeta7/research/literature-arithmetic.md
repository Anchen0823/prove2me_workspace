# 奇 ζ 值的超几何线性形式与分母机制：原始文献核查

核查日期：2026-09-24。本次只整理文献，未扩展或修改现有实验。
以下五份经典来源都**不能推出单独 ζ(7) 无理**；各项区分原文结果与对本项目的推论。
记 d_n=lcm(1,…,n)，(x)_m=x(x+1)…(x+m−1)。

## 1. Rivoal：无限多个奇 ζ 值的维数下界（2000）

**来源**：T. Rivoal，*La fonction Zeta de Riemann prend une infinité de valeurs irrationnelles aux entiers impairs*，C. R. Acad. Sci. Paris 331，267–270。
[作者预印本及全文](https://arxiv.org/abs/math/0008051)。

**核查位置与定理**：Theorem 1；对每个 ε>0，充分大的 m 满足

\[
 \dim_{\mathbb Q}\langle1,\zeta(3),\ldots,\zeta(2m+1)\rangle
 \ge\frac{1-\varepsilon}{1+\log2}\log m.
\]

**方法与公式**：取整数 1≤r<a/2，文中研究

\[
 S_n(1)=\sum_{k\ge0}n!^{a-2r}
 \frac{(k-rn+1)_{rn}(k+n+2)_{rn}}{(k+1)_{n+1}^{a}}.
\]

n 偶、a 奇时，反射对称性消去偶 ζ 系数；Lemma 5 给
d_n^(a−i)P_(i,n)(1)∈Z，包括常数项 i=0。控制线性形式的衰减与系数增长后使用 Nesterenko 判据。

**借鉴／限制**：先证明所需系数消失，再比较整化成本。维数随 m 增长并不指定哪个值无理；不能把这个定理用于固定 ζ(7) 而省去其他系数。

## 2. Ball–Rivoal：完整的无限维证明（2001）

**来源**：K. Ball、T. Rivoal，*Irrationalité d’une infinité de valeurs de la fonction zêta aux entiers impairs*，Invent. Math. 146，193–207。
[作者保存的原文](https://rivoal.perso.math.cnrs.fr/articles/zetaimp.pdf)；[作者出版目录](https://rivoal.perso.math.cnrs.fr/articles.html)。

**核查位置与定理**：Theorem 1 给出奇 ζ 值张成空间的对数级维数下界；Theorem 2 给出某个奇数 j≤169，使 1、ζ(3)、ζ(j) 在 Q 上线性无关。

**方法**：将有理函数求和、奇偶对称性、分母估计、实数渐近和线性无关判据放在同一构造内；结论涉及一整族值。这里不把一般“超几何”与附加的 very-well-poised 因子混同：Rivoal–Ball 的无限多个结果不要求后来分母恒等式中使用的全部额外结构。

**借鉴／限制**：当前单变量行列式已经避免多 ζ 系数的消元问题，但仍须完成整化后衰减比较。Ball–Rivoal 的维数结论不能替代这一比较，也不能作为 ζ(7) 的非有理性证书。

核查说明：作者 PDF 的部分文字层编码异常；上述定理亦与第1项及第5项 §2.2 的作者交叉说明相符，未据乱码抄写新公式。

## 3. Zudilin：ζ(5)、ζ(7)、ζ(9)、ζ(11) 中至少一个无理（2001）

**来源**：W. Zudilin，*One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational*，Russian Math. Surveys 56，774–776。
[期刊原页及英文全文](https://www.mathnet.ru/eng/rm427)。

**定理**：标题中的四个数**至少一个**无理；没有指定是哪一个。

**方法与公式**：对满足原文条件(1)的参数，以 well-poised 有理函数 R_n 的导数构造

\[
 F_n=\frac1{(r-1)!}\sum_{t=0}^{\infty}R_n^{(r-1)}(t).
\]

Lemma 1 保证它只涉及 1、ζ(r+2)、ζ(r+4)、…、ζ(q−2)，且

\[
 d_{m_1n}^{r}d_{m_2n}\cdots d_{m_{q-r}n}\Phi_n^{-1}F_n
 \in\mathbb Z+\sum_{j=r+2,r+4,\ldots,q-2}\mathbb Z\zeta(j).
\]

其中 m_j=max{η_r,η_0−2η_(r+1),η_0−η_1−η_(r+j)}。
原文取 r=3、q=13、η_0=91、η_1=η_2=η_3=27、η_j=25+j（4≤j≤13）。
其衰减常数 C_0≈227.58019641 大于整化成本 C_1≈226.24944266。

**借鉴／限制**：真正产生严格正差的是解析估计与公因子 Φ_n 的共同作用。形式里仍同时存在四个 ζ 值；上述正差不能改写为单独 ζ(7) 的结果。

## 4. Zudilin：一般 p-adic 公因子机制（预印本2002；期刊2004）

**来源**：W. Zudilin，*Arithmetic of linear forms involving odd zeta values*，J. Théor. Nombres Bordeaux 16，251–291。
[期刊原文](https://www.numdam.org/articles/10.5802/jtnb.447/)；[作者预印本](https://arxiv.org/abs/math/0206176)。

**核查位置与定理**：§§7–8，Lemmas 15–19、Proposition 5、Theorem 3；Theorem 3 完整证明前述四数结论。

**方法与公式**：将 Γ 比值拆成整数值“基本块”，逐一估计导数／留数的 p-adic 阶。对所有极点索引取共同下界，而非选择最有利的一项：

\[
 \nu_p=\min_k\nu_{k,p},\quad
 \Phi=\prod_{\sqrt{h_0}<p\le m_{q-r}}p^{\nu_p},\qquad
 \varphi(x)=\min_{0\le y<1}\varphi_0(x,y).
\]

ν_(k,p)、φ_0 都由阶乘 valuation 的 floor 差构成。Lemma 19 的整性涵盖**常数项及所有 ζ 系数**；素数定理把 log Φ 的增长转化为分段函数积分。
论文还用超几何变换／参数置换组织部分构造的额外整除信息。

**借鉴／限制**：适合借鉴的是“整个系数向量的共同 valuation”与保留正的公因子收益。当前 Hankel determinant 不是该文的线性形式；其 Φ 不能直接照搬，必须重新证明对 determinant 每个系数都有效。

## 5. Krattenthaler–Rivoal：分母猜想与隐藏消去（预印本2003；期刊2007）

**来源**：C. Krattenthaler、T. Rivoal，*Hypergéométrie et fonction zêta de Riemann*，Memoirs AMS 186，no.875。
[作者全文](https://rivoal.perso.math.cnrs.fr/articles/kratriv.pdf)；[预印本记录](https://arxiv.org/abs/math/0311114)。

**定理与公式**：对原文(2.10)–(2.14)定义的对称导数级数系数，Theorem 1 证明

\[
 d_n^{A-l-1}p_{l,n}((-1)^A)\in\mathbb Z\quad(1\le l\le A),
 \qquad 2d_n^{A+C-1}p_{0,C,n}((-1)^A)\in\mathbb Z.
\]

即比逐项粗估节省一份 d_n；**一般常数项定理保留因子2**。
方法是 Andrews 的单重和—多重和变换，再用基本块的整性揭示项间消去。

**借鉴／限制**：§17.1 明确没有证明所有 Zudilin 非对称级数的对应猜想；其已知 Φ 公因子还可能比节省一份 lcm 更强。当前构造应同时研究整除公因子和项间消去，不能只改一个分母指数，更不能从“分母猜想已证明”的标题推得 ζ(7) 无理。

## 对当前项目的技术判断（本项目推论）

这条文献路线有两个相互独立的关口：**系数支持**必须只含目标常数，或能付得起消元代价；**完整整化成本**必须小于非零线性形式／多项式的衰减。
奇偶对称性只自动消掉一种奇偶性，不能自动消掉 ζ(5)、ζ(9)、ζ(11)。
现有单变量 determinant 构造跨过了形式上的系数支持关口，仍卡在第二关。

真正值得带回的研究问题是：能否找到保持同一个 determinant 的变换或另一种整性表示，
显露逐项局部估计遗漏的统一公因子？上述论文提供范式，但没有给出现成定理可直接回答。
这是一项待证明的结构问题；数值 content 增大或少量样本整除都不能代替全参数证明。

本笔记没有以有限范围失败断言该路线不可能，也没有把旧论文的未解决问题当作2026年的完整最新状态。
