# ζ(9) 第四轮：尾部移位最高系数的全序列非零性

设 \(n\ge2\) 为偶数，
\[
\rho_n=\sum_{j=0}^n(-1)^j
 \binom nj^9\binom{n+j}{n}\binom{2n-j}{n},
\qquad A_{n,D}=\kappa_D\rho_n,
\tag{1}
\]
其中第三轮固定权重给出 \(\kappa_6=6531840\)、\(\kappa_8=92897280\)。这里证明
\[
\boxed{\operatorname{sgn}(\rho_n)=(-1)^{n/2},\quad
 \rho_n\ne0\text{ 对全部偶数 }n\ge2.}
\tag{2}
\]
这填补第三轮尾部移位分支“只在六个有限案例检查 \(A\ne0\)”的缺口。它**不**证明 primitive 形式趋零。

## 1. Binomial 幂多项式的负实根

定义
\[
 G_n(z)=\sum_{j=0}^n\binom nj^2z^j.
\]
由 Rodrigues 公式及 Leibniz 法则得到显式展开
\[
 P_n(u)=2^{-n}\sum_{j=0}^n\binom nj^2
       (u-1)^{n-j}(u+1)^j.
\]
代入 \(u=(1+z)/(1-z)\)，并把求和指标改为 \(n-j\)，立即得到恒等式
\[
 G_n(z)=(1-z)^n P_n\!\left(\frac{1+z}{1-z}\right).
\tag{3}
\]
Legendre 多项式 \(P_n\) 的 \(n\) 个零点简单且位于 \((-1,1)\)，所以式 (3) 把它们映为 \(G_n\) 的 \(n\) 个简单负实根。可核对的权威出处为 [NIST DLMF §18.2 的正交多项式零点定理](https://dlmf.nist.gov/18.2)。

令 \(\mathcal T_n(z^j)=\binom nj z^j\)（\(0\le j\le n\)）。其有限稳定性符号为
\[
 \mathcal T_n[(z+w)^n]
 =\sum_{j=0}^n\binom nj^2z^jw^{n-j}
 =w^nG_n(z/w)
 =c\prod_{i=1}^n(z+r_iw),
\tag{4}
\]
其中 \(r_i>0\)。若 \(z,w\) 均在上半平面，每个 \(z+r_iw\) 仍在上半平面，因此此符号实稳定。[Borcea–Brändén, *Pólya–Schur master theorems for circular domains and their boundaries*, Theorem 2](https://arxiv.org/pdf/math/0607416) 的有限次数判据说明 \(\mathcal T_n\) 保持次数至多 \(n\) 的实根性。对 \((1+z)^n\) 连用八次，便得到
\[
 F_n(z)=\sum_{j=0}^n\binom nj^9z^j
\tag{5}
\]
全部零点为实数。其所有系数都严格为正，常数项非零，故零点必全为负；此处尚未要求它们简单。

## 2. 两组线性微分算子消除重根

记 \(\theta=z\,d/dz\)。在单项式 \(z^j\) 上，
\[
 \frac1{n!}\prod_{k=1}^n(\theta+k)
 \quad\text{乘以}\quad\binom{n+j}{n},
\]
\[
 \frac1{n!}\prod_{k=n+1}^{2n}(k-\theta)
 \quad\text{乘以}\quad\binom{2n-j}{n}.
\tag{6}
\]
因此对 \(F_n\) 先后应用式 (6) 的算子，恰得到
\[
 H_n(z)=\sum_{j=0}^n
 \binom nj^9\binom{n+j}{n}\binom{2n-j}{n}z^j,
\qquad H_n(-1)=\rho_n.
\tag{7}
\]

以下根保持性不依赖外部定理。若 \(f(z)\) 的所有根为 \(-r_i<0\)，不同的 \(r_i\) 按升序排列、重数为 \(e_i\)，则对任何 \(k>0\)，\((\theta+k)f\) 在每个旧根的重数恰减一。其余新根由
\[
 y\sum_i\frac{e_i}{y-r_i}=-k,\qquad y=-z>0
\tag{8}
\]
确定。左侧在每个无极点区间严格递减，因为导数是
\(-\sum_i e_ir_i/(y-r_i)^2<0\)。它在 \((0,r_1)\) 及每个 \((r_i,r_{i+1})\) 中各取一次 \(-k\)，新根因此严格为负、简单且不同于旧根。特别地，重复应用 \(n\) 个 \(\theta+k\) 后，所得次数 \(n\) 的多项式具有**简单负根**。

若 \(f\) 次数为 \(n\)，定义倒数多项式 \(f^\vee(z)=z^nf(1/z)\)。恒等式
\[
 ((k-\theta)f)^\vee=(\theta+k-n)f^\vee
\tag{9}
\]
表明，当 \(k>n\) 时，\(k-\theta\) 也保持简单负根：倒数操作保持该性质，而右侧是正参数的 \(\theta+(k-n)\)。式 (6) 的第二组因子均符合 \(k>n\)。故 **\(H_n\) 的 \(n\) 个根全部简单且为负**。

## 3. 对称性给出严格符号

式 (7) 的系数在 \(j\leftrightarrow n-j\) 下不变，因此
\(H_n(z)=z^nH_n(1/z)\)，且首、末系数均为正。其负根按倒数成对：\(-r\) 与 \(-1/r\)。唯一可能的固定负根是 \(-1\)，但 \(n\) 为偶数且全部根简单；若存在单个 \(-1\)，其余根只能成对，度数便为奇数，矛盾。于是 \(H_n(-1)\ne0\)。每对根在 \(-1\) 处贡献
\[
 (-1+r)(-1+1/r)=-\frac{(r-1)^2}{r}<0.
\]
共有 \(n/2\) 对，首项系数为正，式 (2) 随即成立。因此 \(A_{n,D}\) 对所有偶数 \(n\) 都严格非零，且符号 \((-1)^{n/2}\)。

## 4. 指数上界和 primitive 乘数的下界

对偶数 \(n\)，\(\binom nj\) 在 \(j=n/2\) 最大。另令
\(b_j=\binom{n+j}{n}\binom{2n-j}{n}\)。直接计算
\[
 \frac{b_{j+1}}{b_j}
 =\frac{(n+j+1)(n-j)}{(j+1)(2n-j)};
\]
分子减分母为 \(n(n-1-2j)\)。所以 \(b_j\) 亦在中心 \(j=n/2\) 最大。三角不等式给出全 \(n\) 的显式界
\[
 0<|\rho_n|
 \le(n+1)\binom n{n/2}^{9}
          \binom{3n/2}{n}^{2}.
\tag{10}
\]
Stirling 公式遂得
\[
 \log|A_{n,D}|
 \le (7\log2+3\log3)n+O(\log n)
 =(\log3456)n+O(\log n).
\tag{11}
\]
\(\kappa_D\) 与 \(n\) 无关，吸收到 \(O(1)\)。这是**上界**，不声称已确定 \(|A_n|\) 的真实指数率。

设尾部移位原始形式为 \(A_{n,D}\zeta(9)+B_{n,D}\)，将
\(B_{n,D}=b_n/q_n\) 写成最简分数，\(q_n>0\)。因 \(A_{n,D}\in\mathbb Z\) 且已证非零，最小公分母为 \(q_n\)，而
\(\gcd(q_nA_{n,D},b_n)=\gcd(A_{n,D},b_n)\le|A_{n,D}|\)。
正的 primitive 乘数满足
\[
 M_n=\frac{q_n}{\gcd(A_{n,D},b_n)}
 \ge\frac{q_n}{|A_{n,D}|},
\quad
 \liminf\frac{\log M_n}{n}
 \ge\liminf\frac{\log q_n}{n}-\log3456.
\tag{12}
\]
式 (12) 是后续研究分母下界时可直接使用的扣除项；本笔记**没有**证明 \(q_n\) 的所需指数下界。若脱离偶数 \(n\) 或改用其他最高系数而出现 \(A=0\)，上述除以 \(|A|\) 的推理不能使用，应单独按有理常数形式处理。

一个便于量化的条件推论是：第三轮尾部解析给出
\(\lim n^{-1}\log|L_n|=f(x_\ast)>f(1)=3\log3-20\log2\)。
由于
\[
 \log3456-f(1)=27\log2,
\]
若将来能证明 \(\liminf n^{-1}\log q_n>27\log2\)，则式 (12) 立即推出 primitive 值的指数率严格为正。这里的门槛只是**条件**，绝非已证的分母增长率。
