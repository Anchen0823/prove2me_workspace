# ζ(9) 第三轮：分数移位、固定消元及全素数证书

本笔记独立证明 D=6、8 构造的代数支持和安全整化，不引用具有额外参数限制的 FSZ 整性定理。`d_N` 始终指 `lcm(1,...,N)`；其对数为 Chebyshev 的 `psi(N)`，不是 `theta(N)`。

## 1. 构造、约分和九阶残数

设 D 为 6 或 8，n 为不小于 2 的偶数，m 为非负整数，满足
\[
 2Dm\le(10-D)n+7.
\]
记
\[
 Q(t)=\prod_{j=0}^n(t+j),\quad F=\frac{n!^{10-D}}{m!^{2D}},\quad
 R(t)=F\frac{\prod_{\ell=-Dm}^{D(n+m)}(t+\ell/D)}{Q(t)^{10}}.
 \tag{1}
\]
这里只约去分子中 `ell=0,D,...,Dn` 对应的一份 Q。负整数零点和大于 n 的整数零点仍在分子内。余下极点为 `0,-1,...,-n`，阶数恰为 9。

原分子次数为 `D(n+2m)+1`，因此次数差为
`2Dm-(10-D)n-9<=-2`。此数为奇数，故实际不超过 −3，所有本笔记中的移位级数绝对收敛。参数域还蕴含 `m<=n/2`：D=6 时对 n>=4 由 `(4n+7)/12<n/2+1` 及整数性得出，n=2 可直接检查；D=8 更直接。

写部分分式
\[
 R(t)=\sum_{j=0}^n\sum_{s=1}^9\frac{c_{j,s}}{(t+j)^s}.
\]
令 `K=D(n+2m)`。在原分子中只去掉 `ell=Dj` 的一阶零点，可得到特别简单的最高残数公式：
\[
 \boxed{C_j:=c_{j,9}
 =F\frac{(D(j+m))!\,(D(n+m-j))!}
 {D^K j!^{10}(n-j)!^{10}}>0.}
 \tag{2}
\]
分子负因子的个数是 `D(j+m)`，为偶数；原分母非零因子的幂为 10，所以符号为正。这一同号结论不依赖数值检查。

同时，`D^K C_j` 为整数。具体分解为
\[
 D^KC_j=\binom nj^{10-D}\binom{j+m}{m}^{D}\binom{n-j+m}{m}^{D}
 \frac{(D(j+m))!}{(j+m)!^D}
 \frac{(D(n-j+m))!}{(n-j+m)!^D}.
 \tag{3}
\]
最后两个因子都是多项式系数意义下的 multinomial 整数。这说明最高残数的分母只可能含整除 D 的素数，但不说明低阶残数或移位常数具有同样性质。

## 2. 移位支持与固定权重的严格消元

对 `a=1,...,D`，定义
\[
 r_a=\sum_{k=0}^{\infty}R(k+a/D).
\]
`a/D>0`，不存在从极点 `t=0` 开始求和的问题。m=0 时 k=0 项必须保留；m>0 时前 m 项为零，因为 `1/D,2/D,...,m` 是分子零点。

反射恒等式 `R(-n-t)=-R(t)` 给出
\(c_{n-j,s}=(-1)^{s+1}c_{j,s}\)。令 \(\rho_s=\sum_jc_{j,s}\)，则偶数 s 的 rho 为零，且无穷远的 `t^-1` 系数给出 \(\rho_1=0\)。所以
\[
 r_a=B_a+\sum_{s\in\{3,5,7,9\}}\rho_s\zeta(s,a/D),
\]
\[
 B_a=-\sum_{j=0}^n\sum_{s=1}^9c_{j,s}
       \sum_{k=0}^{j-1}(k+a/D)^{-s}\in\mathbb Q.
 \tag{4}
\]
处理 s=1 时必须先有限截断，再用 `rho_1=0` 消去共同发散项，不能写成 `0·ζ(1,a/D)`。空和 `j=0` 为零。

对 d 为 D 的正除数，定义
\[
 S_d=\sum_{a=1}^d r_{aD/d}.
\]
Hurwitz 的乘法恒等式直接由绝对收敛级数分组得到：
\(\sum_{a=1}^d\zeta(s,a/d)=d^s\zeta(s)\)。因此
\[
 S_d=B_d^*+\sum_{s=3,5,7,9}d^s\rho_s\zeta(s),\qquad
 B_d^*=-\sum_{j,s}c_{j,s}d^sH_{dj}^{(s)}.
 \tag{5}
\]

以下固定整数权重消去 s=3、5、7：

| D | 除数 d 的顺序 | 权重 lambda_d | kappa_D=sum lambda_d d^9 |
|---:|---|---|---:|
| 6 | 1,2,3,6 | −7776,1701,−224,1 | 6531840 |
| 8 | 1,2,4,8 | −32768,5376,−168,1 | 92897280 |

证明及防止抄错的方法：令 `x_d=d^2`，取
\[
 \lambda_d=\frac{D^3\prod_{e\mid D,e<D}(D^2-e^2)}
 {d^3\prod_{e\mid D,e\ne d}(d^2-e^2)}.
\]
四点 Lagrange 插值的最高次项系数恒等式给出前三个矩为零，第四个矩为
\[
 \kappa_D=D^3\prod_{e\mid D,e<D}(D^2-e^2)>0.
\]
从而
\[
 \boxed{L:=\sum_{d\mid D}\lambda_dS_d=A\zeta(9)+B,\quad
 A=\kappa_D\rho_9>0,\quad B=\sum_d\lambda_dB_d^*.}
 \tag{6}
\]
因此最终多项式不会因为反射、固定权重或最高系数相消而恒等于零。它在 ζ(9) 处是否为零仍是另一个问题：`A>0` 单独不等于 `L!=0`。

## 3. 不需要最终 gcd 的安全有限证书

令
\[
 H=d_{D(n+m)}/D,\qquad J=d_{Dn}/D.
\]
二者都是整数，且 `J|H`。在极点 `z=t+j` 处，将已经约分的分子每个因子除以其非零常数项，得到
\[
 z^9R(z-j)=C_j\prod_{\ell\notin\{0,D,\ldots,Dn\}}
 \left(1+\frac{Dz}{\ell-Dj}\right)
 \prod_{k\ne j}\left(1+\frac z{k-j}\right)^{-9}.
 \tag{7}
\]
所有 `ell-Dj` 的绝对值不超过 `D(n+m)`；H 同时整化 `D/(ell-Dj)` 和 `1/(k-j)`。负整数幂的二项式系数仍为整数，所以
\[
 H^{9-s}c_{j,s}/C_j\in\mathbb Z.
 \tag{8}
\]
另一方面，移位常数的每个项为 `D^s/(Dk+a)^s`，其中 `1<=Dk+a<=Dn`；因此 J 的 s 次幂整化它。这里的 D 因子不能漏掉，也不能把上限 Dn 无证明改成 n。

由式 (3)、(8)，一个完全不取公因子的有限证书为
\[
 \boxed{T_0=D^K H^8J.}
 \tag{9}
\]
它整化全部移位系数向量以及最终 (A,B)。事实上对每一阶 s，所需的 `H^(9-s)J^s` 都整除 `H^8J`，商为 `(H/J)^(s-1)`。

可只用显式 factorial floors 改进，而不需要计算最终系数的 gcd。对任意素数 p，定义
\[
 \nu_p=\min_{0\le j\le n}\big[(10-D)v_p(n!)-2Dv_p(m!)
 +v_p((D(j+m))!)+v_p((D(n+m-j))!)
 -10v_p(j!)-10v_p((n-j)!)-K v_p(D)\big].
 \tag{10}
\]
它恰为 `min_j v_p(C_j)`，可能为负。令
\[
 v_p(T_{\rm local})=8v_p(H)+v_p(J)-\nu_p.
 \tag{11}
\]
只需遍历 `p<=D(n+m)`，其余指数为零。式 (8) 证明 `T_local` 整化全部系数。负指数合法，应原样保留，不能为了把乘子写成整数而截断。

上述证明包括所有小素数，尤其 p|D；在此处 `v_p(H)=floor(log_p(D(n+m)))-v_p(D)`，不能删去后项。

## 4. p 不整除 D 时更强的局部 Taylor 引理

可以不使用 FSZ 的参数定理，直接证明
\[
 \boxed{p\nmid D\Longrightarrow d_n^{9-s}c_{j,s}\in\mathbb Z_p.}
 \tag{12}
\]
先用如下初等引理：若 `x in Z_p`，则对 `0<=q<=n`，多项式 `binom(x+z,q)` 的第 h 阶 Taylor 系数被 `d_n^h` 整化。Vandermonde 恒等式把它写成
`sum_{k=0}^q binom(x,q-k)binom(z,k)`。前一因子 p 整；后一因子用
\[
 \binom zk=\frac{(-1)^{k-1}z}{k}\prod_{a=1}^{k-1}(1-z/a)
\]
展开，每个 h 阶项至多有 h 个属于 `1,...,n` 的分母。`binom(x,q-k)` 的 p 整性可由整数 x 的稠密性及多项式连续性得到。

为应用该引理，设 `G_0=n!/Q`，
\[
 U_-=(n!/m!)(t-m)_m/Q,\qquad
 U_+=(n!/m!)(t+n+1)_m/Q,
\]
\[
 V_a=(t-m+a/D)_{n+2m}/(m!^2Q)\quad(1\le a<D).
\]
构造有精确的九因子分解
\[
 R=G_0^{8-D}U_-U_+\prod_{a=1}^{D-1}V_a.
 \tag{13}
\]
`G_0,U_-,U_+` 是具有整数残数的简单极点真分式（使用 `m<=n`），其 `z` 乘积在每个极点处的 h 阶 Taylor 系数被 `d_n^h` 整化。虽然 `V_a` 可以有多项式部分，却有局部恒等式
\[
 zV_a(z-j)=zG_0(z-j)
 \binom{z-j-1+a/D}{m}
 \binom{z-j+n+m-1+a/D}{m}
 \binom{z-j+n-1+a/D}{n}.
\]
当 p 不整除 D 时，三个上指标在 `z=0` 时都 p 整，且 m<=n；应用前述引理及乘积法则即可得到式 (12)。这一步并没有声称移位常数也被 `d_n^9` 整化。

有限实现可以逐阶合并式 (8) 与式 (12)。令 `e=v_p(d_n)`、`h=v_p(H)`、`j_0=v_p(J)`。对 p 不整除 D，定义
\[
 \gamma_s=\max(\nu_p-(9-s)h,\ -(9-s)e),
 \qquad v_p(T_{\rm refined})=\max_{1\le s\le9}(s j_0-\gamma_s).
 \tag{14}
\]
对 p|D，仍使用式 (11)。这严格覆盖所有 PF 系数和移位常数，且不劣于式 (11)。这里的 max 来自两个已经证明的局部下界，不能把它理解为任意裁剪估值。

## 5. 统一渐近成本

这一节给的是有效乘子的成本，不是 primitive 乘子的下界。固定有理数 `alpha=m/n>=0`，沿合法的偶数 n 序列取整数 m。

对于 p|D，阶乘估值的一次项全部抵消，且误差一致为 `O_D(log n)`，因此
\[
 \nu_p=-D(n+2m)v_p(D)+O_D(\log n).
 \tag{15}
\]
小素数 `p<=sqrt(D(n+m))` 中不整除 D 的总贡献是 `o(n)`：由式 (3) 在 j=0 的 binomial/multinomial 分解，每个估值非负且至多 `O_D(log_p n)`。

当 `p^2>D(n+m)` 时只剩一层 factorial floors。令 `r=n mod p`、`s=m mod p`。直接消去整数部分后得到精确有限公式
\[
 \boxed{\nu_p=\min_{0\le u\le r}
 \left(\left\lfloor\frac{D(u+s)}p\right\rfloor+
       \left\lfloor\frac{D(r-u+s)}p\right\rfloor\right).}
 \tag{16}
\]
证明：`u<=r` 的指标可直接取 `j=u`；`u>r` 时，把第二个余数写成未经模约化的 `r-u`，估值恰为
\[
 10+\lfloor D(u+s)/p\rfloor+\lfloor D(r-u+s)/p\rfloor.
\]
若改用非负余数 `r-u+p`，同一式子的前项应写成 `10-D`，不能误写为 10。使用未经模约化的版本时，两项 floor 的实数自变量之和始终为 `D(r+2s)/p`；其 floor 和最多相差 1，因此额外的 10 不可能产生较小值。式 (16) 不把连续最小值冒充离散最小值。

定义有界周期函数
\[
 \phi_D(x,y)=\min_{0\le z\le\{x\}}
 [\lfloor D(z+\{y\})\rfloor+
  \lfloor D(\{x\}-z+\{y\})\rfloor],
\]
以及
\[
 \Gamma_D(\alpha)=\int_0^\infty\phi_D(x,\alpha x)\frac{dx}{x^2}.
 \tag{17}
\]
`alpha<=1/2` 时积分在 `x<1/D` 没有支持：取 `z={x}/2` 即可。因此零点附近不发散。

有
\[
 \frac1n\sum_{p\nmid D}\nu_p\log p\longrightarrow\Gamma_D(\alpha).
 \tag{18}
\]
证明的有限化步骤如下：在 `p/n>=epsilon` 的范围，x 属于一个固定紧区间，涉及的 floor 边界有限。避开这些边界的任意小邻域，式 (16) 的格点步长 `1/p` 趋零，连续最小值可在一个具有统一正长度的区间实现，因而离散最小值最终相同。在有限个常值区间上用素数定理；边界邻域的素数贡献由其总长度控制。最后 `p/n<epsilon` 的误差为 `O_D(epsilon n)`，令 epsilon 趋零。小素数已另外控制。

式 (11) 的渐近成本为
\[
 \lim\frac{\log T_{\rm local}}n
 =D(1+2\alpha)\log D+8D(1+\alpha)+D-\Gamma_D(\alpha).
 \tag{19}
\]
对于式 (14)，大素数 `p<=Dn` 的指数为 `9-nu_p`；`p>Dn` 时取 `j=n/2` 可知 `nu_p=0`（因为 `m<=n/2`），改进后的指数为 0。因此
\[
 \boxed{\lim\frac{\log T_{\rm refined}}n
 =D(1+2\alpha)\log D+9D-\Gamma_D(\alpha).}
 \tag{20}
\]
小素数处的合并差异是 `o(n)`。这些公式覆盖 alpha=0，不要求 m>0。

## 6. primitive 比较与尚未闭合的障碍

对式 (6) 的非零有理向量 (A,B)，令 q 为两个分母的 lcm，g 为 `(qA,qB)` 的 gcd；正的 primitive 乘子为 `mu=q/g`。任何已证有效乘子 T 都满足
\[
 T/\mu\in\mathbb Z_{>0},\qquad \log(T/\mu)/n\ge0.
\]
因此式 (9)、(11)、(14) 都可以与精确 primitive 结果作有限比较；这些证书不要求事先知道最终 gcd。更好的证书不会改变同一有理直线上的 primitive 多项式。

必须保留的缺口：式 (15) 是每个最高残数及其最小估值的结论，不能直接推出
`v_p(sum_j C_j)=-K v_p(D)+O(log n)`。虽然所有 C_j 在实数意义下为正，它们在 p 进意义下仍可能相消。尚未证明这种相消只有 `O(log n)`。即使以后控制了这项相消，也不能仅由 p|D 处的估值推出正有理数 primitive 乘子的实数下界：该乘子还可能在其他素数处有分母，抵消其分子的实数大小。必须同时控制这些负估值，或另证完整的实数下界。目前仍未得到 primitive 乘子不指数趋零的统一结论。因此即使分析侧证明固定正 alpha 的原始 L 指数增长，也不能仅凭此或有限实验宣告所有 primitive 序列不可能衰减。

完整有效结论是：单 ζ(9) 支持严格成立，A 恒为正，存在覆盖所有素数和移位常数的显式有限证书及其渐近成本。无理性证明仍需最终 primitive/有效整数化形式的非零衰减；本笔记不作该结论。

## 7. 第二轮函数的 tail-shift 附支

此附支使用另一个函数，不能套用式 (2) 的正残数结论。设
\[
 R_n^{\rm old}(t)=\frac{n!^7(t-n)_n(t+n+1)_n}{Q(t)^9},\qquad
 r_a^{\rm tail}=\sum_{k=n}^{\infty}R_n^{\rm old}(k+a/D).
\]
仍令 D=6、8，并用同一组固定整数权重。其最高残数是
\[
 C_j^{\rm old}=(-1)^j\binom nj^9\binom{n+j}{n}\binom{2n-j}{n},
\]
并不同号。反射和无穷远恒等式仍消去偶阶与一阶的 ζ 系数；尾部起点只把常数项中的截断长度从 j 改成 `j+n`。

第二轮独立简单极点因子证明已经给出
`d_n^(9-s)c_(j,s)^old in Z`。令
\[
 E_{\rm tail}=d_{2Dn}/D.
\]
因为 `D·d_n` 整除 `d_(2Dn)`，有 `d_n|E_tail`。尾部常数中每个分母为 `Dk+a<=2Dn`，因此 `E_tail^s` 整化相应的 s 次移位调和和。于是
\[
 \boxed{T_{\rm tail}=E_{\rm tail}^9=(d_{2Dn}/D)^9}
 \tag{21}
\]
整化全部系数，当然也整化固定权重后的单 ζ(9) 形式。更粗的 `d_(2Dn)^9` 也成立；两者只差固定因子 `D^9`，没有额外的指数 D 因子。

式 (21) 的渐近成本是 `18D`。这一粗证书没有利用移位常数之间的相消；它的成本大于分析侧原始形式约 `-10.43` 的率，意味着这个证书不足以完成无理性判据，而不是证明 primitive 序列不能衰减。此附支的 `rho_9!=0` 必须独立核验，不能引用第 1 节的残数同号论证。

## 8. 有限独立审计及复运行

`../scripts/certificate.py` 的有限证书只使用参数、阶乘估值及已证局部引理，不读取最终 primitive gcd 来决定乘子。已完成：

- 30 个合法小参数案例的全部素数 floors、最高残数闭式及式 (16) 检查。
- 25 个 dense-zero 案例：逐个 PF 系数检查式 (8)、(12)，核对正最高残数、反射、固定消元；对每一个移位常数及最终 (A,B) 检查三种证书整性，并核对与精确 primitive 乘子的正整数比例。
- 6 个 tail-shift 案例：核对交替符号最高残数、`d_n^(9-s)` 的逐系数整性，以及式 (21) 对全部移位常数和最终系数的整性。

所有检查通过，记录在 `../verification/arithmetic-audit.json`，包含来源 artifact 哈希、输入索引哈希、脚本哈希及每个素数的有限指数。浮点对数只作报告用途。复运行：

```powershell
python -B missions/zeta9/round3/scripts/certificate.py --audit-index missions/zeta9/round3/verification/shift-results.jsonl --tail-index missions/zeta9/round3/verification/tail-shift-results.jsonl --output missions/zeta9/round3/verification/arithmetic-audit.json
```

证书仍明显偏粗。例如 `D=6,n=24,m=8` 的改进证书 `log(T)/n≈54.62565625`，与 primitive 乘子的 gap 为 `≈35.54878588`；`D=8,n=24,m=3` 对应为 `≈75.29707926` 和 `≈52.58225499`。这些有限 gap 是精确正整数比例的浮点表示，不是渐近下界。

算术代理还独立核对了本轮解析笔记中的 Stirling 幅度、m=0 首项控制、精确次数端点的 `n^(3/2)` 剖面及可积包络，未发现可见缺口；这些实侧结论和上面未完成的 primitive 下界保持区分。
