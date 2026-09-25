# ζ(9) 第四轮：最高系数非零与大素数分母障碍

2026-09-24。**仍未证明 ζ(9) 无理。本轮完成了一项无穷序列引理，并将当前尾部移位分支的有限失败认证扩大到 n=384。**

最重要的两项进展：

1. 证明本构造的 ζ(9) 系数对全部正偶数 n 非零，且其符号为 $(-1)^{n/2}$，填补第三轮的一个明确缺口。
2. 找到足以单独压过解析衰减的大素数分母。无需生成巨大常数项，就严格证明十个候选的 primitive 整数形式远大于 1。

## 1. 本轮研究的精确范围

固定 $D\in\{6,8\}$、正偶数 $n$、$m=n$，使用第三轮尾部分支：
$$
R_n(t)=n!^7\frac{(t-n)_n(t+n+1)_n}{\prod_{j=0}^n(t+j)^9},
\qquad
r_a=\sum_{k=n}^{\infty}R_n(k+a/D).
$$
按第三轮的固定权重 $w_d$ 组成
$$
L_{n,D}=\sum_{d\mid D}w_d\sum_{a=1}^d r_{aD/d}
=A_{n,D}\zeta(9)+B_{n,D}.
$$
所有级数取样点都大于 n。此前已证明形式仅含 $1,\zeta(9)$，且对充分大的偶数 n，$L_{n,D}<0$，其对数指数为
$$
f(x_*)\quad\text{其中}\quad
f(x)=10x\log x+(x+2)\log(x+2)
 -(x-1)\log(x-1)-10(x+1)\log(x+1).
$$
峰 $x_*>1$ 唯一，原始形式指数衰减。此前的 $f(x_*)<-10.43$ 是上界，不能当成下界使用。本轮的障碍证明只需
$$
f(x_*)>f(1)=3\log3-20\log2.
$$

本报告的有限与条件性障碍仅针对这个具体分支，不排除其他零点布局、其他 m/n 或其他 ζ(9) 构造。

## 2. 已证：ζ(9) 系数永不消失

最高残数给出
$$
C_j=(-1)^j\binom nj^9\binom{n+j}{n}\binom{2n-j}{n},
\qquad
A_{n,D}=\kappa_D\rho_n,\quad \rho_n=\sum_{j=0}^n C_j,
$$
其中 $\kappa_6=6531840$，$\kappa_8=92897280$。本轮证明
$$
\boxed{\operatorname{sgn}(\rho_n)=(-1)^{n/2},\qquad
A_{n,D}\ne0\quad\text{对全部正偶数 }n.}
$$

证明不依赖有限样本：先利用 Legendre 多项式的零点和保持实根的线性算子，证明
$\sum_j\binom nj^9z^j$ 只有负实根；再施加两组明确的微分算子，乘上另外两个二项式系数，同时消除重根。所得多项式系数对称、负根简单且成倒数对，因此偶数次数时 −1 不可能是根，并给出上述符号。

使用的外部输入为 [Borcea–Brändén 原论文 Theorem 2](https://arxiv.org/pdf/math/0607416) 的有限次数保持实根判据，以及 [NIST DLMF 的正交多项式零点性质](https://dlmf.nist.gov/18.2)。具体代入、重根处理和符号推导均已独立核对。完整证明见[最高系数笔记](research/highest_coefficient.md)；本轮不声称该组合恒等式或方法的新颖性。

同时得到
$$
|A_{n,D}|\le\kappa_D(n+1)
 \binom n{n/2}^{9}\binom{3n/2}{n}^{2},
\qquad
\log|A_{n,D}|\le(\log3456)n+O(\log n).
$$

## 3. 已证：哪些大素数一定留在常数项分母中

由部分分式得到
$$
B=-\sum_{j=0}^n\sum_{s=1}^9c_{j,s}
       \sum_{d\mid D}w_dd^sH_{d(j+n)}^{(s)}.
$$
取素数 $p>2n$，并要求 $p^2>2Dn$、$p\nmid D$。这包含本轮所有测试参数。逐阶考察 p 进估值：
$$
p^9B\equiv
-\sum_{j=0}^n C_j
 \sum_{d\mid D}w_dd^9
 H_{\lfloor d(j+n)/p\rfloor}^{(9)}
\pmod p.
$$
右侧非零便严格给出 $v_p(B)=-9$。右侧为零，只能推出 $v_p(B)\ge-8$，不能声称该素数已从分母消失。

尤其当 $Dn<p\le2Dn$ 时，只有 $d=D$ 有贡献，且调和和中只有一个 p 的倍数：
$$
\boxed{
p^9B\equiv-D^9\sum_{j=\lceil p/D\rceil-n}^{n}C_j\pmod p.}
$$
所以只用最高残数的整数尾和，就能得到严格的分母因子。证明覆盖所有需要的分母条件，见[局部算术笔记](research/arithmetic.md)。

扫描 $D=6,8$、$n=24,48,96,192,384$ 的全部 $2n<p\le2Dn$，共 **2428 个参数—素数对**；其中 **2424 个**在模 p 层面非零，严格贡献 $p^9$。四个模 p 零例另做更高精度的局部检查，结果保存在算术笔记和证据中。

两个最外层例外为：
$$
(D,n,p)=(6,384,3767),\qquad(8,384,5527).
$$
独立模 $p^2$ 计算已证明两者均满足 $v_p(B)=-8$。另两个内层例外 $(D,n,p)=(8,48,173),(8,192,947)$ 也得到同一结论。因此四个模 p 零例已全部精确归类：只是少一阶，并未移除这些素数的分母代价。这否定了“所有外层素数都贡献九次方”的猜想。下节保守证书直接排除两个外层例外，不依赖其八次方改进。

## 4. 不用完整 B 的严格有限障碍证书

把 $B=b/q$ 写为最简分数。由于已证 $A\in\mathbb Z\setminus\{0\}$，primitive 的正乘数满足
$$
M=\frac{q}{\gcd(A,b)}\ge\frac q{|A|}.
$$
令 Q 为已证明保留的外层素数九次方之积，则 $Q\mid q$，故
$$
\boxed{|P(\zeta(9))|=M|L|\ge\frac{Q|L|}{|A|}.}
$$
这里已经扣除了可能的所有公因子，不会误把单个素数的估值当作整个有理乘数的实数下界。

原始 L 用 Arb 从原函数直接求和，截到 $k=4n$。首项为精确有理数，相邻项用恒等式
$$
\frac{R_n(t+1)}{R_n(t)}
=\frac{t^{10}(t+2n+1)}{(t-n)(t+n+1)^{10}}
$$
递推。对每个移位取 $x=4n+a/D$，严格尾界为
$$
\sum_{k>4n}R_n(k+a/D)
\le
\frac{n!^7(1+2n/x)^{2n}}
     {(7n+8)x^{7n+8}}.
$$
然后按各移位的权重绝对值合并误差。此过程不计算完整 B，也不使用 ζ(9) 的数值来得到 L。

下表每项 r 都经过向下取整，严格保证 $|P(\zeta(9))|>e^{rn}$：

| n | D=6：保证的 r | D=8：保证的 r |
|---:|---:|---:|
| 24 | 35.43 | 50.89 |
| 48 | 31.19 | 51.33 |
| 96 | 35.00 | 51.81 |
| 192 | 34.32 | 52.65 |
| 384 | 34.70 | 52.57 |

例如 $D=6,n=384$ 已有 $|P|>e^{34.70\times384}$。**这是这些具体有限候选的严格排除结论，不是由浮点趋势外推的结论。** 10 份证书均保存完整 A、Q、逐素数剩余、1024 位 Arb 区间和精确有理尾界。

## 5. 距离无穷序列的障碍定理还缺什么

令 $\mathcal G_{n,D}$ 为外层区间 $Dn<p\le2Dn$ 中最高残数尾和模 p 非零的素数集。由上面的算术下界与已证解析极限，
$$
\liminf\frac{\log|P(\zeta(9))|}{n}
\ge
9\liminf\frac1n\sum_{p\in\mathcal G_{n,D}}\log p
+f(x_*)-\log3456.
$$
注意精确关系
$$
\log3456-f(1)=27\log2.
$$
因此得到一个清楚的**条件定理**：
$$
\liminf_{n\to\infty,\ n\text{ 偶}}
\frac1n\sum_{p\in\mathcal G_{n,D}}\log p>3\log2
\quad\Longrightarrow\quad
\text{primitive 形式指数增长。}
$$
目前尚未证明左侧的统一下界。2428 个有限同余检查不能替代这一步。已能无条件保证的最右侧短窗口宽度仅为 D，不能据此取得正的线性指数。

所以本轮仍没有证明整个尾部分支不可能成功，更没有证明 ζ(9) 有理或无理。但实验证据已获得严格的有限解释：**当前固定权重移位消元引入的大素数常数项分母，是明确且巨大的代价。**

## 6. 验证、复现和交付

三名子代理分别处理局部算术、最高系数全序列证明、精确扫描；主代理构造并核验有限障碍证书，随后交叉审查。

- 六个旧完整档案的分母及 primitive 乘数均用已知范围内素数完整试除，余数为 1；200 次大素数同余与精确 B 直接对照通过。
- 新十组扫描逐素数保存剩余。有限障碍计算独立使用外层尾和公式，并与完整扫描逐项匹配。
- 十份实数下界均从存档有理区间独立重算；其中 n=24 两例还与第三轮完整 $A\zeta(9)+B$ 的区间交叉一致。
- 最高系数的无穷序列论证使用已核对的外部定理及本地证明；小规模精确符号检查只用于排查实现错误。

复现入口：

```powershell
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' -B missions/zeta9/round4/scripts/prime_scan.py
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' -B missions/zeta9/round4/scripts/denominator_obstruction.py
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' -B missions/zeta9/round4/scripts/obstruction_audit.py
```

[完整实验与分母分组](research/experiments.md) · [最高系数证明](research/highest_coefficient.md) · [局部算术证明](research/arithmetic.md) · [汇总证据](verification/summary.json) · [产物哈希清单](verification/artifact-manifest.json)

本轮全部新增内容位于 `missions/zeta9/round4/`；前三轮文件保持冻结。
