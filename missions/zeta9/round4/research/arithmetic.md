# ζ(9) 第四轮：尾部移位常数的大素数分母

本笔记给出不计算完整常数 B 的局部证书，并把它转为合法的实数 primitive 下界。重点区分：有限可检验结论、严格无条件的短窗口，以及尚未证明的素数密度假设。

## 1. 参数和已有的全序列最高系数

取偶数 `n>=2`、`D=6` 或 8，使用第二轮的整数极点函数
\[
 R_n(t)=\frac{n!^7(t-n)_n(t+n+1)_n}{\prod_{j=0}^n(t+j)^9}
       =\sum_{j=0}^n\sum_{s=1}^9\frac{c_{j,s}}{(t+j)^s}.
\]
尾部移位从 k=n 开始。采用第三轮的固定权重
\[
 (d,w_d)=(1,-7776),(2,1701),(3,-224),(6,1)
\]
或
\[
 (d,w_d)=(1,-32768),(2,5376),(4,-168),(8,1).
\]
由精确的 Hurwitz 乘法恒等式及三个低奇数矩消去，最终形式为
\[
 L_{n,D}=A_{n,D}\zeta(9)+B_{n,D},
\]
\[
 B_{n,D}=-\sum_{j=0}^n\sum_{s=1}^9c_{j,s}
               \sum_{d\mid D}w_dd^sH_{d(j+n)}^{(s)}.
 \tag{1}
\]
最高极点系数为
\[
 C_j=c_{j,9}=(-1)^j\binom nj^9\binom{n+j}{n}\binom{2n-j}{n}\in\mathbb Z.
 \tag{2}
\]
这里的 C_j 有交替符号，不能使用第三轮 dense-zero 构造的同号论证。

本轮 [最高系数独立证明](highest_coefficient.md) 已证明
\[
 \operatorname{sgn}\sum_jC_j=(-1)^{n/2},\qquad
 A_{n,D}=\kappa_D\sum_jC_j\ne0,
 \tag{3}
\]
其中 `kappa_6=6531840`、`kappa_8=92897280`。算术代理另行核对了该证明的负根保持算子、倒数算子与偶次回文根配对，也核对了所引用的 [Borcea–Brändén 原文 Theorem 2](https://arxiv.org/pdf/math/0607416) 的稳定性判据。因此本族全部偶 n 都可安全除以 `|A|`，不再将 A=0 留作本族风险。

还将使用第二轮已独立证明的局部整性：
\[
 d_n^{9-s}c_{j,s}\in\mathbb Z.
 \tag{4}
\]
所以 p>2n 时全部 PF 系数都 p 整，且 C_j 全为 p 单位（式 (2) 中所有 factorial 参数至多 2n）。

## 2. 模 p 的截断最高残数公式

本节假设素数 p 满足
\[
 p>2n,\qquad p\nmid D,\qquad p^2>2Dn.
 \tag{5}
\]
最后一项确保所有调和分母最多含一次 p。对 n>=4 它自动成立；在最小参数处不能遗漏，例如 `D=8,n=2,p=5` 不满足它。

由式 (1)、(4)，`v_p(B)>=-9`。乘以 p^9 后，所有 s<=8 项模 p 为零；s=9 中分母不被 p 整除的项也为零。于是
\[
 \boxed{p^9B\equiv-
 \sum_{j=0}^nC_j\sum_{d\mid D}w_dd^9
 H_{\lfloor d(j+n)/p\rfloor}^{(9)}\pmod p.}
 \tag{6}
\]
此处右边的调和和在有限域中计算，其指标小于 p，所以所有求逆都有定义。

令
\[
 T_J=\sum_{j=J}^nC_j,\qquad
 J_{a,d,p}=\max(0,\lceil ap/d\rceil-n).
\]
交换有限求和次序，式 (6) 等价于可直接编程的截断式
\[
 \boxed{p^9B\equiv-
 \sum_{d\mid D}w_dd^9
 \sum_{a=1}^{\lfloor2dn/p\rfloor}a^{-9}T_{J_{a,d,p}}
 \pmod p.}
 \tag{7}
\]
界限使用精确整数 ceiling；不能用实数舍入代替。若式 (6)/(7) 的值非零，则严格有 `v_p(B)=-9`；若为零，只能先得 `v_p(B)>=-8`，不能说 p 从分母消失。

特别地，在外区
\[
 Dn<p\le2Dn,
\]
每个真除数 `d<=D/2` 都没有 p 倍数；d=D 恰有一个 p 倍数。因 `w_D=1`，得到
\[
 \boxed{p^9B\equiv-D^9
 \sum_{j=\lceil p/D\rceil-n}^{n}C_j\pmod p.}
 \tag{8}
\]
此范围自动满足式 (5) 的平方条件。

## 3. 模 p² 提升：零模 p 不等于分母消失

对式 (5) 的所有 p，可以再保留 s=8 项：
\[
 p^9B\equiv-
 \sum_{d\mid D}w_d\sum_{a=1}^{\lfloor2dn/p\rfloor}
 \left[d^9a^{-9}T_{J_{a,d,p}}
       +p d^8a^{-8}U_{J_{a,d,p}}\right]\pmod{p^2},
 \tag{9}
\]
其中第一项在模 p² 中计算，第二项只需 `U_J mod p`，并且
\[
 U_J=\sum_{j=J}^nc_{j,8},\qquad
 c_{j,8}=C_j[10H_j-10H_{n-j}-H_{n+j}+H_{2n-j}].
 \tag{10}
\]
式 (10) 是局部消去九阶极点后的一阶对数导数。所有调和分母至多 2n，小于 p。

式 (9) 的证明与式 (6) 相同：s<=7 项带至少 p²，非 p 倍数项带 p^9；两者模 p² 都消失。外区进一步简化为
\[
 p^9B\equiv-D^9T_J-pD^8U_J\pmod{p^2},
 \qquad J=\lceil p/D\rceil-n.
 \tag{11}
\]

扫描出现的四个零模 p 例子已由独立实现全部提升：

| D | n | p | 区域 | p^9 B mod p² | p^8 B mod p | 已证 v_p(B) |
|---:|---:|---:|---|---:|---:|---:|
| 6 | 384 | 3767 | 外区 | 1284547 | 341 | −8 |
| 8 | 384 | 5527 | 外区 | 28038471 | 5073 | −8 |
| 8 | 48 | 173 | 内区 | 15224 | 88 | −8 |
| 8 | 192 | 947 | 内区 | 643013 | 679 | −8 |

例如前两行的外区截断指标分别为 244、307，`T_J mod p²` 分别为 5722073、13176368，`U_J mod p` 分别为 2600、3465。表内的模 p² 值均等于 p 乘以一个非零剩余类，所以精确结论是分母含 p^8，而不是含 p^9，也不是不含 p。

## 4. 已保证的短窗口与未证明的正长度区间

若
\[
 D(2n-1)<p\le2Dn,
\]
截断式 (8) 只剩 `C_n=binom(2n,n)`。由于 p>2n，该数是 p 单位，因此此窗口中的每个素数都严格满足 `v_p(B)=-9`。

这个窗口宽度只有 D；在 `p/n` 尺度上其长度趋零，不能提供指数级分母质量。一个无条件的无限子序列也很弱：对素数 `p≡-1 (mod 4D)`，令 `n=(p+1)/(2D)`，则 n 为偶数，且 `p=2Dn-1` 位于上述窗口。Dirichlet 定理保证这样的 p 无穷多，但每个 n 只保证这一个素数，所得 `log p/n` 仍趋零。

到目前为止，尚未证明任何正长度的固定 `p/n` 区间对所有足够大偶 n 都没有异常，也未证明某个无限 n 子序列拥有足够多的非零截断和。第 3 节的外区反例已排除“整个 `(D,2D)` 区间都无异常”这一更强断言，但不排除未来证明某个较小区间或密度结论。

精确异常条件就是
\[
 \sum_{j=\lceil p/D\rceil-n}^n
 (-1)^j\binom nj^9\binom{n+j}{n}\binom{2n-j}{n}\equiv0\pmod p.
 \tag{12}
\]
实数意义上的交替尾和非零并不保证式 (12) 不成立；不能用单调项或同号实数论证代替有限域证明。

## 5. 吸收其他素数分母的 primitive 下界

把 B 写为最简分数 `b/q`，q>0。因 A 为非零整数，primitive 乘子恰为
\[
 M=\frac q{\gcd(qA,b)}=\frac q{\gcd(A,b)}.
\]
对任意一组已证明式 (8) 非零的外区素数，令
\[
 Q=\prod_{p\in\mathcal G}p^9.
\]
则 `Q|q`，而 `gcd(A,b)<=|A|`，所以
\[
 \boxed{M\ge Q/|A|,\qquad
 |M L|\ge Q|L|/|A|.}
 \tag{13}
\]
这是真正的实数下界：允许 M 在其他素数处有分母，它们已被 `|A|` 上界吸收。式 (13) 不把单个 p 进估值直接当作实数大小。若进一步用式 (9) 证明某些异常素数恰有指数 8，也可以把对应 p^8 因子乘入 Q。

因此有限检验可以完全绕开完整 B：精确求 A，逐素数验证截断和，把已证的分母因子组成 Q，再用严格实区间给出 `|L|` 的正下界。如果所得 `Q|L|/|A|>1`，则对应的最终 primitive 形式严格大于 1。这是有限失败证书，不是全序列结论。

## 6. 精确的条件性渐近门槛

定义
\[
 \beta_n=\frac1n\sum_{\substack{Dn<p\le2Dn\\p\text{ 满足式 (8) 非零}}}\log p.
\]
最高系数的严格上界为
\[
 0<|A|\le\kappa_D(n+1)\binom n{n/2}^{9}\binom{3n/2}{n}^{2},
\]
因此
\[
 \log|A|\le C_A n+O(\log n),\quad
 C_A=7\log2+3\log3=\log3456.
\]
第三轮的尾部解析证明
\[
 \lim\frac{\log|L|}{n}=f(x_*)>f(1),\qquad
 f(1)=3\log3-20\log2.
\]
注意 `f(x*)<-10.43` 是上界，不能拿来证明这里所需的下界。真正使用的是精确的 `f(1)`，且
\[
 C_A-f(1)=27\log2.
\]
由式 (13) 得到条件定理：
\[
 \boxed{\liminf_{n\to\infty}\beta_n>3\log2
 \quad\Longrightarrow\quad
 \liminf_{n\to\infty}\frac1n\log|M_nL_n|>0.}
 \tag{14}
\]
阈值 `3log2≈2.07944154` 对 D=6、8 都适用。素数定理只说明整个外区的总对数质量趋于 D；它不能自动说明非零截断和所占的质量。式 (14) 的密度假设尚未证明，有限扫描中异常稀少也不代替这个假设。

## 7. 实现和审计

`../scripts/local_residue.py` 用两种独立方法产生 C_j：整数精确递推及有限域递推。共同递推比例为
\[
 \frac{C_{j+1}}{C_j}
 =-\frac{(n-j)^{10}(n+j+1)}{(j+1)^{10}(2n-j)}.
\]
在 p>2n 时所有分母均可逆。截断和按精确 ceiling 取指标；模 p² 提升使用整数 C_j 与独立的调和剩余类。

审计命令读取第三轮六份冻结档案，只用其中的精确 B 交叉核验，不修改源文件：

```powershell
python -B missions/zeta9/round4/scripts/local_residue.py --audit-index missions/zeta9/round3/verification/tail-shift-results.jsonl --output missions/zeta9/round4/verification/local-residue-audit.json
```

该审计已经执行：六份档案的 200 个素数逐一通过模 p 与模 p² 的精确 B 对照，两种最高系数递推一致；四个扫描异常全部证明估值恰为 −8；`D=8,n=2,p=5` 的平方边界被明确拒绝。审计文件包含输入索引、每份源档案和脚本的 SHA-256，便于固定证据。

局部证书解决了如何验证分母贡献的问题；尚未解决的是无穷序列上足够大的素数对数质量。
