# ζ(9) 第二轮：奇极点阶数、有限整化与精确消元

本笔记只证明构造的代数、全素数整性、消元与缩放结论，不把多 ζ 线性形式误称为单 ζ(9) 形式。第一轮的特殊 `d_n^9/G` 定理不在这里直接迁移。下文用 `r` 表示极点阶数，用 `ell` 表示素数；计算接口中的参数 `p` 等于这里的 `r`。

## 1. 通用部分分式及确切支持

取
\[
 r\in\{3,5,7,9\},\quad d=9-r,\quad b=d+1=10-r,
 \quad n\ge2\text{ 为偶数},\quad m\ge0,
 \quad2bm\le r(n+1)-2.
\]
`m=0` 可以作为控制案例。Pochhammer 使用 rising 约定。定义
\[
 R_m(t)=\frac{n!^r}{m!^{2b}}
 \frac{[(t-m)_m(t+n+1)_m]^b}{(t)_{n+1}^{r}},
 \qquad L_m=\frac1{d!}\sum_{k=1}^{\infty}R_m^{(d)}(k).
\]
分子、分母的次数差不超过 −2，且为奇数，故实际上不超过 −3。所有导数级数绝对收敛。`t=1,...,m` 为 `b=d+1` 重零点，因此前 m 个求和项严格为零。

唯一部分分式写成
\[
 R_m(t)=\sum_{j=0}^n\sum_{k=1}^r\frac{c_{j,k}}{(t+j)^k}.
\]
最高阶系数为非零整数
\[
 \boxed{C_j:=c_{j,r}=(-1)^{m+j}\binom nj^r
             \binom{j+m}{m}^{b}\binom{n-j+m}{m}^{b}.}
\]
这也给出了整性证明所使用的公因子
\(G=\gcd(|C_0|,\ldots,|C_n|)>0\)。

令 `z=t+j`。在正式幂级数环中，
\[
 \frac{z^rR_m(z-j)}{C_j}
 =\prod_{a=1}^m(1-z/(j+a))^b(1+z/(n-j+a))^b
  \prod_{a=1}^j(1-z/a)^{-r}
  \prod_{a=1}^{n-j}(1+z/a)^{-r}.
 \tag{1}
\]
若右侧为 \(\sum_{h\ge0}a_{j,h}z^h\)，则 \(c_{j,r-h}=C_ja_{j,h}\) 对 `0<=h<=r-1` 成立。一个便于精确计算的递推是
\[
 T_{j,v}=10H_j^{(v)}-bH_{j+m}^{(v)}
       +(-1)^v[10H_{n-j}^{(v)}-bH_{n-j+m}^{(v)}],
\]
\[
 a_{j,0}=1,\qquad a_{j,h}=\frac1h\sum_{v=1}^hT_{j,v}a_{j,h-v}.
 \tag{2}
\]
其中 `H_0^(v)=0`。式 (2) 中出现的 `/h` 不应额外计入整化成本；式 (1) 的整数二项式展开给出更准确的分母结论。

反射恒等式 `R_m(-n-t)=-R_m(t)` 给出
\[
 c_{n-j,k}=(-1)^{k+1}c_{j,k}.
\]
因此所有偶数 k 的系数和为零。无穷远的 `t^(-1)` 系数为零，另有 \(\sum_jc_{j,1}=0\)。记
\[
 \beta_k=\binom{d+k-1}{d},\quad
 A_{d+k}=\beta_k\sum_{j=0}^nc_{j,k},\quad
 B=-\sum_{j=0}^n\sum_{k=1}^r\beta_kc_{j,k}H_j^{(d+k)}.
\]
由于 d 为偶数，逐项求导不带负号。最终得到
\[
 \boxed{L_m=B+\sum_{s\in\{d+3,d+5,\ldots,9\}}A_s\zeta(s).}
 \tag{3}
\]

| r | d | b | 保留的 ζ 值 | 个数 q |
|---:|---:|---:|---|---:|
| 3 | 6 | 7 | ζ(9) | 1 |
| 5 | 4 | 5 | ζ(7), ζ(9) | 2 |
| 7 | 2 | 3 | ζ(5), ζ(7), ζ(9) | 3 |
| 9 | 0 | 1 | ζ(3), ζ(5), ζ(7), ζ(9) | 4 |

`r=9,d=0,k=1` 不能形式地写成 `0·ζ(1)`。严格做法是先把求和截断于 N：
\(\sum_jc_{j,1}(H_{N+j}-H_j)\)。由 \(\sum_jc_{j,1}=0\) 及 \(H_{N+j}-H_N\to0\)，极限等于 \(-\sum_jc_{j,1}H_j\)，正好是 B 中相应项。

## 2. 全素数的安全证书及分母拆分

写 \(D=d_{n+m}\)、\(E=d_n\)，其中 \(d_N=\operatorname{lcm}(1,\ldots,N)\)。式 (1) 中所有非零整数分母的绝对值至多 n+m。对任意整数 e（包括负整数），\(\binom eh\in\mathbb Z\)。逐项展开式 (1) 即证
\[
 \boxed{D^{r-k}c_{j,k}/G\in\mathbb Z\quad(1\le k\le r).}
 \tag{4}
\]
这是所有素数同时成立的证明，尤其包括 2、3、5、7；没有把形式导数中的阶乘当作额外分母。

由 \(E^sH_j^{(s)}\in\mathbb Z\)（`j<=n`），安全乘子 `D^9/G` 覆盖式 (3) 的整个系数向量。更强而仍然初等的统一证书为
\[
 \boxed{t_{\rm split}=D^{r-1}E^b/G,\qquad
 t_{\rm split}(B,A_{d+3},\ldots,A_9)\in\mathbb Z^{q+1}.}
 \tag{5}
\]
对常数 B 的每个 k 项，所需分母为 \(D^{r-k}E^{d+k}\)，而
\[
 \frac{D^{r-1}E^b}{D^{r-k}E^{d+k}}
 = (D/E)^{k-1}\in\mathbb Z.
\]
对 ζ 系数只需式 (4)。所以式 (5) 不依赖任何未证的公因子消除，且优于或等于 `D^9/G`。

精确局部指数可以直接计算。对每个素数 ell，令
\[
 \nu_\ell=\min_{0\le j\le n}\big[
 r v_\ell(n!)+b v_\ell((j+m)!)+b v_\ell((n-j+m)!)
 -10v_\ell(j!)-10v_\ell((n-j)!) -2b v_\ell(m!)\big].
 \tag{6}
\]
这是 `v_ell(G)`，包括全部素数幂层；不能把外面的 min 移入各层之和。式 (5) 的素数指数恰为
\[
 (r-1)\lfloor\log_\ell(n+m)\rfloor
 +b\lfloor\log_\ell n\rfloor-\nu_\ell.
\]
若指数为负，必须保留该负值；乘子允许为有理数，截成零会损失已经证明的整除性。

## 3. r=7、9 的简单极点因子证书

以下是重新证明的第二种证书，不是第一轮 `E^9/G` 定理的迁移。假设 `r` 为 7 或 9，且 `0<=m<=n`。令
\[
 Q(t)=\prod_{j=0}^n(t+j),\quad G_0(t)=n!/Q(t),\quad
 F_{A,m}(t)=\frac{n!}{m!}\frac{(t+A+1)_m}{Q(t)}.
\]
`F_(A,m)` 为真分式，仅有简单极点。对整数 A，其在 `-j` 的残数为
\[
 (-1)^j\binom nj\binom{A+m-j}{m}\in\mathbb Z.
\]
负整数上指标的广义二项式仍是整数。`G_0` 的残数也均为整数。由于 `r-2b>=0`，有精确因子分解
\[
 R_m=G_0^{r-2b}F_{-m-1,m}^{\,b}F_{n,m}^{\,b}.
 \tag{7}
\]
右边恰有 r 个简单极点因子。

若 \(F(t)=\sum_{a=0}^n u_a/(t+a)\)，且所有 \(u_a\in\mathbb Z\)，则在 `z=t+j` 处
\[
 zF(z-j)=u_j+\sum_{a\ne j}u_a\frac z{a-j+z}.
\]
它的第 h 阶 Taylor 系数被 `E^h` 整化。对式 (7) 的 r 个因子取乘积即得
\[
 E^{r-k}c_{j,k}\in\mathbb Z,\qquad
 \boxed{E^9(B,A_{d+3},\ldots,A_9)\in\mathbb Z^{q+1}.}
 \tag{8}
\]
式 (8) 没有除以 G。它对 `m=n,r=9` 尤其适用，但该原子仍含 ζ(3)、ζ(5)、ζ(7)、ζ(9) 四项；即使证明它正且指数衰减，也不能单独推出 ζ(9) 无理。

相邻窗口还可能包含 `m=n+c>n`。这时不能再声称 `F_(A,m)` 是真分式，但有另一直接证书：
\[
 R_{n+c}(t)=R_n(t)
 \frac{\prod_{a=1}^c[(t-n-a)(t+2n+a)]^b}
 {[(n+c)!/n!]^{2b}}.
\]
分子乘子在 `Z[t]` 中，其各极点处 Taylor 系数均为整数。于是
\[
 \boxed{[(n+c)!/n!]^{2b}E^9}
 \tag{9}
\]
整化该原子的全部系数，只要原构造仍满足真分式条件。固定 c 时，式 (9) 相对 `E^9` 的额外对数成本为 `O(log n)`。

可以合并独立证书：若正有理数 `t_1,t_2` 都整化同一非零向量，则它们的有理 gcd 也整化该向量。证明是通分后对两个整数用 Bezout。等价地，每个素数取 `min(v_ell(t_1),v_ell(t_2))`；这与未经证明截断指数完全不同。

## 4. 大素数公因子公式与统一渐近

本节不要求 `n>=2m`。设素数 `ell^2>n+m`，记 `rho=n mod ell`、`sigma=m mod ell`。由式 (6) 只有一层 factorial floors，故
\[
 \boxed{\nu_\ell=b\,\mathbf1_{\rho+2\sigma\ge2\ell-1}.}
 \tag{10}
\]
证明：对 `u=j mod ell`，`v=(rho-u) mod ell`，对应估值为
\[
 r\mathbf1_{u>\rho}
 +b\mathbf1_{u+\sigma\ge\ell}
 +b\mathbf1_{v+\sigma\ge\ell}.
\]
在 `0<=u<=rho` 中，无 carry 的整数区间恰为
\[
 [\max(0,\rho+\sigma-\ell+1),\ \min(\rho,\ell-\sigma-1)].
\]
它非空当且仅当 `rho+2sigma<=2ell-2`，并且这些 u 都能由 `j=u<=n` 实现。否则 `u=0` 给出估值 b。若某个 `u>rho` 的两个分子 carry 均为零，由 `u+v=ell+rho` 会推出 `rho+2sigma<=ell-2`，矛盾。因此它不能使最小值低于 b。即使 `ell>n`、部分 u 不可取，以上 `u<=rho` 的论证仍完整。

固定正有理数 `alpha`，令 `m=alpha n` 沿允许的偶数 n 取整值。则
\[
 \frac{\log G}{n}\longrightarrow
 \Gamma_b(\alpha):=b\int_0^\infty
 \mathbf1_{\{x\}+2\{\alpha x\}\ge2}\frac{dx}{x^2}.
 \tag{11}
\]
该积分在 0 附近没有支持，所以不发散。证明的三个误差控制为：

1. 对 `ell<=sqrt(n+m)`，用 `nu_ell<=v_ell(C_0)<=b floor(log_ell(n+m))`，全部贡献为 `O(sqrt(n) log n)=o(n)`。
2. 有限门槛 `2ell-1` 与积分门槛 `2ell` 的唯一差别是 `rho+2sigma=2ell-1`。此时 `ell` 整除 `n+2m+1`，全部对数贡献不超过 `b log(n+2m+1)=o(n)`。
3. 固定 `ell/n>=epsilon` 后只有有限个 floor 区间，可以逐区间用素数定理。被截掉的素数贡献不超过 `b theta(epsilon n)=O(epsilon n)`，然后令 epsilon 趋零。

积分可以从 `1/(1+alpha)` 开始：更小 x 对应 `ell>n+m`，指标恒为零。`alpha=0` 控制有 G=1，可单独处理。注意 `log d_N=psi(N)`，不是 `theta(N)`。因此
\[
 \lim\frac{\log t_{\rm split}}n
 =9+(r-1)\alpha-\Gamma_b(\alpha).
 \tag{12}
\]

当 `r=7,9` 且 `0<alpha<=1`，把式 (5) 与式 (8) 逐素数合并，得到更强的渐近成本
\[
 9-b\int_1^\infty
 \mathbf1_{\{x\}+2\{\alpha x\}\ge2}\frac{dx}{x^2}.
 \tag{13}
\]
对大素数 `ell<=n`，两个证书的最小指数为 `9-b·indicator`；对 `n<ell<=n+m`，式 (8) 的指数为 0，而式 (5) 的指数是 `r-1-b·indicator>=0`。小素数差异仍是 `o(n)`。

在 `alpha=1`，积分可精确求和：
\[
 J=\sum_{k=1}^\infty\left(\frac1{k+2/3}-\frac1{k+1}\right)
   =\frac32\log3-\frac12-\frac\pi{2\sqrt3}
   \approx0.2410187508850556.
\]
该求和可以不用特殊函数：先写成 \(\int_0^1(t^{2/3}-t)/(1-t)\,dt\)，再代入 `t=u^3`，得到 \(3\int_0^1u^4/(1+u+u^2)\,du\)，作有理函数积分即得上式。
所以 `r=9` 的合并成本为 `9-J≈8.7589812491`，`r=7` 为 `9-3J≈8.2769437473`。这些是原子多 ζ 向量的成本，不能直接当作消元后单 ζ(9) 的成本。

## 5. 精确消元、退化和 primitive 缩放

固定 r，取 `q=(r-1)/2` 个允许的 m 值，每个原子向量按
\[
 v_i=(B_i,A_{d+3,i},\ldots,A_{9,i})\in\mathbb Q^{q+1}
\]
存储。选任何已证乘子 `t_i>0`，整化后再除整向量各项的 gcd，得到 primitive 整向量 `P_i=mu_i v_i`。

对任何非零有理向量 v，令 D 为所有坐标分母的 lcm，c 为 `Dv` 各坐标的非负 gcd，则 `mu=D/c` 是唯一正的 primitive 乘子。任何其他有效正有理乘子 t 都满足
\[
 t/\mu\in\mathbb Z_{>0}.
 \tag{14}
\]
这是 Bezout 恒等式的直接推论。因此 `log(t/mu)/n>=0` 是有定义的有限整化 gap；零向量没有这种 primitive 缩放。

令 M 为 primitive 原子的低 ζ 系数矩阵，形状 `(q-1)×q`，列对应原子。定义精确整数权重
\[
 W_i=(-1)^i\det M_{\widehat i}\quad(i=0,\ldots,q-1).
 \tag{15}
\]
按空行列式等于 1 的约定，`q=1` 时 `W_0=1`。Laplace 展开严格给出 `MW=0`。若 W 非零，先除其坐标 gcd，然后组合 `sum W_iP_i`；它只有常数和 ζ(9) 两项，再除这两项的 gcd 即得最终 primitive 多项式。

必须分别处理以下状态：

- `rank(M)=q-1`：至少一个余子式非零，消元核恰是一维。
- 全部 W 为零：只证明这个余子式方案退化。精确核中存在最高 ζ 系数非零的向量，当且仅当 `rank([M; A_9-row])>rank(M)`。若不进一步计算核，应记录 `rank_degenerate`，不能称为构造恒零。
- W 非零但合成的 `A_9=0`：若合成 B 非零，primitive 结果只是常数 ±1，不能提供无理性衰减；若 B 也为零，则为零向量。
- `A_9!=0`：只是多项式非零，不是其在 ζ(9) 处非零。有限案例可用严格实区间验证；无穷序列仍需非零性论证。

满行秩时，最终最高 ζ 系数等于完整 q×q ζ 系数矩阵的行列式（至多差一个已知符号和权重 gcd），可以作为独立一致性检查。

若对未整化的原始向量直接取有理余子式，记产生的单值向量为 F，则 `prod_i t_i` 是其有效整化乘子：每个余子式乘上它涉及的 `prod_(j!=i)t_j`，正好成为整化矩阵的整数余子式。这是消元的有限证书，不能只沿用某一个原子的乘子。

## 6. 换基不改变什么，相邻 m 又改变了什么

固定 q 个原子的低 ζ 矩阵满行秩时，对这 q 个输入作任意可逆有理换基（包括独立缩放、先取 primitive、改为有限差分基），其消元核只按逆矩阵变换。因此最终的非零单值向量沿同一条有理直线，primitive 结果至多差整体符号。更好的整化界或不同余子式实现不能降低同一个最终 primitive 多项式的绝对值。

但联合相邻 m 并非把一个原子改写了名字。令 `u=t(t+n)`，对 `a>=0` 有
\[
 R_{m+a}(t)=R_m(t)
 \prod_{h=1}^a
 \left(\frac{u-(m+h)(n+m+h)}{(m+h)^2}\right)^b.
 \tag{16}
\]
右边的多项式乘子次数依次为 `0,b,2b,...`，所以这些有理函数在函数空间中线性独立。非平凡消元组合确实是 `R_m(t)P(t(t+n))` 的另一有理函数；共同保留 `1,...,m` 的 b 重零点。

这并不推出它们的 ζ 系数向量线性独立：从有理函数到级数/系数的线性映射可能有核。改变 m 窗口或极点阶数 r 能改变真实输入子空间；只对同一窗口换成差分基则不能改变满秩情形的最终 primitive 输出。也不能仅凭固定项数的差分声称指数率改善：需要证明主鞍点振幅消除、剩余鞍点或高阶项的严格大小。式 (16) 单独没有这种结论。

## 7. 实现与证据边界

`../scripts/certificate.py` 独立计算最高阶整数系数、公因子、全部素数的 floor-min、式 (5)、式 (8)/(9) 及它们的有理 gcd。它可对精确系数向量检查每个证书的整性，并报告 primitive gap。其浮点对数仅作报告，不作为整性证明输入。

已运行的有限独立检查：

- 309 个小参数案例：直接最高阶系数 gcd、所有素数的式 (6)、式 (10) 一致。
- 10 个代表案例：使用式 (1) 的直接 Taylor 乘积计算 PF，独立于计算代理的幂和递推；覆盖四种极点阶数、`m<n`、`m=n`、`m>n` 和 `m` 明显大于 n。逐个 PF 系数核验式 (4) 及简单极点/扩展证书，并核验反射、留数和与最终全系数整性。
- 对冻结的 160 个原子文件逐个只读审计，四类极点阶数的案例数依次为 13、29、45、73。文件 SHA-256、G、原 safe 乘子、primitive 乘子、所有新证书对完整向量的整性以及证书/primitive 的正整数比例全部通过。

完整审计和各素数的有限指数保存在 `../verification/arithmetic-audit.json`，包含输入索引与每个源 artifact 的哈希。复运行命令为：

```powershell
python -B missions/zeta9/round2/scripts/certificate.py --audit-index missions/zeta9/round2/verification/elimination-atoms.jsonl --output missions/zeta9/round2/verification/arithmetic-audit.json
```

例如 `r=9,n=48,m=48`，联合证书的 `log(t)/n≈8.6639771132`，与精确 primitive 乘子的 gap 为 `≈0.6074864613`。这些有限证据核查了实现，统一结论仍依赖前述证明。解析代理已独立复核第 3–4 节，未发现证明缺口。

本笔记已经证明的是有限代数/整性、式 (10) 的局部估值以及式 (11)–(13) 的证书成本。它没有证明消元矩阵在无穷序列上满秩，没有证明消元后 A_9 始终非零，也没有证明最终单 ζ(9) 形式非零且趋零。原子多 ζ 形式的正性或衰减，必须和消元权重的大小及符号一起重新分析。
