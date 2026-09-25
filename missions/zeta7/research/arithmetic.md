# ζ(7) 局部算术推广：已证明的界、可计算常数与边界

2026-09-24。依据工作区 `referpaper/ZETA5_IS_IRRATIONAL.pdf` 的 §§3–5
逐项重做；不以该文的总定理为前提。本笔记给出一族整数归一化的算术界，
**没有证明 ζ(7) 无理**。下述数值积分只作探索，不是区间或有理数认证。

## 1. 参数与泛函

固定奇数 s≥5、整数 q≥1、正有理数 α,λ，令 N=αK、h=λK 为整数。
可以取任意 h，未强制 h=K−N。设

\[
 D_A(t)=\prod_{j=1}^A(t+j^2),\quad
 G_{ij}=\mu_s(D_N^{2q}t^{i+j}/D_K),\quad\Delta=\det G.
\]

这里

\[
 \mu_s(t^e)=\frac{(-1)^eB_{2e+2}}{(s-1)!}
             \prod_{j=3}^{s}(2e+j),
\quad
 \mu_s((t+j^2)^{-1})=j^{s-1}(X-H_j^{(s)})-\frac1{s-1}+\frac1{2j}.
\]

以 τ_s(P)=L(P^{(s−2)})/(s−1)!、L(x^k)=B_k 表示拉回泛函，则

\[
 \mu_s(R)=\tau_{s,X}(x^sR(-x^2)),\qquad
 \tau_{s,X}((x-r)^{-1})=H_{d(r)}^{(s)}-X,
\]

其中 d(r)=r (r≥0)，d(r)=−r−1 (r<0)。多项式恒等式直接由导数验证；
极点恒等式由 x^s/(j²−x²) 的除法与 H_j−H_{j−1}=j^(−s) 验证。

## 2. 首个非整多项式矩与真秩界

对 p>s，von Staudt–Clausen 给出 v_p(µ_s(t^e))≥−1。写 n=2e+2。
唯一可能的 p 分母来自 p−1|n。当 n=k(p−1)、1≤k≤s−2 时，
分子中的 n+k=kp 消除此分母。因此

\[
 e<T_s(p):=\frac{s-1}{2}(p-1)-1\quad\Longrightarrow\quad
 \mu_s(t^e)\in\mathbb Z_p.
\]

特别地，**ζ(7) 的阈值是 3p−4**，不是 ζ(5) 的 2p−3。

取整数 c_e≡pµ_s(t^e) mod p，且 e<T_s(p) 时取 c_e=0。
令 µ_s^0(t^e)=µ_s(t^e)−c_e/p，而所有极点值保持不变。
于是 G=A+p^(−1)L，且 L 是常数整矩阵。因为除法的多项式商次数至多
i+j+2qN−K，故

\[
 L_{ij}=0\quad\text{if }i+j<K-2qN+T_s(p).
\]

这使前 h−r 行与列为零，给出 **Q_p 上的实际秩界**

\[
 \operatorname{rank}L\le
 r_h(p):=\min\bigl(h,\,[2h+2qN-K-T_s(p)-1]_+\bigr).
\]

ζ(7) 时括号内为 2h+2qN−K−3p+3。原文 5N≤2p−2 的作用只是保证
其未截断的秩数≤h；ζ(7)、h=K−N 的对应条件为
(2q−1)N≤3p−3。直接取 min(h,r) 可以去掉这项额外限制。

## 3. 分布公式、内区与小素数

对足够大的 p，τ_s 在 Tate 代数上的算子范数≤p：Bernoulli 系数至多丢一阶 p。
次数≤p+1 的首项不会丢 p，因为 s≥5。
简单近极点的互差为 p 单位，且调和指标<p 时，它们的泛函值整。
故原文 Lemma 3.1 的完整有理函数结论保留。

远极点展开的首项为 −a^(−(s−1))/(s−1)。对所有 p>s+1，
\(\sum_{a=1}^{p-1}a^{-(s-1)}\equiv0\pmod p\)，其余项也给出
C_p∈p^s Z_p。于是用 Y=p^sX+C_p 有

\[
 \tau_{s,X}(g)=p^{-(s-1)}\sum_{a=0}^{p-1}
              \tau_{s,Y}^{\rm ext}(g(a+pz)).
\]

这不是只对 residues 的公式。多项式部分由 Bernoulli multiplication 验证；
1/x 决定 Y；平移差分为 g^(s−1)(0)/(s−1)!，反射为负号，继而决定全部整数极点。

令 ℓ_A(a)=#{1≤j≤A:j≡±a mod p}、m_A=⌊A/p⌋。
若行多项式在 t=−a² 的零阶数为 ν_i(a)，则普通来源的完整局部界是

\[
 \nu_i(a)+\nu_j(a)+2q\ell_N(a)-\ell_K(a)-(s-1).
\]

零来源的界为

\[
 2\nu_i(0)+2\nu_j(0)+4qm_N-2m_K+1.
\]

固定 1<B<M，把 K/M<p≤K/B 作为内区。写 H=λ+qα、m=(p−1)/2。
预留 L_0=O_{q,s,α,λ}(M) 个零来源行，使零来源对普通行的半权重
大于所有普通权重。取足够大的常数倍 M 即可，例如 10(q+s+H+1)M。
令

\[
 mT+E=h-L_0+q(N-m_N),\quad 0\le E<m,\qquad
 L_a=T-q\ell_N(a)+\epsilon_a.
\]

把 E 个额外行优先给 ℓ_K 较大的类，取 ε_a∈{0,1}。与原文相同的 CRT 基
\(E_{a,i}=\prod_{c\ne a}(t+c^2)^{L_c}(t+a^2)^i\)
是 Z_p 幺模基：各因子模 p 两两互素，局部对角元是单位。
普通权重取

\[
 w_{a,i}=i+q\ell_N(a)-(\ell_K(a)+s-1)/2.
\]

零块权重取它在所有来源处半权重的最小值。由于 ℓ_K 只有两个相邻值，
extras 的上述排序保证其它来源的半权重不小于指定权重。
相应 determinant valuation 是 γ_in=2Σw。

对于固定 M，近极点大小、首项次数与零块维数都是 O(M)，而 p→∞，
所以完整泛函引理的所有次数条件最终成立。p²>CK 也最终成立。
这给出渐近定理所需的 K_0，但本笔记未计算最小有效 K_0。

**分配的一个明确充分条件**：在 2αB<1 下，要求

\[
 \delta_{\rm alloc}:=\min(2HB-q,\lambda/\alpha-q)>0.
\]

因为 qℓ(αx,z)≤q⌈2αx⌉，而
inf_(x≥B)(2Hx−q⌈2αx⌉) 是上述两个数的最小值。
每次 ceiling 跳跃后的最低值依次为 kλ/α−q，递增。
所以实际 T=floor(2Hx+O_M(1/p)) 也最终保证所有 L_a≥0。
脚本将这项正裕量设为硬门槛，不能略去负维分配的素数范围。

小素数使用整数值多项式基。令

\[
 q_0=1,\quad q_i=\frac{(-1)^i2tD_{i-1}(t)}{(2i)!},\qquad
 f_i=(D_N/(N!)^2)^q q_i.
\]

f_i(−x²) 在 Z_p 上整数值。因此

\[
 F=S\Delta=\det[(K!)^2\mu_s(f_if_j/D_K)],\qquad
 S=\frac{(K!)^{2h}4^{h-1}}{(N!)^{4qh}\prod_{i=1}^{h-1}((2i)!)^2}.
\]

Bernoulli 泛函损失至多 (s−1)floor(log_p(d+1))，去极点的整数值商损失
再多两阶 logarithm；调和极点也至多 (s+1) 阶。因此对一个固定 C=C(s,q,α,λ)，

\[
 v_p^G(F)\ge -(s+1)h\lfloor\log_p(CK)\rfloor-hv_p((s-1)!).
\]

ζ(7) 小素数系数是 **8**，不是 6。

## 4. 外区权重及任意 h 的子式推广

取 p>K/B，p²>2K，2N<p。普通 square class 的原始极点数记 ℓ；
δ=1(a≤N)，故剩余极点数为 ℓ−δ。当 p≤K 时，每类恰有两个原极点≤p，
所以高极点 j>p 有 ℓ−2 个。这对任意固定 B 成立，不限于 B=3。

令 Q_a 为该类剩余分母，P_a=D_tail/Q_a，E_a 为高极点因子的乘积。
行 P_a q_(a,i) 取

\[
 q_{a,i}=(t+a^2)^i\ (i<\ell-2),\qquad
 q_{a,i}=E_a(t)(t+a^2)^{i-(\ell-2)}\ (i\ge\ell-2).
\]

局部多项式为逐次次数的 monic 多项式，异类 resultants 为单位，故这是
完整 K−N 维空间的 Z_p 幺模基。跨类条目没有极点，µ_s^0 的多项式值全整。

高极点全部取消后，只剩 a,p−a 两节点；它们相差恰一阶 p。
由于 s 为奇数，H_(p−a)^(s)≡H_(a−1)^(s) mod p。
µ_s 两极点值的 X 系数同余，常数系数差也同余为零：
调和增量 a^(−s) 乘 a^(s−1)，恰被 1/(2a)−1/(2(p−a)) 抵消。
所以两节点 divided difference 整，任意 Z_p 多项式分子也保留此性质。

未取消高极点时，harmonic 最多丢 s 阶，节点导数丢 ℓ−δ−1 阶，
W=D_N^(2q−1) 提供 (2q−1)δ 阶。故有效非正权重为

\[
 w_{a,i}=\begin{cases}
 \min(0,i+q\delta-(\ell+s-1)/2),&i<\ell-2,\\
 0,&i\ge\ell-2.
 \end{cases}
\]

ζ(7)、q=4 时，removed classes ℓ=2,3,4,5,6 的代价 −2Σw 是
0,1,2,4,6；unremoved class 的代价是 **9(ℓ−2)**，原 ζ(5) 是 7(ℓ−2)。
因此虽然新秩界较好，residue 代价却较差。

零 square class 只有 m=⌊K/p⌋≤B 个节点 j=kp。各极点值最多丢一阶 p，
节点互差最多丢两阶，故可统一赋 w=−m，足以覆盖所有条目。
其总权重与维数均 O_B(1)，对 K² 归一化常数无贡献。它不能在有限 K 的
整数归一化中直接删去；应保留这个保守 O_B(1) bound。

**h≥K−N**：补上 D_tail(t)t^j 作为额外行，仍是幺模基；这些行没有极点，
在 A 中与所有行的配对均整，赋权重零。

**h<K−N**：完整空间的单项式子空间到该幺模基的坐标矩阵属 Z_p。
Cauchy–Binet 两次给出 A_h 任意 k 阶子式估值≥2Σ_(i≤k)w_(i)，
其中全权重从最负到零排序。恢复 L_h，按其子式秩 r_h 展开 determinant。
每丢弃一个负权重，补偿≥1，足以抵消 p^(−1)；只有所选 h 权重中的零权有损失。
于是对所有 h 成立

\[
 v_p^G(\Delta_h)\ge 2\sum_{i=1}^h w_{(i)}
      -\min(r_h,\,[h-\#\{w<0\}]_+).
\]

analytic_audit 子代理独立核对了上述任意 h 的子式论证。

## 5. 可编程的 prime-sum 常数

记 ℓ(x,z)=floor(x−z)+floor(x+z)+1、b=qℓ(αx,z)，z∈(0,1/2)。令

\[
 T=\lfloor2Hx\rfloor,\ u=Hx-T/2,\ k=\lfloor2x\rfloor,\ n_+=(2x-k)/2,
\]

\[
 \Gamma_s(x)=\int_0^{1/2}(T-b)(T+b-\ell(x,z)-s)dz
       +u(2T-k-s)+(u-n_+)_+.
\]

令 J(v)=mv−m(m+1)/4，m=floor(2v)，则

\[
 \mathcal N(x)=2\lambda x\lfloor x\rfloor
       -4q\lambda x\lfloor\alpha x\rfloor-2J(\lambda x),\qquad
 R(x)=-\Gamma_s(x)-\mathcal N(x).
\]

均匀地 γ_in=pΓ_s(K/p)+O_M(1)，v_p(S)=pN(K/p)+O_M(1)。

外区用 y=p/K、x=1/y，按上一节权重在 z∈(0,1/2) 上积分，每个权重的
维数密度为 y dz；从最负开始最多取 λ 的总维数。令其总代价为 C_λ(y)，
全体负权重的密度为 n_−(y)，Z_λ(y)=[λ−n_−(y)]_+。另设

\[
 r_\lambda(y)=[2\lambda-1+2q\alpha-(s-1)y/2]_+,
\]

\[
 T_{\rm out}(y)=C_\lambda(y)+\min(r_\lambda(y),Z_\lambda(y))
       -2\lambda\lfloor1/y\rfloor+\sum_{j\ge1}(2\lambda-jy)_+.
\]

y>1 时 C_λ=0、Z_λ=λ。所有非零贡献都在
Y=max(1,2λ,2(2λ−1+2qα)/(s−1)) 以内，有限 K 的 O(1) 边缘可直接保留。
素数定理给出一个正有理归一化 m，使 mF∈Z[X]，并且

\[
 \limsup K^{-2}\log m\le
 A_{s,q,\alpha,\lambda,B,M}:=
 \frac{(s+1)\lambda}{M}+\int_B^M\frac{R(x)}{x^3}dx
       +\int_{1/B}^{Y}T_{\rm out}(y)dy.
\]

每个素数指数必须保留正负号：正 valuation 允许从 F 中除去公因子。
上述 m 不要求等于精确 primitive normalization。

## 6. 实现与独立数值检查

`missions/zeta7/scripts/arithmetic_bounds.py` 的接口：

```python
arithmetic(alpha=.075, q=4, s=7, lam=.925, B=3, M=200)
```

R 在显式分段点之间为仿射函数；脚本解析积分 ax+b 除以 x³。
外区包含秩/零权的交点及任意 h 截断负权重的交点，也分段解析积分。
每段额外进行中点 affine 检查。此实现仍使用浮点，不能当作最后认证。

原文基准 s=5,q=3,α=.075,λ=.925 给
I_out=1.3307395833333338，复现论文的 **127751/96000**。
与 root 另写的 50 万点 vectorized midpoint 积分对照如下：

| s | q | α | λ | A_(M=200) 分段积分 | 两实现差绝对值 |
|---|---|---|---|---|---|
| 5 | 3 | .075 | .925 | 1.345514764847035 | 3.05e−5 |
| 7 | 4 | .075 | .925 | 1.723096570942416 | 3.37e−5 |
| 7 | 4 | .12 | .88 | .837259217392892 | 5.37e−6 |
| 7 | 4 | .075 | 1.3 | 3.894850681328146 | 5.51e−5 |

中点误差来自 floor 跳点处的普通 quadrature；分段内部 affine 残差≤8.1e−11。
这只检查常数实现，不替代 p-adic 证明。

旧 `joint-grid-initial.json` 有五个不能使用的 B=3、λ=1−α 点：
(q,α)=(6,.15),(8,.015),(8,.03),(8,.125),(8,.15)。它们的 inner 分配缺乏正裕量，
并会出现负维，必须标为无效，不能因浮点 affine 检查通过而接纳。
其余 initial 34 点及检查时的 extra-rows 50 点、fewer-rows 280 点、cutoff 102 点
满足 2αB<1 和 δ_alloc>0；既有 B≥3 结果没有因新增条件而整体失效。

对 s=7,q=4,α=.075,λ=.925,M=400，B=2,3,4,5,6 分别给
A≈1.88492515,1.70260223,1.73606453,1.80250408,1.87679094。
缩小或扩大 cutoff 都没有改善这个基准点。
任意 h 的示例 α=.04,q=4,λ=.5,B=6,M=200 给 A≈1.548886009942714。

## 7. 目前达到与没有达到的结论

已得到完整泛函的 local bounds、改进的 Bernoulli rank threshold、任意 h 的
外区子式法，以及一个可计算的整数归一化增长上界。固定有理参数满足上述
正裕量条件后，这些论证给出渐近算术结论；不依赖浮点参数搜索为真。

准确的完成边界：本笔记已给出局部代数估值的证明及 prime-sum 的推导，
**没有实现逐个有限 K 的归一化 m，也没有产生完整机器可核验的素数指数证书**。
O_M(1) 的 uniform 性使用固定 M 下仅 O(M) 个类计数断点、每段点数误差≤2、
每个权重 O(M)，以及截取 h 个最负权重只改变 O_M(1) 个端点行；
这足以说明极限过程，尚未把每个隐含常数逐一展开。PNT 只给渐近归一化代价，
没有有效有限阈值。实数侧的全域 potential 上界及 O(K log K) remainder
不属于本子任务已验证的结论。

尚未得到 A+U<0，其中 U 为必须认证的实数侧 determinant 衰减常数。
已测参数的联合结果由 root 整合；这里未产生负裕量候选，因此没有为一个失败点
制作巨大 Fraction 表，也没有把数值 potential supremum 当作严格上界。
证明仍需：找到严格负裕量参数或新构造，再认证所有 real suprema 与最终常数，
并写明选定参数的统一 K_0。不能由当前数据声称 ζ(7) 无理，或声称整个方法不可能。

一个保留整数值基的未实施变体是分子 ∏_r D_(N_r)^(2q_r)。此时
b=Σq_rℓ(α_r x,z)、H=λ+Σq_rα_r，scalar 的 N 项改为
−4λxΣq_r floor(α_r x)。外区 Q(z)=Σq_r 1(z≤α_r/y)，δ=1(Q>0)，
权重变为 min(0,i+Q−(ℓ+s−1)/2)，rank 改用
[2λ−1+2Σq_rα_r−(s−1)y/2]_+。这允许分层零重数；尚未做联合优化或认证。
