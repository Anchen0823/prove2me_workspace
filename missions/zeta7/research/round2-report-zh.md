# ζ(7) 攻击计划执行报告

日期：2026-09-24。**没有得到 ζ(7) 无理性的证明。** 已执行两条主攻路线，补充了由新次数公式导出的固定次数路线，并完成精确系数、有限整化与一份全域实数估计的验证。以下区分已证明的中间命题、有限计算与尚未闭合的渐近步骤；不主张这些中间命题具有文献上的新颖性。

本轮没有进行 Lean 形式化或外部提交。此前文献调研见 [literature-review-zh.md](literature-review-zh.md)。复现 ζ(5) 的有限计算不等于独立验证原论文的全部证明。

## 1. 执行了什么，数值告诉了我们什么

计算器新增可选 `exponents`，严格检查非负、递增和长度；默认基底保持不变。分子为多层前缀 `∏ D_(N_a)^(2q_a)`，平移路线使用完整基底 `t^g,...,t^(g+h−1)`。每例直接计算行列式的全部有理系数、清分母并除尽内容公因子，得到与行列式同方向的 primitive 整数多项式 P。

主搜索严格执行计划中的 144 个双层、12 个三层参数；B 路线采用原型和 A 的前三种零点布局，各有四种正平移及一个零平移对照。按 `log P(ζ7)/K²` 晋级，最多两个计算进程，每例限时 120 秒。全部成功结果都有完整系数、SHA-256、精确 primitive scale 和 Arb 区间，并可从检查点恢复。

| 路线 | K | 成功记录 | 最低 `log P(ζ7)/K²` |
|---|---:|---:|---:|
| A：分层重数 | 40 | 156 | +0.6526094973 |
| B：整体平移 | 40 | 20，含 4 个零平移对照 | 正平移最低 +0.6626367349 |
| A：晋级 | 80 | 4 | +0.7123910455 |
| B：晋级 | 80 | 4 | +0.7425370779 |
| A、B：再晋级 | 160 | 0/2 | 两例超时，未决 |
| 固定次数补充分支 | 40、80 | 36 | K40 +0.7396646344；K80 +0.7976405783 |

A 的最佳剖面为 `(N_a/K,q_a)=(3/40,1),(6/40,3)`、`h/K=1/2`；B 最佳正平移在此基础上取 `g/K=1/40`。原型 ζ(7) 对照在 K40 的指标约为 +0.7669498457。分层有有限改善，但同族 K80 没有向负值发展。

另有 ζ(5)、ζ(7) 各在 K40、K80 的四个独立重算对照。合计 **224 条成功记录：222 条 ζ(7) 均 P(ζ7)>1，两个 ζ(5) 均 0<P(ζ5)<1**。这些数字包含对照及重复构造，不是 224 个互不相同的参数空间结论。主代理用偶数／奇数系数拆分的另一求值顺序，对全部 224 份系数重新做 Arb 求值、gcd 和哈希核验。

两例 K160 不能算作数学上的失败。还测试了 Newton 换基能否加快精确求解：K80 基准从原基约 3.75 秒增至约 10.59／11.22 秒，逐项系数相同，因而没有据此重试 K160。

详见 [主搜索执行记录](../verification/round2-execution.md)、[固定次数记录](../verification/round2-fixed-degree-execution.md)、[独立区间复核](../verification/round2-independent-audit.json)。旧实验文件保留。

## 2. 已证明的代数结论与固定次数路线

多层分子和整体平移仍给出只含 `1,ζ(7)` 的仿射矩阵 `G(X)=A+XB`，且 `G(ζ7)` 严格正定。一个更精确的次数结论是

\[
\deg_X\det(A+XB)=\operatorname{rank}_{\mathbb Q}B.
\]

理由是以正定矩阵 `G(ζ7)` 共轭，得到实对称矩阵 C；`det G(X)=det G(ζ7) det(I+(X−ζ7)C)` 的次数正好等于 C 的非零特征值数。无需假定所有极点权重同号。

记 `d=2Σ q_aN_a`、`L=K−d−4−2g`。无穷远 Laurent 系数给出：当 `i+j<L`，`B_ij=0`；当 `i+j=L`，`B_ij=−1`。于是

\[
h-1\le L\le2h-2\Longrightarrow\deg\Delta=2h-1-L,
\qquad L>2h-2\Longrightarrow\deg\Delta=0.
\]

后一片参数区被严格排除：行列式是正有理常数，其正整数化结果至少为 1，不能用于所需反证。

这也导出固定次数 m 的序列：令 `2h=K−d−2g−3+m`。对于 m=1，得到

\[
\Delta_K(X)=\det Q_K\,(R_K-X),\qquad R_K\in\mathbb Q,quad R_K>\zeta(7).
\]

`R_K−ζ7` 是正 Gram 矩阵的 Schur 补，也等于一个首一多项式的最小加权平方积分。约分后的 primitive 多项式是 `a_K−b_KX`。固定次数只需证明这些正整数线性形式趋于零，逻辑上不必要求 `exp(−cK²)`；但这没有自动解决分母增长。

补充的 36 例采用三组较浅零点布局、两种平移、次数 1/3/5、K40/K80；全部实测次数等于预测值。12 个一次多项式均给出严格有理上界，但仍无小于 1 的线性形式。最佳一次剖面为三层 `(1,1),(3,1),(6,1)` 除以 K40 的尺度，`g/K=1/40`：

| K | 约分后的分母位数 | `log10(R_K−ζ7)` 的 Arb 近似 |
|---:|---:|---:|
| 40 | 570 | −55.43410789 |
| 80 | 2331 | −113.64701076 |

逼近虽准确，分母增长更快；乘回分母之后，目标值仍很大。此处没有用小数拟合替代证明。完整推导见 [round2-analytic.md](round2-analytic.md)，误差区间见 [rational-approximants](../verification/round2-rational-approximants.json)。

## 3. 有限算术证书：可以严格比较整化损失了

本轮构造了真正有限的正有理倍数 t，并证明 **tΔ∈Z[X]**，覆盖常数项和所有小素数。没有把渐近 `exp(AK²)` 当成有限分母。

- 独立的逐项证书：用 `min(v_p(A_ij),v_p(B_ij))` 的最小匹配权重下界行列式系数估值，并保存整数对偶势，认证匹配最优性。
- 结构证书：混合子式展开保留两个 Vandermonde 因子，以 p-adic 同余树计算极点子集下界；满足明确有限条件时再用 CRT 改进。
- Newton 基的逐项证书与结构证书逐素数取较强者。换基只改善估计，不改变同一行列式的 primitive 多项式。

若 `P=m_prim Δ`，则 `t/m_prim` 是正整数，可以严格定义有限缺口 `g_K=log(t/m_prim)/K²`。最佳 A 剖面的比较为：

| K | 原单项式逐项界 | Newton 逐项界 | 混合子式＋CRT | 逐素数合并 |
|---:|---:|---:|---:|---:|
| 40 | 2.474278 | 1.318488 | 0.475886 | 0.377357 |
| 80 | 3.081579 | 1.474453 | 0.748908 | 0.321936 |

全部 186 条主搜索 ζ(7) 成功记录均通过结构乘子／primitive scale 的精确整除检查。证明及实现经过独立审查；一个尚未证明的整数值基估计已明确禁用，未进入有效下界。对 K160/320 只计算了有限结构乘子，没有声称获得这些规模的 primitive 值。

仍缺少足够强的统一渐近算术界，尤其是小素数公因子以及多层内区的完整分配论证。见 [结构证明](round2-arithmetic.md) 和 [独立匹配证书证明](round2-entry-certificate.md)。

## 4. 已认证一份全域实数侧上界

对最佳正平移剖面，外场为

\[
V(t)=2\pi\sqrt t+J_1(t)-2J_{3/40}(t)-6J_{3/20}(t)-\tfrac1{20}\log t,
\quad J_a(t)=\int_0^a\log(t+u^2)\,du.
\]

把 32 个嵌套弧正弦分量的端点选为明确有理数，并把权重精确归一到 1/2，得到固定比较测度 ρ。以两端解析界及中间 **312 个闭区间** 的 Arb 计算证明

\[
2U_\rho(t)-V(t)<-153/25\quad(t>0).
\]

这里覆盖整个半轴，已经不只是最大值采样。初次认证使用 192 位，主代理再从保存的有理测度和区间划分以 256 位重放，核对无空隙覆盖、两端界及能量。

统一采用平移阶乘归一化

\[
S=\frac{4^{h-1}(K!)^{2h}}
 {\prod_a(N_a!)^{4q_ah}\prod_{i=0}^{h-1}((2(g+i))!)^2}.
\]

结合已证明的势能比较引理，得到

\[
\log(S\Delta_K(\zeta(7)))
\le U K^2+O(K\log K),\qquad U<0.506826824116<0.507.
\]

这是有效的实数侧上界，数值仍为正；它本身不推出实际值增长，也不推出无理性。要沿此证书闭合，仍需整化倍数的统一负增长足以抵消它。有限规模的整化成本不能直接冒充渐近常数。

详见 [全域证书说明](../verification/round2-energy-certificate.md) 及 [256 位重放记录](../verification/round2-energy-replay.json)。

## 5. 停止点与复现

完成了计划中的有限参数域、递增规模试验、严格代数引理、有限整化证书和一份全域实数侧证书。**没有闭合最终负指数，也没有证明两条路线渐近不可能。** 两例 K160 保持未决；找到有效路线之前未开始 Lean 形式化。

当前证据不支持仅继续提高同一候选的 K 或进行同空间换基。继续研究必须解决小素数整除性的统一控制，或找到精度与分母增长更有利的新函数空间；固定次数路线已提供一个可以单独分析的有理上界序列。完整原始系数已包含有限参数下所有整体公因子，不能再靠约分让同一个 P 变小。

在工作区根目录用 PowerShell 复核：

```powershell
$zetaPython = 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
& $zetaPython missions/zeta7/scripts/attack_round2.py --limit-new 0
& $zetaPython missions/zeta7/scripts/round2_independent_audit.py
& $zetaPython missions/zeta7/scripts/round2_independent_audit.py --input round2-fixed-degree.jsonl --output round2-fixed-degree-independent-audit.json
& $zetaPython missions/zeta7/scripts/arithmetic_round2_checks.py
& $zetaPython missions/zeta7/scripts/round2_energy_certificate.py --verify
& $zetaPython missions/zeta7/scripts/round2_energy_replay.py
& $zetaPython scripts/workspace.py check
```

去掉 `--limit-new 0` 会恢复主搜索，只重试未成功的候选，包括两份 K160 超时记录。完整系数在 `verification/round2-coeff/` 与 `verification/round2-fixed-degree-coeff/`；JSONL 按 case_id 取最后一条状态，保留了早期已修复的启动错误事件。依赖位于 `tmp/zeta7/exact_packages`，运行版本与源码哈希见各证书和执行记录。
