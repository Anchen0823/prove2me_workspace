# ζ(9) 第二轮：高阶极点与精确消元

2026-09-24。**本轮已完成，仍未证明 ζ(9) 无理。**
这次改变了有理函数的极点阶数。我们严格构造出正的、指数趋零的整数系数多 ζ 形式，
但消去其他 ζ 值后，测试得到的单 ζ(9) 形式失去了小量性质。

## 1. 执行的构造与范围

取 $p\in\{3,5,7,9\}$、$d=9-p$、$b=10-p$、偶数 $n$，定义

$$
R_{p,n,m}(t)=\frac{n!^p}{m!^{2b}}
\frac{[(t-m)_m(t+n+1)_m]^b}{(t)_{n+1}^p},\qquad
L_{p,n,m}=\sum_{k\ge1}\frac{R_{p,n,m}^{(d)}(k)}{d!}.
$$

要求 $2bm\le p(n+1)-2$。反射与无穷远条件严格消去偶数 ζ 值和最低阶项。
每个原子形式保留的值分别为：

| 极点阶数 $p$ | 保留的 ζ 值 | 消元所用相邻 $m$ 个数 |
|---:|---|---:|
| 3 | ζ(9) | 1 |
| 5 | ζ(7)、ζ(9) | 2 |
| 7 | ζ(5)、ζ(7)、ζ(9) | 3 |
| 9 | ζ(3)、ζ(5)、ζ(7)、ζ(9) | 4 |

在 $n=12,24,48$ 上执行 58 个均匀选取的窗口；因独立解析推导，另加 3 个 $p=9,m_{\rm start}=n$ 窗口。
再按预设下降门槛晋级 2 个窗口至 $n=96$。合计 **160 个不同原子、63 个消元组合**。
每例最多 120 秒，至多两个并发；没有超时、计算错误或秩退化。
完整参数表见[实验报告](research/elimination.md)。

## 2. 已闭合的局部结论：正的多 ζ 小形式

对 $p=9,m=n$，有

$$
R_{9,n,n}(k)=n!^7\frac{(k-1)!^{10}(k+2n)!}{(k-n-1)!(k+n)!^{10}}>0
\quad(k>n),\qquad L_n=\sum_{k>n}R_{9,n,n}(k)>0.
$$

把 $R$ 分解为九个具有整数残数的简单极点因子，证明

$$
F_n=d_n^9L_n\in
\mathbb Z+\mathbb Z\zeta(3)+\mathbb Z\zeta(5)+\mathbb Z\zeta(7)+\mathbb Z\zeta(9),
\qquad d_n=\operatorname{lcm}(1,\ldots,n).
$$

全域实数估计给出 $L_n\le \exp((-10.43+o(1))n)$，故

$$
\boxed{0<F_n\le\exp((-1.43+o(1))n)\longrightarrow0.}
$$

这不是从有限数据拟合出的结论：证明分别覆盖 $k/n\downarrow1$ 的一致 Stirling 误差、紧区间的全局相位上界和无穷尾部。
主代理另以 Arb 验证粗对数不等式，以整数算术验证导数比较，并直接核验了六个尺度的全系数整性与正值。
完整证明见[解析笔记](research/analytic.md)与[算术笔记](research/arithmetic.md)。

**该结论含有四个 ζ 值，不能指定 ζ(9) 为无理数。**
它复现了经典多值小形式的方法机制。简单极点乘积与相关系数消元的文献依据见
[Fischler–Sprang–Zudilin 原论文第 2、5 节](https://arxiv.org/html/1803.08905)；本轮的具体分解和界已在本地独立证明，未声称文献原创性。

## 3. 消元前后发生了什么

取同一 $(p,n)$ 的 $q=(p-1)/2$ 个相邻 $m$ 原子形式，先分别除尽整数系数 gcd，
再用低 ζ 系数矩阵的整数余子式作权重，精确消去全部其他 ζ 值，最后再约成 primitive 的 $P_n(X)=A_nX+B_n$。
所有低阶系数都按整数严格验证为零，没有使用浮点近似关系。

最有理论依据的 $p=9,m=n,n+1,n+2,n+3$ 窗口给出：

| $n$ | $m=n$ 原子多 ζ 形式的 $\log|\cdot|/n$ | 消元后单 ζ(9) 形式的 $\log|P_n(\zeta(9))|/n$ |
|---:|---:|---:|
{{CANONICAL}}

两列均已在各自的整个系数向量中除尽 gcd，所以差别不能通过重复清分母消除。
160 个原子中有 **49 个**认证绝对值小于 1；**63 个单 ζ(9) 组合全部认证绝对值大于 1**。
组合的符号为正 39 个、负 24 个，求值始终处理符号后再取绝对值对数。

两组晋级结果为：

| 参数 | $n=48$ 的指标 | $n=96$ 的指标 |
|---|---:|---:|
{{PROMOTED}}

这是有限实验，不是整个族不可行的证明。但它清楚显示：原子形式的衰减本身还不够，消元系数的增长必须同时受控。
固定满秩窗口内，任何可逆有理换基、重新缩放或差分基给出的最终 primitive 单值形式至多相差符号；
只改变同一个窗口的表示，无法改善本表中的绝对值。

## 4. 新增的统一算术结论

记 $D=d_{n+m}$、$E=d_n$、$G$ 为最高阶残数的 gcd。本轮对整个系数向量证明了安全乘子

$$
t_{\rm split}=D^{p-1}E^{10-p}/G.
$$

对 $p=7,9$、$m\le n$，简单极点分解另给出 $E^9$ 证书；对固定 $c$ 的 $m=n+c$，
乘子 $[(n+c)!/n!]^{2b}E^9$ 的额外对数成本仅为 $O(\log n)$。
这几种证书可以用有理 gcd 逐素数合并，但不能取代消元权重的估计。
全部素数都已纳入证明；有限证书没有使用渐近常数替代真实分母。

## 5. 独立核验

- 重读 160 份原子及 63 份组合，重算完整系数比例、gcd、输入哈希、所有余子式与消元向量，并用另一求和顺序重新进行 Arb 求值，223/223 通过。
- 三阶极点与首轮程序逐项完全一致；四种极点阶数分别通过完整多项式恒等式和直接 Taylor 求和加严格尾界检查。
- 独立算术实现验证了 309 个小参数的全部素数估值，并对 10 个代表案例直接展开 Taylor 乘积，核对各阶系数；所有 160 个实际原子另通过分拆及合并证书检查。
- 正多 ζ 小形式的解析证明与简单极点整性证明经过交叉审查。尚无最终消元形式在无穷序列上的非零与衰减证明。

证据入口：[消元审计](verification/elimination-audit.json)、[算术审计](verification/arithmetic-audit.json)、
[主代理独立核验](verification/independent-audit.json)、[组合结果索引](verification/elimination-results.jsonl)。

## 6. 下一条更有针对性的路线

本轮暴露的是随 $n$ 增长的消元代价。因此下一步优先寻找**系数关系预先受控**的多个形式。
原论文利用同一有理函数在有理移位上的求和，使各奇数 ζ 系数具有共同系数乘以 $d^s$ 的结构。
这里的下一步设想是重新构造仅含 $s=3,5,7,9$ 的版本，即
$S_d=B_d+\sum_{s=3,5,7,9}\rho_s d^s\zeta(s)$；该版本尚未建立。

对 $d=1,2,3,6$，已经精确算出与 $n$ 无关的整数权重

$$
(w_1,w_2,w_3,w_6)=(-7776,1701,-224,1),
$$

它们满足 $\sum_d w_dd^3=\sum_d w_dd^5=\sum_d w_dd^7=0$、
$\sum_dw_dd^9=6531840\ne0$，且 $\sum_dw_dd=-5040\ne0$。
这能在上述条件成立时用固定权重隔离 ζ(9)，见[精确代数种子](verification/shift-seed.json)。

**本轮只验证了这组条件性代数恒等式。** 原论文的构造要求 $s\ge3D$，$s=9,D=6$ 不满足；
因此不能直接套用其衰减与整性定理。还需重新设计有理函数、证明对应系数关系和全域估计。
这个方向尚未实施新的函数网格，也不是 ζ(9) 的证明。

## 7. 复现

从工作区根目录运行；脚本复用现有 python-flint/Arb 运行环境。首轮文件保留不变。

```powershell
$py = 'C:/Users/anche/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
& $py missions/zeta9/round2/scripts/attack_elimination.py --extend
& $py missions/zeta9/round2/scripts/audit_elimination.py
& $py missions/zeta9/round2/scripts/independent_audit.py
& $py missions/zeta9/round2/scripts/certificate.py --self-test
& $py missions/zeta9/round2/scripts/shift_elimination_seed.py
& $py missions/zeta9/round2/scripts/build_report.py
```

[机器摘要](verification/summary.json)与[文件哈希清单](verification/artifact-manifest.json)覆盖本轮交付。
本轮未开始 Lean 形式化，也未进行外部投稿。
