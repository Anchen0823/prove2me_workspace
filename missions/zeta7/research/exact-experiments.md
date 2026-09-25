# ζ(7) Hankel 多项式的精确算术实验

2026-09-24。这里复现提供的 `referpaper/ZETA5_IS_IRRATIONAL.pdf` 中的 ζ(5) 构造，并对同型 ζ(7) 泛函做有限参数实验。**没有得到 ζ(7) 无理性证明，也没有证明这类方法不可能成功。**

## 多项式与精确规范化

令 $D_m(t)=\prod_{j=1}^m(t+j^2)$。对奇数 $s\geq3$，使用论文公式的泛化

\[
\mu_s(t^e)=(-1)^eB_{2e+2}\frac{(2e+s)!}{(s-1)!(2e+2)!},\quad
\mu_{s,X}\!\left(\frac1{t+j^2}\right)
=j^{s-1}(X-H_j^{(s)})-\frac1{s-1}+\frac1{2j}.
\]

基准矩阵为 $G_{ij}(X)=\mu_{s,X}(D_N(t)^{2q}t^{i+j}/D_K(t))$，$0\leq i,j<h$，$\Delta(X)=\det G(X)$。正测度表示使 $\Delta(\zeta(s))>0$。除去共同因子后，极点数是 $r=K-N$，故 $\deg\Delta\leq\min(h,r)$；当 $h=r$ 时算得度恰为 $r$。

所有 $G_{ij}$ 都在 $\mathbb Q[X]$。脚本用 `python-flint` 精确构造矩与行列式。若 $\Delta=A(X)/d$，其中 $d>0$ 是所有系数的最小公分母、$A\in\mathbb Z[X]$，再令 $c>0$ 是 $A$ 的系数最大公因子，则

\[
P(X)=A(X)/c=(d/c)\Delta(X)\in\mathbb Z[X].
\]

这是与 $\Delta$ 同方向的**唯一 primitive 整系数规范化**，从而仍有 $P(\zeta(s))>0$。相同构造换基不会再降低 primitive 多项式的整体整数倍。这个实验取最小整数内容，比较的不是论文中用于渐近估计的保守局部规范化。

精确构造利用残数递推。记 $a_j=-j^2$，$R_e=t^eP_0(t)/D_{\rm tail}(t)=Q_e(t)+\sum_j r_ja_j^e/(t-a_j)$。则

\[
Q_{e+1}=tQ_e+\sum_jr_ja_j^e.
\]

因此每组参数只需一次多项式除法。$h\leq r$ 且 $X$ 系数矩阵可逆时，用其特征多项式求 $\Delta$；其他情况用 $X=0,\ldots,\min(h,r)$ 处的**精确有理数**行列式作 Newton 插值，并在额外整数点校验小矩阵。

## 认证的关键结果

表内 $P$ 均为上述 primitive 多项式。每个 $P(\zeta(s))$ 通过 Arb 球区间得到严格正下界，且 `log_interval` 包住其对数；表中显示约值。完整球区间和系数保存在下述机器可读文件。

| $s$ | $K,N,q,h$ | $\log P(\zeta(s))$ | $\log P/K^2$ | 结论 |
|---:|---:|---:|---:|---|
| 5 | 40,3,3,37 | −265.129066976873718 | −0.165706 | 按原论文参数复现，$0<P<1$ |
| 7 | 40,3,3,37 | +1227.119753148780355 | +0.766950 | $P>1$ |
| 7 | 40,3,4,37 | +1274.372591989417211 | +0.796483 | $P>1$ |
| 5 | 80,6,3,74 | −833.331534801571993 | −0.130208 | $0<P<1$ |
| 7 | 80,6,3,74 | +5414.209044297366941 | +0.845970 | $P>1$ |

K=40 的三组完整 primitive 系数在 `verification/exact_baseline.json.gz`；K=80 的 ζ(7) 和 ζ(5) 系数分别在 `verification/exact_K80.json.gz` 与 `verification/exact_K80_s5.json.gz`。每条还包含系数 SHA-256、精确分母、分子内容、Arb 位精度，以及 `P_interval`、`log_interval` 的严格十进制包围。区间三元组 `(mid,rad,exp)` 表示值属于 `[(mid-rad)*10**exp,(mid+rad)*10**exp]`。

有限扫描的 333 条保存记录含重复参数；其中 324 条 ζ(7) 的 `log_interval` 下界严格大于 0，9 条 ζ(5) 的上界严格小于 0。扫描范围：

- `exact_sweep.jsonl`：91 条，包括 ζ(7) 的 $K=8,12,16,20,24$、$q=2,3,4,5$、若干 $N/K$，以及 $K=32,40$ 目标例和 ζ(5) 对照；取 $h=K-N$。
- `exact_h_sweep.jsonl`：120 条 ζ(7)；$K=8,12,16,20$，$q=1,2,3,4$，$h$ 约为极点数的 0.5、0.75、1、1.25、1.5、2 倍。$h>r$ 时 $\deg\Delta\leq r$。
- `exact_h_large.jsonl`：45 条 ζ(7)；$K=24,32,40$，$q=2,\ldots,6$，$h$ 约为极点数的 0.55、0.7、0.85 倍。该组最小 $\log P/K^2$ 为 K=24,N=2,q=3,h=19 的 +0.665128；K=40 的该范围最佳为 N=3,q=4,h=31 的 +0.747067。
- `exact_zero_sweep.jsonl`：72 条 ζ(7)；$K=8,12,16$，八种非均匀或非前缀零点分布、三种 $h$。其中 $D_1^2D_2^2$ 分子相当于第 1 因子四重、第 2 因子二重。该组最小 $\log P/K^2$ 为 +0.395746。

有限结果说明：直接照搬 ζ(5) 的 $K=40,80$ 参数，在 ζ(7) 上得到很大的 primitive 值；这些特定参数不能提供所需的 $0<P(\zeta(7))<1$。所扫的其他参数也未给出小于 1 的值。有限计算不能排除未试的零点布局、矩阵维度、参数缩放方式或更大 $K$，更不能代替正二次指数上界的证明。

## 复现

本次使用 bundled Python 3.12：`C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe`。`python-flint`、`mpmath`、`scipy` 及 `numpy` 的 wheel 安装在工作区 `tmp/zeta7/exact_packages`；主脚本会自动将此目录加入导入路径。举例：

```powershell
$py = 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
& $py missions/zeta7/scripts/exact_hankel.py --cases 5:40:3:3,7:40:3:3,7:40:3:4 --coefficients --output missions/zeta7/verification/exact_baseline.json.gz | Out-Null
& $py missions/zeta7/scripts/exact_sweep.py | Out-Null
& $py missions/zeta7/scripts/exact_h_sweep.py | Out-Null
& $py missions/zeta7/scripts/exact_h_large.py | Out-Null
& $py missions/zeta7/scripts/exact_zero_sweep.py | Out-Null
& $py missions/zeta7/verification/exact_verify.py
```

`exact_verify.py` 本次报告 `Total: 333 saved certificates checked`，并核对完整系数文件的 primitive 内容与哈希。`exact_hankel.py` 的默认无附加参数运行是一个较小样例；完整基准文件使用上面的显式命令生成。
