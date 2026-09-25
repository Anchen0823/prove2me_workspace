# ζ(9) 第三轮：固定权重有理移位的有限实验

本轮按预定网格完成 25 个精确案例，未得到绝对值小于 1 的 **primitive 整系数** ζ(9) 线性形式。25 个案例的系数、消元及符号均经独立存档重算；这只是有限计算结论，既不证明 ζ(9) 有理，也不排除别的参数或构造。

## 构造和精确计算

取 $D\in\{6,8\}$、偶数 $n>0$、$m\geq0$，满足 $2Dm\leq(10-D)n+7$。定义

$$R(t)=\frac{n!^{10-D}}{m!^{2D}}
  \frac{\prod_{\ell=-Dm}^{D(n+m)}(t+\ell/D)}{\prod_{j=0}^n(t+j)^{10}}.$$

仅约掉分子中 $\ell=0,D,\ldots,Dn$ 的因子；两端剩余的整数因子仍属于分子。得到九阶极点的精确部分分式 $R(t)=\sum_{j=0}^{n}\sum_{s=1}^9 c_{j,s}(t+j)^{-s}$。程序用 $c_{j,9}$ 与对数导数的 Taylor 递推计算全部 $c_{j,s}$，并逐例在三个有理点验证此恒等式。反射关系给出 $c_{n-j,s}=(-1)^{s+1}c_{j,s}$，衰减给出 $\rho_1=\sum_j c_{j,1}=0$，而 $\rho_{2,4,6,8}=0$。全部断言均以精确有理数检查。

对 $a=1,\ldots,D$，从 $k=0$ 开始求和得到

$$r_a=\sum_{k=0}^{\infty}R(k+a/D)
=B_a+\sum_{s\in\{3,5,7,9\}}\rho_s\zeta(s,a/D),\qquad
B_a=-\sum_{j,s}c_{j,s}\sum_{k=0}^{j-1}(k+a/D)^{-s}.$$

对每个 $d\mid D$，令 $S_d=\sum_{a=1}^d r_{aD/d}$。Hurwitz 乘法公式使 $\zeta(s)$ 系数成为 $d^s\rho_s$。用精确整数余子式解三个消元方程 $\sum_{d\mid D}w_d d^s=0$（$s=3,5,7$）：

| $D$ | 除数顺序 | 规范化权重 $w_d$ | $\kappa_9=\sum w_dd^9$ |
|---:|---|---|---:|
| 6 | 1, 2, 3, 6 | −7776, 1701, −224, 1 | 6531840 |
| 8 | 1, 2, 4, 8 | −32768, 5376, −168, 1 | 92897280 |

最终未经整化的形式是 $L=A\zeta(9)+B$，其中 $A=\kappa_9\rho_9>0$、$B=\sum w_dB_d$。取 $Q=\operatorname{lcm}(\operatorname{den}A,\operatorname{den}B)$、$g=\gcd(QA,QB)>0$，定义正的 primitive 乘数 $M=Q/g$，使 $P=ML$ 的两个整数系数互素。该唯一正比例规范化便于比较不同案例；它可能大幅放大很小的原始 $L$。本轮未把尚待独立证明的统一算术整化证书当作已证结果。

## 结果

表中三列分别为 $\log|L|/n$、$\log M/n$ 和 $\log|P|/n$。这些展示小数由 Arb 球导出；每例保存了有符号的球区间及全部精确系数。加号表示正值，负号表示负值。

| $D$ | $n$ | $m$ | 符号 | 原始 | 放大 | primitive |
|---:|---:|---:|:---:|---:|---:|---:|
| 6 | 6 | 0 | + | 1.22447 | 13.58826 | 14.81272 |
| 6 | 6 | 1 | − | −0.31037 | 13.94834 | 13.63797 |
| 6 | 6 | 2 | − | 1.14212 | 15.94610 | 17.08822 |
| 8 | 6 | 0 | + | 1.20687 | 18.96319 | 20.17005 |
| 8 | 6 | 1 | − | 2.35764 | 21.34920 | 23.70684 |
| 6 | 12 | 0 | + | 0.44445 | 16.27498 | 16.71943 |
| 6 | 12 | 1 | + | −0.13158 | 16.58017 | 16.44859 |
| 6 | 12 | 2 | − | 0.22216 | 16.44055 | 16.66271 |
| 6 | 12 | 3 | − | 0.83354 | 18.32950 | 19.16303 |
| 6 | 12 | 4 | − | 1.88201 | 19.01296 | 20.89497 |
| 8 | 12 | 0 | + | 0.40236 | 21.66084 | 22.06321 |
| 8 | 12 | 1 | − | 1.06662 | 22.31111 | 23.37774 |
| 6 | 24 | 0 | + | 0.13530 | 17.08554 | 17.22084 |
| 6 | 24 | 1 | + | −0.13340 | 17.11431 | 16.98091 |
| 6 | 24 | 2 | − | −0.01946 | 16.93483 | 16.91537 |
| 6 | 24 | 3 | − | 0.24755 | 16.98157 | 17.22912 |
| 6 | 24 | 4 | − | 0.53286 | 16.91688 | 17.44974 |
| 6 | 24 | 5 | − | 0.89956 | 17.55496 | 18.45452 |
| 6 | 24 | 6 | − | 1.35643 | 18.10975 | 19.46618 |
| 6 | 24 | 7 | − | 1.92879 | 18.90392 | 20.83271 |
| 6 | 24 | 8 | − | 2.68563 | 19.07687 | 21.76250 |
| 8 | 24 | 0 | + | 0.09860 | 22.28053 | 22.37913 |
| 8 | 24 | 1 | − | 0.51948 | 21.96602 | 22.48550 |
| 8 | 24 | 2 | − | 1.35582 | 22.19533 | 23.55115 |
| 8 | 24 | 3 | − | 2.49008 | 22.71482 | 25.20491 |

四个原始 $L$ 的绝对值小于 1（$D=6$ 的 $(n,m)=(6,1),(12,1),(24,1),(24,2)$），但全部 25 个 primitive $P$ 经 Arb 严格判定 $|P|>1$；其中 17 个为负。可比的 $m/n=1/12$ 剖面在 $n=12\to24$ 时，$D=6$ 的 primitive 指标为 $16.44859\to16.91537$，$D=8$ 的为 $23.37774\to23.55115$，都未改善。按预设晋级规则，本轮没有运行 $n=48,96$。

## 复现与证据

以工作区根目录为当前目录，用本地 bundled Python 运行：

```powershell
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round3/scripts/shift_forms.py --self-test
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round3/scripts/attack_shift.py
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round3/scripts/audit_shift.py
```

`attack_shift.py` 可续跑，每例独立子进程限时 120 秒，最多两个并发进程。25 条摘要在 `verification/shift-results.jsonl`；各例的完整 $c_{j,s}$、$B_a$、$\rho_s$、raw/primitive 系数、乘数、SHA-256 与 Arb 区间在 `verification/shift-D*-n*-m*.json.gz`。`verification/shift-audit.json` 逐例从存档精确重算部分分式、移位常数、消元、清分母与哈希，并以独立 Arb 顺序复查符号和大小；结果为 25/25 通过。源脚本 SHA-256 也保存在产物中。

## 单独的尾部移位分支

主网格完成后又按预先指定的六例测试另一构造。这里**有理函数不变**，直接采用第二轮 $p=9,m=n$ 的 $R(t)$，不增加分数零点；改变的是求和起点：$r_a=\sum_{k=n}^{\infty}R(k+a/D)$。因此常数项用 $H_{j+n}^{(s)}(a/D)$，不能沿用主网格的 $H_j^{(s)}(a/D)$。固定 $D=6,8$、$n=6,12,24$，复用上述四个除数的权重消去 $\zeta(3),\zeta(5),\zeta(7)$。该分支最高极点残数可交替变号；程序保留 $A$ 的真实符号，只用**正**的 primitive 乘数，不强制 $A>0$。

| $D$ | $n=m$ | 符号 | $\log|L|/n$ | $\log M/n$ | $\log|P|/n$ |
|---:|---:|:---:|---:|---:|---:|
| 6 | 6 | + | −11.33808 | 102.08507 | 90.74699 |
| 8 | 6 | − | −11.28721 | 129.42407 | 118.13686 |
| 6 | 12 | − | −11.11348 | 103.97461 | 92.86113 |
| 8 | 12 | − | −10.97011 | 139.68941 | 128.71930 |
| 6 | 24 | − | −10.95399 | 107.46228 | 96.50829 |
| 8 | 24 | − | −10.88798 | 142.69194 | 131.80396 |

六个未整化 $L$ 均经 Arb 严格判定 $|L|<1$，但六个 primitive 整系数 $P$ 均经 Arb 严格判定 $|P|>1$，且 $\zeta(9)$ 系数都非零。特别是原始形式约以 $e^{-11n}$ 衰减，而所需 primitive 乘数约以 $e^{100n}$ 或更快增长；在这六例中，算术代价完全压过解析衰减。有限样本仍不能推断所有 $n$ 的命运。

```powershell
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round3/scripts/tail_shift.py --scan
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round3/scripts/audit_tail_shift.py
```

六例的完整 PF、$B_a$、$\rho_s$、权重、raw/primitive 系数与 Arb 区间见 `verification/tail-shift-D*-n*-m*.json.gz`，清单见 `verification/tail-shift-results.jsonl`，逐例重算记录见 `verification/tail-shift-audit.json`。每例都是独立的 120 秒限时子进程，最多两个并发，清单支持续跑。
