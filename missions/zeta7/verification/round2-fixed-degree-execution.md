# 固定次数分支：有限精确结果

2026-09-24。这里按 `deg Δ=rank B` 和 ζ(7) 的无穷远零三角公式，专门选取行列式次数 `m=1,3,5` 的三种层布局。令 `d=2∑q_a N_a`，`g=shift40·K/40`，逐个 `K=40,80` 取

```text
h=(K−d−2g−3+m)/2,
L=K−d−4−2g,
rank B=2h−1−L=m.
```

这使次数在 `K` 变大时保持固定，而 `h/K` 趋向 `1/2−∑q_a(N_a/40)−shift40/40`。选三种 `layers40`：`[(1,1),(3,1)]`、`[(2,1),(4,1)]`、`[(1,1),(3,1),(6,1)]`；每种配 `shift40=0,1` 和 `m=1,3,5`，共 `3×2×3×2=36` 个候选。完整确定参数在 [`round2-fixed-degree-manifest.json`](round2-fixed-degree-manifest.json)，成功结果在 [`round2-fixed-degree.jsonl`](round2-fixed-degree.jsonl)，各行 `artifact_path` 指向完整 primitive 系数 gzip。

| 阶段 | 成功数 | 最低 `log P(ζ(7))/K²` | 参数 |
|---|---:|---:|---|
| K40 | 18/18 | +0.7396646344 | 三层 `(1,1),(3,1),(6,1)`；`shift40=1,m=1` |
| K80 | 18/18 | +0.7976405783 | 同一固定次数族 |

全部 36 条均有 Arb `log_interval` 严格正下界，即 `P(ζ(7))>1`；每一条的精确 `degree=B_rank=predicted_B_rank=m`。逐条重读完整 gzip，文件与系数 SHA-256、primitive 系数 gcd=1、`primitive_scale=denominator/numerator_content` 均核对通过。18 对相同布局、shift 和次数的候选，从 K40 到 K80 的 `log P/K²` 都增大。由于未出现 `P<1`，按预定停止规则不扩至 K160。有限结果不能排除其他固定次数族或渐近构造。

其中 12 个 `m=1` 多项式的符号均为 `P(X)=a−bX`，`a,b` 是正整数。正值 `P(ζ(7))>0` 因而给出有理上界 `a/b>ζ(7)`；但本轮还严格得到 `P(ζ(7))>1`，所以这些上界没有达到整数线性型证明无理性所需的 `0<P(ζ(7))<1`。这只评价本轮的有限系数，不否定别的有理逼近序列。

本轮 36 个成功 artifact 中的源码 SHA-256 一致：`exact_hankel.py` 为 `7a4ab50cd249f0c283c55c3aa1b366f5077a5e3ca1071c09679d815d0c4c8cb9`，提供 worker 的 `attack_round2.py` 为 `3cc6e9140d83c6287ffdc7ceee4f884d2c3670bd5bfeed36a0da7e87476352d9`；检查点另存固定次数 runner `attack_fixed_degree.py` 的 SHA-256 `99d056f27122d72cb4a867807545ceb8716e23b5bf87cd09ce853fda349d5406`。这些与旧的第一批 188 个 artifact 的 `exact_hankel.py` 源码哈希不同，旧文件保持原状。

复现命令（工作区根目录；最多两个计算子进程，每例限时 120 秒，检查点可续跑）：

```powershell
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta7/scripts/attack_fixed_degree.py
```
