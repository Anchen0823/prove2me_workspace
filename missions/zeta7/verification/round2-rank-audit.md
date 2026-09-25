# 精确次数、无穷远支撑与有限整数证书复核

2026-09-24。在现有 `exact_hankel.py` 的 `parameters` 中增加精确 `B_rank`；用它代替原来较松的 `min(h, pole_count)` 插值次数，并断言 `deg det(A+XB)=rank B`。数学依据是正定 `G(ζ(s))` 与对称 `B` 的合同变换；此处的运行仅检查实现。新记录还含 `infinity_threshold_L` 和适用时的 `predicted_B_rank`。旧的 188 个第二轮成功 gzip 文件及其中源码哈希**没有改写**。

当指数为整块 `g,g+1,...,g+h−1`，记 `d=2∑_j zero_multiplicities[j]`，通用奇数 `s` 的界为 `L=K−d−(s+1)/2−2g`。`B[i,j]=0` 若 `i+j<L`，等于 `(-1)^((s−1)/2)` 若 `i+j=L`。特别在 ζ(7) 是 `L=K−d−4−2g`、边界系数 `−1`。当 `L>2h−2` 时秩为 0；当 `h−1≤L≤2h−2` 时秩为 `2h−1−L`。脚本仅在此公式适用的区间强制预测秩，不对其余区间套公式。

[`round2-rank-tests.json`](round2-rank-tests.json) 保存八个小例：纯 Python `Fraction` 从原分子、分母重新求残数和 `B`，独立消元求秩；另在 `X=0,...,h` 直接求有理数行列式，用有限差分取得次数。八例的独立秩、直接次数和主算法次数一致。关键边界包括 ζ(7) 无零点 `K=10,h=2,g=0` 的常数行列式（`L=6,rank=0`），ζ(7) `K=12,N=1,q=1,h=4,g=0` 的 `L=6,rank=1`，以及整块平移、稀疏非连续指数、ζ(5)/ζ(9) 不同边界符号。重新计算四个 K40 控制/代表候选，其完整 primitive 系数仍逐项匹配旧 artifact。

[`round2-entry-tiny-audit.json`](round2-entry-tiny-audit.json) 保存四个 ζ(5)、ζ(7)、ζ(9) 小例。先调用独立有限 entry certificate 的原始矩阵匹配下界，然后逐个读取**精确原始 `Δ` 系数**并核对 `m_cert·Δ = gap_integer·P`，各系数均为整数且整体 gcd 恰为 `gap_integer`；所有被枚举素数上的实际最小 valuation 不小于 assignment 下界。这是小例的全系数、全素数整性检验，未推出任何渐近算术界。

按建议试过 K80 最佳 A 例的三种精确求值基，使用 [`tmp/zeta7/exact_basis_benchmark.py`](../../../tmp/zeta7/exact_basis_benchmark.py)，每种都将变基行列式除以 `det(T)^2` 后与原多项式精确相等。一次计时中，原基求多项式为 3.75 秒；monic Newton 基为 10.59 秒，带 `(2i)!` 缩放的 Newton 基为 11.22 秒（另有 0.10–0.15 秒组装成本）。两种变基均较慢，因此未据此重试先前 120 秒超时的 K160 样本。计时只是此环境的一次有界诊断。

旧第二轮 artifact 内 `exact_hankel.py` SHA-256 是 `138d595cbe9c32a43830f34be6d086c6b3359369fcc1830aa652dde362ecaee6`；这次添加 rank 断言后源码 SHA-256 为 `7a4ab50cd249f0c283c55c3aa1b366f5077a5e3ca1071c09679d815d0c4c8cb9`。后续复现应区分两个版本。
