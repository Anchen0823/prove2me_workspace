# 第二轮精确 Hankel 搜索：执行与核验

执行日期：2026-09-24。此文件只记录有限计算，不构成 ζ(7) 无理性证明。

## 参数与结果

`attack_round2.py` 将层 `[{N40,q},...]` 解释为分子 `∏ D_(N40·K/40)(t)^(2q)`；对于每个因子 `(t+j²)`，各层重数相加。行指数为 `exponents`，B 路线使用**整块平移** `g,g+1,...,g+h−1`，其中 `g=shift40·K/40`。A 路线令 `g=0`。全部参数及精确结果逐行保存在 [`round2-results.jsonl`](round2-results.jsonl)；每条成功记录的 `artifact_path` 指向完整 primitive 整系数的 gzip JSON。`basis_mode=whole_shift` 使基的定义明确。

| 阶段 | 成功数 | 最低 `log P(ζ(7))/K²` | 对应候选 |
|---|---:|---:|---|
| A, K40 | 156/156 | +0.6526094973 | 两层 `(N40,q)=(3,1),(6,3)`；`h40=20` |
| B, K40 | 20/20 | +0.6526094973 | 同一 A 候选，`shift40=0` 控制；真正平移中最低为 `shift40=1` 的 +0.6626367349 |
| A, K80 | 4/4 | +0.7123910455 | `(3,1),(6,3)`；`h40=20` |
| B, K80 | 4/4 | +0.7425370779 | `(3,1),(6,3)`；`h40=20, shift40=1` |
| A 与 B, K160 | 0/2 | 未知 | 两例各到 120 秒限时，标为 `unresolved` |

另有四个独立重算的控制例：ζ(5)/ζ(7) 各在 K40、K80 的 `(N,q,h)=(3,3,37)` 按比例放大。四组完整系数 SHA-256 与先前的 `exact_baseline.json.gz`、`exact_K80.json.gz`、`exact_K80_s5.json.gz` 完全一致。四个 B 路线 `shift40=0` 控制也与来源多项式哈希一致。A 的 156 个 K40 参数是 144 个双层组合和 12 个三层组合；B 的 20 个 K40 参数为原型及 A 最佳三种不同零点布局，各配五种 shift。K80 按每路线最低四个 `log P/K²` 候选晋级；K160 每路线最低一个晋级。排序先按 `log P/K²`，再按 `qsum,h,case_id`。同一阶段与路线的相邻 Arb 对数区间均不相交，所以当前排序没有球区间精度造成的并列歧义。

## 算术与区间核验

`P` 是与原始行列式 `Δ` 同方向的 primitive 整系数多项式：若 `Δ=A/d`、`content(A)=c`，则 `P=(d/c)Δ`。记录保存 `denominator=d`、`numerator_content=c`、约分后的 `primitive_scale_numerator/denominator`、系数哈希与完整系数。逐条重读 188 个成功 gzip artifact 后，已核对文件 SHA-256、系数 SHA-256、系数 gcd=1、`primitive_scale=d/c` 和 `exponents=range(g,g+h)`。Arb `log_interval` 的严格符号显示其中 186 个 ζ(7) 值均 `P(ζ(7))>1`，另两个 ζ(5) 控制值均满足 `0<P(ζ(5))<1`。K160 两例没有通过限时，不得列入成功或失败的数学样本。JSONL 是追加式检查点，含四条启动阶段参数序列化错误的旧事件；读取时按 `case_id` 取最后一条记录，实际唯一候选共 190 个。

新 `exponents` 接口与旧连续指数默认模式得到相同系数。小维度对连续、非连续与整块平移指数均在多个整数 X 上以精确有理数核对 `det(A+XB)=Δ(X)`；非法指数被拒绝。运行进程最多两个，每例单独 120 秒限时，成功记录随完成立即刷盘。超时保持 `unresolved`，再次运行同一命令会只重试未成功候选。

复现命令（工作区根目录）：

```powershell
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta7/scripts/attack_round2.py
```

Python 3.12.14、python-flint 0.9.0、mpmath 1.4.1、NumPy 2.5.3、SciPy 1.18.1。运行时 `exact_hankel.py` SHA-256 为 `138d595cbe9c32a43830f34be6d086c6b3359369fcc1830aa652dde362ecaee6`，`attack_round2.py` 为 `3cc6e9140d83c6287ffdc7ceee4f884d2c3670bd5bfeed36a0da7e87476352d9`；每个成功 artifact 也保存这两个哈希。若脚本随后修改，原结果仍以各 artifact 中记录的源码哈希为准。

有限的 `log P/K²` 可比较同一 primitive 规范化下的实际数值，但正值随 K 从 40 到 80 增大并不是渐近不可能性的证明。原先均匀 `q` 构造的理论 `A+U` 没有自动适用于分层零点或整块指数平移，不能与这些值混作已认证的同一指标。
