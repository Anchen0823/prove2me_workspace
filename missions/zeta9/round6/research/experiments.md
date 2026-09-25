# ζ(9) 第六轮：四次不变多项式的 primitive 选向

本轮固定上一轮的函数 $R_{9,n,n}(t)$，取 $u=t(t+n)$ 和

\[
 W(u)=\sum_{r=0}^{4}w_ru^r,\qquad w_r\in\mathbb Z.
\]

五个原始有理坐标按 $(B,A_3,A_5,A_7,A_9)$ 排列。只选同时满足 $A_3=A_5=A_7=0$ 的整数 $W$。旧档案提供 $n=12,24,48$ 的原始五列和饱和整数核；本轮对 $n=96,192$ 用同一精确部分分式算法重新生成五列，并用转置 HNF 的 unimodular 变换求饱和核。五个低核均为秩二。

设饱和核的两行整数基为 $K$，其原始像为两行 $(B,A_9)$ 矩阵 $F$。存档记录共同分母 $Q$、整数像 $J=QF$，以及 $J$ 的 Smith 不变量 $s_1,s_2$；逐个尺度有 $s_1=1$，$s_2$ 的十进制位数依次是 51、109、232、445、937。程序只试除小素数，剩余合数不声称已分解。**整数像 $J\mathbb Z^2$ 始终保持原状，没有把它擅自饱和。**

为比较 primitive 形式，程序在有理数域计算 $E=F^{-1}K$。一行整数对 $q=(B,A_9)$ 的有理原像是 $qE$。将 $E$ 的第 $r$ 列乘以 $n^{2r}$，统一清分母后作精确整数 LLL，并保留其 unimodular 变换。随后只枚举 LLL 两行的 $[-4,4]^2$ primitive 整数组合，按精确的

\[
 \|qE\|_{1,n}=\sum_{r=0}^4 |(qE)_r|n^{2r}
\]

排序；平方二范数及整数对只用于破同分。**前八个非纯常数方向在任何 ζ(9) 数值求值前已经固定。** 这与第五轮直接最小化整数 $W$ 高度的规则不同。对于每个方向，程序把 $qE$ 乘以最小正有理数 $S$，得到 primitive 整数多项式 $W=S qE$，再精确验证 $W=zK$、$z\in\mathbb Z^2$、五坐标像 $(SB,0,0,0,SA_9)$。因此真正的 primitive 乘子是 $M=1/S$，primitive 形式是 $B+A_9\zeta(9)$。中间的有理方向绝没有被误称为原整数像中的未缩放点。

| $n$ | 输入来源 | 前八候选 | 最小认证 $\log|B+A_9\zeta(9)|/n$ | 八个候选均 $|P|<1$ |
|---:|---|---:|---:|:---:|
| 12 | 第五轮档案 | 8 | −5.101469 | 是 |
| 24 | 第五轮档案 | 8 | −5.116920 | 是 |
| 48 | 第五轮档案 | 8 | −5.090410 | 是 |
| 96 | 本轮精确重算 | 8 | −5.072782 | 是 |
| 192 | 本轮精确重算 | 8 | −5.064944 | 是 |

表中小数只是存档内有符号 Arb 区间对数的显示值；40 个非零、$|P|<1$ 判断均由 Arb 区间给出。40 个已选 primitive $(B,A_9)$ 对两两不同，未出现纯常数方向。每个输入档案保存完整五列、饱和核、$F,Q,J,s_1,s_2$、小素数试除记录与来源哈希；每个搜索档案保存 $E$、LLL 整数矩阵与变换、选前清单、每个候选的整数 $W,z$、原始像、$M$、精确范数、Arb 球与源码哈希。`search-audit.json` 再次从档案重算全部 40 个整数提升和五坐标恒等式，并核对五个 SNF 与 LLL 变换。

复现命令（PowerShell，从工作区根运行；使用已配置的 bundled Python）：

```powershell
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round6/scripts/runner.py --phase both --n 12 24 48 96 192
& 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' missions/zeta9/round6/scripts/audit_search.py
```

`runner.py` 顺序运行、逐块 120 秒超时，并按源码哈希跳过已完成块；`--force` 会重算。结果位于 `missions/zeta9/round6/verification/search-input-n*.json.gz`、`search-n*.json.gz` 与 `search-audit.json`。

这是一组**有限计算证据**。秩二有理像中的任意 primitive 整数对都可经清分母获得某个整数 $W$，故 $|P|<1$ 本身既不是特殊整除增益，也不构成无理性证明。必须进一步证明一个随 $n\to\infty$ 取值趋零且非零的明确序列，并对 $\|qE\|_{1,n}$、乘子 $M$ 与解析积分给出统一严格界；现有五个尺度的负数不能替代这些证明。
