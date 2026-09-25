# VC 的有限精确估值探测（偶数 `n=8..24`）

本探测针对每个偶数 `n=8,10,...,24`，枚举素数
`sqrt(7n/2) < p <= n`，由整数矩阵 `A_n=d_n^9 F_n` 的精确子式 gcd 计算
`N_n=|det A_n| delta_3/(delta_4^*)^2`，再用整除循环精确计算 `v_p(N_n)`。
形式系数由现有独立有理乘积重建器
[`check_prime_valuation_attack.py`](../verification/check_prime_valuation_attack.py#L55-L82)
生成；行列式展开见同文件第 85–89 行。`delta_3` 是列 `(A_3,A_5,A_7)` 的全部
三阶子式 gcd；`delta_4^*` 是列 `(A_3,A_5,A_7,B)` 与
`(A_3,A_5,A_7,A_9)` 的全部四阶子式 gcd。

## 数据

表内每个 `p:v` 表示该范围内素数 `p` 的精确估值 `v_p(N_n)=v`；所列素数均满足
`sqrt(7n/2)<p<=n`。`p>n/2` 的检查在本区间每个素数上都适用。

| `n` | 中间素数 `p:v_p(N_n)` | `p>n/2` 时是否均 `<=11` | 全部中间素数是否均 `<=12` |
|---:|---|:---:|:---:|
| 8 | `7:11` | 是 | 是 |
| 10 | `7:11` | 是 | 是 |
| 12 | `7:11, 11:9` | 是 | 是 |
| 14 | `11:8, 13:11` | 是 | 是 |
| 16 | `11:9, 13:10` | 是 | 是 |
| 18 | `11:9, 13:11, 17:11` | 是 | 是 |
| 20 | `11:9, 13:11, 17:10, 19:11` | 是 | 是 |
| 22 | `11:10, 13:11, 17:10, 19:10` | 是 | 是 |
| 24 | `11:11, 13:11, 17:11, 19:10, 23:11` | 是 | 是 |

因此在这个有限区间没有发现 `p>n/2` 且 `v_p(N_n)>11` 的例子，也没有发现中间素数
估值超过 `12` 的例子。没有反例，故无需另作反例证书。

本表只覆盖 `n≤24`。[后续精确局部证书](vc-local-smith-next.md)在 `n=234,p=29` 和 `n=258,p=257` 分别找到这两个全称候选界的反例；本表的有限观察不能外推。

## 复现

在仓库根目录的 PowerShell 中执行下列代码。它调用上面所指的有理形式重建器，直接
计算全部所需子式 gcd、行列式与 `N_n`，随后输出各个中间素数的估值。所有运算均为
Python 任意精度整数或 `Fraction` 精确运算。

```powershell
@'
import importlib.util, itertools, math
path = "missions/zeta9/roadmap/verification/check_prime_valuation_attack.py"
spec = importlib.util.spec_from_file_location("valuation_probe", path)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
for n in range(8, 25, 2):
    forms = m.exact_forms(n)
    q = math.lcm(*range(1, n + 1)) ** 9
    A = [[int(x * q) for x in row] for row in forms]
    d3 = math.gcd(*(abs(m.det([[A[i][j] for j in (1, 2, 3)] for i in I]))
                    for I in itertools.combinations(range(5), 3)))
    d4 = math.gcd(*(abs(m.det([[A[i][j] for j in (1, 2, 3, c)] for i in I]))
                    for I in itertools.combinations(range(5), 4) for c in (0, 4)))
    D = abs(m.det(A)); assert D * d3 % (d4 * d4) == 0
    N = D * d3 // (d4 * d4)
    ps = [p for p in m.primes(n) if math.sqrt(7*n/2) < p <= n]
    print(n, [(p, m.valuation(N, p)) for p in ps])
'@ | python -
```

## 证据边界

这是 `n=8..24` 的有限精确计算。它只能说明上述样本符合两个待探测的估值阈值，不能
推出对所有偶数 `n` 成立的 VC 结论、渐近界或任何渐近证明。
