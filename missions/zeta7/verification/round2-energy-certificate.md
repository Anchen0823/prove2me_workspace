# 全域实数侧能量证书：选定移位分层参数

2026-09-24。参数为 `λ=1/2`、`γ=1/40`、两层 `(α,q)=(3/40,1),(3/20,3)`。此证书只给出 [第二轮解析框架](../research/round2-analytic.md) 中实数侧常数 `U` 的严格上界；它不提供对应的渐近整数化界，因而不证明 ζ(7) 无理。

从早先探索性 [`round2-energy.json`](round2-energy.json) 取 32 个嵌套圆弧的浮点显示值，将每个 `repr(float)` 小数**作为精确有理数**定义新区间端点与原始正权重，再用精确有理数把权重归一为总质量 `λ=1/2`。因此不需要证明原浮点优化所得端点有任何最优性。脚本逐项验证 `0<a_i<b_i<2`、`a_i` 严格递减、`b_i` 严格递增、所有权重为正且总和精确为 `1/2`。完整有理数保存在 [`round2-energy-certificate.json`](round2-energy-certificate.json)。

记 `J_α(t)=∫₀^α log(t+u²)du`，`V(t)=2π√t+J₁(t)−2∑q_aJ_(α_a)(t)−2γlog t`；`P_i(t)` 是第 `i` 个圆弧概率测度的对数势，`G(t)=2∑c_iP_i(t)−V(t)`。Arb 192 位区间运算认证全域上界 `sup_(t>0)G(t)<−153/25=−6.12`：

- `0<t≤ε=10⁻¹⁴`：所有圆弧在 `ε` 右侧；由 `P_i(t)≤log b_max`、`J₁(t)≥−2`、`J_α(t)≤J_α(ε)`、`log t≤log ε` 得 `G(t)<−6.4927110494`。
- `t≥T=2`：`P_i(t)≤log t`、`J₁(t)≥log t`、`J_α(t)≤αlog t+α³/t`，所以 `G(t)≤Dlog t−2π√t+C/t`，其中 `D=11/10`、`C=2∑q_aα_a³`。条件 `π√T>D` 使右端从 `T` 起递减；其 `T` 值 `<−8.1127571027`。
- `[ε,T]`：用所有圆弧端点预分段，再有理二分到 312 个闭区间。每段用端点势最大值减去 `V` 的 Arb 区间下界；其中 245 段进一步使用严格导数区间的中值上界。全部保存了有理端点和各自上界；逐段上界都严格小于 `−6.12`，覆盖区间无空隙。

嵌套圆弧的能量按精确权重恒等式 `I=∑(C_i²−C_(i−1)²)log((b_i−a_i)/4)` 计算。结合解析框架中的 `C*` 公式和已认证 `M<−6.12`，得到 `U=C*+λM−I<0.506826824116<0.507`。这个严格实数侧界仍为**正**，必须和适用的渐近算术上界合并，不能与有限 primitive 系数代价直接混用。

复现与重新逐段核验（工作区根目录）：

```powershell
$py = 'C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
& $py missions/zeta7/scripts/round2_energy_certificate.py --seconds 300
& $py missions/zeta7/scripts/round2_energy_certificate.py --verify
```

本次运行与 `--verify` 均通过。源数据 SHA-256 为 `bb037649a990ade51b64533b9802eb0aff9a2180fe92ac512eababf5fff279a1`，证书脚本为 `08037d71a906b8a4a5a51c9c20f0f5b40783f6760e264dc98bbe7d5735401f95`，并写入 JSON 供版本核对。
