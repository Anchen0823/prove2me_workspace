# five-primes 后续计划（2026-09-18 拟）

依据：2026-09-18 两次实测（root frontier 18 条；`theorem51_typeII_bound` 子树图 86 节点）。

## 0. 平台现状（事实层）

- **真 frontier**：`/theorems/59fb46ad/open-leaves` = **18 条**（跨 TaoFivePrimes / WeakGoldbach /
  Richstein2001 / RamareSaouter2003）。`?page=` 分页是坏的，别用。
- 18 条里按性质分：
  - **有限计算/数值证书**（3）：`rosser_psi_finite_middle`(1000<n<10^8)、
    `rosser_schoenfeld_theta_lower_analytic_mid`(1420≤t≤10^10，本次新造)、
    `WeakGoldbach.verified_range_sieve_coverage`；另 Richstein / RamareSaouter 两条需要 10^14 量级数据。
  - **引用型外部定理**（14）：R&S 三条（product_bound / schoenfeld_psi_error_large /
    已约简的 theta 两条）、Liu–Wang、Siebert、Ramaré 两条、Tao Prop 7.2、
    WeakGoldbach 五条（Helfgott–Platt 数值与三元 Goldbach 段）。
  - **已证伪**（1）：`theorem51_vaughan_split`（本次数值反例，评论 `1c0c941b`）。
- **`theorem51_typeII_bound`(605a083b) 已 Proved**，但它子树里仍挂着多个 Open 节点，其中两个
  与本地已编译成果直接相关：
  - `theorem51_typeII_dyadic_representation`(65017650, Open) —— 本地
    `Theorem51ScaleIntegralBridge` 链已证同一命题（只差 `Set.Ioi 0` 集合积分/可积性/支撑的适配）。
  - `theorem51_typeII_dyadic_block_bound`(5b36c013, Open) —— 节点自述「四个零件
    （large_sieve_subdivision / typeII_counting_bounds / typeII_pointwise /
    typeII_sqrt_expansion）都已在平台证明」，而 `theorem51_scale_bound_signed`(b111b484) 也
    已 Proved ⇒ 很可能是一个十几行的短约简。
  ⚠️ **但它俩不是 frontier 叶**（父节点已 Proved，树不再需要它们）⇒ 按平台计分口径
  **大概率不计分**；要计分需 captain 把 Lemma 4.11 / Theorem 5.1 的 milestone 重新挂上去
  （这两条 milestone 现在 `theorem: null`）。
- **Mathlib 侧的一条硬事实**（决定若干叶的可行性）：`Chebyshev.psi_le_const_mul_self` 的常数是
  `log 4 + 4 ≈ 5.39`，`Chebyshev.psi_le` 是 `log4·x + 2√x·log x`（主项 1.386x）。
  两者都**远弱于** `rosser_psi_finite_middle` 需要的 `1.03883x` ⇒ 该叶不可能靠 Mathlib 现成结果关掉。

## P0（低风险、本回合即可开工）孤儿节点收尾

1. `theorem51_typeII_dyadic_block_bound`：用 4 个已证零件 + `theorem51_scale_bound_signed`
   写短约简（预计 <50 行）。
2. `theorem51_typeII_dyadic_representation`：把本地 `Theorem51ScaleIntegralBridge` 及其依赖
   （ActualScaleKernel / ScaleReindex / NatOddReindex / FiniteScaleBridge / TypeIIFinite /
   EtaScale / ScaleSupport / ScaleIntegrals）捆进一个提交文件，补三块胶：
   (a) 平台 tsum `K(W)` = 本地有限 kernel（tsum→finset，`W∉(0,x)` 时归零）；
   (b) 支撑 `W ∉ Icc V (x/U) ⇒ ‖K(W)‖=0`；
   (c) `IntegrableOn (‖K(W)‖/W) (Ioi 0)` + 区间积分 → 集合积分。
3. 开工前发一条 comment 请 captain 把 Theorem 5.1 / Lemma 4.11 的 milestone 指向这两个节点
   （否则白干记分层面）。

**产出**：两个平台上的完整证明（可验证），并把本地 theorem51 机器变成平台资产。

## P1（有分量、忠于原文）`ramare_squarefree_totient_sum_le_large` 约简

目标：`N ≥ 142300 ⇒ Σ_{n≤N, sqfree} 1/φ(n) ≤ log N + 1.4708`。
节点自述已给出路线：Ramaré Lemma 3.2 的显式展开 + `θ(t) ≤ 1.001093 t`，经其 (3.10)–(3.12)
化到阈值 142300。做法与本次 θ 约简同型：

- 先取 numdam 原文（ASNSP 1995, 645–706, pp. 659–660）核对 (3.10)–(3.12) 的确切形式；
- 新子节点 1：Ramaré Lemma 3.2 的显式误差展开（源陈述，Open）；
- 新子节点 2（可选）：`θ(t) ≤ 1.001093 t`（若平台无此节点；这是一个 R&S 型显式上界，本身也可作为叶子排队）；
- 父节点用这两块 + 初等代数完成约简。

**产出**：一条真正的 frontier 叶约简，且把「硬」的部分压成两个标准显式分析输入。

## P1'（便宜，随 P0/P1 顺手做）把我们造的中段再降一档

`..._theta_lower_analytic_mid` 现在是 `[1420, 10^10]`；若把 `log t ≤ 8 t^{1/8}` 换成更细的分段界，
可把上端降到 `10^8`（Schoenfeld 输入的起点），使中段与使命既有计算叶 `(1000,10^8)` 对齐。
代价：一次新的提交（对同一目标通常不允许重复；应改为「约简我造的 mid 子」这条新边）。

## P2（高价值、重）`theorem51_vaughan_split` 的形式化证伪

平台有 `proof_type=disprove` 一级入口，且已有 Disproved 先例。前置工作两件：

1. **最小反例搜索**：找出失败实例中 `x` 最小、项数最少的一个，并给出 `|S|`、`inf_c T_I`、`T_II`
   的余量分布（决定证书规模）。
2. **证书可行性 spike**：对一组 `X_d / Y_d / T_II / S` 做有理区间估计（禁止 `native_decide`，
   只能用 `norm_num` + 分块聚合），先估单点成本，再决定是否生成整份 Lean 证书。

备选（更省，但只针对「证明步骤」而非平台节点）：形式化地给出一个两三元函数 `F`，
证明 Tao 论文里那一步 `½|Σ_{w>V} log w F(dw)| ≤ |Σ_n log n F(dn)|` 不成立——
这是很小的引理，可作为评论附件交给 captain 定夺。

## P3（阻断项，值得一次试探）ψ/θ 有限范围的 Lean 证书机制

3 条 frontier 叶（`rosser_psi_finite_middle`、新的 mid 子、WeakGoldbach sieve coverage）都卡在
「Lean 里做不了 10^8 量级对数求和」。建议做一次 **单点 spike**：对一对端点 `(b,a)` 证明
`ψ(b) < 1.03883 a`（取 b≈10^6，用 LCM/分块 + 有理 log 界），量出单点成本。
结论只有两种：要么能用几千个端点证书关掉某条叶，要么正式判定这几条叶在当前工具链下不可做，
从计划里划掉。

## P4（新领域、稳定产出）Mission IV：panmagic / symmetric 3 阶计数

`missions/project-review-2026-09-17.md` 的 S1/S2：定义层（`panMagicCount`/`symmetricMagicCount`）
已白送；发布 `Def_MagicSquaresSpecial3` → 建 Mission IV proposal + items + milestone →
证 `pan_three_card`、`symm_three_card`。全部是本地可控的组合计数，且前三个 magic-squares
使命（I/II/III）已经 goal Proved + proposal Reviewed。
**注意**：proposal 的 Submit 按钮只有宇轩本人能点。

## 建议顺序

P0（本周，两个可验证结果 + 把本地机器变成平台资产）→ P1（一条真 frontier 叶的实质约简）
→ P3 spike（决定三条有限叶的生死）→ P2 或 P4 视目标而定（要「难题推进」选 P2，要「稳定产出」选 P4）。

## 需要宇轩决定的

1. 目标是「平台计分」还是「难题推进」还是「稳定新产出」？
2. 孤儿节点（P0）要不要先干（不计分但结果是真的）？
3. vaughan 证伪（P2）现在就上，还是等 captain 对评论 `1c0c941b` 的回应？
