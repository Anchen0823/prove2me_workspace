# KK 装箱算法归约声明审查（2026-10-02）

范围：只读审查 `alg2_iterations_le`、`algorithm2_bound` 的形式声明、续做验证 JSON、任务定义及现有 Step 3 证明。未改正式 Lean 文件，也未运行构建。

## 结论

两个目标的数学声明都可由计划中的引理推出，常数吻合；未发现反例。最初读取的 verification JSON 快照中，`alg2_size_recursion`、`alg2_lin_telescoping`、`geomGroup_bounds`、`size_le_lin_le_opt_le_lin_add` 均为平台 `Open`；当时线上已 Proved 的相关依赖只有 Step 3 计数/装箱和 `anyFit_card_le`。之后新增了独立的本地 `lin_le_opt` Solution；本报告没有核查其平台状态。

## `alg2_iterations_le`

声明有 `ht : 1 ≤ tr.t`，这是必要的。记 `Sᵢ = SIZE (tr.inst i)`、`L = log(1/g)`、`T = 1 + L/(1−1/k)`。由 `g ≤ 1` 得 `L ≥ 0`，由 `k ≥ 2` 得分母为正，所以 `T ≥ 1`。取最后一次执行 `i=t−1`，`tr.loop_run` 给出 `S_(t−1) > T`。

递归定理只需使用最后一项 `S_(i+1) ≤ Sᵢ/k + L`，对前 `t−1` 步展开：

`S_(t−1) ≤ S₀/k^(t−1) + L · Σ_{j=0}^{t−2} k^(−j) ≤ S₀/k^(t−1) + L/(1−1/k)`。

与严格循环条件合并，得到 `S₀/k^(t−1) > 1`，于是 `t−1 < log(S₀)/log(k)`，足以推出目标的非严格界。`t=1` 时展开是零步，几何和为空，论证仍成立。`loop_exit` 不需要。

重要陷阱：不要照抄论文里把 `SIZE(I_t)` 当成大于 `T` 的量；当前 `Alg2Trace.loop_exit` 明确给的是 `SIZE(inst t) ≤ T`。正确的严格下界来自最后一次 `loop_run`，对象是 `inst (t−1)`。当 `t=0` 时原目标右侧甚至可能小于零，因此现有 `ht` 不能删除。

依赖建议：迭代归约只需递归结论的最后一项，不需要它前面四段 LP/支持集链条，也不需要 geom-group 或 LP-opt 定理。若可把依赖收窄，单独陈述并证明 `alg2_size_shrinks`（每步大小递推）会比把完整 `alg2_size_recursion` 当成该归约的必需条件更精确。

## `algorithm2_bound`

令 `L = log(1/g)`。`g ≤ 1/2` 使 AnyFit 引理可用参数 `2g ≤ 1`；其“大件”恰为 `p > g`，与 Step 3 打包对象一致，其“小件”恰为 `p ≤ g`，与 `tr.P_insert` 一致。

Step 3 的箱数上界加 telescoping 的 `ΣXᵢ ≤ LIN(J₀)+t` 后为

`LIN(J₀) + t·(1 + 4k + 2kL) + 2 + 2L/(1−1/k)`。

再用 `LIN(J₀) ≤ OPT(I)` 及迭代界 `t ≤ 1 + log(SIZE I)/log k`，正好得到目标第二分支中的表达式；AnyFit 给目标第一分支 `(1+2g)OPT(I)+1`。`hS : 1 ≤ SIZE I` 保证 `log(SIZE I) ≥ 0`，所以目标中乘 `t` 的系数可用于替换，且零次循环时直接有 `0 ≤ 1 + log(SIZE I)/log k`。装箱合法性由 Step 3 的 `IsPacking` 和 AnyFit 的关系给出。

需显式处理的边界与前提：

- `inst 0 = I.filter (g < p)` 可能为空，即使 `SIZE I ≥ 1` 且 `g ≤ 1/2`。因此不能无条件调用要求 `hne : I ≠ 0` 的 `geomGroup_bounds`。空实例时需单独化简 `geomJ k 0 = 0`、`LIN 0 = 0`；非空时才用几何分组给出的 `LIN(J₀) ≤ LIN(inst 0)`。
- 继续把 `LIN(inst 0)` 压到 `OPT(I)`，需要 `LIN(inst 0) ≤ OPT(inst 0)` 以及过滤子实例的 `OPT(inst 0) ≤ OPT(I)`。完整 LP 界中的其他部分（特别是 `OPT ≤ LIN +(m+1)/2`）在这条推导中未用到。完整 geomGroup_bounds 中的 SIZE、OPT 结论也未用到。
- 将 `SIZE(inst 0)` 的迭代界转为输入大小，需要 `SIZE(inst 0) ≤ SIZE(I)`；用输入 `hS` 得到输入对数非负。对 `t≥1`，最后一次 loop_run 还给出 `SIZE(inst 0) > T ≥ 1`，确保迭代界涉及正数的对数。
- 所有系数符号都正确：`L ≥ 0`、`1−1/k > 0`，故 `C = 1+4k+2kL > 0`。Step 3 的 `t·2k(2+L)` 与 telescoping 的 `+t` 合并为 `tC`，没有丢掉常数。

依赖/循环审查：预期 DAG 为 `algorithm2_bound → {Step3, telescoping, iterations, AnyFit, LIN(J₀)≤OPT(I)}`，`iterations → size recurrence`。`LIN(J₀)≤OPT(I)` 可由窄化后的几何分组线性下界、窄化后的 `LIN≤OPT`、以及 OPT 对子多重集的单调性组成；不必依赖整个 `geomGroup_bounds` 三项或 LP 的加性上界。用目标 `algorithm2_bound` 证明这些前提会构成循环，必须避免。定义本身 `Alg2Trace` 不引用上述结论，未发现结构性循环。

## 状态证据与文件

在本报告最初读取的快照中，`verification/continuation-2026-10-02/iterations.json` 与 `recursion.json` 状态均为 `Open` 且提交列表为空；`telescoping.json`、`geom-bounds.json`、`lpbound.json` 也为 `Open`。当时 `milestones.json` 标记 Step 3 (`60512c22-1463-4f7e-a718-99f57b5098bc`) 和 Lemma 3 / AnyFit 已完成，迭代及最终界尚未完成。它们是该快照的状态证据，不替代后续平台状态核查。

## 正式 Solution / 草稿复核（追加，2026-10-02）

### 迭代数归约草稿

`Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_iterations_le.lean` 现已存在，theorem `solution` 的参数和结论与目标声明一致。证明对 `i ≤ t` 归纳，每步只取递归定理的最后一项；在 `i=t−1` 使用 `loop_run`，再取对数并除以正的 `log k`。`ht` 保证下标合法，包括 `t=1` 时下标为 0。未用 `loop_exit`、目标自身或直接写入的假证明。另一代理已报告该正式文件 Lean 编译 exit 0；本审查没有重跑。当前文件仍导入 Open 的 `alg2_size_recursion` Theorems 镜像，因此它是对递归里程碑的条件归约，不是无外部前提的独立证明；该镜像含 `sorry` 占位。

恒等式 `C/k + log(1/g)=C`、几何展开及 `Real.log_lt_log` 的正性前提在源码中均正确。`research/iterations/axioms.lean` 还准备了 `#print axioms solution`，但本次没有可读的命令输出记录；因此本代理不声称亲自测得其传递公理集合。

### 完整算法归约

`Solutions/Sol_KKBinPacking_GeometricGrouping_algorithm2_bound.lean` 的 `solution` 声明与目标 theorem 的所有参数、结论和常数一致。两个局部 helper `filter_sum_le` 与 `opt_filter_le` 分别依赖非负件重的筛选和由整包逐箱过滤得到子实例装箱；构造最优装箱使用 `Nat.sInf_mem`，先证明可行装箱集合非空。`anyFit_packing` 按 AnyFit 的 `intoBin` / `newBin` 构造归纳，维持件数守恒和箱容量。源码未见直接 `sorry`、`axiom` 或目标定理自引用。

边界实现整体吻合目标：`t=0` 单独使用 Step 3 的零次求和界；`t>0` 取 `htpos`，从 `loop_run 0` 得初始筛选实例大小为正，再合法调用要求非空实例的 geom grouping 界；此处理覆盖了 `SIZE(I)≥1` 但 `inst 0` 为空的逻辑可能性，因为在 `t>0` 分支中 loop 条件本身排除了空实例。`g≤1/2` 被转换成 AnyFit 的参数 `2g≤1`，筛选分割为 `p>g` 与 `p≤g`，与 Step 3 和插入定义一致。`hsize_le`、对数单调性及正系数 `hcoeff` 将两个上界合并时方向正确。完整来源声明使用 `LIN(J₀)≤LIN(inst 0)≤OPT(inst 0)≤OPT(I)`；这正是非空分支需要的三段。

### 依赖状态和无绕过边界

两份归约源码都没有直接写入假证明。迭代 Solution 导入的 `alg2_size_recursion` 镜像以 `by sorry` 结束。root 当前导入 Step 3、iterations、telescoping、geom bounds、`lin_le_opt`、AnyFit 的 Theorems 镜像；这些本地镜像仍含 `sorry` 占位。主代理提供的 `source-verification.json` 与当前 root 文件 SHA-256 一致，并记录 binder/statement exact、无直接 sorry/admit/axiom、编译 exit 0。对应 `local-verification.txt` 的 `#print axioms` 输出明确包含 `sorryAx`：所以 exit 0 只确认条件归约源码可编译，不证明其依赖已关闭。已接受的线上里程碑是否由提交服务替换为真实证明，需以平台绑定和审计结果为准。本代理没有亲自编译或运行公理检查。

新建的 `Solutions/Sol_KKBinPacking_GeometricGrouping_lin_le_opt.lean` 是独立证明：它只导入两个 Definitions 模块，未导入 Theorems、其他 Solution 或 Open 里程碑；helpers 从 packing 构造 LP 可行解，并用达到自然数下确界的最优装箱给出 `LIN≤OPT`。源码静态检查未见 `sorry`、`admit`、`axiom` 或不透明占位。因此该 direct child 的数学证明没有隐含 Open 定理依赖。与此同时，root 导入的是 `Theorems.Thm_KKBinPacking_GeometricGrouping_lin_le_opt` 镜像，而不是这个证明文件；该镜像当前仍是 `by sorry`，故 root 的本地 `sorryAx` 不会因新增 Solution 自动消失。其他 Open 依赖也仍然存在。


