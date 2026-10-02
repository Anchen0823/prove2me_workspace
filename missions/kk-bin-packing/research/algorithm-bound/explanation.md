# 根定理 algorithm2_bound 的条件归约

本文件把完整算法的箱数估计归约到既有里程碑，并直接证明两个必要的结构引理。它不是对全部开放里程碑的完整证明。正式源码只导入依赖的定理镜像，不导入目标自身。

令 A 是原始实例 I 删除所有大小不超过 g 的物品后的实例；令 P₀ 是第 3 步完成时的全部箱子。

1. 第 3 步里程碑给出 P₀ 正确装下 A，以及其箱数不超过主箱总数加 t·2k(2+ln(1/g)) 和最后一次装箱的常数项。
2. 对 AnyFit 的三种构造作归纳，直接证明插入保持物品守恒及容量合法。结合两个互补 filter 的并恰为 I，得到最终输出确实是 I 的装箱。
3. 把 AnyFit 箱数定理用于参数 2g（满足 0<2g≤1）。于是最终箱数不超过 max(|P₀|,(1+2g)OPT(I)+1)。
4. 若 t=0，主箱总数及迭代代价都是 0；所需的第 2 个 max 分支直接由第 3 步界及其余非负项推出。这样无需对空初始实例取对数。
5. 若 t≥1，循环运行条件和 ln(1/g)≥0 保证 SIZE(A)>0。因此 A 非空，可使用几何分组里程碑的 LIN(geomJ(A))≤LIN(A)。再由独立子定理 lin_le_opt 给出的 LIN(A)≤OPT(A)，以及本文件直接证明的 OPT(filter I)≤OPT(I)，得到 LIN(geomJ(A))≤OPT(I)。此处无需依赖包含更强舍入界的 size_le_lin_le_opt_le_lin_add 里程碑。
6. LP 望远镜里程碑控制主箱总数≤LIN(geomJ(A))+t。迭代次数里程碑及 SIZE(A)≤SIZE(I)、对数的单调性给出 t≤1+ln(SIZE(I))/ln k。因为 k≥2，分母 ln k 严格正；乘子的 1+4k+2k ln(1/g) 非负。
7. 将这些不等式代入第 3 步界并展开，恰得根定理第 2 个 max 分支；最后合并第 3 步的 AnyFit 最大值界。

其中 OPT(filter I)≤OPT(I) 的证明取一个达到自然数下确界的最优装箱，把同一谓词用于每个箱子。物品非负保证过滤后每箱总和不增加，而箱子的个数保持不变。最优装箱的存在则用每件物品一个单件箱子作为可行见证。

直接依赖仅为 alg2_step3_card_le、alg2_iterations_le、alg2_lin_telescoping、geomGroup_bounds、lin_le_opt 和 anyFit_card_le 六个子结论。没有导入目标 algorithm2_bound 本身。平台状态以主代理的实时核查为准。

开放定理镜像含平台占位证明，因此本地 kernel 检查的是明确声明的条件归约，不得据此宣称这些依赖已经解决。正式 solution 源码没有 sorry、admit 或新增 axiom。验证过程使用 pinned Lean 4.33.1 的 lake env lean 串行编译实际依赖及当前正式文件；没有构建全库。
