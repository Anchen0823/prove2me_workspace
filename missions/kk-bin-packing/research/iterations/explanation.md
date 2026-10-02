# Algorithm 2 的迭代次数：递推归约

这是依赖平台子定理 `alg2_size_recursion` 的归约证明。该子定理目前仍为 Open，因此本提交应作为 sketch；本文件没有独立证明递推子定理，也没有导入待证的 `alg2_iterations_le`。

记 `Sᵢ = SIZE (tr.inst i)`，`L = log(1/g)`，`C = L / (1 − 1/k)`。由 `k ≥ 2` 和 `0 < g ≤ 1`，分母为正，且 `L ≥ 0`、`C ≥ 0`。递推子定理给出每次已执行迭代满足 `Sᵢ₊₁ ≤ Sᵢ/k + L`。恒等式 `C/k + L = C` 因而让归纳得到 `Sᵢ ≤ S₀/kⁱ + C`，其中初始步骤使用 `C ≥ 0`。

因为 `t ≥ 1`，最后一次运行的下标 `t−1` 合法。循环运行条件给出 `Sₜ₋₁ > 1+C`，与上面的几何界合并可得 `1 < S₀/kᵗ⁻¹`，即 `kᵗ⁻¹ < S₀`。此时两边均为正，可以对两边取自然对数：`(t−1) log k < log S₀`。又因为 `k ≥ 2`，有 `log k > 0`，故 `t−1 < log S₀ / log k`，从而得到平台要求的非严格界 `t ≤ log S₀ / log k + 1`。

证明只使用原有定义、Mathlib 和 `alg2_size_recursion`，不使用循环退出条件，不引用自身目标。数学步骤对应 Karmarkar–Karp (FOCS 1982), p. 316 的递推、几何界与对数估计。

本地验证使用 Lean 4.33.1。已定向构建 `Theorems.Thm_KKBinPacking_GeometricGrouping_alg2_size_recursion`，再以 `lake env lean missions/kk-bin-packing/research/iterations/draft.lean` 验证归约，退出码为 0。对正式源码的副本 `axioms.lean` 再次编译并执行 `#print axioms solution`，退出码也为 0，输出为 `[propext, sorryAx, Classical.choice, Quot.sound]`。这里的 `sorryAx` 来自导入的开放平台递推子定理，因此不能把此归约视为独立完整证明。最终任务 scope 构建由主代理统一执行。
