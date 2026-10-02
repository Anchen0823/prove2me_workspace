# 几何分组的逐项支配证书

目标证书 `KKDominance.geom_dominance_certificate` 的接口是：对任意自然数 `k` 和任意实数多重集 `I`，存在实数对的多重集 `pairs`，使其第一投影恰为 `geomJ k I`，第二投影是 `I` 的子多重集，而且每一对 `(rounded, source)` 满足 `rounded ≤ source`。子多重集关系按重数限制物品使用次数，所以它给出的确实是原物品槽位中的注入。

对每对相邻分组 `(A, G)`，取前组的前缀 `A.take G.length`，把每件 `x` 映射为 `(G.headD 0, x)`。这个前缀共有 `min(A.length, G.length)` 件；平台定义的下一组舍入部分 `G.take A.length` 也恰有这么多件，并将所有物品舍入到 `G.headD 0`。因此两者第一投影作为多重集完全相等。

所有配对的第二投影都是各前组的前缀。每个分组仅作为后一组的前组使用一次，故归纳相加后，第二投影受所有原分组的多重集和控制。已接受 Step 3 证明中的 `groups_sum` 将该和识别为 `I`。

为证明大小支配，先证明分组列表扁平化后就是原来的降序排列；这是 `takeUntil` 前缀与剩余后缀分割恒等式的递归应用。整个扁平列表降序，因而前组中的每件 `x` 都大于等于后一组的头 `G.headD 0`。后一组为空时证书对应部分为空，不产生边界例外。

上述论证只依赖排序与相邻分组结构，因此不需要 `IsInstance I`、`k ≥ 2` 或物品的正性。本研究文件直接复用已接受的 `Solutions.Sol_KKBinPacking_GeometricGrouping_alg2_step3_card_le` 模块里的两个已证辅助引理；未引用任何开放平台定理。

## 本地验证

已使用已安装 Lean 4.33.1 执行 `lake env lean missions/kk-bin-packing/research/geom-dominance/Certificate.lean`，退出码为 0，无警告。文件末尾的公理检查输出：

```text
'KKDominance.geom_dominance_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

没有 `sorryAx`。由于已确认沙箱内加载现有 Mathlib `.olean` 文件会失败，本次调用在沙箱外运行；不涉及安装或网络。
