# 研究材料与正式证明

正式提交源码位于根目录 `Solutions/`，任务构建入口由 `../scope.json` 的 `build` 列出。使用 `python scripts/workspace.py build kk-bin-packing` 验证这些正式模块及其真实依赖。

本目录保存推导、子代理草稿、接口实验和证明说明，不是一个整体 Lean 构建目标。其中 `LinOptCheck.lean` 是早期失败的探针；`telescoping-audit/TraceBounds.lean` 的边界辅助引理在集成时修正，正式版本以 `Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_lin_telescoping.lean` 为准。不要把草稿存在视为已经验收。

本轮几何支配和 LP 删除单调性的正式独立版本分别为 `Sol_KKBinPacking_GeometricGrouping_geom_dominance_certificate.lean`、`Sol_KKBinPacking_GeometricGrouping_lin_mono_submultiset.lean`。本地精确类型、公理检查与平台判定见 `../verification/frontier-next-2026-10-02/`。

`lp-monotone/explanation.md` 还记录了任意逐项缩小场景中尚未形式化的概率分流构造；这部分不是已完成的证明。
