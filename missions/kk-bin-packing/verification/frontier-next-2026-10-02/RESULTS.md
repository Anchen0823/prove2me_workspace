# 望远镜归约与两个独立辅助定理

2026-10-02。Lean 4.33.1；Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。

| 内容 | 本地验证 | 平台状态 |
|---|---|---|
| `alg2_lin_telescoping` | 精确声明通过；只依赖下述两个既有开放节点 | [SKETCH_ACCEPTED](https://prove2.me/submissions/4d681118-a28c-41b7-95f0-d1e68f3fbbb7) |
| `geom_dominance_certificate` | 独立证明通过，无 `sorryAx` | [ACCEPTED](https://prove2.me/submissions/14fab497-6ca3-4f3e-9257-9ecd7ee5d6d6) |
| `lin_mono_submultiset` | 独立证明通过，无 `sorryAx` | [ACCEPTED](https://prove2.me/submissions/f6a79723-f605-481e-8251-2c1e668d071e) |

望远镜归约于北京时间 21:48:36 验收。它补齐执行轨迹的实例合法性、非空性和 `g > 1` 时零次迭代的边界，再从已有单步 LP 界和分组单调性得到首步较紧的求和界。

支配证书于北京时间 22:04:48、LP 删除单调性于 22:15:32 验收，两项定理均为 **Proved**，本次提交均为平台的首个接受提交。三份服务端源码均已回读，规范化 UTF-8 哈希与本地验证版本完全一致。

平台实际根定理的开放节点从 3 个减少到 2 个：

- `KKBinPacking.GeometricGrouping.alg2_size_recursion`
- `KKBinPacking.GeometricGrouping.geomGroup_bounds`

两者仍为 Open，完整算法尚未证明。支配证书只证明按重数的一一对应和尺寸比较；删除单调性只处理子多重集，不把它误用为任意逐项缩小的 LP 单调性。

分工：GPT-6 Astra 提供子多重集 LP 单调性，GPT-6.1 Sol 提供几何分组支配证书，GPT-6 Luna 提供轨迹边界草稿；主代理修正边界、完成望远镜证明、集成独立提交、编译与服务端核对。

`python scripts/workspace.py build kk-bin-packing` 已成功，本次构建覆盖 9 个任务根模块及其实际依赖。所有三份本轮正式源码都没有证明占位。两份直接证明的公理仅为 `propext`、`Classical.choice`、`Quot.sound`；归约的 `sorryAx` 只来自明确导入的两个平台定理镜像。

`workspace.py check` 与起始基线相同：仅两个既存的 five-primes 文件未归属；本任务新增文件均已登记。对应结果见 `workspace-check.txt`。仓库设置保留 CRLF，Git 空白检查按这一行尾规则执行。

机器可读证据：`local-checks.json`、`source-audit.json`、`mission-build-result.json`、`final-results.json`、`frontier-before.json` 与 `frontier-after.json`。本轮三项提交均已取得最终验收判定。
