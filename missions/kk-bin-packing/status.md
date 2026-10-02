# Karmarkar–Karp 几何分组装箱算法

2026-10-02：从线上开放任务中选择。

- Mission: `359adb44-9a24-441c-8a2b-bd71395fcad4`
- 首轮目标：`KKBinPacking.GeometricGrouping.alg2_step3_card_le`
- Theorem: `641936bb-5a63-4aa2-9352-d96c0186cb3f`
- Milestone: `60512c22-1463-4f7e-a718-99f57b5098bc`
- 初查状态 Open；无提交、无历史变更、无讨论或提及。
- 环境：Lean 4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。
- 原文：Karmarkar–Karp, FOCS 1982, pp. 315–317。
  https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf

## 本次证明

- 正式源码：`Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_step3_card_le.lean`。
- 证明了第 3 步的物品守恒、各箱容量合法和箱子总数上界。
- 分工：GPT-6.1 Sol 证明几何分组性质，GPT-6 Astra 证明装箱正确性，GPT-6 Luna 审查边界与数量口径；主代理完成计数、集成和提交。
- `python scripts/workspace.py build kk-bin-packing` 成功。只有目标中 `hk`、`hg0` 未使用警告：证明实际适用于更弱条件，保留平台原绑定。
- `#print axioms solution` 仅显示 `propext`、`Classical.choice`、`Quot.sound`。无 `sorryAx`，没有平台 Theorems 导入。
- 本地验证详情：`verification/local-verification.json`。
- 2026-10-02 19:28（北京时间）提交，19:40:59 服务器返回 **ACCEPTED**：`68a45a9e-63d6-4cff-b1b1-a11360be9146`。
- 复查目标状态 **Proved**，对应里程碑 `completed: true`；这是该定理的**首个接受提交**，归属当前账户。证据分别在 `verification/target-after.json`、`milestones-after.json`、`first-accepted.json`、`verdict.json`。
- [定理页面](https://prove2.me/theorems/641936bb-5a63-4aa2-9352-d96c0186cb3f) · [接受提交](https://prove2.me/submissions/68a45a9e-63d6-4cff-b1b1-a11360be9146)
- 人类可读证明：`explanation.md`。已随提交上传。

## 验证边界

此任务是完整算法中的一个里程碑。完整算法的根定理复查仍为 **Open**，证据在 `verification/root-after.json`。

`python scripts/workspace.py check` 仍报告本次开始前已存在的两个跨任务归属问题：

- `Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean`
- `Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2.lean`

本任务的所有新定义、定理镜像和正式证明均已登记；未修改其他任务的文件或清单。

平台技能本地旧版为 0.10.3，登录回报线上 0.11.6。本次读取了官方 main 的 0.11.6 SKILL 和 prove/discover 文档后执行，没有对有既存改动的整库做 pull。

## 2026-10-02：Lemma 2 的体积下界与舍入归约

本次选择平台的 Lemma 2 里程碑 `5455998b-e4e9-4edb-92fc-4effa3b071a2`。
GPT-6.1 Sol 完成直接下界，GPT-6 Astra 完成条件归约，GPT-6 Luna 独立核对原文与边界；主代理集成、构建与提交。

- 新增直接证明 `SIZE I ≤ LIN I`：
  `Solutions/Sol_KKBinPacking_GeometricGrouping_size_le_lin.lean`。
  [定理](https://prove2.me/theorems/6776b904-ac8c-4693-a670-aaa1a0aee5d6) 已为 **Proved**；
  [提交](https://prove2.me/submissions/62180682-e5b6-4539-bbe8-95e232733f4a)
  于北京时间 21:34:06 返回 **ACCEPTED**，并确认是当前账户的首个接受提交。
- 完整 Lemma 2 的本地归约：
  `Solutions/Sol_KKBinPacking_GeometricGrouping_size_le_lin_le_opt_le_lin_add.lean`。
  复用既有 `lin_le_opt` 和已证明的 `opt_le_two_size_add_one`，
  把剩余工作明确分成稀疏近最优 LP 解与向下取整证书两个开放核心。
  归约证明了最优整数装箱存在性、主部与残余拼接、残余界的平均，以及正误差趋零论证。
- 两个核心声明均已发布：
  [稀疏近最优 LP 解](https://prove2.me/theorems/a3149f0a-8819-48eb-a74d-26789cfba321)；
  [向下取整证书](https://prove2.me/theorems/d4f0eca3-b658-4ba1-82b1-267d1e0de27c)。
  两者尚未证明。父定理归约提交 `ad4a1544-6ebb-4451-9e9b-d7c58d819c46` 正等待服务器验证。
- 本地任务构建成功（6 个选定根模块）。并行 Mathlib 导入曾报缓存读取错误；
  串行构建新增依赖后，`python scripts/workspace.py build kk-bin-packing` 成功。
- 直接下界的公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
  条件归约辅助定理同样没有 `sorryAx`；父定理通过显式平台定理镜像导入待证假设，
  所以不能把该归约称为完整证明。
- 证据、解释、源文件哈希和类型/公理检查位于
  `verification/volume-2026-10-02/`。准备和验证脚本均只操作本任务；API 写入由主代理执行。

本次 `workspace.py check` 基线为上面的两个 five-primes 归属错误。
期间并行工作曾出现两个其他新增文件的临时未归属报告，后续已由其所属工作登记；
本次未修改那些文件。本次新增文件均已登记，最新归属检查只剩基线中的两个 five-primes 问题。
完整任务及 Lemma 2 尚未被本次工作直接证明。

## 2026-10-02 后续贡献：三项提交全部验收

本轮汇总：`verification/continuation-2026-10-02/final-results.json`。

- **独立证明 `lin_le_opt`：ACCEPTED / Proved**。定理 `555b051c-6aa5-4769-866f-a595b8c60e2c`；提交 `956de592-7e80-4f94-ae20-f0b7fe913d4e`，北京时间 20:39:35 验收。平台首个接受提交为本次提交。只导入实例和配置 LP 定义；本地公理仅 `propext`、`Classical.choice`、`Quot.sound`。
- **迭代界 `alg2_iterations_le`：SKETCH_ACCEPTED**。提交 `e96b7f2a-43fc-4061-a627-e7a78cc24166`，北京时间 20:24:23 验收。已完成从单步递推到对数迭代界的证明，只依赖开放的 `alg2_size_recursion`。
- **根定理 `algorithm2_bound`：SKETCH_ACCEPTED**。提交 `e04dd93a-25f4-405f-890f-3daf94e1c012`，北京时间 20:40:16 验收。连接 Step 3、迭代界、LP 望远镜界、几何分组界、独立 LP 下界与 AnyFit。

[LP 下界证明](https://prove2.me/submissions/956de592-7e80-4f94-ae20-f0b7fe913d4e) · [迭代界归约](https://prove2.me/submissions/e96b7f2a-43fc-4061-a627-e7a78cc24166) · [算法总界归约](https://prove2.me/submissions/e04dd93a-25f4-405f-890f-3daf94e1c012)

正式源码分别是 `Solutions/Sol_KKBinPacking_GeometricGrouping_lin_le_opt.lean`、`Solutions/Sol_KKBinPacking_GeometricGrouping_alg2_iterations_le.lean`、`Solutions/Sol_KKBinPacking_GeometricGrouping_algorithm2_bound.lean`。三份源码分别由主代理、GPT-6.1 Sol、GPT-6 Astra 完成，GPT-6 Luna 独立审查声明和边界。说明文档随三份提交上传；两项原有目标已按平台流程评分。

### 验证与边界

- 三份正式源码分别通过 Lean；匿名 example 使用平台原始声明逐个匹配 `solution`，均通过。两份归约的本地 `sorryAx` 来自明确导入的定理镜像，不代表其开放依赖已经证明。
- `python scripts/workspace.py build kk-bin-packing` 成功。为避免 Windows 并发加载 Mathlib 的资源错误，先串行构建实际依赖。构建后的 Python 输出因 GBK 不能显示警告符号失败，但完整 UTF-8 日志已保存，构建本身退出码为 0。
- 已回读平台实际存储的三份源码，其规范化 UTF-8 哈希与本地验证源码完全一致。
- 本轮新增文件均登记到 `scope.json`。`workspace check` 与执行前完全一致，仍只有上文两个其他任务的既存未归属文件，没有新增问题。
- 完整算法根定理仍为 **Open**。平台实际 frontier 已归结为三个开放子定理：`alg2_size_recursion`（单步递推）、`alg2_lin_telescoping`（LP 望远镜界）、`geomGroup_bounds`（几何分组界）。没有把两个接受的归约当作完整证明。

精确声明、公理检查、编译日志、提交回执、服务器判定、实际依赖图、源码哈希及评分响应均在 `verification/continuation-2026-10-02/`。独立审查见 `research/statement-audit-2026-10-02.md`。

## 2026-10-02：望远镜归约与直接辅助定理

最新结果见 [本轮验收与验证记录](verification/frontier-next-2026-10-02/RESULTS.md)。望远镜归约已获 SKETCH_ACCEPTED，根定理的开放节点从三个减少到两个；新证明和既有贡献均纳入本任务限定构建。平台最终判定和源码哈希以该目录的 final-results.json 为准。
