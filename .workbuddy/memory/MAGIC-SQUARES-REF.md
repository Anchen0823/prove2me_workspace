# 幻方领域参考（prove2me_workspace）

**改选幻方题目、或给幻方开新 mission 之前先读这段。**
2026-09-18 评估 + 2026-09-19 修订。本文件从 `MEMORY.md` 拆出来（那边只留指针和两条红线）。

- 完整评估：`missions/project-review-2026-09-18.md`
- Mission V 设计书：`missions/magic-squares-v/DESIGN.md`
- 文献读法与 BCCG 结构定理：`referpaper/README.md` §五
- BCCG 2003 全文文本：`tmp/bccg.txt`

---

## 1. 平台规模与归属

- 幻方相关节点**实测 47 个**（9 定义 + 38 定理；搜索口径 `q=MagicSquares|magic|panmagic`），
  **全部 `Proved` / `Definition`，零 Open**（2026-09-19 复核）。旧记的「39 个 / 7 定义 + 32 定理」
  是漏查口径，已废。
- **43 个有 mission 归属，4 个孤儿全是定义**（`MagicSquaresTransforms`、`Normal3`、
  `Pandiagonal`、`MostPerfect`；定义没有 `theorem_id`，只能用 proposal reference item 挂）。
- 归属读法见 `MEMORY.md` 的「平台约定 → 成员资格」条。

## 2. 深度分布

- **$n=3$ 完全闭环**：$H_3/M_3/P_3/S_3$ + MacMahon 参数化 + 洛书唯一性 + 变换族。
- $n=2$ 现有 5 条（2026-09-18 P0 补齐 $H_2/M_2/S_2/P_2$ 与 BCCG 的 $P_3=\binom{t+2}{2}$）。
- **一般 $n$ 只有 1 条**（`magic_constant_of_normal`）；**$n\ge4$ 零**。
- ⇒ 基建是「$n=3$ 的完整理论」，**不是一般计数机制**。新项目要往「一般 $n$ / 更高阶」选，
  别再加 $n=3$ 的变体。

## 3. 🔴 两条红线

- **`IsPanMagic` ≠ BCCG 的 $P_n$**：我方要**两个方向**的断对角，BCCG 只要**一个方向**
  （含主对角、绕回、**不要求副对角** ⇒ 与其「magic」互不包含）。$n=3$ 实测：单向
  $=\binom{t+2}{2}$（即 BCCG 的 $P_3$），双向 $=\mathbf 1_{3\mid t}$。**引用时不可互相对照。**
  两个读法现在都在平台上并列（`Definitions/Def_MagicSquaresPandiagonal.lean` 的
  `IsPandiagonal`），就是为防张冠李戴。
- **Mathlib 无 Ehrhart / 拟多项式 / 有理生成函数**（精确 grep 过，「Ehrhart」0 命中）。
  只有凸几何侧的 `Analysis/Convex/Birkhoff.lean`、`DoublyStochasticMatrix`。
  **格点计数机制要自建**——这是所有「一般 n」路线的共同成本。

## 4. 文献结构（BCCG 2003 = 主要来源）

| 编号 | 内容 |
|---|---|
| MacMahon 1915 | $H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$；$M_3(t)=\frac29t^2+\frac23t+1\ (3\mid t)$ |
| [2] Anand–Dumir–Gupta 1966, Duke 33, 757–769 | 猜想 $H_n$ 是 $(n-1)^2$ 次多项式 |
| **Theorem 1 (Ehrhart 1973 / Stanley 1973)** | $H_n(t)$ **多项式**，次数 $(n-1)^2$；$H_n(-n-t)=(-1)^{n-1}H_n(t)$；$H_n(-1)=\cdots=H_n(-n+1)=0$ |
| **ref [14] = J. Spencer, "Counting magic squares", Amer. Math. Monthly 87 (1980) 397–399** | **Theorem 1 的初等证明** ← 「一般 n」唯一现实的入口 |
| **Theorem 2 (BCCG)** | $M_n,S_n,P_n$ 是**拟**多项式，次数 $n^2-2n-1$、$n^2/2-n/2-2$、$n^2-3n+2$ |
| Theorem 3 (BCCG) | $H^d_n(t)$（超立方体）是拟多项式，次数 $(n-1)d$ |
| Theorem 4 (Ehrhart) | 有理多胞形的整点计数是拟多项式，次数 = 维数，周期整除顶点分母的 lcm |
| Theorem 5 (Ehrhart–Macdonald) | $L_P(-t)=(-1)^{\dim P}L^*_P(t)$ |
| [4] Beck–Pixton | Birkhoff 多胞形的 Ehrhart 多项式（$H_4$ 的交叉校验来源） |
| [15] Stanley 1973 Duke 40, 607–632 | 线性丢番图方程与图的 magic labeling |

**库里只有 BCCG。** Spencer 1980、Beck–Pixton、Stanley 1973 要另找。
BCCG 原文第 55 行直说「there are **880** traditional 4×4 magic squares」。

**文献陷阱**：`referpaper/` 里 Beck–van Herick 算的是**互异正整数**（inside-out polytope），
不是弱读法；**最完美幻方（Ollerenshaw–Brée）的核心文献不在库里**。

## 5. 已核对的数值数据（2026-09-18/19）

**方法论警告**：判多项式阶数必须**「拟合后用剩余点回验」**，别用「差分到常数」——
点数不够时差分会给假结论（2026-09-19 用 8 个点把 6 次误判为已定）。
脚本：`tmp/order4_counts.py`、`tmp/order4_structure.py`、`tmp/scout_order4.py`。

### $n=3$
- $H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$：t=0..10 = 1, 6, 21, 55, 120, 231, 406, 666,
  1035, 1540, 2211（暴力枚举逐项一致）。

### $n=4$
- **$H_4(t)$ 是 9 次多项式**，t=0..14 全部验证（第 10 阶差分恒 0），系数：
  $\frac{11}{11340}t^{9}+\frac{11}{630}t^{8}+\frac{19}{135}t^{7}+\frac23t^{6}
  +\frac{1109}{540}t^{5}+\frac{43}{10}t^{4}+\frac{35117}{5670}t^{3}+\frac{379}{63}t^{2}
  +\frac{65}{18}t+1$。
  ✅ **2026-09-19 已与 Beck–Pixton 原文逐项核对一致**（DCG 30 (2003) 623–637, §3）。
  ⚠️ **首项 $11/11340$ 是 Ehrhart 多项式的首项系数，不是 $\mathrm{vol}(B_4)$**：
  $\mathrm{vol}(B_4)=4^{3}\cdot\frac{11}{11340}=\frac{176}{2835}$（计数格相对基本域体积 $n^{n-1}=64$）。
  对照 $\mathrm{vol}(B_3)=9/8$、首项 $1/8$。$9!\cdot$首项 $=352$ 作为**格归一化体积**是对的。
  **引用时别把首项系数当体积。**
- **$M_4(t)$**（t=0..12）= 1, 8, 48, 200, 675, 1904, 4736, 10608, 21925, 42328, 77328,
  134680, 225351。**次数由 Theorem 2 定为 7**（不再靠差分猜），**周期未知**；
  BCCG §4 说周期 = 顶点分母的 lcm。
- **对称 4×4 半幻方**：**周期 2、6 次**拟多项式。偶分支
  $1+\frac{16}{3}s+\frac{116}{9}s^2+\frac{52}{3}s^3+\frac{119}{9}s^4+\frac{16}{3}s^5+\frac89s^6$
  （11 点回验）、奇分支另一个 6 次式（10 点回验），两支首项都是 $8/9$。
- **对称 4×4 + 主对角 $=t$**：奇 $t$ 为 0；偶分支是 $s=t/2$ 的 **5 次**多项式
  $1+\frac{47}{12}s+\frac{55}{8}s^2+\frac{155}{24}s^3+\frac{25}{8}s^4+\frac58s^5$。
- **对称 4×4 幻方（两对角都 $=t$）**：奇 $t$ 为 0；偶部分**不是** $s$ 的多项式
  ⇒ **周期 4、次数 4**，恰等于 Theorem 2 的 $n^2/2-n/2-2=4$。
  t = 0,2,…,20 = 1, 8, 37, 112, 269, 552, 1017, 1728, 2761, 4200, 6141。

## 6. 可选路线

- **一般 $n$（推荐）**：BCCG Theorem 1 为目标，Spencer 1980 为硬梯级，$n=1,2,3,4$ 为
  具体检查点。详见 `missions/magic-squares-v/DESIGN.md`。
- **$n=4$ 特殊类**：对称 4×4 三条（数据已备），或最完美幻方 $n=4$——
  Ollerenshaw–Brée 是**构造 + 双射**（与 reversible squares），**不需要 Ehrhart**，
  但核心文献不在库里。
- **$n\ge4$ 计数**：$H_4$ 显式多项式可作独立梯级，但证明「对一切 $t$ 成立」需要机制。
