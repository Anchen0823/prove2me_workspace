# Mission: magic-squares — 幻方形式化基础建设

负责人：anche（徐宇轩） · 环境：Lean 4.33.1 / Mathlib `0df444a3` · 平台：prove2.me v0.10.3

最后更新：2026-09-17 02:20（goal 已 Proved）（Asia/Shanghai）

## 0. 本次会话的主线

宇轩在手机上给出了一张 8 条的建设顺序建议（行和汇总 → 转置/翻转 → 仿射 →
三阶中心 → 中心对称格 → 三参数构造 → 还原 → 唯一性），本轮据此推进，
并按他的建议把**长路径定理改为 mission 管理证明 DAG**。

## 1. 目标

在 prove2me 平台上从零建立**幻方（magic square）**领域的形式化基础：
定义层 → 结构层 → 计数层。平台上此前没有任何幻方内容（2026-09-16 检索确认）。

## 2. 文献

`referpaper/` 下 11 篇，清单与形式化切入点见 `referpaper/README.md`。

- **计数主线**：Beck–Cohen–Cuomo–Gribelyuk (2003, AMM 110) — $H_n,M_n,P_n,S_n$ 的定义基准；
  Beck–Zaslavsky (2006, 2010)；Beck–van Herick (2011) $4\times4$；De Loera–Liu–Yoshida (2009)；
  Ahmed–De Loera–Hemmecke (2003)。
- **构造**：Xin (2008) 3 阶幻方完全参数化 —— 本工作参数化的直接来源。
- **开放问题**：Pierrat–Thiriet–Zimmermann（平方数幻方）；Rome–Yamagishi (2024)；Flores (2024)。

## 3. Mission（2026-09-16 创建，已 Reviewed，2026-09-17）

- **Proposal id**：`c66f86f5-4921-40de-bce2-fb6564aebc67`
- **名称**：*Magic Squares I: MacMahon's Enumeration of Order-Three Magic Squares*
- **类型**：`ResearchPaper` · **字段**：Combinatorics `55eec41b-ff24-45ad-96b6-49d7a6869286`
- **Goal item**：`MagicSquares.magic_count_three_divisible`
- **Milestones**：6 个（见下表「milestone」列）

Proposal 已处于 `Reviewed`；待 moderator 审核后成为公开 mission。

## 4. 已发布内容

### 定义（Definitions）

| 平台名 | 本地文件 | 状态 |
|---|---|---|
| `MagicSquares` | `Definitions/Def_MagicSquares.lean` | PUBLISHED `be2f2b6a-a540-47ae-b487-ac22532a2745` |
| `MagicSquaresParam3` | `Definitions/Def_MagicSquaresParam3.lean` | PUBLISHED `68eaae9b-d759-4a2a-83f6-741ecdbca5f8` |
| `MagicSquaresTransforms` | `Definitions/Def_MagicSquaresTransforms.lean` | PUBLISHED（见 `missions/magic-squares/submit-definition-transforms.json`，job `161e8f0a`） |

`Def_MagicSquares`：`Square n α`、行/列/主对角/副对角/断对角和、
`IsSemiMagic` / `IsMagic` / `IsPanMagic` / `IsAssociative` / `IsCompact` /
`IsSymmetric` / `IsBimagic` / `IsNormal`、`magicConstant`、`complement`、
四个计数函数 `semiMagicCount` `magicCount` `panMagicCount` `symmetricMagicCount`。

`Def_MagicSquaresParam3`：`mkMagic3`（MacMahon 参数化）、`IsParam3`、`paramSet`、`paramCount`。

`Def_MagicSquaresTransforms`：`transpose` / `flipVertical` / `flipHorizontal` /
`affine`，以及仿射的行、列、主对角、副对角求和恒等式
（$S \mapsto aS + nb$）。对称性引理未放进定义模块，各 proof 内联。

### 定理（Theorems）

| theorem_name | 平台 id | 状态 | milestone |
|---|---|---|---|
| `MagicSquares.center_of_order_three` | `ebbc5687-663f-472d-afb6-f760546652db` | **Proved** | ✅ 1 |
| `MagicSquares.normal_order_two_none` | `f342d9be-b483-44d5-af8a-257a17bdda11` | **Proved** | |
| `MagicSquares.magic_constant_of_normal` | `2b184629-25ee-4be3-9075-89d9e624208d` | **Proved** | |
| `MagicSquares.magic_count_three_otherwise` | `fb4507f0-4ebd-432b-a1e7-e59697218d61` | **Proved** | |
| `MagicSquares.normal_order_three_constant` | `08463353-63d3-4260-89cf-9f61e97f7a04` | **Proved** | |
| `MagicSquares.normal_order_three_center_five` | `337eccfa-ed88-441d-b7ff-df1c3133fc30` | **Proved** | |
| `MagicSquares.normal_order_three_associative` | `3a365b32-43e3-476f-b22c-4151d8274eb8` | **Proved** | |
| `MagicSquares.panmagic_is_magic` | `1ece0a73-2e26-4db4-9f45-5d2d39f1d53d` | **Proved** | |
| `MagicSquares.total_sum_eq_n_line_sum` | `426e247c-26f9-4b16-9c70-e541e809f3b1` | **Proved** | |
| `MagicSquares.transpose_preserves_magic` | `3b7c0d09-0acb-4754-97c7-068a27b91c00` | **Proved** | |
| `MagicSquares.flipVertical_preserves_magic` | `9b89d44c-f278-4eb8-a8c2-b2513ecd1f12` | **Proved** | |
| `MagicSquares.flipHorizontal_preserves_magic` | `0bd2ee84-7eea-45d9-84fa-7c6f28595d84` | **Proved** | |
| `MagicSquares.affine_preserves_magic` | `2e82f714-7b8e-4902-81bf-35bb9bf56c81` | **Proved** | |
| `MagicSquares.order_three_opposite_sum_eq_twice_center` | `695c1fc5-a4a3-4ee4-9eda-9a132228ba46` | **Proved** | ✅ 2 |
| `MagicSquares.magic_three_param_sufficient` | `665c40f1-688c-4f40-aafb-1b8d82bbeb35` | **Proved** | ✅ 3 |
| `MagicSquares.magic_three_param_necessary` | `4e513d72-b4b7-419b-a0e6-dc115ee77a94` | **Proved** | ✅ 4 |
| `MagicSquares.magic_three_param_bij` | `f62c9364-c183-42f8-84b8-a6ac8e72ade7` | **Proved** | ✅ 5 |
| `MagicSquares.param_three_card` | `8063946a-dd43-4ff9-9107-f3e4d7cb040b` | **Proved**（submission `db22e0b4`，ACCEPTED） | ✅ 6 |
| `MagicSquares.magic_count_three_divisible` | `393a2adc-5e8e-4847-b9c6-f7b141a5114e` | **Proved** — GOAL 已达成（2026-09-17） | GOAL |
| `MagicSquares.semi_magic_count_three` | `55e2191d-be25-4e6d-af7a-4635a34e5c63` | **Open** | |

## 5. MacMahon 计数定理的分解树

$$M_3(3e) = 2e^2 + 2e + 1$$

```
magic_count_three_divisible (Open, GOAL)
├── magic_three_param_bij : magicCount 3 (3e) = paramCount e   (证明已提交)
│   ├── magic_three_param_sufficient  (Proved) ← 三参数构造满足幻方条件
│   └── magic_three_param_necessary   (Proved) ← 任意三阶幻方还原为构造
└── param_three_card      : paramCount e = 2 e^2 + 2 e + 1     (Open)
```

归约体（已 ACCEPTED）
```lean
theorem solution (e : ℕ) : magicCount 3 (3 * e) = 2 * e ^ 2 + 2 * e + 1 := by
  rw [magic_three_param_bij e, param_three_card e]
```

**`magic_three_param_bij` 的证明要点**（本轮完成，本地已编译通过）

`Finset.card_bij` 三件事：

1. **像在参数集内**：由 `magic_three_param_necessary`，$M=\mathrm{mkMagic3}(e,a,c)$；
   两条对角线给 $a+e+M_{22}=3e$、$c+e+M_{20}=3e$，故 $a,c\le 2e$；
   第 0 行给 $a+M_{01}+c=3e$，故 $a+c\le 3e$；
   其余三条不等式由中间行/列元素的显式形式配合线等式用 `omega` 得到。
2. **单射**：两个幻方若 $(M_{00},M_{02})$ 相同，则都等于同一个 `mkMagic3`，故相等。
3. **满射**：给定可行 $(a,c)$，`mkMagic3 e a c` 由 `magic_three_param_sufficient` 是幻方；
   其每个元素 $\le 3e$（角 $\le 2e$，其余由线等式界定），故可读作 `Fin (3e+1)` 数组。

**`param_three_card` 的已知推导（数学已完成，尚未形式化）**

按 $a$ 分组：固定 $a\in[0,2e]$ 时，$c$ 的可行区间为
$$\max(0,|a-e|)\le c\le \min(2e,\,3e-a,\,e+a).$$
- $a\le e$：区间 $[e-a,\ e+a]$，长度 $2a+1$；
- $a\ge e$：区间 $[a-e,\ 3e-a]$，长度 $4e-2a+1$。

于是
$$\#=\sum_{a=0}^{e}(2a+1)+\sum_{a=e}^{2e}(4e-2a+1)-(2e+1)=(e+1)^2+(e+1)^2-(2e+1)=2e^2+2e+1 .$$

（等价的 $\ell_1$ 球路径：代 $p=a-e,q=c-e$，条件化为 $|p|+|q|\le e$，
格点数 $1+4\sum_{k=1}^e k$。）

**难点**：`Finset` 上按第一坐标的纤维分解（`Finset.sigma` / `card_biUnion`）与
两段有限和化简。

## 6. 下一步建议

1. **轮询 `magic_three_param_bij`**（submission `2b7bc6bc`）确认 ACCEPTED。
2. **啃 `param_three_card`** —— 这是 goal 的最后一个未证子引理，证毕后
   `magic_count_three_divisible` 自动转 Proved。
3. 宇轩在网页端确认 mission proposal 并 Submit。
4. 之后 `semi_magic_count_three`（$H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$），
   需要 4 自由参数的 Birkhoff 多胞体格点计数。
5. 更远：$4\times4$ 计数（Beck–van Herick，周期 6 拟多项式）、泛魔方、
   最完美幻方（Ollerenshaw–Brée）、平方数幻方（开放问题，只能做部分结果）。

## 7. 环境坑（本机）

- **`∑ k in s, f k` 记号在这个 mathlib 版本里不解析**，必须写 `∑ k ∈ s, f k`。
- `Finset.eq_empty_iff_forall_not_mem` 不存在；用 `Finset.not_nonempty_iff_eq_empty`。
- `lakefile.lean` 全局设了 `autoImplicit false`；`examples/` 不在 lean_lib 里，
  所以本地 `lake env lean examples/...` 不会启用该选项 —— **提交前务必把证明放进
  `Solutions/` 再编译一次**。
- 提交轮询端点是 `GET /verify?submission_id=...`，不是 `/submission/{id}`。
- 平台偶发 `Import parser timed out after 5s`（导入解析超时）—— 属瞬时故障，
  原样重提即可（本轮 `flipHorizontal` 遇到过一次，重提后 ACCEPTED）。
- 平台编译对 tactic 冗余更敏感：本地能过的 `rw ...; ring` 在平台可能报
  `No goals to be solved`；改用 `simpa [...]` 更稳。
- **`Square 3 ℕ` 与 `Fin 3 → Fin 3 → ℕ` 在类型标注下不可互换**：
  给 `have hEq : ...` 写类型时，`(fun i j => ...) : Square 3 ℕ` 会被展开，
  而 `magic_three_param_necessary` 的返回类型不展开。解法是**不给 have 写类型**，
  让 Lean 推断，再用 `congr_fun` 取分量。
- 定义模块里同时 `variable [AddCommMonoid α]` 与 `variable [Semiring α]` 会触发
  `overlapping instances` 错误；用 `section` 把两段分开。
- Write 工具写 `/-! ... -/` 模块文档时，结束符偶尔会被写成 `-/}` 或 `-/]`，
  写完务必 Read 一眼第 17 行附近。
