# Mission: magic-squares-iv — 三阶幻方的特殊类（泛魔方 / 对称幻方）

负责人：anche（徐宇轩） · 环境：Lean 4.33.1 / Mathlib `0df444a3` · 平台：prove2.me v0.10.4

创建：2026-09-18 · 最后更新：2026-09-18 22:05（**goal 已 Proved，全部节点一次通过**）

## 0. 定位

幻方形式化项目的**第四个 mission**，也是三阶部分的收官：

| mission | 内容 | 结果 |
|---|---|---|
| I `magic-squares` | 幻方计数 | $M_3(3e)=2e^2+2e+1$（二次） |
| II `semi-magic` | 半幻方计数 | $H_3(t)=3\binom{t+3}{4}+\binom{t+2}{2}$ |
| III `normal3` | 正规幻方分类 | 洛书唯一性（8 个） |
| **IV（本 mission）** | **特殊类计数** | **泛魔 $P_3=1$（常数）、对称 $S_3(3e)=2e+1$（线性）** |

本 mission 的价值在于**对比**：同一个线和参数下，三阶幻方的三种强化方向给出
二次（普通幻方）、线性（对称）、常数（泛魔）三种完全不同的增长——而阶数四以上
这三种都没有闭式。

## 1. Proposal

- **id**：`7af96e14-bc8e-4e17-96b0-3aefec5f3a45`
- **名称**：*Magic Squares IV: The Special Classes of Order-Three Magic Squares*
- **类型**：`ResearchPaper` · **字段**：Combinatorics `55eec41b-ff24-45ad-96b6-49d7a6869286`
- 状态：`Draft`，**待宇轩在网页端确认后 Submit**
- 7 个 item（1 个定义 + 6 个定理），`main_item_id` = `special_three_count`（goal）；
  3 个 milestone 挂在支撑节点上（goal 不挂）

## 2. 已发布节点（全部 Proved / PUBLISHED）

### 定义

| 平台名 | 本地文件 | id |
|---|---|---|
| `MagicSquaresSpecial3` | `Definitions/Def_MagicSquaresSpecial3.lean` | `dc7c7ce9-2547-4cd2-9592-2974f777ff2a`（job `f03ed42d` PUBLISHED） |

`constSquare3 e : Square 3 (Fin (3*e+1))`、`symmMagic3 e a`、`symmParamSet e`（`range (2*e+1)`）、
`symmParamCount e`。

### 定理

| theorem_name | id | 状态 | submission |
|---|---|---|---|
| `MagicSquares.pan_three_card` | `418897d2-7993-4acd-8625-687a351efb11` | **Proved** | `a0a172a9` ACCEPTED |
| `MagicSquares.symmetric_magic_three_classify` | `8ce82e6f-d4df-4db4-9a22-19e17c230371` | **Proved** | `0c4a3f50` ACCEPTED |
| `MagicSquares.symm_three_bij` | `0b52ef65-8a48-445f-a9bd-9a2c271ad6bb` | **Proved** | `0e540dab` ACCEPTED |
| `MagicSquares.pan_three_otherwise` | `025bcf4a-7b1e-4813-acfa-27f69cf2dcd5` | **Proved** | `53ccbacb` ACCEPTED |
| `MagicSquares.symm_three_otherwise` | `632cc340-833d-4a83-9537-d53be8c54378` | **Proved** | `91d14644` ACCEPTED |
| `MagicSquares.special_three_count` | `0e66e443-931d-419d-8ec0-b925b0678288` | **Proved**（GOAL） | `3b22d8c0` SKETCH_ACCEPTED → 孩子全 Proved 后**自动升为 Proved** |

### DAG

```
special_three_count (GOAL) : P_3(t) = (if 3∣t then 1 else 0) ∧
                             S_3(t) = (if 3∣t then 2*(t/3)+1 else 0)
├── pan_three_card              : panMagicCount 3 (3*e) = 1
├── symm_three_bij              : symmetricMagicCount 3 (3*e) = symmParamCount e
│   └── symmetric_magic_three_classify : IsMagic M (3e) → IsSymmetric M → M = symmMagic3 e (M 0 0)
├── pan_three_otherwise         : ¬ 3 ∣ t → panMagicCount 3 t = 0
└── symm_three_otherwise        : ¬ 3 ∣ t → symmetricMagicCount 3 t = 0
```

## 3. 数学方案

### 3.1 泛魔方：塌缩成常数阵

$3\times3$ 非负整数阵线和为 $3e$，写成 $\begin{smallmatrix}a&b&c\\d&m&f\\g&h&i\end{smallmatrix}$。
十二个线和等式（3 行 + 3 列 + 6 条断对角）**全是加法**，一起喂给 `omega` 即得
$a=b=\cdots=i=e$。于是 $P_3(3e)=1$，唯一的元素是 `constSquare3 e`。

对比：普通幻方有 $2e^2+2e+1$ 个，加 6 条断对角后**只剩 1 个**。

> ⚠️ **定义对齐（2026-09-18 补记，重要）**：本 mission 用的是 `Def_MagicSquares.IsPanMagic`
> ——**两个方向**的断对角都要等于线和。文献 BCCG(2003) 的 pandiagonal 只要求**一个方向**
> （与主对角平行、含主对角、绕回），其 $P_3(t)=\binom{t+2}{2}=\frac12t^2+\frac32t+1$
> 是 $t$ 的 2 次多项式（实测 $t=0..9$ 为 $1,3,6,10,15,21,28,36,45,55$，与公式吻合）。
> **两者不可互相对照**，本 mission 的「$P_3=1$ 当且仅当 $3\mid t$」**不是** BCCG 的 $P_3$。
> 另注：BCCG 的单向泛魔不要求副对角，故与该文的「magic」**互不包含**。
> 详见 `missions/project-review-2026-09-18.md` §3.1 与 `referpaper/README.md` §五。

### 3.2 对称幻方：一参数族

对称给出 $M_{01}=M_{10}$、$M_{02}=M_{20}$、$M_{12}=M_{21}$，八个线和条件塌成五个：
三行 + 主对角 $a+m+i=3e$ + 副对角 $2c+m=3e$。副对角立刻给 $c=m=e$（用
$c+m+g=2c+m=3e$ 与主对角相消得 $a+i=2c$，(E1)+(E3) 与 (E2),(E4) 联立得 $6c=6e$），
再由三行得

$$\mathrm{symmMagic3}(e,a)=\begin{pmatrix}a&2e-a&e\\2e-a&e&a\\e&a&2e-a\end{pmatrix},\qquad a=M_{00}.$$

**可容许条件**（$a\le 2e$）是**截断减法**的事：$(0,1)$ 项是 $2e-a$，行和
$a+(2e-a)+e=3e$ 在 $\mathbb N$ 里当且仅当 $a\le 2e$ 成立。由此 `card_bij` 给出
$S_3(3e)=2e+1$（线性）。

### 3.3 $3\nmid t$ 两支

两个特殊类都含于幻方类，而三阶幻方中心被 `center_of_order_three` 锁死为 $t/3$，
故 $3\nmid t$ 时两个有限集都空——和 Mission I 的 `magic_count_three_otherwise` 同型。

## 4. 形式化要点（本轮新踩的坑）

- **平台 summand 的形态**：本 mission 没这个问题，但值得记——Mission IV 全部节点
  都是「直接证」，不走约简 import 链，除了 goal：goal 的文件 import 四个孩子的
  `Theorems.Thm_*` 镜像。
- 🔴 **goal 节点的裁决会随孩子变化**：`special_three_count` 提交时两个 `otherwise`
  孩子还在 PENDING，平台判为 `SKETCH_ACCEPTED`；等孩子全 ACCEPTED 后节点**自动**
  变成 `Proved`。⇒ **不要因为看到 SKETCH_ACCEPTED 就以为失败**，过一会儿重新查
  `/theorems/<id>`，或直接看 `/decompositions` 里孩子的 status。
- 🔴 **`Fin` 上的加法/取反要 `fin_cases` 才化简**：`brokenDiagSum M k = ∑ i, M i (i+k)`
  在具体 `k : Fin 3` 与具体 `i` 下才归约到地面项；写法是
  `fin_cases k <;> simp [brokenDiagSum, Fin.sum_univ_three]`。
- 🔴 **`ext i j` 作用在 `Square 3 (Fin n)` 上直接给 ℕ 相等**（不是 `Fin` 相等）：
  `ext i j` 之后**不要再 `apply Fin.ext`**，否则报 "could not unify the conclusion of
  `@Fin.ext`"。`symmetric_magic_three_classify` 与 `pan_three_card` 都靠这一条。
- **`DecidablePred` 陷阱**：`example : (Finset.univ.filter (fun M : Square 3 (Fin (3*e+1)) => IsPanMagic …)).card = 1`
  在**陈述**层就会报 `failed to synthesize DecidablePred`（证明体里写 `classical` 没用，
  陈述先被 elaborate）。⇒ 陈述要经由 `panMagicCount`/`panMagicSquares` 这类
  内部已 `by classical` 包装的 def 表达。
- **`Nat.mul_div_left` 的隐参数**：签名是 `Nat.mul_div_left m {n} (H : 0 < n) : m * n / n = m`
  （**乘数在前、除数隐式**）。所以 `3 * e / 3 = e` 要写成
  `by rw [mul_comm 3 e]; exact Nat.mul_div_left e (n := 3) (by norm_num)`；
  直接写 `Nat.mul_div_left e (by norm_num)` 会因为 `by norm_num` 在 `?n` 未赋值前就
  elaborate 而报 `⊢ 0 < ?m.86`。
- **`/-! -/` 与 `/-- -/` 不能悬空挂在 `namespace` 前**：`/-- doc -/ namespace X` 报
  `unexpected token 'namespace'; expected 'lemma'`（doc comment 只能挂声明）。改用
  `/- ... -/`。
- **`Finset.eq_singleton_iff_unique_mem`** 是证「有限集是单点集」的省力写法：
  `rw [Finset.card_eq_one]; refine ⟨x, ?_⟩; rw [Finset.eq_singleton_iff_unique_mem]`
  然后给「$x$ 在集合里」+「任何元素等于 $x$」。
- **`omega` 能吃 12 条加法等式**：`pan_three_card` 的唯一性就是 9 个 `fin_cases` 目标各
  一次 `omega`，每次带 12 条假设，秒级通过。

## 5. 复现

```bash
# 定义
lake build Definitions.Def_MagicSquaresSpecial3
# 六份提交文件
lake build Solutions.Sol_MagicSquares_pan_three_card \
            Solutions.Sol_MagicSquares_symmetric_magic_three_classify \
            Solutions.Sol_MagicSquares_symm_three_bij \
            Solutions.Sol_MagicSquares_pan_three_otherwise \
            Solutions.Sol_MagicSquares_symm_three_otherwise \
            Solutions.Sol_MagicSquares_special_three_count
# payload 生成器
python tmp/build_special3_definition_payload.py
python tmp/build_special3_problems_payload.py
python tmp/build_special3_problems_payload2.py
```

裁决留档：`missions/magic-squares-iv/verification-*.json`；
proposal 元数据：`proposal_items.json` / `proposal-meta.json` / `milestone-tmp.json`。

## 6. 下一步

1. **宇轩在网页端确认 proposal `7af96e14` 并 Submit**（只有本人能点）。
2. Mission IV 已全部完成，无遗留节点。可选延伸：
   - 把两个「$3\mid t$ 闭式」也写成 $\mathrm{rank}$ 形式（$P_3(t)=1_{3\mid t}$）便于引用；
   - **四阶 $H_4$ / $M_4$ 计数（Beck–van Herick，周期 6 拟多项式）** 作为
     Magic Squares V——需要先补 Ehrhart / Birkhoff 多胞体格点计数机制；
   - 关联度较高的便宜项：`semi_magic_count_three` 仍 Open（Mission II 的遗留）。
