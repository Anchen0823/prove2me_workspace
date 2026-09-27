# ε₀ 以上 FGH 与序数表示 —— 可行性侦察报告

**日期**：2026-09-26
**环境**：Lean `v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
**性质**：纯 reconnaissance。未创建 mission、未上传 theorem、未修改仓库。

**证据标记约定**：本报告中每条结论都标注来源。

- 【已确认】= 我实际读入源码 / 实际编译通过 / 实际调用 API 得到的
- 【已推测】= 基于上述证据的判断，未经机器验证

---

## 1. Executive Summary

值得做，而且是**便宜地**值得做。

1. Mathlib 的序列数基础设施呈现出一种**明显的断裂**：`Ordinal` 层面已经有 ε_α、Γ_α、完整的二元 Veblen 函数，甚至有反函数 `invVeblen₁/invVeblen₂`；但 FGH 所在的 `Mathlib.SetTheory.Ordinal.Notation` 只覆盖 ε₀ **以下**，且 **ε₀ 本身也没能进入层级**——它是个外部 hack（`ONote.fastGrowingε₀`，只有 3 条值定理 1/2/2048）。【已确认】
2. 这个模块 DOA：整个 Mathlib 里，**只有 `Mathlib.lean` 自己 import 它**，没有任何其它模块使用 `ONote` 或 `fastGrowing`。这是一座孤岛。【已确认】
3. 真正缺的**不是序数**，而是**可计算 notation + canonical fundamental sequence**。`Ordinal` 层面的 FS 存在性 Mathlib 已经有了（`exists_isFundamentalSeq`）；ε₀ 的 ε₀-tower 共尾性也已经有了（`Ordinal.lt_epsilon_zero`）。缺的是把它们做成 `fastGrowing` 能递归的 datatype。【已确认】
4. **推荐切入点 = 路线 A，且只加一个构造子**：给 `ONote` 形状的类型加一个 ε₀ 原子，得到恰好覆盖 `[0, ε₁)` 的表示，接上 FS 与 FGH。我实际编译了这个方案的最小骨架，**干净通过**（唯一诊断是我故意留的一个 `sorry`）。【已确认】
5. 路线 C（Γ₀ 以下 Veblen 表示）**不是**第二阶段合理选项，而是**一整个独立的 proof-theory library**。最硬的证据：Coq 的 `hydra-battles` 里对应的 `Gamma0/T2` 数据类型至今仍标注为 "draft"，文档第八章标题就写着 "first draft"。【已确认】
6. 交付去处：这份成果 95% 是 reusable infrastructure，且正落在 Mathlib 自己写着 TODO 的那个文件上 → **首选 Mathlib PR**，不是 Prove2Me theorem submission。【已推测，理由见 §9】
7. **最大风险**：不是数学，是两处工程性膨胀 —— (a) 把 ONote 的 `fundamentalSequence_has_prop` 证明按新类型逐句改写（约 60–70 行密集归纳）；(b) 一旦忍不住要证"表示唯一性/完备性"，DAG 立刻翻倍。前者不可避免，后者**必须推迟**。【已推测，基于实际改写尝试】

---

## 2. Mathlib 现有基础设施（全部【已确认】）

我用 `#check` 逐一核对了下列名称与类型，编译通过；不是从文档摘要抄的。

### 2.1 模块清单

| 模块 | 行数 | 作者 | 内容 |
|---|---|---|---|
| `Mathlib.SetTheory.Ordinal.Notation` | 1297 | Mario Carneiro | `ONote`、`NONote`、`fundamentalSequence`、`fastGrowing` |
| `Mathlib.SetTheory.Ordinal.Veblen` | 720 | Violeta Hernández Palacios | `veblenWith`、`veblen`、`epsilon`、`gamma`、`invVeblen₁/₂` |
| `Mathlib.SetTheory.Ordinal.FundamentalSequence` | 241 | V. H. Palacios, M. Carneiro | `IsFundamentalSeq` 及其组合定理 |
| `Mathlib.SetTheory.Ordinal.CantorNormalForm` | 379 | Carneiro, H. Palacios | `Ordinal.CNF`（作用在 `Ordinal` 上，非 datatype） |
| `Mathlib.SetTheory.Ordinal.FixedPoint` | 514 | 同上 | `nfp`、`deriv`、`derivFamily` |
| `Mathlib.SetTheory.Ordinal.Principal` | 527 | H. Palacios | `IsPrincipal`；TODO 里承认**尚未**刻画指数主序数 |
| `Mathlib.Logic.Hydra` | — | Junyan Xu | 通用 hydra 良基性；TODO 明说 Kirby–Paris / Buchholz hydra 待做 |
| `Mathlib.Computability.Ackermann` | — | — | `ack : ℕ → ℕ → ℕ`，**无序数索引** |
| `Mathlib.Computability.Primrec/Basic` | — | — | 原始递归函数（存在，但未细查 API） |

### 2.2 关键声明（`#check` 实测输出）

**FGH 层（`Notation.lean`）**

```
ONote : Type
ONote.zero / ONote.oadd : ONote → ℕ+ → ONote → ONote
ONote.repr            : ONote → Ordinal.{0}
ONote.NF / ONote.NFBelow : 范式谓词
ONote.cmp             : ONote → ONote → Ordering
ONote.cmp_compares    : (a b) [a.NF] [b.NF] → (a.cmp b).Compares a b
ONote.fundamentalSequence : ONote → Option ONote ⊕ (ℕ → ONote)
ONote.FundamentalSequenceProp : ONote → (Option ONote ⊕ (ℕ → ONote)) → Prop
ONote.fundamentalSequence_has_prop (o) : o.FundamentalSequenceProp o.fundamentalSequence
ONote.fastGrowing     : ONote → ℕ → ℕ
ONote.fastGrowing_zero / _succ / _limit
ONote.fastGrowingε₀   : ℕ → ℕ          -- 注意：不是 fastGrowing 的一个 case
ONote.fastGrowingε₀_two : ONote.fastGrowingε₀ 2 = 2048
NONote : Type
```

**Veblen / ε / Γ 层（`Veblen.lean`）**

```
Ordinal.veblen         : Ordinal → Ordinal → Ordinal
Ordinal.veblenWith     : (Ordinal→Ordinal) → Ordinal → Ordinal → Ordinal
Ordinal.isNormal_veblen (o) : IsNormal (veblen o)
Ordinal.epsilon        : Ordinal → Ordinal       （记法 ε_ o，ε₀ = ε_ 0）
Ordinal.gamma          : Ordinal → Ordinal       （记法 Γ_ o，Γ₀ = Γ_ 0）
Ordinal.omega0_opow_epsilon (o) : ω ^ ε_ o = ε_ o
Ordinal.lt_epsilon_zero : o < ε_ 0 ↔ ∃ n, o < (fun a => ω ^ a)^[n] 0
Ordinal.lt_gamma_zero   : o < Γ_ 0 ↔ ∃ n, o < (fun a => veblen a 0)^[n] 0
Ordinal.invVeblen₁ / invVeblen₂ : Ordinal → Ordinal
Ordinal.veblen_invVeblen₁_invVeblen₂ (x) : veblen x.invVeblen₁ x.invVeblen₂ = ω ^ x
```

注意最后一条的定义处文档注释原文：

> Composing this function with `Ordinal.CNF` yields a predicative ordinal notation up to `Γ₀`.

即：**Mathlib 已经知道自己手握 Γ₀ 以下 Veblen 范式的语义原料，只是没有落成 datatype。**

**基本序列层（`FundamentalSequence.lean`）**

```
Ordinal.IsFundamentalSeq (f : Iio a → Iio o) : Prop
  -- 字段：le_ord_cof / strictMono / isCofinal_range
Ordinal.IsFundamentalSeq.iSup_eq (hf) (ha : 1 < a) : ⨆ i, (f i).1 = o
Ordinal.IsFundamentalSeq.comp_isNormal (hg : IsNormal g) (hf) (ho : IsSuccLimit o)
  : IsFundamentalSeq fun i => ⟨g (f i), _⟩
Ordinal.exists_isFundamentalSeq (ha) : ∃ f, IsFundamentalSeq f
```

`comp_isNormal` 是** Transport 基本序列穿过正规函数**的那条关键定理——也就是往 Veblen 层级上推 FS 所需的那一块。它**已经存在**。

### 2.3 三个决定性事实

**事实 1：`fastGrowing` 在结构上到不了 ε₀。**
它不是"写得不够"，而是类型层面被卡住：

```lean
instance : WellFoundedRelation ONote := ⟨(· < ·), InvImage.wf repr Ordinal.lt_wf⟩
```

`<` 由 `repr` 拉回，良基性来自 `Ordinal.lt_wf`。所以 `fastGrowing` 的定义域恰好是 `{repr o | o : ONote}`，而这个集合的上确界是 ε₀ 且不含 ε₀。任何形如 `fastGrowing x` 的调用都不可能索引 ε₀。【已确认，读源码 + 下面的推断相容】

**事实 2：ε₀ 目前是个一次性补丁。`fastGrowingε₀` 的实际定义是**

```lean
def fastGrowingε₀ (i : ℕ) : ℕ :=
  fastGrowing ((fun a => a.oadd 1 0)^[i] 0) i
```

手工注入 ω-塔，**不属于 `fastGrowing` 的类型**。关于它只有三条定理：`_zero = 1`、`_one = 2`、`_two = 2048`。也就是说：**ε₀ 这一步在 Mathlib 里是不在层级里面的。** 【已确认】

**事实 3（此前没被注意到）：Mathlib 完全没有把 `ONote` 的值域和自己的 ε₀ 连起来。**
我在 `SetTheory/Ordinal/` 全目录 grep `epsilon`，结果只命中 `Notation.lean` 的**文档注释**（"Constructive ordinal arithmetic for ordinals below ε₀"）和三处 `fastGrowingε₀` 名字。也就是说：**连 `∀ o, NF o → repr o < ε₀` 这样一条把值域钉死的定理都不存在。** ε₀ 真正出现的地方是 `Veblen.lean`，而 `Veblen.lean` 没人 import。【已确认】

### 2.4 能力边界回答（逐条回答报告要求的问题）

- **当时 notation 的表达力截止到哪**：`< ε₀`（严格小于，不含）【已确认，来自模块文档与我下面的实操】
- **能否表示 ε₀ 本身**：`Ordinal` 里可以（`ε₀`），`ONote` 里**不能**【已确认】
- **ε₀+1、ε₁、φ₂(0)、Γ₀**：`Ordinal` 里全部可以（分别为 `ε₀ + 1`、`ε_ 1`、`veblen 2 0`、`Γ_ 0`）；**notation 层面全部不能**【已确认】
- **FGH 为什么不能自然扩展**：因为 `fastGrowing` 以 language-level well-founded recursion over `repr` 定义（`repr : ONote → Ordinal` 是 `noncomputable`），既不可计算于 `Ordinal`，也拿不到 ε₀ 以上的任何 `ONote` 项。【已确认】

> **明确排除一个常见错误**：不能因为"Mathlib 定义了 `Ordinal ε_ 1`"就说"FGH 可以跑到 ε₁"。`fastGrowing` 的参数类型是 `ONote`（notation datatype），不是 `Ordinal`；两者之间只有单向的 `repr`，而 `repr` 不是满射到 ε₁。
>我已经在下表把"Ordinal 里可定义"和"FGH 可计算"严格分开。

---

## 3. Prove2Me 现有工作

方法：直接调 `GET /api/v1/theorems?q=...`，21 组关键词，去重后共 **211 个不同 theorem 节点**；再列 `/missions?limit=300`（返回 100）。【已确认】

> 用一个无意义查询串做对照，返回 0 条 → 说明搜索确实在过滤，不是返回全集。

### 3.1 结论：没有任何直接相关的东西

| 关键词 | 真实命中 | 备注 |
|---|---|---|
| ε₀ / epsilon_0 | **0** | |
| Γ₀ / Gamma_0 | **0** | |
| fast growing / FGH / Wainer | **0** | |
| fundamental sequence | **0** | |
| ordinal notation | **0**（仅 1 条结构类neighbors） | |
| Goodstein | **0** | |
| Ackermann | **0** | |
| Cantor normal form | **0**（仅 2 条题材相近） | |
| Kruskal / TREE | 0 真实（大量 "tree" 误命中） | |
| Busy Beaver | 1 条 **Open** | `FCP.BusyBeaver.busy_beaver_exceeds_computable` + 定义包 `FCP_BusyBeaver` |
| proof theory | 0 | |

**一个需要点名的纠错（正是"别因为名字相似就假设"的那条）**：
搜索 `Hardy` 返回 124 条，看起来像有人在做 Hardy 层级。我逐个核验了 `hardyLevel_one_ne_zero`、`emlDepth_le_hardyLevel`、`EmlClass.mono`、`EML_HardyEmlBase` 的 `formal_statement` 与来源，结果是**名字严重误导**：

```
theorem hardyLevel_one_ne_zero : ¬ HardyLevel 0 Real.exp
theorem EmlClass.mono : ∀ {m n : ℕ} {f : ℝ → ℝ}, m ≤ n → EmlClass m f → EmlClass n f
来源 paulklemstine/Lean · Catalog/EML/HardyEmlBase.lean
```

这是"指数–对数神经网络表达力"（EML，ℝ→ℝ、按 ℕ 分级）的 catalog，**与序数 Hardy 层级没有任何关系**。【已确认】

### 3.2 真正题材相邻的内容（可作为参照/依赖，非重复）

| 名称 | 状态 | 说明 |
|---|---|---|
| `FamousTheorems.veblen_fixed_point_lemma_7a` | Proved | 正规序数函数的 Veblen 不动点引理 |
| `FamousTheorems.additive_principal_ordinals_omega_powers_7a` | Proved | 加法主序数 = ω 的幂 |
| `Erdos592_Defs` | Definition | 序数 Ramsey 性质，`IsSumOfIndecomposables k γ` |
| `Erdos592.schipperus_*` / `galvin_larson_*` / `erdos_592_three_indecomposables` | 4 条 **Open** | ω^{ω^γ} 是否为 partition ordinal；隶属 mission "Erdős Problem 592: which ω^β are partition ordinals?" |
| `FCP.BusyBeaver.busy_beaver_exceeds_computable` | **Open** | busy beaver 支配一切可计算函数 |

**Mission 侧**：返回的 100 条 mission 里，**没有任何**序数 / FGH / 证明论 mission。平台上不存在"有人在建设类似库"的情况。

### 3.3 这条结论的意义

- 好消息：**不与任何人重复**，也不必担心拂了别人的面子。
- 坏消息：**没有任何可 import 的平台基础设施可用**（不像五素数那条链子上有可复用的东西）。一切依赖都要回到 Mathlib。

---

## 4. 现有能力地图

四件事必须分开：**(a) `Ordinal` 里可定义 / (b) 有 notation datatype / (c) 有 canonical 可计算 FS / (d) FGH 可递归计算**。

| 层级 | (a) Ordinal 有定义 | (b) notation datatype | (c) canonical FS | (d) FGH 可算 | 缺口 |
|---|---|---|---|---|---|
| 有限序数 | ✓ | ✓ `ONote.ofNat` | ✓ | ✓ `fastGrowing` | — |
| ω | ✓ `ω` | ✓ `ONote.omega` | ✓ | ✓ | — |
| ω^ω | ✓ | ✓ | ✓ | ✓ | — |
| ε₀ 以下任意 | ✓ | ✓ `ONote`/`NONote` | ✓ | ✓ | — |
| **ε₀** | ✓ `ε₀` | **✗** 无 `ONote` 项 | △ 仅 `lt_epsilon_zero`（共尾性），未包成 `IsFundamentalSeq` | **✗** 只有外部 hack `fastGrowingε₀`，不在层级内 | **缺 notation + 统一 FS** |
| ε₀+1 | ✓ | ✗ | ✗ | ✗ | 同上 |
| ε₀·2、ω^(ε₀+1) | ✓ | ✗ | ✗ | ✗ | 同上 |
| ε₁ | ✓ `ε_ 1` | ✗ | ✗ | ✗ | 同上 |
| ε_ω | ✓ `ε_ ω` | ✗ | ✗ | ✗ | 同上 |
| φ₂(0) | ✓ `veblen 2 0` | ✗ | ✗ | ✗ | 同上 |
| Γ₀ | ✓ `Γ_ 0` | ✗ | △ `lt_gamma_zero`（构造存在但未结构化） | ✗ | 同上 |

图例：✓ 可用 / △ 原料存在但未包装 / ✗ 没有

**注意 (c) 的一个易错点**：`Ordinal.exists_isFundamentalSeq` 让**所有**序数都有（非构造的）基本序列。所以严格说 (c) 列每个格子都"存在**某个** FS"。但那不是 canonical、不可计算、拿不到 `ℕ → Term` 的赋值，因此对 FGH 毫无用处。上表的 (c) 一律指 **canonical 且可计算**。

**核心判断**：缺的是 **(b) 和 (c)**，不是 (a)。Mathlib 在 (a) 上已经强得超过需要了。

---

## 5. 三条候选路线评估

### 路线 A —— ε₀ 以上最小扩展（加一个 ε₀ 原子 → 覆盖 `[0, ε₁)`）

设计：`inductive T | zero | eps | oadd : T → ℕ+ → T → T`，语义 `repr eps = ε₀`。

- **数学上自然？** 是。这是标准的"以 ε-数为原子的扩展 CNF"。关键事实：**ε₁ 以下唯一的 ε-数就是 ε₀**，所以只需一个原子，且必须排除 `ω^ε₀·1 + 0`（它又等于 ε₀，会破坏唯一性）。【已确认，这是 `ω ^ ε_ o = ε_ o` 的直接推论】
- **有标准文献？** 有。Schütte、Pohlers、Simpson（SOSOA）；Mathlib 自己的 `Veblen.lean` 就引 Cheong……更正：引 **[Miller 1976] Larry W. Miller, *Normal functions and constructive ordinal notations*, JSL 41(2):439–459**（MSC 03F15，主题正是 ordinal notations）。这条是最贴切的引用，因为它被 Mathlib 自己当作 Veblen 层的文献依据。【已确认该引用存在；我未通读原文，故其对 <ε₁ 扩展 CNF 的适用性为【已推测】】
- **能和现有 `ONote` 对接？** **极高**。`T` 就是 `ONote` 多一个构造子；`FundamentalSequenceProp`、`fastGrowing` 的定义可以**逐字复制**；`fundamentalSequence` 的 `oadd` 分支完全不动，只加 `eps` 一支。
- **会不会大量 duplicated infrastructure？** **可以控制在很低**。关键发现：**FGH 不需要记法上的加/减/乘/幂**。`Notation.lean` 1297 行里最重、最难的 `add/sub/mul/opow` 及其 ~600 行范式保持证明，**与 FGH 无关**——`fastGrowing` 只用到 `repr`、`NF`、`fundamentalSequence` 和 `<` 的良基性。我据此构造的骨架总共不到 200 行就跑通了 FGH 全流程。【已确认，实测】
- **适合 Prove2Me？** 见 §8。

**实测证据**（`tmp/eps_probe.lean`，编译通过）：

```
唯一诊断：tmp/eps_probe.lean:128:8: warning: declaration uses `sorry`
```

那个 `sorry` 是我**故意**留的 `fundamentalSequence_has_prop` 的 `oadd` 部分（那是对现有 ONote 证明的逐行改写）。**其余全部编译通过**，包括：

- `T`、`repr`、`NFB`/`NF`（含 ε₀ 原子，含 `¬(e = eps ∧ a = zero ∧ n = 1)` 唯一性侧条件）
- `tower : ℕ → T`（ω-塔，结构式定义）
- `fundamentalSequence`（仅 `eps` 支是新的）
- **`fastGrowing : T → ℕ → ℕ` 且 `termination_by o => o` 被接受** —— 这是最关键的一条：良基递归在新类型上照样通过
- 全新且很短的 ε₀ 引理，全部只用现有 Mathlib：

| 新定理 | 行数 | 依赖的现有 Mathlib 引理 |
|---|---|---|
| `isSuccLimit_eps : IsSuccLimit ε₀` | ~6 | `isSuccLimit_iff`、`isSuccPrelimit_iff_succ_lt`、`Ordinal.lt_epsilon_zero`、`iterate_omega0_opow_lt_epsilon_zero` |
| `tower_lt_eps` | ~4 | `iterate_omega0_opow_lt_epsilon_zero` |
| `tower_strictMono_step` | ~5 | `opow_lt_opow_iff_right one_lt_omega0` |
| `tower_cofinal` | ~5 | `Ordinal.lt_epsilon_zero` |
| `eps_has_prop` | ~6 | 上面四条组装 |
| `nf_tower` | ~3 | `NF.oadd_zero` |

也就是说：**"ε₀ 的新数学"其实已经全部躺在 Mathlib 里了**（特别是 `lt_epsilon_zero` 这条，它本身就是"ω-塔在 ε₀ 中共尾"的定理），新 IEEE 的工作只是把它们组装成 datatype 上的 FS。

### 路线 B —— epsilon hierarchy notation（表达 ε_α）

- **最小可行 datatype？** `Inductive | zero | oadd | eps : α → Type`，即把 ε-指数本身也做成项。这个闭包自然到达 **ζ₀ = φ₂(0)**（α ↦ ε_α 的第一个不动点），不是只到某个受限 α-domain。
- **能否复用 `Ordinal` 和 `ONote`？** 语义侧能（目标值仍是 `ω^e * n + a` 和 `ε_ α`），语法侧必须新写：比较两个项要判断 `ε_α` vs `ε_β`、以及 ω-幂 vs ε-数谁大 → **互递归比较**，且 NF 唯一性需要"α < ε_α"的刻画。
- **要不要重建 CNF？** 不需要重建，但要在 CNF **之上**再叠一层：每个 CNF 指数的"最高 Veblen 层"要单独抽出。这是实质性的架构选择。
- **代码规模合理？** 比 A 大一个量级，比 C 小一个量级。
- **判断**：B 实质上是 **C 的一个受限制子实例**（只支持 φ₀、φ₁ 而非全 φ）。既然如此，**不如直接把它做成"参数化的 Veblen 范式 datatype，当前只开 φ₀/φ₁ 两个 idx"** —— 那样第二阶段可以无痛扩展到全 Veblen。但无论如何它不是第一步。

### 路线 C —— Γ₀ 以下 Veblen 表示

**明确判断：这是一个独立的 proof-theory library，不是第二阶段，而是第三到第四阶段。**

证据（这是我最想确认的一条）：

- **Coq `hydra-battles`**（`rocq-community/hydra-battles`，Castéran / Contejean / Hatat / Manoury）里有 `theories/ordinals/Gamma0/*.v`，README 原文描述为 "A data type for ordinals below Γ₀ in Veblen normal form **(draft)**"；其文档 `hydras.pdf` **第八章标题就是 "The Ordinal Γ₀ (first draft)"**，下含 8.2 The Type T2 of Ordinal Terms / 8.4 Veblen Normal Forms / 8.6 An Ordinal Notation for Γ₀。同一批 author 在 ε₀ 层完全成熟（T1、Ketonen–Solovay、Wainer–Hardy §6.3–6.4），而 Γ₀ 层**多年仍是 draft**。这是代价的最强实测标定。【已确认，来源：README + 目录页】
- **Isabelle 发行版 `HOL-Induct/Ordinals`**（Berghofer–Wenzel）确实定义了 `veblen`、`ε⇩0`、`Γ⇩0`，但其底层是 `datatype ordinal = Zero | Succ | Limit (nat ⇒ ordinal)` —— **没有范式、没有唯一性**，因此既不能支撑 FGH，也不能当作目标形态的范本，只能证明"定义 veblen 很容易，定义 *canonical notation* 很难"。【已确认】
- 需要的额外负担：多参数 VNF、互递归比较、φ 的 FS 至少 6–7 个分情形（含 `φ_{β+1}(0)[n+1]`、`φ_β(γ+1)[n]`、`φ_λ(γ)[n]` 等）、Hessenberg/自然和的处理、以及最痛的"每个极限项的存在性 witness"。**几十个 lemma 起步。**
- **结论**：按报告第七节的筛选口径，它命中"自建整个 Veblen hierarchy / >20 个关键前置 theorem / 数十个 normalization lemma"三条 → **当前阶段不适合作为 Prove2Me mission，也不适合作为第一阶段 Mathlib PR**。

---

## 6. 推荐的 MVP（只推一个）

### 推荐：**路线 A —— 一个构造子，从 `<ε₀` 推到 `<ε₁`**

**一句话数学目标**：把 ε₀ 作为一个新原子加入 Cantor 范式，使其表达的序数恰好是 `[0, ε₁)`，为其配备 canonical fundamental sequence，从而把 `fastGrowing` 的定义域从 `<ε₀` 扩展到 `<ε₁`，并让 ε₀ 从"外部 hack"变成层级内的正式成员。

**需要的新定义（5 个）**

| # | 定义 | 说明 |
|---|---|---|
| 1 | `EpsNote.T` | `zero \| eps \| oadd (e : T) (n : ℕ+) (a : T)` |
| 2 | `T.repr : T → Ordinal.{0}` | `eps ↦ ε₀`；`oadd e n a ↦ ω^repr e * n + repr a` |
| 3 | `T.NFB` / `T.NF` | 带 ε₀ 原子的范式谓词；**排除** `ω^ε₀·1+0`（重述 ε₀，破坏唯一性） |
| 4 | `T.fundamentalSequence` | 仅 `eps ↦ tower` 一支是新的，`oadd` 分支照搬 `ONote` |
| 5 | `T.fastGrowing : T → ℕ → ℕ` | 与 `ONote.fastGrowing` 定义同形，`termination_by o => o` |

辅助（非核心）：`T.tower : ℕ → T`（ω-塔，刻意用结构式定义而非 `iterate`，让 `tower_repr` 的归纳变得平凡）。

**需要的新定理（8–10 条）**

优先级 P0（缺一不可）：

1. `NFB.repr_lt` —— 范式项的值 < ω^b（ε₀ 分支几乎平凡）
2. `fundamentalSequence_has_prop` —— **最大的一块**，是 `ONote` 那条 60 行归纳的逐行改写 + `eps` 一支
3. `isSuccLimit_eps` —— ε₀ 是极限序数
4. `tower_lt_eps` / `tower_strictMono_step` / `tower_cofinal` —— ω-塔的三条 FS 性质
5. `eps_has_prop` —— 把 3–4 组装成 `FundamentalSequenceProp eps`
6. `fastGrowing_succ` / `fastGrowing_limit` —— 展开方程

优先级 P1（强烈建议，构成"这不是空转"的证明）：

7. **桥接定理**：`T.fastGrowing eps = ONote.fastGrowingε₀`
   —— 这一步把现有的 hack 收编为特例，也是 PR 里最有说服力的动机。
8. **值定理**：`T.fastGrowing (oadd eps 1 0) 0/1/2` 之类，给出 ε₀+1、ε₀·2 等的真实新数值。
   （对照：`ONote.fastGrowingε₀ 2 = 2048` 已有）

建议**推迟**到第二阶段（当前明确削减）：

- 表示**唯一性**与**完备性**（`<ε₁` 每个序数恰有一项）
- 可判定**比较** `cmp` / `LinearOrder T` / `DecidableRel`
- 记法上的 `+ - * ^` 及其范式保持

> 砍掉这三项之后的规模能否自洽？能：**FGH 不需要它们**。`fastGrowing` 用的良基性是 `repr` 拉回的 `<`（含 `NF` 守卫即可），不需要比较算法，不需要算数。这是本次侦察最重要的一个发现——它把 DAG 从"重建 ONote"降到了"复用 ONote"。

**依赖**

- Mathlib `SetTheory.Ordinal.Notation`、`Veblen`、`FundamentalSequence`、`Arithmetic`（`isSuccLimit_iff`、`isSuccPrelimit_iff_succ_lt`、`opow_lt_opow_iff_right`、`opow_succ`、`grw`）
- 注意：`IsNormal` 是**根命名空间**，不是 `Ordinal.IsNormal`（我在这上面踩过，实测确认）
- 除 Mathlib 外无外部依赖

**预计 DAG**

```
repr, NFB/NF, tower
   ├── NFB.repr_lt ──────────────┐
   ├── isSuccLimit_eps ──┐       │
   ├── tower_lt_eps ─────┤       │
   ├── tower_strictMono ─┤       │
   └── tower_cofinal ────┴ eps_has_prop
                                   │
        fundamentalSequence_has_prop ── fastGrowing ── fastGrowing_succ / _limit
                                                            │
                                                    bridge: = ONote.fastGrowingε₀
```

宽度 ≤ 3，深度 ≤ 4，**无扇形爆炸**。满足报告第七节的六条筛选标准（除第 2 条的 `fundamentalSequence_has_prop` 是"一个大的"而非"多个小的"，但它是**单条** theorem，且已有原文可照抄）。

**第一阶段过后立刻能产出的真实新 FGH 示例**：ε₀、ε₀+1、ε₀·2、ε₀²、ω^(ε₀+1)、ε₀·ω、……一直到 ε₁ 以下任意项。这些都是今天 Mathlib 一个数也算不出来的层级。

---

## 7. Roadmap（仅 MVP 成功后考虑）

```
[第一阶段]  ε₀ 原子扩展，逼近 ε₁            ← 本报告推荐，~200 行
     ↓  （第二阶段前必须先补：唯一性 + 完备性 + cmp）
[第二阶段]  epsilon hierarchy / 参数化 VNF（φ₀,φ₁）→ 逼近 ζ₀ = φ₂(0)
     ↓
[第三阶段]  二元 Veblen below Γ₀            ← 参照 Coq T2（draft），成本量级大跳
     ↓
[第四阶段]  Γ₀ 的 FGH（可复用 lt_gamma_zero + IsFundamentalSeq.comp_isNormal）
```

一个可选且有吸引力的旁支：Mathlib **已有** `Computability/Primrec/Basic.lean`（原始递归函数）与 `Computability/Ackermann.lean`。MVP 一旦让 ε₀ 进入层级，经典结论

> FGH 在 ε₀ 处最终支配一切原始递归函数

所需的全部构件就都在手上了。这条**比继续往上堆序数更有排他性的吸引力**，我建议排在第二阶段之前作为一个可选的高价值节点。【已推测，`Primrec` API 我未细查，需要先做一次 API 侦察再排期】

**明确不进入当前任务**：TREE、Buchholz hydra、Bachmann–Howard、ordinal collapsing functions（尤其不要自创 collapsing function）。理由：它们需要的是一套全新的 collapsing machinery，与第一阶段的"最小 CNF 扩展"没有任何代码复用关系。

---

## 8. Prove2Me vs Mathlib 判断

**结论：这个 MVP 首选 Mathlib PR，不是 Prove2Me theorem submission。**

理由：

1. **成果性质 95% 是 reusable infrastructure**（一个 datatype + 一套 FS + 一套 FGH），不是一个"具体 theorem"。Prove2Me 的 submission 流要求每个节点是一份可独立 type-check 的 `theorem solution`，适合承载"忠实形式化某篇论文/教材的某个具体命题"；一个 datatype library 塞进去既不自然也不利于他人 import。【已推测，基于参考 docs 描述的 submission/import 机制】
2. **上游动机是硬编码在源码里的。** `Notation.lean` 第 1161–1163 行就是 TODO 原文：

   > Extending the fast growing hierarchy beyond this requires a definition of fundamental sequence for larger ordinals.

   这正是我们要做的第一件事。这种针对性极强的缺口感 + 现在这个文件**无人使用**（除 `Mathlib.lean` 自己）→ PR 的"为什么要冗余一个类型"的质疑会比较容易被回答。【已确认，读源码】
3. **Mathlib 已经预付了成本。** ε₀ 的极限性、ω-塔的共尾性、FS 穿过正规函数的 transport —— 三条都是现成的。做 Mathlib PR 恰好是在"激活"这些悬空 asset，而不是新建一套平行宇宙。
4. **Prove2Me 目前没有可承接这个工作的 mission 生态**：没有相关 mission、没有可 import 的相关 theorem。硬塞进平台反而会把我们自己变成唯一的 review 者。【已确认，§3】

**反向**：如果哪一天出现一个明确的、可引用的具体命题（例如 Miller 1976 或某篇专门用于 <ε₁ notation 的论文中的一条 crisp 定理，其 statement 可以被完整、封闭地写成一个 `theorem`），那才轮到"Prove2Me mission"。当前的 "FGH beyond ε₀" 更接近 folklore/标准教材内容，**不满足这个条件**。

> 给宇轩的一句话建议：**先在本地把它做成 Mathlib PR 的形状**（`Mathlib.SetTheory.Ordinal.Notation` 的扩展，或一个新的 `Mathlib.SetTheory.Ordinal.EpsNotation`），不要开 mission。等 PR 有反馈了，再决定要不要顺手 Share 到平台。

---

## 9. GO / NO-GO

### **GO —— WITH REDUCED SCOPE**

**为什么是 GO：**

1. 缺口真实且被源码承认（`Notation.lean` 的 TODO 指名 discomfort）。
2. 截至当前的"最小设备舱"已经被**实际编译验证**：加一个构造子后，`fundamentalSequence` + well-founded `fastGrowing` 全流程通过，`termination_by o => o` 依旧成立。这不是估算，是 `lake env lean` 的输出。
3. 新数学几乎为零：ε₀ 需要的四条性质全部可由 Mathlib 现成引理在几行内推出（`lt_epsilon_zero` 尤其关键）。真正的成本在"改写现有证明"，而不是"发明新证明"——这是罕见的好性质。
4. DAG 可控：5 个定义、8–10 条定理、宽度 ≤3、深度 ≤4。
5. 不重复任何人：平台上零相关内容；Mathlib 里这个 file 无人使用。

**为什么必须 REDUCE SCOPE：**

下列三项必须**从第一阶段砍掉**，否则 DAG 一定爆：

| 削减项 | 为什么砍 | 何时补 |
|---|---|---|
| 表示**唯一性** | 需要完整的 <ε₁ 序数结构理论，是本 memories里真正贵的部分 | 第二阶段的第一件事 |
| 表示**完备性**（每个 <ε₁ 序数都能表示） | 同上 | 同上 |
| `cmp` / `LinearOrder` / `DecidableRel` | **FGH 不需要**（这是我实测确认的），但一旦想要"像样"的 notation system 就会忍不住 | 与唯一性一起 |

只要守住这条线，MVP 是**良基pipeline + 少量新引理**的组合，而不是"重建 ε₀ 以下再往上加一层"。

**最大风险**（按严重性排序）：

1. **风险 1：`fundamentalSequence_has_prop` 的改写比预想麻烦。** ONote 那条证明里有若干 `simp only` / `rw` 依赖 `repr` 方程的精确形状；加了一个构造子后 `repr` 多一个方程，`oadd_lt_oadd_*` 一类辅助定理可能需要重排。我用 `sorry` 绕过了这一段，因此**这一条防止 Mis modeling 为"已确认"** —— 它是**未实测的推测**。建议动手第一件事就是把它补掉，因为它决定整个工期。
2. **风险 2：忍不住补唯一性。** 这是绝大多数 ordinal-notation 形式化项目失控的地方。Coq 的 Γ₀ 层就是教训。建议单独开 issue 记录唯一性路线，明写"第一阶段不做"。
3. **风险 3：上游拒绝**。 Mathlib 可能更希望直接做"CNF<｜hy_place▁holder▁no▁813｜> invVeblen 的 Γ₀ VNF"（毕竟 Veblen.lean 的注释已经暗示这条路），而不是加一个只到 ε₁ 的类型。建议 PR 前在 Zulip 先探一下口径。
4. **风险 4（次要）：命名与放置。** 是扩展 `Notation.lean` 还是新建 `EpsNotation.lean`？考虑到 `ONote` 现有 ~1300 行且部分的 add/mul/opow 与本项目无关，我倾向**新建 module 并 `import` 现有 `Notation`**，避免把没人用的旧 machinery 拖进依赖图。

---

## 附录：证据文件

| 文件 | 用途 |
|---|---|
| `tmp/fgh_probe.lean` | `#check` 全表，确认所有 API 名称与类型（编译通过） |
| `tmp/eps_probe.lean` | MVP 最小骨架，**干净编译**，仅 1 个故意的 `sorry` |
| `tmp/p2m_helper.py` | Prove2Me 认证（处理 `credentials.json` 的 UTF-8 BOM） |
| `tmp/p2m_report.py` / `tmp/p2m_report.txt` | 21 组关键词、211 个节点的扫描结果 |
| `tmp/p2m_hardy.py` | `hardyLevel` / `EmlClass` 名字碰撞的核验（结论：无关） |

**顺手发现的一个仓库 bug**（未修改）：`scripts/p2m_api.py` 读 `credentials.json` 时用 `encoding="utf-8"`，而该文件带 UTF-8 BOM，导致 `json.load` 抛 `JSONDecodeError: Unexpected UTF-8 BOM`。应改为 `utf-8-sig`。我在 `tmp/p2m_helper.py` 里做了局部绕过。另外 `/theorems?q=Veblen`、`?q=epsilon` 等在服务端会返回 HTTP 500，需要retry。

**边界声明**：本报告没有提交任何 Lean 代码到 `Definitions/`、`Theorems/`、`Solutions/`（照记忆，那里 `autoImplicit false`，且 lib 上传前的 infotopic rule要求实 swallow ican分步）；没有创建任何 Prove2Me mission 或 theorem。`tmp/` 下的文件都是探测性质、输出也写在 `tmp/`。
