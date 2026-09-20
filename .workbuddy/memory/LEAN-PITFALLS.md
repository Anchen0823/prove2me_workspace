# Lean 4 / Mathlib 踩坑清单（prove2me_workspace）

配套 `MEMORY.md`。这份清单按主题堆规则，不按 mission。**新坑往这里加，别往
MEMORY.md 加**（那只要保持小到能被注入）。环境：Lean `v4.33.1`，
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。

## 记号与 tactic

- **`∑ k in s, f k` 本版本不解析** → 写 `∑ k ∈ s, f k`。
- 🔴 **空集判定的大小写**（2026-09-19 更正本行）：`Finset.eq_empty_iff_forall_not_mem` **不存在**
  —— 正确名是 **`Finset.eq_empty_iff_forall_notMem`（大写 M）**，签名
  `s = ∅ ↔ ∀ x, x ∉ s`。旧记录里写的 `Finset.not_nonempty_iff_eq_empty` 只在
  `s.Nonempty` 反面可用；要「证空集」直接用前者。
- `Finset.not_mem_empty` **也不存在**：`rw […] at h` 后 `h : x ∈ ∅` 且目标 `False` 时，
  用 `simp at h`（会化简成 `False` 并关掉目标），别 `exact Finset.not_mem_empty _ h`。
- 🔴 **对 `.card` 求和别用裸 `Finset.sum_congr`**：若 `f C = (matFiber … C).card`、而手头只有
  **Finset 相等**的引理，写 `Finset.sum_congr rfl (fun C _ => h C)` 会让它把两个函数统一成
  *Finset* 值，报出极误导的 `failed to synthesize AddCommMonoid (Finset (Matrix …))`。
  正确写法：`fun C _ => congrArg Finset.card (h C)`。
- 🔴 **`def` 包的 Prop 上点记号会跑偏**：`(h : IsPolyDegLe K b).mono hle` 报
  `Invalid field 'mono': The environment does not contain 'Exists.mono'`（因为 `IsPolyDegLe`
  展开成了 `∃`）。用全名调用 `isPolyDegLe_mono h hle`，或把引理声明成 `IsPolyDegLe.mono`。
- 🔴 **`push_cast` 的顺序不对称**（`rw` 进带 cast 的目标时）：
  目标 `↑(#B') = ↑(#B) + ∑ C, ↑(#(… C))`，
  - 先 `push_cast` 会把右边的 sum 拉进 cast（`↑(#B + ∑ C, #C)`），且 linter 报它
    「does nothing」——**别信这个警告**；
  - 正确顺序是 **先 `rw [hstep]`**（hstep 是 ℕ 级等式），**再 `push_cast`**，最后 `rfl`
    （两侧只剩 binder 名不同，alpha 等价即关）。
- `Polynomial.eval x (0 : ℚ[X])` **不 defeq 于 `(0 : ℚ)`** ⇒ 想把多项式取成 `0` 时
  `show (0:ℚ) = …` 会失败 → 用 `Polynomial.C 0` + `rw [Polynomial.eval_C]`。
- **Mathlib 无 `Finset.strong_induction_on`**（2026-09-19 grep 全库，只有
  `Nat.strong_induction_on`）→ 有限集强归纳写成
  `have key : ∀ k, ∀ B, B.card = k → P B := by intro k; induction k using Nat.strong_induction_on with | _ k ih => …`，
  用 `ih C.card (by rw [← hBk]; exact Finset.card_lt_card hlt) C rfl`。
  `(n - 1) + 1 = n` 用 `Nat.sub_add_cancel hpos`（`hpos : 1 ≤ n`）。
- 🔴 **`Polynomial.natDegree_C` 要显式参数**（2026-09-19 踩）：`natDegree_X` 无参，但
  `natDegree_C (a) : (C a).natDegree = 0` 是带参的 → `le_of_eq Polynomial.natDegree_C` 报
  "Application type mismatch … expected `(C 1).natDegree = 0`"。写
  `le_of_eq (Polynomial.natDegree_C (1 : ℚ))`。复合次数界用
  `Polynomial.natDegree_comp_le`（`≤ natDegree p * natDegree q`）+ 显式 `calc`，
  别用 `natDegree_sub_le_of_le ?_ ?_`（它把 `m`/`n` 留成元变量，`.trans` 接不上）。
- **`Finset.card_eq_sum_card_fiberwise`**（在 `Algebra/BigOperators/Group/Finset/Basic.lean`，
  名字就在 `Finset.` 下，**不在** `Finset.Nat.` —— 那里只是 `section Nat`）：
  签名 `(H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}`。
- ✅ **查「是不是真证完了」的省事办法**：`tmp/check_x.lean` 里写
  `import <模块全名>` + `#print axioms <定理名>`，跑 `lake env lean tmp/check_x.lean`。
  输出 `depends on axioms: [propext, Classical.choice, Quot.sound]` = 无 `sorryAx`；
  `#print <定理名>` 还能把**实际陈述**（而不是你记忆里的陈述）打出来核对。
  用 lib 里的模块名要带书名号：`import examples.«magic-squares».spencer.Aggregate`。
- **scratch lib 可以 import 平台定义**：`Definitions` 本身就是 lean_lib ⇒ 在
  `examples/...` 里写 `import Definitions.Def_MagicSquares` + `open MagicSquares`
  就能直接用 `semiMagicCount`/`IsSemiMagic`，不必重述（Aggregate.lean 就是这么接的）。
- 用 `Finset.filter` + 命题谓词的 def 必须放 `noncomputable section`。
- `Finset.single_le_sum` 被遮蔽时推断失败 → 显式 `s :=`、`f :=`。
- `Finset.mem_filter.mp (by simpa …)` 常失败 → 先写显式类型的
  `have h' : x ∈ (…).filter p := by simpa …`。
- `Finset.sum_range_reflect f (n+1)`：`∑ j, f (n-j) = ∑ j, f j`。
- `tsum_eq_zero` **不存在** → `rw [tsum_congr (fun d => tsum_congr (fun w => hzero d w))]; simp`。
- **`Finset.eq_singleton_iff_unique_mem`** 是证「有限集 = 单点集」的省力写法：
  `rw [Finset.card_eq_one]; refine ⟨x, ?_⟩; rw [Finset.eq_singleton_iff_unique_mem]`
  → 给「x 在集合里」+「任何元素等于 x」；比构造到单点类型的双射便宜。
- 计数写成 `C(n+k-1,n)` 时改成「k+1 个部分」，避开 `k-1` 的 Nat 截断减法。
- **平台禁 `native_decide`**（trusts compiled native code）→ `norm_num […]`/`decide`。
- **心跳上限 200000** → solution 顶部 `set_option maxHeartbeats 0`；别 `dsimp [x] at h` 展开 let
  （改 `have hx_def : x = … := rfl` 再交给 omega）。
- 平台对 tactic 冗余敏感：本地 `rw …; ring` 可能报 `No goals to be solved` → 用 `simpa […]`。
  偶发 `Import parser timed out after 5s` → 原样重提。
- 🔴 **`DecidablePred` 只认陈述层**：把
  `Finset.univ.filter (fun M : Square 3 _ => IsPanMagic …)` 直接写进 `example`/`theorem` 的
  **类型**里会报 `failed to synthesize DecidablePred`（证明体里的 `classical` 救不了，
  陈述先 elaborate）→ 陈述要经由 `panMagicCount`/`magicCount` 这类内部已 `by classical`
  包装的 def 表达，或在证明里用 `change` 展开。
  **2026-09-19 再次踩到、且后果极具误导性**：`theorem ... : ((matBox n t).filter (fun M => LineSums M t)).card = …`
  在陈述层就崩，症状却是**后面所有 tactic 集体失灵**（`rw [matBox]` 报 "Failed to rewrite using
  equation theorems"、后续 tactic 全被标 "never executed"、整条声明被打成 "uses `sorry`"）。
  ⇒ 正确做法就是把那个 filter 提成具名 def：
  `noncomputable def matBoxLine (n t) := by classical exact (matBox n t).filter (fun M => LineSums M t)`。
  **教训：一条报错可能是「声明其实没 elaborate」，别急着逐一去改后面的 tactic。**

## Fin / 矩阵

- **`Fin.cons` 是依赖类型版**，钉住类型族
  `Fin.cons (n := k) (α := fun _ => Fin (N+1)) x q`；`simp [Fin.cons_zero, Fin.cons_succ]`
  会踩 → 用 `change`。
- **`simp` 不展开 `Fin n` 上的全称量词** → 显式 `Fin.forall_fin_succ` 剥到地面再 `norm_num`
  （`Fin.forall_fin_three` 不存在）。
- **`Fin n` 上的索引算术（`i + k`、`Fin.rev i + k`）不会自动化简**：`k : Fin n` 上量词是符号的，
  必须 `fin_cases k` 剥到地面实例，再 `simp [brokenDiagSum, Fin.sum_univ_three]`
  才得到 `M 0 1 + M 1 2 + M 2 0` 这类显式项。
- **`Square n α` = `Matrix (Fin n) (Fin n) α`**；具体方阵用嵌套向量
  `![![a,b,c],![d,e,f],![g,h,i]]`（`!![…]` 是单行，类型不对）。
- `ext i j` 对 `Square n ℕ` 已展开到 Nat，**其后别加 `apply Fin.ext`**；
  ⚠️ 对 `Square n (Fin k)`（计数函数的元素类型）**也是给 ℕ 相等**，同样别加
  `apply Fin.ext`（报 could not unify `@Fin.ext`）。
  跨 `Fin (t+1)` 与 ℕ 取值用 `congrArg (fun x : Fin (t+1) => (x : ℕ))`。
- `ext` 处理 `Finset (ℕ × ℕ)` **先 `rcases` 拆配对**，否则 `rfl` 在 `ac.1` 上失败。
- `Square 3 ℕ` 与 `Fin 3 → Fin 3 → ℕ` 在**写了类型标注**时不可互换 →
  不给 `have` 写类型，让它推断，再 `congr_fun`。
- 具体成员资格用 `norm_num [paramSet, IsParam3]`；`simp` 只展开到 range/product/filter。

## Nat 算术与 omega

- `omega` 对混大字面量/`/` 的 Nat 目标会 "maximum recursion depth" →
  拆 `Nat.div_mul_le_self`/`calc`。`omega` **原生支持 `min`**（`Nat.min_eq_zero_iff`）。
- `omega` 能一次吃掉十几条「三项之和 = 常数」的加法等式（`pan_three_card` 的 12 条线方程 ×
  9 个 `fin_cases` 目标），Nat 截断减法的可满足性（`a + (2*e - a) + e = 3*e ⟹ a ≤ 2*e`）
  也能靠 case split 找到，**不必手写分支**。
- **`Nat.mul_div_left` 的隐参数顺序**：`mul_div_left m {n} (H : 0 < n) : m * n / n = m`
  （**乘数在前、除数隐式**）。所以 `3 * e / 3 = e` 要写
  `by rw [mul_comm 3 e]; exact Nat.mul_div_left e (n := 3) (by norm_num)`；
  写成 `Nat.mul_div_left e (by norm_num)` 会因 `by norm_num` 在 `?n` 赋值前 elaborate
  而报 `⊢ 0 < ?m.86`。

## 实数分析（分析类节点）

- `rw [h]` 会连**右侧子项里的同名变量**一起重写（`ht_eq : t = s^8` 而 `s` 含 `t`）→
  先 `have := congrArg Real.log ht_eq` 再 `rw`。
- `rw [lt_div_iff₀ h]` 要求形如 `a < b / c`；`(19/40) * (t / L)` 先 `rw [← mul_div_assoc]`。
- `linarith` 串两个 `√` 原子不稳 → `exact le_trans h1 h2`。
- `rw [Real.log_pow]` 需先把 `t` 写成 `(root)^8`；`Real.log_two_lt_d9` 在
  `Mathlib.Analysis.Complex.ExponentialBounds`，要显式 import。
- `congr_fun`/`integral_congr` 目标带 lambda beta-redex → 先 `show f W = g W` 再 `rw`；
  **binder 内部**的 tsum 不能直接 `rw [← 引理]`（元变量推不出绑定变量）→
  用 `setIntegral_congr_fun` + `simp only [引理 x W]`，或 `IntegrableOn.congr_fun … measurableSet_Ioi`。
- `setIntegral_eq_integral_of_forall_compl_eq_zero` 方向是 `∫ in s = ∫`（反用加 `.symm`）；
  `∫ in Ioi 0 = ∫ in Icc a b` 要经无限制积分分两步转。
- `Complex.ofReal_mul` 只匹配 `↑(a*b)`；`if` 在 cast 内部先 `by_cases` 拆开再 `rw [if_pos …]`。
- **`⟨…⟩` 里 hypothesis 参数别用 `by linarith` 猜**：缺哪个假设就补进引理签名
  （2026-09-18 `integrableOn` 缺 `hUx/hVx/hUV` 各一次）。
- **平台 summand 与本地 def 的形态要逐字核**：本地 `theorem51FiniteScaleKernel` 含 `W⁻¹`、
  平台 `typeII_dyadic_representation` 不含 ⇒ `K W = W * kernel W`，不是 `= kernel`。

## Lake / 工程

- 新增 `Definitions/*.lean` 后先 `lake build Definitions.Def_X` 生成 olean。
- **`theorem solution` 必须在 namespace 之外**（顶层），否则平台报
  `Unknown identifier solution`；移动时前面的 `/-- -/` doc comment 必须一起搬。
- **`/-- doc -/` 不能挂 `namespace`**（报 `unexpected token 'namespace'; expected 'lemma'`）
  → 段首说明用 `/- … -/`。
- 🔴 **Lake lib target 必须有「根模块文件」**：`lean_lib «Solutions»` 会去找 `Solutions.lean`，
  没有就报 `some modules have bad imports` 且**一个任务都不跑**
  （`lake build Solutions.Sol_X` 一直能过，所以长期没发现）。
  已修：每个 lib 显式 `roots := #[]` + `globs := #[.submodules \`Solutions]`。
- `import examples.…`（连字符目录写 `examples.«five-primes».X`）未声明为 lib 时
  `lake build <源文件路径>` 报 unknown module source path；要用就声明成 lib。
- **内联 bundle 的 `import` 必须在文件最前**（`/-! -/` 放前面 → `invalid 'import' command`）。
- **`Edit` 工具在 `Solutions/` 下出现过「报成功但没落盘」**（2026-09-18，两次）→
  改完必须 `grep`/`Read` 复核，或整体 `Write` 覆盖。
- **`lake script`/lake 别用 `timeout` 掐**：SIGTERM 掉 lean 子进程会报 code 143，像编译错。

## `fin_cases` 与 omega（2026-09-18，P0 六个对齐定理踩到）

- 🔴 **`fin_cases` 之后的 Fin 索引不是字面量**：分支目标里出现的是
  `M ⟨0, ⋯⟩ ⟨1, ⋯⟩`（`Fin.mk k _`），而假设里是 `M 0 1`（`OfNat` 形式）。二者的
  **proof component 不同 ⇒ 不是 definitional equality ⇒ `omega` 把它们当两个原子**，
  于是 `omega` 报「可能的反例」而失败。`simp` / `rw` / `exact` 按 `isDefEq` 匹配，
  不受影响。
  **对策（可靠）**：在**数字索引**处先把需要的等式证出来（`omega` 在无 `fin_cases`
  的上下文里工作正常），然后在 `fin_cases` 的分支里用 `exact`/`rw`/`simp only` 去用它们。
  另外 `show (M 0 1 : ℕ) = (N 0 1 : ℕ)` 能把分支目标改写回数字形式（`show` 用 defeq 检查）。
- `dsimp only at h ⊢` / `dsimp only at *` 在这种场合**不一定**能归一化 Fin 字面量，
  别指望；用上面那条。
- 用 `let g : Fin 3 → ℕ := ![x, y, z]` 定义辅助函数时，`g ⟨0,⋯⟩` 的化简同样卡在索引形式上；
  **改用 `fun k => if (k : ℕ) = 0 then … else if (k : ℕ) = 1 then … else …`**，
  化简变成可判定的，`simp` 能一路算完（`pandiagonal_count_three` 的 surj 分支就是这样过的）。
- **`Finset.sum_range_reflect (f) (n)` 的方向是 `∑ i, f (n-1-i) = ∑ i, f i`**，
  即 `∑ (t-i+1) = ∑ (i+1)`，**不要再加 `.symm`**。
- **Pascal 的参数**：`Nat.choose_succ_succ' n k : choose (n+1) (k+1) = choose n k + choose n (k+1)`。
  要把 `(t+2).choose 2` 化成 `(t+1).choose 2 + (t+1)` 得用 `(t+1) 1`，
  写成 `t 1` 会得到 `t + t.choose 2`（一个看起来很像但错的结果）。
- **把定理从 `examples/` 抽成 `Solutions/` 单文件时**：抽取要**剥掉紧跟在后面的
  「下一个声明的 doc comment」**（它落在上一个块里），否则文件末尾悬挂一个 doc comment，
  报 `unexpected end of input; expected 'lemma'`。且**逐个串行 `lake build`**——
  并行 6 个会撞上本机已知的 `.olean.private` 随机读失败。

## 单例见证元必须具名（2026-09-19，`semi_magic_count_one` 费了三次编译）

用 `Finset.card_eq_one` + `Finset.eq_singleton_iff_unique_mem` 证「计数 = 1」时，
**见证元必须是具名项**：

```lean
let M0 : Square 1 (Fin (t + 1)) := fun _ _ => ⟨t, Nat.lt_succ_self t⟩
...
rw [Finset.card_eq_one]
refine ⟨M0, ?_⟩
rw [Finset.eq_singleton_iff_unique_mem]
```

把 lambda **内联**写成 `refine ⟨fun _ _ => ⟨t, …⟩, ?_⟩` 会让 `{…}` 这一步被解析成
**集合概括式**（Set comprehension）而不是 `Finset.singleton`，于是：

- `rw [Finset.eq_singleton_iff_unique_mem]` 报
  `Did not find an occurrence of the pattern @Eq (Finset ?m) ?m.30 {?m.31}`；
- `simp only [..., Finset.mem_filter, ...]` 报 **`Finset.mem_filter` 未使用**；
- `constructor` 报 **`target is not an inductive datatype`**（因为那已是 `Set.Mem`，
  即函数应用，不是归纳类型）；
- 偶尔还有 `full error: function expected M i`。

**症状全部指向错误的方向**（像是对 `M i` 的展开问题），实际原因是记号解析。
判据：只要看到「`Finset.mem_*` 被报未使用」+「`constructor` 说不是归纳类型」，
先怀疑**见证元/集合字面量的解析**，而不是那条 `simp` 引理名。

对照：已通过的 `Sol_MagicSquares_pan_three_card.lean` 用的就是具名 `constSquare3 e`，
一直没有这个问题 —— 这不是巧合。

## 求和引理的精确配对（2026-09-19，SupportSplit 费了 3 轮编译）

这个 pin 的 Mathlib 里，两个「省一个引理」的写法必须配对正确：

| 想要 | 用 | 别用 |
|---|---|---|
| `∑ x, (if a = x then f x else 0) = f a` | `Finset.sum_ite_eq` | `Finset.sum_ite_eq'`（它是 `if x = a` 形式） |
| `∑ x, (if x = a then f x else 0) = f a` | `Finset.sum_ite_eq'` | `Finset.sum_ite_eq` |

🔴 **`Finset.sum_sub_distrib` 对 `∑ x,` 形式匹配失败**（报 "Did not find an occurrence of the
pattern `∑ x ∈ ?m.65, (?m.72 x - ?g x)`"，且伴随 "not type-correct under the implicit
transparency level / function expected T i" 这类误导性附注）。一元的 `∑ x, f x` 与二元的
`∑ x ∈ s, f x` 只是 **defeq 相等，不是句法相同**，`rw` 按句法匹配就炸。
**绕法（可靠）**：改走加法——把目标写成 `∑ f = ∑ (f - g) + ∑ g` 用
`Finset.sum_add_distrib`，配合逐点 `Nat.sub_add_cancel (h : g x ≤ f x)`，最后 `omega` 收尾。

一般规律：**在 `∑` 里 `rw` 很脆**。优先 (a) 把等式 `have` 成局部重写规则喂给 `simp only [...]`，
(b) 用 `Finset.sum_congr`，(c) 干脆换一个不需要该求和恒等式的表述。

## `subst` 的方向与残余目标（2026-09-19）

`subst hki`（`hki : k = i`）会把 **`i` 换成 `k`**（保留右侧），所以目标里会出现 `σ k` 而不是
`σ i`；此后不要再指望 `if_pos rfl` 能收掉 `if σ k = j` —— 要从原等式里另取一条
（`(Prod.ext_iff.mp hk).2`）显式喂给 `if_pos`。`subst` 后原假设也会被改写，仍可继续用。

## 用 python heredoc 生成 Lean 源码时的反斜杠（2026-09-19）

🔴 **别用 `r'''...'''` 写 Lean 代码块**：`r` 前缀会保留 `\\`，而 Lean 里 `\\` 不是合法 token
（集合差只写 `\`）。症状：`unexpected token '\'`，而且**连带把它之后的整个证明炸成一堆
"unsolved goals"**，看起来像多处错误、其实只有一处。
**做法**：用普通三引号并在 python 里写 `\\`（会落成 `\`），或写完立刻 `grep -c '\\\\' <file>` 确认是 0。

## `card_bij` 的 `f` 与分析性投影（2026-09-19）

- `Finset.card_bij` 的 `f` 是 **`(a : α) → a ∈ s → β`**（带成员证明），所以写法是
  `refine Finset.card_bij (fun T _ => ⟨..., ...⟩) ?_ ?_ ?_`，三个子目标是
  ①`∀ a ha, f a ha ∈ t` ②`∀ a₁ h₁ a₂ h₂, f a₁ h₁ = f a₂ h₂ → a₁ = a₂` ③`∀ b ∈ t, ∃ a ha, f a ha = b`。
- 目标里出现的会是 `⟨a, b⟩.snd i j` 这种**投影形式**，`rw [Matrix.sub_apply]` 匹配不上
  （会报 "not type-correct under the implicit transparency level / function expected"）。
  **先 `show (T - permMatrix σ) i j ≤ s` 归一化**（`show` 按 defeq 检查）再 `rw`。
- `Finset.sigma` 的二段类型若**不依赖**第一段（如 `Σ C, Matrix ... ℕ`），
  `congrArg Sigma.snd h` 给出干净的等式；依赖的话会掉进 `HEq` 泥潭。

## `omega` 不会自己用 λ 型假设（2026-09-19）

`hbox : ∀ i j, T i j ≤ s` 在上下文里，`omega` **不会**替你实例化。
要先 `have hTij : T i j ≤ s := hbox i j` 再喂给 `omega`，否则它报"可能存在反例"，
且反例里那个量显示成一个**不透明的原子**（如 `c := ↑(T i j - permMatrix σ i j)`）——这就是信号。
