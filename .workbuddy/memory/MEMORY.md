# Project memory — prove2me_workspace

Lean 4 / Mathlib 打 prove2.me 众包形式化平台。**本文件只做索引**：

| 想找什么 | 去哪 |
|---|---|
| Lean / Mathlib 踩坑、tactic 怪癖 | `memory/LEAN-PITFALLS.md` |
| 平台 API、成员资格、draft 校验、盲审、两种提交模式 | `memory/PLATFORM-NOTES.md` |
| 幻方领域数据、BCCG 文献、可选路线 | `memory/MAGIC-SQUARES-REF.md` |
| 单个 mission 的设计与进度 | `missions/<slug>/status.md` |

## 环境（Windows）

- Bash PATH 是坏的：**每条命令先**
  `export PATH="/usr/bin:/bin:/c/Windows/System32:/c/Windows:$PATH";`
  PowerShell 工具取不到输出，别用。**同一消息里别并行发两个 Bash 调用**（其中一个会被
  SIGTERM 且无输出，2026-09-17 复现三次）；长命令用 `run_in_background`，后台跑时也别再发第二条。
- 🔴 **别用 Bash 删 `Solutions/` 里的文件**（2026-09-17：三次尝试导致整个目录消失）→
  改用资源管理器；恢复 `rm -f .git/index.lock && git checkout HEAD -- .`。
- Lean `v4.33.1`（elan），Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，
  已构建在 `.lake/`（8.4 GB，**绝不删**）。Python：
  `C:/Users/anche/.workbuddy/binaries/python/versions/3.13.12/python.exe`。
- 单文件 `lake env lean <file>`；模块 `lake build <Module.Name>`。
  ⚠️ **全量 `lake build` 会随机失败 20–35 个模块**（`failed to read file '...olean'`，
  并发 IO 竞争未定位）→ 只 build 目标模块。
- `lakefile.lean` 给 `Definitions`/`Theorems`/`Solutions` 开了 `autoImplicit false`，
  `examples/` 不是 lean_lib（那里是 ON）⇒ **提交前必须挪进 `Solutions/` 再编一遍**。
  **例外**：`examples/magic-squares/spencer/` **八**文件互相 `import`，2026-09-19 已加成 lean_lib
  `SpencerRoute`（非 default target；roots 见 `lakefile.lean`）→ `lake build SpencerRoute`
  （冷 ~2–3 min，热 30 s）。import 名带书名号：`import examples.«magic-squares».spencer.SupportSplit`。
- `lakefile.lean`/`lean-toolchain`/`lake-manifest.json` **都是被跟踪的**（2026-09-19 复核：
  `git ls-files` 三个都在，`git check-ignore` 无输出 ⇒ 当前**不匹配任何 ignore 规则**）。
  ⇒ 常规 `git add` 即可，**不需要 `-f`**（旧记录说要 `-f`，已作废）。

## 各 mission 状态指针

| mission | slug | 状态 |
|---|---|---|
| Magic Squares I（$M_3$ 计数） | `magic-squares` | goal Proved，proposal Reviewed |
| Magic Squares II（$H_3$） | `semi-magic` | goal Proved（`semi_magic_count_three` 2026-09-19 复核 Proved），proposal Reviewed |
| Magic Squares III（洛书唯一性） | `normal3` | goal Proved，proposal Reviewed（`98d3dea7`） |
| **Magic Squares IV（泛魔/对称三阶计数）** | `magic-squares-iv` | goal + 6 定理 + 1 定义全 Proved（2026-09-18，5 份一次 ACCEPTED）；proposal `7af96e14` `In review` |
| **Magic Squares V（一般 n 的计数多项式）** | `magic-squares-v` | ✅ **V 已 live**：`mission_id = e06131f8-1bf5-47c4-b8f4-507f107269e0`（提案 `3a8476fd` → `Reviewed`；别和 mission IV `df1cb8cc` 搞混）。**8 条 milestone**，goal = `semi_magic_polynomial_exists`（`72482ba2`，仍 `Open`）。✅ **2026-09-20：Spencer 路线的本地终点已上平台** —— 节点 `4394b225-cc88-46d4-a57e-0765707d3246`（`semi_magic_polynomial_exists_degree_eq`，**Proved**，提交 `448ec295` ACCEPTED），milestone `4995687d` 挂在 sort_order 5；`vol(B_4)` 里程碑文字已更正（新 id `c791e322`，旧的 `9e912298` 被误删过）+ 讨论区更正评论 `f4035c14`。**只剩 S5**（倒易律 `q(−1)=1`） |
| 孤儿挂回（一次性） | `magic-squares-reattach` | 2026-09-19：18 条定理经 milestone 挂回，22 → 4 孤儿（余 4 个是定义；V 已于 21:1x 转 live ⇒ 挂回条件已满足，尚未执行） |
| Every Odd Number … Five Primes | `five-primes` | Open；真 frontier 18 条叶（2026-09-18）。已约简 `rosser_schoenfeld_theta_lower_analytic`（SKETCH_ACCEPTED）；`theorem51_typeII_dyadic_representation` ACCEPTED；`vaughan_split` **数值证伪** |
| Weak Goldbach | `weak-goldbach` | 目标 Open，已归约到一个筛覆盖孩子 |
| Bunkbed is False | `bunkbed` | 全部封版归档 |
| Irrationality of Euler's γ | `euler-gamma` | 部分 Proved，见 `sondow/INTEGRAL-IDENTITY-COMPLETE.md` |

**五素数三条硬约束**（细节在 `missions/five-primes/status.md`）：
① frontier 的 18 条叶大多是硬外部结果（R&S、Schoenfeld、Liu–Wang、Siebert、Helfgott–Platt、
4·10^14 Goldbach 计算）；② `theorem51_vaughan_split` **是假的**（评论 `1c0c941b`，
反例 `vaughan-step-counterexample.lean`）——别再当 LOCAL_BRIDGE；③
`theorem51_typeII_dyadic_block_bound` **不是短约简**（三个「已证成分」都以 Open 的
`large_sieve_inequality` 为假设）。**完整数值证伪不可行**：需 ~1400 条 7–8 位精度
`Real.log` 界、~10⁵ 行。动手前先读 `GET /missions/<mid>/comments`。

## 幻方领域红线

细节全在 `memory/MAGIC-SQUARES-REF.md`。留在本文件的三条：

- **`IsPanMagic` ≠ BCCG 的 $P_n$**：我方要**两个方向**的断对角，BCCG 只要**一个方向**
  （含主对角、绕回、**不要求副对角**）。$n=3$ 实测：单向 $=\binom{t+2}{2}$，
  双向 $=\mathbf 1_{3\mid t}$。**引用时不可互相对照。**
- **Mathlib 无 Ehrhart / 拟多项式 / 有理生成函数**（grep 过）。格点计数机制要自建。
- 一句话现状：**$n=3$ 完全闭环、$n=2$ 补齐、一般 $n$ 只有 1 条、$n\ge4$ 零**。
  方向已定：**BCCG Theorem 1（Ehrhart–Stanley）**，走 Spencer 1980 初等路线。
- 🔴 **动 M5 前先读 `missions/magic-squares-v/SPENCER-ROUTE.md`**（§4.2 上下界、§7 实现坑、**§8 构建与剩余步骤**）：
  Spencer 是**纯初等**路线（生成函数 + Hall + 支撑集偏序，**不用 Ehrhart**），Mathlib 零件齐
  （Faulhaber 伯努利形式 `Polynomial.sum_range_pow_eq_bernoulli_sub`、
  `Finset.all_card_le_biUnion_card_iff_exists_injective`）。
  **2026-09-19 状态：S1/S2/S3/S4 全完，只剩 S5。** 八文件、无 sorry/axiom，`#print axioms` 只有
  三条标准公理；`lake build SpencerRoute`。
  1. 粗版（`Aggregate.lean`）：`exists_polynomial_semiMagicCount_pos`，次数 `≤ n*n`，`t ≥ 1`；
  2. 锐上界（`Rank.lean`+`Sharp.lean`）：`exists_polynomial_semiMagicCount_sharp`，次数 `≤ (n−1)²`；
     `rankB B := dim(零线和空间)`（= 面秩 ρ，无图论）；严格单调靠**逃逸引理**
     （对偶 `range_dualMap_eq_dualAnnihilator_ker` + σ/τ 两组求和矛盾；**裸「φ(τ)⊆C⊆B ⇒ 严格」是假的**，
     必须用 candidate 约束 `B\φ(σ) ⊆ C`）；
  3. **精确次数（`Degree.lean`，Brick 11）**：下界用**显式线性族**——阶 `n+1`、线和 `(n+1)s` 时取自由块
     `c : Fin n → Fin n → Fin (s/n+1)` 铺左上 `n×n`，末行/列/角由线和补出 ⇒ 单射 ⇒
     `semiMagicCount (n+1) ((n+1)s) ≥ (s/n+1)^(n*n)`（`semiMagicCount_ge_family`）；再用纯初等
     `le_natDegree_of_lowerBound`（`eval_le_mul_pow` + `exists_nat_gt`，无渐近）逼出下界。终点：
     ```
     theorem MagicSquaresSpencer.exists_polynomial_semiMagicCount_degree_eq (n : ℕ) (hn : 1 ≤ n) :
         ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
           ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
     ```
     ⚠️ 签名与平台 goal **只差 `1 ≤ t`**，别拿它冒充 goal。
  **剩余**：**只有 S5** —— 线和 = 0 处的值 `q(-1) = 1`（= Ehrhart–Macdonald 倒易律在 −1 处，
  等价于 `B_n` 无内格点；最硬，需另立课题）。**degree_eq 已于 2026-09-20 作为 sibling 节点
  发布**（节点 `4394b225`，milestone `4995687d`，ACCEPTED）——注意它只是 goal 的弱化版，
  **goal 仍然 Open**。

## 仓库卫生

- 两轮瘦身（2026-09-17）只做 `git rm --cached`，**磁盘文件全保留**；974 跟踪文件 /
  索引树 18.1 MB；5 个大证书物理删除释放 199.7 MB。新生成的证书产物一律写 `tmp/`。
- ⚠️ `.git` 仍 146 MB（历史里还在），彻底瘦身要 `git filter-repo` + force push
  —— **不可逆，必须宇轩明确点头**。

## 用户偏好

- 数学/Lean/文档写**英文**，给他的汇报写**中文**。Lean 教学别拆太碎，给完整证明任务。
- **严格区分「我确认了」和「我推测」**——数值验证 ≠ 形式化证明。
- 不可逆操作（rewrite history / force push / 删历史产物）**必须先问**。
- 要可运行的交付物，不要「看起来完成了」。
- **他是这几个幻方 mission 的 captain**（2026-09-18 本人确认）⇒ 挂节点、批 proposal
  这类 captain 动作他自己能做，别默认要走外部评审。
