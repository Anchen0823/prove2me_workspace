# 互异素数多项式搜索

## 规则与目标

整数系数；连续整数输入；输出绝对值是互异素数；1 不算素数。
历史基准：二次45、三次46、整数系数四次46。达到更多项后需重新审计文献，不直接宣布世界纪录。

## 文件

- `scripts/search.py`：原始小系数有限穷举。
- `scripts/fast_search.cpp`：上一轮轮筛与滑动窗口搜索，保留可复现。
- `scripts/record_search.cpp`：本轮扩展算法。
- `scripts/verify_campaign.py`：独立精确试除验证每次改善及最佳候选。
- `scripts/verify_records.py`：文献实例验证。
- `verification/`：原始日志、统计、完整素数列表。
- [上一轮报告](CAMPAIGN.md)：搜索限制和性能测量。

## 2026-09-24 进展

源码与证据从被忽略的 tmp 迁入本任务。上一轮未打破纪录；二次45、三次46；高度331的三次候选产生39项。
本轮扩展三次范围、加入四次搜索并加强模素数筛选。结论由最终验证文件补充。

这是本地研究任务，没有向外部平台提交结果。根目录43个其他任务引用的临时文件仍保留原路径。


## 本轮结束：未打破纪录

| 搜索 | 筛后完整扫描数 | 本轮最佳长度 | 时间 |
| --- | ---: | ---: | ---: |
| 扩展三次 | 72,283 | 32 | 90秒 |
| 扩展四次 | 104,383 | 29 | 90秒 |
| 四次局部，目标47不漏解筛选 | 276,448 | 21 | 70秒 |

合计453,114次候选完整扫描。本轮最佳不替代上一轮较好的45/46项候选。
所有改善记录已用独立Python精确试除与互异检查验证；已知实例回归通过。
工作区索引检查通过。详细统计见 verification/continuation-summary.json。

新筛选的必要性证明见 [SIEVE.md](SIEVE.md)。该筛选对47项目标不漏解，但候选形状仍是限时抽样，不能证明不存在更好解。
下一步应优化无根筛选之外的小素数例外位置约束，降低安全筛选的素性测试成本，随后扩展批次；不宜单纯重复已有随机范围。

复现（仓库根目录，先确保临时构建目录存在）：

```powershell
New-Item -ItemType Directory -Force tmp/prime-polynomial-build
 g++ -O3 -std=c++17 missions/prime-polynomials/scripts/safe_search.cpp -o tmp/prime-polynomial-build/safe_search.exe
.\tmp\prime-polynomial-build\safe_search.exe 7 70 2026092404 missions/prime-polynomials/verification/quartic-next-20260924
python missions/prime-polynomials/scripts/verify_campaign.py
```

保留旧轮筛版本用于比较。新运行请换文件前缀和随机种子；目前不是断点续跑。


## 继续推进：保留小素数例外的快速筛选

实现 `scripts/exception_search.cpp`。对29至47之间的素数，模p有根时通过二分查找保留可能出现±p的候选，其余严格排除。

同样500个形状、25475个通过第一级筛选的候选：旧策略3.62691秒，新策略0.144318秒，约25.13倍（单次测量，含初始化）。精确扫描由25475降为54。低于目标长度的候选不保证保留，因此两种策略的短串最好值不可比较。

- 150000个小范围测试通过；20786个达到对应目标的正例没有误删；小素数例外与49项实例回归通过。
- 三次新批次：1767716个形状，63019252个第一级候选，93234个完整扫描，保留793个可能的小素数例外候选，未达47项。
- 五次有限扰动族：60801个形状全部访问，3177197个第一级候选，7215个完整扫描，20.63秒完成，仍为已知49项，未达50项。
- 上述五次扰动族、常数项范围[-498960,501269]、输入[-80,80]内，没有找到长度至少50的互异素数串；这不构成任何全局上界。
- 所有新改善记录均由独立Python精确试除验证。

完整指标、源码哈希见 `verification/exception-search-summary.json`。
实现已在有限形状访问完后提前结束，避免重复随机抽样消耗剩余时间。

复现宽五次批次：

```powershell
g++ -O3 -std=c++17 missions/prime-polynomials/scripts/exception_search.cpp -o tmp/prime-polynomial-build/exception_search.exe
.\tmp\prime-polynomial-build\exception_search.exe 8 45 2026092413 missions/prime-polynomials/verification/quintic-replay-20260924 0 exception 50
python missions/prime-polynomials/scripts/verify_campaign.py
```

下一步：改用不同的多项式形状家族或有理整值基；当前这组60801形状已经搜索完，换随机种子只会改变顺序，没有新覆盖。

## 多代理推进：新家族与增量轮筛（2026-09-24）

本轮仍未打破历史基准。三个子代理分别负责新家族、性能优化和独立审计，主线增加整数六次搜索并运行新的三次批次。

| 搜索家族 | 完整形状数 | 完整扫描候选数 | 找到的最长串 | 停止原因 |
| --- | ---: | ---: | ---: | --- |
| 整数六次，两次210倍系数扰动，R=20 | 16,401 | 16,671 | 44 | 有限族穷尽 |
| 有理整值五次，单项式扰动，R=50 | 60,801 | 2,856 | 57 | 有限族穷尽 |
| 有理整值五次，二项式基扰动，R=30 | 36,601 | 1,671 | 57 | 有限族穷尽 |
| 新轮筛三次，seed=2026092424 | 7,598,372 | 400,934 | 36 | 90秒限时 |

前三组分别未找到45、58、58项；现有44/57项都是已知基线。三次新批次未找到47项，36只是本批次筛后找到的长度，不替代已有46项实例，也不是该范围内短串的最优值。

范围：整数六次输入[-40,40]、常数[-498960,501269]；两种有理五次输入[-80,80]、整数常数[-498960,508199]；三次输入[-80,80]、常数[-498960,501269]。六次基形状及扰动证明见 [审计](audit_20260924.md)，有理五次精确定义见 verification/family_*_verified.json。未覆盖这些族之外的系数或输入。

优化引擎 `scripts/opt_wheel17_search.cpp` 增量生成模510510的允许剩余类。同种子、同形状数三轮中位数：三次1.67953→0.677015秒，约2.48倍；五次1.76099→1.50576秒，约1.17倍。六组候选扫描数、改善日志完全一致；51051000次轮筛等价检查零差异，150000项例外回归零误删。详见 [算法与复现](OPT_WHEEL.md)。不应将此前25.13倍和本次2.48倍直接相乘，两次基准的搜索族与样本不同。

审计修复：各新引擎记录完整扫描形状数、预算和停止原因；不再把限时前开始处理的形状直接视为已完成。通用验证器新增 --pattern，默认核验全部JSONL；空日志明确不代表穷尽，有理系数由专用验证器核验。所有本轮改善记录已独立精确试除并检查绝对值互异。

新运行入口（先按 OPT_WHEEL.md 编译；请使用新输出前缀）：

```powershell
.\tmp\prime-polynomial-build\opt_wheel17_search.exe 3 90 2026092424 missions/prime-polynomials/verification/cubic-wheel17-replay 0 exception 50
python missions/prime-polynomials/scripts/verify_campaign.py
python missions/prime-polynomials/scripts/family_verify_rational_quintic.py
python missions/prime-polynomials/scripts/family_verify_binomial_quintic.py
```

下一步应增加不同的有理整值形状或改变扰动方向，并记录系数高度分层；已穷尽的三组有限族无需仅换种子重跑。当前实验不构成全局上界或最新世界纪录认证。
