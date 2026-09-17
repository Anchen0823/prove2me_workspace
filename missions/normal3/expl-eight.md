## 目标

三阶正规幻方恰有八个——也就是说，**洛书（Lo Shu）在对称群作用下唯一**：

$$\mathrm{normalParamCount}(5)=8 .$$

这里 $\mathrm{normalParamCount}(e)$ 数的是 $\mathrm{paramSet}(e)$ 中使 $\mathrm{mkMagic3}(e,a,c)$ 正规的参数对 $(a,c)$；正规指九个格子恰好是 $1,\dots,9$ 的一个排列。$e=5$ 时线和为 $15$，正是三阶正规幻方的幻方常数。

由 Mission I 的 `magic_three_param_bij`，可行参数对与三阶幻方一一对应，所以本定理等价于：三阶正规幻方恰有八个，即洛书

$$\begin{pmatrix}4&9&2\\3&5&7\\8&1&6\end{pmatrix}$$

在正方形的对称群 $D_{4}$ 下的八个像。

## 结构：一次归约

本定理不重做搜索，只把 `magic_three_normal_classify` 的结论装配起来。该子定理已经刻画出：可行参数对中，`mkMagic3 5 a c` 正规当且仅当

$$(a,c)\in\{(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)\}.$$

于是 $\mathrm{normalParamSet}\ 5$ 的定义式 filter 选出的正是这八个对，而它们互不相同，故基数为 $8$。

## 形式化要点

* `normalParamSet` 必须先用 `classical` 定义：$`IsNormal`$ 含 `Function.Injective`，没有可判定实例，`filter` 无法构造性地形成——这是把 filter 封装进一个定义模块的原因。
* 归约的双向都逐个展开八个参数对。`ext` 之后先 `rcases` 把配对拆成 $(a,c)$，否则 `rfl` 作用在 `ac.1` 上会失败。
* 成员资格 $(2,4)\in\mathrm{paramSet}\ 5$ 这类事实要用 `norm_num [paramSet, IsParam3]` 判定；`simp` 只会把目标展开成 `range`/`product`/`filter` 的形式而停在那里。
* 最后 `eightPairs.card = 8` 交给 `native_decide`。

## 为什么这个结果值得单独成一个 mission

前两个 mission 做的是**计数**：$M_3(3e)$ 与 $H_3(t)$ 各有多少。计数只告诉你"有多少"，不告诉你"长什么样"。本 mission 把 MacMahon 参数化反过来当**分类工具**用：参数化加一次有限验证，就得到完整的清单而不只是基数。

这也是三阶之所以特殊的地方：$n=4$ 时正规幻方有 $880$ 个（模对称），$n\ge5$ 则没有任何已知分类。洛书唯一性作为组合学中最古老的非平凡分类结果，把它机器验证通过，等于把整条形式化层级从"能数"推进到"能列"。
