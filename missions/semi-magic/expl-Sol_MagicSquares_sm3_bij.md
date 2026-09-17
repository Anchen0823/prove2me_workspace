## 目标

把半幻方的个数与规范化系数向量的个数等同起来：

$$H_{3}(t)=\mathrm{semiMagicCount}\ 3\ t=\mathrm{sm3Count}\ t .$$

一边是 $3\times3$、元素落在 $\mathrm{Fin}(t+1)$、行列和都为 $t$ 的方阵；另一边是六个非负整数 $(u,v,w,x,y,z)$、和为 $t$、且 $\min(x,y,z)=0$。两者都是有限集，本定理给出它们之间的**双射**。

## 结构：这是一次归约

本证明不重做分解本身，而是 `import` 已经证好的子定理

```
import Theorems.Thm_MagicSquares_sm3_canonical
```

`sm3_canonical` 提供两件事：每个半幻方都存在规范化表示，且该表示唯一。本定理只负责把这两件事翻译成一次 `Finset.card_bij`。

## 正向映射

给定规范化向量 $p$，映到方阵

$$M_{ij}=\bigl(\mathrm{sm3Of}\ p\bigr)_{ij}.$$

这里有两处需要显式处理：

* **元素必须落在 $\mathrm{Fin}(t+1)$.** $\mathrm{sm3Of}$ 的每个元素是两个系数之和，例如 $M_{00}=u+x$；由六个系数总和为 $t$ 知它 $\le t$，故可读作 $\mathrm{Fin}(t+1)$ 中的元素。这就是 `sm3Of_le_sum`。
* **像确实是半幻方.** `sm3Of` 的六条线和都等于系数和，而系数和正是 $t$。

## 单射

若两个规范化向量给出同一个方阵，把等式取到 $\mathbb{N}$ 上得到两个 $\mathrm{sm3Of}$ 表示相等。对其中一个调用 `sm3_canonical` 得到典范的 $(u,v,w,x,y,z)$；它的唯一性条款说：**任何**规范化表示都等于这个典范表示。于是两个向量都等于同一个典范向量，故相等。

注意这里用的是"唯一性"而不是"存在性"——存在性只给出某个表示，唯一性才把任意表示钉死到典范表示上。

## 满射

给定半幻方 $M$（元素是 $\mathrm{Fin}(t+1)$），先把它读作 $\mathbb{N}$ 上的方阵再调用 `sm3_canonical`，得到 $(u,v,w,x,y,z)$。需要：

* **系数落在 $\mathrm{Fin}(t+1)$.** 由 $u+v+w+x+y+z=t$，每个系数都 $\le t$。
* **该向量属于 $\mathrm{sm3Params}\ t$.** 和为 $t$，且 $\min(x,y,z)=0$ 正是 `sm3_canonical` 给出的规范化条件。
* **正向映射回到原方阵.** $\mathrm{Fin}(t+1)$ 两元素相等当且仅当它们的自然数值相等，而后者正是 `sm3_canonical` 给的分量等式。

## 形式化要点

* 用 `Finset.card_bij` 而不是 `card_bij'`：满射方向由 `sm3_canonical` 的存在性直接给出原像，不必先定义一个反向函数再验证左右逆。
* 方阵类型在两边不同——一边是 `Square 3 (Fin (t+1))`，另一边取到 $\mathbb{N}$ 后才是 `Square 3 ℕ`。所有跨越都显式用 `congrArg (fun x : Fin (t+1) => (x : ℕ))` 取自然数值，再由 `omega` 完成算术。
* `ext i j` 对 `Square` 会一路展开到自然数值相等，因此其后**不需要**再 `apply Fin.ext`（加上会报类型不匹配）。
