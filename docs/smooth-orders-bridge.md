# 平滑阶数的独立辅助结果

`Spectral/SmoothOrders.lean` 与 `Spectral/PrimeParameters.lean` 已在工程固定的
Lean/mathlib 版本下编译；`smooth-orders-axioms.log` 对其中全部 37 个定理作了
独立导入后的公理审计，仅出现 `propext`、`Classical.choice`、`Quot.sound`。

主要桥接定理如下。

* `MultiplicativelyDenseAtTop.nth_ratio_tendsto`：若自然数谓词在每个充分大的
  乘法区间 `(x,(1+ε)x]` 都有元素，则 `Nat.nth` 给出的严格递增枚举满足相邻比趋于一。
* `MultiplicativelyDenseAtTop.exists_sequence_above`：可以同时去掉任意有限初段。
* `polynomial_ratio_tendsto`：若参数趋于无穷且相邻比趋于一，则任意非零实系数
  多项式的取值也满足相邻比趋于一。
* `pslOrder_ratio_tendsto`：将上述结果用于准确的自然数阶数
  `q*(q^2-1)/2`；源码另行证明除法整除性、正性与严格单调性。
* `multiplicativelyDenseAtTop_of_weightedCounting_limit`：正的加权计数渐近常数
  可以推出乘法区间密度。

素数部分实际调用固定 mathlib 中的狄利克雷定理，已经无条件证明互素剩余类中的
素数枚举严格递增且趋于无穷。相邻比极限仍明确要求相应的素数对数权重计数极限；
文件没有把这个输入宣布为已证明的素数定理，也没有引入公理。

这些文件保留为独立的可复用结果。主工程正在采用另外的有限域纤维与 MGG 扩展图
构造，因此不需要将这项尚未接入的算术级数素数定理用作最终证明的输入。
