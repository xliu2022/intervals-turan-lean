# MGG 到普通 Turán 密度末端区间：完整替代证明路线

本文说明当前 Lean 工程实际完成的数学论证，供读者逐段核对公式、对象和定理接口。目标是 Liu–Pikhurko 的 *Intervals of hypergraph Turán densities*（[arXiv:2605.25914v1](https://arxiv.org/abs/2605.25914)）主定理 1.1：对每个整数 $r\ge3$，存在 $\delta>0$，使得所有 $x\in[1-\delta,1]$ 都是某个任意禁止族的普通 $r$ 一致 Turán 密度。

**当前主定理已经无条件装配完成。** `IntervalsTuran.main_theorem` 以及将普通密度定义直接展开的 `IntervalsTuran.ordinary_density_terminal_interval` 均已通过独立检查。下文是一条完成该主定理的替代证明：它保留有限 Lagrangian、递归区间、升维和 complete join 的总体思路，替换谱图输入及配套外层优化。它没有证明原来度数为 138 的 LPS/Cayley 家族接口，也没有声称形式化了 LPS 的 Ramanujan 定理。全文不作数学新颖性主张。

最终整体验收已经通过，包括全项目重新编译、全面传递公理审计、独立目标类型检查和源码一致性核验。完整状态、声明计数和构建范围见 [verification/result.json](../verification/result.json)。

## 1. 约定、来源与最终参数

对非空顶点集上的有限简单 $r$ 一致超图 $G$，Lagrangian 采用归一化

\[
\lambda(G)=\max_{x_v\ge0,\ \sum_vx_v=1}
 r!\sum_{e\in E(G)}\prod_{v\in e}x_v.
\]

工程中的统一定义是把所有概率权重下的归一化多项式取值与 $\{0\}$ 合并后取上确界（supremum）；空载体没有概率权重，其 Lagrangian 按此定义为 $0$。对非空有限载体，这一定义与上面的最大值一致。

记未乘 $r!$ 的边多项式为 $P_G$。对有限类型上的实函数，本文一律使用未归一化的平方范数 $\|f\|_2^2=\sum_v f(v)^2$。归一化游走算子与未归一化邻接和之间的度数因子会明确写出。

MGG 谱界复用 [Geoffrey Irving 的 `girving/aks` 工程](https://github.com/girving/aks)，固定提交为

```text
c7fb62ed80a4a610f87f34db0082cadbd7c00c9f
```

来源采用 Apache-2.0 许可证。本工程引入 MGG 谱定理和图平方所需的 12 个源模块，保留上游声明命名空间，修改本地导入前缀，并在 DFT 文件中作八处强制转换证明的兼容性调整。逐文件原始 Git blob、来源 URL、移植范围及固定工具链见 [aks-import.json](aks-import.json)；许可证原文见 [Vendor/AKS/LICENSE](../IntervalsTuran/Vendor/AKS/LICENSE)。可直接对照上游 [MGG/Spectral.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Spectral.lean)。端口置换适配以及下述有限域提升和超图论证是本工程加入的部分。既有有限超图、替换与部分递归基础的来源另见 [reused-foundation.json](reused-foundation.json) 和 [reused-analysis.json](reused-analysis.json)。

贯穿新路线的固定参数为

\[
q=8^{16}=2^{48},\qquad d=q(q-1),\qquad k=d/5,
\]

\[
N_j=(j+3)^2q^2,\qquad m_j=3N_j,\qquad
a=1-\frac1{k^2},\qquad c=\frac{k/3+3}{k^2}>0.
\]

自然数等式 $5k=d$ 已证明；这里的 $d/5$ 不是忽略余数的形式除法。工程还证明 $k\ge4$ 及每个 $j\ge0$ 都满足 $m_j\ge48k$。这些参数很大，但最终目标只要求存在性，不要求实用大小或最佳区间长度。

## 2. MGG 的归一化谱界与十六步排列端口

上游 MGG 图在 $n^2$ 个顶点上有八个带标号的端口。其算子定义为

\[
\operatorname{spectralGap}(G)
=\|W_G-\mathbb E\|,
\]

其中 $W_G$ 是归一化游走算子，$\mathbb E$ 是常值均值投影。`spectralGap_mgg` 对 $n\ge3$ 给出

\[
\|W_G-\mathbb E\|\le\frac{5\sqrt2}{8}.
\]

这是绝对算子范数的控制，因此在全体零和函数上有效。四次图平方对应长度为 $16$ 的游走；端口数成为 $8^{16}=q$。实际代码用有理数证书

\[
\frac{5\sqrt2}{8}\le\frac{89}{100},\qquad
\left(\frac{89}{100}\right)^{16}\le\frac16
\]

把归一化零和算子范数压到 $1/6$。

还需证明这些端口真是置换。原八个端口的逆端口与顶点无关，所以每个固定端口给出顶点双射；固定长度端口序列对应置换的复合，平方过程保持此性质。因此得到实际排列 $P_i\in\operatorname{Sym}(V)$，而不是假设它们已经存在。不同端口可能给出相同置换，此时仍是带重数的排列多重图。

对未归一化端口算子 $A_0f(v)=\sum_{i=1}^{q}f(P_i v)$，最终接口为

\[
\sum_v f(v)=0
\quad\Longrightarrow\quad
\|A_0f\|_2^2\le(q/6)^2\|f\|_2^2.
\]

| 数学步骤 | Lean 声明 |
| --- | --- |
| MGG 的归一化界 | 上游 `spectralGap_mgg` |
| 迭代平方的谱界 | 上游 `spectralGap_iterSquare` |
| 固定端口双射及平方保持 | `Spectral.MGG.mgg_hasPermutationPorts`、`Spectral.MGG.HasPermutationPorts.iterSquare` |
| $q=2^{48}=8^{16}$ | `Spectral.MGG.portDegree_eq_two_pow`、`portDegree_eq_eight_pow` |
| 实际排列族 | `Spectral.MGG.portPerm` |
| 十六步归一化界 | `Spectral.MGG.graph_gap_le`、`walk_norm_le` |
| 未归一化有限和平方界 | `Spectral.MGG.sum_square_le` |

本表及下文表格中的本地声明通常省略共同前缀 `IntervalsTuran.`。适配源码为 [Adapter.lean](../IntervalsTuran/Vendor/AKS/MGG/Adapter.lean)。

## 3. 有限域双曲线纤维的精确能量恒等式

取任意阶为 $q$ 的有限域 $K$。对 $i\in K$，定义

\[
B_i=\{(a,i/a):a\in K\setminus\{0\}\},\qquad
(C_if)(x,y)=\sum_{a\ne0}f(x+a,y+i/a).
\]

关键是对所有 $i,a,b$ 作精确差分计数。若 $a=b\ne0$，位移差为零，共有 $q(q-1)$ 个表示。若第一坐标差 $u=a-b\ne0$，则有 $q-2$ 对非零 $a,b$ 满足该差；且

\[
i/a-i/b=i(a^{-1}-b^{-1})
\]

随 $i\in K$ 双射地遍历 $K$。所以每个第一坐标非零的差分恰有 $q-2$ 个表示。第一坐标为零而第二坐标非零的差分没有表示。

展开平方、按差分重新求和，得到精确恒等式

\[
\boxed{
\sum_{i\in K}\|C_if\|_2^2
=q(q-1)\|f\|_2^2
 +(q-2)\left[
  \left(\sum_{x,y}f(x,y)\right)^2
  -\sum_x\left(\sum_y f(x,y)\right)^2
 \right].}
\]

对零和 $f$，方括号非正，而 $q\ge2$，故

\[
\sum_i\|C_if\|_2^2\le q(q-1)\|f\|_2^2.
\]

这一步只用有限域代数、有限求和和平方非负，不依赖字符和估计。另一个以后要用的精确恒等式是

\[
\sum_{x,y}(C_if)(x,y)=(q-1)\sum_{x,y}f(x,y),
\]

它保证每个卷积保持零和纤维。

对应 [FiberDesingularization.lean](../IntervalsTuran/Spectral/FiberDesingularization.lean) 中的 `Spectral.Fiber.sum_shift_differences`、`sum_convolution_sq`、`sum_convolution_sq_le` 和 `sum_convolution_eq`。

## 4. 简单正则二部提升及算子的均值分解

将排列端口用 $K$ 标号，在

\[
W=V\times K^2
\]

的两个副本之间定义关系

\[
(v,x,y)\sim(P_i v,x+a,y+i/a),
\qquad i\in K,\quad a\ne0.
\]

**这里使用的算子是双邻接算子：它将右侧副本上的函数送到左侧副本上的函数。** 两侧共用同一个索引类型，关系不要求对称。下文的零和范数界是这一单侧到单侧映射的界；它不是整个 $2|W|\times2|W|$ 二部邻接矩阵在全体零和空间上的界，后者还有由两个常值副本之差产生的特征值 $-d$。

### 4.1 简单性与左右正则性

固定起点后，终点第二坐标恢复 $a$，再由第三坐标恢复 $i$。因此 $(i,a)$ 到邻点的映射单射，即使某些 $P_i$ 重合也没有重边。左侧度数恰为

\[
d=q(q-1).
\]

对固定终点，前驱写成

\[
(P_i^{-1}v,x-a,y-i/a).
\]

同样的坐标恢复证明前驱标号单射，所以右侧度数也是 $d$。Lean 中邻点是实际 `Finset` 的像，基数定理不是多重度数的计数替代。

### 4.2 均值部分和零纤维和部分

给定全局零和函数 $F:W\to\mathbb R$，写

\[
\overline F(v)=q^{-2}\sum_{x,y}F(v,x,y),\qquad
R(v,x,y)=F(v,x,y)-\overline F(v).
\]

于是 $\sum_v\overline F(v)=0$，且每条纤维都满足 $\sum_{x,y}R(v,x,y)=0$。两部分正交：

\[
\|F\|_2^2=q^2\|\overline F\|_2^2+\|R\|_2^2.
\]

设提升的双邻接算子为 $A$。常值纤维部分满足

\[
A\overline F(v,x,y)=(q-1)A_0\overline F(v).
\]

对零纤维和部分，先对端口 $i$ 使用 Cauchy–Schwarz，再对 $v$ 求和并用 $P_i$ 重排，最后逐纤维应用上一节的能量界，得到

\[
\|AR\|_2^2\le q^2(q-1)\|R\|_2^2.
\]

输出的残余部分仍逐纤维零和，因而输出也具有同样的正交分解。因此，如果基础排列算子的零和范数界为 $\theta$，则提升的平方界可以取

\[
\max\{(q-1)^2\theta^2,\ q^2(q-1)\}.
\]

代入 $\theta=q/6$。第一项等于 $(d/6)^2$；第二项不超过它当且仅当 $q-1\ge36$。所以 $q\ge37$ 时，真实简单核满足

\[
\|AF\|_2\le\frac d6\|F\|_2
\quad(\sum F=0).
\]

| 数学步骤 | Lean 声明，命名空间 `Spectral.PermutationLift` |
| --- | --- |
| 邻点与前驱索引单射 | `neighbor_injective`、`predecessor_injective` |
| 双侧度数 | `neighbors_card`、`incoming_neighbors_card` |
| 实际邻点和等于卷积算子 | `sum_neighbors_eq_operator` |
| 输入正交分解 | `sum_sq_decomposition` |
| 零纤维和部分的界 | `operator_sq_le_of_fiber_sum_zero` |
| 输出正交分解 | `operator_sum_sq_decomposition` |
| 一般平方界 | `operator_sq_le` |
| 实际二部核与最终 $1/6$ 界 | `kernel`、`kernel_hasZeroSumBound_one_sixth` |

源码为 [PermutationLift.lean](../IntervalsTuran/Spectral/PermutationLift.lean)，二部核定义见 [BipartiteKernel.lean](../IntervalsTuran/Spectral/BipartiteKernel.lean)。

## 5. 固定有限域给出无条件的平滑阶数图族

现在取 `GaloisField 2 48`，其基数由 mathlib 的有限域定理证明为 $q=2^{48}$。用真实等势双射把域元素对应到 `Fin MGG.portDegree`，再取 $n=j+3$ 的 MGG 排列族。提升的单侧顶点集为

\[
\operatorname{Fin}((j+3)^2)\times K^2,
\]

基数恰为 $N_j=(j+3)^2q^2$。为了接入加法构造，使用顶点等价将真实邻点集合转移到 `ZMod N_j`；重标号保持双侧正则度数和双邻接范数。此步骤不声称所得核是 Cayley 图。

于是得到实际核 $B_j$，对每个 $j\ge0$ 有

\[
\deg(B_j)=d=5k,\qquad
\|B_jf\|_2\le\frac{5k}{6}\|f\|_2\quad(\sum f=0).
\]

阶数严格递增、趋于无穷，并且

\[
\frac{N_{j+1}}{N_j}=\left(\frac{j+4}{j+3}\right)^2\longrightarrow1.
\]

不需要为该极限引入素数分布假设，也没有遗漏有限初段：$48k\le3N_j$ 对所有 $j$ 成立。

| 对象或性质 | Lean 声明 |
| --- | --- |
| 重标号保持范数 | `Spectral.BipartiteKernel.hasZeroSumBound_relabel` |
| 固定有限域及其基数 | `Spectral.SimpleExpander.PortField`、`card_portField` |
| 实际二部核族 | `Spectral.SimpleExpander.kernel` |
| 度数和双邻接界 | `Spectral.SimpleExpander.kernel_valency`、`kernel_hasZeroSumBound_real` |
| $k\ge4$、$48k\le3N_j$ | `Spectral.SimpleExpander.four_le_k`、`order_large` |
| 阶数性质 | `Spectral.SimpleExpander.order_strictMono`、`order_tendsto`、`order_ratio_tendsto` |

对应源码为 [KernelRelabel.lean](../IntervalsTuran/Spectral/KernelRelabel.lean) 和 [SimpleExpanderFamily.lean](../IntervalsTuran/Spectral/SimpleExpanderFamily.lean)。

## 6. 加法三部构造：两个 link 的界已足够

设 $B$ 是定义在有限加法群 $U$ 上的上述简单正则二部核，$|U|=N$，度数为 $d$，双邻接零和界为 $\theta$。在三个有不同类标号的 $U$ 副本上定义三一致超图 $H_B$：

\[
\{(0,x),(1,y),(2,z)\}\in E(H_B)
\quad\Longleftrightarrow\quad z\in B.\operatorname{neighbors}(x+y).
\]

不同类标号保证每条超边含三个不同顶点；边索引映射单射。实际顶点数是 $3N$，实际边数是 $dN^2$。

固定 $x$ 或固定 $y$ 时，相应 link 是 $B$ 的平移重标号，均可使用双邻接混合界。固定 $z$ 的第三种 link 不需要另行证明同样的谱性质。

给三类非负权重的总质量分别记为 $A,B,C$，$A+B+C=1$；把各类函数中心化后的二范数记为 $X,Y,Z$。两个 link 估计的误差分别受 $\theta B XZ$、$\theta A YZ$ 控制。取二者平均，再利用

\[
2(BXZ+AYZ)\le X^2+Y^2+Z^2
\]

以及类质量的平方和下界，得到对所有概率权重 $w$ 的估计

\[
\boxed{
6P_{H_B}(w)\le
\frac{2d}{9N}+\frac{3\theta}{2}
\left(\sum_vw_v^2-\frac1{3N}\right).}
\]

均匀权重取得常数项 $2d/(9N)$。此外，单凭三部性就有粗界 $6P_{H_B}(w)\le2/9$。

外层优化使用任意质量 $t=\sum_vx_v$ 的非负切片。对 $t>0$ 归一化后乘回 $t^3$，并独立处理 $t=0$，得到两个原始权重界。代入 $d=5k$、$\theta=5k/6$、$m=3N$ 后为

\[
6P_{H_B}(x)\le\frac29t^3,
\]

\[
6P_{H_B}(x)\le
\frac{10k/3-5k/4}{m}\,t^3+
\frac{5k}{4}\,t\sum_vx_v^2.
\]

谱系数确为 $3\theta/2=5k/4$。这一数值是下一步支撑直线证书的输入。

主要声明位于命名空间 `Spectral.BipartiteKernel`：`tripartiteGraph_edge_card`、`tripartiteGraph_edgePolynomial`、`tripartiteGraph_normalizedPolynomial_le`、`tripartiteGraph_uniform_evaluation`、`tripartiteGraph_lagrangian_le`、`tripartiteGraph_raw_weak_spectral_le`。源码为 [AdditiveTripartite.lean](../IntervalsTuran/Spectral/AdditiveTripartite.lean) 和 [AdditiveGadgetScaling.lean](../IntervalsTuran/Spectral/AdditiveGadgetScaling.lean)。

## 7. 外层支撑直线与精确 Lagrangian

取 $k$ 个 $H_B$ 的副本作真实 complete join，得到 $Q_B$。对任意概率向量，把第 $i$ 个部分的质量、平方和与内部归一化多项式记为

\[
w_i=\sum_vx_{i,v},\qquad s_i=\sum_vx_{i,v}^2,
\qquad p_i=6P_{H_B}(x_{i,\cdot}).
\]

实际有限简单图的三次恒等式给出

\[
6P_{Q_B}(x)=
1-\sum_iw_i^3-3\sum_i(1-w_i)s_i+\sum_ip_i.
\]

碰撞修正项 $-3\sum_i(1-w_i)s_i$ 被保留。每部分满足

\[
s_i\ge w_i^2/m,
\qquad p_i\le\frac29w_i^3,
\qquad
p_i\le\frac{10k/3-5k/4}{m}w_i^3+\frac{5k}{4}w_i s_i.
\]

令

\[
A=1-\frac{10k/3+3}{m},\qquad
L(w)=A\left(\frac{3w}{k^2}-\frac2{k^3}\right)
 +\frac3m\left(\frac{2w}{k}-\frac1{k^2}\right).
\]

在 $k\ge4,m\ge48k$ 下，代码证明每个部分的逐点不等式

\[
L(w)\le w^3+3(1-w)s-p.
\]

证明分成两个明确的代数区域。

* 若 $(5k/4+3)w-3\le0$，使用谱界，并利用该系数的符号将 $s\ge w^2/m$ 代入。随后使用 $w^3$、$w^2$ 在 $w=1/k$ 处的支撑直线。
* 若该系数为正，由 $k\ge4$ 推出 $kw\ge3/2$。此时用三部粗界，并将 $m\ge48k$ 化为 $3k/m\le1/16$。所需三次证书是
  \[
  (3x-2)+(2x-1)/16\le(7/9)x^3\quad(x\ge3/2).
  \]

因此该上界对所有概率向量成立，不要求事先知道极大点的位置、存在内部驻点或极大点唯一。对 $L(w_i)$ 求和，仅使用 $\sum_iw_i=1$，便得到

\[
6P_{Q_B}(x)\le
1-\frac1{k^2}+\frac{k/3+3}{k^2m}.
\]

所有外层部分等质量、所有部分内部取均匀权重时达到同一值，从而得到精确最大值

\[
\boxed{\lambda(Q_B)=1-\frac1{k^2}+\frac{k/3+3}{k^2m}.}
\]

| 数学步骤 | Lean 声明 |
| --- | --- |
| 支撑直线与三次证书 | `Construction.cube_support`、`square_support`、`large_mass_certificate` |
| 两个区域的统一逐点界 | `Construction.raw_part_ge_support` |
| 对任意外层权重的普遍上界 | `Construction.weakRawOuter_le` |
| 实际外层图 | `Spectral.BipartiteKernel.weakOuterGraph` |
| 均匀权重取值 | `Spectral.BipartiteKernel.weakOuterGraph_uniform_evaluation` |
| 精确 Lagrangian | `Spectral.BipartiteKernel.weakOuterGraph_lagrangian` |

对应源码为 [WeakOuterOptimization.lean](../IntervalsTuran/Construction/WeakOuterOptimization.lean) 和 [WeakOuterGraph.lean](../IntervalsTuran/Construction/WeakOuterGraph.lean)。

## 8. 真正的有限图序列及逼近方向

将上一节应用于实际 $B_j$，并重标号成 `FiniteGraph 3`，得到 $Q_j$。其值满足

\[
\boxed{
\lambda(Q_j)=1-\frac1{k^2}
 +\frac{(k/3+3)/k^2}{3N_j}
 =a+\frac{c}{3N_j}.}
\]

因此 $\lambda(Q_j)>a$，序列严格递减到 $a$，且

\[
\frac{\lambda(Q_j)-a}{\lambda(Q_{j+1})-a}
=\frac{N_{j+1}}{N_j}\longrightarrow1.
\]

这不是给未知图假设精确最优值：$Q_j$ 是已经定义的真实有限简单三图，精确式来自全局上界与实际均匀取值。相关声明为 `Spectral.SimpleExpander.outerSequence`、`outerSequence_lagrangian`、`outerSequence_strictAnti`、`outerSequence_tendsto`、`outerSequence_gap_ratio_tendsto` 和 `exists_smooth_finite_lagrangians`，见 [WeakOuterSequence.lean](../IntervalsTuran/Construction/WeakOuterSequence.lean)。

这里必须区分两种方向。上述序列从 $a$ 的上方趋近，并不能证明 $a$ 从有限 Lagrangian 的下方可逼近。工程另外证明

\[
\operatorname{BelowLagrangianApprox}(3,a),
\]

即存在实际有限见证，其每项 Lagrangian 都不超过 $a$ 并趋于 $a$。这一点由零系数的 $k$ 部 complete join 闭包获得，声明为 `Construction.belowLagrangianApprox_weakOuterBase`。

## 9. 递归替换、扰动斜率和尾区间重叠

选完全三图参数 $M=3k^2$，其顶点数为 $M+2$。`Construction.weakOuterBase_lt_clique_uniform` 给出真实均匀 clique 值严格大于 $a$ 的代数证书。由此得到递归基点

\[
\mu=\operatorname{cliqueRatioValue}(M,a)>a.
\]

递归一步的函数是概率单纯形上的真实最大值

\[
\psi_b(t)=\max_z\bigl(g_M(z)+tz_0^3+bz_1^3\bigr),
\]

其中 $g_M$ 是完全三图的归一化边多项式。工程证明最大值存在、关于各参数单调、关于 $t$ 为 1-Lipschitz，且 $\mu$ 是 $\psi_a$ 的最小非负不动点。有限替换图的多项式恒等式和最大值公式把有限递归截断连接到真实有限超图；无限递归值通过单调有界截断定义，并证明尾递推方程。

取 $b_n=\lambda(Q_n)$，误差 $\varepsilon_n=b_n-a>0$。在基点目标的极大点中再最大化第二递归坐标，得到一个两递归坐标均为正的极大点。为避免与有限域阶数 $q$ 混淆，记

\[
\eta=z_0^3>0,\qquad R=z_1^3>0.
\]

紧致最大值的右扰动定理给出

\[
\psi_{a+\varepsilon}(\mu)-\mu
=R\varepsilon+o(\varepsilon).
\]

对尾值超出 $\mu$ 的差 $\Delta_n\ge0$，在同一实际极大点求值则给出

\[
\Delta_n\ge\eta\Delta_{n+1}+R\varepsilon_n.
\]

连续使用两次，有

\[
\Delta_{n+1}\ge R(\varepsilon_{n+1}+\eta\varepsilon_{n+2}).
\]

由相邻误差比趋于一，右侧除以 $\varepsilon_n$ 趋于 $R(1+\eta)>R$；而单步基点增量除以 $\varepsilon_n$ 趋于 $R$。所以充分深的尾部满足所需重叠不等式。这个论证不需要没有依据的全局严格压缩率。

尾区间重叠与有限贪心截断给出一个非退化区间 $[\mu,v]$，其中每一点均可从下方由实际有限 Lagrangian 逼近。关键声明对应如下。

| 环节 | Lean 声明或模块 |
| --- | --- |
| 实际有限替换及从下方逼近保持 | `Spectrum/GraphSubstitution.lean`、`SubstitutionValue.lean`、`SubstitutionApproximation.lean` |
| 递归一步、紧致比值与最小不动点 | `Spectrum/CliqueStep.lean`、`CliqueRatio.lean`、`CliqueFixedPoint.lean` |
| 非退化极大点 | `Spectrum.exists_nondegenerate_base_maximizer` |
| 右扰动斜率与递推下界 | `Spectrum.cliqueStep_right_slope`、`cliqueStep_lower_from_base_maximizer` |
| 两步放大的尾区间重叠 | `Analysis/TailOverlap.lean` |
| 有限截断与贪心逼近 | `Analysis/RecursiveValues.lean`、`GreedyApproximation.lean`、`Turan/RecursiveInterval.lean` |
| 平滑有限图序列推出区间 | `Spectrum.exists_interval_of_smooth_finite_lagrangians` |
| 新参数的具体装配 | `Construction.weakBase_exists_interval_of_smooth_finite_lagrangians` |
| 无额外前提的三一致区间 | `IntervalsTuran.exists_three_below_lagrangian_interval` |

具体参数桥接见 [WeakBaseParameters.lean](../IntervalsTuran/Construction/WeakBaseParameters.lean)，递归装配见 [RecursiveIntervalRealization.lean](../IntervalsTuran/Construction/RecursiveIntervalRealization.lean)。

## 10. 从有限 Lagrangian 到普通密度，并得到所有一致度的末端区间

### 10.1 普通 Turán 密度的实现

工程的禁止族是 `Set (FiniteGraph r)`，允许无限禁止族。自由性使用全局单射的普通超图嵌入；极值密度按 $\binom nr$ 归一化。`SetFamily.extremalDensity_tendsto` 证明该实际极值序列收敛到 `SetFamily.turanDensity`。

对一个从下方可逼近的系数 $x$，使用实际阈值禁止族

\[
\mathcal F_x=\{F:\lambda(F)>x\}.
\]

`LagrangianCap` 与下逼近接口证明其普通 Turán 密度恰为 $x$。因此区间结论最终落在普通密度谱上，没有把目标改定义为递归值集合或 Lagrangian 极限集合。相关源码为 [SetFamilyExtremal.lean](../IntervalsTuran/Density/SetFamilyExtremal.lean)、[LagrangianCap.lean](../IntervalsTuran/Turan/LagrangianCap.lean) 和 [BelowApproximation.lean](../IntervalsTuran/Turan/BelowApproximation.lean)。

### 10.2 真实悬挂提升到 $r\ge3$

有限三图的实际悬挂构造把 Lagrangian 按正数

\[
c_r=\frac{27r!}{6r^r},\qquad c_3=1
\]

缩放，并保持从下方逼近。于是三一致非退化区间给出每个 $r\ge3$ 的非退化区间。对应声明为 `RGraph.lagrangian_suspension`、`finiteSuspension_lagrangian`、`BelowLagrangianApprox.lift`，见 [Lifting.lean](../IntervalsTuran/Construction/Lifting.lean)。

### 10.3 Complete join 闭包与末端覆盖

从下方可逼近系数集在变换

\[
J_M(x)=1-\frac{1-x}{M^{r-1}}
\]

下封闭。实现该闭包时，实际有限 complete join 给出上界；匹配下界通过克隆图序列达到，互异克隆标签的采样因子趋于一。不能直接给任意有限图宣称一个忽略碰撞的精确 join 等式，工程也没有这样做。对应声明为 `BelowLagrangianApprox.completeJoin`，见 [CompleteJoinClosure.lean](../IntervalsTuran/Construction/CompleteJoinClosure.lean)。

对一个非退化区间反复应用 $J_M$，充分大的相邻 $M$ 所给出的区间重叠，并向 1 聚集；端点 1 也单独有下逼近见证。`terminalIntervalClaim_of_join_preserves_below` 因而给出一个完整末端区间。升维与闭包的总接口是 `mainTheoremStatement_of_three_interval_and_join_preserves_below`，见 [TerminalReduction.lean](../IntervalsTuran/Turan/TerminalReduction.lean)。

## 11. 最终定理的精确类型和验收边界

最终 [Main.lean](../IntervalsTuran/Main.lean) 直接使用本说明的具体平滑有限图序列，不接受谱图存在性参数：

```lean
theorem IntervalsTuran.main_theorem :
    IntervalsTuran.MainTheoremStatement

theorem IntervalsTuran.ordinary_density_terminal_interval :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ forbidden : Set (IntervalsTuran.FiniteGraph r),
          IntervalsTuran.SetFamily.turanDensity forbidden = x
```

这两个无条件类型已经由独立入口检查，传递依赖公理仅为 `propext`、`Classical.choice`、`Quot.sound`。当前不存在为了装配主定理而留给读者证明的 MGG 谱假设、平滑阶数假设或递归区间假设。原 `SmoothSpectralFamily` 接口仍是另一条保留的条件分支，未被这个不同的构造实例化。

验收需要同时看结论类型、实际对象语义以及内核依赖，单独一个标准公理列表不能把条件定理变成无条件定理。本文数学路线的独立语义复核见 [weak-route-review.md](weak-route-review.md)；最终验收应核对以下记录：

* [verification/unconditional-main.log](../verification/unconditional-main.log)：无条件主入口及普通密度展开类型；
* [verification/axiom-audit.log](../verification/axiom-audit.log)：包括移植第三方声明的传递公理审计；
* [verification/full-build.log](../verification/full-build.log)：全部模块重新编译；
* [verification/source-scan.log](../verification/source-scan.log)：占位符、额外公理和禁用构造扫描；
* [verification/source-manifest.json](../verification/source-manifest.json)：交付 Lean 源码散列；
* [verification/result.json](../verification/result.json)：上述验收的最终状态和统计。

证明源码在撰写本说明时已冻结；本文只解释已实现的论证，没有加入新的数学前提或修改 Lean 证明声明。
