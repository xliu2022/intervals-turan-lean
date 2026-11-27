# 弱扩张图路线的独立语义复核

复核日期：2026-11-26。

## 范围与当前结论

本记录检查真实图对象、谱范数的归一化、重边消除、概率权重与原始权重之间的缩放，以及外层图的精确 Lagrangian。它不是只检查文件中是否出现 `sorry`。

已检查以下源码：

- `Spectral/FiberDesingularization.lean`；
- `Spectral/PermutationLift.lean`；
- `Spectral/BipartiteKernel.lean`；
- `Spectral/AdditiveTripartite.lean`、`Spectral/AdditiveGadgetScaling.lean`；
- `Vendor/AKS/MGG/Adapter.lean`；
- `Construction/WeakOuterOptimization.lean`、`Construction/WeakOuterGraph.lean`；
- `Spectral/SimpleExpanderFamily.lean`、`Spectral/KernelRelabel.lean`；
- `Construction/WeakOuterSequence.lean`、`Construction/WeakBaseParameters.lean`；
- `Construction/RecursiveIntervalRealization.lean`、`Construction/CompleteJoinClosure.lean`；
- `Turan/BelowApproximation.lean`、`Turan/RecursiveInterval.lean`、`Turan/TerminalReduction.lean`；
- `MainStatement.lean`、`Main.lean`，以及普通密度定义与 cap 家族桥接的源码。

这些文件中的数学接口和推导相容，未发现度数、重数、谱范数归一化、序列方向或目标定义错误。最终有限域实例、平滑序列、递归区间、升维与末端区间的装配均已纳入本记录。`Main.lean` 已成功编译；独立入口对无条件主定理及其普通密度展开式的检查也已通过。后续全项目验收也已完成：104 个模块重新编译、3,296 个声明的全面传递公理审计及源码扫描均通过，详见 `verification/result.json` 和对应日志。

这条路线更换了论文中使用的谱图构造和固定参数。它的目标是直接完成主定理，并不是构造旧接口中度数为 `138` 的 `SmoothSpectralFamily`，也不应被描述为已经形式化 LPS 的 Ramanujan 定理。

## 1. MGG 输入确实是有标号的置换多重图

`MGG.graph n = (mgg n).iterSquare 4` 保留 `n*n` 个顶点，端口数为

\[
q=8^{16}=2^{48}.
\]

`MGG.portPerm n i` 是实际顶点置换，而不是假设所有端口都互不相同。原图固定端口的逆端口不依赖顶点；这一性质给出双射性，并在四次平方下保留。

`MGG.sum_square_le` 的结论为：对 `n ≥ 3` 和每个满足 `∑v f v = 0` 的实函数，

\[
\sum_v\Bigl(\sum_{i\in\operatorname{Fin}(q)}f(P_i v)\Bigr)^2
\le (q/6)^2\sum_v f(v)^2.
\]

这里左侧是**未归一化**的实际端口邻接算子。证明先使用上游 `spectralGap_mgg`，其中 `spectralGap G = ‖G.walkCLM − meanCLM‖`，再利用四次平方和有理数界 `(89/100)^16 ≤ 1/6`。它控制整个零和子空间的绝对算子范数，并未排除负特征值。没有把此多重图直接当作简单图或 Cayley 图。

上游源码为 `girving/aks` 提交 `c7fb62ed80a4a610f87f34db0082cadbd7c00c9f` 的 [MGG/Spectral.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Spectral.lean) 与 [MGG/Axioms.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Axioms.lean)。本工程的导入与兼容修改另记在 `docs/aks-import.json`。

## 2. 双曲线纤维真正消除了重边

设有限域 `K` 的阶为 `q`，端口以 `i : K` 标号。提升后的顶点为

\[
W=V\times K^2,
\]

其邻点由 `(i,a) ∈ K × Kˣ` 给出：

\[
(v,x,y)\longmapsto(P_i v,x+a,y+i/a).
\]

`PermutationLift.neighbor_injective` 从第二坐标恢复 `a`，再从第三坐标恢复 `i`。因此即使原端口置换重合，邻点集合 `Finset.univ.image ...` 仍恰有

\[
d=q(q-1)
\]

个元素。固定端口的前驱为 `(P_i⁻¹v,x−a,y−i/a)`；前驱标号也单射。因此 `neighbors_card` 与 `incoming_neighbors_card` 分别证明左右两类的度数均为 `d`。这是两个顶点副本之间的简单正则关系，不要求邻接矩阵对称。

### 谱估计中的纤维项

令 `C_i f(x,y)=∑_{a≠0}f(x+a,y+i/a)`。`Fiber.sum_convolution_sq` 证明精确恒等式

\[
\sum_i\|C_i f\|_2^2
=q(q-1)\|f\|_2^2
 +(q-2)\left[\Bigl(\sum_{x,y}f(x,y)\Bigr)^2
 -\sum_x\Bigl(\sum_y f(x,y)\Bigr)^2\right].
\]

它来自有限域差分计数：零差分有 `q(q−1)` 个表示；第一坐标非零的每个差分有 `q−2` 个表示；第一坐标为零而第二坐标非零的差分无表示。对零和 `f`，方括号非正，故得到 `sum_convolution_sq_le`。这里没有使用未证明的字符和或 Weil 界。

`PermutationLift.operator_sq_le` 将任意全局零和函数分解为纤维常值部分和逐纤维零和部分。输入、输出的两部分分别正交，纤维大小 `q²` 的因子均被保留。常值部分的邻接算子为 `(q−1) A_base`；残余部分满足平方范数界 `q²(q−1)`。因此，当原端口界为 `q/6` 且 `q ≥ 37` 时，

\[
\|A_{\rm lift}f\|_2\le d\|f\|_2/6
\quad\text{对所有全局零和 }f.
\]

对应声明为 `kernel_hasZeroSumBound_one_sixth`。残余项所需不等式恰为 `q−1 ≥ 36`，没有遗漏额外的平方根或纤维因子。

## 3. 两个好链接已经足够

对一个实际简单正则二部核 `B`，在三个有限加法群副本上取超边

\[
\{(0,x),(1,y),(2,z)\},\qquad z\in B.\mathrm{neighbors}(x+y).
\]

`B.tripartiteGraph_edge_card` 证明边数为 `d n²`，其中 `n=|V|`；`tripartiteGraph_edgePolynomial` 将普通超边多项式与真实三重求和相等起来。每条超边的三个类标号不同，所以不存在超边内部的顶点重合，也不会因标号表示重复计边。

两个平移链接的误差分别为 `θ B xz` 和 `θ A yz`，其中 `A,B,C` 为非负类质量、`A+B+C=1`，而 `x,y,z` 为中心化二范数。平均后使用

\[
2(Bxz+Ayz)\le x^2+y^2+z^2
\]

得到 `tripartiteGraph_normalizedPolynomial_le`：对所有概率权重 `w`，

\[
6P_H(w)\le\frac{2d}{9n}
+\frac{3\theta}{2}\left(\sum_vw_v^2-\frac1{3n}\right).
\]

三部性独立给出 `λ(H) ≤ 2/9`。均匀权重取得 `2d/(9n)`。缩放模块明确处理零质量切片，再对正质量切片归一化；因此原始权重界不暗含质量非零假设。

在 `d=5k`、`θ=5k/6`、`m=3n` 时，`tripartiteGraph_raw_weak_spectral_le` 的精确结论为

\[
6P_H(x)\le
\frac{10k/3-5k/4}{m}\,t^3
+\frac{5k}{4}\,t\sum_vx_v^2,
\qquad t=\sum_vx_v.
\]

这与外层优化的输入完全一致。

## 4. 外层图优化没有假设优化点存在或唯一

`Construction.weakRawOuter_le` 对 `k ≥ 4`、`m ≥ 48k` 和任意实际概率类质量给出普遍上界。小质量分支使用谱界和 `s_i ≥ w_i²/m`；大质量分支使用三部性和明确的三次多项式证书。两个分支使用同一条支撑直线。此定理不依赖 KKT 条件。

`B.weakOuterGraph k` 是 `k` 个实际三部图的真实 complete join。`weakOuterGraph_lagrangian` 结合精确三次 join 恒等式、上述普遍上界和均匀权重，证明

\[
\lambda(Q)=1-\frac1{k^2}
+\frac{k/3+3}{k^2m}.
\]

其中修正项为正。系数检查为 `2d/3+3−3k = k/3+3`；没有把有限简单 complete join 误写成忽略碰撞项的理想公式。

## 5. 固定有限域、平滑阶数与实际有限图序列

`SimpleExpander.PortField` 是 `GaloisField 2 48`，`card_portField` 从有限域阶数定理得到其阶为 `q=2^48`。`portEquiv` 是该域与 `Fin MGG.portDegree` 的真实等势双射；`base_sum_square_le` 通过该双射重排有限和，没有把端口索引替换成不同的算子。

参数定义为

\[
d=q(q-1),\qquad k=d/5,\qquad N_j=(j+3)^2q^2.
\]

`five_mul_k` 在自然数中证明 `5*k=d`，所以后续没有把有余数的自然数除法当作精确实数除法。`four_le_k`、`order_pos`、`order_large` 分别证明 `k≥4`、`N_j>0`、`48k≤3N_j`；最后一个不等式对所有 `j` 成立，无须未说明地丢弃开头若干项。

提升后的顶点集 `Fin ((j+3)*(j+3)) × K²` 的基数恰为 `N_j`。`vertexEquiv` 将其重标号为 `ZMod N_j`。`KernelRelabel.relabel` 的定义对实际邻点集合取双射像；左右正则性、邻接算子的有限和及零和范数界都通过双射传递。因此加法群结构仅用于三部图中的 `x+y`，没有额外假设原 MGG 图或提升图为 Cayley 图。

`outerSequence j : FiniteGraph 3` 是真实外层图向 `Fin` 顶点集的拉回；`canonicalFiniteGraph_lagrangian` 通过双向嵌入证明其 Lagrangian 不变。精确公式为

\[
\lambda(Q_j)=\alpha+\frac{c}{3N_j},\qquad
\alpha=1-\frac1{k^2},\qquad
c=\frac{k/3+3}{k^2}>0.
\]

`order_strictMono` 与 `order_tendsto` 给出 `N_j` 严格递增并趋于无穷。于是 `baseValue_lt_outerSequence`、`outerSequence_strictAnti`、`outerSequence_tendsto` 分别得到严格位于 `α` 上方、严格递减、收敛到 `α`。相邻差值比的方向也已核对：

\[
\frac{\lambda(Q_j)-\alpha}{\lambda(Q_{j+1})-\alpha}
=\frac{N_{j+1}}{N_j}
=\left(\frac{j+4}{j+3}\right)^2\longrightarrow1.
\]

`exists_smooth_finite_lagrangians` 的完整类型没有任何谱存在性前提。

## 6. 递归入口与真正的普通 Turán 密度目标

`belowLagrangianApprox_weakOuterBase` 使用已经构造的 complete join 极限，将 `0` 的下逼近送到 `α=1−1/k²`。它不使用从上方趋于 `α` 的 `Q_j` 序列来冒充从下方逼近。对 `3k²+2` 个顶点的完全三图，均匀值与 `α` 的差恰为

\[
\frac{8k^2+4}{k^2(3k^2+2)^2}>0.
\]

这给出 `weakOuterBase_lt_cliqueRatioValue` 的真实严格递归间隙。`weakBase_exists_interval_of_smooth_finite_lagrangians` 将上述有限图序列送入已有的递归实现定理。该定理使用实际有限替换图、逐尾值、已证明的最终重叠、有限贪心组合和从下方的对角极限；其左端点也由独立的下逼近定理覆盖，没有假设整个 Turán 谱闭合。

`exists_three_below_lagrangian_interval` 因而无条件产生一个非退化三一致区间。`Turan.TerminalReduction` 先用实际悬挂构造升到任意 `r≥3`，再用完整的 join 下逼近闭包和数值区间覆盖证明得到末端区间。这里的 join 闭包来自有限简单图加克隆的上下界与极限，未把有限图的 join Lagrangian 直接认作忽略顶点碰撞的理想表达式。

最终目标中的定义也已逐项展开：

- `RGraph` 的边是 `Finset (Finset V)`，每条边恰有 `r` 个不同顶点，所以对象是有限简单一致超图。
- `SetFamily.Free` 排除所有禁图的普通嵌入；`RGraph.IsEmbedding` 要求整个顶点映射单射，包括孤立顶点。
- `SetFamily.extremalNumber F n` 是 `n` 顶点普通 `F`-free 图的最大边数；没有可行图时取 `0`。
- `SetFamily.extremalDensity F n` 是该数除以 `n.choose r`。
- `SetFamily.turanDensity F` 以该序列从 `n≥r` 开始的下确界定义，而 `extremalDensity_tendsto` 已证明普通归一化极值序列确实收敛到它。
- `F : Set (FiniteGraph r)` 允许任意禁图族，并未缩成有限禁图族，也未将普通嵌入改为同态避免。

`LagrangianCap` 使用实际族 `F_x={G : x<λ(G)}`。它证明同态自由的有限图给出普通密度下界、普通自由的图给出上界，再将真实有限 Lagrangian 的下逼近极限实现为 `turanDensity F_x=x`。其中的有限子族下确界公式已由固定顶点数的截断直接证明。因而最终目标不是一个仅按 Lagrangian 或递归值重新定义的替代谱。

## 7. 独立入口的内核审计与全项目状态

已在新进程中直接导入纤维模块和缩放模块，对精确差分恒等式、纤维平方范数界、二部混合界、超图边数/多项式恒等式、概率权重界、均匀值以及全部原始权重界执行 `#print axioms`。这些声明只依赖 `propext`、`Classical.choice`、`Quot.sound`。

本轮还检查了 `verification/UnconditionalMain.lean` 与实际输出 `verification/unconditional-main.log`。该独立入口直接导入 `IntervalsTuran.Main`，接受了以下两个没有额外前提的声明：

```lean
IntervalsTuran.main_theorem : IntervalsTuran.MainTheoremStatement

IntervalsTuran.ordinary_density_terminal_interval :
  ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
      ∃ forbidden : Set (IntervalsTuran.FiniteGraph r),
        IntervalsTuran.SetFamily.turanDensity forbidden = x
```

日志对两个声明均报告且仅报告：

```text
[propext, Classical.choice, Quot.sound]
```

因此无条件主定理的这条依赖路径已经通过内核检查；不存在以谱存在性、区间实现或整个结论作前提来关闭该声明的情形。随后完成的全项目重新构建及全面传递公理审计均已通过。审计按声明来源模块以及项目命名空间筛选，覆盖本地私有声明和保留原命名空间的第三方声明；最终共有 3,296 个声明，其中 2,909 个为 theorem 声明（含自动生成项），所有公理依赖均在上述标准三项之内。
