# 谱图输入的独立审计与最终替代路线

更新：2026-11-26。作者与维护者：Xizhi Liu。

## 当前结论

**最终主定理已经不依赖任何未证明的谱图族存在性前提。** `IntervalsTuran.main_theorem : MainTheoremStatement` 及其展开为普通禁止族密度的入口已编译，并已核对类型。最终 104 个模块重新编译、3,296 个声明的全库传递公理审计及源码扫描均已通过；完整统计与记录见 `verification/result.json`。

原有 `Nonempty Spectral.SmoothSpectralFamily` 仍没有在本项目中证明。这只描述保留的 138 度 Cayley 分支，不再描述最终主定理的完成状态。下面保留该分支的精确义务和最初源码审计，供复核当时为何不能宣称完整形式化。

## 实际提供谱输入的已编译证明

本次后续检索找到了并实际移植了 [girving/aks 的 MGG 谱证明](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Spectral.lean)，固定提交为 `c7fb62ed80a4a610f87f34db0082cadbd7c00c9f`，许可证 Apache-2.0。原定理为

```lean
theorem spectralGap_mgg (n : ℕ) (hn : 3 ≤ n) :
    spectralGap (mgg n) ≤ 5 * Real.sqrt 2 / 8
```

其中 `spectralGap G = ‖G.walkCLM - meanCLM n‖`，不是将谱界作为前提的包装定理。其 12 个必需上游模块已移植到 `IntervalsTuran/Vendor/AKS`，在固定 Lean/mathlib 环境编译；原始 Git blob 及局部兼容性修正见 `docs/aks-import.json`。谱定理及适配器的定向传递公理检查均只有 `propext`、`Classical.choice`、`Quot.sound`。

MGG 原对象允许重边，不能直接作为简单超图构造的底图。本工程随后实际证明：

1. 四次平方后的 16 步 MGG 有 q=8¹⁶=2⁴⁸ 个置换端口；端口计数邻接算子在零和空间上范数至多 q/6。
2. 在 K=`GaloisField 2 48` 上，用位移 `(a,i/a)`（a≠0）提升第 i 个置换端口，恢复标签证明没有重边，得到 d=q(q−1) 度的简单左右正则二部核。
3. 对纤维卷积证明精确平方和恒等式，再将函数分成纤维常数部分和纤维均值为零部分，得到双邻接算子在单侧零和空间上的界 d/6。该算子从右侧函数映射到左侧函数；不对整个二部图邻接矩阵宣称这样的全零和界，因为后者包含特征值 −d。
4. 图单侧阶数明确为 Nⱼ=(j+3)²q²，因此平滑性直接由实数极限证明，不需要算术级数中的素数定理。
5. 以 `B(x+y,z)` 定义实际三部三图，使用两个 link 的界，再用外层支撑直线估计证明精确 Lagrangian。k=d/5 时，其值为 `1−1/k² + ((k/3+3)/k²)/(3Nⱼ)`。
6. 这列实际有限超图提供递归区间定理的全部输入，最终接到普通 Turán 密度主定理。

关键模块为 `Spectral/SimpleExpanderFamily.lean`、`Construction/WeakOuterSequence.lean` 和 `Construction/WeakBaseParameters.lean`。主要谱接口实际为

```lean
theorem IntervalsTuran.Spectral.SimpleExpander.kernel_hasZeroSumBound_real
    (j : ℕ) :
    (kernel j).HasZeroSumBound (5 * (k : ℝ) / 6)
```

这里 `kernel j` 是已定义的实际有限二部核，`5*k=d` 已证明，没有要求调用者提供额外谱假设。完整检索范围、MerLean 中的显式公理、Prove2Me 证明体尚未读取的限制，以及其他候选的声明类型，见 `docs/search-update-2026-11-26.md`。

---

以下各节是**旧 Cayley/LPS 分支的审计记录**。这些精确义务仍未在该分支内部闭合，但不再是 `main_theorem` 的依赖。保留这份记录是为了区分“补全特定 LPS 实例”和“用已证明的另一类图完成原主定理”。

## 历史分支：仍未构造的精确 Cayley 类型

需要构造的对象由 `IntervalsTuran/Spectral/Family.lean` 定义。可以把缺失的存在命题直接写成下列 Lean 类型：

```lean
Nonempty IntervalsTuran.Spectral.SmoothSpectralFamily
```

这仍是旧 Cayley 分支尚未证明的目标，不是最终无条件主定理的前提。该结构要求以下全部数据与证明。

| 字段 | 精确内容 |
| --- | --- |
| `graph` | 一列真正的有限 Cayley 图；顶点带有限群结构，生成元是有限集合，不含单位元，并且对取逆封闭。 |
| `valency_eq` | 每张图的生成元个数恰好为 `degree = 138`。 |
| `zeroSum_bound` | 对每个零和实函数 `h`，邻接算子满足 `‖A h‖₂ ≤ (47 / 2) ‖h‖₂`。本项目的二范数定义为平方和的平方根。 |
| `order_strictMono` | 图的顶点数严格递增。 |
| `order_tendsto` | 实数化的顶点数趋向无穷。 |
| `consecutive_ratio_tendsto` | 相邻顶点数之比 `n_(j+1) / n_j` 趋于 `1`。 |

其中邻接算子是实际的有限和

```lean
G.adjacency h u = ∑ s ∈ G.generators, h (u * s)
```

而谱条件的定义是

```lean
∀ h : G.Vertex → ℝ, (∑ u, h u) = 0 →
  G.l2Norm (G.adjacency h) ≤ spectralBound * G.l2Norm h
```

`FiniteCayley.mixing` 已经证明这个算子条件蕴含所需的函数型混合估计，但它以算子条件为假设，不构造满足该条件的图。

几个容易误判的区别会直接影响能否关闭这一目标：

- 仅有 Cayley 图的定义、邻接矩阵的定义或一般谱分解，不能提供指定数值的谱界。
- 允许特征值 `±138` 例外的 Ramanujan 谓词，单独不足以给出上述零和子空间范数界。接入经典 LPS 图时，还需处理连通性及非二部性；`−138` 不能留在零和子空间中。
- 任意大的有限图，或顶点数按倍增增长的覆盖塔，单独不足以给出相邻阶数比趋于 `1`。
- 匹配多项式的根位于 Ramanujan 区间，与某列实际邻接算子具有所需谱界，是不同的结论。

## 历史检索：固定依赖的本地检查

本项目固定使用：

- Lean `v4.35.0-rc2`；
- mathlib 提交 `065356127b1dc0016f66b7283ce0ce2c4055aa55`。

对该 mathlib 树中的 **8,536 个 `.lean` 文件**，检索了词项 `Lubotzky`、`Phillips`、`Sarnak`、`Ramanujan`、`WeakPNT`、`PNT` 与 `expander`。命中的 `Ramanujan` 内容是 Eisenstein 级数导数公式以及 Chudnovsky 型公式，没有命中 LPS 图或所需谱图存在定理。完整检索词、文件数、命中文件及对应行保存在 `docs/spectral-local-search.json`；这些记录支持有限范围内的检索结论，不构成对全部数学库内容的不存在证明。

另外核对了相关文件是否存在：

| 固定 mathlib 中的文件 | 结果 |
| --- | --- |
| `Mathlib/NumberTheory/LSeries/WeakPNT.lean` | 不存在 |
| `Mathlib/NumberTheory/LSeries/WienerIkehara.lean` | 不存在 |
| `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` | 存在 |
| `Mathlib/NumberTheory/Chebyshev.lean` | 存在 |

本项目源码中的 `SmoothSpectralFamily` 使用点，均为结构定义或以 `F : SmoothSpectralFamily` 为参数的下游结果；此次检查没有找到产生该结构实例的证明。

## 历史检索：最初检查的上游源码

以下四项记录最初的源码接口检查。这四组文件没有导入当前工程，也没有在本项目环境复核其整个传递依赖；后续实际导入并编译的 AKS/MGG 不在此历史列表中。后续搜索与移植另见 `docs/search-update-2026-11-26.md`。

### 1. 当前官方 mathlib 的素数分布结果

通过 GitHub 连接器直接读取了官方提交
`348837d3aa976624060d7c35c183fff587c5a24a` 的
[WeakPNT.lean](https://github.com/leanprover-community/mathlib4/blob/348837d3aa976624060d7c35c183fff587c5a24a/Mathlib/NumberTheory/LSeries/WeakPNT.lean)。文件 Git blob 为
`6237ad722409f3040bbf9ee71c30206c14ef40de`。

该源码包含 `Nat.isEquivalent_card_prime_modEq`，即固定互素剩余类中的素数计数渐近式；也包含普通素数的 `Nat.isEquivalent_nth_prime_succ`。这为将来证明适合 LPS 参数的素数序列具有相邻比趋于 `1` 提供了可核查的上游起点。源码没有直接给出本项目的 Cayley 图族。

相同提交的
[lean-toolchain](https://github.com/leanprover-community/mathlib4/blob/348837d3aa976624060d7c35c183fff587c5a24a/lean-toolchain)
为 `v4.37.0-rc1`。因此它不是当前固定环境中已有的可导入证明；接入时还需迁移依赖或升级后重新检查整个工程。源文件把算术级数中的短乘法区间素数结论列为后续方向，因而本项目需要的剩余类相邻素数比结论还应从已给出的计数渐近式正式推导。

本次 GitHub 代码搜索对 `WeakPNT` 返回空结果，但直接取官方文件成功。这一反例也说明：搜索无命中不能被当作某份源码不存在的充分证据。

### 2. 当前官方 mathlib 的图论接口

直接检查了官方
[Cayley.lean](https://github.com/leanprover-community/mathlib4/blob/348837d3aa976624060d7c35c183fff587c5a24a/Mathlib/Combinatorics/SimpleGraph/Cayley.lean)
与
[AdjMatrix.lean](https://github.com/leanprover-community/mathlib4/blob/348837d3aa976624060d7c35c183fff587c5a24a/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean)。前者提供 Cayley 图及其邻接关系的基本 API，后者提供实际邻接矩阵、正则图常向量作用以及游走计数等接口。所检查的声明没有提供固定度数 LPS 图族及其 Ramanujan 界。

官方仓库内对 `Lubotzky`、`Sarnak` 的代码搜索没有返回结果；`Ramanujan` 的命中为上述数论同名结果及参考文献；`LPS` 命中主要是无关的 `Lp` 空间标识符。搜索结果使用的仓库快照与局限已记录在 `docs/spectral-remote-search.json`。

### 3. Godsil–Gutman / Heilmann–Lieb 项目

检查的仓库提交为 `karlesmarin/godsil-gutman-lean` 的
`9614b005907e423a34cf61c4f71411a341ca30ce`。

实际读取的
[RamanujanBound.lean](https://github.com/karlesmarin/godsil-gutman-lean/blob/9614b005907e423a34cf61c4f71411a341ca30ce/RamanujanBound.lean)
定义 `IsRamanujan` 并证明有关数值界的性质；它没有从无假设构造 LPS 图。
[HeilmannLiebBound.lean](https://github.com/karlesmarin/godsil-gutman-lean/blob/9614b005907e423a34cf61c4f71411a341ca30ce/MSS/HeilmannLiebBound.lean)
的 `matchingPoly_bounded` 约束的是匹配多项式。
[TwoLift.lean](https://github.com/karlesmarin/godsil-gutman-lean/blob/9614b005907e423a34cf61c4f71411a341ca30ce/MSS/TwoLift.lean)
的主要结果是二重覆盖对应分块矩阵的特征多项式分解。

这些声明的类型均不能直接给出 `SmoothSpectralFamily`。审计没有以项目 README 中的证明完整性宣传代替实际声明类型检查。

### 4. 另一个图签名搜索命中

还读取了 `shengtongz/bilu-linial-opus` 提交
`991a77a002487c48e54f978750dfc8a6b55b8314` 的
[BiluLinial/Main.lean](https://github.com/shengtongz/bilu-linial-opus/blob/991a77a002487c48e54f978750dfc8a6b55b8314/BiluLinial/Main.lean)。

其 `near_ramanujan_signing_proof` 的结论带有存在量词给出的常数 `C` 与阈值 `d₀`，并在 `d ≥ d₀` 时为给定有限图产生签名。该类型没有给出 `d = 138`、范数界 `47/2`、有限群上的 Cayley 结构，以及所需的平滑阶数序列。因此即使该项目在自身环境中的完整证明经过核验，这个接口也不能直接填补旧 Cayley 接口。本次未将该项目加入依赖。

## 可选的后续工作：补全原 Cayley/LPS 分支

最终主定理已由 MGG 替代路线闭合。若另行要求得到旧 `SmoothSpectralFamily` 实例，或形式化论文的特定 LPS 路线，仍需一个实际的 Lean 构造及证明链，至少包括：

1. 以合适素数参数构造有限群及反演封闭的非单位生成元集合，证明其度数为 `138`；
2. 证明相应邻接算子在整个零和实子空间上满足 `2 * sqrt 137` 的界，并处理这一界所需的连通性与非二部性；
3. 证明足够多的合适素数参数存在，并选出使图阶数严格递增且相邻比趋于 `1` 的序列；
4. 用本项目已经核验的 `2 * sqrt 137 ≤ 47/2` 数值不等式，将以上数据封装为真正的 `SmoothSpectralFamily` 实例；
5. 在工程固定的 Lean/mathlib 环境中编译该实例，并对该分支的存在性定理及其传递公理重新审计。

经典 [Lubotzky–Phillips–Sarnak 论文](https://doi.org/10.1007/BF02126799) 是数学依据；论文引用本身不是 Lean 证明项。另一种方法也可以关闭上述精确类型，但不能省去该类型所规定的谱界、Cayley 结构和阶数平滑性。

本次检查没有得到能直接完成这组特定 LPS 义务的现成、已核验实例。当前工程保留了明确的旧接口与条件推导；最终 `main_theorem` 使用不同的简单二部图序列，已不依赖此接口。这个结论只覆盖已检查的来源，不声称所有公开或非公开项目中都不存在完整 LPS 形式化。
