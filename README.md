# Intervals of hypergraph Turán densities — Lean 4

论文：Xizhi Liu 与 Oleg Pikhurko，[*Intervals of hypergraph Turán densities*](https://arxiv.org/abs/2605.25914)，v1，主定理 1.1。

本工程作者与维护者：Xizhi Liu。许可证：Apache-2.0。工程复用了既有 `TuranUniversality` 基础及 [Geoffrey Irving 的 AKS 项目](https://github.com/girving/aks)中的 MGG 谱证明；原始来源、许可证、逐文件散列及移植范围见下文。

## 当前完成状态

**论文主定理 1.1 已得到没有额外数学前提的 Lean 证明项。** 已编译的主入口为：

```lean
theorem IntervalsTuran.main_theorem :
    IntervalsTuran.MainTheoremStatement
```

其结论是

\[
\forall r\ge3,\quad \exists\delta>0,\quad
[1-\delta,1]\subseteq\Pi_\infty^{(r)}.
\]

更直接展示普通 Turán 密度定义的入口为：

```lean
theorem IntervalsTuran.ordinary_density_terminal_interval :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ forbidden : Set (IntervalsTuran.FiniteGraph r),
          IntervalsTuran.SetFamily.turanDensity forbidden = x
```

这里使用实际有限简单一致超图、全局单射的子图嵌入、任意禁止族，以及按 `Nat.choose n r` 归一化的普通极值数。工程证明该极值密度序列收敛到 `SetFamily.turanDensity`，没有把结论改为同态密度或仅有 Lagrangian 的区间。

证明库的原始核验记录覆盖 104 个模块和 3,296 个声明。主入口及普通密度展开类型通过了独立检查，传递公理限于 `propext`、`Classical.choice`、`Quot.sound`。结果见 [verification/result.json](verification/result.json)。

## Palomar 的独立声明

[Challenge.lean](Challenge.lean) 仅导入 Mathlib，在文件内定义有限一致超图、普通子图嵌入及禁止族，并把极值数写成可实现边数集合在自然数中的上确界。比较的定理是 `IntervalsTuran.terminal_interval_of_turan_density_limits`。它直接断言，对每个端区间中的实数，都存在一个禁止族，其归一化极值数收敛到该实数。Challenge 中的一个 `sorry` 标记待比较的定理。[Solution.lean](Solution.lean) 先证明这个上确界等于库中的极值数，再从无条件主定理取得禁止族，用 `SetFamily.extremalDensity_tendsto` 得到该极限。

比较的声明和允许的公理见 [comparator.json](comparator.json)。作者、文献、代码来源、GPT 参与情况与复核记录见 [formalization.yaml](formalization.yaml)。在装有 `bubblewrap` 的 Linux 环境中，可在 `lake exe cache get` 和 `lake build` 后运行：

```sh
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --config comparator.json
```

同一项检查在 [GitHub Actions](https://github.com/xliu2022/intervals-turan-lean/actions/workflows/verify.yml) 中运行。Palomar 提交时选择项目根目录下的 `comparator.json`。

### 原有谱输入缺口如何关闭

最终证明使用 **MGG 多重图的已形式化谱界、有限域双曲线纤维的简单化提升、只需两个 link 谱界的三部图，以及外层优化的支撑直线估计**。这些步骤构造了主定理真正需要的光滑有限超图序列。

早期路线的 `Nonempty Spectral.SmoothSpectralFamily` 仍未在本工程中证明。它要求度数恰为 138 的有限 Cayley 图族；最终无条件定理不再以它为前提。原有 `main_theorem_of_smooth_spectral_family` 和 `main_theorem_of_spectral_existence` 保留为单独的条件结果。本工程没有宣称已经形式化 LPS 定理，也没有用 MGG 多重图冒充该旧接口的实例。

## 实际无条件证明链

逐段数学证明、精确能量恒等式、支撑直线证书及 Lean 声明对照见 [docs/mgg-route.md](docs/mgg-route.md)。

| 环节 | 主要模块 | 已证明的内容 |
| --- | --- | --- |
| 已有 MGG 谱证明 | `Vendor/AKS/MGG/Spectral.lean`、`Adapter.lean` | 对每个 n≥3，MGG 归一化游走在零和空间上的范数至多 5√2/8；四次平方得到 16 步图、q=8¹⁶=2⁴⁸ 个置换端口和范数至多 1/6。 |
| 简单正则二部图 | `Spectral/FiberDesingularization.lean`、`PermutationLift.lean`、`KernelRelabel.lean` | 以有限域上的位移 `(a,i/a)` 区分端口，得到真实的简单、左右正则二部核，并证明其谱界。 |
| 明确的光滑阶数 | `Spectral/SimpleExpanderFamily.lean` | 单侧阶数 Nⱼ=(j+3)²q²、度数 d=q(q−1)，Nⱼ 严格增加、趋于无穷且 Nⱼ₊₁/Nⱼ→1。 |
| 两个 link 的三部构造 | `Spectral/AdditiveTripartite.lean`、`AdditiveGadgetScaling.lean` | 超边由 `B(x+y,z)` 定义，边数为 dN²；证明归一化及原始切片的加权估计，谱系数为 3θ/2。 |
| 外层真实超图与精确值 | `Construction/WeakOuterOptimization.lean`、`WeakOuterGraph.lean` | 将谱界和粗略三部界分区使用，证明支撑直线估计；k 部 complete join 的均匀取值达到全局上界。 |
| 实际有限 Lagrangian 序列 | `Construction/WeakOuterSequence.lean`、`WeakBaseParameters.lean` | 显式有限图的 Lagrangian 严格递减至 a=1−1/k²，相邻误差比趋于一；另外证明 a 从下方可逼近。 |
| 实际有限替换 | `Spectrum/GraphSubstitution.lean`、`SubstitutionValue.lean`、`SubstitutionApproximation.lean` | 替换图的多项式恒等式、最大值公式、零载体处理，以及从下方有限逼近的保持。 |
| 递归基点与区间 | `Spectrum/Clique*.lean`、`Construction/PerturbedRecursion.lean`、`RecursiveIntervalRealization.lean`、`Analysis/TailOverlap.lean`、`GreedyApproximation.lean` | 紧致比值公式、最小不动点、真实有限递归截断、右扰动斜率、尾区间重叠及有限贪心逼近。 |
| 普通密度实现 | `Density/SetFamilyExtremal.lean`、`Turan/LagrangianCap.lean`、`BelowApproximation.lean` | 若有限 Lagrangian 从下方趋于 x，则实际禁止族 `{F : λ(F)>x}` 的普通 Turán 密度为 x。 |
| 高一致度与终端区间 | `Construction/Lifting.lean`、`CompleteJoin*.lean`、`Turan/TerminalReduction.lean`、`Main.lean` | 真实悬挂提升、complete join 的有限上界与克隆极限、终端区间覆盖及端点一，得到所有 r≥3 的主结论。 |

上述二部图的谱界指**双邻接矩阵，即从右侧函数到左侧函数的邻接算子**在单侧零和空间上的二范数界：`‖Bh‖₂≤(d/6)‖h‖₂`。它不声称整个 2N 阶二部图邻接矩阵在全部零和空间上有此界；后者包含特征值 −d。二部核在两侧使用同一个有限索引类型，关系无需对称。

## 最终构造的参数与精确公式

固定

\[
q=2^{48}=8^{16},\qquad d=q(q-1),\qquad k=d/5,
\qquad N_j=(j+3)^2q^2,\qquad m_j=3N_j.
\]

代码证明 5 整除 d、k≥4，以及 mⱼ≥48k。有限域使用 `GaloisField 2 48`；将其提升顶点重标记到 `ZMod Nⱼ` 仅用于加法三部构造，不额外断言重标记后的核是 Cayley 图。

对实际 k 部外层图 Qⱼ，证明了精确公式

\[
\lambda(Q_j)
= a+\frac{c}{m_j},\qquad
 a=1-\frac1{k^2},\qquad
 c=\frac{k/3+3}{k^2}>0.
\]

其上界来自所有概率向量上的支撑直线估计，下界由均匀向量取得。因此不需要假设最大点唯一、内部最大点存在，或仅将最优值作为接口条件。由此得到

\[
\frac{\lambda(Q_j)-a}{\lambda(Q_{j+1})-a}
=\frac{N_{j+1}}{N_j}\longrightarrow1.
\]

递归完全三图使用参数 `3*k^2`，其顶点类型为 `Fin (3*k^2+2)`。实际均匀 clique 值严格大于 a 的代数证书、a 的从下方逼近，以及全部序列假设均在主入口内由已证明定理提供。这些巨大常数服务于存在性证明，工程没有声称得到实用大小的图或最优终端区间长度。

## 保持逼近方向与普通密度

`BelowLagrangianApprox r x` 要求每一个有限见证满足 `λ(G_n)≤x`。外层序列从 a 的上方收敛，不能用于证明 a 从下方可逼近。工程独立地通过零图的 k 部 complete join 证明 `belowLagrangianApprox_weakOuterBase`。

有限 complete join 满足

\[
\lambda(J_M(G))\le1-\frac{1-\lambda(G)}{M^{r-1}}.
\]

匹配值由真实的克隆图序列在极限中取得：互异克隆标签给出 `samplingFactor(r,q)` 倍的下界，该因子趋于一。工程没有给任意未经克隆的有限图声明这个一般不成立的精确等式。空载体、r=1 和 M=1 在闭包证明中另行处理。

从三一致图到 r 一致图的真实悬挂构造，其缩放常数为

\[
c_r=\frac{27r!}{6r^r},\qquad c_3=1.
\]

最终定理再使用 complete join 放大非退化区间，覆盖某个 `[1−δ,1]`，并通过阈值禁止族得到普通 Turán 密度。

## 保留的历史 Cayley 分支

`Spectral/Family.lean` 与 `Construction/OuterSequence.lean` 等旧模块仍提供固定参数

\[
p=137,\quad D=138,\quad\theta=47/2,\quad k=30
\]

的条件论证。它们从一个实际 `SmoothSpectralFamily` 推出

\[
\lambda(Q_G)=\frac{899}{900}+\frac{1}{540|G|}.
\]

这条分支的存在输入仍未构造；其精确公式和下游推导仍是有效的条件结果。完整检索记录见 `docs/spectral-input-status.md` 和 `docs/search-update-2026-11-26.md`。检索找到了能够实际移植的 MGG 谱证明，进而促成当前替代路线；这与“找到了完整 LPS 证明”是不同的结论。

## 来源与移植范围

- **论文主定理与整体数学目标：** Liu–Pikhurko，arXiv:2605.25914v1，Theorem 1.1。最终工程替换了原谱图输入和相应外层估计，并非逐行翻译论文中的 LPS 证明路线。
- **MGG 形式化：** [girving/aks，提交 c7fb62ed80a4a610f87f34db0082cadbd7c00c9f](https://github.com/girving/aks/tree/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f)，[Apache-2.0](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/LICENSE)。仅引入 MGG 谱定理和迭代平方所需的 12 个源模块，保留原声明命名空间及源文件内容；修改导入路径，另有 DFT 中八处数值强制转换证明兼容性修正。逐文件原始 Git blob、修改范围及重新编译结果见 `docs/aks-import.json`；许可证原文保存在 `IntervalsTuran/Vendor/AKS/LICENSE`。端口置换证明、16 步适配以及后续简单提升和超图论证为本工程新增。
- **既有 TuranUniversality 工程：** 有限超图、普通密度、替换及部分递归分析基础复用 Xizhi Liu 的既有本地项目源码，并在当前环境重新编译。原文件 SHA-256、抽取范围及修改记录见 `docs/reused-foundation.json`、`docs/reused-analysis.json`。这些复用部分没有被描述为本次从零编写的成果。

## 编译与审计

本次交付的实际检查结果：

| 检查 | 结果 |
| --- | --- |
| 全项目重新编译 | 104 个 Lean 模块全部通过；有部分弃用和风格警告，无编译错误。 |
| 全面传递公理审计 | 3,296 个声明通过，其中 2,909 个为 theorem 声明，含自动生成项；同时覆盖保留上游命名空间的 AKS 声明。 |
| 独立目标类型检查 | 无参数主定理及普通 Turán 密度的展开式均通过。 |
| 源码扫描 | 104 个模块源文件、18,730 行通过；没有证明占位符、自定义公理或绕过内核检查的指令。 |
| 源码一致性 | 当前文件集合与 SHA-256 manifest 一致；打包前自动重新核验记录。 |

源码统计包括既有基础、引入的 12 个 AKS 模块及本工程新增证明，不是全部新写代码的数量。

固定环境：

- Lean：`leanprover/lean4:v4.35.0-rc2`；
- mathlib：`065356127b1dc0016f66b7283ce0ce2c4055aa55`；
- 其余传递包提交固定在 `lake-manifest.json`。

常规 Lake 工作流：

```sh
lake exe cache get
lake build
lake env lean verification/UnconditionalMain.lean
lake env lean verification/AxiomAudit.lean
python3 scripts/audit-source.py
```

在本次已有固定依赖缓存的环境中使用：

```sh
scripts/build-local.sh
scripts/lean-local.sh verification/UnconditionalMain.lean
scripts/lean-local.sh verification/AxiomAudit.lean
python3 scripts/audit-source.py
```

`lean-local.sh` 支持 `INTERVALS_TURAN_LEAN_BIN` 与 `INTERVALS_TURAN_PACKAGE_ROOT`，不下载或重新构建外部依赖。常规 Lake 命令用于说明移植工作流；本次没有声称已在一台全新机器上完成联网获取依赖的构建。

最终验收文件：

- `verification/full-build.log`：全项目逐模块构建记录；
- `verification/axiom-audit.log`：项目声明的传递公理审计；
- `verification/unconditional-main.log`：无条件主定理及普通密度展开类型的独立检查；
- `verification/source-scan.log`：源码占位符与禁用构造扫描；
- `verification/source-manifest.json`：交付 Lean 源文件的 SHA-256；
- `verification/result.json`：最终验收状态、构建范围及统计；
- `docs/proof-review.md`、`docs/weak-route-review.md`：普通密度、旧条件链与新无条件路线的语义复核。

验收只允许 `propext`、`Classical.choice`、`Quot.sound`，并检查没有 `sorry`、`admit`、自定义公理、`native_decide` 或绕过内核检查的指令。除审计公理依赖外，还必须检查结论类型：当前 `main_theorem` 没有 `SmoothSpectralFamily` 或任何替代存在性前提。原条件定理的标准公理列表不等于证明了其旧前提，这一区别在历史记录中保留。
