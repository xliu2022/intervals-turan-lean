# 谱图形式化检索更新：2026-11-26

## 结论与证据等级

本次继续检索找到了**能实际引入、重新编译并通过传递公理审计的 MGG 谱定理**，来源为 `girving/aks`。本工程已将它接到置换端口、简单二部提升、加法三部超图和精确外层优化，最终得到无参数的 `IntervalsTuran.main_theorem : MainTheoremStatement`。这项结果不依赖找到完整的 LPS 形式化。

原有 138 度 Cayley 接口 `Nonempty Spectral.SmoothSpectralFamily` 仍未被构造。检索没有得到一个已实际核验、可直接提供该特定实例的外部定理；这不是关于所有公开、未公开或未被索引项目的不存在断言。

下表区分“读到实际源码”“本地编译”“核验传递公理”，避免将网页的完成标签或一个名称含 Ramanujan 的定理当成已接入的完整谱图存在证明。

| 来源 | 实际检查 | 在本工程编译／审计 | 对本项目的结果 |
| --- | --- | --- | --- |
| `girving/aks` | MGG 定理、算子定义、功率接口及其 12 模块依赖闭包 | 已移植编译；关键定理与新增适配器已做传递公理审计 | 实际采用，支撑最终无条件路线。 |
| `doxtor6/MerLean_bpqc` | LPS 定义和 Ramanujan 命题的实际源码 | 未导入，未在本环境构建 | 构造基础有实质内容，但七个显式公理及保留的谱假设不能充当完整 LPS 证明。 |
| Prove2Me | 公开页面的形式陈述、状态及公开 API 使用说明 | 未取得提交证明体，未编译或审计 | 页面标为 Proved 的强候选仍是未核验来源；不以页面占位符推断实际证明含有漏洞。 |
| Tobias Weiss / CayleySpec | 作者说明页及其形式公式；尝试获取所指仓库 | 未取得完整源树，未编译 | 所示公式是邻接元素在表示下的像，没有给出定量谱族存在定理。 |
| `propertyH_lean` | 实际有限顶点扩张图存在证明 | 源码检查，未在本环境构建 | 最大度数和顶点扩张界不同于所需精确正则双邻接谱界。 |
| 其他下列谱图项目 | 对应实际声明或源码片段 | 未引入或本地构建 | 用于判断候选的具体范围，未被计入最终证明依赖。 |

最终整库验收现已通过：104 个模块重新编译，3,296 个项目声明（包括保留上游命名空间的 AKS 声明）通过传递公理审计。独立主定理类型检查与源码扫描也已通过。完整状态和统计见 `verification/result.json`。下文还保留实际导入时的定向核验记录；本工程没有据此认证未导入的整个外部仓库。

## 1. 实际采用：girving/aks 的 MGG 谱证明

仓库：[girving/aks](https://github.com/girving/aks)。固定提交：
`c7fb62ed80a4a610f87f34db0082cadbd7c00c9f`。

主要实际源码：

- [AKS/MGG/Spectral.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Spectral.lean)：最终 MGG 谱定理。
- [AKS/Graph/Regular.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Regular.lean)：真实端口旋转图、归一化游走及谱量的定义。
- [AKS/Graph/Square.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Square.lean)：图平方与谱范数幂界。
- [AKS/MGG/Defs.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Defs.lean)：MGG 的实际仿射变换。
- [LICENSE](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/LICENSE)：Apache-2.0，原文已随引入子树保留。

核心声明的实际类型为

```lean
theorem spectralGap_mgg (n : ℕ) (hn : 3 ≤ n) :
    spectralGap (mgg n) ≤ 5 * Real.sqrt 2 / 8
```

这里

```lean
noncomputable def spectralGap {n d : ℕ} (G : RegularGraph n d) : ℝ :=
  ‖G.walkCLM - meanCLM n‖
```

因此它约束实际归一化游走减常数投影的算子范数，而不是仅定义一个 Ramanujan 谓词或在假设相同谱界之后重述结论。证明使用有限二维 Fourier 分析及上游已经证明的估计。它的图对象允许自环和重边，这一点在后续接线中保留。

### 版本、源码对应和实际信任检查

上游使用 Lean `v4.29.0-rc4`，mathlib
`294b7c26a7cac74c34b43ddace82c85ebff331b1`。
本工程固定 Lean `v4.35.0-rc2`，mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`。

移植恰包括 `MGG/Spectral.lean` 和迭代图平方所需的 12 个上游模块，放在 `IntervalsTuran/Vendor/AKS`。保留原声明命名空间；改写导入前缀，添加来源说明，并在 DFT 的八处 `convert` 证明中显式正规化强制转换。将这些已记录改动逆转并统一末尾换行后，12 个文件均匹配原始 Git blob。逐文件 URL、blob 与修改列表保存在 `docs/aks-import.json`。

这 12 个上游模块以及本项目的 `MGG/Adapter.lean` 和独立审计输入 `MGG/Audit.lean` 已在固定环境编译。审计实际检查了

```text
spectralGap_mgg
spectralGap_iterSquare
IntervalsTuran.Spectral.MGG.mgg_hasPermutationPorts
IntervalsTuran.Spectral.MGG.graph_gap_le
IntervalsTuran.Spectral.MGG.portPerm
IntervalsTuran.Spectral.MGG.sum_square_le
```

这些声明的传递公理输出均为

```text
[propext, Classical.choice, Quot.sound]
```

这不是对整个 AKS 仓库的认证；它核验了此次实际引入并使用的依赖闭包及适配结果。许可证与来源归属保留，没有将上游 MGG 谱证明计为本工程新写的证明。

### 本工程的精确适配接口

在命名空间 `IntervalsTuran.Spectral.MGG` 内：

```lean
abbrev portDegree : ℕ := iterSquareDeg 8 4

theorem portDegree_eq_two_pow : portDegree = 2 ^ 48

theorem portDegree_eq_eight_pow : portDegree = 8 ^ 16

def graph (n : ℕ) : RegularGraph (n * n) portDegree :=
  (mgg n).iterSquare 4

noncomputable def portPerm (n : ℕ) (i : Fin portDegree) :
  Equiv.Perm (Fin (n * n))

theorem graph_gap_le (n : ℕ) (hn : 3 ≤ n) :
  spectralGap (graph n) ≤ (1 : ℝ) / 6

theorem sum_square_le (n : ℕ) (hn : 3 ≤ n)
    (f : Fin (n * n) → ℝ) (hf : ∑ v, f v = 0) :
    (∑ v, (∑ i : Fin portDegree, f (portPerm n i v)) ^ 2) ≤
      ((portDegree : ℝ) / 6) ^ 2 * ∑ v, (f v) ^ 2
```

每个原始端口的反向端口与顶点无关，据此证明该端口的邻居映射是置换；平方保持这一性质。四次平方等于 16 步，度数为 8¹⁶，并使用 `(89/100)^16≤1/6` 放宽数值界。最后一条声明给出未归一化有限和的平方界，正好供简单提升使用。

### 为什么能完成原主定理而没有证明 LPS

本工程新增的提升在 K=`GaloisField 2 48` 上以

\[
(v,x,y)\longmapsto(P_i v,x+a,y+i/a),\qquad a\ne0,
\]

定义邻居。两个纤维坐标恢复 a 和 i，因此不同端口不会合并为同一条边；真正的左右正则简单二部核度数为 q(q−1)。有限域计数恒等式和纤维均值分解证明其双邻接范数在单侧零和空间上至多度数的 1/6。单侧阶数为 `(j+3)^2 q^2`，直接具备相邻比趋于一的性质。

随后加法三部 gadget 和新的外层支撑直线证明给出实际有限超图的精确 Lagrangian 序列。最终无需构造 138 度 Cayley 图，也无需将更新版素数定理迁入固定 mathlib。完整模块依赖见 `docs/dependency-map.md`；参数与精确公式见 README。

## 2. MerLean：实质构造代码，但谱结论仍含关键假设

仓库：[doxtor6/MerLean_bpqc](https://github.com/doxtor6/MerLean_bpqc)，检查提交
`6a4a131f7e6385c868240ace87962ae32a2dcf26`。

直接读取的两个文件为：

- [Def_21_LPSExpanderGraphs.lean](https://github.com/doxtor6/MerLean_bpqc/blob/6a4a131f7e6385c868240ace87962ae32a2dcf26/MerLeanBpqc/Definitions/Def_21_LPSExpanderGraphs.lean)，blob `b59c774ead9804b898e78a38f13067518482e361`；
- [Thm_11_LPSRamanujan.lean](https://github.com/doxtor6/MerLean_bpqc/blob/6a4a131f7e6385c868240ace87962ae32a2dcf26/MerLeanBpqc/Theorems/Thm_11_LPSRamanujan.lean)，blob `323ce20cb842a4937442675a50f12570ecdbe547`。

第一份文件包含真正的矩阵、商群、生成元和图定义，也明确声明以下七个公理：

```text
LPS.Sp_card
LPS.lpsGenSetPGL_card
LPS.lpsGenSetPSL_card
LPS.lpsGenSetPGL_generates
LPS.lpsGenSetPSL_generates
LPS.lpsGraphPGL_independent_of_xy
LPS.lpsGraphPSL_independent_of_xy
```

例如 `lpsGenSetPGL_card` 直接把生成元集合大小等于 p+1 声明为 `axiom`。该文件中的相应正则性结果会使用此声明。

第二份文件的最终 PGL 联合定理实际类型为：

```lean
theorem lpsRamanujan_PGL (q : ℕ) [Fact (Nat.Prime q)]
    (p : ℕ) [Fact (Nat.Prime p)] (hpq : p ≠ q)
    (hoddp : p % 2 = 1) (hoddq : q % 2 = 1)
    (hq_gt : (q : ℝ) > 2 * Real.sqrt p)
    (x y : ZMod q) (hxy : x ^ 2 + y ^ 2 + 1 = 0)
    (hconn : (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy).Connected)
    (hram : IsRamanujan (lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy) (p + 1)
      (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt)) :
    let G := lpsGraphPGL q p hpq hoddp hoddq hq_gt x y hxy
    G.Connected ∧
    G.IsRegularOfDegree (p + 1) ∧
    2 ≤ Fintype.card (PGL2 q) ∧
    IsRamanujan G (p + 1) (lpsGraphPGL_card_ge_two q p hpq hoddp hoddq hq_gt)
```

其证明将 `hconn` 与 `hram` 原样放回合取结论。PSL 版本同样保留连通性和 Ramanujan 性假设。

应区分另一个声明 `lpsGraphPGL_lambda2_le`：它以 `hram : IsRamanujan ...` **和** `hspec : |secondLargestEigenvalue ...| < p+1` 为前提，推出第二大特征值至多 `2*sqrt p`；PSL 版本相同。不是某一个最终定理同时接受 `hconn`、`hram`、`hspec` 三个参数，而是这些假设分布于不同声明。

因此，检查到的源码没有提供能替代本项目旧 Cayley 存在义务的完整证明。此判断根据实际公理与定理类型，而非根据文件名；也没有否认这些文件中已有的代数构造。未把该项目加入依赖，未在本环境编译其完整工程。

## 3. Prove2Me：强候选的公开陈述，提交证明体尚未读取

检查到的公开页面包括：

- [exists_high_girth_adjacency_expander](https://prove2.me/theorems/14f84d0e-b540-407b-a1fe-aa0032257ee8)，公开命名为 `OPG37364.exists_high_girth_adjacency_expander`；本次直接访问显示 **Proved**，部分搜索缓存仍显示 Open。
- [exists_high_girth_strict_cut_expander](https://prove2.me/theorems/fe4b7673-1145-453e-8506-2b7f22c532da)，直接访问显示 Proved。
- [exists_high_girth_spectral_expander](https://prove2.me/theorems/1b251773-0536-424f-98fc-88f9451c2250)，检查时显示 Open。
- [lps13Graph_bipartite](https://prove2.me/theorems/5159a1d2-fdcb-4f43-8bb2-557a2247efb3)，检查时显示 Proved。

最强相关页面给出的形式结论为：

```lean
∀ g : ℕ, 3 ≤ g →
  ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
    IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
    HasGirthAtLeast G g ∧
    (∀ μ : ℝ, μ ∈ spectrum ℝ (G.adjMatrix ℝ) → μ ≠ 14 → μ < 12)
```

页面环境为 Lean `4.33.1`、mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`。另一个公开声明是

```lean
theorem lps13Graph_bipartite {q : ℕ} [Fact q.Prime]
    (hq : 13 < q) (i : LPS13Root q)
    (hnr : legendreSym q 13 = -1) :
    IsBipartite (lps13Graph hq i)
```

这些陈述值得继续研究，但本次没有取得并读取相应提交的完整 Lean 证明文件与依赖。公开页面展示的 `by sorry` 是形式任务陈述的占位形式，**不能据此断言被接受的提交证明本身使用了 `sorry`**；同样，Proved 标签也不足以代替本项目要求的实际源码和传递公理审计。

官方 [prove2me_workspace](https://github.com/prove2me/prove2me_workspace) 的 [discover.md](https://github.com/prove2me/prove2me_workspace/blob/main/references/discover.md) 描述通过 Bearer 认证访问 theorem submissions 和 submission solution 的接口。本次没有通过该接口取得证明体，也没有为此创建账号或请求凭据。公开可读的相关仓库及按精确声明名称的搜索，没有提供可直接下载并审计的对应证明文件；这是本次访问范围的限制。

即使上面的存在命题已被完整证明，显示的接口也不直接给出旧度数 138 的 Cayley 条件或光滑阶数序列。它给出的二部谱陈述是一侧上界，允许 −14；这不能直接解释为整个零和邻接空间的绝对范数小于 14。它可能对适当的二部奇异值路线有用，需要额外的谱转化和阶数控制，但本工程最终没有依赖这一未读取的证明。

## 4. 其他候选的实际范围

### Tobias Weiss / CayleySpec

作者的 [Cayley graphs and Hecke operators 页面](https://www.tobias-weiss.org/content/research/lean4-cayley-graphs-hecke-operators/) 指向 [tobias-weiss-ai-xr/CayleySpec](https://github.com/tobias-weiss-ai-xr/CayleySpec)。本次尝试获取仓库和所提发布版本时返回 404，因此没有取得完整源树，也没有本地编译。

页面显示的一个关键公式为

```lean
theorem adjacencyElement_spectral
    (ρ : FDRep ℂ G) [CategoryTheory.Simple ρ] :
    Representation.asAlgebraHom ρ.ρ (adjacencyElement S)
      = ∑ s ∈ S, ρ.ρ s := by
  exact adjacencyElement_rep S ρ.ρ
```

这表示群代数邻接元素在一个表示下的像。公式本身没有断言任何定量谱界或一列满足该界的有限图存在，不能作为所需 LPS 输入。404 只描述本次可访问性，不证明项目从未存在。

### propertyH_lean：真实顶点扩张图存在定理

检查提交 `f26ef6845f23fa016b8a9aeba94e7aae605d73f8` 的
[ExpanderExistence.lean](https://github.com/demendoncabraga/propertyH_lean/blob/f26ef6845f23fa016b8a9aeba94e7aae605d73f8/lean/PropertyH/ExpanderExistence.lean) 和
[Expanders.lean](https://github.com/demendoncabraga/propertyH_lean/blob/f26ef6845f23fa016b8a9aeba94e7aae605d73f8/lean/PropertyH/Expanders.lean)。实际声明 `exists_expander_on` 为任意有限类型 V 给出一个满足 `IsVertexExpander G 64 (1/2)` 的简单图；构造使用有限置换计数，另有在 `Fin (n+5)` 上的图族。

这里的性质是最大度数至多 64 及小集的外邻域至少为其大小的一半，不是精确正则性及指定常数的双邻接算子范数。因此它是有实质内容的扩张图存在结果，但不能直接接到当时的谱接口。此次读了源码，没有在固定环境构建，也未采用。

### 谱展开与谱下界项目

| 仓库与固定源码 | 读取到的具体内容 | 本次判断范围 |
| --- | --- | --- |
| [sjh227/LeanExpanderGraph，91c958c2164df8f04cba93890eaec7d62d6d94a4](https://github.com/sjh227/LeanExpanderGraph/tree/91c958c2164df8f04cba93890eaec7d62d6d94a4) | 谱扩张与顶点扩张的定义、有限小图例子；README 还明确记录未完成证明。 | 检查部分没有提供本项目所需族；未构建。 |
| [jtraverso/expander-spectral，Expanders.lean](https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean) | `expander_mixing_of_two_le_card` 从零和 Rayleigh 界推出混合估计；另有 Alon–Boppana/Nilli 方向结果。 | 一般谱界的后果，不提供本项目所需的谱族存在输入；未构建。 |
| [sneed-and-feed/lean-theorems-3，SpectralBound.lean](https://github.com/sneed-and-feed/lean-theorems-3/blob/85dbbf28ba211d4aee2de08e82092a65d018f71d/Formalization/AlonBoppana/SpectralBound.lean) | 实际文件把 `alon_boppana_bound` 声明为 `axiom`。 | 该具体声明不能作为无自定义公理的依赖；没有对仓库其他所有声明作结论；未构建。 |

### 最初已审计的 mathlib、Godsil–Gutman 和 Bilu–Linial 来源

详细源码版本和限制保留在 `docs/spectral-input-status.md` 的历史部分，包括：

- mathlib `348837d3aa976624060d7c35c183fff587c5a24a` 的 [WeakPNT.lean](https://github.com/leanprover-community/mathlib4/blob/348837d3aa976624060d7c35c183fff587c5a24a/Mathlib/NumberTheory/LSeries/WeakPNT.lean)，有 `Nat.isEquivalent_card_prime_modEq` 及 `Nat.isEquivalent_nth_prime_succ`；固定 mathlib 没有这个新文件，且素数计数定理本身不是 LPS 谱界。
- `karlesmarin/godsil-gutman-lean` 提交 `9614b005907e423a34cf61c4f71411a341ca30ce` 的 [HeilmannLiebBound.lean](https://github.com/karlesmarin/godsil-gutman-lean/blob/9614b005907e423a34cf61c4f71411a341ca30ce/MSS/HeilmannLiebBound.lean) 等，约束匹配多项式并提供二重覆盖矩阵恒等式；检查的声明不直接构造旧 Cayley 族。
- `shengtongz/bilu-linial-opus` 提交 `991a77a002487c48e54f978750dfc8a6b55b8314` 的 [Main.lean](https://github.com/shengtongz/bilu-linial-opus/blob/991a77a002487c48e54f978750dfc8a6b55b8314/BiluLinial/Main.lean)，`near_ramanujan_signing_proof` 的常数和度数阈值由存在量词给出，不能直接提供度数 138 的指定界或阶数平滑性。

这些来源均未在本工程作为证明依赖引入。另对 mathlib PR、Lean 社区讨论和作者页面的检索用于发现候选；索引无命中、旧讨论或一篇作者介绍均不被当作不存在证明，也不替代实际定理类型的检查。

## 5. 本次检索改变了什么

早期问题是“能否关闭指定 `SmoothSpectralFamily` 类型”；这要求特定 Cayley 结构、度数、双边零和谱界和光滑阶数同时成立。后续正面发现是“已有完整可移植的 MGG 算子谱界”。本工程在保留原目标的前提下证明了简单化提升及新的超图估计，从这个已核验起点构造另一列满足递归区间论证要求的有限超图。

因此当前可以同时准确地说：**原论文主定理已有无前提的 Lean 证明；本项目仍未证明特定 LPS/Cayley 存在实例。** 新证明的外部归属、局部改动、实际编译和审计分别记录，没有把一个搜索命中、一个网页完成标签或一个带假设的 Ramanujan 声明当成完整证明。
