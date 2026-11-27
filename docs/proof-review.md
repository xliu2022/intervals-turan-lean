# Independent proof review

Updated: 2026-11-26. Environment: Lean `v4.35.0-rc2`, mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Current result: the main theorem is unconditional

The current `Main.lean` contains the compiled declaration

```lean
theorem IntervalsTuran.main_theorem : IntervalsTuran.MainTheoremStatement
```

It has no spectral-family, interval-realization, or join-closure parameter.
The concrete input is now `Spectral.SimpleExpander.outerSequence`, built from
the imported MGG spectral proof and the proved simple bipartite lift. The
older implication from `Nonempty Spectral.SmoothSpectralFamily` is retained
separately; that particular Cayley family has not been constructed and is
not used to supply a premise of the new main theorem.

The independent exact-type check in `verification/UnconditionalMain.lean`
also checks the conclusion with ordinary forbidden-family densities
expanded. Its recorded output is `verification/unconditional-main.log`.
The checked main declarations have only
`[propext, Classical.choice, Quot.sound]` as transitive axioms. This is a
check of a parameter-free theorem, not an inference that an explicit premise
has been proved merely because a conditional result has a standard axiom list.

The new route and its graph estimates are reviewed in
`docs/weak-route-review.md`. The preserved review below covers the common
density, substitution, recursive, suspension, and complete-join foundation,
and the earlier conditional Cayley route. The final full-project rebuild
has passed for all 104 modules. The whole-project audit passed for 3,296
declarations, including 2,909 theorem declarations with generated items.
The source scan and independent target check also passed. These are the
current release results, recorded in `verification/result.json` and the
associated logs, rather than the earlier conditional-build totals.

## Final integration checked against the actual source

| Current declaration | Source-level obligation and discharge |
| --- | --- |
| `Spectral.SimpleExpander.kernel_hasZeroSumBound_real` | The actual simple bipartite kernel has d=5k, and its right-to-left biadjacency map has norm at most d/6 on the zero-sum functions of one index copy. It is obtained from the MGG port bound and the finite-field lift, not supplied as an extra family hypothesis. |
| `Spectral.SimpleExpander.outerSequence_lagrangian` | Every member is a genuine `FiniteGraph 3`. Its Lagrangian equals `weakOuterValue k (3*order j)`, including the exact uniform lower bound and the universal supporting-line upper bound. |
| `Construction.weakBase_exists_interval_of_smooth_finite_lagrangians` | This general helper still explicitly asks for a finite graph sequence and its properties. The actual call in `Main.lean` supplies `outerSequence`, `baseValue_lt_outerSequence`, strict antitonicity, convergence, and the proved adjacent-gap ratio limit. |
| `exists_three_below_lagrangian_interval` | No premise. It provides an actual nondegenerate interval of `BelowLagrangianApprox 3` by the preceding concrete call. |
| `main_theorem` | No premise. It passes that interval to the proved suspension and terminal-interval reduction and supplies actual `BelowLagrangianApprox.completeJoin` at every required uniformity. |
| `ordinary_density_terminal_interval` | No spectral premise. It expands the conclusion to `∀ r≥3, ∃ δ>0, ∀ x∈[1−δ,1], ∃ forbidden, SetFamily.turanDensity forbidden=x`. |

The current proof has q=2^48, d=q(q−1), k=d/5, and single-side kernel order
Nⱼ=(j+3)^2q^2. Divisibility, k≥4, and 3Nⱼ≥48k are proved numerically or
algebraically. Its finite graph Lagrangians are

\[
\lambda(Q_j)=a+\frac{c}{3N_j},\qquad
 a=1-\frac1{k^2},\qquad c=\frac{k/3+3}{k^2}>0.
\]

Consequently their positive error ratio is Nⱼ₊₁/Nⱼ, which tends to one.
The required approximation of a from below is supplied independently by
complete joins of zero, not inferred from this sequence approaching a from
above. The recursive parameter is 3k²; the strict gap to the actual clique
ratio is proved using the uniform value on `Fin (3*k^2+2)`.

Two semantic distinctions remain important. First, a regular bipartite graph
has an eigenvalue −d in its full adjacency operator; the new interface is a
bound on the **biadjacency** map on a single side's zero-sum functions, so it
does not falsely claim a bound on that full adjacency operator. Second,
`vertexEquiv` relabels the simple lifted kernel onto a cyclic additive type;
it does not claim that this arbitrary relabeling makes the kernel a Cayley
graph. The additive gadget uses only its proved kernel properties.

## Provenance and proof scope

The MGG proof is imported from
[girving/aks at c7fb62ed80a4a610f87f34db0082cadbd7c00c9f](https://github.com/girving/aks/tree/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f),
under Apache-2.0. Its 12-module closure was migrated, compiled, and its key
spectral declarations audited; `docs/aks-import.json` records original blobs,
source correspondence, and local compatibility changes. The imported
`spectralGap_mgg` proves its quantitative norm bound rather than assuming it.
The adapter, simple lift, additive gadget, and modified outer proof connect
that theorem to this project's target. This is an alternative proof of the
paper's main theorem, not a completed formalization of the original LPS
existence theorem.

The `TuranUniversality` reuse is separately documented in
`docs/reused-foundation.json` and `docs/reused-analysis.json`, with exact local
source hashes and extraction scope. Neither these foundations nor the AKS
proof are attributed to newly written proof code in this project.

## Historical review: conditional Cayley route

**Scope of the preserved record below:** it describes the earlier version
whose main entry point still required `Nonempty SmoothSpectralFamily`.
Its observations about ordinary density and finite constructions remain
applicable. Its completion status is historical and is superseded by the
parameter-free declarations and concrete MGG route reviewed above. The old
specific Cayley instance remains unproved; this does not leave a premise in
the current main theorem.

### Result and scope

No semantic defect was identified in the reviewed chain from finite graph
Lagrangians to ordinary Turán densities, through substitution and recursive
interval realization. The normalization, empty-carrier cases, and direction
of finite approximation are handled explicitly. The source review of
`Main.lean` at this earlier snapshot confirmed that its main entry point was conditional on exactly
`Nonempty Spectral.SmoothSpectralFamily`. Base approximation and complete-join
closure had been discharged by actual finite graph proofs. That snapshot did
**not** certify an unconditional proof of the paper's main theorem: the specific
Cayley spectral-family instance remained unresolved. The new MGG route above
subsequently removed that dependency from the final theorem.

The principal files reviewed were `Turan/LagrangianCap.lean`,
`Turan/BelowApproximation.lean`, `Turan/RecursiveInterval.lean`,
`Construction/Lifting.lean`, `Construction/PerturbedRecursion.lean`,
`Construction/RecursiveIntervalRealization.lean`,
`Construction/SpectralInterval.lean`, and `MainStatement.lean`. The follow-up
review covered `Construction/CompleteJoinBounds.lean`,
`Construction/CompleteJoinApprox.lean`, `Construction/CompleteJoinClosure.lean`,
`Turan/TerminalReduction.lean`, and the five then-existing statements in `Main.lean`.
Their relevant
density, substitution, compact-maximum, fixed-point, greedy approximation, and
spectral dependencies were inspected as well. Paths are relative to
`IntervalsTuran/` unless stated otherwise. No proof source was modified during
this review.

### Definitions and normalization

`SetFamily.Free` forbids globally injective edge-preserving embeddings of
every member of a set of finite simple uniform hypergraphs. Thus isolated
vertices count towards an embedding, and the definition is not homomorphism
avoidance or induced avoidance.

`SetFamily.extremalNumber F n` is the maximum number of edges of an ordinary
`F`-free graph on `Fin n`, with zero when there is no free host.
`SetFamily.extremalDensity F n` divides this number by `Nat.choose n r`.
`SetFamily.turanDensity` is the infimum of these densities for orders at least
`r`, and `extremalDensity_tendsto` proves that the full ordinary extremal
sequence converges to it. Accordingly, `turanSpectrum r` is the range of actual
ordinary densities of arbitrary forbidden families.

The edge polynomial is unnormalized; the Lagrangian is the supremum of
`r! * edgePolynomial` over real probability weights, with zero inserted.
`normalizedExtremalDensity_eq_factor` verifies the exact bridge

\[
\frac{r!\operatorname{ex}(F,n)}{n^r}
=\frac{r!\binom nr}{n^r}
 \frac{\operatorname{ex}(F,n)}{\binom nr},
\]

for `r ≤ n`; the first factor tends to one. The inserted zero and the
zero-extremal-number branch are used explicitly rather than assuming an
extremal host exists in every degenerate case.

### Checked proof obligations

| Component | Exact conclusion checked | Review result |
| --- | --- | --- |
| Lagrangian cap | `SetFamily.turanDensity_lagrangianCap_eq_of_tendsto` identifies the density of `{G : x < λ(G)}` with `x`, given finite Lagrangians bounded above by `x` and converging to `x`. | Lower bounds pass through genuine hom-free hosts and the proved finite-subfamily infimum formula. Upper bounds use ordinary free extremal hosts. No spectrum-closedness hypothesis appears. |
| Approximation from below | `belowLagrangianApprox_iff`, `BelowLagrangianApprox.of_tendsto_from_below`, and `.of_monotone_tendsto`. | Every selected finite witness retains `λ(G) ≤ x`; limits approached from above are not silently admitted. |
| Actual substitution | `substitute_polynomial`, `lagrangian_substitute`, and `belowLagrangianApprox_substitutionValue`. | Edges are the disjoint union of transversal base edges and internal child edges. Disjointness requires `2 ≤ r`. The exact maximum uses actual child Lagrangians and all real weights. Monotonicity preserves the upper bound on every finite approximant. |
| Empty child carriers | `exists_nonempty_lagrangian_representative` and `finiteSubstitute_lagrangian`. | A zero-order child is replaced by a one-vertex edgeless graph with the same Lagrangian. The exact substitution formula's nonempty-child hypothesis is then supplied, not discarded. |
| Suspension | `RGraph.lagrangian_suspension` and `BelowLagrangianApprox.lift`. | Adding `r-3` common vertices gives the factor `27*r!/(6*r^r)`. This is positive for `r > 0` and equals one at `r=3`. The upper bound handles zero slice mass; the lower proof does not require a maximizer on an empty original carrier. |
| Perturbed maximum | `exists_nondegenerate_base_maximizer` and `cliqueStep_right_slope`. | Compactness is applied to the full closed simplex. The selected maximizer maximizes the second-coordinate cube among all base maximizers. Positive branch coefficients follow from `a < μ` and the concrete clique symmetry. Neither uniqueness nor an implicit-function theorem is assumed. |
| Infinite recursion | `cliqueSequenceValue_constant`, `_tails_tendsto`, and `belowLagrangianApprox_cliqueSequenceValue`. | The value is the supremum of increasing finite zero-terminal substitutions. Continuity gives the tail equation; least-fixed-point arguments identify the constant case. Only monotonicity and a Lipschitz constant of one are used. |
| Interval realization | `Spectrum.exists_interval_of_smooth_finite_lagrangians`. | Positive errors and their adjacent-ratio limit prove eventual overlap. Greedy finite compositions remain below the target; diagonal approximation produces finite graphs. Preservation and interval filling are proved, rather than included as assumptions of this concrete theorem. |
| Complete-join closure | `BelowLagrangianApprox.completeJoin`. | Actual finite clone joins have an ideal-tuple upper bound and a matching asymptotic lower bound from independent injective clone labels. Both subtraction reversals preserve the upper bound on every witness. The construction handles `r=1`, `M=1`, and empty cores explicitly. |

All uses of the cap realization require `0 < r`; all concrete recursive uses
have `r=3`. The final lifting branch requires `3 ≤ r`. Thus the special
zero-uniformity conventions do not enter the intended theorem.

### Conditional integration at the earlier snapshot

The five then-existing statements in `Main.lean` were checked against their bodies and the
actual realization theorems they invoke:

| Statement | Remaining mathematical input |
| --- | --- |
| `belowLagrangianApprox_limitValue` | None. Applies the proved complete-join closure to zero, in uniformity three with thirty parts, giving `899/900`. |
| `terminalIntervalClaim_of_below_lagrangian_interval` | A nondegenerate interval of approximable finite Lagrangians, with `2 ≤ r`. Actual complete-join closure is supplied by the proof, not requested as an extra premise. |
| `main_theorem_of_smooth_spectral_family` | A term `F : Spectral.SmoothSpectralFamily`. The base approximation, recursive interval, lifting, and terminal amplification are discharged internally. |
| `main_theorem_of_spectral_existence` | Exactly `Nonempty Spectral.SmoothSpectralFamily`. |
| `ordinary_density_terminal_interval_of_smooth_spectral_family` | A term `F : Spectral.SmoothSpectralFamily`; the conclusion explicitly quantifies a forbidden family with the required ordinary `SetFamily.turanDensity`. |

In particular, no base-approximation, join-closure, abstract interval-filling,
or prescribed-Lagrangian assertion remains hidden in the main theorem's
input. `MainTheoremStatement` itself is unchanged and does not include a
spectral premise; the proved theorem is an implication to that target.

The clone lower bound uses the event that all clone labels are distinct. This
is stronger than necessary for an actual edge, so it correctly gives a lower
bound rather than a false finite equality. Its expectation factors as
`samplingFactor r q` times the ideal join value. At `q < r` this lower bound
is zero; the witness sequence uses `q=n+1`, and the factor tends to one.
For `r=1` or `M=1`, the join transform reduces to the identity. Empty cores
are replaced by a one-vertex edgeless graph before a maximizer is chosen.

At that snapshot, the only unresolved existence input was the finite Cayley spectral family.
A standard kernel-axiom list for a conditional theorem does **not** prove
its explicit premise. In particular, neither `main_theorem_of_spectral_existence`
nor an axiom audit of that implication supplies an inhabitant of
`SmoothSpectralFamily`.

### Historical observations before the final integration

The following observations were recorded before `Main.lean` was added.
Items 2 and 3 were resolved by the actual proofs described above; item 4
describes the still earlier state of `MainStatement.lean` alone. Item 1 remains
open only for the retained Cayley branch; it is no longer a dependency of the
current unconditional main theorem.

1. **The specific Cayley-family existence remains open in this project.**
   `SmoothSpectralFamily` explicitly requires finite groups with a symmetric
   generator subset of size `138`, zero-sum adjacency norm at most `47/2`,
   strictly increasing orders tending to infinity, and adjacent order ratios
   tending to one. It has no inhabitant supplied by a theorem. The exact
   tripartite and outer graph results prove consequences of this input; they
   do not establish it.

2. **The spectral interval interface also takes base approximation.**
   At the initial review, `SmoothSpectralFamily.exists_below_lagrangian_interval`
   has the explicit argument
   `hα : BelowLagrangianApprox 3 (899/900)`. The outer sequence approaches
   `899/900` from above, so it cannot discharge this argument using the
   from-below closure theorem. The intended independent discharge is the
   complete-join approximation of zero with thirty parts.

3. **Terminal amplification required genuine join closure.**
   `exists_terminal_interval_of_join_closed` is a proved real-variable
   implication whose join-closure argument is explicit. To complete the main
   reduction, the finite complete-join approximation must establish
   `x ↦ 1-(1-x)/M^(r-1)` on the relevant approximation set. The finite cubic
   identity alone is not this asymptotic closure theorem. The zero input,
   endpoint one, and all lifted uniformities must be integrated with that
   result.

4. **The named target was a proposition without a main reduction theorem.**
   `MainStatement.lean` defines `MainTheoremStatement` and proves only a
   definition-expansion equivalence. This accurately expresses ordinary
   Turán terminal intervals for every `r ≥ 3`. Existence of a proof term of
   that proposition should only be claimed after the remaining inputs are
   discharged. Any subsequently added conditional main theorem should retain
   its explicit spectral-family argument in reports.

The fixed-parameter spectral route contains a proved strengthening: the
outer graph has the exact value `899/900 + 1/(180*m)`. Its size requirement
`95 ≤ m` follows automatically from the generator-set cardinality. It avoids
the paper's asymptotic optimizer and decreasing-subsequence extraction; this
is an alternative proved route, not a verbatim translation of those lemmas.

### Targeted trust check recorded for the conditional snapshot

The separate input `verification/ProofReviewAxioms.lean` was run successfully
against the compiled modules. The complete output is in
`docs/proof-review-axioms.log`. It checks one principal declaration from each
of the nine spectral/outer modules, plus cap realization, suspension,
substitution preservation, the right perturbation slope, the concrete smooth
interval theorem, and its spectral specialization: **15 declarations total**.

Every checked declaration reports precisely:

```text
[propext, Classical.choice, Quot.sound]
```

No checked declaration depends on `sorryAx`, a custom axiom, or
`Lean.ofReduceBool`. The reviewed source search also found no `sorry`,
`axiom`, `native_decide`, or `admit`. Axiom output does not detect outstanding
explicit hypotheses or a mismatch between an intended theorem and its formal
statement; those were reviewed separately above. This targeted review is not
a replacement for the final complete build and whole-project audit.
