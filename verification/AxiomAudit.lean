module

meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms
import all IntervalsTuran
import all IntervalsTuran.Analysis.GreedyApproximation
import all IntervalsTuran.Analysis.MaxPerturbation
import all IntervalsTuran.Analysis.RecursiveValues
import all IntervalsTuran.Analysis.SmoothSubsequence
import all IntervalsTuran.Analysis.TailOverlap
import all IntervalsTuran.Analysis.TerminalIntervals
import all IntervalsTuran.Construction.BaseParameters
import all IntervalsTuran.Construction.CompleteGraphs
import all IntervalsTuran.Construction.CompleteJoin
import all IntervalsTuran.Construction.CompleteJoinApprox
import all IntervalsTuran.Construction.CompleteJoinBounds
import all IntervalsTuran.Construction.CompleteJoinClosure
import all IntervalsTuran.Construction.CompleteJoinCubic
import all IntervalsTuran.Construction.CompleteJoinWeights
import all IntervalsTuran.Construction.Lifting
import all IntervalsTuran.Construction.OuterGraph
import all IntervalsTuran.Construction.OuterOptimization
import all IntervalsTuran.Construction.OuterSequence
import all IntervalsTuran.Construction.OuterStationarity
import all IntervalsTuran.Construction.PerturbedRecursion
import all IntervalsTuran.Construction.RecursiveIntervalRealization
import all IntervalsTuran.Construction.RecursivePattern
import all IntervalsTuran.Construction.SpectralInterval
import all IntervalsTuran.Construction.WeakBaseParameters
import all IntervalsTuran.Construction.WeakOuterGraph
import all IntervalsTuran.Construction.WeakOuterOptimization
import all IntervalsTuran.Construction.WeakOuterSequence
import all IntervalsTuran.Density.Averages
import all IntervalsTuran.Density.Box
import all IntervalsTuran.Density.Cloning
import all IntervalsTuran.Density.EdgeDensity
import all IntervalsTuran.Density.Extremal
import all IntervalsTuran.Density.FamilyBasic
import all IntervalsTuran.Density.FamilyExtremal
import all IntervalsTuran.Density.FamilyLower
import all IntervalsTuran.Density.FamilyUpper
import all IntervalsTuran.Density.FiniteSubfamilyInf
import all IntervalsTuran.Density.HomDensity
import all IntervalsTuran.Density.SampleMoments
import all IntervalsTuran.Density.Sampling
import all IntervalsTuran.Density.SetFamilyBasic
import all IntervalsTuran.Density.SetFamilyExtremal
import all IntervalsTuran.Density.WeightedHom
import all IntervalsTuran.Density.WeightedHomPushforward
import all IntervalsTuran.Density.WeightedSampling
import all IntervalsTuran.Hypergraph.Basic
import all IntervalsTuran.Hypergraph.Blowup
import all IntervalsTuran.Hypergraph.BlowupCount
import all IntervalsTuran.Hypergraph.Clique
import all IntervalsTuran.Hypergraph.Compression
import all IntervalsTuran.Hypergraph.FiniteBasis
import all IntervalsTuran.Hypergraph.Hom
import all IntervalsTuran.Hypergraph.Lagrangian
import all IntervalsTuran.Hypergraph.LagrangianHom
import all IntervalsTuran.Hypergraph.Polynomial
import all IntervalsTuran.Hypergraph.Relabel
import all IntervalsTuran.Hypergraph.Restriction
import all IntervalsTuran.Hypergraph.SymmetricSums
import all IntervalsTuran.Main
import all IntervalsTuran.MainStatement
import all IntervalsTuran.Selector.CrossIntersecting
import all IntervalsTuran.Selector.FiniteAverages
import all IntervalsTuran.Selector.ProductMixing
import all IntervalsTuran.Spectral.AdditiveGadgetScaling
import all IntervalsTuran.Spectral.AdditiveTripartite
import all IntervalsTuran.Spectral.BipartiteKernel
import all IntervalsTuran.Spectral.Family
import all IntervalsTuran.Spectral.FiberDesingularization
import all IntervalsTuran.Spectral.GadgetScaling
import all IntervalsTuran.Spectral.KernelRelabel
import all IntervalsTuran.Spectral.Parameters
import all IntervalsTuran.Spectral.PermutationLift
import all IntervalsTuran.Spectral.PrimeParameters
import all IntervalsTuran.Spectral.SimpleExpanderFamily
import all IntervalsTuran.Spectral.SmoothOrders
import all IntervalsTuran.Spectral.TripartiteEstimate
import all IntervalsTuran.Spectral.TripartiteGraph
import all IntervalsTuran.Spectrum.CliqueFixedPoint
import all IntervalsTuran.Spectrum.CliqueRatio
import all IntervalsTuran.Spectrum.CliqueStep
import all IntervalsTuran.Spectrum.GraphSubstitution
import all IntervalsTuran.Spectrum.SubstitutionApproximation
import all IntervalsTuran.Spectrum.SubstitutionValue
import all IntervalsTuran.Turan.BelowApproximation
import all IntervalsTuran.Turan.LagrangianCap
import all IntervalsTuran.Turan.RecursiveInterval
import all IntervalsTuran.Turan.TerminalReduction
import all IntervalsTuran.Uniformity.MassOptimization
import all IntervalsTuran.Uniformity.Suspension
import all IntervalsTuran.Vendor.AKS.Graph.Regular
import all IntervalsTuran.Vendor.AKS.Graph.Square
import all IntervalsTuran.Vendor.AKS.MGG.Adapter
import all IntervalsTuran.Vendor.AKS.MGG.Audit
import all IntervalsTuran.Vendor.AKS.MGG.DFT
import all IntervalsTuran.Vendor.AKS.MGG.Defs
import all IntervalsTuran.Vendor.AKS.MGG.Spectral
import all IntervalsTuran.Vendor.AKS.MGG.WalkExpansion
import all IntervalsTuran.Vendor.AKS.MGG.Young
import all IntervalsTuran.Vendor.AKS.MGG.YoungAssembly
import all IntervalsTuran.Vendor.AKS.MGG.YoungDefs
import all IntervalsTuran.Vendor.AKS.Misc.Fin
import all IntervalsTuran.Vendor.AKS.ZigZag.RVWBound
import all IntervalsTuran.Vendor.AKS.ZigZag.RVWInequality

/-!
The imports above are generated by `scripts/generate-imports.py`. Each project
module is imported with `all` so the audit can inspect private proof helpers
and distinguish actual axioms from declarations with hidden bodies.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    -- Module provenance includes AKS declarations in their upstream namespaces.
    let fromProjectModule := match env.getModuleIdxFor? name with
      | some idx => (`IntervalsTuran).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if fromProjectModule then
      if info.isAxiom then
        throwError "PROJECT AXIOM: {name}"
      if info.isTheorem then
        theoremCount := theoremCount + 1
      names := names.push name
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun ax => !allowed.contains ax)
    if !unexpected.isEmpty then
      throwError "UNEXPECTED AXIOMS: {name}: {unexpected.toList}"
    logInfo m!"AUDIT {name}: {axioms.qsort Name.lt |>.toList}"
  logInfo m!"AUDIT PASSED: {names.size} project declarations; {theoremCount} theorems; permitted axioms only: {allowed}"
