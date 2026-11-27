module

public import IntervalsTuran.Analysis.GreedyApproximation
public import IntervalsTuran.Analysis.MaxPerturbation
public import IntervalsTuran.Analysis.RecursiveValues
public import IntervalsTuran.Analysis.SmoothSubsequence
public import IntervalsTuran.Analysis.TailOverlap
public import IntervalsTuran.Analysis.TerminalIntervals
public import IntervalsTuran.Construction.BaseParameters
public import IntervalsTuran.Construction.CompleteGraphs
public import IntervalsTuran.Construction.CompleteJoin
public import IntervalsTuran.Construction.CompleteJoinApprox
public import IntervalsTuran.Construction.CompleteJoinBounds
public import IntervalsTuran.Construction.CompleteJoinClosure
public import IntervalsTuran.Construction.CompleteJoinCubic
public import IntervalsTuran.Construction.CompleteJoinWeights
public import IntervalsTuran.Construction.Lifting
public import IntervalsTuran.Construction.OuterGraph
public import IntervalsTuran.Construction.OuterOptimization
public import IntervalsTuran.Construction.OuterSequence
public import IntervalsTuran.Construction.OuterStationarity
public import IntervalsTuran.Construction.PerturbedRecursion
public import IntervalsTuran.Construction.RecursiveIntervalRealization
public import IntervalsTuran.Construction.RecursivePattern
public import IntervalsTuran.Construction.SpectralInterval
public import IntervalsTuran.Construction.WeakBaseParameters
public import IntervalsTuran.Construction.WeakOuterGraph
public import IntervalsTuran.Construction.WeakOuterOptimization
public import IntervalsTuran.Construction.WeakOuterSequence
public import IntervalsTuran.Density.Averages
public import IntervalsTuran.Density.Box
public import IntervalsTuran.Density.Cloning
public import IntervalsTuran.Density.EdgeDensity
public import IntervalsTuran.Density.Extremal
public import IntervalsTuran.Density.FamilyBasic
public import IntervalsTuran.Density.FamilyExtremal
public import IntervalsTuran.Density.FamilyLower
public import IntervalsTuran.Density.FamilyUpper
public import IntervalsTuran.Density.FiniteSubfamilyInf
public import IntervalsTuran.Density.HomDensity
public import IntervalsTuran.Density.SampleMoments
public import IntervalsTuran.Density.Sampling
public import IntervalsTuran.Density.SetFamilyBasic
public import IntervalsTuran.Density.SetFamilyExtremal
public import IntervalsTuran.Density.WeightedHom
public import IntervalsTuran.Density.WeightedHomPushforward
public import IntervalsTuran.Density.WeightedSampling
public import IntervalsTuran.Hypergraph.Basic
public import IntervalsTuran.Hypergraph.Blowup
public import IntervalsTuran.Hypergraph.BlowupCount
public import IntervalsTuran.Hypergraph.Clique
public import IntervalsTuran.Hypergraph.Compression
public import IntervalsTuran.Hypergraph.FiniteBasis
public import IntervalsTuran.Hypergraph.Hom
public import IntervalsTuran.Hypergraph.Lagrangian
public import IntervalsTuran.Hypergraph.LagrangianHom
public import IntervalsTuran.Hypergraph.Polynomial
public import IntervalsTuran.Hypergraph.Relabel
public import IntervalsTuran.Hypergraph.Restriction
public import IntervalsTuran.Hypergraph.SymmetricSums
public import IntervalsTuran.Main
public import IntervalsTuran.MainStatement
public import IntervalsTuran.Selector.CrossIntersecting
public import IntervalsTuran.Selector.FiniteAverages
public import IntervalsTuran.Selector.ProductMixing
public import IntervalsTuran.Spectral.AdditiveGadgetScaling
public import IntervalsTuran.Spectral.AdditiveTripartite
public import IntervalsTuran.Spectral.BipartiteKernel
public import IntervalsTuran.Spectral.Family
public import IntervalsTuran.Spectral.FiberDesingularization
public import IntervalsTuran.Spectral.GadgetScaling
public import IntervalsTuran.Spectral.KernelRelabel
public import IntervalsTuran.Spectral.Parameters
public import IntervalsTuran.Spectral.PermutationLift
public import IntervalsTuran.Spectral.PrimeParameters
public import IntervalsTuran.Spectral.SimpleExpanderFamily
public import IntervalsTuran.Spectral.SmoothOrders
public import IntervalsTuran.Spectral.TripartiteEstimate
public import IntervalsTuran.Spectral.TripartiteGraph
public import IntervalsTuran.Spectrum.CliqueFixedPoint
public import IntervalsTuran.Spectrum.CliqueRatio
public import IntervalsTuran.Spectrum.CliqueStep
public import IntervalsTuran.Spectrum.GraphSubstitution
public import IntervalsTuran.Spectrum.SubstitutionApproximation
public import IntervalsTuran.Spectrum.SubstitutionValue
public import IntervalsTuran.Turan.BelowApproximation
public import IntervalsTuran.Turan.LagrangianCap
public import IntervalsTuran.Turan.RecursiveInterval
public import IntervalsTuran.Turan.TerminalReduction
public import IntervalsTuran.Uniformity.MassOptimization
public import IntervalsTuran.Uniformity.Suspension
public import IntervalsTuran.Vendor.AKS.Graph.Regular
public import IntervalsTuran.Vendor.AKS.Graph.Square
public import IntervalsTuran.Vendor.AKS.MGG.Adapter
public import IntervalsTuran.Vendor.AKS.MGG.Audit
public import IntervalsTuran.Vendor.AKS.MGG.DFT
public import IntervalsTuran.Vendor.AKS.MGG.Defs
public import IntervalsTuran.Vendor.AKS.MGG.Spectral
public import IntervalsTuran.Vendor.AKS.MGG.WalkExpansion
public import IntervalsTuran.Vendor.AKS.MGG.Young
public import IntervalsTuran.Vendor.AKS.MGG.YoungAssembly
public import IntervalsTuran.Vendor.AKS.MGG.YoungDefs
public import IntervalsTuran.Vendor.AKS.Misc.Fin
public import IntervalsTuran.Vendor.AKS.ZigZag.RVWBound
public import IntervalsTuran.Vendor.AKS.ZigZag.RVWInequality

/-!
# Intervals of hypergraph Turan densities: formalization library

Author and maintainer: Xizhi Liu.

The unconditional main theorem is `IntervalsTuran.main_theorem`. Its proof
uses the checked MGG construction and an actual simple bipartite lift.
The earlier LPS-based conditional lemmas are retained as separate results.
-/

