module

public import IntervalsTuran.Construction.OuterSequence
public import IntervalsTuran.Construction.BaseParameters
public import IntervalsTuran.Construction.RecursiveIntervalRealization

/-!
# Connecting the spectral sequence to the realized recursive interval

Author and maintainer: Xizhi Liu.

The finite Cayley spectral family remains an explicit argument. This theorem
does not assert that such a family exists.
-/

@[expose] public section

namespace IntervalsTuran.Spectral.SmoothSpectralFamily

theorem exists_below_lagrangian_interval (F : SmoothSpectralFamily)
    (hα : BelowLagrangianApprox 3 limitValue) :
    ∃ v : ℝ, Spectrum.cliqueRatioValue 2699 limitValue < v ∧
      Set.Icc (Spectrum.cliqueRatioValue 2699 limitValue) v ⊆
        {x | BelowLagrangianApprox 3 x} :=
  Spectrum.exists_interval_of_smooth_finite_lagrangians 2699 hα
    limitValue_lt_cliqueRatioValue F.outerSequence F.limitValue_lt_outerSequence
    F.outerSequence_strictAnti.antitone F.outerSequence_tendsto
    F.outerSequence_gap_ratio_tendsto

end IntervalsTuran.Spectral.SmoothSpectralFamily
