module

public import IntervalsTuran.Spectrum.CliqueFixedPoint
public import IntervalsTuran.Analysis.MaxPerturbation

/-!
# A positive active branch and the one-step perturbation slope

Author and maintainer: Xizhi Liu.

This proves the nondegeneracy and perturbation assertions for the actual
complete-graph recursion. The only numerical hypothesis is that its least
fixed point exceeds the side coefficient. The maximizing vector is selected
over the whole compact simplex, including its degenerate boundary.
-/

@[expose] public section

namespace IntervalsTuran.Spectrum

open Finset Set Filter Topology Analysis

theorem cliqueStepObjective_continuous (m : ℕ) (t b : ℝ) :
    Continuous (cliqueStepObjective m t b) := by
  unfold cliqueStepObjective RGraph.edgePolynomial
  fun_prop

/-- Select a base maximizer with the largest second-coordinate cube. Both
distinguished coordinates are positive, and its first coordinate is below one. -/
theorem exists_nondegenerate_base_maximizer (m : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (hgap : a < cliqueRatioValue m a) :
    ∃ z : Fin (m + 2) → ℝ, ProbabilityWeights z ∧
      0 < z 0 ^ 3 ∧ z 0 ^ 3 < 1 ∧ 0 < z 1 ^ 3 ∧
      cliqueStepObjective m (cliqueRatioValue m a) a z = cliqueRatioValue m a ∧
      ∀ x, ProbabilityWeights x →
        cliqueStepObjective m (cliqueRatioValue m a) a x = cliqueRatioValue m a →
        x 1 ^ 3 ≤ z 1 ^ 3 := by
  have hμ : 0 < cliqueRatioValue m a := ha.trans_lt hgap
  obtain ⟨z, hz, hfz, hhz⟩ := exists_lexicographic_maximizer
    probabilityWeights_isCompact probabilityWeights_nonempty
    (cliqueStepObjective_continuous m (cliqueRatioValue m a) a).continuousOn
    (show ContinuousOn (fun x : Fin (m + 2) → ℝ => x 1 ^ 3)
      {x | ProbabilityWeights x} by fun_prop)
  have hval : cliqueStepObjective m (cliqueRatioValue m a) a z = cliqueRatioValue m a := by
    apply le_antisymm
    · exact (cliqueStepObjective_le m _ _ z hz).trans_eq (cliqueRatioValue_fixed m a)
    · calc
        cliqueRatioValue m a = cliqueStep m (cliqueRatioValue m a) a :=
          (cliqueRatioValue_fixed m a).symm
        _ ≤ cliqueStepObjective m (cliqueRatioValue m a) a z :=
          (cliqueStep_le_iff m _ _ _).mpr (fun x hx => hfz hx)
  have hmax : ∀ x, ProbabilityWeights x →
      cliqueStepObjective m (cliqueRatioValue m a) a x = cliqueRatioValue m a →
      x 1 ^ 3 ≤ z 1 ^ 3 := fun x hx he => hhz x hx (he.trans hval.symm)
  obtain ⟨y, hy, hypos, hyval⟩ := exists_cliqueStep_base_maximizer_second_pos m ha hμ
  have hR : 0 < z 1 ^ 3 := (pow_pos hypos 3).trans_le (hmax y hy hyval)
  have hz1 : 0 < z 1 := by
    by_contra h
    have he : z 1 = 0 := le_antisymm (le_of_not_gt h) (hz.1 1)
    rw [he] at hR
    norm_num at hR
  have hz0 : 0 < z 0 := cliqueStep_maximizer_first_pos m hμ hgap z hz
    (hval.trans (cliqueRatioValue_fixed m a).symm)
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hsum : z 0 + z 1 ≤ 1 := by
    calc
      z 0 + z 1 = ∑ i ∈ ({0, 1} : Finset (Fin (m + 2))), z i := by simp [h01]
      _ ≤ ∑ i, z i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hz.1 i)
      _ = 1 := hz.2
  exact ⟨z, hz, pow_pos hz0 _, pow_lt_one₀ hz0.le (by linarith) (by decide),
    hR, hval, hmax⟩

/-- The right derivative of the optimized value in the side coefficient is
the largest active second-coordinate cube. This is an actual limit of the
concrete recursion map, with no differentiability hypothesis. -/
theorem cliqueStep_right_slope (m : ℕ) {a : ℝ} {z : Fin (m + 2) → ℝ}
    (hz : ProbabilityWeights z)
    (hval : cliqueStepObjective m (cliqueRatioValue m a) a z = cliqueRatioValue m a)
    (hmax : ∀ x, ProbabilityWeights x →
      cliqueStepObjective m (cliqueRatioValue m a) a x = cliqueRatioValue m a →
      x 1 ^ 3 ≤ z 1 ^ 3) :
    Tendsto (fun η : ℝ =>
      (cliqueStep m (cliqueRatioValue m a) (a + η) - cliqueRatioValue m a) / η)
      (𝓝[>] 0) (𝓝 (z 1 ^ 3)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η₀, hη₀, hu⟩ := exists_uniform_perturbation_upper
    probabilityWeights_isCompact
    (cliqueStepObjective_continuous m (cliqueRatioValue m a) a).continuousOn
    (show ContinuousOn (fun x : Fin (m + 2) → ℝ => x 1 ^ 3)
      {x | ProbabilityWeights x} by fun_prop)
    (fun x hx => (cliqueStepObjective_le m _ _ x hx).trans_eq (cliqueRatioValue_fixed m a))
    hmax (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hη₀] with η hη
  have hlo : cliqueRatioValue m a + η * z 1 ^ 3 ≤
      cliqueStep m (cliqueRatioValue m a) (a + η) := by
    have h := cliqueStepObjective_le m (cliqueRatioValue m a) (a + η) z hz
    unfold cliqueStepObjective at h hval
    linarith
  have hhi : cliqueStep m (cliqueRatioValue m a) (a + η) ≤
      cliqueRatioValue m a + η * (z 1 ^ 3 + ε / 2) := by
    apply (cliqueStep_le_iff m _ _ _).mpr
    intro x hx
    have h := hu η hη.1.le hη.2 x hx
    unfold cliqueStepObjective at h ⊢
    linarith
  have hlo' : z 1 ^ 3 ≤
      (cliqueStep m (cliqueRatioValue m a) (a + η) - cliqueRatioValue m a) / η := by
    apply (le_div_iff₀ hη.1).mpr
    linarith
  have hhi' : (cliqueStep m (cliqueRatioValue m a) (a + η) -
      cliqueRatioValue m a) / η ≤ z 1 ^ 3 + ε / 2 := by
    apply (div_le_iff₀ hη.1).mpr
    linarith
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Evaluation at a fixed base maximizer gives the two-branch lower recurrence. -/
theorem cliqueStep_lower_from_base_maximizer (m : ℕ) {a : ℝ}
    {z : Fin (m + 2) → ℝ} (hz : ProbabilityWeights z)
    (hval : cliqueStepObjective m (cliqueRatioValue m a) a z = cliqueRatioValue m a)
    (δ ε : ℝ) :
    cliqueRatioValue m a + z 0 ^ 3 * δ + z 1 ^ 3 * ε ≤
      cliqueStep m (cliqueRatioValue m a + δ) (a + ε) := by
  have h := cliqueStepObjective_le m (cliqueRatioValue m a + δ) (a + ε) z hz
  unfold cliqueStepObjective at h hval
  nlinarith only [h, hval]

end IntervalsTuran.Spectrum
