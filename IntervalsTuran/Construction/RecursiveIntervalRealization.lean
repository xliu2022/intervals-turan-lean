module

public import IntervalsTuran.Construction.RecursivePattern
public import IntervalsTuran.Construction.PerturbedRecursion
public import IntervalsTuran.Analysis.TailOverlap
public import IntervalsTuran.Turan.RecursiveInterval

/-!
# From a smooth decreasing Lagrangian sequence to an interval

Author and maintainer: Xizhi Liu.

This file proves the interval-filling implication using actual finite
substitution graphs, the compact polynomial maximum, its right perturbation
slope, the recursive tail limit, and greedy finite approximation. It does not
assume interval filling or realization of an abstract recursive value.
The existence of the smooth finite-graph sequence is a separate input.
-/

@[expose] public section

namespace IntervalsTuran.Spectrum

open Set Filter Topology Analysis

/-- The concrete clique recursion fills an interval whenever its side values
decrease smoothly to an approximable base coefficient below the least fixed
point. All side values are themselves realized by finite graph approximation. -/
theorem exists_interval_of_smooth_side_values
    (m : ℕ) (a : DensityInterval) (b : ℕ → DensityInterval)
    (hα : BelowLagrangianApprox 3 (a : ℝ))
    (hβ : ∀ n, BelowLagrangianApprox 3 (b n : ℝ))
    (hgap : (a : ℝ) < cliqueRatioValue m a)
    (hab : ∀ n, a < b n) (hanti : Antitone b)
    (hlim : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (a : ℝ)))
    (hratio : Tendsto (fun n => ((b n : ℝ) - a) / ((b (n + 1) : ℝ) - a))
      atTop (𝓝 1)) :
    ∃ v : ℝ, cliqueRatioValue m a < v ∧
      Icc (cliqueRatioValue m a) v ⊆ {x | BelowLagrangianApprox 3 x} := by
  let μ := cliqueRatioValue m a
  let ν : ℕ → ℝ := fun n => cliqueSequenceValue m (fun i => b (i + n))
  let ε : ℕ → ℝ := fun n => (b n : ℝ) - a
  have hε : ∀ n, 0 < ε n := fun n => sub_pos.mpr (hab n)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [sub_self] using hlim.sub (tendsto_const_nhds (x := (a : ℝ)))
  have hμ : 0 < μ := a.property.1.trans_lt hgap
  have hν : ∀ n, μ < ν n := fun n =>
    cliqueSequenceValue_gt_base m a (fun i => b (i + n)) hμ (fun i => hab (i + n))
  have hνlim : Tendsto ν atTop (𝓝 μ) :=
    cliqueSequenceValue_tails_tendsto m b a hanti hlim
  have hrec : ∀ n, ν n = cliqueStep m (ν (n + 1)) (b n) :=
    cliqueSequenceValue_shift_succ m b
  obtain ⟨z, hz, hq, -, hR, hzval, hzmax⟩ :=
    exists_nondegenerate_base_maximizer m a.property.1 hgap
  have hδ : ∀ n, 0 ≤ ν n - μ := fun n => sub_nonneg.mpr (hν n).le
  have hδrec (n : ℕ) : z 0 ^ 3 * (ν (n + 1) - μ) + z 1 ^ 3 * ε n ≤ ν n - μ := by
    have h := cliqueStep_lower_from_base_maximizer m hz hzval (ν (n + 1) - μ) (ε n)
    have ht : cliqueRatioValue m a + (ν (n + 1) - μ) = ν (n + 1) := by dsimp [μ]; ring
    have hb : (a : ℝ) + ε n = b n := by dsimp [ε]; ring
    rw [ht, hb, ← hrec n] at h
    dsimp only [μ] at *
    linarith
  have hright : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε⟩
  have hs : Tendsto (fun n => (cliqueStep m μ (b n) - μ) / ε n)
      atTop (𝓝 (z 1 ^ 3)) := by
    have h := (cliqueStep_right_slope m hz hzval hzmax).comp hright
    have hb (n : ℕ) : (a : ℝ) + ε n = b n := by dsimp [ε]; ring
    simpa only [Function.comp_def, hb, μ] using h
  have hoverlap : ∀ᶠ n in atTop, cliqueStep m μ (b n) ≤ ν (n + 1) := by
    have h := eventually_lt_next_tail_of_ratio_limit hε hratio hq hR hδ hδrec hs
    filter_upwards [h] with n hn
    linarith
  exact exists_belowLagrangianApprox_interval_of_eventual_recursive_overlap
    (ψ := fun n t => cliqueStep m t (b n))
    (fun n => cliqueStep_monotone_input m (b n))
    (fun n => cliqueStep_lipschitz_input m (b n))
    (fun n => le_cliqueStep m μ (b n)) hν hνlim hrec hoverlap
    (belowLagrangianApprox_cliqueRatioValue m hα)
    (fun n _ ht => belowLagrangianApprox_cliqueStep m ht (hβ n))

/-- Version with the side coefficients supplied by actual finite 3-graphs. -/
theorem exists_interval_of_smooth_finite_lagrangians
    (m : ℕ) {a : ℝ} (ha : BelowLagrangianApprox 3 a)
    (hgap : a < cliqueRatioValue m a)
    (G : ℕ → FiniteGraph 3)
    (hab : ∀ n, a < (G n).2.lagrangian)
    (hanti : Antitone (fun n => (G n).2.lagrangian))
    (hlim : Tendsto (fun n => (G n).2.lagrangian) atTop (𝓝 a))
    (hratio : Tendsto (fun n => ((G n).2.lagrangian - a) /
      ((G (n + 1)).2.lagrangian - a)) atTop (𝓝 1)) :
    ∃ v : ℝ, cliqueRatioValue m a < v ∧
      Icc (cliqueRatioValue m a) v ⊆ {x | BelowLagrangianApprox 3 x} := by
  let a' : DensityInterval := ⟨a, ha.nonneg, ha.le_one⟩
  let b : ℕ → DensityInterval := fun n =>
    ⟨(G n).2.lagrangian, (G n).2.lagrangian_nonneg, (G n).2.lagrangian_le_one⟩
  exact exists_interval_of_smooth_side_values m a' b ha
    (fun n => belowLagrangianApprox_lagrangian (G n)) hgap hab hanti hlim hratio

/-- In particular, the resulting interval lies in the ordinary Turan spectrum. -/
theorem exists_turan_interval_of_smooth_finite_lagrangians
    (m : ℕ) {a : ℝ} (ha : BelowLagrangianApprox 3 a)
    (hgap : a < cliqueRatioValue m a)
    (G : ℕ → FiniteGraph 3)
    (hab : ∀ n, a < (G n).2.lagrangian)
    (hanti : Antitone (fun n => (G n).2.lagrangian))
    (hlim : Tendsto (fun n => (G n).2.lagrangian) atTop (𝓝 a))
    (hratio : Tendsto (fun n => ((G n).2.lagrangian - a) /
      ((G (n + 1)).2.lagrangian - a)) atTop (𝓝 1)) :
    ∃ u v : ℝ, u < v ∧ Icc u v ⊆ turanSpectrum 3 := by
  obtain ⟨v, hv, hI⟩ := exists_interval_of_smooth_finite_lagrangians
    m ha hgap G hab hanti hlim hratio
  exact ⟨cliqueRatioValue m a, v, hv, fun _ hx => (hI hx).mem_turanSpectrum (by omega)⟩

end IntervalsTuran.Spectrum
