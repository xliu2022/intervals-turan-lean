module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

/-!
# One-sided perturbations of a maximum on a compact set

This module proves the elementary compactness estimate used in the Lagrangian
asymptotics and in the recursive interval construction. All estimates concern
nonnegative perturbation parameters. No uniqueness of the unperturbed
maximizer is assumed.

Author and maintainer: Xizhi Liu.
-/

public section

namespace IntervalsTuran.Analysis

open Set Filter

open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- The supremum of the perturbed objective over the specified domain.
The theorems below establish attainment and the needed bounds for nonempty
compact domains and continuous objectives. -/
noncomputable def perturbationMaximum (K : Set X) (f h : X → ℝ) (t : ℝ) : ℝ :=
  sSup ((fun x => f x + t * h x) '' K)

/-- A uniform first-order upper estimate. The value `R` bounds `h` on every
point where `f` attains its upper bound `M`. This formulation does not require
choosing a maximizer and also applies to an empty domain. -/
theorem exists_uniform_perturbation_upper
    {K : Set X} {f h : X → ℝ} {M R : ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hh : ContinuousOn h K)
    (hfM : ∀ x ∈ K, f x ≤ M)
    (hhR : ∀ x ∈ K, f x = M → h x ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 ≤ t → t < t₀ →
      ∀ x ∈ K, f x + t * h x ≤ M + t * (R + ε) := by
  let B : Set X := K ∩ h ⁻¹' Ici (R + ε)
  have hBc : IsCompact B :=
    hh.upperSemicontinuousOn.isCompact_inter_preimage_Ici hK (R + ε)
  by_cases hB : B.Nonempty
  · obtain ⟨z, hz, hfz⟩ := hBc.exists_isMaxOn hB (hf.mono inter_subset_left)
    have hzK : z ∈ K := hz.1
    have hzlarge : R + ε ≤ h z := hz.2
    have hzlt : f z < M := by
      refine lt_of_le_of_ne (hfM z hzK) ?_
      intro hzM
      have hzR := hhR z hzK hzM
      linarith
    obtain ⟨C, hC⟩ := hK.bddAbove_image hh
    let L : ℝ := max (C - R) 1
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine ⟨(M - f z) / L, div_pos (sub_pos.mpr hzlt) hLpos, ?_⟩
    intro t ht ht₀ x hx
    by_cases hxsmall : h x ≤ R + ε
    · exact add_le_add (hfM x hx) (mul_le_mul_of_nonneg_left hxsmall ht)
    · have hxB : x ∈ B := ⟨hx, le_of_lt (lt_of_not_ge hxsmall)⟩
      have hfx : f x ≤ f z := hfz hxB
      have hxC : h x ≤ C := hC (mem_image_of_mem h hx)
      have hxL : h x - R ≤ L :=
        (sub_le_sub_right hxC R).trans (le_max_left _ _)
      have hmul := mul_le_mul_of_nonneg_left hxL ht
      have htL : t * L < M - f z := (lt_div_iff₀ hLpos).mp ht₀
      have hte : 0 ≤ t * ε := mul_nonneg ht hε.le
      nlinarith only [hfx, hmul, htL, hte]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht _ x hx
    have hxsmall : h x ≤ R + ε := by
      by_contra hxlarge
      exact hB ⟨x, hx, le_of_lt (lt_of_not_ge hxlarge)⟩
    exact add_le_add (hfM x hx) (mul_le_mul_of_nonneg_left hxsmall ht)

/-- If `x₀` maximizes `f`, and among such maximizers also maximizes `h`, the
maximum of `f + t*h` has right first-order coefficient `h x₀`.
The epsilon formulation avoids any differentiability assumption. -/
theorem perturbationMaximum_bounds
    {K : Set X} {f h : X → ℝ} {x₀ : X}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hh : ContinuousOn h K)
    (hx₀ : x₀ ∈ K) (hfmax : IsMaxOn f K x₀)
    (hhmax : ∀ x ∈ K, f x = f x₀ → h x ≤ h x₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 ≤ t → t < t₀ →
      f x₀ + t * h x₀ ≤ perturbationMaximum K f h t ∧
      perturbationMaximum K f h t ≤ f x₀ + t * (h x₀ + ε) := by
  obtain ⟨t₀, ht₀, hu⟩ :=
    exists_uniform_perturbation_upper hK hf hh (fun x hx => hfmax hx) hhmax hε
  refine ⟨t₀, ht₀, ?_⟩
  intro t ht hlt
  have hc : ContinuousOn (fun x => f x + t * h x) K :=
    hf.add (continuousOn_const.mul hh)
  constructor
  · exact le_csSup (hK.bddAbove_image hc) (mem_image_of_mem _ hx₀)
  · apply csSup_le (Nonempty.image _ ⟨x₀, hx₀⟩)
    rintro _ ⟨x, hx, rfl⟩
    exact hu t ht hlt x hx

/-- On a nonempty compact domain, one can first maximize `f` and then maximize
`h` over the entire set of maximizers of `f`. -/
theorem exists_lexicographic_maximizer
    {K : Set X} {f h : X → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ContinuousOn f K) (hh : ContinuousOn h K) :
    ∃ x₀ ∈ K, IsMaxOn f K x₀ ∧
      ∀ x ∈ K, f x = f x₀ → h x ≤ h x₀ := by
  obtain ⟨z, hz, hfz⟩ := hK.exists_isMaxOn hne hf
  let A : Set X := K ∩ f ⁻¹' Ici (f z)
  have hAc : IsCompact A :=
    hf.upperSemicontinuousOn.isCompact_inter_preimage_Ici hK (f z)
  have hzA : z ∈ A := ⟨hz, le_rfl⟩
  obtain ⟨x₀, hx₀A, hhmax⟩ :=
    hAc.exists_isMaxOn ⟨z, hzA⟩ (hh.mono inter_subset_left)
  have hx₀K : x₀ ∈ K := hx₀A.1
  have hfeq : f x₀ = f z := le_antisymm (hfz hx₀K) hx₀A.2
  refine ⟨x₀, hx₀K, ?_, ?_⟩
  · intro x hx
    exact (hfz hx).trans hfeq.ge
  · intro x hx hfx
    apply hhmax
    exact ⟨hx, by change f z ≤ f x; rw [hfx, hfeq]⟩

/-- The right difference quotient of the maximum converges to the largest
perturbation value among all unperturbed maximizers. -/
theorem tendsto_perturbationMaximum_right_slope
    {K : Set X} {f h : X → ℝ} {x₀ : X}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hh : ContinuousOn h K)
    (hx₀ : x₀ ∈ K) (hfmax : IsMaxOn f K x₀)
    (hhmax : ∀ x ∈ K, f x = f x₀ → h x ≤ h x₀) :
    Tendsto (fun t : ℝ => (perturbationMaximum K f h t - f x₀) / t)
      (𝓝[>] 0) (𝓝 (h x₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t₀, ht₀, hb⟩ :=
    perturbationMaximum_bounds hK hf hh hx₀ hfmax hhmax (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
  obtain ⟨hlo, hhi⟩ := hb t ht.1.le ht.2
  have hquotlo : h x₀ ≤ (perturbationMaximum K f h t - f x₀) / t := by
    apply (le_div_iff₀ ht.1).mpr
    nlinarith only [hlo]
  have hquothi : (perturbationMaximum K f h t - f x₀) / t ≤ h x₀ + ε / 2 := by
    apply (div_le_iff₀ ht.1).mpr
    nlinarith only [hhi]
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A hypothesis-free compact-domain version: the lexicographic maximizer and
the right first-order expansion both exist for any two continuous objectives. -/
theorem exists_maximizer_with_perturbation_expansion
    {K : Set X} {f h : X → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hf : ContinuousOn f K) (hh : ContinuousOn h K) :
    ∃ x₀ ∈ K, IsMaxOn f K x₀ ∧
      (∀ x ∈ K, f x = f x₀ → h x ≤ h x₀) ∧
      Tendsto (fun t : ℝ => (perturbationMaximum K f h t - f x₀) / t)
        (𝓝[>] 0) (𝓝 (h x₀)) := by
  obtain ⟨x₀, hx₀, hfx₀, hhx₀⟩ := exists_lexicographic_maximizer hK hne hf hh
  exact ⟨x₀, hx₀, hfx₀, hhx₀,
    tendsto_perturbationMaximum_right_slope hK hf hh hx₀ hfx₀ hhx₀⟩

end IntervalsTuran.Analysis
