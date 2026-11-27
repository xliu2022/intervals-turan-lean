module

public import IntervalsTuran.Analysis.MaxPerturbation
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

/-!
# Smooth errors force overlap with the next recursive tail

This is the numerical part of the tail-overlap argument. A two-step lower
recurrence supplies an asymptotically larger coefficient than a one-step
perturbation. No strict contraction assumption is used.

Author and maintainer: Xizhi Liu.
-/

public section

namespace IntervalsTuran.Analysis

open Filter
open scoped Topology

/-- Inverting the ratio of successive positive errors preserves the limit one. -/
theorem tendsto_successive_error_ratio_reverse
    {ε : ℕ → ℝ}
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1)) :
    Tendsto (fun n => ε (n + 1) / ε n) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using hratio.inv₀ (show (1 : ℝ) ≠ 0 from one_ne_zero)

/-- Smooth adjacent errors also have a smooth two-step ratio. -/
theorem tendsto_two_step_error_ratio
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1)) :
    Tendsto (fun n => ε (n + 2) / ε n) atTop (𝓝 1) := by
  have h₁ := tendsto_successive_error_ratio_reverse hratio
  have h₂ := h₁.comp (tendsto_add_atTop_nat 1)
  have hprod := h₂.mul h₁
  convert hprod using 1
  · funext n
    simpa only [Function.comp_def, Nat.add_assoc] using
      (div_mul_div_cancel₀ (a := ε (n + 2)) (c := ε n) (hε (n + 1)).ne').symm
  · norm_num

/-- Two applications of the lower recurrence already give the estimate needed
for overlap. -/
theorem next_tail_lower_bound
    {ε δ : ℕ → ℝ} {q R : ℝ}
    (hq : 0 ≤ q) (hδ : ∀ n, 0 ≤ δ n)
    (hrec : ∀ n, q * δ (n + 1) + R * ε n ≤ δ n) (n : ℕ) :
    R * (ε (n + 1) + q * ε (n + 2)) ≤ δ (n + 1) := by
  have hrec₁ := hrec (n + 1)
  have hrec₂ := hrec (n + 2)
  have hnonneg : 0 ≤ q * δ (n + 2 + 1) := mul_nonneg hq (hδ _)
  have hlower : R * ε (n + 2) ≤ δ (n + 2) := by
    nlinarith only [hrec₂, hnonneg]
  have hscaled := mul_le_mul_of_nonneg_left hlower hq
  have hrec₁' : q * δ (n + 2) + R * ε (n + 1) ≤ δ (n + 1) := by
    simpa only [Nat.add_assoc] using hrec₁
  nlinarith only [hrec₁', hscaled]

/-- The normalized two-step lower bound has coefficient `R * (1 + q)`. -/
theorem tendsto_normalized_two_step_bound
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1))
    (q R : ℝ) :
    Tendsto (fun n => R * (ε (n + 1) / ε n + q * (ε (n + 2) / ε n)))
      atTop (𝓝 (R * (1 + q))) := by
  have h₁ := tendsto_successive_error_ratio_reverse hratio
  have h₂ := tendsto_two_step_error_ratio hε hratio
  simpa only [mul_one] using
    tendsto_const_nhds.mul (h₁.add (tendsto_const_nhds.mul h₂))

/-- A one-step upper slope of at most `R` is eventually strictly below the next
tail. This version requires only the upper epsilon estimate, not a full limit. -/
theorem eventually_lt_next_tail_of_upper_slope
    {ε δ s : ℕ → ℝ} {q R : ℝ}
    (hε : ∀ n, 0 < ε n)
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1))
    (hq : 0 < q) (hR : 0 < R) (hδ : ∀ n, 0 ≤ δ n)
    (hrec : ∀ n, q * δ (n + 1) + R * ε n ≤ δ n)
    (hs : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, s n ≤ (R + η) * ε n) :
    ∀ᶠ n in atTop, s n < δ (n + 1) := by
  have hgap : 0 < R * q / 2 := half_pos (mul_pos hR hq)
  have hlim := tendsto_normalized_two_step_bound hε hratio q R
  have hmargin : R + R * q / 2 < R * (1 + q) := by nlinarith
  have hevent : ∀ᶠ n in atTop,
      R + R * q / 2 < R * (ε (n + 1) / ε n + q * (ε (n + 2) / ε n)) :=
    tendsto_const_nhds.eventually_lt hlim hmargin
  filter_upwards [hs (R * q / 2) hgap, hevent] with n hsn hbound
  have hidentity : R * (ε (n + 1) / ε n + q * (ε (n + 2) / ε n)) =
      (R * (ε (n + 1) + q * ε (n + 2))) / ε n := by ring
  rw [hidentity] at hbound
  have hstrict : (R + R * q / 2) * ε n <
      R * (ε (n + 1) + q * ε (n + 2)) := (lt_div_iff₀ (hε n)).mp hbound
  exact hsn.trans_lt (hstrict.trans_le (next_tail_lower_bound hq.le hδ hrec n))

/-- The ratio-limit form of the tail-overlap criterion. -/
theorem eventually_lt_next_tail_of_ratio_limit
    {ε δ s : ℕ → ℝ} {q R : ℝ}
    (hε : ∀ n, 0 < ε n)
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1))
    (hq : 0 < q) (hR : 0 < R) (hδ : ∀ n, 0 ≤ δ n)
    (hrec : ∀ n, q * δ (n + 1) + R * ε n ≤ δ n)
    (hs : Tendsto (fun n => s n / ε n) atTop (𝓝 R)) :
    ∀ᶠ n in atTop, s n < δ (n + 1) := by
  apply eventually_lt_next_tail_of_upper_slope hε hratio hq hR hδ hrec
  intro η hη
  have hev : ∀ᶠ n in atTop, s n / ε n < R + η :=
    hs.eventually (eventually_lt_nhds (show R < R + η by linarith))
  filter_upwards [hev] with n hn
  exact ((div_lt_iff₀ (hε n)).mp hn).le

/-- After deleting a finite initial segment, overlap holds at every index. -/
theorem exists_tail_with_overlap
    {ε δ s : ℕ → ℝ} {q R : ℝ}
    (hε : ∀ n, 0 < ε n)
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1))
    (hq : 0 < q) (hR : 0 < R) (hδ : ∀ n, 0 ≤ δ n)
    (hrec : ∀ n, q * δ (n + 1) + R * ε n ≤ δ n)
    (hs : Tendsto (fun n => s n / ε n) atTop (𝓝 R)) :
    ∃ N : ℕ, ∀ n : ℕ, s (n + N) ≤ δ (n + N + 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_lt_next_tail_of_ratio_limit hε hratio hq hR hδ hrec hs)
  exact ⟨N, fun n => (hN (n + N) (by omega)).le⟩

/-- Directly connect compact maximum perturbation to the numerical overlap
criterion along a positive error sequence converging to zero. -/
theorem compact_perturbation_eventually_lt_next_tail
    {X : Type*} [TopologicalSpace X]
    {K : Set X} {f h : X → ℝ} {x₀ : X}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hh : ContinuousOn h K)
    (hx₀ : x₀ ∈ K) (hfmax : IsMaxOn f K x₀)
    (hhmax : ∀ x ∈ K, f x = f x₀ → h x ≤ h x₀)
    {ε δ : ℕ → ℝ} {q : ℝ}
    (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hratio : Tendsto (fun n => ε n / ε (n + 1)) atTop (𝓝 1))
    (hq : 0 < q) (hR : 0 < h x₀) (hδ : ∀ n, 0 ≤ δ n)
    (hrec : ∀ n, q * δ (n + 1) + h x₀ * ε n ≤ δ n) :
    ∀ᶠ n in atTop,
      perturbationMaximum K f h (ε n) - f x₀ < δ (n + 1) := by
  have hright : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hε⟩
  have hs := (tendsto_perturbationMaximum_right_slope hK hf hh hx₀ hfmax hhmax).comp hright
  exact eventually_lt_next_tail_of_ratio_limit hε hratio hq hR hδ hrec hs

end IntervalsTuran.Analysis
