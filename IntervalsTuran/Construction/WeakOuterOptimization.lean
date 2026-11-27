/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Construction.OuterStationarity

/-!
# Exact outer optimization for a fixed normalized spectral gap

The internal simple bipartite graph has degree 5k and norm at most 5k/6.
The two-link tripartite estimate has coefficient 5k/4. For k ≥ 4 and
m ≥ 48k, a supporting-line argument gives the exact uniform outer value.
The large-mass branch uses only tripartiteness. No stationarity assumption
is needed for this universal polynomial inequality.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Construction

noncomputable section

def weakOuterBase (k : ℕ) : ℝ := 1 - 1 / (k : ℝ) ^ 2

def weakOuterCoefficient (k : ℕ) : ℝ := ((k : ℝ) / 3 + 3) / (k : ℝ) ^ 2

def weakOuterValue (k : ℕ) (m : ℝ) : ℝ :=
  weakOuterBase k + weakOuterCoefficient k / m

def outerSupport (k A m w : ℝ) : ℝ :=
  A * (3 * w / k ^ 2 - 2 / k ^ 3) + (3 / m) * (2 * w / k - 1 / k ^ 2)

theorem cube_support {k w : ℝ} (hk : 0 < k) (hw : 0 ≤ w) :
    3 * w / k ^ 2 - 2 / k ^ 3 ≤ w ^ 3 := by
  have h := mul_nonneg (sq_nonneg (w - 1 / k))
    (show 0 ≤ w + 2 / k by positivity)
  have heq : (w - 1 / k) ^ 2 * (w + 2 / k) =
      w ^ 3 - (3 * w / k ^ 2 - 2 / k ^ 3) := by
    field_simp [hk.ne']
    ring
  rw [heq] at h
  linarith

theorem square_support {k w : ℝ} (hk : 0 < k) :
    2 * w / k - 1 / k ^ 2 ≤ w ^ 2 := by
  have h := sq_nonneg (w - 1 / k)
  have heq : (w - 1 / k) ^ 2 = w ^ 2 - (2 * w / k - 1 / k ^ 2) := by
    field_simp [hk.ne']
    ring
  rw [heq] at h
  linarith

theorem outerSupport_le_reduced {k A m w : ℝ}
    (hk : 0 < k) (hA : 0 ≤ A) (hm : 0 < m) (hw : 0 ≤ w) :
    outerSupport k A m w ≤ A * w ^ 3 + (3 / m) * w ^ 2 := by
  exact add_le_add (mul_le_mul_of_nonneg_left (cube_support hk hw) hA)
    (mul_le_mul_of_nonneg_left (square_support hk) (by positivity))

theorem large_mass_certificate {x : ℝ} (hx : 3 / 2 ≤ x) :
    (3 * x - 2) + (2 * x - 1) / 16 ≤ (7 / 9) * x ^ 3 := by
  have h : 0 ≤ (x - 3 / 2) *
      ((7 / 9) * (x - 3 / 2) ^ 2 + (7 / 2) * (x - 3 / 2) + 17 / 8) := by
    apply mul_nonneg (sub_nonneg.mpr hx)
    have hp := sq_nonneg (x - 3 / 2)
    nlinarith
  nlinarith

theorem outerSupport_le_coarse {k A m w : ℝ}
    (hk : 0 < k) (hA : A ≤ 1) (hm : 48 * k ≤ m)
    (hw : 3 / 2 ≤ k * w) :
    outerSupport k A m w ≤ (7 / 9) * w ^ 3 := by
  have hmpos : 0 < m := by linarith
  have hkm : 3 * k / m ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ hmpos).mpr
    linarith
  have h1 := mul_le_mul_of_nonneg_right hA
    (show 0 ≤ 3 * (k * w) - 2 by linarith)
  have h2 := mul_le_mul_of_nonneg_right hkm
    (show 0 ≤ 2 * (k * w) - 1 by linarith)
  have hc := large_mass_certificate hw
  have heq : outerSupport k A m w * k ^ 3 =
      A * (3 * (k * w) - 2) + (3 * k / m) * (2 * (k * w) - 1) := by
    dsimp [outerSupport]
    field_simp [hk.ne', hmpos.ne'] <;> ring
  apply (mul_le_mul_iff_of_pos_right (pow_pos hk 3)).mp
  rw [heq]
  nlinarith

theorem outerSupport_sum {k : ℕ} (hk : 0 < k) (A m : ℝ)
    (w : Fin k → ℝ) (hw : ProbabilityWeights w) :
    (∑ i, outerSupport (k : ℝ) A m (w i)) =
      A / (k : ℝ) ^ 2 + 3 / (m * (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hp (x : ℝ) : outerSupport (k : ℝ) A m x =
      (3 * A / (k : ℝ) ^ 2 + 6 / (m * (k : ℝ))) * x -
        (2 * A / (k : ℝ) ^ 3 + 3 / (m * (k : ℝ) ^ 2)) := by
    dsimp [outerSupport]
    field_simp [hk0] <;> ring
  simp only [hp, Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk0] <;> ring

/-- A pointwise supporting line valid in both the spectral and coarse branches. -/
theorem raw_part_ge_support {k m w s p : ℝ} (hk : 4 ≤ k) (hm : 48 * k ≤ m)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hs : w ^ 2 / m ≤ s)
    (hcoarse : p ≤ (2 / 9) * w ^ 3)
    (hspectral : p ≤ ((10 * k / 3 - 5 * k / 4) / m) * w ^ 3 +
      (5 * k / 4) * w * s) :
    outerSupport k (1 - (10 * k / 3 + 3) / m) m w ≤
      w ^ 3 + 3 * (1 - w) * s - p := by
  have hkpos : 0 < k := by linarith
  have hmpos : 0 < m := by linarith
  have hs0 : 0 ≤ s := (div_nonneg (sq_nonneg _) hmpos.le).trans hs
  have hA0 : 0 ≤ 1 - (10 * k / 3 + 3) / m := by
    have h : (10 * k / 3 + 3) / m ≤ 1 := (div_le_one hmpos).mpr (by linarith)
    linarith
  have hA1 : 1 - (10 * k / 3 + 3) / m ≤ 1 := by
    have h : 0 ≤ (10 * k / 3 + 3) / m := by positivity
    linarith
  by_cases hsmall : (5 * k / 4 + 3) * w - 3 ≤ 0
  · have hc := mul_le_mul_of_nonpos_left hs hsmall
    have hred : (1 - (10 * k / 3 + 3) / m) * w ^ 3 + (3 / m) * w ^ 2 ≤
        w ^ 3 + 3 * (1 - w) * s - p := by
      have hid : ((10 * k / 3 - 5 * k / 4) / m) * w ^ 3 +
          ((5 * k / 4 + 3) * w - 3) * (w ^ 2 / m) =
          ((10 * k / 3 + 3) / m) * w ^ 3 - (3 / m) * w ^ 2 := by ring
      nlinarith
    exact (outerSupport_le_reduced hkpos hA0 hmpos hw0).trans hred
  · have hwlarge : 3 / 2 ≤ k * w := by
      have hcoef : 5 * k / 4 + 3 ≤ 2 * k := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoef hw0
      linarith
    have hc : 0 ≤ 3 * (1 - w) * s :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hw1)) hs0
    exact (outerSupport_le_coarse hkpos hA1 hm hwlarge).trans (by linarith)

/-- Universal finite outer bound, with no assumed optimizer. -/
theorem weakRawOuter_le {k : ℕ} (hk : 4 ≤ k) {m : ℝ} (hm : 48 * (k : ℝ) ≤ m)
    (w s p : Fin k → ℝ) (hw : ProbabilityWeights w)
    (hs : ∀ i, w i ^ 2 / m ≤ s i)
    (hcoarse : ∀ i, p i ≤ (2 / 9) * w i ^ 3)
    (hspectral : ∀ i, p i ≤ ((10 * (k : ℝ) / 3 - 5 * (k : ℝ) / 4) / m) * w i ^ 3 +
      (5 * (k : ℝ) / 4) * w i * s i) :
    1 - (∑ i, w i ^ 3) - 3 * (∑ i, (1 - w i) * s i) + (∑ i, p i) ≤
      weakOuterValue k m := by
  have hkpos : 0 < k := by omega
  have hkreal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => raw_part_ge_support hkreal hm (hw.1 i) (hw.apply_le_one i)
      (hs i) (hcoarse i) (hspectral i))
  rw [outerSupport_sum hkpos _ _ w hw] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum] at hsum
  have hid : 1 - ((1 - (10 * (k : ℝ) / 3 + 3) / m) / (k : ℝ) ^ 2 +
      3 / (m * (k : ℝ))) = weakOuterValue k m := by
    dsimp [weakOuterValue, weakOuterBase, weakOuterCoefficient]
    field_simp [hk0]
    ring
  linarith

theorem weakOuterCoefficient_pos {k : ℕ} (hk : 0 < k) :
    0 < weakOuterCoefficient k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  dsimp [weakOuterCoefficient]
  positivity

end
end IntervalsTuran.Construction
