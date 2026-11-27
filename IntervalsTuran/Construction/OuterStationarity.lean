/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Hypergraph.Lagrangian
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A linear spectral threshold from stationarity of outer masses

At an actual maximizing weighting of a complete join, the class masses
are O(1/k), with an absolute constant. This improves the coarse O(k^(-2/3))
bound and allows a sufficiently strong fixed normalized expander gap.
All statements below concern an actual minimum of the explicit mass loss.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace IntervalsTuran.Construction

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def outerLoss (s g w : I → ℝ) : ℝ :=
  ∑ i, ((1 - g i - 3 * s i) * w i ^ 3 + 3 * s i * w i ^ 2)

def outerLossSlope (s g w : I → ℝ) (i : I) : ℝ :=
  3 * (1 - g i - 3 * s i) * w i ^ 2 + 6 * s i * w i

def massPerturb (w : I → ℝ) (i : I) (t : ℝ) (j : I) : ℝ :=
  w j + t * (w j - if j = i then 1 else 0)

theorem probabilityWeights_massPerturb {w : I → ℝ}
    (hw : ProbabilityWeights w) {i : I} (hi : 0 < w i) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ProbabilityWeights (massPerturb w i t) := by
  have hfactor : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t := by
    have hc : ContinuousAt (fun t : ℝ => 1 + t) 0 := by fun_prop
    exact hc.eventually (lt_mem_nhds (show (0 : ℝ) < 1 + 0 by norm_num))
  have hcoord : ∀ᶠ t : ℝ in 𝓝 0, 0 < w i + t * (w i - 1) := by
    have hc : ContinuousAt (fun t : ℝ => w i + t * (w i - 1)) 0 := by fun_prop
    exact hc.eventually (lt_mem_nhds (show 0 < w i + 0 * (w i - 1) by simpa using hi))
  filter_upwards [hfactor, hcoord] with t ht hti
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [massPerturb] using hti.le
    · have h := mul_nonneg ht.le (hw.1 j)
      simpa only [massPerturb, if_neg hji, sub_zero, add_mul, one_mul] using h
  · simp only [massPerturb, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hw.2]
    simp

theorem outerLoss_massPerturb_hasDerivAt (s g w : I → ℝ) (i : I) :
    HasDerivAt (fun t => outerLoss s g (massPerturb w i t))
      (∑ j, outerLossSlope s g w j * (w j - if j = i then 1 else 0)) 0 := by
  have hd (j : I) : HasDerivAt (fun t : ℝ => massPerturb w i t j)
      (w j - if j = i then 1 else 0) 0 := by
    simpa [massPerturb] using
      (((hasDerivAt_id (0 : ℝ)).mul_const
        (w j - if j = i then 1 else 0)).const_add (w j))
  have hp (j : I) : HasDerivAt
      (fun t : ℝ => (1 - g j - 3 * s j) * massPerturb w i t j ^ 3 +
        3 * s j * massPerturb w i t j ^ 2)
      (outerLossSlope s g w j * (w j - if j = i then 1 else 0)) 0 := by
    convert (((hd j).pow 3).const_mul (1 - g j - 3 * s j)).add
      (((hd j).pow 2).const_mul (3 * s j)) using 1 <;>
      simp [massPerturb, outerLossSlope] <;> ring
  convert (HasDerivAt.sum (u := Finset.univ) (fun j _ => hp j)) using 1
  funext t
  simp only [outerLoss, Finset.sum_apply]

theorem outerLoss_stationarity (s g w : I → ℝ)
    (hw : ProbabilityWeights w)
    (hmin : ∀ z, ProbabilityWeights z → outerLoss s g w ≤ outerLoss s g z)
    {i : I} (hi : 0 < w i) :
    outerLossSlope s g w i = ∑ j, w j * outerLossSlope s g w j := by
  have hlocal : IsLocalMin (fun t => outerLoss s g (massPerturb w i t)) 0 := by
    filter_upwards [probabilityWeights_massPerturb hw hi] with t ht
    have h0 : massPerturb w i 0 = w := by funext j; simp [massPerturb]
    change outerLoss s g (massPerturb w i 0) ≤ outerLoss s g (massPerturb w i t)
    rw [h0]
    exact hmin _ ht
  have hzero := hlocal.hasDerivAt_eq_zero (outerLoss_massPerturb_hasDerivAt s g w i)
  have heq : (∑ j, outerLossSlope s g w j * (w j - if j = i then 1 else 0)) =
      (∑ j, w j * outerLossSlope s g w j) - outerLossSlope s g w i := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hzero
  linarith

theorem outerLoss_weighted_slope (s g w : I → ℝ) :
    (∑ j, w j * outerLossSlope s g w j) =
      3 * outerLoss s g w - 3 * ∑ j, s j * w j ^ 2 := by
  simp only [outerLoss, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [outerLossSlope]
  ring

theorem outerLoss_coarse_lower (s g w : I → ℝ) (hw : ProbabilityWeights w)
    (hs : ∀ i, 0 ≤ s i) (hg : ∀ i, g i ≤ 2 / 9) :
    (7 / 9) * (∑ i, w i ^ 3) ≤ outerLoss s g w := by
  rw [outerLoss, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hcorr : 0 ≤ 3 * s i * w i ^ 2 * (1 - w i) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hs i)) (sq_nonneg _))
      (sub_nonneg.mpr (hw.apply_le_one i))
  have hcube := mul_nonneg (sub_nonneg.mpr (hg i)) (pow_nonneg (hw.1 i) 3)
  nlinarith

/-- The mass bound uses stationarity at a genuine minimizer, not an additional
assumption about the shape of the optimizer. -/
theorem outerLoss_minimizer_mass_bound {k : ℕ} (hk : 3 ≤ k)
    (s g w : Fin k → ℝ) (hw : ProbabilityWeights w)
    (hs : ∀ i, 0 ≤ s i) (hg : ∀ i, g i ≤ 2 / 9)
    (hmin : ∀ z, ProbabilityWeights z → outerLoss s g w ≤ outerLoss s g z)
    (hsmall : outerLoss s g w ≤ 1 / (k : ℝ) ^ 2) :
    ∀ i, w i ≤ 7 / (6 * (k : ℝ)) := by
  have hkreal : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := sq_pos_of_pos hkpos
  have hnin : 1 / (k : ℝ) ^ 2 ≤ (1 / 9 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hcoarse := outerLoss_coarse_lower s g w hw hs hg
  intro i
  by_cases hi : w i = 0
  · rw [hi]
    positivity
  have hipos : 0 < w i := lt_of_le_of_ne (hw.1 i) (Ne.symm hi)
  have hsingle : w i ^ 3 ≤ ∑ j, w j ^ 3 :=
    Finset.single_le_sum (fun j _ => pow_nonneg (hw.1 j) 3) (Finset.mem_univ i)
  have hi23 : w i < 2 / 3 := by
    by_contra hnot
    have hl : (2 / 3 : ℝ) ≤ w i := le_of_not_gt hnot
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) hl 3
    norm_num at hp
    linarith
  have hstat := outerLoss_stationarity s g w hw hmin hipos
  rw [outerLoss_weighted_slope] at hstat
  have hsum : 0 ≤ ∑ j, s j * w j ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hs j) (sq_nonneg _))
  have hupper : outerLossSlope s g w i ≤ 3 / (k : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 3)
    simp only [mul_one_div] at h
    linarith
  have hlower : (7 / 3) * w i ^ 2 ≤ outerLossSlope s g w i := by
    have hc : 0 ≤ 3 * s i * w i * (2 - 3 * w i) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hs i)) (hw.1 i))
        (by linarith)
    have hgprod := mul_nonneg (sub_nonneg.mpr (hg i)) (sq_nonneg (w i))
    dsimp [outerLossSlope]
    nlinarith
  have hsq : (7 / 3) * w i ^ 2 * (k : ℝ) ^ 2 ≤ 3 :=
    (le_div_iff₀ hk2).mp (hlower.trans hupper)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (k : ℝ))).mpr
  nlinarith [sq_nonneg ((k : ℝ) * w i - 7 / 6)]

end

end IntervalsTuran.Construction
