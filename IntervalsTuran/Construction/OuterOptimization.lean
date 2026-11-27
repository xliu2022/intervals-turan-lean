/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.Parameters
public import IntervalsTuran.Hypergraph.Lagrangian

/-!
# Exact optimization of the fixed-parameter outer construction

For `D = 138` and `k = 30`, the reduced mass polynomial from (3.9) of
Liu--Pikhurko is
`1 - (1 - 95 / m) * sum(w_i^3) - (3 / m) * sum(w_i^2)`.
When `95 ≤ m`, both power-sum coefficients have the required sign, so
the uniform vector attains its exact maximum `899/900 + 1/(180*m)`.
This strengthens the asymptotic optimization used in Proposition 3.6.

The raw-slice estimate uses actual per-part masses, square sums and
internal polynomial values. Its hypotheses are explicit; the complete
join's exact cubic identity and the inner gadget estimates supply them.
No spectral family existence is asserted here.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Construction

noncomputable section

def sumSquares (w : Fin 30 → ℝ) : ℝ := ∑ i, (w i) ^ 2
def sumCubes (w : Fin 30 → ℝ) : ℝ := ∑ i, (w i) ^ 3

def reducedOuter (m : ℝ) (w : Fin 30 → ℝ) : ℝ :=
  1 - (1 - 95 / m) * sumCubes w - (3 / m) * sumSquares w

def outerValue (m : ℝ) : ℝ := Spectral.limitValue + Spectral.firstOrderCoefficient / m

def rawOuter (w s p : Fin 30 → ℝ) : ℝ :=
  1 - sumCubes w - 3 * (∑ i, (1 - w i) * s i) + ∑ i, p i

theorem square_certificate (w : Fin 30 → ℝ) (hw : ProbabilityWeights w) :
    (∑ i, (w i - 1 / 30) ^ 2) = sumSquares w - 1 / 30 := by
  have hp (i : Fin 30) : (w i - 1 / 30) ^ 2 =
      (w i) ^ 2 - (1 / 15) * w i + 1 / 900 := by ring
  simp only [hp, sumSquares, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hw.2]
  ring

theorem cube_certificate (w : Fin 30 → ℝ) (hw : ProbabilityWeights w) :
    (∑ i, (w i - 1 / 30) ^ 2 * (w i + 1 / 15)) = sumCubes w - 1 / 900 := by
  have hp (i : Fin 30) : (w i - 1 / 30) ^ 2 * (w i + 1 / 15) =
      (w i) ^ 3 - (1 / 300) * w i + 1 / 13500 := by ring
  simp only [hp, sumCubes, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hw.2]
  ring

theorem sumSquares_ge (w : Fin 30 → ℝ) (hw : ProbabilityWeights w) :
    1 / 30 ≤ sumSquares w := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 30)))
    (fun i _ => sq_nonneg (w i - 1 / 30))
  rw [square_certificate w hw] at h
  linarith only [h]

theorem sumCubes_ge (w : Fin 30 → ℝ) (hw : ProbabilityWeights w) :
    1 / 900 ≤ sumCubes w := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 30)))
    (fun i _ => mul_nonneg (sq_nonneg (w i - 1 / 30))
      (by linarith [hw.1 i] : 0 ≤ w i + 1 / 15))
  rw [cube_certificate w hw] at h
  linarith only [h]

theorem uniform_of_sumCubes_eq (w : Fin 30 → ℝ) (hw : ProbabilityWeights w)
    (heq : sumCubes w = 1 / 900) : ∀ i, w i = 1 / 30 := by
  have hsum : (∑ i, (w i - 1 / 30) ^ 2 * (w i + 1 / 15)) = 0 := by
    rw [cube_certificate w hw, heq, sub_self]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin 30)),
      0 ≤ (w i - 1 / 30) ^ 2 * (w i + 1 / 15) := by
    intro i _
    exact mul_nonneg (sq_nonneg _) (by linarith [hw.1 i])
  intro i
  have ht := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
  have hpos : 0 < w i + 1 / 15 := by linarith [hw.1 i]
  have hs : (w i - 1 / 30) ^ 2 = 0 := (mul_eq_zero.mp ht).resolve_right (ne_of_gt hpos)
  have hz : w i - 1 / 30 = 0 := (sq_eq_zero_iff).mp hs
  linarith only [hz]

theorem reducedOuter_le (m : ℝ) (hm : 95 ≤ m) (w : Fin 30 → ℝ)
    (hw : ProbabilityWeights w) : reducedOuter m w ≤ outerValue m := by
  have hmpos : 0 < m := by linarith
  have hcoef : 0 ≤ 1 - 95 / m := by
    have hdiv : 95 / m ≤ 1 := (div_le_one hmpos).mpr hm
    linarith
  have h3 := mul_le_mul_of_nonneg_left (sumCubes_ge w hw) hcoef
  have h2 := mul_le_mul_of_nonneg_left (sumSquares_ge w hw)
    (show 0 ≤ 3 / m by positivity)
  calc
    _ ≤ 1 - (1 - 95 / m) * (1 / 900) - (3 / m) * (1 / 30) := by
      unfold reducedOuter
      linarith only [h3, h2]
    _ = _ := by
      unfold outerValue Spectral.limitValue Spectral.firstOrderCoefficient
      ring

theorem uniform_probability : ProbabilityWeights (fun _ : Fin 30 => (1 / 30 : ℝ)) := by
  constructor
  · intro i
    norm_num
  · norm_num

theorem reducedOuter_uniform (m : ℝ) :
    reducedOuter m (fun _ : Fin 30 => 1 / 30) = outerValue m := by
  norm_num [reducedOuter, sumCubes, sumSquares, outerValue,
    Spectral.limitValue, Spectral.firstOrderCoefficient]
  ring

theorem limitValue_lt_outerValue {m : ℝ} (hm : 0 < m) :
    Spectral.limitValue < outerValue m := by
  unfold outerValue
  exact lt_add_of_pos_right _ (div_pos Spectral.firstOrderCoefficient_pos hm)

theorem coefficient_neg_of_cube_le {w : ℝ} (_hw : 0 ≤ w)
    (hcube : w ^ 3 ≤ 1 / 700) : (Spectral.spectralBound + 3) * w - 3 < 0 := by
  have hsmall : w < 6 / 53 := by
    by_contra hnot
    have hle : (6 / 53 : ℝ) ≤ w := le_of_not_gt hnot
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6 / 53) hle 3
    norm_num at hp
    linarith only [hcube, hp]
  norm_num [Spectral.spectralBound]
  linarith only [hsmall]

/-- The coarse bound from tripartiteness of every inner gadget. -/
theorem rawOuter_coarse_le (w s p : Fin 30 → ℝ) (hw : ProbabilityWeights w)
    (hs : ∀ i, 0 ≤ s i) (hp : ∀ i, p i ≤ (2 / 9) * (w i) ^ 3) :
    rawOuter w s p ≤ 1 - (7 / 9) * sumCubes w := by
  have hc : 0 ≤ ∑ i, (1 - w i) * s i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hw.apply_le_one i)) (hs i))
  have hpsum : (∑ i, p i) ≤ (2 / 9) * sumCubes w := by
    simpa only [sumCubes, Finset.mul_sum] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i))
  unfold rawOuter
  linarith only [hc, hpsum]

theorem outer_masses_small (w s p : Fin 30 → ℝ) (hw : ProbabilityWeights w)
    (hs : ∀ i, 0 ≤ s i) (hp : ∀ i, p i ≤ (2 / 9) * (w i) ^ 3)
    (hlarge : Spectral.limitValue ≤ rawOuter w s p) :
    ∀ i, (Spectral.spectralBound + 3) * w i - 3 < 0 := by
  have hcoarse := rawOuter_coarse_le w s p hw hs hp
  have hsum : sumCubes w ≤ 1 / 700 := by
    norm_num [Spectral.limitValue] at hlarge
    linarith only [hcoarse, hlarge]
  intro i
  apply coefficient_neg_of_cube_le (hw.1 i)
  calc
    (w i) ^ 3 ≤ sumCubes w :=
      Finset.single_le_sum (fun j _ => pow_nonneg (hw.1 j) 3) (Finset.mem_univ i)
    _ ≤ _ := hsum

/-- Spectral reduction after every class mass has been bounded. -/
theorem rawOuter_le_reduced (m : ℝ) (w s p : Fin 30 → ℝ)
    (hs : ∀ i, (w i) ^ 2 / m ≤ s i)
    (hp : ∀ i, p i ≤ ((92 - Spectral.spectralBound) / m) * (w i) ^ 3 +
      Spectral.spectralBound * w i * s i)
    (hsmall : ∀ i, (Spectral.spectralBound + 3) * w i - 3 ≤ 0) :
    rawOuter w s p ≤ reducedOuter m w := by
  have hpart (i : Fin 30) : p i - 3 * (1 - w i) * s i ≤
      (95 / m) * (w i) ^ 3 - (3 / m) * (w i) ^ 2 := by
    have hc : ((Spectral.spectralBound + 3) * w i - 3) * s i ≤
        ((Spectral.spectralBound + 3) * w i - 3) * ((w i) ^ 2 / m) :=
      mul_le_mul_of_nonpos_left (hs i) (hsmall i)
    calc
      _ ≤ (((92 - Spectral.spectralBound) / m) * (w i) ^ 3 +
          Spectral.spectralBound * w i * s i) - 3 * (1 - w i) * s i :=
        sub_le_sub_right (hp i) _
      _ = ((92 - Spectral.spectralBound) / m) * (w i) ^ 3 +
          ((Spectral.spectralBound + 3) * w i - 3) * s i := by ring
      _ ≤ ((92 - Spectral.spectralBound) / m) * (w i) ^ 3 +
          ((Spectral.spectralBound + 3) * w i - 3) * ((w i) ^ 2 / m) :=
        add_le_add (le_refl _) hc
      _ = _ := by ring
  calc
    _ = 1 - sumCubes w + ∑ i, (p i - 3 * (1 - w i) * s i) := by
      simp only [rawOuter, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    _ ≤ 1 - sumCubes w + ∑ i, ((95 / m) * (w i) ^ 3 - (3 / m) * (w i) ^ 2) :=
      add_le_add (le_refl _) (Finset.sum_le_sum (fun i _ => hpart i))
    _ = _ := by
      simp only [reducedOuter, sumCubes, sumSquares, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring

/-- Exact universal upper bound for the outer construction from its raw
slice data. No existence of an optimizing weighting is needed. -/
theorem rawOuter_le (m : ℝ) (hm : 95 ≤ m) (w s p : Fin 30 → ℝ)
    (hw : ProbabilityWeights w)
    (hs : ∀ i, (w i) ^ 2 / m ≤ s i)
    (hpcoarse : ∀ i, p i ≤ (2 / 9) * (w i) ^ 3)
    (hpspectral : ∀ i, p i ≤ ((92 - Spectral.spectralBound) / m) * (w i) ^ 3 +
      Spectral.spectralBound * w i * s i) :
    rawOuter w s p ≤ outerValue m := by
  have hmpos : 0 < m := by linarith
  by_cases hlarge : Spectral.limitValue ≤ rawOuter w s p
  · have hsnonneg : ∀ i, 0 ≤ s i := fun i =>
      (div_nonneg (sq_nonneg _) hmpos.le).trans (hs i)
    exact (rawOuter_le_reduced m w s p hs hpspectral
      (fun i => (outer_masses_small w s p hw hsnonneg hpcoarse hlarge i).le)).trans
        (reducedOuter_le m hm w hw)
  · exact (lt_of_not_ge hlarge).le.trans (limitValue_lt_outerValue hmpos).le

end

end IntervalsTuran.Construction
