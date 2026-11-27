/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.AdditiveTripartite
public import IntervalsTuran.Spectrum.SubstitutionValue

/-!
# Homogeneous bounds for the additive tripartite gadget

The probability-weight estimates extend to every nonnegative slice,
including slices with zero total mass.  The last theorem uses the weak
expander parameters of the elementary construction.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.BipartiteKernel

noncomputable section

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem tripartiteGraph_raw_coarse_le (B : BipartiteKernel V)
    (x : Fin 3 × V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * B.tripartiteGraph.edgePolynomial x ≤ (2 / 9) * (∑ v, x v) ^ 3 := by
  have h := Spectrum.normalizedPolynomial_le_mass B.tripartiteGraph (by omega) x hx
  norm_num only [Nat.factorial] at h
  exact h.trans (mul_le_mul_of_nonneg_right B.tripartiteGraph_lagrangian_le
    (pow_nonneg (Finset.sum_nonneg (fun v _ => hx v)) 3))

theorem tripartiteGraph_raw_spectral_le (B : BipartiteKernel V) {θ : ℝ}
    (hθ : 0 ≤ θ) (hbound : B.HasZeroSumBound θ)
    (x : Fin 3 × V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * B.tripartiteGraph.edgePolynomial x ≤
      (2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) -
          (3 * θ / 2) / (3 * (Fintype.card V : ℝ))) * (∑ v, x v) ^ 3 +
        (3 * θ / 2) * (∑ v, x v) * (∑ v, x v ^ 2) := by
  let t : ℝ := ∑ v, x v
  have ht : 0 ≤ t := Finset.sum_nonneg (fun v _ => hx v)
  change 6 * B.tripartiteGraph.edgePolynomial x ≤
    (2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) -
        (3 * θ / 2) / (3 * (Fintype.card V : ℝ))) * t ^ 3 +
      (3 * θ / 2) * t * (∑ v, x v ^ 2)
  by_cases hz : t = 0
  · have hzero : x = fun _ => 0 := by
      funext v
      have hv : x v ≤ t := Finset.single_le_sum (fun u _ => hx u) (Finset.mem_univ v)
      exact le_antisymm (by simpa only [hz] using hv) (hx v)
    rw [hzero, B.tripartiteGraph.edgePolynomial_uniform, hz]
    norm_num
  · let y : Fin 3 × V → ℝ := fun v => t⁻¹ * x v
    have hy : ProbabilityWeights y := by
      refine ⟨fun v => mul_nonneg (inv_nonneg.mpr ht) (hx v), ?_⟩
      dsimp only [y]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hz
    have hscale : x = fun v => t * y v := by
      funext v
      dsimp only [y]
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    have hsq : (∑ v, y v ^ 2) = t⁻¹ ^ 2 * (∑ v, x v ^ 2) := by
      simp only [y, mul_pow, Finset.mul_sum]
    have h := B.tripartiteGraph_normalizedPolynomial_le hθ hbound y hy
    rw [hsq] at h
    calc
      _ = t ^ 3 * (6 * B.tripartiteGraph.edgePolynomial y) := by
        conv_lhs => rw [hscale, B.tripartiteGraph.edgePolynomial_scale]
        ring
      _ ≤ t ^ 3 * (2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) +
          (3 * θ / 2) * (t⁻¹ ^ 2 * (∑ v, x v ^ 2) -
            1 / (3 * (Fintype.card V : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg ht 3)
      _ = _ := by
        field_simp [hz, card_real_ne_zero (V := V)]
        ring

theorem tripartiteGraph_square_mass_le (B : BipartiteKernel V) (x : Fin 3 × V → ℝ) :
    (∑ v, x v) ^ 2 / (3 * (Fintype.card V : ℝ)) ≤ ∑ v, x v ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hm : 0 < 3 * (Fintype.card V : ℝ) := by
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
    positivity
  apply (div_le_iff₀ hm).mpr
  have hcard : (Fintype.card (Fin 3 × V) : ℝ) = 3 * (Fintype.card V : ℝ) := by
    exact_mod_cast B.tripartiteGraph_vertex_card
  rw [hcard] at h
  simpa only [mul_one, mul_comm] using h

/-- The exact parameter form used by the derivative-free outer bound. -/
theorem tripartiteGraph_raw_weak_spectral_le (B : BipartiteKernel V) (k : ℕ)
    (hdegree : B.valency = 5 * k)
    (hbound : B.HasZeroSumBound ((5 * (k : ℝ)) / 6))
    (x : Fin 3 × V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * B.tripartiteGraph.edgePolynomial x ≤
      ((10 * (k : ℝ) / 3 - 5 * (k : ℝ) / 4) / (3 * (Fintype.card V : ℝ))) *
          (∑ v, x v) ^ 3 + (5 * (k : ℝ) / 4) * (∑ v, x v) * (∑ v, x v ^ 2) := by
  have h := B.tripartiteGraph_raw_spectral_le
    (show 0 ≤ (5 * (k : ℝ)) / 6 by positivity) hbound x hx
  rw [hdegree] at h
  convert h using 1 <;> push_cast <;> ring

end

end IntervalsTuran.Spectral.BipartiteKernel
