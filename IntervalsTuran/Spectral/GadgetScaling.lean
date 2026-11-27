/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.TripartiteGraph
public import IntervalsTuran.Spectrum.SubstitutionValue

/-!
# Raw slice inequalities for the tripartite gadget

Homogeneity extends the probability-weight estimates to arbitrary
nonnegative slice weights, including zero total mass. These are exactly
the hypotheses consumed by `Construction.rawOuter_le`.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.FiniteCayley

noncomputable section

theorem tripartiteGraph_raw_coarse_le (G : FiniteCayley)
    (x : Fin 3 × G.Vertex → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * G.tripartiteGraph.edgePolynomial x ≤ (2 / 9) * (∑ v, x v) ^ 3 := by
  have h := Spectrum.normalizedPolynomial_le_mass G.tripartiteGraph (by omega) x hx
  norm_num only [Nat.factorial] at h
  exact h.trans (mul_le_mul_of_nonneg_right G.tripartiteGraph_lagrangian_le
    (pow_nonneg (Finset.sum_nonneg (fun v _ => hx v)) 3))

theorem tripartiteGraph_raw_spectral_le (G : FiniteCayley) {θ : ℝ}
    (hθ : 0 ≤ θ) (hbound : G.HasZeroSumBound θ)
    (x : Fin 3 × G.Vertex → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * G.tripartiteGraph.edgePolynomial x ≤
      (2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) - θ / (3 * (G.order : ℝ))) *
          (∑ v, x v) ^ 3 + θ * (∑ v, x v) * (∑ v, (x v) ^ 2) := by
  let t : ℝ := ∑ v, x v
  have ht : 0 ≤ t := Finset.sum_nonneg (fun v _ => hx v)
  change 6 * G.tripartiteGraph.edgePolynomial x ≤
    (2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) - θ / (3 * (G.order : ℝ))) * t ^ 3 +
      θ * t * (∑ v, (x v) ^ 2)
  by_cases hz : t = 0
  · have hzero : x = fun _ => 0 := by
      funext v
      have hv : x v ≤ t := Finset.single_le_sum (fun u _ => hx u) (Finset.mem_univ v)
      exact le_antisymm (by simpa only [hz] using hv) (hx v)
    rw [hzero, G.tripartiteGraph.edgePolynomial_uniform, hz]
    norm_num
  · let y : Fin 3 × G.Vertex → ℝ := fun v => t⁻¹ * x v
    have hy : ProbabilityWeights y := by
      refine ⟨fun v => mul_nonneg (inv_nonneg.mpr ht) (hx v), ?_⟩
      dsimp only [y]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hz
    have hscale : x = fun v => t * y v := by
      funext v
      dsimp only [y]
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    have hsq : (∑ v, (y v) ^ 2) = t⁻¹ ^ 2 * (∑ v, (x v) ^ 2) := by
      simp only [y, mul_pow, Finset.mul_sum]
    have h := G.tripartiteGraph_normalizedPolynomial_le hθ hbound y hy
    rw [hsq] at h
    calc
      _ = t ^ 3 * (6 * G.tripartiteGraph.edgePolynomial y) := by
        conv_lhs => rw [hscale, G.tripartiteGraph.edgePolynomial_scale]
        ring
      _ ≤ t ^ 3 * (2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) +
          θ * (t⁻¹ ^ 2 * (∑ v, (x v) ^ 2) - 1 / (3 * (G.order : ℝ)))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg ht 3)
      _ = _ := by
        field_simp [hz, G.order_real_ne_zero]
        ring

/-- Cauchy--Schwarz for a slice on the three group copies. -/
theorem tripartiteGraph_square_mass_le (G : FiniteCayley)
    (x : Fin 3 × G.Vertex → ℝ) :
    (∑ v, x v) ^ 2 / (3 * (G.order : ℝ)) ≤ ∑ v, (x v) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hm : 0 < 3 * (G.order : ℝ) := by
    have hn : (0 : ℝ) < G.order := by exact_mod_cast G.order_pos
    positivity
  apply (div_le_iff₀ hm).mpr
  have hcard : (Fintype.card (Fin 3 × G.Vertex) : ℝ) = 3 * (G.order : ℝ) := by
    exact_mod_cast G.tripartiteGraph_vertex_card
  rw [hcard] at h
  simpa only [mul_one, mul_comm] using h

/-- Numerical specialization matching the raw outer optimization. -/
theorem tripartiteGraph_raw_fixed_spectral_le (G : FiniteCayley)
    (hdegree : G.valency = degree) (hbound : G.HasZeroSumBound spectralBound)
    (x : Fin 3 × G.Vertex → ℝ) (hx : ∀ v, 0 ≤ x v) :
    6 * G.tripartiteGraph.edgePolynomial x ≤
      ((92 - spectralBound) / (3 * (G.order : ℝ))) * (∑ v, x v) ^ 3 +
        spectralBound * (∑ v, x v) * (∑ v, (x v) ^ 2) := by
  have h := G.tripartiteGraph_raw_spectral_le spectralBound_pos.le hbound x hx
  rw [hdegree] at h
  convert h using 1
  unfold degree
  push_cast
  ring

end

end IntervalsTuran.Spectral.FiniteCayley
