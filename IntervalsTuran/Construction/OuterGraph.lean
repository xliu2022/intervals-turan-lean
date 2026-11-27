/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Construction.CompleteJoinCubic
public import IntervalsTuran.Construction.OuterOptimization
public import IntervalsTuran.Spectral.GadgetScaling

/-!
# Exact Lagrangian of the fixed-parameter outer graph

For a finite Cayley graph with valency `138` and zero-sum operator bound
`47/2`, take the complete join of thirty copies of its tripartite gadget.
Once the gadget has at least `95` vertices, its Lagrangian is exactly
`899/900 + 1/(180*m)`, where `m` is the gadget order. This strengthens the
asymptotic conclusion in Proposition 3.6 for the paper's explicit fixed
parameters. The existence of a smooth family of such Cayley graphs remains
a separate input.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.FiniteCayley

noncomputable section

def outerGraph (G : FiniteCayley) : RGraph (Fin 30 × (Fin 3 × G.Vertex)) 3 :=
  G.tripartiteGraph.completeJoin (Fin 30)

theorem outerGraph_vertex_card (G : FiniteCayley) :
    Fintype.card (Fin 30 × (Fin 3 × G.Vertex)) = 90 * G.order := by
  simp only [Fintype.card_prod, Fintype.card_fin, order]
  ring

theorem outerGraph_normalizedPolynomial_le (G : FiniteCayley)
    (hdegree : G.valency = degree) (hbound : G.HasZeroSumBound spectralBound)
    (horder : 95 ≤ 3 * (G.order : ℝ))
    (x : Fin 30 × (Fin 3 × G.Vertex) → ℝ) (hx : ProbabilityWeights x) :
    6 * G.outerGraph.edgePolynomial x ≤ Construction.outerValue (3 * (G.order : ℝ)) := by
  have hw : ProbabilityWeights (fun i : Fin 30 => ∑ v, x (i, v)) := by
    refine ⟨fun i => Finset.sum_nonneg (fun v _ => hx.1 (i, v)), ?_⟩
    simpa only [Fintype.sum_prod_type] using hx.2
  have h := Construction.rawOuter_le (3 * (G.order : ℝ)) horder
    (fun i => ∑ v, x (i, v))
    (fun i => ∑ v, x (i, v) ^ 2)
    (fun i => 6 * G.tripartiteGraph.edgePolynomial (fun v => x (i, v))) hw
    (fun i => G.tripartiteGraph_square_mass_le (fun v => x (i, v)))
    (fun i => G.tripartiteGraph_raw_coarse_le (fun v => x (i, v)) (fun v => hx.1 (i, v)))
    (fun i => G.tripartiteGraph_raw_fixed_spectral_le hdegree hbound
      (fun v => x (i, v)) (fun v => hx.1 (i, v)))
  rw [outerGraph, G.tripartiteGraph.completeJoin_three_polynomial x hx]
  exact h

theorem outerGraph_uniform_probability (G : FiniteCayley) :
    ProbabilityWeights
      (fun _ : Fin 30 × (Fin 3 × G.Vertex) => (30 * (3 * (G.order : ℝ)))⁻¹) := by
  have hcard : (Fintype.card (Fin 30 × (Fin 3 × G.Vertex)) : ℝ) =
      30 * (3 * (G.order : ℝ)) := by
    simp [order]
  simpa only [hcard] using
    (probabilityWeights_uniform (V := Fin 30 × (Fin 3 × G.Vertex)))

theorem outerGraph_uniform_evaluation (G : FiniteCayley) (hdegree : G.valency = degree) :
    6 * G.outerGraph.edgePolynomial
      (fun _ => (30 * (3 * (G.order : ℝ)))⁻¹) =
        Construction.outerValue (3 * (G.order : ℝ)) := by
  rw [outerGraph, G.tripartiteGraph.completeJoin_three_polynomial _
    G.outerGraph_uniform_probability]
  simp only [G.tripartiteGraph.edgePolynomial_uniform, G.tripartiteGraph_edge_card,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, hdegree, degree, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change 1 - (30 : ℝ) * ((3 * (G.order : ℝ)) * (30 * (3 * (G.order : ℝ)))⁻¹) ^ 3 -
      3 * (30 * ((1 - (3 * (G.order : ℝ)) * (30 * (3 * (G.order : ℝ)))⁻¹) *
        ((3 * (G.order : ℝ)) * ((30 * (3 * (G.order : ℝ)))⁻¹) ^ 2))) +
      30 * (6 * (138 * (G.order : ℝ) ^ 2 * ((30 * (3 * (G.order : ℝ)))⁻¹) ^ 3)) = _
  unfold Construction.outerValue limitValue firstOrderCoefficient
  field_simp [G.order_real_ne_zero]
  ring

/-- The exact fixed-parameter version of Proposition 3.6. -/
theorem outerGraph_lagrangian (G : FiniteCayley)
    (hdegree : G.valency = degree) (hbound : G.HasZeroSumBound spectralBound)
    (horder : 95 ≤ 3 * (G.order : ℝ)) :
    G.outerGraph.lagrangian = Construction.outerValue (3 * (G.order : ℝ)) := by
  have horderpos : 0 < 3 * (G.order : ℝ) := by linarith
  apply le_antisymm
  · apply (G.outerGraph.lagrangian_le_iff
      ((limitValue_pos.le).trans (Construction.limitValue_lt_outerValue horderpos).le)).mpr
    intro x hx
    norm_num only [Nat.factorial]
    exact G.outerGraph_normalizedPolynomial_le hdegree hbound horder x hx
  · rw [← G.outerGraph_uniform_evaluation hdegree]
    have h := G.outerGraph.normalizedPolynomial_le_lagrangian _ G.outerGraph_uniform_probability
    norm_num only [Nat.factorial] at h
    exact h

theorem valency_le_order (G : FiniteCayley) : G.valency ≤ G.order := by
  simpa only [valency, order, Finset.card_univ] using
    Finset.card_le_card (Finset.subset_univ G.generators)

/-- The size threshold is automatic for a generator set of size `138`. -/
theorem gadget_order_large_of_degree (G : FiniteCayley) (hdegree : G.valency = degree) :
    95 ≤ 3 * (G.order : ℝ) := by
  have hn := G.valency_le_order
  rw [hdegree] at hn
  have hnreal : (138 : ℝ) ≤ (G.order : ℝ) := by
    exact_mod_cast hn
  linarith only [hnreal]

theorem outerGraph_lagrangian_of_spectral (G : FiniteCayley)
    (hdegree : G.valency = degree) (hbound : G.HasZeroSumBound spectralBound) :
    G.outerGraph.lagrangian = Construction.outerValue (3 * (G.order : ℝ)) :=
  G.outerGraph_lagrangian hdegree hbound (G.gadget_order_large_of_degree hdegree)

end

end IntervalsTuran.Spectral.FiniteCayley
