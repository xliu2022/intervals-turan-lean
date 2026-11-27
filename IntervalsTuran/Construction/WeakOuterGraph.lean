/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Construction.CompleteJoinCubic
public import IntervalsTuran.Construction.WeakOuterOptimization
public import IntervalsTuran.Spectral.AdditiveGadgetScaling

/-!
# Exact finite outer graphs from a simple bipartite expander

The graph has k equal copies of the actual additive tripartite gadget.
All upper bounds apply to arbitrary probability weightings, and uniform
weights attain the bound. This route needs only a 1/6 normalized gap.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.BipartiteKernel

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def weakOuterGraph (B : BipartiteKernel V) (k : ℕ) :
    RGraph (Fin k × (Fin 3 × V)) 3 :=
  B.tripartiteGraph.completeJoin (Fin k)

theorem weakOuterGraph_normalizedPolynomial_le (B : BipartiteKernel V)
    {k : ℕ} (hk : 4 ≤ k) (hdegree : B.valency = 5 * k)
    (hbound : B.HasZeroSumBound ((5 * (k : ℝ)) / 6))
    (horder : 48 * (k : ℝ) ≤ 3 * (Fintype.card V : ℝ))
    (x : Fin k × (Fin 3 × V) → ℝ) (hx : ProbabilityWeights x) :
    6 * (B.weakOuterGraph k).edgePolynomial x ≤
      Construction.weakOuterValue k (3 * (Fintype.card V : ℝ)) := by
  have hw : ProbabilityWeights (fun i : Fin k => ∑ v, x (i, v)) := by
    refine ⟨fun i => Finset.sum_nonneg (fun v _ => hx.1 (i, v)), ?_⟩
    simpa only [Fintype.sum_prod_type] using hx.2
  have h := Construction.weakRawOuter_le hk horder
    (fun i => ∑ v, x (i, v))
    (fun i => ∑ v, x (i, v) ^ 2)
    (fun i => 6 * B.tripartiteGraph.edgePolynomial (fun v => x (i, v))) hw
    (fun i => B.tripartiteGraph_square_mass_le (fun v => x (i, v)))
    (fun i => B.tripartiteGraph_raw_coarse_le (fun v => x (i, v)) (fun v => hx.1 (i, v)))
    (fun i => B.tripartiteGraph_raw_weak_spectral_le k hdegree hbound
      (fun v => x (i, v)) (fun v => hx.1 (i, v)))
  rw [weakOuterGraph, B.tripartiteGraph.completeJoin_three_polynomial x hx]
  exact h

theorem weakOuterGraph_uniform_probability (B : BipartiteKernel V)
    {k : ℕ} (hk : 0 < k) :
    ProbabilityWeights (fun _ : Fin k × (Fin 3 × V) =>
      ((k : ℝ) * (3 * (Fintype.card V : ℝ)))⁻¹) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hcard : (Fintype.card (Fin k × (Fin 3 × V)) : ℝ) =
      (k : ℝ) * (3 * (Fintype.card V : ℝ)) := by
    simp
  simpa only [hcard] using
    (probabilityWeights_uniform (V := Fin k × (Fin 3 × V)))

theorem weakOuterGraph_uniform_evaluation (B : BipartiteKernel V)
    {k : ℕ} (hk : 0 < k) (hdegree : B.valency = 5 * k) :
    6 * (B.weakOuterGraph k).edgePolynomial
      (fun _ => ((k : ℝ) * (3 * (Fintype.card V : ℝ)))⁻¹) =
        Construction.weakOuterValue k (3 * (Fintype.card V : ℝ)) := by
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card V))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [weakOuterGraph, B.tripartiteGraph.completeJoin_three_polynomial _
    (B.weakOuterGraph_uniform_probability hk)]
  simp only [B.tripartiteGraph.edgePolynomial_uniform, B.tripartiteGraph_edge_card,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, hdegree, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  dsimp [Construction.weakOuterValue, Construction.weakOuterBase,
    Construction.weakOuterCoefficient]
  field_simp [hk0, hn0]
  ring

theorem weakOuterGraph_lagrangian (B : BipartiteKernel V)
    {k : ℕ} (hk : 4 ≤ k) (hdegree : B.valency = 5 * k)
    (hbound : B.HasZeroSumBound ((5 * (k : ℝ)) / 6))
    (horder : 48 * (k : ℝ) ≤ 3 * (Fintype.card V : ℝ)) :
    (B.weakOuterGraph k).lagrangian =
      Construction.weakOuterValue k (3 * (Fintype.card V : ℝ)) := by
  have hkpos : 0 < k := by omega
  have hnonneg : 0 ≤ Construction.weakOuterValue k (3 * (Fintype.card V : ℝ)) := by
    rw [← B.weakOuterGraph_uniform_evaluation hkpos hdegree]
    exact mul_nonneg (by norm_num)
      ((B.weakOuterGraph k).edgePolynomial_nonneg
        (B.weakOuterGraph_uniform_probability hkpos).1)
  apply le_antisymm
  · apply ((B.weakOuterGraph k).lagrangian_le_iff hnonneg).mpr
    intro x hx
    norm_num only [Nat.factorial]
    exact B.weakOuterGraph_normalizedPolynomial_le hk hdegree hbound horder x hx
  · rw [← B.weakOuterGraph_uniform_evaluation hkpos hdegree]
    have h := (B.weakOuterGraph k).normalizedPolynomial_le_lagrangian _
      (B.weakOuterGraph_uniform_probability hkpos)
    norm_num only [Nat.factorial] at h
    exact h

end
end IntervalsTuran.Spectral.BipartiteKernel
