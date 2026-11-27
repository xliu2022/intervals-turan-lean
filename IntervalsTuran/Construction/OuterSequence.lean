/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Construction.OuterGraph
public import IntervalsTuran.Hypergraph.Relabel
public import IntervalsTuran.Hypergraph.LagrangianHom

/-!
# The actual smooth outer graph sequence

Every conclusion in this file is conditional only on a
`SmoothSpectralFamily`. The sequence consists of actual finite simple
three-graphs, relabeled on `Fin`. Their Lagrangians have an exact formula,
which directly yields strict decrease, the limit, and the adjacent-gap
ratio. No subsequence or perturbation asymptotic is needed.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran.Spectral

noncomputable section

namespace FiniteCayley

def outerFiniteGraph (G : FiniteCayley) : FiniteGraph 3 :=
  ⟨Fintype.card (Fin 30 × (Fin 3 × G.Vertex)),
    G.outerGraph.pullback (Fintype.equivFin (Fin 30 × (Fin 3 × G.Vertex))).symm.toEmbedding⟩

theorem outerFiniteGraph_lagrangian (G : FiniteCayley) :
    G.outerFiniteGraph.2.lagrangian = G.outerGraph.lagrangian := by
  let e : Fin (Fintype.card (Fin 30 × (Fin 3 × G.Vertex))) ≃
      Fin 30 × (Fin 3 × G.Vertex) := (Fintype.equivFin _).symm
  exact le_antisymm
    (RGraph.IsHom.lagrangian_le (G.outerGraph.pullback_equiv_embedding e).2)
    (RGraph.IsHom.lagrangian_le (G.outerGraph.pullback_equiv_inverse e).2)

end FiniteCayley

namespace SmoothSpectralFamily

def outerSequence (F : SmoothSpectralFamily) (j : ℕ) : FiniteGraph 3 :=
  (F.graph j).outerFiniteGraph

theorem outerSequence_lagrangian (F : SmoothSpectralFamily) (j : ℕ) :
    (F.outerSequence j).2.lagrangian =
      Construction.outerValue (3 * ((F.graph j).order : ℝ)) := by
  rw [outerSequence, FiniteCayley.outerFiniteGraph_lagrangian]
  exact (F.graph j).outerGraph_lagrangian_of_spectral (F.valency_eq j) (F.zeroSum_bound j)

theorem limitValue_lt_outerSequence (F : SmoothSpectralFamily) (j : ℕ) :
    limitValue < (F.outerSequence j).2.lagrangian := by
  rw [F.outerSequence_lagrangian]
  apply Construction.limitValue_lt_outerValue
  have hn : (0 : ℝ) < (F.graph j).order := by exact_mod_cast (F.graph j).order_pos
  positivity

theorem outerSequence_strictAnti (F : SmoothSpectralFamily) :
    StrictAnti (fun j => (F.outerSequence j).2.lagrangian) := by
  intro i j hij
  change (F.outerSequence j).2.lagrangian < (F.outerSequence i).2.lagrangian
  rw [F.outerSequence_lagrangian, F.outerSequence_lagrangian]
  unfold Construction.outerValue
  have hn : (0 : ℝ) < (F.graph i).order := by exact_mod_cast (F.graph i).order_pos
  have hnij : ((F.graph i).order : ℝ) < (F.graph j).order := by
    exact_mod_cast F.order_strictMono hij
  have hdiv := div_lt_div_of_pos_left firstOrderCoefficient_pos
    (mul_pos (show (0 : ℝ) < 3 by norm_num) hn)
    (mul_lt_mul_of_pos_left hnij (by norm_num : (0 : ℝ) < 3))
  linarith only [hdiv]

theorem outerSequence_tendsto (F : SmoothSpectralFamily) :
    Tendsto (fun j => (F.outerSequence j).2.lagrangian) atTop (𝓝 limitValue) := by
  have hm : Tendsto (fun j => 3 * ((F.graph j).order : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) F.order_tendsto
  have hinv : Tendsto (fun j => (3 * ((F.graph j).order : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hm
  have h := (tendsto_const_nhds (x := limitValue)).add
    ((tendsto_const_nhds (x := firstOrderCoefficient)).mul hinv)
  simpa only [F.outerSequence_lagrangian, Construction.outerValue,
    div_eq_mul_inv, mul_zero, add_zero] using h

theorem outerSequence_gap_ratio (F : SmoothSpectralFamily) (j : ℕ) :
    ((F.outerSequence j).2.lagrangian - limitValue) /
      ((F.outerSequence (j + 1)).2.lagrangian - limitValue) =
        ((F.graph (j + 1)).order : ℝ) / ((F.graph j).order : ℝ) := by
  rw [F.outerSequence_lagrangian, F.outerSequence_lagrangian]
  unfold Construction.outerValue firstOrderCoefficient
  field_simp [(F.graph j).order_real_ne_zero, (F.graph (j + 1)).order_real_ne_zero]
  ring

theorem outerSequence_gap_ratio_tendsto (F : SmoothSpectralFamily) :
    Tendsto (fun j => ((F.outerSequence j).2.lagrangian - limitValue) /
      ((F.outerSequence (j + 1)).2.lagrangian - limitValue)) atTop (𝓝 1) := by
  simpa only [F.outerSequence_gap_ratio] using F.consecutive_ratio_tendsto

/-- Theorem 3.1's finite-graph conclusions from the precisely isolated
spectral existence input. -/
theorem exists_smooth_finite_lagrangians (F : SmoothSpectralFamily) :
    ∃ Q : ℕ → FiniteGraph 3,
      (∀ j, limitValue < (Q j).2.lagrangian) ∧
      StrictAnti (fun j => (Q j).2.lagrangian) ∧
      Tendsto (fun j => (Q j).2.lagrangian) atTop (𝓝 limitValue) ∧
      Tendsto (fun j => ((Q j).2.lagrangian - limitValue) /
        ((Q (j + 1)).2.lagrangian - limitValue)) atTop (𝓝 1) :=
  ⟨F.outerSequence, F.limitValue_lt_outerSequence, F.outerSequence_strictAnti,
    F.outerSequence_tendsto, F.outerSequence_gap_ratio_tendsto⟩

end SmoothSpectralFamily

end

end IntervalsTuran.Spectral
