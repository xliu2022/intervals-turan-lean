/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.TripartiteEstimate
public import IntervalsTuran.Hypergraph.Lagrangian

/-!
# The finite tripartite Cayley hypergraph

The vertex type consists of three disjoint copies of the finite group.
Its edges are exactly `{(0,x),(1,y),(2,x*s*y)}`. The injective indexing of
these edges proves both their count and the equality of the edge
polynomial with the weighted triple sum from `TripartiteEstimate`.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.FiniteCayley

noncomputable section

def gadgetEdge (G : FiniteCayley) (x y s : G.Vertex) : Finset (Fin 3 × G.Vertex) :=
  {(0, x), (1, y), (2, x * s * y)}

theorem gadgetEdge_card (G : FiniteCayley) (x y s : G.Vertex) :
    (G.gadgetEdge x y s).card = 3 := by
  simp [gadgetEdge]

theorem gadgetEdge_eq_iff (G : FiniteCayley) (x y s x' y' s' : G.Vertex) :
    G.gadgetEdge x y s = G.gadgetEdge x' y' s' ↔ x = x' ∧ y = y' ∧ s = s' := by
  constructor
  · intro h
    have hx : x = x' := by
      have hm : ((0 : Fin 3), x) ∈ G.gadgetEdge x' y' s' := by
        rw [← h]
        simp [gadgetEdge]
      simpa [gadgetEdge] using hm
    have hy : y = y' := by
      have hm : ((1 : Fin 3), y) ∈ G.gadgetEdge x' y' s' := by
        rw [← h]
        simp [gadgetEdge]
      simpa [gadgetEdge] using hm
    have hz : x * s * y = x' * s' * y' := by
      have hm : ((2 : Fin 3), x * s * y) ∈ G.gadgetEdge x' y' s' := by
        rw [← h]
        simp [gadgetEdge]
      simpa [gadgetEdge] using hm
    rw [hx, hy] at hz
    exact ⟨hx, hy, mul_left_cancel (mul_right_cancel hz)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

abbrev EdgeIndex (G : FiniteCayley) := G.Vertex × G.Vertex × ↥G.generators

def indexedEdge (G : FiniteCayley) (t : G.EdgeIndex) : Finset (Fin 3 × G.Vertex) :=
  G.gadgetEdge t.1 t.2.1 t.2.2

theorem indexedEdge_injective (G : FiniteCayley) : Function.Injective G.indexedEdge := by
  rintro ⟨x, y, s⟩ ⟨x', y', s'⟩ h
  obtain ⟨hx, hy, hs⟩ := (G.gadgetEdge_eq_iff x y s x' y' s').mp h
  exact Prod.ext hx (Prod.ext hy (Subtype.ext hs))

def tripartiteGraph (G : FiniteCayley) : RGraph (Fin 3 × G.Vertex) 3 where
  edges := Finset.univ.image G.indexedEdge
  uniform := by
    intro e he
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
    exact G.gadgetEdge_card t.1 t.2.1 t.2.2

theorem tripartiteGraph_vertex_card (G : FiniteCayley) :
    Fintype.card (Fin 3 × G.Vertex) = 3 * G.order := by
  simp [order]

theorem tripartiteGraph_edge_card (G : FiniteCayley) :
    G.tripartiteGraph.edges.card = G.valency * G.order ^ 2 := by
  rw [tripartiteGraph, Finset.card_image_of_injective _ G.indexedEdge_injective]
  simp only [Finset.card_univ, EdgeIndex, Fintype.card_prod, Fintype.card_coe]
  dsimp [valency, order]
  ring

theorem prod_gadgetEdge (G : FiniteCayley) (w : Fin 3 × G.Vertex → ℝ)
    (x y s : G.Vertex) :
    (∏ v ∈ G.gadgetEdge x y s, w v) = w (0, x) * w (1, y) * w (2, x * s * y) := by
  simp [gadgetEdge, mul_assoc]

theorem tripartiteGraph_edgePolynomial (G : FiniteCayley) (w : Fin 3 × G.Vertex → ℝ) :
    G.tripartiteGraph.edgePolynomial w =
      G.tripleSum (fun x => w (0, x)) (fun y => w (1, y)) (fun z => w (2, z)) := by
  unfold RGraph.edgePolynomial tripartiteGraph
  rw [Finset.sum_image (fun a _ b _ hab => G.indexedEdge_injective hab)]
  simp only [indexedEdge, G.prod_gadgetEdge, EdgeIndex, Fintype.sum_prod_type]
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_coe_sort G.generators
    (fun s => w (0, x) * w (1, y) * w (2, x * s * y))

theorem mass_classes (G : FiniteCayley) (w : Fin 3 × G.Vertex → ℝ) :
    G.mass (fun x => w (0, x)) + G.mass (fun y => w (1, y)) +
      G.mass (fun z => w (2, z)) = ∑ v, w v := by
  simp only [mass, Fintype.sum_prod_type, Fin.sum_univ_three]

theorem sum_sq_classes (G : FiniteCayley) (w : Fin 3 × G.Vertex → ℝ) :
    (∑ x, (w (0, x)) ^ 2) + (∑ y, (w (1, y)) ^ 2) + (∑ z, (w (2, z)) ^ 2) =
      ∑ v, (w v) ^ 2 :=
  G.mass_classes (fun v => (w v) ^ 2)

/-- The actual finite hypergraph satisfies the tripartite Lagrangian bound. -/
theorem tripartiteGraph_lagrangian_le (G : FiniteCayley) :
    G.tripartiteGraph.lagrangian ≤ 2 / 9 := by
  apply (G.tripartiteGraph.lagrangian_le_iff (by norm_num)).mpr
  intro w hw
  norm_num only [Nat.factorial] at *
  rw [G.tripartiteGraph_edgePolynomial]
  exact G.normalized_tripleSum_le_two_ninths _ _ _
    (fun x => hw.1 (0, x)) (fun y => hw.1 (1, y)) (fun z => hw.1 (2, z))
    ((G.mass_classes w).trans hw.2)

/-- The spectral polynomial bound of Lemma 3.3, now for the actual graph. -/
theorem tripartiteGraph_normalizedPolynomial_le (G : FiniteCayley) {θ : ℝ}
    (hθ : 0 ≤ θ) (hbound : G.HasZeroSumBound θ)
    (w : Fin 3 × G.Vertex → ℝ) (hw : ProbabilityWeights w) :
    6 * G.tripartiteGraph.edgePolynomial w ≤
      2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) +
        θ * ((∑ v, (w v) ^ 2) - 1 / (3 * (G.order : ℝ))) := by
  rw [G.tripartiteGraph_edgePolynomial]
  have h := G.normalized_tripleSum_le hθ hbound
    (fun x => w (0, x)) (fun y => w (1, y)) (fun z => w (2, z))
    (fun x => hw.1 (0, x)) (fun y => hw.1 (1, y)) (fun z => hw.1 (2, z))
    ((G.mass_classes w).trans hw.2)
  rwa [G.sum_sq_classes] at h

theorem tripartiteGraph_uniform_evaluation (G : FiniteCayley) :
    6 * G.tripartiteGraph.edgePolynomial (fun _ => 1 / (3 * (G.order : ℝ))) =
      2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) := by
  rw [G.tripartiteGraph_edgePolynomial]
  exact G.normalized_tripleSum_uniform

end

end IntervalsTuran.Spectral.FiniteCayley
