/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.BipartiteKernel

/-!
# Relabeling finite bipartite kernels

An equivalence of vertex sets preserves actual adjacency, regularity and
the zero-sum operator bound. This permits a simple kernel to be carried
to a finite cyclic group without imposing a group structure on its original
vertex set.
-/

@[expose] public section

namespace IntervalsTuran.Spectral.BipartiteKernel

open scoped BigOperators

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def relabelNeighbors (B : BipartiteKernel V) (e : V ≃ W) (w : W) : Finset W :=
  (B.neighbors (e.symm w)).image e

omit [Fintype W] in
theorem mem_relabelNeighbors (B : BipartiteKernel V) (e : V ≃ W) (w z : W) :
    z ∈ relabelNeighbors B e w ↔ e.symm z ∈ B.neighbors (e.symm w) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨v, hv, rfl⟩
    simpa using hv
  · intro h
    exact Finset.mem_image.mpr ⟨e.symm z, h, e.apply_symm_apply z⟩

omit [Fintype W] in
theorem relabelNeighbors_card (B : BipartiteKernel V) (e : V ≃ W) (w : W) :
    (relabelNeighbors B e w).card = B.valency := by
  rw [relabelNeighbors, Finset.card_image_of_injective _ e.injective]
  exact B.left_regular _

theorem incoming_relabelNeighbors (B : BipartiteKernel V) (e : V ≃ W) (z : W) :
    Finset.univ.filter (fun w => z ∈ relabelNeighbors B e w) =
      (Finset.univ.filter (fun v => e.symm z ∈ B.neighbors v)).image e := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_relabelNeighbors,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨e.symm w, h, e.apply_symm_apply w⟩
  · rintro ⟨v, hv, rfl⟩
    simpa using hv

/-- Transport of the finite relation along an equivalence. -/
def relabel (B : BipartiteKernel V) (e : V ≃ W) : BipartiteKernel W where
  neighbors := relabelNeighbors B e
  valency := B.valency
  left_regular := relabelNeighbors_card B e
  right_regular := by
    intro z
    rw [incoming_relabelNeighbors, Finset.card_image_of_injective _ e.injective]
    exact B.right_regular _

@[simp] theorem relabel_valency (B : BipartiteKernel V) (e : V ≃ W) :
    (B.relabel e).valency = B.valency := rfl

theorem relabel_adjacency (B : BipartiteKernel V) (e : V ≃ W) (f : W → ℝ) (w : W) :
    (B.relabel e).adjacency f w = B.adjacency (fun v => f (e v)) (e.symm w) := by
  exact Finset.sum_image (fun a _ b _ h => e.injective h)

theorem sum_sq_relabel_adjacency (B : BipartiteKernel V) (e : V ≃ W) (f : W → ℝ) :
    ∑ w, ((B.relabel e).adjacency f w)^2 =
      ∑ v, (B.adjacency (fun u => f (e u)) v)^2 := by
  simp only [relabel_adjacency]
  exact Equiv.sum_comp e.symm (fun v => (B.adjacency (fun u => f (e u)) v)^2)

theorem hasZeroSumBound_relabel (B : BipartiteKernel V) (e : V ≃ W) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) : (B.relabel e).HasZeroSumBound θ := by
  intro f hf
  have hzero : ∑ v, f (e v) = 0 := by rw [Equiv.sum_comp e, hf]
  have hb := hbound (fun v => f (e v)) hzero
  unfold l2Norm at hb ⊢
  rw [sum_sq_relabel_adjacency]
  have hs : (∑ v, (f (e v))^2) = ∑ w, (f w)^2 :=
    Equiv.sum_comp e (fun w => (f w)^2)
  rwa [hs] at hb

end IntervalsTuran.Spectral.BipartiteKernel
