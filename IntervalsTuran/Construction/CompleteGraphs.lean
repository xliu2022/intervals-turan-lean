module

public import IntervalsTuran.Turan.LagrangianCap

/-!
# Complete finite hypergraphs and the endpoint densities

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran

namespace RGraph

def complete (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) : RGraph V r where
  edges := Finset.univ.powersetCard r
  uniform := fun _ he => (Finset.mem_powersetCard.mp he).2

@[simp] theorem complete_edge_card (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    (complete V r).edges.card = (Fintype.card V).choose r := by
  simp [complete]

@[simp] theorem lagrangian_empty (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) :
    (empty V r).lagrangian = 0 := by
  apply le_antisymm _ (empty V r).lagrangian_nonneg
  apply ((empty V r).lagrangian_le_iff (le_refl 0)).mpr
  intro x hx
  simp [edgePolynomial, empty]

theorem samplingFactor_le_complete_lagrangian (r n : ℕ) (hn : 0 < n) :
    samplingFactor r n ≤ (complete (Fin n) r).lagrangian := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := (complete (Fin n) r).normalizedPolynomial_le_lagrangian _
    probabilityWeights_uniform
  rw [← oneEdge_homDensity_polynomial, oneEdge_homDensity] at h
  simpa [samplingFactor] using h

theorem complete_lagrangian_tendsto (r : ℕ) :
    Tendsto (fun n => (complete (Fin (n + 1)) r).lagrangian) atTop (𝓝 1) := by
  have hlo : Tendsto (fun n => samplingFactor r (n + 1)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr (samplingFactor_tendsto r)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => samplingFactor_le_complete_lagrangian r (n + 1) (by omega))
    (fun n => (complete (Fin (n + 1)) r).lagrangian_le_one)

end RGraph

theorem belowLagrangianApprox_zero (r : ℕ) : BelowLagrangianApprox r 0 := by
  refine ⟨fun _ => ⟨1, RGraph.empty (Fin 1) r⟩, ?_, ?_⟩
  · intro n
    simp
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem belowLagrangianApprox_one (r : ℕ) : BelowLagrangianApprox r 1 := by
  exact ⟨fun n => ⟨n + 1, RGraph.complete (Fin (n + 1)) r⟩,
    fun n => (RGraph.complete (Fin (n + 1)) r).lagrangian_le_one,
    RGraph.complete_lagrangian_tendsto r⟩

theorem zero_mem_turanSpectrum {r : ℕ} (hr : 0 < r) : 0 ∈ turanSpectrum r :=
  (belowLagrangianApprox_zero r).mem_turanSpectrum hr

theorem one_mem_turanSpectrum {r : ℕ} (hr : 0 < r) : 1 ∈ turanSpectrum r :=
  (belowLagrangianApprox_one r).mem_turanSpectrum hr

theorem turanSpectrum_subset_unitInterval (r : ℕ) : turanSpectrum r ⊆ Set.Icc 0 1 := by
  rintro x ⟨F, rfl⟩
  exact ⟨SetFamily.turanDensity_nonneg F, SetFamily.turanDensity_le_one F⟩

end IntervalsTuran
