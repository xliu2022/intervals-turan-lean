module

public import IntervalsTuran.Construction.CompleteJoinApprox

/-!
# Preservation of finite Lagrangian approximation by complete joins

Author and maintainer: Xizhi Liu.

Every witness below is an actual finite simple hypergraph. The upper bound
comes from the complete-join mass inequality; the matching limit comes from
independent clone labels. Empty vertex types are handled by replacing their
zero Lagrangian with a one-vertex empty graph.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran

noncomputable def finiteJoinClone {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (G : RGraph V r) (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    FiniteGraph r :=
  ⟨Fintype.card (I × (V × Fin q)),
    ((G.inverseImage (Prod.fst : V × Fin q → V)).completeJoin I).pullback
      (Fintype.equivFin (I × (V × Fin q))).symm.toEmbedding⟩

theorem finiteJoinClone_lagrangian {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (G : RGraph V r) (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    (finiteJoinClone G I q).2.lagrangian =
      ((G.inverseImage (Prod.fst : V × Fin q → V)).completeJoin I).lagrangian := by
  exact RGraph.lagrangian_pullback_equiv _ _

theorem belowLagrangianApprox_completeJoin_lagrangian
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {r : ℕ} (G : RGraph V r) (hr : 0 < r)
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    BelowLagrangianApprox r
      (1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1)) := by
  have hD : 0 < (Fintype.card I : ℝ) ^ (r - 1) :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  obtain ⟨x, hx, hmax⟩ := G.exists_lagrangian_maximizer
  have hbelow (n : ℕ) : (finiteJoinClone G I (n + 1)).2.lagrangian ≤
      1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1) := by
    rw [finiteJoinClone_lagrangian]
    have hc := (G.inverseImage_projection (Prod.fst : V × Fin (n + 1) → V)).lagrangian_le
    exact ((G.inverseImage (Prod.fst : V × Fin (n + 1) → V)).completeJoin_lagrangian_le hr I).trans
      (sub_le_sub_left
        (div_le_div_of_nonneg_right (sub_le_sub_left hc 1) hD.le) 1)
  have hlower (n : ℕ) : samplingFactor r (n + 1) *
      (1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1)) ≤
      (finiteJoinClone G I (n + 1)).2.lagrangian := by
    rw [finiteJoinClone_lagrangian]
    simpa only [hmax] using
      G.completeJoin_clone_lagrangian_lower hr (I := I) x hx (q := n + 1) (by omega)
  have hf : Tendsto (fun n => samplingFactor r (n + 1)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr (samplingFactor_tendsto r)
  have hlo : Tendsto
      (fun n => samplingFactor r (n + 1) *
        (1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1))) atTop
      (𝓝 (1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1))) := by
    simpa only [one_mul] using hf.mul_const
      (1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1))
  exact ⟨fun n => finiteJoinClone G I (n + 1), hbelow,
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds hlower hbelow⟩

theorem belowLagrangianApprox_completeJoin_finite
    {r : ℕ} (G : FiniteGraph r) (hr : 0 < r)
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    BelowLagrangianApprox r
      (1 - (1 - G.2.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1)) := by
  rcases G with ⟨n, G⟩
  cases n with
  | zero =>
    have hG : G.lagrangian = 0 := G.lagrangian_of_isEmpty
    simpa only [hG, RGraph.lagrangian_empty] using
      belowLagrangianApprox_completeJoin_lagrangian (RGraph.empty (Fin 1) r) hr I
  | succ n => exact belowLagrangianApprox_completeJoin_lagrangian G hr I

/-- The complete-join map preserves approximation by actual finite
Lagrangians from below, for every positive uniformity. -/
theorem BelowLagrangianApprox.completeJoin {r : ℕ} {x : ℝ}
    (h : BelowLagrangianApprox r x) (hr : 0 < r) (M : ℕ) (hM : 0 < M) :
    BelowLagrangianApprox r (1 - (1 - x) / (M : ℝ) ^ (r - 1)) := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hD : 0 < (M : ℝ) ^ (r - 1) := pow_pos (Nat.cast_pos.mpr hM) _
  obtain ⟨G, hG, hlim⟩ := h
  apply BelowLagrangianApprox.of_tendsto_from_below
    (u := fun n => 1 - (1 - (G n).2.lagrangian) / (M : ℝ) ^ (r - 1))
  · intro n
    simpa only [Fintype.card_fin] using belowLagrangianApprox_completeJoin_finite (G n) hr (Fin M)
  · intro n
    exact sub_le_sub_left
      (div_le_div_of_nonneg_right (sub_le_sub_left (hG n) 1) hD.le) 1
  · exact (tendsto_const_nhds (x := (1 : ℝ))).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).div_const _)

end IntervalsTuran
