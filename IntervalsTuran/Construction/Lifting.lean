module

public import IntervalsTuran.Turan.LagrangianCap
public import IntervalsTuran.Hypergraph.Relabel
public import IntervalsTuran.Uniformity.MassOptimization

/-!
# Lagrangian lifting from uniformity three

Author and maintainer: Xizhi Liu.

Adding common vertices to every edge gives an exact Lagrangian scaling.
Consequently finite approximations from below lift to every larger uniformity.
This construction uses actual finite simple hypergraphs, including the
empty-vertex case, and the ordinary Turan density from LagrangianCap.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran

noncomputable def liftScale (r : ℕ) : ℝ :=
  (r.factorial : ℝ) * (27 / (r : ℝ) ^ r) / 6

theorem liftScale_pos {r : ℕ} (hr : 0 < r) : 0 < liftScale r := by
  unfold liftScale
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  positivity

namespace RGraph

universe u v

theorem lagrangian_pullback_equiv {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
    {r : ℕ} (G : RGraph W r) (e : V ≃ W) :
    (G.pullback e.toEmbedding).lagrangian = G.lagrangian := by
  exact le_antisymm (G.pullback_equiv_embedding e).isHom.lagrangian_le
    (G.pullback_equiv_inverse e).isHom.lagrangian_le

theorem lagrangian_suspension {V : Type u} [DecidableEq V] [Fintype V]
    (G : RGraph V 3) (s : ℕ) :
    (G.suspension s).lagrangian = liftScale (s + 3) * G.lagrangian := by
  have hc : 0 < liftScale (s + 3) := liftScale_pos (by omega)
  apply le_antisymm
  · apply ((G.suspension s).lagrangian_le_iff
      (mul_nonneg hc.le G.lagrangian_nonneg)).mpr
    intro w hw
    have hb : ∀ x, ProbabilityWeights x → G.edgePolynomial x ≤ G.lagrangian / 6 := by
      intro x hx
      have h := G.normalizedPolynomial_le_lagrangian x hx
      norm_num at h
      linarith
    have h := G.suspension_polynomial_bound s (G.lagrangian / 6)
      (div_nonneg G.lagrangian_nonneg (by norm_num)) hb w hw
    calc
      ((s + 3).factorial : ℝ) * (G.suspension s).edgePolynomial w ≤
          ((s + 3).factorial : ℝ) *
            (27 / (s + 3 : ℝ) ^ (s + 3) * (G.lagrangian / 6)) :=
        mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
      _ = liftScale (s + 3) * G.lagrangian := by
        simp only [liftScale, Nat.cast_add, Nat.cast_ofNat]
        ring
  · have hdiv : G.lagrangian ≤ (G.suspension s).lagrangian / liftScale (s + 3) := by
      apply (G.lagrangian_le_iff (div_nonneg (G.suspension s).lagrangian_nonneg hc.le)).mpr
      intro x hx
      apply (le_div_iff₀ hc).mpr
      have h := (G.suspension s).normalizedPolynomial_le_lagrangian
        (suspensionWeights s x) (suspensionWeights_probability s x hx)
      rw [G.suspensionWeights_value] at h
      calc
        ((3 : ℕ).factorial : ℝ) * G.edgePolynomial x * liftScale (s + 3) =
            ((s + 3).factorial : ℝ) *
              (27 / (s + 3 : ℝ) ^ (s + 3) * G.edgePolynomial x) := by
          norm_num [liftScale]
          <;> ring
        _ ≤ _ := h
    simpa [mul_comm] using (le_div_iff₀ hc).mp hdiv

end RGraph

/-- A labelled version of the finite suspension. -/
noncomputable def finiteSuspension (s : ℕ) (G : FiniteGraph 3) : FiniteGraph (s + 3) :=
  ⟨s + G.1, (G.2.suspension s).pullback
    (Fintype.equivOfCardEq
      (show Fintype.card (Fin (s + G.1)) = Fintype.card (Fin s ⊕ Fin G.1) by simp)).toEmbedding⟩

theorem finiteSuspension_lagrangian (s : ℕ) (G : FiniteGraph 3) :
    (finiteSuspension s G).2.lagrangian = liftScale (s + 3) * G.2.lagrangian := by
  dsimp only [finiteSuspension]
  exact (RGraph.lagrangian_pullback_equiv _ _).trans (G.2.lagrangian_suspension s)

theorem BelowLagrangianApprox.lift_add_three {x : ℝ}
    (h : BelowLagrangianApprox 3 x) (s : ℕ) :
    BelowLagrangianApprox (s + 3) (liftScale (s + 3) * x) := by
  obtain ⟨G, hbelow, hlim⟩ := h
  refine ⟨fun n => finiteSuspension s (G n), ?_, ?_⟩
  · intro n
    rw [finiteSuspension_lagrangian]
    exact mul_le_mul_of_nonneg_left (hbelow n) (liftScale_pos (by omega)).le
  · simp_rw [finiteSuspension_lagrangian]
    exact hlim.const_mul _

theorem BelowLagrangianApprox.lift {x : ℝ}
    (h : BelowLagrangianApprox 3 x) {r : ℕ} (hr : 3 ≤ r) :
    BelowLagrangianApprox r (liftScale r * x) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, (Nat.sub_add_cancel hr).symm⟩
  exact h.lift_add_three s

theorem BelowLagrangianApprox.lift_mem_turanSpectrum {x : ℝ}
    (h : BelowLagrangianApprox 3 x) {r : ℕ} (hr : 3 ≤ r) :
    liftScale r * x ∈ turanSpectrum r :=
  (h.lift hr).mem_turanSpectrum (by omega)

end IntervalsTuran
