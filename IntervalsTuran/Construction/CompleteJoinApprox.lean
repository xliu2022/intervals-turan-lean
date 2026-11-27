module

public import IntervalsTuran.Construction.CompleteJoinBounds
public import IntervalsTuran.Construction.Lifting
public import IntervalsTuran.Turan.BelowApproximation

/-!
# Diffuse finite witnesses for complete joins

Author and maintainer: Xizhi Liu.

Independent clone labels avoid collisions. The injective-label probability is
the already defined sampling factor, which tends to one as the clone count
increases. This supplies actual finite hypergraphs approaching the ideal join
value from below.
-/

@[expose] public section

open scoped BigOperators
open Filter Topology

namespace IntervalsTuran.Density

def nestedTupleEquiv (A I V Q : Type*) :
    (A → I × (V × Q)) ≃ (A → I × V) × (A → Q) where
  toFun f := (fun a => ((f a).1, (f a).2.1), fun a => (f a).2.2)
  invFun p a := ((p.1 a).1, ((p.1 a).2, p.2 a))
  left_inv _ := rfl
  right_inv _ := rfl

theorem weightedMean_nested_product {A I V Q : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [Fintype V] [Fintype Q]
    (x : I × V → ℝ) (t : Q → ℝ) (F : (A → I × V) → ℝ) (H : (A → Q) → ℝ) :
    weightedMean (fun z : I × (V × Q) => x (z.1, z.2.1) * t z.2.2)
      (fun f => F (fun a => ((f a).1, (f a).2.1)) * H (fun a => (f a).2.2)) =
      weightedMean x F * weightedMean t H := by
  classical
  unfold weightedMean
  calc
    _ = ∑ p : (A → I × V) × (A → Q),
        (productWeight x p.1 * productWeight t p.2) * (F p.1 * H p.2) := by
      apply Fintype.sum_equiv (nestedTupleEquiv A I V Q)
      intro f
      simp [nestedTupleEquiv, productWeight, Finset.prod_mul_distrib]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring

theorem probabilityWeights_nested_product {I V Q : Type*}
    [Fintype I] [Fintype V] [Fintype Q]
    (x : I × V → ℝ) (t : Q → ℝ) (hx : ProbabilityWeights x) (ht : ProbabilityWeights t) :
    ProbabilityWeights (fun z : I × (V × Q) => x (z.1, z.2.1) * t z.2.2) := by
  refine ⟨fun z => mul_nonneg (hx.1 _) (ht.1 _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ht.2, mul_one]
  simpa only [Fintype.sum_prod_type] using hx.2

noncomputable def uniformPartWeights {I V : Type*} [Fintype I]
    (x : V → ℝ) : I × V → ℝ :=
  fun z => (Fintype.card I : ℝ)⁻¹ * x z.2

theorem uniformPartWeights_probability {I V : Type*} [Fintype I] [Nonempty I] [Fintype V]
    (x : V → ℝ) (hx : ProbabilityWeights x) : ProbabilityWeights (uniformPartWeights (I := I) x) := by
  have hM : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun z => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hx.1 z.2), ?_⟩
  simp [uniformPartWeights, Fintype.sum_prod_type, ← Finset.mul_sum, hx.2, hM]

end IntervalsTuran.Density

namespace IntervalsTuran.RGraph

open Density

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem uniformPartWeights_joinIdeal (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (x : V → ℝ) (hx : ProbabilityWeights x) :
    weightedMean (uniformPartWeights (I := I) x) G.joinIdealIndicator =
      1 - (1 - (r.factorial : ℝ) * G.edgePolynomial x) /
        (Fintype.card I : ℝ) ^ (r - 1) := by
  have hs (i : I) : (∑ v, uniformPartWeights x (i, v)) = (Fintype.card I : ℝ)⁻¹ := by
    simp only [uniformPartWeights, ← Finset.mul_sum, hx.2, mul_one]
  have hp (i : I) : (r.factorial : ℝ) *
      G.edgePolynomial (fun v => uniformPartWeights x (i, v)) =
      ((Fintype.card I : ℝ)⁻¹) ^ r * ((r.factorial : ℝ) * G.edgePolynomial x) := by
    simp only [uniformPartWeights]
    rw [G.edgePolynomial_scale]
    ring
  have hM : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card I : ℝ) * ((Fintype.card I : ℝ)⁻¹) ^ r =
      ((Fintype.card I : ℝ) ^ (r - 1))⁻¹ := by
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 1 := ⟨r - 1, (Nat.sub_add_cancel hr).symm⟩
    simp only [Nat.add_sub_cancel, pow_succ, inv_pow]
    field_simp
  rw [G.weightedMean_joinIdeal hr _ (uniformPartWeights_probability x hx)]
  simp_rw [hs, hp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hc,
    div_eq_mul_inv]
  ring

theorem weightedMean_uniform_complete (r q : ℕ) :
    weightedMean (fun _ : Fin q => (q : ℝ)⁻¹)
      ((oneEdge r).homIndicator (complete (Fin q) r)) = samplingFactor r q := by
  change (oneEdge r).weightedHomDensity (complete (Fin q) r)
    (fun _ : Fin q => (q : ℝ)⁻¹) = _
  have h := (oneEdge r).weightedHomDensity_uniform (complete (Fin q) r)
  simp only [Fintype.card_fin] at h
  rw [h, oneEdge_homDensity, complete_edge_card]
  simp only [Fintype.card_fin, samplingFactor]

/-- Independent injective clone labels turn every ideal-admissible base tuple
into an actual edge of the complete join of cloned copies. -/
theorem ideal_times_clone_injective_le_join (G : RGraph V r)
    {I : Type*} [Fintype I] [DecidableEq I] (q : ℕ)
    (f : Fin r → I × (V × Fin q)) :
    G.joinIdealIndicator (fun a => ((f a).1, (f a).2.1)) *
      (oneEdge r).homIndicator (complete (Fin q) r) (fun a => (f a).2.2) ≤
      (oneEdge r).homIndicator
        ((G.inverseImage (Prod.fst : V × Fin q → V)).completeJoin I) f := by
  classical
  by_cases had : (oneEdge r).IsHom G (fun a => (f a).2.1) ∨
      ∃ a b, (f a).1 ≠ (f b).1
  · by_cases hi : Function.Injective (fun a => (f a).2.2)
    · have hf : (oneEdge r).IsHom
          ((G.inverseImage (Prod.fst : V × Fin q → V)).completeJoin I) f := by
        apply (oneEdge_isHom_completeJoin_iff _ f).mpr
        refine ⟨fun a b hab => hi (congrArg (fun z : I × (V × Fin q) => z.2.2) hab), ?_⟩
        rcases had with hG | hcross
        · left
          apply (isHom_inverseImage_iff (oneEdge r) G
            (Prod.fst : V × Fin q → V) (fun a => (f a).2)).mpr
          exact hG
        · exact Or.inr hcross
      rw [homIndicator_of_hom _ _ hf]
      simp only [joinIdealIndicator, had, ite_true, homIndicator,
        oneEdge_isHom_complete_iff, hi, ite_true, mul_one, le_refl]
    · have hn : ¬ (oneEdge r).IsHom (complete (Fin q) r) (fun a => (f a).2.2) := by
        simpa only [oneEdge_isHom_complete_iff] using hi
      rw [homIndicator_of_not_hom _ _ hn, mul_zero]
      exact (oneEdge r).homIndicator_nonneg _ f
  · simp only [joinIdealIndicator, had, ite_false, zero_mul]
    exact (oneEdge r).homIndicator_nonneg _ f

theorem completeJoin_clone_lagrangian_lower (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (x : V → ℝ) (hx : ProbabilityWeights x) {q : ℕ} (hq : 0 < q) :
    samplingFactor r q *
      (1 - (1 - (r.factorial : ℝ) * G.edgePolynomial x) /
        (Fintype.card I : ℝ) ^ (r - 1)) ≤
      ((G.inverseImage (Prod.fst : V × Fin q → V)).completeJoin I).lagrangian := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let b : I × V → ℝ := uniformPartWeights x
  let t : Fin q → ℝ := fun _ => (q : ℝ)⁻¹
  have hb : ProbabilityWeights b := uniformPartWeights_probability x hx
  have ht : ProbabilityWeights t := by
    simpa only [t, Fintype.card_fin] using (probabilityWeights_uniform (V := Fin q))
  let w : I × (V × Fin q) → ℝ := fun z => b (z.1, z.2.1) * t z.2.2
  have hw : ProbabilityWeights w := probabilityWeights_nested_product b t hb ht
  have hmean := weightedMean_mono w hw.1 (G.ideal_times_clone_injective_le_join (I := I) q)
  rw [weightedMean_nested_product] at hmean
  have hideal : weightedMean b G.joinIdealIndicator =
      1 - (1 - (r.factorial : ℝ) * G.edgePolynomial x) /
        (Fintype.card I : ℝ) ^ (r - 1) := G.uniformPartWeights_joinIdeal hr x hx
  have hclone : weightedMean t ((oneEdge r).homIndicator (complete (Fin q) r)) =
      samplingFactor r q := weightedMean_uniform_complete r q
  rw [hideal, hclone, weightedMean_oneEdge] at hmean
  rw [mul_comm] at hmean
  exact hmean.trans
    (((G.inverseImage (Prod.fst : V × Fin q → V)).completeJoin I).normalizedPolynomial_le_lagrangian w hw)

end IntervalsTuran.RGraph
