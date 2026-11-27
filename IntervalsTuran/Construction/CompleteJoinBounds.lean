module

public import IntervalsTuran.Construction.CompleteJoin

/-!
# Weighted upper and collision bounds for complete joins

Author and maintainer: Xizhi Liu.

The ideal tuple indicator allows repeated vertices only in cross-part tuples.
Its expectation is exactly the complete-join mass polynomial. Actual finite
joins are bounded above by that expectation, and their deficit is bounded by
the collision indicator.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.RGraph

open Density

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

noncomputable def joinIdealIndicator (G : RGraph V r)
    {I : Type*} (f : Fin r → I × V) : ℝ := by
  classical
  exact if (oneEdge r).IsHom G (fun a => (f a).2) ∨
    ∃ a b, (f a).1 ≠ (f b).1 then 1 else 0

theorem homIndicator_completeJoin_le_ideal (G : RGraph V r)
    {I : Type*} [Fintype I] [DecidableEq I] (f : Fin r → I × V) :
    (oneEdge r).homIndicator (G.completeJoin I) f ≤ G.joinIdealIndicator f := by
  classical
  by_cases h : (oneEdge r).IsHom G (fun a => (f a).2) ∨
      ∃ a b, (f a).1 ≠ (f b).1
  · simpa only [joinIdealIndicator, ite_eq_left h] using
      (oneEdge r).homIndicator_le_one (G.completeJoin I) f
  · have hn : ¬ (oneEdge r).IsHom (G.completeJoin I) f :=
      fun hf => h ((G.oneEdge_isHom_completeJoin_iff f).mp hf).2
    simp only [homIndicator_of_not_hom _ _ hn, joinIdealIndicator, ite_eq_right h, le_refl]

theorem joinIdeal_le_homIndicator_add_collision (G : RGraph V r)
    {I : Type*} [Fintype I] [DecidableEq I] (f : Fin r → I × V) :
    G.joinIdealIndicator f ≤ (oneEdge r).homIndicator (G.completeJoin I) f +
      if Function.Injective f then 0 else 1 := by
  classical
  by_cases hf : Function.Injective f
  · simp only [homIndicator, G.oneEdge_isHom_completeJoin_iff, hf,
      true_and, ite_true, add_zero, joinIdealIndicator]
    split_ifs <;> norm_num
  · have hn : ¬ (oneEdge r).IsHom (G.completeJoin I) f :=
      fun h => hf ((G.oneEdge_isHom_completeJoin_iff f).mp h).1
    rw [homIndicator_of_not_hom _ _ hn]
    simp only [ite_eq_right hf, zero_add, joinIdealIndicator]
    split_ifs <;> norm_num

omit [Fintype V] in
theorem joinIdealIndicator_eq (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] (f : Fin r → I × V) :
    G.joinIdealIndicator f =
      1 - (∑ i : I, if ∀ a, (f a).1 = i then 1 else 0) +
      (∑ i : I, if ∀ a, (f a).1 = i then
        (oneEdge r).homIndicator G (fun a => (f a).2) else 0) := by
  classical
  let a₀ : Fin r := ⟨0, hr⟩
  let i₀ : I := (f a₀).1
  by_cases hconstant : ∀ a, (f a).1 = i₀
  · have hiff (i : I) : (∀ a, (f a).1 = i) ↔ i = i₀ := by
      constructor
      · intro h
        exact (h a₀).symm
      · intro h
        simpa only [h] using hconstant
    have hsum (c : ℝ) : (∑ i : I, if ∀ a, (f a).1 = i then c else 0) = c := by
      simp only [hiff]
      simp
    have hcross : ¬ ∃ a b, (f a).1 ≠ (f b).1 := by
      rintro ⟨a, b, hab⟩
      exact hab ((hconstant a).trans (hconstant b).symm)
    rw [hsum, hsum]
    simp only [joinIdealIndicator, hcross, or_false, homIndicator, sub_self, zero_add]
  · have hnone (i : I) : ¬ ∀ a, (f a).1 = i := by
      intro h
      exact hconstant (fun a => (h a).trans (h a₀).symm)
    have hcross : ∃ a b, (f a).1 ≠ (f b).1 := by
      obtain ⟨a, ha⟩ := not_forall.mp hconstant
      exact ⟨a, a₀, ha⟩
    simp only [ite_eq_right (hnone _), Finset.sum_const_zero, sub_zero, add_zero,
      joinIdealIndicator, hcross, or_true, ite_true]

theorem weightedMean_joinIdeal (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] (x : I × V → ℝ)
    (hx : ProbabilityWeights x) :
    weightedMean x G.joinIdealIndicator =
      1 - (∑ i : I, (∑ v, x (i, v)) ^ r) +
      (∑ i : I, (r.factorial : ℝ) * G.edgePolynomial (fun v => x (i, v))) := by
  classical
  have hind (i : I) : weightedMean x (fun f : Fin r → I × V =>
      if ∀ a, (f a).1 = i then 1 else 0) = (∑ v, x (i, v)) ^ r := by
    convert! weightedMean_constant_part_indicator (A := Fin r) x i
    simp only [Fintype.card_fin]
  calc
    _ = weightedMean x (fun f : Fin r → I × V =>
        1 - (∑ i : I, if ∀ a, (f a).1 = i then 1 else 0) +
        (∑ i : I, if ∀ a, (f a).1 = i then
          (oneEdge r).homIndicator G (fun a => (f a).2) else 0)) :=
      weightedMean_congr x (fun f => G.joinIdealIndicator_eq hr f)
    _ = _ := by
      rw [weightedMean_add, weightedMean_sub, weightedMean_sum, weightedMean_sum,
        weightedMean_const x hx.2]
      simp only [hind, weightedMean_constant_part_oneEdge]

/-- A normalized Lagrangian polynomial scales as the `r`-th power of total
mass, including the zero-mass boundary. -/
theorem normalizedPolynomial_le_mass_pow (G : RGraph V r) (hr : 0 < r)
    (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ (∑ v, x v) ^ r * G.lagrangian := by
  let t : ℝ := ∑ v, x v
  have ht : 0 ≤ t := Finset.sum_nonneg (fun v _ => hx v)
  by_cases hzero : t = 0
  · have hxzero : x = fun _ => 0 := by
      funext v
      have hle : x v ≤ t := Finset.single_le_sum (fun w _ => hx w) (Finset.mem_univ v)
      exact le_antisymm (by simpa only [hzero] using hle) (hx v)
    change (r.factorial : ℝ) * G.edgePolynomial x ≤ t ^ r * G.lagrangian
    rw [hxzero, G.edgePolynomial_uniform, hzero, zero_pow (ne_of_gt hr)]
    simp
  · let w : V → ℝ := fun v => t⁻¹ * x v
    have hw : ProbabilityWeights w := by
      refine ⟨fun v => mul_nonneg (inv_nonneg.mpr ht) (hx v), ?_⟩
      dsimp [w]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hzero
    have heq : x = fun v => t * w v := by
      funext v
      dsimp [w]
      rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul]
    change (r.factorial : ℝ) * G.edgePolynomial x ≤ t ^ r * G.lagrangian
    calc
      _ = t ^ r * ((r.factorial : ℝ) * G.edgePolynomial w) := by
        rw [heq, G.edgePolynomial_scale]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (G.normalizedPolynomial_le_lagrangian w hw)
        (pow_nonneg ht _)

theorem completeJoin_normalizedPolynomial_le_masses (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] (x : I × V → ℝ)
    (hx : ProbabilityWeights x) :
    (r.factorial : ℝ) * (G.completeJoin I).edgePolynomial x ≤
      1 - (1 - G.lagrangian) * (∑ i : I, (∑ v, x (i, v)) ^ r) := by
  have hs :
      (∑ i : I, (r.factorial : ℝ) * G.edgePolynomial (fun v => x (i, v))) ≤
      (∑ i : I, (∑ v, x (i, v)) ^ r) * G.lagrangian := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      G.normalizedPolynomial_le_mass_pow hr _ (fun v => hx.1 (i, v))
  calc
    _ = weightedMean x ((oneEdge r).homIndicator (G.completeJoin I)) :=
      (weightedMean_oneEdge _ x).symm
    _ ≤ weightedMean x G.joinIdealIndicator :=
      weightedMean_mono x hx.1 (G.homIndicator_completeJoin_le_ideal)
    _ = 1 - (∑ i : I, (∑ v, x (i, v)) ^ r) +
        (∑ i : I, (r.factorial : ℝ) * G.edgePolynomial (fun v => x (i, v))) :=
      G.weightedMean_joinIdeal hr x hx
    _ ≤ 1 - (∑ i : I, (∑ v, x (i, v)) ^ r) +
        (∑ i : I, (∑ v, x (i, v)) ^ r) * G.lagrangian := by linarith [hs]
    _ = _ := by ring

/-- The genuine finite-join Lagrangian upper bound. A matching equality in
general requires a limit of increasingly diffuse blow-ups. -/
theorem completeJoin_lagrangian_le (G : RGraph V r) (hr : 0 < r)
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    (G.completeJoin I).lagrangian ≤
      1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1) := by
  have hM : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hMone : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hden : 0 < (Fintype.card I : ℝ) ^ (r - 1) := pow_pos hM _
  have hdenone : (1 : ℝ) ≤ (Fintype.card I : ℝ) ^ (r - 1) := one_le_pow₀ hMone
  have htarget : 0 ≤ 1 - (1 - G.lagrangian) / (Fintype.card I : ℝ) ^ (r - 1) := by
    apply sub_nonneg.mpr
    apply (div_le_one hden).mpr
    linarith [G.lagrangian_nonneg]
  have hcoef : (Fintype.card I : ℝ) / (Fintype.card I : ℝ) ^ r =
      1 / (Fintype.card I : ℝ) ^ (r - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s + 1 := ⟨r - 1, (Nat.sub_add_cancel hr).symm⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp [ne_of_gt hM]
  apply ((G.completeJoin I).lagrangian_le_iff htarget).mpr
  intro x hx
  let w : I → ℝ := fun i => ∑ v, x (i, v)
  have hw : ProbabilityWeights w := by
    refine ⟨fun i => Finset.sum_nonneg (fun v _ => hx.1 (i, v)), ?_⟩
    simpa only [w, Fintype.sum_prod_type] using hx.2
  have hp := probabilityWeights_sum_pow_lower w hw r
  have hlag : 0 ≤ 1 - G.lagrangian := sub_nonneg.mpr G.lagrangian_le_one
  calc
    _ ≤ 1 - (1 - G.lagrangian) * (∑ i : I, w i ^ r) :=
      G.completeJoin_normalizedPolynomial_le_masses hr x hx
    _ ≤ 1 - (1 - G.lagrangian) *
        ((Fintype.card I : ℝ) / (Fintype.card I : ℝ) ^ r) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left hp hlag) 1
    _ = _ := by rw [hcoef]; ring

end IntervalsTuran.RGraph
