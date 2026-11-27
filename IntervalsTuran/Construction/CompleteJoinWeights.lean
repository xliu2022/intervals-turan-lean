module

public import IntervalsTuran.Density.WeightedHomPushforward
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Weighted tuple sums for complete joins

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Density

variable {A I V : Type*}

def constantPartEquiv (A I V : Type*) (i : I) :
    {f : A → I × V // ∀ a, (f a).1 = i} ≃ (A → V) where
  toFun f a := (f.val a).2
  invFun g := ⟨fun a => (i, g a), fun _ => rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    exact Prod.ext (f.property a).symm rfl
  right_inv _ := rfl

theorem sum_productWeight_eq_pow [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) :
    (∑ f : A → V, productWeight x f) = (∑ v, x v) ^ Fintype.card A := by
  classical
  have h := Finset.prod_univ_sum (fun _ : A => (Finset.univ : Finset V))
    (fun _ v => x v)
  simpa [productWeight] using h.symm

theorem weightedMean_const_of_mass [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (c : ℝ) :
    weightedMean (A := A) x (fun _ => c) = (∑ v, x v) ^ Fintype.card A * c := by
  unfold weightedMean
  rw [← Finset.sum_mul, sum_productWeight_eq_pow]

theorem weightedMean_add [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (F G : (A → V) → ℝ) :
    weightedMean x (fun f => F f + G f) = weightedMean x F + weightedMean x G := by
  simp only [weightedMean, mul_add, Finset.sum_add_distrib]

theorem weightedMean_sub [Fintype A] [DecidableEq A] [Fintype V]
    (x : V → ℝ) (F G : (A → V) → ℝ) :
    weightedMean x (fun f => F f - G f) = weightedMean x F - weightedMean x G := by
  simp only [weightedMean, mul_sub, Finset.sum_sub_distrib]

/-- Restricting every sampled vertex to one part gives precisely the weighted
tuple sum of the corresponding unnormalized slice. -/
theorem weightedMean_constant_part [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] [Fintype V]
    (x : I × V → ℝ) (i : I) (F : (A → V) → ℝ) :
    weightedMean x (fun f : A → I × V =>
      if ∀ a, (f a).1 = i then F (fun a => (f a).2) else 0) =
      weightedMean (fun v => x (i, v)) F := by
  classical
  unfold weightedMean
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_subtype _
    (p := fun f : A → I × V => ∀ a, (f a).1 = i)
    (by intro f; simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  apply Fintype.sum_equiv (constantPartEquiv A I V i)
  intro f
  change (∏ a, x (f.val a)) * F (fun a => (f.val a).2) =
    (∏ a, x (i, (f.val a).2)) * F (fun a => (f.val a).2)
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact congrArg x (Prod.ext (f.property a) rfl)

theorem weightedMean_constant_part_indicator [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] [Fintype V]
    (x : I × V → ℝ) (i : I) :
    weightedMean x (fun f : A → I × V =>
      if ∀ a, (f a).1 = i then 1 else 0) =
      (∑ v, x (i, v)) ^ Fintype.card A := by
  simpa only [weightedMean_const_of_mass, mul_one] using
    weightedMean_constant_part (A := A) x i (fun _ => 1)

end IntervalsTuran.Density

namespace IntervalsTuran

/-- The power mean inequality for probability masses, in a form avoiding
negative integer powers. -/
theorem probabilityWeights_sum_pow_lower {I : Type*} [Fintype I] [Nonempty I]
    (w : I → ℝ) (hw : ProbabilityWeights w) (r : ℕ) :
    (Fintype.card I : ℝ) / (Fintype.card I : ℝ) ^ r ≤ ∑ i, w i ^ r := by
  have hM : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hMne : (Fintype.card I : ℝ) ≠ 0 := ne_of_gt hM
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
    (fun _ : I => (Fintype.card I : ℝ)⁻¹) w
    (fun _ _ => inv_nonneg.mpr hM.le)
    (by simp [hMne]) (fun i _ => hw.1 i) r
  rw [← Finset.mul_sum, hw.2, mul_one, ← Finset.mul_sum] at h
  have hm := mul_le_mul_of_nonneg_left h hM.le
  simpa only [inv_pow, div_eq_mul_inv, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul] using hm

end IntervalsTuran
