/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Hyperbola fibers remove parallel edges

The shifts `(a, i / a)`, where `a ≠ 0`, belonging to different labels `i`
are disjoint.  Their summed correlation operator has an elementary exact
formula over every finite field.  Its restriction to functions of mean
zero supplies the spectral estimate for the permutation lift.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.Fiber

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def shift (i a : K) : K × K := (a, i / a)

def convolution (i : K) (f : K × K → ℝ) (x : K × K) : ℝ :=
  ∑ a ∈ Finset.univ.erase (0 : K), f (x + shift i a)

omit [Fintype K] [DecidableEq K] in
theorem shift_label_injective {i j a b : K} (ha : a ≠ 0)
    (h : shift i a = shift j b) : i = j ∧ a = b := by
  have hab : a = b := congrArg Prod.fst h
  subst b
  have hdiv : i / a = j / a := congrArg Prod.snd h
  exact ⟨(div_left_inj' ha).mp hdiv, rfl⟩

omit [DecidableEq K] in
theorem sum_sub_left (g : K → ℝ) (a : K) :
    (∑ b, g (a - b)) = ∑ u, g u := by
  exact Equiv.sum_comp (Equiv.subLeft a) g

theorem sum_nonzero_eq (g : K → ℝ) :
    (∑ a ∈ Finset.univ.erase (0 : K), g a) = (∑ a, g a) - g 0 := by
  classical
  exact Finset.sum_erase_eq_sub (Finset.mem_univ _)

theorem sum_nonzero_const (c : ℝ) :
    (∑ _a ∈ Finset.univ.erase (0 : K), c) = ((Fintype.card K : ℝ) - 1) * c := by
  rw [sum_nonzero_eq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem convolution_const (i : K) (c : ℝ) (x : K × K) :
    convolution i (fun _ => c) x = ((Fintype.card K : ℝ) - 1) * c :=
  sum_nonzero_const c

theorem sum_convolution_eq (i : K) (f : K × K → ℝ) :
    (∑ x, convolution i f x) = ((Fintype.card K : ℝ) - 1) * ∑ x, f x := by
  unfold convolution
  rw [Finset.sum_comm]
  have htranslate (a : K) : (∑ x, f (x + shift i a)) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.addRight (shift i a)) f
  simp_rw [htranslate]
  exact sum_nonzero_const _

theorem sum_nonzero_pair_difference (g : K → ℝ) :
    (∑ a ∈ Finset.univ.erase (0 : K),
      ∑ b ∈ Finset.univ.erase (0 : K), g (a - b)) =
      ((Fintype.card K : ℝ) - 2) * (∑ u, g u) + g 0 := by
  classical
  simp_rw [sum_nonzero_eq, sum_sub_left, sub_zero]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem sum_label_shift_difference (g : K × K → ℝ) (a b : K) :
    (∑ i, g (shift i a - shift i b)) =
      if a = b then (Fintype.card K : ℝ) * g 0 else ∑ v, g (a - b, v) := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right_iff.mpr (fun h => (hab h).elim)]
    have hcoef : a⁻¹ - b⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_injective.ne hab)
    calc
      _ = ∑ i, g (a - b, i * (a⁻¹ - b⁻¹)) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        simp [shift, div_eq_mul_inv, mul_sub]
      _ = _ := Equiv.sum_comp (Equiv.mulRight₀ _ hcoef) (fun v => g (a - b, v))

theorem sum_nonzero_diagonal (c : ℝ) :
    (∑ a ∈ Finset.univ.erase (0 : K),
      ∑ b ∈ Finset.univ.erase (0 : K), if a = b then c else 0) =
      ((Fintype.card K : ℝ) - 1) * c := by
  classical
  have hinner (a : K) (ha : a ∈ Finset.univ.erase (0 : K)) :
      (∑ b ∈ Finset.univ.erase (0 : K), if a = b then c else 0) = c := by
    simp [ha]
  simp_rw [Finset.sum_congr rfl hinner]
  exact sum_nonzero_const c

/-- Exact difference multiplicities of the hyperbola shifts.  A zero
first coordinate forces the entire difference to be zero.  Every other
difference has exactly `card K - 2` representations after summing labels. -/
theorem sum_shift_differences (g : K × K → ℝ) :
    (∑ i, ∑ a ∈ Finset.univ.erase (0 : K),
      ∑ b ∈ Finset.univ.erase (0 : K), g (shift i a - shift i b)) =
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) * g 0 +
      ((Fintype.card K : ℝ) - 2) *
        (∑ u ∈ Finset.univ.erase (0 : K), ∑ v, g (u, v)) := by
  classical
  let q : ℝ := Fintype.card K
  let G : K → ℝ := fun u => ∑ v, g (u, v)
  have hpoint (a b : K) :
      (∑ i, g (shift i a - shift i b)) =
        G (a - b) + if a = b then q * g 0 - G 0 else 0 := by
    rw [sum_label_shift_difference]
    by_cases hab : a = b
    · subst b
      simp only [ite_true, sub_self]
      dsimp only [q]
      ring
    · simp [hab, G]
  calc
    _ = ∑ a ∈ Finset.univ.erase (0 : K),
        ∑ b ∈ Finset.univ.erase (0 : K), ∑ i, g (shift i a - shift i b) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = (∑ a ∈ Finset.univ.erase (0 : K),
          ∑ b ∈ Finset.univ.erase (0 : K), G (a - b)) +
        (∑ a ∈ Finset.univ.erase (0 : K),
          ∑ b ∈ Finset.univ.erase (0 : K),
            if a = b then q * g 0 - G 0 else 0) := by
      simp only [hpoint, Finset.sum_add_distrib]
    _ = (q - 2) * (∑ u, G u) + G 0 + (q - 1) * (q * g 0 - G 0) := by
      rw [sum_nonzero_pair_difference, sum_nonzero_diagonal]
    _ = _ := by
      rw [sum_nonzero_eq]
      change (q - 2) * (∑ u, G u) + G 0 + (q - 1) * (q * g 0 - G 0) =
        q * (q - 1) * g 0 + (q - 2) * ((∑ u, G u) - G 0)
      ring

def correlation (f : K × K → ℝ) (u : K × K) : ℝ :=
  ∑ x, f x * f (x + u)

omit [DecidableEq K] in
theorem sum_mul_translates (f : K × K → ℝ) (s t : K × K) :
    (∑ x, f (x + s) * f (x + t)) = correlation f (s - t) := by
  calc
    _ = ∑ x, f (x + t) * f ((x + t) + (s - t)) := by
      apply Finset.sum_congr rfl
      intro x _
      have heq : (x + t) + (s - t) = x + s := by abel
      rw [heq, mul_comm]
    _ = _ := Equiv.sum_comp (Equiv.addRight t) (fun x => f x * f (x + (s - t)))

omit [DecidableEq K] in
theorem correlation_zero (f : K × K → ℝ) :
    correlation f 0 = ∑ x, (f x) ^ 2 := by
  simp [correlation, pow_two]

omit [DecidableEq K] in
theorem sum_correlation (f : K × K → ℝ) :
    (∑ u, correlation f u) = (∑ x, f x) ^ 2 := by
  have htranslate (x : K × K) : (∑ u, f (x + u)) = ∑ u, f u :=
    Equiv.sum_comp (Equiv.addLeft x) f
  unfold correlation
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, htranslate]
  rw [← Finset.sum_mul, pow_two]

omit [DecidableEq K] in
theorem sum_vertical_correlation (f : K × K → ℝ) :
    (∑ v, correlation f (0, v)) = ∑ a, (∑ b, f (a, b)) ^ 2 := by
  have htranslate (a b : K) : (∑ v, f (a, b + v)) = ∑ v, f (a, v) :=
    Equiv.sum_comp (Equiv.addLeft b) (fun v => f (a, v))
  unfold correlation
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Prod.mk_add_mk, add_zero, ← Finset.mul_sum, htranslate]
  rw [← Finset.sum_mul, pow_two]

/-- The precise summed correlation formula.  The final term is a
nonnegative vertical-fiber correction, so the formula immediately gives
the desired bound on the mean-zero subspace. -/
theorem sum_convolution_sq (f : K × K → ℝ) :
    (∑ i, ∑ x, (convolution i f x) ^ 2) =
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) * (∑ x, (f x) ^ 2) +
      ((Fintype.card K : ℝ) - 2) *
        ((∑ x, f x) ^ 2 - ∑ a, (∑ b, f (a, b)) ^ 2) := by
  classical
  calc
    _ = ∑ i, ∑ x, ∑ a ∈ Finset.univ.erase (0 : K),
        ∑ b ∈ Finset.univ.erase (0 : K), f (x + shift i a) * f (x + shift i b) := by
      simp only [convolution, pow_two, Finset.mul_sum, mul_comm]
    _ = ∑ i, ∑ a ∈ Finset.univ.erase (0 : K),
        ∑ b ∈ Finset.univ.erase (0 : K),
          ∑ x, f (x + shift i a) * f (x + shift i b) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ i, ∑ a ∈ Finset.univ.erase (0 : K),
        ∑ b ∈ Finset.univ.erase (0 : K), correlation f (shift i a - shift i b) := by
      simp only [sum_mul_translates]
    _ = _ := by
      rw [sum_shift_differences, correlation_zero, sum_nonzero_eq]
      rw [← Fintype.sum_prod_type, sum_correlation, sum_vertical_correlation]

/-- Uniform bound for all hyperbola convolution operators together.
This is a finite-field counting and Cauchy--Schwarz statement; it uses
no character-sum estimate. -/
theorem sum_convolution_sq_le (f : K × K → ℝ) (hzero : ∑ x, f x = 0) :
    (∑ i, ∑ x, (convolution i f x) ^ 2) ≤
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1) * ∑ x, (f x) ^ 2 := by
  rw [sum_convolution_sq, hzero, zero_pow (by decide : 2 ≠ 0), zero_sub]
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 2 ≤ Fintype.card K from Fintype.one_lt_card)
  have hv : 0 ≤ ∑ a, (∑ b, f (a, b)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hn := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq) (neg_nonpos.mpr hv)
  linarith only [hn]

end

end IntervalsTuran.Spectral.Fiber
