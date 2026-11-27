/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.Family

/-!
# Simple regular bipartite kernels

The two vertex classes are copies of the same finite type. Symmetry of the
relation is not required. This is the input used by the additive tripartite
construction, and permits a simple lift of an already formalized expander.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral

noncomputable section

structure BipartiteKernel (V : Type*) [Fintype V] [DecidableEq V] where
  neighbors : V → Finset V
  valency : ℕ
  left_regular : ∀ v, (neighbors v).card = valency
  right_regular : ∀ w, (Finset.univ.filter (fun v => w ∈ neighbors v)).card = valency

namespace BipartiteKernel

variable {V : Type*} [Fintype V] [DecidableEq V]

def adjacency (B : BipartiteKernel V) (h : V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ B.neighbors v, h w

def l2Norm (h : V → ℝ) : ℝ := Real.sqrt (∑ v, h v ^ 2)

def HasZeroSumBound (B : BipartiteKernel V) (θ : ℝ) : Prop :=
  ∀ h : V → ℝ, (∑ v, h v) = 0 → l2Norm (B.adjacency h) ≤ θ * l2Norm h

theorem sum_sq_nonneg (h : V → ℝ) : 0 ≤ ∑ v, h v ^ 2 :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem bound_of_squared (B : BipartiteKernel V) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : ∀ h : V → ℝ, (∑ v, h v) = 0 →
      (∑ v, B.adjacency h v ^ 2) ≤ θ ^ 2 * ∑ v, h v ^ 2) :
    B.HasZeroSumBound θ := by
  intro h hh
  dsimp [l2Norm]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · exact mul_nonneg hθ (Real.sqrt_nonneg _)
  · rw [mul_pow, Real.sq_sqrt (sum_sq_nonneg h)]
    exact hbound h hh

theorem squared_of_bound (B : BipartiteKernel V) {θ : ℝ}
    (hθ : 0 ≤ θ) (hbound : B.HasZeroSumBound θ)
    (h : V → ℝ) (hh : (∑ v, h v) = 0) :
    (∑ v, B.adjacency h v ^ 2) ≤ θ ^ 2 * ∑ v, h v ^ 2 := by
  have hb := hbound h hh
  have hp := sq_le_sq₀ (show 0 ≤ l2Norm (B.adjacency h) from Real.sqrt_nonneg _)
    (mul_nonneg hθ (show 0 ≤ l2Norm h from Real.sqrt_nonneg _))
  have hsq := hp.mpr hb
  simpa only [l2Norm, mul_pow, Real.sq_sqrt (sum_sq_nonneg h),
    Real.sq_sqrt (sum_sq_nonneg (B.adjacency h))] using hsq

theorem adjacency_eq_sum_ite (B : BipartiteKernel V) (h : V → ℝ) (v : V) :
    B.adjacency h v = ∑ w, if w ∈ B.neighbors v then h w else 0 := by
  rw [← Finset.sum_filter]
  simp [adjacency]

theorem adjacency_const (B : BipartiteKernel V) (c : ℝ) (v : V) :
    B.adjacency (fun _ => c) v = B.valency * c := by
  simp [adjacency, B.left_regular]

theorem sum_adjacency (B : BipartiteKernel V) (h : V → ℝ) :
    (∑ v, B.adjacency h v) = (B.valency : ℝ) * ∑ v, h v := by
  simp_rw [B.adjacency_eq_sum_ite h]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Finset.sum_filter]
  simp [B.right_regular]

theorem adjacency_add (B : BipartiteKernel V) (f g : V → ℝ) (v : V) :
    B.adjacency (fun w => f w + g w) v = B.adjacency f v + B.adjacency g v := by
  simp [adjacency, Finset.sum_add_distrib]

theorem adjacency_sub (B : BipartiteKernel V) (f g : V → ℝ) (v : V) :
    B.adjacency (fun w => f w - g w) v = B.adjacency f v - B.adjacency g v := by
  simp [adjacency, Finset.sum_sub_distrib]

theorem adjacency_smul (B : BipartiteKernel V) (c : ℝ) (f : V → ℝ) (v : V) :
    B.adjacency (fun w => c * f w) v = c * B.adjacency f v := by
  simp [adjacency, Finset.mul_sum]

def mass (f : V → ℝ) : ℝ := ∑ v, f v

def mean (f : V → ℝ) : ℝ := mass f / (Fintype.card V : ℝ)

def centered (f : V → ℝ) (v : V) : ℝ := f v - mean f

def variance (f : V → ℝ) : ℝ := ∑ v, (centered f v) ^ 2

theorem mass_comp (e : V ≃ V) (f : V → ℝ) : mass (fun v => f (e v)) = mass f :=
  Equiv.sum_comp e f

theorem mean_comp (e : V ≃ V) (f : V → ℝ) : mean (fun v => f (e v)) = mean f := by
  unfold mean
  rw [mass_comp]

theorem l2Norm_comp (e : V ≃ V) (f : V → ℝ) : l2Norm (fun v => f (e v)) = l2Norm f := by
  unfold l2Norm
  rw [Equiv.sum_comp e (fun v => f v ^ 2)]

theorem centered_comp (e : V ≃ V) (f : V → ℝ) (v : V) :
    centered (fun u => f (e u)) v = centered f (e v) := by
  simp only [centered, mean_comp]

theorem centered_l2Norm_comp (e : V ≃ V) (f : V → ℝ) :
    l2Norm (centered (fun v => f (e v))) = l2Norm (centered f) := by
  simp only [funext (centered_comp e f)]
  exact l2Norm_comp e (centered f)

theorem mass_nonneg (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) : 0 ≤ mass f :=
  Finset.sum_nonneg (fun v _ => hf v)

theorem variance_nonneg (f : V → ℝ) : 0 ≤ variance f :=
  Finset.sum_nonneg (fun v _ => sq_nonneg _)

theorem centered_l2Norm_sq (f : V → ℝ) : l2Norm (centered f) ^ 2 = variance f :=
  Real.sq_sqrt (variance_nonneg f)

section Nonempty

variable [Nonempty V]

theorem card_real_ne_zero : (Fintype.card V : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card V))

theorem sum_centered (f : V → ℝ) : (∑ v, centered f v) = 0 := by
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mean, mass]
  field_simp [card_real_ne_zero (V := V)]
  ring

theorem adjacency_centered (B : BipartiteKernel V) (f : V → ℝ) (v : V) :
    B.adjacency (centered f) v = B.adjacency f v - B.valency * mean f := by
  simp [adjacency, centered, Finset.sum_sub_distrib, B.left_regular]

theorem sum_adjacency_centered (B : BipartiteKernel V) (f : V → ℝ) :
    (∑ v, B.adjacency (centered f) v) = 0 := by
  rw [B.sum_adjacency, sum_centered, mul_zero]

theorem centered_mixing (B : BipartiteKernel V) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) (f g : V → ℝ) :
    (∑ v, centered f v * B.adjacency (centered g) v) ≤
      θ * l2Norm (centered f) * l2Norm (centered g) := by
  calc
    _ ≤ l2Norm (centered f) * l2Norm (B.adjacency (centered g)) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ l2Norm (centered f) * (θ * l2Norm (centered g)) :=
      mul_le_mul_of_nonneg_left (hbound _ (sum_centered g)) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem inner_adjacency_decompose (B : BipartiteKernel V) (f g : V → ℝ) :
    (∑ v, f v * B.adjacency g v) =
      (B.valency : ℝ) * (Fintype.card V : ℝ) * mean f * mean g +
        ∑ v, centered f v * B.adjacency (centered g) v := by
  have hpoint (v : V) :
      f v * B.adjacency g v = centered f v * B.adjacency (centered g) v +
        mean f * B.adjacency (centered g) v +
        ((B.valency : ℝ) * mean g) * centered f v +
        ((B.valency : ℝ) * mean f * mean g) := by
    rw [B.adjacency_centered]
    dsimp only [centered]
    ring
  calc
    _ = ∑ v, (centered f v * B.adjacency (centered g) v +
        mean f * B.adjacency (centered g) v +
        ((B.valency : ℝ) * mean g) * centered f v +
        ((B.valency : ℝ) * mean f * mean g)) :=
      Finset.sum_congr rfl (fun v _ => hpoint v)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_centered,
        B.sum_adjacency_centered, mul_zero, add_zero, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

theorem mixing_mass (B : BipartiteKernel V) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) (f g : V → ℝ) :
    (∑ v, f v * B.adjacency g v) ≤
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass f * mass g +
        θ * l2Norm (centered f) * l2Norm (centered g) := by
  rw [B.inner_adjacency_decompose]
  have hmain : (B.valency : ℝ) * (Fintype.card V : ℝ) * mean f * mean g =
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass f * mass g := by
    dsimp only [mean]
    field_simp [card_real_ne_zero (V := V)]
  rw [hmain]
  exact add_le_add (le_refl _) (B.centered_mixing hbound f g)

theorem variance_eq (f : V → ℝ) :
    variance f = (∑ v, f v ^ 2) - mass f ^ 2 / (Fintype.card V : ℝ) := by
  have hpoint (v : V) :
      centered f v ^ 2 = f v ^ 2 - 2 * mean f * f v + mean f ^ 2 := by
    unfold centered
    ring
  unfold variance
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp [mean, mass]
  field_simp [card_real_ne_zero (V := V)]
  ring

end Nonempty

end BipartiteKernel
end
end IntervalsTuran.Spectral
