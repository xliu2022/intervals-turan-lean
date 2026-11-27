/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.Parameters
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Finite Cayley operators and the spectral input interface

This file records the finite operator estimate actually used by the
three-uniform construction, and proves its functional mixing consequence.
`SmoothSpectralFamily` is an explicit data interface. No inhabitant of it
is asserted here; constructing one is the outstanding LPS dependency.
In particular, a theorem with such a family as an argument is conditional.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace IntervalsTuran.Spectral

noncomputable section

/-- A finite group and an inverse-closed set of nonidentity generators.
Connectedness is not built in: the zero-sum norm estimate, when supplied,
is the actual property needed by the construction. -/
structure FiniteCayley where
  Vertex : Type
  [group : Group Vertex]
  [fintype : Fintype Vertex]
  [decidableEq : DecidableEq Vertex]
  generators : Finset Vertex
  one_not_mem : 1 ∉ generators
  inverse_closed : ∀ s ∈ generators, s⁻¹ ∈ generators

attribute [instance] FiniteCayley.group FiniteCayley.fintype FiniteCayley.decidableEq

namespace FiniteCayley

def order (G : FiniteCayley) : ℕ := Fintype.card G.Vertex

def valency (G : FiniteCayley) : ℕ := G.generators.card

def adjacency (G : FiniteCayley) (h : G.Vertex → ℝ) (u : G.Vertex) : ℝ :=
  ∑ s ∈ G.generators, h (u * s)

def mean (G : FiniteCayley) (h : G.Vertex → ℝ) : ℝ :=
  (∑ u, h u) / (G.order : ℝ)

def centered (G : FiniteCayley) (h : G.Vertex → ℝ) (u : G.Vertex) : ℝ :=
  h u - G.mean h

def l2Norm (G : FiniteCayley) (h : G.Vertex → ℝ) : ℝ :=
  Real.sqrt (∑ u, (h u) ^ 2)

theorem order_pos (G : FiniteCayley) : 0 < G.order := by
  exact Fintype.card_pos

theorem order_real_ne_zero (G : FiniteCayley) : (G.order : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt G.order_pos)

theorem l2Norm_nonneg (G : FiniteCayley) (h : G.Vertex → ℝ) : 0 ≤ G.l2Norm h :=
  Real.sqrt_nonneg _

theorem sum_centered (G : FiniteCayley) (h : G.Vertex → ℝ) :
    ∑ u, G.centered h u = 0 := by
  simp only [centered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mean, order]
  have hn : (Fintype.card G.Vertex : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card G.Vertex))
  field_simp [hn]
  ring

theorem sum_right_translate (G : FiniteCayley) (h : G.Vertex → ℝ) (s : G.Vertex) :
    ∑ u, h (u * s) = ∑ u, h u := by
  exact Equiv.sum_comp (Equiv.mulRight s) h

theorem sum_adjacency (G : FiniteCayley) (h : G.Vertex → ℝ) :
    ∑ u, G.adjacency h u = (G.valency : ℝ) * ∑ u, h u := by
  simp only [adjacency]
  rw [Finset.sum_comm]
  simp only [G.sum_right_translate, Finset.sum_const, nsmul_eq_mul, valency]

theorem adjacency_const (G : FiniteCayley) (c : ℝ) (u : G.Vertex) :
    G.adjacency (fun _ => c) u = (G.valency : ℝ) * c := by
  simp [adjacency, valency]

theorem adjacency_centered (G : FiniteCayley) (h : G.Vertex → ℝ) (u : G.Vertex) :
    G.adjacency (G.centered h) u =
      G.adjacency h u - (G.valency : ℝ) * G.mean h := by
  simp [adjacency, centered, Finset.sum_sub_distrib, valency]

theorem sum_adjacency_centered (G : FiniteCayley) (h : G.Vertex → ℝ) :
    ∑ u, G.adjacency (G.centered h) u = 0 := by
  rw [G.sum_adjacency, G.sum_centered, mul_zero]

/-- The exact input estimate on the subspace perpendicular to constants. -/
def HasZeroSumBound (G : FiniteCayley) (θ : ℝ) : Prop :=
  ∀ h : G.Vertex → ℝ, (∑ u, h u) = 0 →
    G.l2Norm (G.adjacency h) ≤ θ * G.l2Norm h

theorem inner_le_l2Norm_mul (G : FiniteCayley) (f g : G.Vertex → ℝ) :
    ∑ u, f u * g u ≤ G.l2Norm f * G.l2Norm g := by
  exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g

theorem centered_mixing (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (f g : G.Vertex → ℝ) :
    (∑ u, G.centered f u * G.adjacency (G.centered g) u) ≤
      θ * G.l2Norm (G.centered f) * G.l2Norm (G.centered g) := by
  calc
    _ ≤ G.l2Norm (G.centered f) * G.l2Norm (G.adjacency (G.centered g)) :=
      G.inner_le_l2Norm_mul _ _
    _ ≤ G.l2Norm (G.centered f) * (θ * G.l2Norm (G.centered g)) :=
      mul_le_mul_of_nonneg_left (hbound _ (G.sum_centered g)) (G.l2Norm_nonneg _)
    _ = _ := by ring

/-- Splitting off constant functions gives the exact mean contribution. -/
theorem inner_adjacency_decompose (G : FiniteCayley) (f g : G.Vertex → ℝ) :
    (∑ u, f u * G.adjacency g u) =
      (G.valency : ℝ) * (G.order : ℝ) * G.mean f * G.mean g +
        ∑ u, G.centered f u * G.adjacency (G.centered g) u := by
  have hpoint (u : G.Vertex) :
      f u * G.adjacency g u =
        G.centered f u * G.adjacency (G.centered g) u +
        G.mean f * G.adjacency (G.centered g) u +
        ((G.valency : ℝ) * G.mean g) * G.centered f u +
        ((G.valency : ℝ) * G.mean f * G.mean g) := by
    rw [G.adjacency_centered]
    dsimp only [centered]
    ring
  calc
    _ = ∑ u, (G.centered f u * G.adjacency (G.centered g) u +
        G.mean f * G.adjacency (G.centered g) u +
        ((G.valency : ℝ) * G.mean g) * G.centered f u +
        ((G.valency : ℝ) * G.mean f * G.mean g)) :=
      Finset.sum_congr rfl (fun u _ => hpoint u)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, G.sum_centered,
        G.sum_adjacency_centered, mul_zero, add_zero, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, order]
      ring

/-- Functional expander mixing from the specified zero-sum operator bound.
This theorem proves the implication; it does not supply the spectral bound. -/
theorem mixing (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (f g : G.Vertex → ℝ) :
    (∑ u, f u * G.adjacency g u) ≤
      (G.valency : ℝ) * (G.order : ℝ) * G.mean f * G.mean g +
        θ * G.l2Norm (G.centered f) * G.l2Norm (G.centered g) := by
  rw [G.inner_adjacency_decompose]
  exact add_le_add (le_refl _) (G.centered_mixing hbound f g)

end FiniteCayley

/-- The minimal infinite input consumed by the fixed-parameter spectral
construction. This is a specification, not an existence theorem. -/
structure SmoothSpectralFamily where
  graph : ℕ → FiniteCayley
  valency_eq : ∀ j, (graph j).valency = degree
  zeroSum_bound : ∀ j, (graph j).HasZeroSumBound spectralBound
  order_strictMono : StrictMono (fun j => (graph j).order)
  order_tendsto : Tendsto (fun j => ((graph j).order : ℝ)) atTop atTop
  consecutive_ratio_tendsto :
    Tendsto (fun j => ((graph (j + 1)).order : ℝ) / ((graph j).order : ℝ))
      atTop (𝓝 1)

end

end IntervalsTuran.Spectral
