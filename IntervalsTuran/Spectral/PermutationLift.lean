/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Selector.FiniteAverages
public import IntervalsTuran.Spectral.FiberDesingularization
public import IntervalsTuran.Spectral.BipartiteKernel
public import Mathlib.FieldTheory.Finite.Basic

/-!
# A simple bipartite lift of a family of permutations

For permutations `P i` of a finite set `V` and a finite field `K`, the neighbors
of `(v,x,y)` are `(P i v, x+a, y+i/a)`, indexed by `i : K` and `a : Kˣ`.
The two field coordinates make the indexing injective, even when some of the
permutations agree. Consequently the resulting bipartite relation is simple
and regular on both sides, with degree `|K| (|K|-1)`.
-/

@[expose] public section

namespace IntervalsTuran.Spectral.PermutationLift

open scoped BigOperators

variable {K V : Type*} [Field K]

/-- The vertex set of the simple lift. -/
abbrev Vertex (V K : Type*) := V × (K × K)

/-- The actual neighbor indexed by a port and a nonzero field element. -/
def neighbor (P : K → Equiv.Perm V) (w : Vertex V K) (ia : K × Kˣ) : Vertex V K :=
  (P ia.1 w.1, w.2.1 + (ia.2 : K), w.2.2 + ia.1 / (ia.2 : K))

/-- The unique predecessor for a fixed port and nonzero field element. -/
def predecessor (P : K → Equiv.Perm V) (w : Vertex V K) (ia : K × Kˣ) : Vertex V K :=
  ((P ia.1).symm w.1, w.2.1 - (ia.2 : K), w.2.2 - ia.1 / (ia.2 : K))

@[simp] theorem predecessor_neighbor (P : K → Equiv.Perm V)
    (w : Vertex V K) (ia : K × Kˣ) :
    predecessor P (neighbor P w ia) ia = w := by
  rcases w with ⟨v, x, y⟩
  simp [neighbor, predecessor]

@[simp] theorem neighbor_predecessor (P : K → Equiv.Perm V)
    (w : Vertex V K) (ia : K × Kˣ) :
    neighbor P (predecessor P w ia) ia = w := by
  rcases w with ⟨v, x, y⟩
  simp [neighbor, predecessor]

theorem neighbor_injective (P : K → Equiv.Perm V) (w : Vertex V K) :
    Function.Injective (neighbor P w) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hab : (a : K) = (b : K) := by
    have hx := congrArg (fun z : Vertex V K => z.2.1) h
    exact add_left_cancel hx
  have ha : a = b := Units.ext hab
  subst b
  have hij : i = j := by
    have hy := congrArg (fun z : Vertex V K => z.2.2) h
    exact (div_left_inj' (Units.ne_zero a)).mp (add_left_cancel hy)
  subst j
  rfl

theorem predecessor_injective (P : K → Equiv.Perm V) (w : Vertex V K) :
    Function.Injective (predecessor P w) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hab : (a : K) = (b : K) := by
    have hx := congrArg (fun z : Vertex V K => z.2.1) h
    exact sub_right_injective hx
  have ha : a = b := Units.ext hab
  subst b
  have hij : i = j := by
    have hy := congrArg (fun z : Vertex V K => z.2.2) h
    exact (div_left_inj' (Units.ne_zero a)).mp (sub_right_injective hy)
  subst j
  rfl

variable [Fintype K] [DecidableEq K] [DecidableEq V]

/-- This is a set of neighbors, with no multiplicities. -/
def neighbors (P : K → Equiv.Perm V) (w : Vertex V K) : Finset (Vertex V K) :=
  Finset.univ.image (neighbor P w)

theorem mem_neighbors_iff (P : K → Equiv.Perm V) (w z : Vertex V K) :
    z ∈ neighbors P w ↔ ∃ ia, neighbor P w ia = z := by
  simp [neighbors]

theorem neighbors_card (P : K → Equiv.Perm V) (w : Vertex V K) :
    (neighbors P w).card = Fintype.card K * (Fintype.card K - 1) := by
  rw [neighbors, Finset.card_image_of_injective _ (neighbor_injective P w)]
  simp [Fintype.card_units]

omit [Fintype K] [DecidableEq K] [DecidableEq V] in
theorem neighbor_eq_iff (P : K → Equiv.Perm V) (w z : Vertex V K)
    (ia : K × Kˣ) :
    neighbor P w ia = z ↔ predecessor P z ia = w := by
  constructor
  · intro h
    rw [← h, predecessor_neighbor]
  · intro h
    rw [← h, neighbor_predecessor]

variable [Fintype V]

theorem incoming_neighbors_eq (P : K → Equiv.Perm V) (z : Vertex V K) :
    Finset.univ.filter (fun w => z ∈ neighbors P w) =
      Finset.univ.image (predecessor P z) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_neighbors_iff,
    neighbor_eq_iff, Finset.mem_image, true_and]

theorem incoming_neighbors_card (P : K → Equiv.Perm V) (z : Vertex V K) :
    (Finset.univ.filter (fun w => z ∈ neighbors P w)).card =
      Fintype.card K * (Fintype.card K - 1) := by
  rw [incoming_neighbors_eq, Finset.card_image_of_injective _ (predecessor_injective P z)]
  simp [Fintype.card_units]

omit [Fintype V] in
theorem sum_neighbors (P : K → Equiv.Perm V) (w : Vertex V K)
    (f : Vertex V K → ℝ) :
    ∑ z ∈ neighbors P w, f z = ∑ ia : K × Kˣ, f (neighbor P w ia) := by
  exact Finset.sum_image (fun a _ b _ h => neighbor_injective P w h)

/-- Conversion between the unit index and the erased-zero index used by the
fiber convolution. -/
theorem sum_units_eq_sum_erase_zero (f : K → ℝ) :
    ∑ a : Kˣ, f (a : K) = ∑ a ∈ Finset.univ.erase (0 : K), f a := by
  apply Finset.sum_bij (fun (a : Kˣ) _ => (a : K))
  · intro a _
    simp
  · intro a _ b _ h
    exact Units.ext h
  · intro b hb
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    exact ⟨Units.mk0 b hb0, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

/-- The adjacency sum, written in the fiber-convolution coordinates. -/
noncomputable def operator (P : K → Equiv.Perm V) (f : Vertex V K → ℝ)
    (w : Vertex V K) : ℝ :=
  ∑ i, Fiber.convolution i (fun xy => f (P i w.1, xy)) w.2

omit [Fintype V] in
theorem sum_neighbors_eq_operator (P : K → Equiv.Perm V)
    (f : Vertex V K → ℝ) (w : Vertex V K) :
    ∑ z ∈ neighbors P w, f z = operator P f w := by
  rw [sum_neighbors, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_units_eq_sum_erase_zero
    (fun a => f (P i w.1, w.2.1 + a, w.2.2 + i / a))

/-- The port operator on the original vertex set, allowing repeated ports. -/
noncomputable def baseOperator (P : K → Equiv.Perm V) (f : V → ℝ) (v : V) : ℝ :=
  ∑ i, f (P i v)

omit [Fintype V] [DecidableEq V] in
theorem operator_add (P : K → Equiv.Perm V) (f g : Vertex V K → ℝ) :
    operator P (fun w => f w + g w) = fun w => operator P f w + operator P g w := by
  funext w
  simp [operator, Fiber.convolution, Finset.sum_add_distrib]

omit [Fintype V] [DecidableEq V] in
theorem operator_fiber_constant (P : K → Equiv.Perm V) (g : V → ℝ)
    (w : Vertex V K) :
    operator P (fun z => g z.1) w =
      ((Fintype.card K : ℝ) - 1) * baseOperator P g w.1 := by
  simp only [operator, Fiber.convolution, Fiber.sum_nonzero_const, baseOperator]
  rw [Finset.mul_sum]

/-- A direct finite-sum Cauchy--Schwarz inequality. -/
theorem square_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    (∑ i, g i)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, (g i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) g

omit [DecidableEq V] in
/-- The nonconstant fiber part is controlled independently of the port
permutations. -/
theorem operator_sq_le_of_fiber_sum_zero (P : K → Equiv.Perm V)
    (f : Vertex V K → ℝ) (hzero : ∀ v, ∑ xy, f (v, xy) = 0) :
    ∑ w, (operator P f w)^2 ≤
      (Fintype.card K : ℝ)^2 * ((Fintype.card K : ℝ) - 1) * ∑ w, (f w)^2 := by
  let q : ℝ := Fintype.card K
  have hq : 0 ≤ q := by positivity
  calc
    ∑ w, (operator P f w)^2 = ∑ v, ∑ xy, (operator P f (v, xy))^2 :=
      Fintype.sum_prod_type _
    _ ≤ ∑ v, ∑ xy, q *
        ∑ i, (Fiber.convolution i (fun z => f (P i v, z)) xy)^2 := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro xy _
      exact square_sum_le_card_mul_sum_sq _
    _ = q * ∑ v, ∑ i, ∑ xy,
        (Fiber.convolution i (fun z => f (P i v, z)) xy)^2 := by
      simp_rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
    _ = q * ∑ v, ∑ i, ∑ xy,
        (Fiber.convolution i (fun z => f (v, z)) xy)^2 := by
      congr 1
      rw [Finset.sum_comm, Finset.sum_comm (f := fun v i =>
        ∑ xy, (Fiber.convolution i (fun z => f (v, z)) xy)^2)]
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp (P i) (fun v =>
        ∑ xy, (Fiber.convolution i (fun z => f (v, z)) xy)^2)
    _ ≤ q * ∑ v, q * (q - 1) * ∑ xy, (f (v, xy))^2 := by
      apply mul_le_mul_of_nonneg_left _ hq
      apply Finset.sum_le_sum
      intro v _
      exact Fiber.sum_convolution_sq_le _ (hzero v)
    _ = (Fintype.card K : ℝ)^2 * ((Fintype.card K : ℝ) - 1) *
        ∑ w, (f w)^2 := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      dsimp [q]
      ring

/-- The average of a function on each field-coordinate fiber. -/
noncomputable def fiberMean (f : Vertex V K → ℝ) (v : V) : ℝ :=
  Selector.mean (fun xy : K × K => f (v, xy))

/-- Removal of the fiber average. -/
noncomputable def residual (f : Vertex V K → ℝ) (w : Vertex V K) : ℝ :=
  f w - fiberMean f w.1

omit [DecidableEq K] [DecidableEq V] [Fintype V] in
theorem sum_fiber_eq_card_mul_mean (f : Vertex V K → ℝ) (v : V) :
    ∑ xy, f (v, xy) = (Fintype.card (K × K) : ℝ) * fiberMean f v := by
  rw [fiberMean, Selector.mean_eq_sum_div_card]
  have hc : (Fintype.card (K × K) : ℝ) ≠ 0 := by positivity
  field_simp

omit [DecidableEq K] [DecidableEq V] [Fintype V] in
theorem sum_residual_zero (f : Vertex V K → ℝ) (v : V) :
    ∑ xy, residual f (v, xy) = 0 := by
  simp only [residual, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [sum_fiber_eq_card_mul_mean]
  ring

omit [DecidableEq K] [DecidableEq V] in
theorem sum_fiberMean_zero (f : Vertex V K → ℝ) (hzero : ∑ w, f w = 0) :
    ∑ v, fiberMean f v = 0 := by
  have hsum : (Fintype.card (K × K) : ℝ) * ∑ v, fiberMean f v = 0 := by
    rw [Finset.mul_sum]
    simp_rw [← sum_fiber_eq_card_mul_mean]
    rw [← Fintype.sum_prod_type]
    exact hzero
  exact (mul_eq_zero.mp hsum).resolve_left (by positivity)

omit [DecidableEq K] [DecidableEq V] [Field K] in
/-- Orthogonality of fiber constants and functions having zero fiber sums. -/
theorem sum_sq_add_fiber_constant (g : V → ℝ) (r : Vertex V K → ℝ)
    (hzero : ∀ v, ∑ xy, r (v, xy) = 0) :
    ∑ w, (g w.1 + r w)^2 =
      (Fintype.card (K × K) : ℝ) * ∑ v, (g v)^2 + ∑ w, (r w)^2 := by
  have hfiber (v : V) : (∑ xy, (g v + r (v, xy))^2) =
      (Fintype.card (K × K) : ℝ) * (g v)^2 + ∑ xy, (r (v, xy))^2 := by
    calc
      _ = ∑ xy, ((g v)^2 + (2 * g v) * r (v, xy) + (r (v, xy))^2) := by
        apply Finset.sum_congr rfl
        intro xy _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hzero,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_zero, add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [hfiber]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.sum_prod_type]

omit [DecidableEq K] [DecidableEq V] in
theorem sum_sq_decomposition (f : Vertex V K → ℝ) :
    ∑ w, (f w)^2 =
      (Fintype.card (K × K) : ℝ) * ∑ v, (fiberMean f v)^2 +
        ∑ w, (residual f w)^2 := by
  convert sum_sq_add_fiber_constant (fiberMean f) (residual f) (sum_residual_zero f) using 1
  apply Finset.sum_congr rfl
  intro w _
  simp [residual]

omit [Fintype V] [DecidableEq V] in
theorem sum_operator_fiber_zero (P : K → Equiv.Perm V)
    (r : Vertex V K → ℝ) (hzero : ∀ v, ∑ xy, r (v, xy) = 0) (v : V) :
    ∑ xy, operator P r (v, xy) = 0 := by
  simp only [operator]
  rw [Finset.sum_comm]
  simp only [Fiber.sum_convolution_eq, hzero, mul_zero, Finset.sum_const_zero]

omit [Fintype V] [DecidableEq V] in
theorem operator_decomposition (P : K → Equiv.Perm V)
    (f : Vertex V K → ℝ) (w : Vertex V K) :
    operator P f w = ((Fintype.card K : ℝ) - 1) *
      baseOperator P (fiberMean f) w.1 + operator P (residual f) w := by
  have hf : f = fun z => fiberMean f z.1 + residual f z := by
    funext z
    simp [residual]
  calc
    operator P f w = operator P (fun z => fiberMean f z.1 + residual f z) w :=
      congrArg (fun h => operator P h w) hf
    _ = _ := by simp only [operator_add, operator_fiber_constant]

omit [DecidableEq V] in
theorem operator_sum_sq_decomposition (P : K → Equiv.Perm V)
    (f : Vertex V K → ℝ) :
    ∑ w, (operator P f w)^2 =
      (Fintype.card (K × K) : ℝ) * ((Fintype.card K : ℝ) - 1)^2 *
        ∑ v, (baseOperator P (fiberMean f) v)^2 +
      ∑ w, (operator P (residual f) w)^2 := by
  simp_rw [operator_decomposition P f]
  rw [sum_sq_add_fiber_constant
    (fun v => ((Fintype.card K : ℝ) - 1) * baseOperator P (fiberMean f) v)
    (operator P (residual f))
    (sum_operator_fiber_zero P (residual f) (sum_residual_zero f))]
  simp only [mul_pow, ← Finset.mul_sum, mul_assoc]

omit [DecidableEq V] in
/-- The full zero-sum bound follows from the port bound and the elementary
fiber bound. The two explicit inequalities select a common squared bound. -/
theorem operator_sq_le (P : K → Equiv.Perm V) {θ ρ : ℝ}
    (hbase : ∀ g : V → ℝ, (∑ v, g v) = 0 →
      (∑ v, (baseOperator P g v)^2) ≤ θ^2 * ∑ v, (g v)^2)
    (hconstant : ((Fintype.card K : ℝ) - 1)^2 * θ^2 ≤ ρ^2)
    (hfiber : (Fintype.card K : ℝ)^2 * ((Fintype.card K : ℝ) - 1) ≤ ρ^2)
    (f : Vertex V K → ℝ) (hzero : ∑ w, f w = 0) :
    ∑ w, (operator P f w)^2 ≤ ρ^2 * ∑ w, (f w)^2 := by
  let N : ℝ := Fintype.card (K × K)
  let c : ℝ := (Fintype.card K : ℝ) - 1
  have hN : 0 ≤ N := by positivity
  have hmean : (∑ v, (baseOperator P (fiberMean f) v)^2) ≤
      θ^2 * ∑ v, (fiberMean f v)^2 := hbase _ (sum_fiberMean_zero f hzero)
  have hres := operator_sq_le_of_fiber_sum_zero P (residual f) (sum_residual_zero f)
  have hmeanEnergy : 0 ≤ ∑ v, (fiberMean f v)^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hresEnergy : 0 ≤ ∑ w, (residual f w)^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [operator_sum_sq_decomposition, sum_sq_decomposition f]
  calc
    _ ≤ N * c^2 * (θ^2 * ∑ v, (fiberMean f v)^2) +
        ((Fintype.card K : ℝ)^2 * c) * ∑ w, (residual f w)^2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hmean (mul_nonneg hN (sq_nonneg c))) hres
    _ ≤ ρ^2 * (N * ∑ v, (fiberMean f v)^2) +
        ρ^2 * ∑ w, (residual f w)^2 := by
      apply add_le_add
      · have h := mul_le_mul_of_nonneg_right hconstant (mul_nonneg hN hmeanEnergy)
        dsimp [c, N] at *
        nlinarith only [h]
      · exact mul_le_mul_of_nonneg_right hfiber hresEnergy
    _ = _ := by dsimp [N]; ring

/-- The lift as an actual finite simple regular bipartite kernel. -/
def kernel (P : K → Equiv.Perm V) : BipartiteKernel (Vertex V K) where
  neighbors := neighbors P
  valency := Fintype.card K * (Fintype.card K - 1)
  left_regular := neighbors_card P
  right_regular := incoming_neighbors_card P

@[simp] theorem kernel_valency (P : K → Equiv.Perm V) :
    (kernel P).valency = Fintype.card K * (Fintype.card K - 1) := rfl

@[simp] theorem kernel_adjacency (P : K → Equiv.Perm V) (f : Vertex V K → ℝ)
    (w : Vertex V K) :
    (kernel P).adjacency f w = operator P f w :=
  sum_neighbors_eq_operator P f w

theorem kernel_hasZeroSumBound (P : K → Equiv.Perm V) {θ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbase : ∀ g : V → ℝ, (∑ v, g v) = 0 →
      (∑ v, (baseOperator P g v)^2) ≤ θ^2 * ∑ v, (g v)^2)
    (hconstant : ((Fintype.card K : ℝ) - 1)^2 * θ^2 ≤ ρ^2)
    (hfiber : (Fintype.card K : ℝ)^2 * ((Fintype.card K : ℝ) - 1) ≤ ρ^2) :
    (kernel P).HasZeroSumBound ρ := by
  apply BipartiteKernel.bound_of_squared _ hρ
  intro f hzero
  simp only [kernel_adjacency]
  exact operator_sq_le P hbase hconstant hfiber f hzero

/-- A normalized port bound of `1/6` is preserved by the simple lift once
the field has at least `37` elements. -/
theorem kernel_hasZeroSumBound_one_sixth (P : K → Equiv.Perm V)
    (hlarge : 37 ≤ Fintype.card K)
    (hbase : ∀ g : V → ℝ, (∑ v, g v) = 0 →
      (∑ v, (baseOperator P g v)^2) ≤
        ((Fintype.card K : ℝ) / 6)^2 * ∑ v, (g v)^2) :
    (kernel P).HasZeroSumBound ((kernel P).valency / 6) := by
  let q : ℝ := Fintype.card K
  have hq : (37 : ℝ) ≤ q := by
    change (37 : ℝ) ≤ (Fintype.card K : ℝ)
    exact_mod_cast hlarge
  have hqnat : 1 ≤ Fintype.card K := le_trans (by decide) hlarge
  have hval : ((kernel P).valency : ℝ) = q * (q - 1) := by
    simp only [kernel_valency, Nat.cast_mul, Nat.cast_sub hqnat, Nat.cast_one, q]
  rw [hval]
  apply kernel_hasZeroSumBound P (θ := q / 6)
  · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  · exact hbase
  · dsimp [q]
    nlinarith only [sq_nonneg ((Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 1))]
  · have hc : 36 * (q - 1) ≤ (q - 1)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg q)
    change q^2 * (q - 1) ≤ (q * (q - 1) / 6)^2
    nlinarith only [hh]

end IntervalsTuran.Spectral.PermutationLift
