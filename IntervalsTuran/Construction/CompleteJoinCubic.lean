/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Construction.CompleteJoin
public import IntervalsTuran.Hypergraph.SymmetricSums

/-!
# Exact cubic polynomial of a finite complete join

The elementary symmetric identity retains the repeated-vertex correction
in the complete join.  This is the finite polynomial identity required
by the outer spectral construction.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.RGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem complete_three_polynomial (x : V → ℝ) :
    6 * (complete V 3).edgePolynomial x =
      (∑ v, x v) ^ 3 - 3 * (∑ v, x v) * (∑ v, (x v) ^ 2) +
        2 * (∑ v, (x v) ^ 3) := by
  simpa only [complete, edgePolynomial, Weighted.elementary] using
    Weighted.elementary_third_identity Finset.univ x

/-- The exact collision correction for the finite complete join. -/
theorem completeJoin_three_polynomial (G : RGraph V 3)
    {I : Type*} [Fintype I] [DecidableEq I] (x : I × V → ℝ)
    (hx : ProbabilityWeights x) :
    6 * (G.completeJoin I).edgePolynomial x =
      1 - (∑ i, (∑ v, x (i, v)) ^ 3) -
        3 * (∑ i, (1 - ∑ v, x (i, v)) * (∑ v, x (i, v) ^ 2)) +
        ∑ i, 6 * G.edgePolynomial (fun v => x (i, v)) := by
  have h := G.completeJoin_normalizedPolynomial (by omega) x
  norm_num only [Nat.factorial] at h
  rw [h, complete_three_polynomial, hx.2]
  simp only [complete_three_polynomial, one_pow, mul_one, one_mul,
    Fintype.sum_prod_type, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sub_mul, one_mul, mul_assoc, ← Finset.mul_sum]
  ring

end IntervalsTuran.RGraph
