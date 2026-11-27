/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Linarith

/-!
# Explicit parameters for the spectral construction

The choices `p = 137`, `D = 138`, `k = 30`, and `m = 2701` are those in
Section 6 of Liu--Pikhurko, *Intervals of hypergraph Turán densities*.
The rational norm bound `47 / 2` is slightly weaker than `2 * sqrt 137`.
These numerical facts do not assert the existence of an LPS family.
-/

@[expose] public section

namespace IntervalsTuran.Spectral

noncomputable section

def auxiliaryPrime : ℕ := 137
def degree : ℕ := 138
def outerParts : ℕ := 30
def recursiveParts : ℕ := 2701
def spectralBound : ℝ := 47 / 2
def limitValue : ℝ := 899 / 900
def firstOrderCoefficient : ℝ := 1 / 180

theorem auxiliaryPrime_prime : Nat.Prime auxiliaryPrime := by
  norm_num [auxiliaryPrime]

theorem auxiliaryPrime_mod_four : auxiliaryPrime % 4 = 1 := by
  norm_num [auxiliaryPrime]

theorem degree_eq_prime_add_one : degree = auxiliaryPrime + 1 := by
  norm_num [degree, auxiliaryPrime]

theorem spectralBound_pos : 0 < spectralBound := by
  norm_num [spectralBound]

/-- A rational upper bound for the LPS norm bound at the fixed prime. -/
theorem ramanujanBound_le_spectralBound :
    2 * Real.sqrt (auxiliaryPrime : ℝ) ≤ spectralBound := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 137 by norm_num)
  have hnonneg := Real.sqrt_nonneg (137 : ℝ)
  norm_num [auxiliaryPrime, spectralBound]
  nlinarith

/-- The cube of the first numerical inequality in (3.1), after clearing
positive denominators. This form uses only rational arithmetic. -/
theorem parameter_inequality_cubed :
    (spectralBound + 3) ^ 3 < 21 * (outerParts : ℝ) ^ 2 := by
  norm_num [spectralBound, outerParts]

theorem outerParts_lt_degree_bound :
    (outerParts : ℝ) < 2 * (degree : ℝ) / 9 + 1 := by
  norm_num [outerParts, degree]

theorem limitValue_eq : limitValue = 1 - 1 / (outerParts : ℝ) ^ 2 := by
  norm_num [limitValue, outerParts]

theorem limitValue_pos : 0 < limitValue := by
  norm_num [limitValue]

theorem limitValue_lt_one : limitValue < 1 := by
  norm_num [limitValue]

theorem firstOrderCoefficient_eq :
    firstOrderCoefficient =
      (2 * (degree : ℝ) / 3 - 3 * ((outerParts : ℝ) - 1)) /
        (outerParts : ℝ) ^ 2 := by
  norm_num [firstOrderCoefficient, degree, outerParts]

theorem firstOrderCoefficient_pos : 0 < firstOrderCoefficient := by
  norm_num [firstOrderCoefficient]

theorem recursiveParts_ge_four : 4 ≤ recursiveParts := by
  norm_num [recursiveParts]

/-- Exact arithmetic for the complete-graph expression used in (4.1).
The separate Lagrangian theorem identifies this expression with the
Lagrangian of the complete three-uniform graph on 2700 vertices. -/
theorem completeGraphExpression_eq :
    (((recursiveParts : ℝ) - 2) * ((recursiveParts : ℝ) - 3)) /
        ((recursiveParts : ℝ) - 1) ^ 2 =
      limitValue + 1 / 3645000 := by
  norm_num [recursiveParts, limitValue]

theorem limitValue_lt_completeGraphExpression :
    limitValue <
      (((recursiveParts : ℝ) - 2) * ((recursiveParts : ℝ) - 3)) /
        ((recursiveParts : ℝ) - 1) ^ 2 := by
  rw [completeGraphExpression_eq]
  norm_num

end

end IntervalsTuran.Spectral
