module

public import IntervalsTuran.Construction.RecursivePattern
public import IntervalsTuran.Spectral.Parameters

/-!
# The explicit recursive base lies above the spectral limiting value

Author and maintainer: Xizhi Liu.

The uniform weighting of the complete three-graph on 2701 vertices already
has normalized polynomial value strictly greater than 899/900. Its actual
Lagrangian, and hence the least recursive fixed point, are at least this
value. No formula for the maximizing clique weights is required.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran

namespace Spectrum

/-- Evaluate the genuine clique polynomial at uniform weights using the cubic
symmetric identity, avoiding enumeration of the three-edges. -/
theorem clique_uniform_cubic_value (n : ℕ) (hn : 0 < n) :
    6 * (RGraph.clique (Fin n) 3).edgePolynomial (fun _ => (n : ℝ)⁻¹) =
      ((n : ℝ) - 1) * ((n : ℝ) - 2) / (n : ℝ) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [clique_polynomial_cubic]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn0]
  ring

end Spectrum

namespace Spectral

set_option backward.isDefEq.respectTransparency false

/-- The uniform complete-three-graph evaluation already exceeds the limiting
spectral value used in Section 6. -/
theorem limitValue_lt_clique_uniform :
    limitValue < 6 * (RGraph.clique (Fin 2701) 3).edgePolynomial
      (fun _ => (1 / 2701 : ℝ)) := by
  have h := Spectrum.clique_uniform_cubic_value 2701 (by omega)
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  norm_num [limitValue]

theorem limitValue_lt_clique_lagrangian :
    limitValue < (RGraph.clique (Fin 2701) 3).lagrangian := by
  apply limitValue_lt_clique_uniform.trans_le
  have hx : ProbabilityWeights (fun _ : Fin 2701 => (1 / 2701 : ℝ)) := by
    constructor
    · intro i
      norm_num
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
  have h := (RGraph.clique (Fin 2701) 3).normalizedPolynomial_le_lagrangian _
    hx
  norm_num only [Nat.factorial] at h
  exact h

/-- The explicit least recursive fixed point is strictly larger than the
side-value limit. `2699 + 2` is the number of parts of the actual base clique. -/
theorem limitValue_lt_cliqueRatioValue :
    limitValue < Spectrum.cliqueRatioValue 2699 limitValue :=
  limitValue_lt_clique_lagrangian.trans_le
    (Spectrum.clique_lagrangian_le_ratio 2699 limitValue_pos.le)

theorem cliqueRatioValue_2699_pos :
    0 < Spectrum.cliqueRatioValue 2699 limitValue :=
  limitValue_pos.trans limitValue_lt_cliqueRatioValue

theorem cliqueRatioValue_2699_le_one :
    Spectrum.cliqueRatioValue 2699 limitValue ≤ 1 :=
  Spectrum.cliqueRatioValue_le_one 2699 limitValue_lt_one.le

theorem cliqueRatioValue_2699_mem_unitInterval :
    Spectrum.cliqueRatioValue 2699 limitValue ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cliqueRatioValue_2699_pos.le, cliqueRatioValue_2699_le_one⟩

end Spectral

end IntervalsTuran
