module

public import IntervalsTuran.Construction.WeakOuterOptimization
public import IntervalsTuran.Construction.CompleteJoinClosure
public import IntervalsTuran.Construction.BaseParameters
public import IntervalsTuran.Construction.RecursiveIntervalRealization

/-!
# Recursive base parameters for the fixed spectral-gap construction

The complete join of the zero coefficient with `k` parts approximates
`1 - 1 / k²` from below by actual finite hypergraphs. The uniform complete
three-graph on `3*k²+2` vertices already exceeds this base. This gives the
strict recursive gap required for the interval theorem, for every `k ≥ 4`.
-/

@[expose] public section

open scoped BigOperators
open Filter Topology Set

namespace IntervalsTuran.Construction

theorem weakOuterBase_pos {k : ℕ} (hk : 4 ≤ k) : 0 < weakOuterBase k := by
  have hkr : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hsq : (1 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  exact sub_pos.mpr ((div_lt_one (pow_pos hkpos 2)).mpr hsq)

theorem weakOuterBase_lt_one {k : ℕ} (hk : 0 < k) : weakOuterBase k < 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
  dsimp [weakOuterBase]
  linarith

/-- Genuine complete joins provide the base approximation, independently of
the sequence approaching it from above. -/
theorem belowLagrangianApprox_weakOuterBase {k : ℕ} (hk : 0 < k) :
    BelowLagrangianApprox 3 (weakOuterBase k) := by
  simpa [weakOuterBase] using
    (belowLagrangianApprox_zero 3).completeJoin (by omega : 0 < 3) k hk

/-- A uniform clique value strictly exceeds the outer limiting coefficient. -/
theorem weakOuterBase_lt_clique_uniform {k : ℕ} (hk : 0 < k) :
    weakOuterBase k <
      6 * (RGraph.clique (Fin (3 * k ^ 2 + 2)) 3).edgePolynomial
        (fun _ => ((3 * k ^ 2 + 2 : ℕ) : ℝ)⁻¹) := by
  rw [Spectrum.clique_uniform_cubic_value (3 * k ^ 2 + 2) (by omega)]
  push_cast
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hNpos : (0 : ℝ) < 3 * (k : ℝ) ^ 2 + 2 := by positivity
  have hdiff :
      ((3 * (k : ℝ) ^ 2 + 2 - 1) * (3 * (k : ℝ) ^ 2 + 2 - 2) /
        (3 * (k : ℝ) ^ 2 + 2) ^ 2) - weakOuterBase k =
      (8 * (k : ℝ) ^ 2 + 4) /
        ((k : ℝ) ^ 2 * (3 * (k : ℝ) ^ 2 + 2) ^ 2) := by
    dsimp [weakOuterBase]
    field_simp [hk0, hNpos.ne']
    ring
  have hpos : (0 : ℝ) < (8 * (k : ℝ) ^ 2 + 4) /
      ((k : ℝ) ^ 2 * (3 * (k : ℝ) ^ 2 + 2) ^ 2) := by positivity
  exact sub_pos.mp (hdiff.symm ▸ hpos)

theorem weakOuterBase_lt_clique_lagrangian {k : ℕ} (hk : 0 < k) :
    weakOuterBase k < (RGraph.clique (Fin (3 * k ^ 2 + 2)) 3).lagrangian := by
  apply (weakOuterBase_lt_clique_uniform hk).trans_le
  have hNpos : 0 < 3 * k ^ 2 + 2 := by omega
  have hN0 : (((3 * k ^ 2 + 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hNpos)
  have hx : ProbabilityWeights
      (fun _ : Fin (3 * k ^ 2 + 2) => (((3 * k ^ 2 + 2 : ℕ) : ℝ))⁻¹) := by
    constructor
    · intro i
      positivity
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ hN0
  have h := (RGraph.clique (Fin (3 * k ^ 2 + 2)) 3).normalizedPolynomial_le_lagrangian _ hx
  norm_num only [Nat.factorial] at h
  exact h

/-- The actual least recursive fixed point is strictly above the new base. -/
theorem weakOuterBase_lt_cliqueRatioValue {k : ℕ} (hk : 4 ≤ k) :
    weakOuterBase k < Spectrum.cliqueRatioValue (3 * k ^ 2) (weakOuterBase k) :=
  (weakOuterBase_lt_clique_lagrangian (by omega : 0 < k)).trans_le
    (Spectrum.clique_lagrangian_le_ratio (3 * k ^ 2) (weakOuterBase_pos hk).le)

theorem weakBase_cliqueRatioValue_pos {k : ℕ} (hk : 4 ≤ k) :
    0 < Spectrum.cliqueRatioValue (3 * k ^ 2) (weakOuterBase k) :=
  (weakOuterBase_pos hk).trans (weakOuterBase_lt_cliqueRatioValue hk)

/-- Any smooth decreasing sequence of actual finite Lagrangians above the
new base supplies a nontrivial interval of approximation from below. -/
theorem weakBase_exists_interval_of_smooth_finite_lagrangians
    (k : ℕ) (hk : 4 ≤ k) (G : ℕ → FiniteGraph 3)
    (hab : ∀ n, weakOuterBase k < (G n).2.lagrangian)
    (hanti : Antitone (fun n => (G n).2.lagrangian))
    (hlim : Tendsto (fun n => (G n).2.lagrangian) atTop (𝓝 (weakOuterBase k)))
    (hratio : Tendsto
      (fun n => ((G n).2.lagrangian - weakOuterBase k) /
        ((G (n + 1)).2.lagrangian - weakOuterBase k)) atTop (𝓝 1)) :
    ∃ v : ℝ, Spectrum.cliqueRatioValue (3 * k ^ 2) (weakOuterBase k) < v ∧
      Icc (Spectrum.cliqueRatioValue (3 * k ^ 2) (weakOuterBase k)) v ⊆
        {x | BelowLagrangianApprox 3 x} :=
  Spectrum.exists_interval_of_smooth_finite_lagrangians (3 * k ^ 2)
    (belowLagrangianApprox_weakOuterBase (by omega : 0 < k))
    (weakOuterBase_lt_cliqueRatioValue hk) G hab hanti hlim hratio

end IntervalsTuran.Construction

