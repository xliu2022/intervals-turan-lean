module

public import IntervalsTuran.Analysis.RecursiveValues
public import IntervalsTuran.Spectrum.CliqueFixedPoint

/-!
# Actual recursive clique patterns and their infinite values

Author and maintainer: Xizhi Liu.

The recursion map is the maximum of the normalized complete-three-graph
polynomial with one recursive part and one side part. Every finite
substitution is an actual finite graph; approximation from below is retained
at every finite stage and at the infinite limit.
-/

@[expose] public section

namespace IntervalsTuran.Spectrum

open Set Filter Analysis
open scoped Topology

noncomputable section

theorem cliqueStep_monotone_input (m : ℕ) (b : ℝ) :
    Monotone (fun t => cliqueStep m t b) :=
  fun _ _ h => cliqueStep_mono m h le_rfl

theorem cliqueStep_lipschitz_input (m : ℕ) (b : ℝ) :
    LipschitzWith 1 (fun t => cliqueStep m t b) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    cliqueStep_abs_sub_le m t u b b (abs_nonneg _) le_rfl (by simp)

/-- Actual finite graph substitution preserves approximation from below for
both distinguished branch values. -/
theorem belowLagrangianApprox_cliqueStep (m : ℕ) {t b : ℝ}
    (ht : BelowLagrangianApprox 3 t) (hb : BelowLagrangianApprox 3 b) :
    BelowLagrangianApprox 3 (cliqueStep m t b) := by
  apply belowLagrangianApprox_substitutionValue _ (by omega)
  intro i
  unfold twoCoefficients
  split
  · exact ht
  · split
    · exact hb
    · exact belowLagrangianApprox_zero 3

/-- Each iterate of the constant recursion has finite graph approximants
bounded by its exact value. -/
theorem belowLagrangianApprox_cliqueIter (m : ℕ) {b : ℝ}
    (hb : BelowLagrangianApprox 3 b) (n : ℕ) :
    BelowLagrangianApprox 3 (cliqueIter m b n) := by
  induction n with
  | zero => exact belowLagrangianApprox_zero 3
  | succ n ih => exact belowLagrangianApprox_cliqueStep m ih hb

/-- The compact ratio maximum is realized by a limit of genuine finite
three-graph Lagrangians, approached from below. -/
theorem belowLagrangianApprox_cliqueRatioValue (m : ℕ) {b : ℝ}
    (hb : BelowLagrangianApprox 3 b) :
    BelowLagrangianApprox 3 (cliqueRatioValue m b) :=
  BelowLagrangianApprox.of_tendsto_from_below
    (belowLagrangianApprox_cliqueIter m hb) (cliqueIter_le_ratio m b)
    (cliqueIter_tendsto m b)

/-- The paper's concrete recursion, restricted to its invariant unit interval.
The parameter is the side value, followed by the recursive tail value. -/
def cliqueRecursiveSystem (m : ℕ) : RecursiveSystem := by
  refine RecursiveSystem.ofReal (fun b t => cliqueStep m t b) ?_ ?_ ?_ ?_ ?_
  · intro b hb t ht
    exact ⟨ht.1.trans (le_cliqueStep m t b), cliqueStep_le_one m ht.2 hb.2⟩
  · intro b _ t _ u _ htu
    exact cliqueStep_mono m htu le_rfl
  · intro t _ b _ c _ hbc
    exact cliqueStep_mono m le_rfl hbc
  · intro b _ t _
    exact le_cliqueStep m t b
  · intro b _ t _ u _
    exact cliqueStep_abs_sub_le m t u b b (abs_nonneg _) le_rfl (by simp)

@[simp] theorem cliqueRecursiveSystem_step (m : ℕ) (b t : DensityInterval) :
    ((cliqueRecursiveSystem m).step b t : ℝ) = cliqueStep m t b := rfl

/-- Infinite right composition, defined as the supremum of its finite
zero-terminal truncations. -/
def cliqueSequenceValue (m : ℕ) (b : ℕ → DensityInterval) : ℝ :=
  ((cliqueRecursiveSystem m).value b : ℝ)

theorem cliqueSequenceValue_mem (m : ℕ) (b : ℕ → DensityInterval) :
    cliqueSequenceValue m b ∈ Icc (0 : ℝ) 1 :=
  ((cliqueRecursiveSystem m).value b).property

theorem cliqueSequenceValue_tail (m : ℕ) (b : ℕ → DensityInterval) :
    cliqueSequenceValue m b =
      cliqueStep m (cliqueSequenceValue m (fun i => b (i + 1))) (b 0) := by
  exact congrArg (fun t : DensityInterval => (t : ℝ))
    ((cliqueRecursiveSystem m).value_tail b)

theorem cliqueSequenceValue_shift_succ (m : ℕ) (b : ℕ → DensityInterval) (n : ℕ) :
    cliqueSequenceValue m (fun i => b (i + n)) =
      cliqueStep m (cliqueSequenceValue m (fun i => b (i + (n + 1)))) (b n) := by
  simpa only [Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 n] using
    cliqueSequenceValue_tail m (fun i => b (i + n))

theorem cliqueSequenceValue_mono (m : ℕ) {b c : ℕ → DensityInterval}
    (hbc : ∀ i, b i ≤ c i) : cliqueSequenceValue m b ≤ cliqueSequenceValue m c :=
  (cliqueRecursiveSystem m).value_parameter_mono hbc

/-- A constant sequence has exactly the compact ratio value, with no strict
contraction assumption. -/
theorem cliqueSequenceValue_constant (m : ℕ) (b : DensityInterval) :
    cliqueSequenceValue m (fun _ => b) = cliqueRatioValue m b := by
  let μ : DensityInterval :=
    ⟨cliqueRatioValue m b, cliqueRatioValue_nonneg m b, cliqueRatioValue_le_one m b.property.2⟩
  have hμ : IsLeast {t : DensityInterval | (cliqueRecursiveSystem m).step b t ≤ t} μ := by
    constructor
    · change cliqueStep m (cliqueRatioValue m b) b ≤ cliqueRatioValue m b
      exact (cliqueRatioValue_fixed m b).le
    · intro t ht
      exact cliqueRatioValue_le_of_fixed_bound m b t t.property.1 ht
  exact congrArg (fun t : DensityInterval => (t : ℝ))
    ((cliqueRecursiveSystem m).value_constant_eq_of_isLeast b μ hμ)

theorem cliqueSequenceValue_gt_base (m : ℕ) (a : DensityInterval)
    (b : ℕ → DensityInterval) (hμ : 0 < cliqueRatioValue m a)
    (hb : ∀ i, a < b i) : cliqueRatioValue m a < cliqueSequenceValue m b := by
  have htail : cliqueRatioValue m a ≤
      cliqueSequenceValue m (fun i => b (i + 1)) := by
    rw [← cliqueSequenceValue_constant m a]
    exact cliqueSequenceValue_mono m (fun i => (hb (i + 1)).le)
  rw [cliqueSequenceValue_tail]
  exact (cliqueStep_above_base m a.property.1 hμ (hb 0)).trans_le
    (cliqueStep_mono m htail le_rfl)

/-- Every infinite pattern with side values approximable from below has the
same finite-graph realization property. -/
theorem belowLagrangianApprox_cliqueSequenceValue (m : ℕ)
    (b : ℕ → DensityInterval) (hb : ∀ i, BelowLagrangianApprox 3 (b i : ℝ)) :
    BelowLagrangianApprox 3 (cliqueSequenceValue m b) := by
  have htr (n : ℕ) (c : ℕ → DensityInterval)
      (hc : ∀ i, BelowLagrangianApprox 3 (c i : ℝ)) :
      BelowLagrangianApprox 3 ((cliqueRecursiveSystem m).truncation c n : ℝ) := by
    induction n generalizing c with
    | zero => exact belowLagrangianApprox_zero 3
    | succ n ih =>
        exact belowLagrangianApprox_cliqueStep m
          (ih (fun i => c (i + 1)) (fun i => hc (i + 1))) (hc 0)
  exact BelowLagrangianApprox.of_tendsto_from_below
    (fun n => htr n b hb) (fun n => (cliqueRecursiveSystem m).truncation_le_value b n)
    ((cliqueRecursiveSystem m).tendsto_truncation_real b)

/-- The compact ratio maximum varies by at most the side coefficient. -/
theorem cliqueRatioValue_lipschitz (m : ℕ) : LipschitzWith 1 (cliqueRatioValue m) := by
  apply LipschitzWith.of_dist_le_mul
  intro b c
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using cliqueRatioValue_abs_sub_le m b c

/-- Tail values of a decreasing coefficient sequence are trapped between the
constant limiting value and the constant value at the current coefficient. -/
theorem cliqueSequenceValue_tail_bounds (m : ℕ) (b : ℕ → DensityInterval)
    (a : DensityInterval) (hb : Antitone b) (ha : ∀ n, a ≤ b n) (n : ℕ) :
    cliqueRatioValue m a ≤ cliqueSequenceValue m (fun i => b (i + n)) ∧
      cliqueSequenceValue m (fun i => b (i + n)) ≤ cliqueRatioValue m (b n) := by
  constructor
  · rw [← cliqueSequenceValue_constant m a]
    exact cliqueSequenceValue_mono m (fun i => ha (i + n))
  · rw [← cliqueSequenceValue_constant m (b n)]
    exact cliqueSequenceValue_mono m (fun i => hb (Nat.le_add_left n i))

/-- Smoothness is unnecessary for this tail limit: antitonicity and convergence
of the side coefficients suffice. Smoothness is used only in the overlap step. -/
theorem cliqueSequenceValue_tails_tendsto (m : ℕ) (b : ℕ → DensityInterval)
    (a : DensityInterval) (hb : Antitone b)
    (hlim : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (a : ℝ))) :
    Tendsto (fun n => cliqueSequenceValue m (fun i => b (i + n)))
      atTop (𝓝 (cliqueRatioValue m a)) := by
  have ha (n : ℕ) : a ≤ b n := by
    change (a : ℝ) ≤ (b n : ℝ)
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop n] with k hk
    exact hb hk
  have hupper := (cliqueRatioValue_lipschitz m).continuous.continuousAt.tendsto.comp hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => (cliqueSequenceValue_tail_bounds m b a hb ha n).1)
    (fun n => (cliqueSequenceValue_tail_bounds m b a hb ha n).2)

end

end IntervalsTuran.Spectrum
