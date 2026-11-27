module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-!
# Values of recursive interval constructions

Finite values are right compositions of monotone interval maps applied to zero.
Their supremum is a limit and satisfies the first-step recursion. The maps are
only assumed nonexpansive, not strictly contracting.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace IntervalsTuran.Analysis

open Set Filter
open scoped Topology

noncomputable section

/-- The closed interval of admissible densities. -/
abbrev DensityInterval := unitInterval

/-- The exact order and metric assumptions used for recursive density maps.
All inputs lie in the unit interval; no global real-line property is imposed. -/
structure RecursiveSystem where
  step : DensityInterval → DensityInterval → DensityInterval
  monotone_input : ∀ b, Monotone (step b)
  monotone_parameter : ∀ t, Monotone (fun b => step b t)
  le_step : ∀ b t, t ≤ step b t
  nonexpansive : ∀ b, LipschitzWith 1 (step b)

namespace RecursiveSystem

/-- Restrict real-valued recursion maps to their invariant unit interval.
Every hypothesis is guarded by membership in the unit interval. -/
def ofReal (ψ : ℝ → ℝ → ℝ)
    (hmem : ∀ b ∈ DensityInterval, ∀ t ∈ DensityInterval,
      ψ b t ∈ DensityInterval)
    (htmono : ∀ b ∈ DensityInterval, MonotoneOn (ψ b) DensityInterval)
    (hbmono : ∀ t ∈ DensityInterval, MonotoneOn (fun b => ψ b t) DensityInterval)
    (hle : ∀ b ∈ DensityInterval, ∀ t ∈ DensityInterval, t ≤ ψ b t)
    (hlip : ∀ b ∈ DensityInterval, ∀ t ∈ DensityInterval, ∀ u ∈ DensityInterval,
      |ψ b t - ψ b u| ≤ |t - u|) : RecursiveSystem where
  step b t := ⟨ψ b t, hmem b b.property t t.property⟩
  monotone_input b := fun t u htu => htmono b b.property t.property u.property htu
  monotone_parameter t := fun b c hbc => hbmono t t.property b.property c.property hbc
  le_step b t := hle b b.property t t.property
  nonexpansive b := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
      hlip b b.property t t.property u u.property

variable (S : RecursiveSystem)

/-- A finite right-composed prefix acting on an arbitrary terminal value. -/
def prefixMap (S : RecursiveSystem) (b : ℕ → DensityInterval) : ℕ → DensityInterval → DensityInterval
  | 0, t => t
  | n + 1, t => S.step (b 0) (S.prefixMap (fun i => b (i + 1)) n t)

/-- The value of a finite truncation, with zero at the terminal branch. -/
def truncation (b : ℕ → DensityInterval) (n : ℕ) : DensityInterval :=
  S.prefixMap b n 0

@[simp] theorem prefix_zero (b : ℕ → DensityInterval) (t : DensityInterval) :
    S.prefixMap b 0 t = t := rfl

@[simp] theorem prefix_succ (b : ℕ → DensityInterval) (n : ℕ) (t : DensityInterval) :
    S.prefixMap b (n + 1) t = S.step (b 0) (S.prefixMap (fun i => b (i + 1)) n t) := rfl

@[simp] theorem truncation_zero (b : ℕ → DensityInterval) :
    S.truncation b 0 = 0 := rfl

@[simp] theorem truncation_succ (b : ℕ → DensityInterval) (n : ℕ) :
    S.truncation b (n + 1) = S.step (b 0) (S.truncation (fun i => b (i + 1)) n) := rfl

theorem prefix_monotone (b : ℕ → DensityInterval) (n : ℕ) :
    Monotone (S.prefixMap b n) := by
  induction n generalizing b with
  | zero => exact monotone_id
  | succ n ih =>
      exact (S.monotone_input (b 0)).comp (ih (fun i => b (i + 1)))

theorem prefix_lipschitz (b : ℕ → DensityInterval) (n : ℕ) :
    LipschitzWith 1 (S.prefixMap b n) := by
  induction n generalizing b with
  | zero => exact LipschitzWith.id
  | succ n ih =>
      have heq : S.prefixMap b (n + 1) =
          S.step (b 0) ∘ S.prefixMap (fun i => b (i + 1)) n := by
        funext t
        rfl
      rw [heq]
      simpa only [one_mul] using
        (S.nonexpansive (b 0)).comp (ih (fun i => b (i + 1)))

theorem prefix_continuous (b : ℕ → DensityInterval) (n : ℕ) :
    Continuous (S.prefixMap b n) := (S.prefix_lipschitz b n).continuous

/-- A finite prefix does not increase the real distance between terminal values. -/
theorem prefix_abs_sub_le (b : ℕ → DensityInterval) (n : ℕ)
    (t u : DensityInterval) :
    |(S.prefixMap b n t : ℝ) - (S.prefixMap b n u : ℝ)| ≤ |(t : ℝ) - (u : ℝ)| := by
  simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
    (S.prefix_lipschitz b n).dist_le_mul t u

theorem le_prefix (b : ℕ → DensityInterval) (n : ℕ) (t : DensityInterval) :
    t ≤ S.prefixMap b n t := by
  induction n generalizing b with
  | zero => exact le_rfl
  | succ n ih => exact (ih (fun i => b (i + 1))).trans (S.le_step _ _)

theorem truncation_le_succ (b : ℕ → DensityInterval) (n : ℕ) :
    S.truncation b n ≤ S.truncation b (n + 1) := by
  induction n generalizing b with
  | zero => exact bot_le
  | succ n ih =>
      exact S.monotone_input (b 0) (ih (fun i => b (i + 1)))

theorem truncation_monotone (b : ℕ → DensityInterval) :
    Monotone (S.truncation b) := monotone_nat_of_le_succ (S.truncation_le_succ b)

theorem prefix_parameter_mono {b c : ℕ → DensityInterval}
    (hbc : ∀ i, b i ≤ c i) (n : ℕ) (t : DensityInterval) :
    S.prefixMap b n t ≤ S.prefixMap c n t := by
  induction n generalizing b c with
  | zero => exact le_rfl
  | succ n ih =>
      exact (S.monotone_input (b 0) (ih (fun i => hbc (i + 1)))).trans
        (S.monotone_parameter _ (hbc 0))

theorem truncation_parameter_mono {b c : ℕ → DensityInterval}
    (hbc : ∀ i, b i ≤ c i) (n : ℕ) :
    S.truncation b n ≤ S.truncation c n := S.prefix_parameter_mono hbc n 0

/-- The infinite recursive value is the supremum of its finite truncations. -/
def value (b : ℕ → DensityInterval) : DensityInterval :=
  ⨆ n, S.truncation b n

theorem value_real_eq_iSup (b : ℕ → DensityInterval) :
    (S.value b : ℝ) = ⨆ n, (S.truncation b n : ℝ) := by
  exact Set.Icc.coe_iSup (show (0 : ℝ) ≤ 1 from zero_le_one)

theorem truncation_le_value (b : ℕ → DensityInterval) (n : ℕ) :
    S.truncation b n ≤ S.value b := le_iSup (S.truncation b) n

theorem value_le {b : ℕ → DensityInterval} {t : DensityInterval}
    (h : ∀ n, S.truncation b n ≤ t) : S.value b ≤ t := iSup_le h

theorem tendsto_truncation (b : ℕ → DensityInterval) :
    Tendsto (S.truncation b) atTop (𝓝 (S.value b)) :=
  tendsto_atTop_iSup (S.truncation_monotone b)

theorem tendsto_truncation_real (b : ℕ → DensityInterval) :
    Tendsto (fun n => (S.truncation b n : ℝ)) atTop (𝓝 (S.value b : ℝ)) :=
  continuous_subtype_val.continuousAt.tendsto.comp (S.tendsto_truncation b)

theorem value_parameter_mono {b c : ℕ → DensityInterval}
    (hbc : ∀ i, b i ≤ c i) : S.value b ≤ S.value c :=
  iSup_mono (fun n => S.truncation_parameter_mono hbc n)

/-- A common supersolution bounds every finite truncation. -/
theorem truncation_le_of_step_le {b : ℕ → DensityInterval} {t : DensityInterval}
    (hb : ∀ i, S.step (b i) t ≤ t) (n : ℕ) : S.truncation b n ≤ t := by
  induction n generalizing b with
  | zero => exact bot_le
  | succ n ih =>
      exact (S.monotone_input (b 0) (ih (fun i => hb (i + 1)))).trans (hb 0)

/-- A common supersolution also bounds the infinite recursive value. -/
theorem value_le_of_step_le {b : ℕ → DensityInterval} {t : DensityInterval}
    (hb : ∀ i, S.step (b i) t ≤ t) : S.value b ≤ t :=
  S.value_le (S.truncation_le_of_step_le hb)

/-- The first-step recursion passes to the infinite limit. -/
theorem value_tail (b : ℕ → DensityInterval) :
    S.value b = S.step (b 0) (S.value (fun i => b (i + 1))) := by
  have h₁ := (S.tendsto_truncation b).comp (tendsto_add_atTop_nat 1)
  have h₂ := (S.nonexpansive (b 0)).continuous.continuousAt.tendsto.comp
    (S.tendsto_truncation (fun i => b (i + 1)))
  apply tendsto_nhds_unique h₁
  simpa only [Function.comp_def, truncation_succ] using h₂

theorem value_constant_fixed (b : DensityInterval) :
    S.value (fun _ => b) = S.step b (S.value (fun _ => b)) :=
  S.value_tail (fun _ => b)

/-- The constant-sequence value is the least supersolution. This gives a
direct characterization of a baseline recursive value without any strict
contraction hypothesis. -/
theorem value_constant_isLeast (b : DensityInterval) :
    IsLeast {t : DensityInterval | S.step b t ≤ t} (S.value (fun _ => b)) := by
  constructor
  · exact (S.value_constant_fixed b).ge
  · intro t ht
    exact S.value_le_of_step_le (fun _ => ht)

theorem value_constant_eq_of_isLeast (b t : DensityInterval)
    (ht : IsLeast {u : DensityInterval | S.step b u ≤ u} t) :
    S.value (fun _ => b) = t :=
  (S.value_constant_isLeast b).unique ht

/-- Splitting a finite composition into a prefix and the remaining suffix. -/
theorem prefix_add (b : ℕ → DensityInterval) (k n : ℕ) (t : DensityInterval) :
    S.prefixMap b (k + n) t =
      S.prefixMap b k (S.prefixMap (fun i => b (i + k)) n t) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
      simpa only [Nat.succ_add, prefix_succ, Nat.add_assoc] using
        congrArg (S.step (b 0)) (ih (fun i => b (i + 1)))

/-- Any finite prefix can be separated from the infinite recursive tail. -/
theorem value_prefix (b : ℕ → DensityInterval) (k : ℕ) :
    S.value b = S.prefixMap b k (S.value (fun i => b (i + k))) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
      rw [S.value_tail b, ih (fun i => b (i + 1))]
      simp only [prefix_succ, Nat.add_assoc]

end RecursiveSystem

end

end IntervalsTuran.Analysis
