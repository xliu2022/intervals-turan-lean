module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

/-!
# Greedy finite-prefix approximation

This file formalizes the scalar interval-filling argument behind Section 4 of
Liu--Pikhurko, *Intervals of hypergraph Turán densities*. The recursive maps are
assumed monotone and nonexpansive, and consecutive recursive tails overlap.
The proof constructs finite compositions and proves their convergence directly;
it does not assume an interval-covering or density-realization theorem.

Author and maintainer: Xizhi Liu.
-/

public section

open Filter Set
open scoped Topology

namespace IntervalsTuran

/-- The finite composition obtained after examining the first `n` indices.
An index is included exactly when its new lower endpoint remains below `y`. -/
@[expose]
noncomputable def greedyPrefix (ψ : ℕ → ℝ → ℝ) (μ y : ℝ) : ℕ → ℝ → ℝ := by
  classical
  exact Nat.rec id (fun n F => if F (ψ n μ) < y then F ∘ ψ n else F)

@[simp]
theorem greedyPrefix_zero (ψ : ℕ → ℝ → ℝ) (μ y : ℝ) :
    greedyPrefix ψ μ y 0 = id := rfl

theorem greedyPrefix_succ (ψ : ℕ → ℝ → ℝ) (μ y : ℝ) (n : ℕ) :
    greedyPrefix ψ μ y (n + 1) =
      if greedyPrefix ψ μ y n (ψ n μ) < y then
        greedyPrefix ψ μ y n ∘ ψ n else greedyPrefix ψ μ y n := by
  classical
  rfl

/-- Every greedy prefix is monotone when every input map is monotone. -/
theorem greedyPrefix_monotone
    {ψ : ℕ → ℝ → ℝ} (hψ : ∀ n, Monotone (ψ n)) (μ y : ℝ) (n : ℕ) :
    Monotone (greedyPrefix ψ μ y n) := by
  classical
  induction n with
  | zero => simpa only [greedyPrefix_zero] using (monotone_id : Monotone (id : ℝ → ℝ))
  | succ n ih =>
    rw [greedyPrefix_succ]
    split_ifs
    · exact ih.comp (hψ n)
    · exact ih

/-- Every greedy prefix is nonexpansive when every input map is nonexpansive. -/
theorem greedyPrefix_lipschitz
    {ψ : ℕ → ℝ → ℝ} (hψ : ∀ n, LipschitzWith 1 (ψ n)) (μ y : ℝ) (n : ℕ) :
    LipschitzWith 1 (greedyPrefix ψ μ y n) := by
  classical
  induction n with
  | zero => simpa only [greedyPrefix_zero] using (LipschitzWith.id (α := ℝ))
  | succ n ih =>
    rw [greedyPrefix_succ]
    split_ifs
    · simpa only [one_mul] using ih.comp (hψ n)
    · exact ih

/-- The greedy lower endpoint stays strictly below the target, while the full
remaining tail stays above it. This is preserved both when an index is accepted
and when it is rejected. -/
theorem greedyPrefix_invariant
    {ψ : ℕ → ℝ → ℝ} {μ y : ℝ} {ν : ℕ → ℝ}
    (hψ : ∀ n, Monotone (ψ n))
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ n, ψ n μ ≤ ν (n + 1))
    (hμy : μ < y) (hyν : y ≤ ν 0) (n : ℕ) :
    greedyPrefix ψ μ y n μ < y ∧ y ≤ greedyPrefix ψ μ y n (ν n) := by
  classical
  induction n with
  | zero => simpa only [greedyPrefix_zero, id_eq] using And.intro hμy hyν
  | succ n ih =>
    rw [greedyPrefix_succ]
    by_cases htake : greedyPrefix ψ μ y n (ψ n μ) < y
    · simp only [ite_eq_left htake, Function.comp_apply]
      refine ⟨htake, ?_⟩
      simpa only [← hrec n] using ih.2
    · simp only [ite_eq_right htake]
      refine ⟨ih.1, ?_⟩
      exact (le_of_not_gt htake).trans
        (greedyPrefix_monotone hψ μ y n (hoverlap n))

/-- A quantitative error estimate for each finite greedy prefix. -/
theorem greedyPrefix_error_bound
    {ψ : ℕ → ℝ → ℝ} {μ y : ℝ} {ν : ℕ → ℝ}
    (hψmono : ∀ n, Monotone (ψ n))
    (hψlip : ∀ n, LipschitzWith 1 (ψ n))
    (hνμ : ∀ n, μ ≤ ν n)
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ n, ψ n μ ≤ ν (n + 1))
    (hμy : μ < y) (hyν : y ≤ ν 0) (n : ℕ) :
    0 ≤ y - greedyPrefix ψ μ y n μ ∧
      y - greedyPrefix ψ μ y n μ ≤ ν n - μ := by
  have hi := greedyPrefix_invariant hψmono hrec hoverlap hμy hyν n
  have hdist :
      |greedyPrefix ψ μ y n (ν n) - greedyPrefix ψ μ y n μ| ≤ |ν n - μ| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (greedyPrefix_lipschitz hψlip μ y n).dist_le_mul (ν n) μ
  rw [abs_of_nonneg (sub_nonneg.mpr (hνμ n))] at hdist
  have hwidth : greedyPrefix ψ μ y n (ν n) - greedyPrefix ψ μ y n μ ≤ ν n - μ :=
    (le_abs_self _).trans hdist
  constructor <;> linarith

/-- Finite greedy lower endpoints converge to the specified target. -/
theorem greedyPrefix_tendsto
    {ψ : ℕ → ℝ → ℝ} {μ y : ℝ} {ν : ℕ → ℝ}
    (hψmono : ∀ n, Monotone (ψ n))
    (hψlip : ∀ n, LipschitzWith 1 (ψ n))
    (hνμ : ∀ n, μ ≤ ν n) (hνlim : Tendsto ν atTop (𝓝 μ))
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ n, ψ n μ ≤ ν (n + 1))
    (hμy : μ < y) (hyν : y ≤ ν 0) :
    Tendsto (fun n => greedyPrefix ψ μ y n μ) atTop (𝓝 y) := by
  have hlower : Tendsto (fun n => y - (ν n - μ)) atTop (𝓝 y) := by
    simpa only [sub_self, sub_zero] using
      (tendsto_const_nhds (x := y)).sub
        (hνlim.sub (tendsto_const_nhds (x := μ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    have he := (greedyPrefix_error_bound hψmono hψlip hνμ hrec hoverlap hμy hyν n).2
    linarith
  · intro n
    exact (greedyPrefix_invariant hψmono hrec hoverlap hμy hyν n).1.le

/-- If each map raises the base value, the greedy lower endpoints are
nondecreasing. Rejected indices leave the lower endpoint unchanged. -/
theorem greedyPrefix_lower_monotone
    {ψ : ℕ → ℝ → ℝ} {μ y : ℝ}
    (hψmono : ∀ n, Monotone (ψ n)) (hbase : ∀ n, μ ≤ ψ n μ) :
    Monotone (fun n => greedyPrefix ψ μ y n μ) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  rw [greedyPrefix_succ]
  split_ifs
  · exact greedyPrefix_monotone hψmono μ y n (hbase n)
  · exact le_rfl

/-- Finite prefixes preserve any set preserved by all the input maps. -/
theorem greedyPrefix_mapsTo
    {ψ : ℕ → ℝ → ℝ} {C : Set ℝ} (hψC : ∀ n, MapsTo (ψ n) C C)
    (μ y : ℝ) (n : ℕ) : MapsTo (greedyPrefix ψ μ y n) C C := by
  classical
  induction n with
  | zero =>
    intro x hx
    simpa only [greedyPrefix_zero, id_eq] using hx
  | succ n ih =>
    rw [greedyPrefix_succ]
    split_ifs
    · exact ih.comp (hψC n)
    · exact ih

/-- A target between the base value and the initial full tail has monotone
finite-prefix approximants in any invariant set containing the base value.
All approximants remain strictly below the target and converge to it. -/
theorem exists_sequence_in_set_tendsto_of_recursive_overlap
    {ψ : ℕ → ℝ → ℝ} {μ y : ℝ} {ν : ℕ → ℝ} {C : Set ℝ}
    (hψmono : ∀ n, Monotone (ψ n))
    (hψlip : ∀ n, LipschitzWith 1 (ψ n))
    (hbase : ∀ n, μ ≤ ψ n μ)
    (hνμ : ∀ n, μ ≤ ν n) (hνlim : Tendsto ν atTop (𝓝 μ))
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ n, ψ n μ ≤ ν (n + 1))
    (hμC : μ ∈ C) (hψC : ∀ n, MapsTo (ψ n) C C)
    (hμy : μ < y) (hyν : y ≤ ν 0) :
    ∃ u : ℕ → ℝ, Monotone u ∧ (∀ n, u n ∈ C) ∧
      (∀ n, μ ≤ u n ∧ u n < y) ∧ Tendsto u atTop (𝓝 y) := by
  have hmono := greedyPrefix_lower_monotone (y := y) hψmono hbase
  refine ⟨fun n => greedyPrefix ψ μ y n μ, hmono, ?_, ?_, ?_⟩
  · exact fun n => greedyPrefix_mapsTo hψC μ y n hμC
  · intro n
    refine ⟨?_, (greedyPrefix_invariant hψmono hrec hoverlap hμy hyν n).1⟩
    simpa only [greedyPrefix_zero, id_eq] using hmono (Nat.zero_le n)
  · exact greedyPrefix_tendsto hψmono hψlip hνμ hνlim hrec hoverlap hμy hyν

end IntervalsTuran
