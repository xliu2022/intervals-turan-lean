module

public import IntervalsTuran.Analysis.GreedyApproximation
public import IntervalsTuran.Turan.BelowApproximation
public import IntervalsTuran.Construction.Lifting

/-!
# Realizing an interval from overlapping finite recursive constructions

Author and maintainer: Xizhi Liu.

The hypotheses in this file describe a family of recursive maps and its tails.
They are explicit hypotheses, not axioms.  The conclusions use the actual set
of ordinary Turan densities defined from forbidden families of finite graphs.
This reduction does not by itself establish the concrete spectral construction
required by Liu--Pikhurko, Theorem 1.1.
-/

@[expose] public section

open Filter Set Topology

namespace IntervalsTuran

/-- Greedy finite compositions and a diagonal limit realize every point of the
closed interval.  The left endpoint is supplied separately as a finite-graph
approximation; no topological closedness of the whole spectrum is assumed. -/
theorem belowLagrangianApprox_interval_of_recursive_overlap
    {r : ℕ} {ψ : ℕ → ℝ → ℝ} {μ : ℝ} {ν : ℕ → ℝ}
    (hψmono : ∀ n, Monotone (ψ n))
    (hψlip : ∀ n, LipschitzWith 1 (ψ n))
    (hbase : ∀ n, μ ≤ ψ n μ)
    (hνμ : ∀ n, μ ≤ ν n) (hνlim : Tendsto ν atTop (𝓝 μ))
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ n, ψ n μ ≤ ν (n + 1))
    (hμ : BelowLagrangianApprox r μ)
    (hpres : ∀ n x, BelowLagrangianApprox r x → BelowLagrangianApprox r (ψ n x)) :
    Icc μ (ν 0) ⊆ {x | BelowLagrangianApprox r x} := by
  intro y hy
  change BelowLagrangianApprox r y
  rcases eq_or_lt_of_le hy.1 with h | h
  · simpa only [← h] using hμ
  · obtain ⟨u, hmono, hu, -, hlim⟩ :=
      exists_sequence_in_set_tendsto_of_recursive_overlap
        (C := {x | BelowLagrangianApprox r x}) hψmono hψlip hbase hνμ
        hνlim hrec hoverlap hμ hpres h hy.2
    exact BelowLagrangianApprox.of_monotone_tendsto hu hmono hlim

/-- The preceding interval consists of genuine ordinary Turan densities. -/
theorem turanSpectrum_interval_of_recursive_overlap
    {r : ℕ} (hr : 0 < r) {ψ : ℕ → ℝ → ℝ} {μ : ℝ} {ν : ℕ → ℝ}
    (hψmono : ∀ n, Monotone (ψ n))
    (hψlip : ∀ n, LipschitzWith 1 (ψ n))
    (hbase : ∀ n, μ ≤ ψ n μ)
    (hνμ : ∀ n, μ ≤ ν n) (hνlim : Tendsto ν atTop (𝓝 μ))
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ n, ψ n μ ≤ ν (n + 1))
    (hμ : BelowLagrangianApprox r μ)
    (hpres : ∀ n x, BelowLagrangianApprox r x → BelowLagrangianApprox r (ψ n x)) :
    Icc μ (ν 0) ⊆ turanSpectrum r := by
  intro x hx
  exact (belowLagrangianApprox_interval_of_recursive_overlap
    hψmono hψlip hbase hνμ hνlim hrec hoverlap hμ hpres hx).mem_turanSpectrum hr

/-- Eventual overlap suffices: discard a finite prefix, and retain a strictly
positive interval whenever every recursive tail is above the base value. -/
theorem exists_belowLagrangianApprox_interval_of_eventual_recursive_overlap
    {r : ℕ} {ψ : ℕ → ℝ → ℝ} {μ : ℝ} {ν : ℕ → ℝ}
    (hψmono : ∀ n, Monotone (ψ n))
    (hψlip : ∀ n, LipschitzWith 1 (ψ n))
    (hbase : ∀ n, μ ≤ ψ n μ)
    (hνμ : ∀ n, μ < ν n) (hνlim : Tendsto ν atTop (𝓝 μ))
    (hrec : ∀ n, ν n = ψ n (ν (n + 1)))
    (hoverlap : ∀ᶠ n in atTop, ψ n μ ≤ ν (n + 1))
    (hμ : BelowLagrangianApprox r μ)
    (hpres : ∀ n x, BelowLagrangianApprox r x → BelowLagrangianApprox r (ψ n x)) :
    ∃ b : ℝ, μ < b ∧ Icc μ b ⊆ {x | BelowLagrangianApprox r x} := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hoverlap
  refine ⟨ν N, hνμ N, ?_⟩
  have hlim : Tendsto (fun n => ν (n + N)) atTop (𝓝 μ) :=
    (tendsto_add_atTop_iff_nat N).mpr hνlim
  have h := belowLagrangianApprox_interval_of_recursive_overlap
    (ψ := fun n => ψ (n + N)) (ν := fun n => ν (n + N))
    (fun n => hψmono (n + N)) (fun n => hψlip (n + N))
    (fun n => hbase (n + N)) (fun n => (hνμ (n + N)).le) hlim
    (fun n => by simpa only [Nat.add_right_comm] using hrec (n + N))
    (fun n => by
      simpa only [Nat.add_right_comm] using hN (n + N) (Nat.le_add_left N n))
    hμ (fun n => hpres (n + N))
  simpa only [Nat.zero_add] using h

/-- A nondegenerate interval of approximable 3-graph Lagrangians produces one
in every higher uniformity by the exact suspension construction. -/
theorem exists_lifted_belowLagrangianApprox_interval
    {a b : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ {x | BelowLagrangianApprox 3 x})
    {r : ℕ} (hr : 3 ≤ r) :
    ∃ c d : ℝ, c < d ∧ Icc c d ⊆ {x | BelowLagrangianApprox r x} := by
  have hscale := liftScale_pos (show 0 < r by omega)
  refine ⟨liftScale r * a, liftScale r * b, mul_lt_mul_of_pos_left hab hscale, ?_⟩
  intro y hy
  change BelowLagrangianApprox r y
  have hya : a ≤ y / liftScale r := (le_div_iff₀ hscale).mpr (by
    simpa only [mul_comm] using hy.1)
  have hyb : y / liftScale r ≤ b := (div_le_iff₀ hscale).mpr (by
    simpa only [mul_comm] using hy.2)
  have h := (hI ⟨hya, hyb⟩).lift hr
  simpa only [mul_div_cancel₀ _ (ne_of_gt hscale)] using h

end IntervalsTuran
