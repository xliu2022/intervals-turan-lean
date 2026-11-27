module

public import IntervalsTuran.Analysis.TerminalIntervals
public import IntervalsTuran.Turan.RecursiveInterval
public import IntervalsTuran.Construction.CompleteGraphs
public import IntervalsTuran.MainStatement

/-!
# Terminal-interval reduction on finite-graph approximations

Author and maintainer: Xizhi Liu.

This file connects the numerical covering lemma to ordinary Turan density.
The complete-join realization property is explicit at this interface and must
be discharged by the finite construction and its diffuse blow-up limit.
-/

@[expose] public section

namespace IntervalsTuran

open Set

theorem terminalIntervalClaim_of_join_preserves_below
    {r : ℕ} (hr : 2 ≤ r)
    (hjoin : ∀ M : ℕ, 2 ≤ M → ∀ x : ℝ, BelowLagrangianApprox r x →
      BelowLagrangianApprox r (1 - (1 - x) / (M : ℝ) ^ (r - 1)))
    {a b : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ {x | BelowLagrangianApprox r x}) :
    TerminalIntervalClaim r := by
  have hb : b ≤ 1 := (hI ⟨hab.le, le_rfl⟩).le_one
  obtain ⟨δ, hδ, hcover⟩ := exists_terminal_interval_of_join_closed
    (S := {x | BelowLagrangianApprox r x}) (show 0 < r - 1 by omega)
    (belowLagrangianApprox_one r) hjoin hab hb hI
  exact ⟨δ, hδ, fun _ hx => (hcover hx).mem_turanSpectrum (by omega)⟩

/-- A three-uniform interval, exact suspension, and the actual complete-join
closure theorem suffice for the target statement in all uniformities. -/
theorem mainTheoremStatement_of_three_interval_and_join_preserves_below
    (hjoin : ∀ r : ℕ, 3 ≤ r → ∀ M : ℕ, 2 ≤ M → ∀ x : ℝ,
      BelowLagrangianApprox r x →
      BelowLagrangianApprox r (1 - (1 - x) / (M : ℝ) ^ (r - 1)))
    {a b : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ {x | BelowLagrangianApprox 3 x}) :
    MainTheoremStatement := by
  intro r hr
  obtain ⟨c, d, hcd, hJ⟩ := exists_lifted_belowLagrangianApprox_interval hab hI hr
  exact terminalIntervalClaim_of_join_preserves_below (by omega) (hjoin r hr) hcd hJ

end IntervalsTuran
