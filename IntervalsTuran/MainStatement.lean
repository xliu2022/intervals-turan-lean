module

public import IntervalsTuran.Turan.LagrangianCap

/-!
# The exact target statement of Liu--Pikhurko, Theorem 1.1

This file DEFINES the target proposition.  It does not assert a proof of it.
All notions expand to finite simple hypergraphs, globally injective embeddings,
arbitrary forbidden families, and the ordinary binomial-normalized extremal
limit (whose existence is proved in Density.SetFamilyExtremal).

Author and maintainer: Xizhi Liu.
Source: Xizhi Liu and Oleg Pikhurko, arXiv:2605.25914v1.
-/

@[expose] public section

namespace IntervalsTuran

/-- The terminal-interval conclusion at one uniformity. -/
def TerminalIntervalClaim (r : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Set.Icc (1 - δ) 1 ⊆ turanSpectrum r

/-- Theorem 1.1 as a proposition, with no spectral or interval hypothesis. -/
def MainTheoremStatement : Prop :=
  ∀ r : ℕ, 3 ≤ r → TerminalIntervalClaim r

/-- A definition-expansion audit of the target, rather than a proof of it. -/
theorem terminalIntervalClaim_iff (r : ℕ) :
    TerminalIntervalClaim r ↔
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ F : Set (FiniteGraph r), SetFamily.turanDensity F = x := by
  simp only [TerminalIntervalClaim, Set.subset_def, Set.mem_Icc, turanSpectrum,
    Set.mem_range, and_imp]

end IntervalsTuran
