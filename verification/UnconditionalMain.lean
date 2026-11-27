module

import IntervalsTuran.Main

/-! Check the exact unconditional target independently of the proof file. -/

example : IntervalsTuran.MainTheoremStatement := IntervalsTuran.main_theorem

example : ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
      ∃ forbidden : Set (IntervalsTuran.FiniteGraph r),
        IntervalsTuran.SetFamily.turanDensity forbidden = x :=
  IntervalsTuran.ordinary_density_terminal_interval

#check IntervalsTuran.main_theorem
#check IntervalsTuran.ordinary_density_terminal_interval
#print axioms IntervalsTuran.main_theorem
#print axioms IntervalsTuran.ordinary_density_terminal_interval

run_cmd Lean.logInfo "UNCONDITIONAL MAIN VERIFIED: exact target and ordinary-density expansion"
