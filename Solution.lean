module

public import IntervalsTuran.Main

/-! # Liu–Pikhurko's terminal interval theorem in its ordinary limit form -/

public section

namespace IntervalsTuran

open Filter Topology

/-- Every point of a terminal interval is a limit of ordinary extremal
densities. The forbidden family is supplied by the main theorem. -/
theorem terminal_interval_of_turan_density_limits :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ F : Set (FiniteGraph r), Tendsto (SetFamily.extremalDensity F) atTop (𝓝 x) := by
  intro r hr
  obtain ⟨δ, hδ, realize⟩ := ordinary_density_terminal_interval r hr
  refine ⟨δ, hδ, ?_⟩
  intro x hlo hhi
  obtain ⟨F, hF⟩ := realize x hlo hhi
  exact ⟨F, hF ▸ SetFamily.extremalDensity_tendsto F⟩

end IntervalsTuran
