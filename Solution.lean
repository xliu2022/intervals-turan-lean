module

public import IntervalsTuran.Main
public import Mathlib.Order.Lattice.Nat

/-! # Liu–Pikhurko's terminal interval theorem in its ordinary limit form -/

@[expose] public section

namespace IntervalsTuran

namespace SetFamily

variable {r : ℕ}

/-- The supremum of the edge counts of `F`-free hosts on `n` vertices. -/
noncomputable def extremalEdgeCount (F : Set (FiniteGraph r)) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = k}

/-- Taking the supremum gives the library's extremal number, including
when no host avoids the family. -/
theorem extremalEdgeCount_eq (F : Set (FiniteGraph r)) (n : ℕ) :
    extremalEdgeCount F n = extremalNumber F n := by
  let counts : Set ℕ := {k | ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = k}
  have bounded : BddAbove counts := by
    refine ⟨n.choose r, ?_⟩
    rintro k ⟨G, _, rfl⟩
    exact G.edge_card_le_choose
  change sSup counts = extremalNumber F n
  apply le_antisymm
  · apply csSup_le'
    rintro k ⟨G, hG, rfl⟩
    exact edge_card_le_extremalNumber F G hG
  · apply (extremalNumber_le_iff F n _).2
    intro G hG
    exact le_csSup bounded (show G.edges.card ∈ counts from ⟨G, hG, rfl⟩)

end SetFamily

open Filter Topology

/-- Every point of a terminal interval is a limit of ordinary extremal
densities. The forbidden family is supplied by the main theorem. -/
theorem terminal_interval_of_turan_density_limits :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ F : Set (FiniteGraph r),
          Tendsto (fun n : ℕ => (SetFamily.extremalEdgeCount F n : ℝ) / (n.choose r : ℝ))
            atTop (𝓝 x) := by
  intro r hr
  obtain ⟨δ, hδ, realize⟩ := ordinary_density_terminal_interval r hr
  refine ⟨δ, hδ, ?_⟩
  intro x hlo hhi
  obtain ⟨F, hF⟩ := realize x hlo hhi
  refine ⟨F, ?_⟩
  simpa only [SetFamily.extremalEdgeCount_eq, SetFamily.extremalDensity, hF] using
    SetFamily.extremalDensity_tendsto F

end IntervalsTuran
