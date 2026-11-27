module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Intervals of ordinary hypergraph Turán densities

Liu and Pikhurko, *Intervals of hypergraph Turán densities*, Theorem 1.1
(arXiv:2605.25914v1). For every uniformity at least three, every real number
in some closed interval ending at one is the ordinary Turán density of a
family of finite hypergraphs. The forbidden family may be infinite.
-/

@[expose] public section

namespace IntervalsTuran

universe u v

/-- A simple uniform hypergraph on `V`. Each edge is a set of exactly `r`
vertices. Vertices outside all edges are allowed. -/
structure RGraph (V : Type u) [DecidableEq V] (r : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

/-- A copy of `F` in `H` is injective on all vertices and maps edges to edges. -/
def RGraph.IsEmbedding {V : Type u} {W : Type v}
    [DecidableEq V] [DecidableEq W] {r : ℕ}
    (F : RGraph V r) (H : RGraph W r) (f : V → W) : Prop :=
  Function.Injective f ∧ ∀ e ∈ F.edges, e.image f ∈ H.edges

/-- A labelled finite `r`-graph together with its number of vertices. -/
abbrev FiniteGraph (r : ℕ) := Σ n : ℕ, RGraph (Fin n) r

namespace SetFamily

variable {r : ℕ}

/-- The host contains no copy of any member of the forbidden family. -/
def Free {V : Type u} [DecidableEq V] (F : Set (FiniteGraph r)) (G : RGraph V r) : Prop :=
  ∀ A ∈ F, ¬ ∃ f, A.2.IsEmbedding G f

/-- The supremum of the attainable edge counts on `n` vertices. These
natural numbers are bounded by `n.choose r`, so this is their maximum
when a host exists. The empty set of counts has supremum zero in `ℕ`. -/
noncomputable def extremalEdgeCount (F : Set (FiniteGraph r)) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : RGraph (Fin n) r, Free F G ∧ G.edges.card = k}

end SetFamily

open Filter Topology

/-- Theorem 1.1. For each `r ≥ 3` there is a positive `δ` such that each
`x ∈ [1 − δ, 1]` is the limit of the normalized extremal numbers of some
family of finite `r`-graphs. -/
theorem terminal_interval_of_turan_density_limits :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ F : Set (FiniteGraph r),
          Tendsto (fun n : ℕ => (SetFamily.extremalEdgeCount F n : ℝ) / (n.choose r : ℝ))
            atTop (𝓝 x) := by
  sorry

end IntervalsTuran
