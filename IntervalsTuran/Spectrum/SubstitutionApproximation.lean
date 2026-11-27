module

public import IntervalsTuran.Spectrum.SubstitutionValue
public import IntervalsTuran.Turan.BelowApproximation
public import IntervalsTuran.Construction.CompleteGraphs

/-!
# Finite substitution preserves approximation from below

Author and maintainer: Xizhi Liu.

The finite substitution constructor and exact optimization formula are reused
from `TuranUniversality`.  This file supplies their realization theorem for
`BelowLagrangianApprox`, keeping the upper bound on every finite witness.
-/

@[expose] public section

namespace IntervalsTuran.Spectrum

open Filter Topology

variable {r : ℕ}

theorem exists_nonempty_lagrangian_representative (G : FiniteGraph r) :
    ∃ H : FiniteGraph r, 0 < H.1 ∧ H.2.lagrangian = G.2.lagrangian := by
  rcases G with ⟨n, G⟩
  cases n with
  | zero =>
    refine ⟨⟨1, RGraph.empty (Fin 1) r⟩, by change 0 < (1 : ℕ); omega, ?_⟩
    simp
  | succ n => exact ⟨⟨n + 1, G⟩, Nat.succ_pos _, rfl⟩

theorem exists_nonempty_below_lagrangian_sequence {a : ℝ}
    (ha : BelowLagrangianApprox r a) :
    ∃ G : ℕ → FiniteGraph r, (∀ n, 0 < (G n).1) ∧
      (∀ n, (G n).2.lagrangian ≤ a) ∧
      Tendsto (fun n => (G n).2.lagrangian) atTop (𝓝 a) := by
  obtain ⟨G, hbelow, hlim⟩ := ha
  choose H hpos hval using fun n => exists_nonempty_lagrangian_representative (G n)
  exact ⟨H, hpos, fun n => (hval n).trans_le (hbelow n), by simpa only [hval] using hlim⟩

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The optimization is continuous in the finitely many child values. -/
theorem substitutionValue_tendsto (H : RGraph I r) (hr : 0 < r)
    {b : ℕ → I → ℝ} {c : I → ℝ}
    (h : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (c i))) :
    Tendsto (fun n => substitutionValue H (b n)) atTop (𝓝 (substitutionValue H c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ n in atTop, ∀ i, |b n i - c i| < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro i
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (h i)) (ε / 2) (by linarith)
  filter_upwards [he] with n hn
  rw [Real.dist_eq]
  exact (substitutionValue_abs_sub_le H hr (b n) c (by linarith)
    (fun i => (hn i).le)).trans_lt (by linarith)

/-- Relabel the actual substituted graph to the canonical finite carrier. -/
noncomputable def finiteSubstitute (H : RGraph I r) (G : I → FiniteGraph r) :
    FiniteGraph r :=
  let V : I → Type := fun i => Fin (G i).1
  let J := substitute H (fun i => (G i).2)
  ⟨Fintype.card (Sigma V), J.pullback (Fintype.equivFin (Sigma V)).symm.toEmbedding⟩

theorem finiteSubstitute_lagrangian (H : RGraph I r) (hr : 2 ≤ r)
    (G : I → FiniteGraph r) (hpos : ∀ i, 0 < (G i).1) :
    (finiteSubstitute H G).2.lagrangian =
      substitutionValue H (fun i => (G i).2.lagrangian) := by
  let V : I → Type := fun i => Fin (G i).1
  let J : RGraph (Sigma V) r := substitute H (fun i => (G i).2)
  let e : Fin (Fintype.card (Sigma V)) ≃ Sigma V := (Fintype.equivFin _).symm
  let (i : I) : Nonempty (V i) := ⟨⟨0, hpos i⟩⟩
  have heq : (J.pullback e.toEmbedding).lagrangian = J.lagrangian :=
    le_antisymm (J.pullback_equiv_embedding e).isHom.lagrangian_le
      (J.pullback_equiv_inverse e).isHom.lagrangian_le
  exact heq.trans (lagrangian_substitute H (fun i => (G i).2) hr)

theorem belowLagrangianApprox_substitutionValue (H : RGraph I r) (hr : 2 ≤ r)
    (b : I → ℝ) (hb : ∀ i, BelowLagrangianApprox r (b i)) :
    BelowLagrangianApprox r (substitutionValue H b) := by
  classical
  choose G hpos hbelow hlim using fun i => exists_nonempty_below_lagrangian_sequence (hb i)
  refine ⟨fun n => finiteSubstitute H (fun i => G i n), ?_, ?_⟩
  · intro n
    rw [finiteSubstitute_lagrangian H hr _ (fun i => hpos i n)]
    exact substitutionValue_mono H (fun i => hbelow i n)
  · have heq (n : ℕ) := finiteSubstitute_lagrangian H hr
      (fun i => G i n) (fun i => hpos i n)
    simpa only [heq] using substitutionValue_tendsto H (by omega) hlim

end IntervalsTuran.Spectrum
