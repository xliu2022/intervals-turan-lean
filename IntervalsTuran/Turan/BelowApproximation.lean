module

public import IntervalsTuran.Turan.LagrangianCap

/-!
# Finite witnesses and diagonal limits from below

Author and maintainer: Xizhi Liu.

This file provides the finite-epsilon form of Lagrangian approximation and its
closure under limits approached from below.  In particular it does not assume
that the whole Turan spectrum is topologically closed.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran

theorem belowLagrangianApprox_iff {r : ℕ} {x : ℝ} :
    BelowLagrangianApprox r x ↔
      ∀ ε : ℝ, 0 < ε → ∃ G : FiniteGraph r,
        G.2.lagrangian ≤ x ∧ x - ε < G.2.lagrangian := by
  constructor
  · rintro ⟨G, hbelow, hlim⟩ ε hε
    have hev : ∀ᶠ n in atTop, x - ε < (G n).2.lagrangian :=
      hlim.eventually (eventually_gt_nhds (by linarith : x - ε < x))
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨G n, hbelow n, hn⟩
  · intro h
    have hex (n : ℕ) : ∃ G : FiniteGraph r,
        G.2.lagrangian ≤ x ∧ x - ((n + 1 : ℕ) : ℝ)⁻¹ < G.2.lagrangian :=
      h _ (by positivity)
    choose G hG using hex
    refine ⟨G, fun n => (hG n).1, ?_⟩
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hinv' := (tendsto_add_atTop_iff_nat 1).mpr hinv
    have hlo : Tendsto (fun n : ℕ => x - ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.sub hinv'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun n => (hG n).2.le) (fun n => (hG n).1)

theorem BelowLagrangianApprox.of_tendsto_from_below {r : ℕ}
    {u : ℕ → ℝ} {x : ℝ} (hu : ∀ n, BelowLagrangianApprox r (u n))
    (hbelow : ∀ n, u n ≤ x) (hlim : Tendsto u atTop (𝓝 x)) :
    BelowLagrangianApprox r x := by
  apply belowLagrangianApprox_iff.mpr
  intro ε hε
  have hev : ∀ᶠ n in atTop, x - ε / 2 < u n :=
    hlim.eventually (eventually_gt_nhds (by linarith : x - ε / 2 < x))
  obtain ⟨n, hn⟩ := hev.exists
  obtain ⟨G, hG, hclose⟩ := belowLagrangianApprox_iff.mp (hu n) (ε / 2) (by linarith)
  exact ⟨G, hG.trans (hbelow n), by linarith⟩

theorem BelowLagrangianApprox.of_monotone_tendsto {r : ℕ}
    {u : ℕ → ℝ} {x : ℝ} (hu : ∀ n, BelowLagrangianApprox r (u n))
    (hmono : Monotone u) (hlim : Tendsto u atTop (𝓝 x)) :
    BelowLagrangianApprox r x := by
  apply BelowLagrangianApprox.of_tendsto_from_below hu _ hlim
  intro n
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hmono hm

theorem belowLagrangianApprox_lagrangian {r : ℕ} (G : FiniteGraph r) :
    BelowLagrangianApprox r G.2.lagrangian :=
  ⟨fun _ => G, fun _ => le_rfl, tendsto_const_nhds⟩

theorem finite_lagrangian_mem_turanSpectrum {r : ℕ} (hr : 0 < r)
    (G : FiniteGraph r) : G.2.lagrangian ∈ turanSpectrum r :=
  (belowLagrangianApprox_lagrangian G).mem_turanSpectrum hr

end IntervalsTuran
