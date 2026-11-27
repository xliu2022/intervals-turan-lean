module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Amplifying an interval to a terminal interval

This file proves the real-variable part of Section 5.1 of Liu--Pikhurko,
*Intervals of hypergraph Turán densities*. A set closed under the numerical
complete-join maps inherits a terminal interval from any nondegenerate interval.
The closure under complete joins is an explicit hypothesis; this file does not
assert a combinatorial realization of that hypothesis.

Author and maintainer: Xizhi Liu.
-/

public section

open Filter Set
open scoped Topology

namespace IntervalsTuran

/-- Consecutively overlapping intervals cover everything between the first
left endpoint and the limit of the left endpoints. Monotonicity of the endpoints
is unnecessary: take the first left endpoint strictly beyond the desired point. -/
theorem exists_mem_interval_of_consecutive_overlap
    {l u : ℕ → ℝ} {c y : ℝ}
    (hl : Tendsto l atTop (𝓝 c))
    (hoverlap : ∀ n, l (n + 1) ≤ u n)
    (hy0 : l 0 ≤ y) (hyc : y < c) :
    ∃ n : ℕ, y ∈ Icc (l n) (u n) := by
  classical
  have hex : ∃ n : ℕ, y < l n :=
    (hl.eventually (lt_mem_nhds hyc)).exists
  let n : ℕ := Nat.find hex
  have hn : y < l n := Nat.find_spec hex
  have hn_pos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    exact (not_lt_of_ge hy0) hn
  have hpred : n - 1 < n := by omega
  have hlo : l (n - 1) ≤ y := le_of_not_gt (Nat.find_min hex hpred)
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
  have hup : l n ≤ u (n - 1) := by
    simpa only [hsucc] using hoverlap (n - 1)
  exact ⟨n - 1, hlo, hn.le.trans hup⟩

/-- Intervals with endpoints `1 - A / M^d` and `1 - B / M^d` overlap
consecutively from some point on and cover a terminal half-open interval.
This is the numerical covering argument needed for complete joins. -/
theorem exists_terminal_cover_by_power_intervals
    {A B : ℝ} {d : ℕ} (hB : 0 ≤ B) (hBA : B < A) (hd : 0 < d) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧
      ∀ y : ℝ, 1 - A / (M₀ : ℝ) ^ d ≤ y → y < 1 →
        ∃ M : ℕ, M₀ ≤ M ∧
          y ∈ Icc (1 - A / (M : ℝ) ^ d) (1 - B / (M : ℝ) ^ d) := by
  have hA : 0 < A := hB.trans_lt hBA
  have hratio : Tendsto
      (fun M : ℕ => (M : ℝ) ^ d / ((M + 1 : ℕ) : ℝ) ^ d) atTop (𝓝 1) := by
    simpa only [div_pow, one_pow, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_div_add_atTop (1 : ℝ)).pow d
  have hBA_one : B / A < 1 := (div_lt_one hA).mpr hBA
  have hevent : ∀ᶠ M : ℕ in atTop,
      B / A < (M : ℝ) ^ d / ((M + 1 : ℕ) : ℝ) ^ d :=
    hratio.eventually (lt_mem_nhds hBA_one)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let M₀ : ℕ := max N 2
  have hM₀ : 2 ≤ M₀ := le_max_right _ _
  have hoverlap (M : ℕ) (hM : M₀ ≤ M) :
      1 - A / ((M + 1 : ℕ) : ℝ) ^ d ≤ 1 - B / (M : ℝ) ^ d := by
    have hMpos_nat : 0 < M := lt_of_lt_of_le (by omega : 0 < M₀) hM
    have hMpos : 0 < (M : ℝ) ^ d := pow_pos (by exact_mod_cast hMpos_nat) d
    have hMnext : 0 < ((M + 1 : ℕ) : ℝ) ^ d := by positivity
    have hr := hN M ((le_max_left N 2).trans hM)
    have hcross : B * ((M + 1 : ℕ) : ℝ) ^ d < (M : ℝ) ^ d * A :=
      (div_lt_div_iff₀ hA hMnext).mp hr
    have hdiv : B / (M : ℝ) ^ d ≤ A / ((M + 1 : ℕ) : ℝ) ^ d := by
      apply (div_le_div_iff₀ hMpos hMnext).mpr
      simpa only [mul_comm] using hcross.le
    exact sub_le_sub_left hdiv 1
  have hscale : Tendsto (fun M : ℕ => (M : ℝ) ^ d) atTop atTop :=
    (tendsto_pow_atTop (ne_of_gt hd)).comp tendsto_natCast_atTop_atTop
  have hleft : Tendsto (fun M : ℕ => 1 - A / (M : ℝ) ^ d) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (hscale.const_div_atTop A)
  refine ⟨M₀, hM₀, ?_⟩
  intro y hy0 hy1
  have hlshift : Tendsto
      (fun n : ℕ => 1 - A / ((n + M₀ : ℕ) : ℝ) ^ d) atTop (𝓝 1) :=
    hleft.comp (tendsto_add_atTop_nat M₀)
  have hovershift (n : ℕ) :
      1 - A / (((n + 1) + M₀ : ℕ) : ℝ) ^ d ≤
        1 - B / ((n + M₀ : ℕ) : ℝ) ^ d := by
    simpa only [Nat.add_right_comm] using hoverlap (n + M₀) (by omega)
  obtain ⟨n, hn⟩ := exists_mem_interval_of_consecutive_overlap hlshift hovershift
    (by simpa only [zero_add] using hy0) hy1
  exact ⟨n + M₀, by omega, hn⟩

/-- A subset of the real line that contains `1`, is closed under all numerical
complete-join maps, and contains a nondegenerate interval below `1`, contains an
entire terminal interval. The exponent is any positive integer.

This statement isolates the real analysis from the separate hypergraph theorem
that realizes the complete-join maps on a Turán spectrum. -/
theorem exists_terminal_interval_of_join_closed
    {S : Set ℝ} {d : ℕ} (hd : 0 < d) (h1 : (1 : ℝ) ∈ S)
    (hjoin : ∀ M : ℕ, 2 ≤ M → ∀ x : ℝ, x ∈ S →
      1 - (1 - x) / (M : ℝ) ^ d ∈ S)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 1) (habS : Icc a b ⊆ S) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (1 - δ) 1 ⊆ S := by
  let A : ℝ := 1 - a
  let B : ℝ := 1 - b
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hBA : B < A := by dsimp [A, B]; linarith
  have hA : 0 < A := hB.trans_lt hBA
  obtain ⟨M₀, hM₀, hcover⟩ := exists_terminal_cover_by_power_intervals hB hBA hd
  have hM₀pos : 0 < (M₀ : ℝ) ^ d := by
    apply pow_pos
    exact_mod_cast (by omega : 0 < M₀)
  refine ⟨A / (M₀ : ℝ) ^ d, div_pos hA hM₀pos, ?_⟩
  intro y hy
  by_cases hyone : y = 1
  · simpa only [hyone] using h1
  have hylt : y < 1 := lt_of_le_of_ne hy.2 hyone
  obtain ⟨M, hM, hyM⟩ := hcover y hy.1 hylt
  have hMtwo : 2 ≤ M := hM₀.trans hM
  have hC : 0 < (M : ℝ) ^ d := by
    apply pow_pos
    exact_mod_cast (by omega : 0 < M)
  let x : ℝ := 1 - (1 - y) * (M : ℝ) ^ d
  have hupper : (1 - y) * (M : ℝ) ^ d ≤ A := by
    apply (le_div_iff₀ hC).mp
    linarith [hyM.1]
  have hlower : B ≤ (1 - y) * (M : ℝ) ^ d := by
    apply (div_le_iff₀ hC).mp
    linarith [hyM.2]
  have hx : x ∈ Icc a b := by
    dsimp [x, A, B] at *
    constructor <;> linarith
  have hresult := hjoin M hMtwo x (habS hx)
  have heq : 1 - (1 - x) / (M : ℝ) ^ d = y := by
    dsimp [x]
    field_simp [ne_of_gt hC]
    ring
  rwa [heq] at hresult

end IntervalsTuran
