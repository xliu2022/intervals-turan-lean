module

public import IntervalsTuran.Spectrum.CliqueRatio
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Least fixed points and positive branches of the concrete clique recursion

Author and maintainer: Xizhi Liu.

The retained analytic proofs were adapted from
`TuranUniversality/Spectrum/CliqueRecursive.lean`; exact source hash and
extraction details appear in `docs/reused-analysis.json`.
-/

@[expose] public section

namespace IntervalsTuran.Spectrum

open Finset Set Filter Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem clique_add_cubes_le_one {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) (hx : ProbabilityWeights x) :
    6 * (RGraph.clique I 3).edgePolynomial x + ∑ i, x i ^ 3 ≤ 1 := by
  have hs : (∑ i, x i ^ 3) ≤ ∑ i, x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [pow_succ]
    exact mul_le_of_le_one_right (sq_nonneg _) (hx.apply_le_one i)
  have hp := clique_polynomial_cubic x
  rw [hx.2] at hp
  nlinarith

theorem cliqueStep_le_one (m : ℕ) {t b : ℝ} (ht : t ≤ 1) (hb : b ≤ 1) :
    cliqueStep m t b ≤ 1 := by
  apply (substitutionValue_le_iff _ _ _).mpr
  intro x hx
  have hs : (∑ i, twoCoefficients m t b i * x i ^ 3) ≤ ∑ i, x i ^ 3 := by
    apply Finset.sum_le_sum
    intro i _
    have hi : twoCoefficients m t b i ≤ 1 := by
      unfold twoCoefficients
      split
      · exact ht
      · split
        · exact hb
        · norm_num
    exact mul_le_of_le_one_left (pow_nonneg (hx.1 i) _) hi
  have hh := clique_add_cubes_le_one x hx
  change ((3 : ℕ).factorial : ℝ) * (RGraph.clique (Fin (m + 2)) 3).edgePolynomial x +
    ∑ i, twoCoefficients m t b i * x i ^ 3 ≤ 1
  norm_num only [Nat.factorial] at *
  linarith

theorem cliqueRatioValue_le_one (m : ℕ) {b : ℝ} (hb : b ≤ 1) :
    cliqueRatioValue m b ≤ 1 :=
  cliqueRatioValue_le_of_fixed_bound m b 1 (by norm_num) (cliqueStep_le_one m le_rfl hb)

theorem clique_lagrangian_le_ratio (m : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (RGraph.clique (Fin (m + 2)) 3).lagrangian ≤ cliqueRatioValue m b := by
  apply ((RGraph.clique (Fin (m + 2)) 3).lagrangian_le_iff
    (cliqueRatioValue_nonneg m b)).mpr
  intro x hx
  have hh := cliqueStepObjective_le m (cliqueRatioValue m b) b x hx
  rw [cliqueRatioValue_fixed] at hh
  have h0 := mul_nonneg (cliqueRatioValue_nonneg m b) (pow_nonneg (hx.1 0) 3)
  have h1 := mul_nonneg hb (pow_nonneg (hx.1 1) 3)
  norm_num only [Nat.factorial] at *
  unfold cliqueStepObjective at hh
  linarith

theorem cliqueStep_tendsto (m : ℕ) {t b : ℕ → ℝ} {t₀ b₀ : ℝ}
    (ht : Tendsto t atTop (𝓝 t₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun n => cliqueStep m (t n) (b n)) atTop (𝓝 (cliqueStep m t₀ b₀)) := by
  apply substitutionValue_tendsto _ (by omega)
  intro i
  unfold twoCoefficients
  split
  · exact ht
  · split
    · exact hb
    · exact tendsto_const_nhds

noncomputable def cliqueIter (m : ℕ) (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => cliqueStep m (cliqueIter m b n) b

theorem cliqueIter_mono (m : ℕ) (b : ℝ) : Monotone (cliqueIter m b) :=
  monotone_nat_of_le_succ (fun n => le_cliqueStep m _ _)

theorem cliqueIter_nonneg (m : ℕ) (b : ℝ) (n : ℕ) : 0 ≤ cliqueIter m b n :=
  cliqueIter_mono m b (Nat.zero_le n)

theorem cliqueIter_le_ratio (m : ℕ) (b : ℝ) (n : ℕ) :
    cliqueIter m b n ≤ cliqueRatioValue m b := by
  induction n with
  | zero => exact cliqueRatioValue_nonneg m b
  | succ n ih =>
    exact (cliqueStep_mono m ih le_rfl).trans_eq (cliqueRatioValue_fixed m b)

theorem cliqueIter_tendsto (m : ℕ) (b : ℝ) :
    Tendsto (cliqueIter m b) atTop (𝓝 (cliqueRatioValue m b)) := by
  have hbd : BddAbove (Set.range (cliqueIter m b)) :=
    ⟨cliqueRatioValue m b, fun _ ⟨n, hn⟩ => hn ▸ cliqueIter_le_ratio m b n⟩
  let c := ⨆ n, cliqueIter m b n
  have hc : Tendsto (cliqueIter m b) atTop (𝓝 c) :=
    tendsto_atTop_ciSup (cliqueIter_mono m b) hbd
  have hc0 : 0 ≤ c := ge_of_tendsto hc (Eventually.of_forall (cliqueIter_nonneg m b))
  have hcL : c ≤ cliqueRatioValue m b := ciSup_le (cliqueIter_le_ratio m b)
  have hcF : cliqueStep m c b = c := by
    have hs : Tendsto (fun n => cliqueIter m b (n + 1)) atTop (𝓝 c) :=
      (tendsto_add_atTop_iff_nat 1).mpr hc
    exact tendsto_nhds_unique (cliqueStep_tendsto m hc tendsto_const_nhds) hs
  have hLc : cliqueRatioValue m b ≤ c :=
    cliqueRatioValue_le_of_fixed_bound m b c hc0 hcF.le
  have he : c = cliqueRatioValue m b := le_antisymm hcL hLc
  simpa only [he] using hc

theorem cliqueRatio_equiv (m : ℕ) (b s : ℝ) (y : Fin (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    cliqueRatio m b s (y ∘ e) - cliqueRatio m b s y =
      (1 - s) ^ 2 * b * (y (e 0) ^ 3 - y 0 ^ 3) / (1 + s + s ^ 2) := by
  have hsum := Equiv.sum_comp e (fun i => y i ^ 2)
  have hpoly := clique_polynomial_equiv y e
  unfold cliqueRatio
  simp only [Function.comp_apply] at *
  rw [hsum, hpoly]
  ring

theorem exists_cliqueRatio_positive_second (m : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hL : 0 < cliqueRatioValue m b) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ y : Fin (m + 1) → ℝ,
      ProbabilityWeights y ∧ s < 1 ∧ 0 < y 0 ∧ cliqueRatio m b s y = cliqueRatioValue m b := by
  obtain ⟨s, hs, y, hy, hm⟩ := exists_cliqueRatio_maximizer m b
  have hs1 : s < 1 := by
    apply lt_of_le_of_ne hs.2
    intro he
    rw [he, cliqueRatio_one] at hm
    linarith
  by_cases hy0 : 0 < y 0
  · exact ⟨s, hs, y, hy, hs1, hy0, hm⟩
  · have hz : y 0 = 0 := le_antisymm (le_of_not_gt hy0) (hy.1 0)
    have hex : ∃ j : Fin (m + 1), 0 < y j := by
      by_contra h
      push Not at h
      have hs : (∑ i, y i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
      rw [hy.2] at hs
      norm_num at hs
    obtain ⟨j, hj⟩ := hex
    let e := Equiv.swap (0 : Fin (m + 1)) j
    have he0 : e 0 = j := Equiv.swap_apply_left _ _
    have hy' := probabilityWeights_equiv e y hy
    have hg := cliqueRatio_equiv m b s y e
    rw [he0, hz, zero_pow (by omega : 3 ≠ 0), sub_zero] at hg
    have hnonneg : 0 ≤ (1 - s) ^ 2 * b * y j ^ 3 / (1 + s + s ^ 2) := by
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hb) (pow_nonneg (hy.1 _) _))
        (cliqueRatio_den_pos s).le
    have hu := cliqueRatio_le_value m b hs hy'
    refine ⟨s, hs, y ∘ e, hy', hs1, by simpa only [Function.comp_apply, he0] using hj, ?_⟩
    linarith

theorem exists_cliqueStep_base_maximizer_second_pos (m : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hL : 0 < cliqueRatioValue m b) :
    ∃ x : Fin (m + 2) → ℝ, ProbabilityWeights x ∧ 0 < x 1 ∧
      cliqueStepObjective m (cliqueRatioValue m b) b x = cliqueRatioValue m b := by
  obtain ⟨s, hs, y, hy, hs1, hy0, hm⟩ := exists_cliqueRatio_positive_second m hb hL
  refine ⟨splitWeights m s y, splitWeights_probability m hs hy, ?_, ?_⟩
  · change 0 < (1 - s) * y 0
    exact mul_pos (sub_pos.mpr hs1) hy0
  · rw [cliqueStepObjective_split m _ b s hy, hm]
    ring

theorem cliqueStep_above_base (m : ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hL : 0 < cliqueRatioValue m a) (hab : a < b) :
    cliqueRatioValue m a < cliqueStep m (cliqueRatioValue m a) b := by
  obtain ⟨x, hx, hx1, hm⟩ := exists_cliqueStep_base_maximizer_second_pos m ha hL
  have hu := cliqueStepObjective_le m (cliqueRatioValue m a) b x hx
  have hp : 0 < (b - a) * x 1 ^ 3 := mul_pos (sub_pos.mpr hab) (pow_pos hx1 _)
  unfold cliqueStepObjective at hm hu
  nlinarith

theorem cliqueStep_strict_second (m : ℕ) {a b c : ℝ} (ha : 0 ≤ a)
    (hL : 0 < cliqueRatioValue m a) (hab : a ≤ b) (hbc : b < c) :
    cliqueStep m (cliqueRatioValue m a) b < cliqueStep m (cliqueRatioValue m a) c := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [cliqueRatioValue_fixed]
    exact cliqueStep_above_base m ha hL hbc
  · obtain ⟨x, hx, hm⟩ := exists_cliqueStep_maximizer m (cliqueRatioValue m a) b
    have hx1 : 0 < x 1 := by
      by_contra h
      have hz : x 1 = 0 := le_antisymm (le_of_not_gt h) (hx.1 1)
      have hu := cliqueStepObjective_le m (cliqueRatioValue m a) a x hx
      rw [cliqueRatioValue_fixed] at hu
      have hp := cliqueStep_above_base m ha hL hab
      simp only [cliqueStepObjective, hz, zero_pow (by omega : 3 ≠ 0), mul_zero,
        add_zero] at hm hu
      linarith
    have hu := cliqueStepObjective_le m (cliqueRatioValue m a) c x hx
    have hp : 0 < (c - b) * x 1 ^ 3 := mul_pos (sub_pos.mpr hbc) (pow_pos hx1 _)
    unfold cliqueStepObjective at hm hu
    nlinarith

end IntervalsTuran.Spectrum
