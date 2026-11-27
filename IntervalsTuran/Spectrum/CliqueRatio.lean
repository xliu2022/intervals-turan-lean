module

public import IntervalsTuran.Spectrum.CliqueStep

@[expose] public section

/-! # A compact formula for the least clique-substitution fixed point

Author and maintainer: Xizhi Liu.

Adapted from `TuranUniversality/Spectrum/CliqueRecursive.lean`; provenance and
source hash are recorded in `docs/reused-analysis.json`.

Separating the recursive part with mass `s` gives a continuous quotient
on a compact product. Its value at `s = 1` is explicitly zero; no singular
quotient or implicit fixed-point choice enters the construction.
-/

namespace IntervalsTuran.Spectrum

open Finset Set

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def splitWeights (m : ℕ) (s : ℝ) (y : Fin (m + 1) → ℝ) : Fin (m + 2) → ℝ :=
  Fin.cons s (fun i => (1 - s) * y i)

theorem splitWeights_probability (m : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {y : Fin (m + 1) → ℝ} (hy : ProbabilityWeights y) :
    ProbabilityWeights (splitWeights m s y) := by
  constructor
  · intro i
    refine Fin.cases hs.1 (fun j => ?_) i
    exact mul_nonneg (sub_nonneg.mpr hs.2) (hy.1 j)
  · simp only [splitWeights, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ← Finset.mul_sum, hy.2, mul_one]
    ring

theorem splitWeights_sum_pow (m : ℕ) (s : ℝ) (y : Fin (m + 1) → ℝ) (k : ℕ) :
    (∑ i, splitWeights m s y i ^ k) = s ^ k + (1 - s) ^ k * ∑ i, y i ^ k := by
  simp only [splitWeights, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    mul_pow, ← Finset.mul_sum]

theorem splitWeights_clique (m : ℕ) (s : ℝ) {y : Fin (m + 1) → ℝ}
    (hy : ProbabilityWeights y) :
    6 * (RGraph.clique (Fin (m + 2)) 3).edgePolynomial (splitWeights m s y) =
      3 * s * (1 - s) ^ 2 * (1 - ∑ i, y i ^ 2) +
        (1 - s) ^ 3 * (6 * (RGraph.clique (Fin (m + 1)) 3).edgePolynomial y) := by
  rw [clique_polynomial_cubic, clique_polynomial_cubic,
    splitWeights_sum_pow, splitWeights_sum_pow]
  have hsum : (∑ i, splitWeights m s y i) = 1 := by
    simp only [splitWeights, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      ← Finset.mul_sum, hy.2, mul_one]
    ring
  rw [hsum, hy.2]
  ring

noncomputable def cliqueRatio (m : ℕ) (b s : ℝ) (y : Fin (m + 1) → ℝ) : ℝ :=
  (1 - s) * (3 * s * (1 - ∑ i, y i ^ 2) +
    (1 - s) * (6 * (RGraph.clique (Fin (m + 1)) 3).edgePolynomial y + b * y 0 ^ 3)) /
      (1 + s + s ^ 2)

theorem cliqueRatio_den_pos (s : ℝ) : 0 < 1 + s + s ^ 2 := by
  nlinarith [sq_nonneg (s + 1 / 2)]

@[simp] theorem cliqueRatio_one (m : ℕ) (b : ℝ) (y : Fin (m + 1) → ℝ) :
    cliqueRatio m b 1 y = 0 := by simp [cliqueRatio]

theorem cliqueRatio_continuous (m : ℕ) (b : ℝ) :
    Continuous (fun p : ℝ × (Fin (m + 1) → ℝ) => cliqueRatio m b p.1 p.2) := by
  unfold cliqueRatio RGraph.edgePolynomial
  fun_prop (disch := intro p; exact ne_of_gt (cliqueRatio_den_pos p.1))

theorem cliqueStepObjective_split (m : ℕ) (t b s : ℝ)
    {y : Fin (m + 1) → ℝ} (hy : ProbabilityWeights y) :
    cliqueStepObjective m t b (splitWeights m s y) =
      t * s ^ 3 + (1 - s ^ 3) * cliqueRatio m b s y := by
  unfold cliqueStepObjective
  rw [splitWeights_clique m s hy]
  have h0 : splitWeights m s y 0 = s := rfl
  have h1 : splitWeights m s y 1 = (1 - s) * y 0 := rfl
  rw [h0, h1]
  unfold cliqueRatio
  field_simp [ne_of_gt (cliqueRatio_den_pos s)]
  ring

def cliqueRatioDomain (m : ℕ) : Set (ℝ × (Fin (m + 1) → ℝ)) :=
  Set.Icc (0 : ℝ) 1 ×ˢ {y | ProbabilityWeights y}

theorem cliqueRatioDomain_compact (m : ℕ) : IsCompact (cliqueRatioDomain m) :=
  isCompact_Icc.prod probabilityWeights_isCompact

theorem cliqueRatioDomain_nonempty (m : ℕ) : (cliqueRatioDomain m).Nonempty := by
  obtain ⟨y, hy⟩ := probabilityWeights_nonempty (V := Fin (m + 1))
  exact ⟨(0, y), ⟨by norm_num, hy⟩⟩

noncomputable def cliqueRatioValue (m : ℕ) (b : ℝ) : ℝ :=
  sSup ((fun p : ℝ × (Fin (m + 1) → ℝ) => cliqueRatio m b p.1 p.2) ''
    cliqueRatioDomain m)

theorem cliqueRatio_values_bddAbove (m : ℕ) (b : ℝ) :
    BddAbove ((fun p : ℝ × (Fin (m + 1) → ℝ) => cliqueRatio m b p.1 p.2) ''
      cliqueRatioDomain m) :=
  ((cliqueRatioDomain_compact m).image (cliqueRatio_continuous m b)).bddAbove

theorem cliqueRatio_le_value (m : ℕ) (b : ℝ) {s : ℝ} {y : Fin (m + 1) → ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hy : ProbabilityWeights y) :
    cliqueRatio m b s y ≤ cliqueRatioValue m b :=
  le_csSup (cliqueRatio_values_bddAbove m b) ⟨(s, y), ⟨hs, hy⟩, rfl⟩

theorem cliqueRatioValue_le_iff (m : ℕ) (b c : ℝ) : cliqueRatioValue m b ≤ c ↔
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y, ProbabilityWeights y → cliqueRatio m b s y ≤ c := by
  constructor
  · intro h s hs y hy
    exact (cliqueRatio_le_value m b hs hy).trans h
  · intro h
    apply csSup_le ((cliqueRatioDomain_nonempty m).image _)
    rintro z ⟨⟨s, y⟩, ⟨hs, hy⟩, rfl⟩
    exact h s hs y hy

theorem exists_cliqueRatio_maximizer (m : ℕ) (b : ℝ) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ y, ProbabilityWeights y ∧
      cliqueRatio m b s y = cliqueRatioValue m b := by
  obtain ⟨⟨s, y⟩, ⟨hs, hy⟩, hmax⟩ :=
    (cliqueRatioDomain_compact m).exists_isMaxOn (cliqueRatioDomain_nonempty m)
      (cliqueRatio_continuous m b).continuousOn
  refine ⟨s, hs, y, hy, le_antisymm (cliqueRatio_le_value m b hs hy) ?_⟩
  exact (cliqueRatioValue_le_iff m b _).mpr (fun t ht z hz =>
    hmax (show (t, z) ∈ cliqueRatioDomain m from ⟨ht, hz⟩))

theorem cliqueRatioValue_nonneg (m : ℕ) (b : ℝ) : 0 ≤ cliqueRatioValue m b := by
  obtain ⟨y, hy⟩ := probabilityWeights_nonempty (V := Fin (m + 1))
  simpa only [cliqueRatio_one] using cliqueRatio_le_value m b (s := 1) (by norm_num) hy

theorem probabilityWeights_split {m : ℕ} (x : Fin (m + 2) → ℝ)
    (hx : ProbabilityWeights x) (h0 : x 0 < 1) :
    ∃ y : Fin (m + 1) → ℝ, ProbabilityWeights y ∧ splitWeights m (x 0) y = x := by
  let y : Fin (m + 1) → ℝ := fun i => x i.succ / (1 - x 0)
  have hs : 0 < 1 - x 0 := sub_pos.mpr h0
  have hsum : ∑ i : Fin (m + 1), x i.succ = 1 - x 0 := by
    have hh := hx.2
    rw [Fin.sum_univ_succ] at hh
    linarith
  refine ⟨y, ⟨fun i => div_nonneg (hx.1 _) hs.le, ?_⟩, ?_⟩
  · dsimp only [y]
    rw [← Finset.sum_div, hsum, div_self (ne_of_gt hs)]
  · funext i
    refine Fin.cases rfl (fun j => ?_) i
    change (1 - x 0) * (x j.succ / (1 - x 0)) = x j.succ
    field_simp [ne_of_gt hs]

theorem cliqueStep_fixed_bound_iff (m : ℕ) (b c : ℝ) (hc : 0 ≤ c) :
    cliqueStep m c b ≤ c ↔ cliqueRatioValue m b ≤ c := by
  rw [cliqueStep_le_iff, cliqueRatioValue_le_iff]
  constructor
  · intro h s hs y hy
    by_cases hz : s = 1
    · simpa only [hz, cliqueRatio_one] using hc
    · have hs' : s < 1 := lt_of_le_of_ne hs.2 hz
      have hp : 0 < 1 - s ^ 3 := sub_pos.mpr (pow_lt_one₀ hs.1 hs' (by omega))
      have hh := h (splitWeights m s y) (splitWeights_probability m hs hy)
      rw [cliqueStepObjective_split m c b s hy] at hh
      nlinarith
  · intro h x hx
    by_cases hz : x 0 < 1
    · obtain ⟨y, hy, he⟩ := probabilityWeights_split x hx hz
      rw [← he, cliqueStepObjective_split m c b (x 0) hy]
      have hb := h (x 0) ⟨hx.1 0, hx.apply_le_one 0⟩ y hy
      have hn : 0 ≤ 1 - x 0 ^ 3 :=
        sub_nonneg.mpr (pow_le_one₀ (hx.1 0) (hx.apply_le_one 0))
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hb)]
    · have hx0 : x 0 = 1 := le_antisymm (hx.apply_le_one 0) (le_of_not_gt hz)
      have hxrest : ∀ i : Fin (m + 1), x i.succ = 0 := by
        have hs : ∑ i : Fin (m + 1), x i.succ = 0 := by
          have hh := hx.2
          rw [Fin.sum_univ_succ, hx0] at hh
          linarith
        exact fun i => (Finset.sum_eq_zero_iff_of_nonneg
          (f := fun j : Fin (m + 1) => x j.succ) (fun j _ => hx.1 j.succ)).mp hs i (by simp)
      have he : x = fun i => if i = 0 then 1 else 0 := by
        funext i
        refine Fin.cases (by simp [hx0]) (fun j => ?_) i
        simp [hxrest]
      unfold cliqueStepObjective
      rw [clique_polynomial_cubic, he]
      norm_num

theorem cliqueRatioValue_fixed (m : ℕ) (b : ℝ) :
    cliqueStep m (cliqueRatioValue m b) b = cliqueRatioValue m b :=
  le_antisymm ((cliqueStep_fixed_bound_iff m b _ (cliqueRatioValue_nonneg m b)).mpr le_rfl)
    (le_cliqueStep m _ _)

theorem cliqueRatioValue_le_of_fixed_bound (m : ℕ) (b c : ℝ) (hc : 0 ≤ c)
    (h : cliqueStep m c b ≤ c) : cliqueRatioValue m b ≤ c :=
  (cliqueStep_fixed_bound_iff m b c hc).mp h

theorem cliqueRatioValue_abs_sub_le (m : ℕ) (b b' : ℝ) :
    |cliqueRatioValue m b - cliqueRatioValue m b'| ≤ |b - b'| := by
  have hbound (u v : ℝ) : cliqueRatioValue m u ≤ cliqueRatioValue m v + |u - v| := by
    apply cliqueRatioValue_le_of_fixed_bound m u _
      (add_nonneg (cliqueRatioValue_nonneg m v) (abs_nonneg _))
    have hh := cliqueStep_abs_sub_le m (cliqueRatioValue m v + |u - v|)
      (cliqueRatioValue m v) u v (abs_nonneg _) (by simp) le_rfl
    rw [cliqueRatioValue_fixed] at hh
    linarith [(abs_le.mp hh).2]
  exact abs_le.mpr ⟨by have := hbound b' b; rw [abs_sub_comm b' b] at this; linarith,
    by have := hbound b b'; linarith⟩

end IntervalsTuran.Spectrum
