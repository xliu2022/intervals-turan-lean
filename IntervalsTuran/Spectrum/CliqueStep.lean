module

public import IntervalsTuran.Spectrum.SubstitutionApproximation
public import IntervalsTuran.Hypergraph.Clique
public import IntervalsTuran.Hypergraph.SymmetricSums

@[expose] public section

/-! # The two distinguished parts of the Pikhurko construction

Author and maintainer: Xizhi Liu.

Adapted from the existing `TuranUniversality` formalization; source hashes and
selection details are recorded in `docs/reused-analysis.json`.

The base is an actual complete 3-graph. One part receives the recursive tail
value and a second part receives the next finite-graph Lagrangian. All other
parts have no internal edges. The operation is the exact substitution maximum.
-/

namespace IntervalsTuran.Spectrum

open Finset

set_option backward.isDefEq.respectTransparency false

theorem clique_polynomial_cubic {I : Type*} [Fintype I] [DecidableEq I] (x : I → ℝ) :
    6 * (RGraph.clique I 3).edgePolynomial x =
      (∑ i, x i) ^ 3 - 3 * (∑ i, x i) * (∑ i, x i ^ 2) + 2 * ∑ i, x i ^ 3 :=
  Weighted.elementary_third_identity Finset.univ x

theorem clique_polynomial_equiv {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) (e : I ≃ I) :
    (RGraph.clique I 3).edgePolynomial (x ∘ e) = (RGraph.clique I 3).edgePolynomial x := by
  have h1 := Equiv.sum_comp e x
  have h2 := Equiv.sum_comp e (fun i => x i ^ 2)
  have h3 := Equiv.sum_comp e (fun i => x i ^ 3)
  have hp := clique_polynomial_cubic (x ∘ e)
  have hq := clique_polynomial_cubic x
  simp only [Function.comp_apply] at hp
  rw [h1, h2, h3] at hp
  linarith only [hp, hq]

def twoCoefficients (m : ℕ) (t b : ℝ) (i : Fin (m + 2)) : ℝ :=
  if i = 0 then t else if i = 1 then b else 0

noncomputable def cliqueStep (m : ℕ) (t b : ℝ) : ℝ :=
  substitutionValue (RGraph.clique (Fin (m + 2)) 3) (twoCoefficients m t b)

def cliqueStepObjective (m : ℕ) (t b : ℝ) (x : Fin (m + 2) → ℝ) : ℝ :=
  6 * (RGraph.clique (Fin (m + 2)) 3).edgePolynomial x + t * x 0 ^ 3 + b * x 1 ^ 3

theorem twoCoefficients_objective (m : ℕ) (t b : ℝ) (x : Fin (m + 2) → ℝ) :
    substitutionObjective (RGraph.clique (Fin (m + 2)) 3) (twoCoefficients m t b) x =
      cliqueStepObjective m t b x := by
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have he (i : Fin (m + 2)) :
      twoCoefficients m t b i * x i ^ 3 =
        (if i = 0 then t * x i ^ 3 else 0) + (if i = 1 then b * x i ^ 3 else 0) := by
    by_cases h0 : i = 0
    · subst i
      simp [twoCoefficients, h01]
    · by_cases h1 : i = 1 <;> simp [twoCoefficients, h0, h1]
  simp only [substitutionObjective, he, Finset.sum_add_distrib]
  simp [cliqueStepObjective, Nat.factorial, add_assoc]

theorem exists_cliqueStep_maximizer (m : ℕ) (t b : ℝ) :
    ∃ x, ProbabilityWeights x ∧ cliqueStepObjective m t b x = cliqueStep m t b := by
  simpa only [cliqueStep, twoCoefficients_objective] using
    exists_substitution_maximizer (RGraph.clique (Fin (m + 2)) 3) (twoCoefficients m t b)

theorem cliqueStepObjective_le (m : ℕ) (t b : ℝ) (x : Fin (m + 2) → ℝ)
    (hx : ProbabilityWeights x) : cliqueStepObjective m t b x ≤ cliqueStep m t b := by
  simpa only [cliqueStep, twoCoefficients_objective] using
    substitutionObjective_le_value (RGraph.clique (Fin (m + 2)) 3) (twoCoefficients m t b) x hx

theorem cliqueStep_le_iff (m : ℕ) (t b c : ℝ) : cliqueStep m t b ≤ c ↔
    ∀ x, ProbabilityWeights x → cliqueStepObjective m t b x ≤ c := by
  simpa only [cliqueStep, twoCoefficients_objective] using
    substitutionValue_le_iff (RGraph.clique (Fin (m + 2)) 3) (twoCoefficients m t b) c

theorem le_cliqueStep (m : ℕ) (t b : ℝ) : t ≤ cliqueStep m t b := by
  let x : Fin (m + 2) → ℝ := fun i => if i = 0 then 1 else 0
  have hx : ProbabilityWeights x := by
    constructor
    · intro i; dsimp only [x]; split <;> norm_num
    · simp [x]
  have hp : 6 * (RGraph.clique (Fin (m + 2)) 3).edgePolynomial x = 0 := by
    rw [clique_polynomial_cubic]
    norm_num [x]
  have h01 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hh := cliqueStepObjective_le m t b x hx
  simpa [cliqueStepObjective, hp, x, h01] using hh

theorem cliqueStep_mono (m : ℕ) {t t' b b' : ℝ} (ht : t ≤ t') (hb : b ≤ b') :
    cliqueStep m t b ≤ cliqueStep m t' b' := by
  apply substitutionValue_mono
  intro i
  unfold twoCoefficients
  split <;> first | exact ht | (split <;> first | exact hb | exact le_rfl)

theorem cliqueStep_abs_sub_le (m : ℕ) (t t' b b' : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : |t - t'| ≤ ε) (hb : |b - b'| ≤ ε) :
    |cliqueStep m t b - cliqueStep m t' b'| ≤ ε := by
  apply substitutionValue_abs_sub_le _ (by omega) _ _ hε
  intro i
  unfold twoCoefficients
  split <;> first | exact ht | (split <;> first | exact hb | simpa using hε)

theorem cliqueStep_maximizer_first_pos (m : ℕ) {t b : ℝ} (ht : 0 < t) (hbt : b < t)
    (x : Fin (m + 2) → ℝ) (hx : ProbabilityWeights x)
    (hmax : cliqueStepObjective m t b x = cliqueStep m t b) : 0 < x 0 := by
  by_contra hn
  have hx0 : x 0 = 0 := le_antisymm (le_of_not_gt hn) (hx.1 0)
  have hex : ∃ j : Fin (m + 2), 0 < x j := by
    by_contra h
    push Not at h
    have hs : (∑ i, x i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    rw [hx.2] at hs
    norm_num at hs
  obtain ⟨j, hj⟩ := hex
  let e := Equiv.swap (0 : Fin (m + 2)) j
  have hy := probabilityWeights_equiv e x hx
  have hbound := cliqueStepObjective_le m t b (x ∘ e) hy
  rw [← hmax] at hbound
  have hpoly := clique_polynomial_equiv x e
  have hcube : 0 < x j ^ 3 := pow_pos hj _
  by_cases hj1 : j = 1
  · subst j
    have he0 : e 0 = 1 := Equiv.swap_apply_left _ _
    have he1 : e 1 = 0 := Equiv.swap_apply_right _ _
    simp only [cliqueStepObjective, Function.comp_apply, hpoly, he0, he1, hx0,
      zero_pow (by omega : 3 ≠ 0), mul_zero, add_zero] at hbound
    nlinarith only [hbound, mul_pos (sub_pos.mpr hbt) hcube]
  · have h10 : (1 : Fin (m + 2)) ≠ 0 := by
      intro h; have hv := congrArg Fin.val h; norm_num at hv
    have he0 : e 0 = j := Equiv.swap_apply_left _ _
    have he1 : e 1 = 1 := Equiv.swap_apply_of_ne_of_ne h10 (Ne.symm hj1)
    simp only [cliqueStepObjective, Function.comp_apply, hpoly, he0, he1, hx0,
      zero_pow (by omega : 3 ≠ 0), mul_zero, add_zero] at hbound
    nlinarith only [hbound, mul_pos ht hcube]

theorem cliqueStep_strictMono_tail (m : ℕ) {t t' b : ℝ}
    (ht : 0 < t) (hbt : b < t) (htt' : t < t') :
    cliqueStep m t b < cliqueStep m t' b := by
  obtain ⟨x, hx, hm⟩ := exists_cliqueStep_maximizer m t b
  have hp := cliqueStep_maximizer_first_pos m ht hbt x hx hm
  have hbound := cliqueStepObjective_le m t' b x hx
  have hgain : 0 < (t' - t) * x 0 ^ 3 := mul_pos (sub_pos.mpr htt') (pow_pos hp _)
  unfold cliqueStepObjective at hm hbound
  nlinarith only [hm, hbound, hgain]

end IntervalsTuran.Spectrum
