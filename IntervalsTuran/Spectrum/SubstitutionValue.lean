module

public import IntervalsTuran.Spectrum.GraphSubstitution
public import IntervalsTuran.Uniformity.MassOptimization

@[expose] public section

/-! # The exact finite substitution optimization

The child graph contributes its actual normalized Lagrangian times the r-th
power of its part mass. All part proportions and all child weights remain
real variables. This identity is the graph-theoretic basis of the spectral
recursive construction.
-/

namespace IntervalsTuran.Spectrum

open Finset

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
variable {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {r : ℕ}

def substitutionObjective (H : RGraph I r) (b x : I → ℝ) : ℝ :=
  (r.factorial : ℝ) * H.edgePolynomial x + ∑ i, b i * (x i) ^ r

noncomputable def substitutionValue (H : RGraph I r) (b : I → ℝ) : ℝ :=
  sSup ((substitutionObjective H b) '' {x | ProbabilityWeights x})

theorem substitutionObjective_continuous (H : RGraph I r) (b : I → ℝ) :
    Continuous (substitutionObjective H b) := by
  unfold substitutionObjective RGraph.edgePolynomial
  fun_prop

theorem substitutionValues_nonempty (H : RGraph I r) (b : I → ℝ) :
    ((substitutionObjective H b) '' {x | ProbabilityWeights x}).Nonempty :=
  probabilityWeights_nonempty.image _

theorem substitutionValues_bddAbove (H : RGraph I r) (b : I → ℝ) :
    BddAbove ((substitutionObjective H b) '' {x | ProbabilityWeights x}) :=
  (probabilityWeights_isCompact.image (substitutionObjective_continuous H b)).bddAbove

theorem substitutionObjective_le_value (H : RGraph I r) (b x : I → ℝ)
    (hx : ProbabilityWeights x) : substitutionObjective H b x ≤ substitutionValue H b :=
  le_csSup (substitutionValues_bddAbove H b) ⟨x, hx, rfl⟩

theorem substitutionValue_le_iff (H : RGraph I r) (b : I → ℝ) (a : ℝ) :
    substitutionValue H b ≤ a ↔ ∀ x, ProbabilityWeights x → substitutionObjective H b x ≤ a := by
  constructor
  · exact fun h x hx => (substitutionObjective_le_value H b x hx).trans h
  · intro h
    apply csSup_le (substitutionValues_nonempty H b)
    rintro z ⟨x, hx, rfl⟩
    exact h x hx

theorem exists_substitution_maximizer (H : RGraph I r) (b : I → ℝ) :
    ∃ x, ProbabilityWeights x ∧ substitutionObjective H b x = substitutionValue H b := by
  obtain ⟨x, hx, hmax⟩ := probabilityWeights_isCompact.exists_isMaxOn
    probabilityWeights_nonempty (substitutionObjective_continuous H b).continuousOn
  refine ⟨x, hx, le_antisymm (substitutionObjective_le_value H b x hx) ?_⟩
  exact (substitutionValue_le_iff H b _).mpr (fun y hy => hmax hy)

theorem normalizedPolynomial_le_mass {W : Type*} [Fintype W] [DecidableEq W]
    (G : RGraph W r) (hr : 0 < r) (x : W → ℝ) (hx : ∀ v, 0 ≤ x v) :
    (r.factorial : ℝ) * G.edgePolynomial x ≤ G.lagrangian * (∑ v, x v) ^ r := by
  let t := ∑ v, x v
  have ht : 0 ≤ t := Finset.sum_nonneg (fun v _ => hx v)
  by_cases hz : t = 0
  · have hzero : x = fun _ => 0 := by
      funext v
      have hv : x v ≤ t := Finset.single_le_sum (fun w _ => hx w) (Finset.mem_univ v)
      exact le_antisymm (by simpa [hz] using hv) (hx v)
    change _ ≤ G.lagrangian * t ^ r
    rw [hzero, G.edgePolynomial_uniform, hz]
    simp [Nat.ne_of_gt hr]
  · let w := fun v => t⁻¹ * x v
    have hw : ProbabilityWeights w := by
      refine ⟨fun v => mul_nonneg (inv_nonneg.mpr ht) (hx v), ?_⟩
      dsimp only [w]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hz
    have heq : x = fun v => t * w v := by
      funext v
      dsimp only [w]
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    have hh := mul_le_mul_of_nonneg_left (G.normalizedPolynomial_le_lagrangian w hw)
      (pow_nonneg ht r)
    change (r.factorial : ℝ) * G.edgePolynomial x ≤ G.lagrangian * t ^ r
    rw [heq, G.edgePolynomial_scale]
    nlinarith only [hh]

theorem lagrangian_substitute_le (H : RGraph I r) (G : ∀ i, RGraph (V i) r)
    (hr : 2 ≤ r) :
    (substitute H G).lagrangian ≤ substitutionValue H (fun i => (G i).lagrangian) := by
  have hb0 : 0 ≤ substitutionValue H (fun i => (G i).lagrangian) := by
    obtain ⟨x, hx⟩ := (probabilityWeights_nonempty (V := I))
    apply le_trans _ (substitutionObjective_le_value H (fun i => (G i).lagrangian) x hx)
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (H.edgePolynomial_nonneg hx.1))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (G i).lagrangian_nonneg (pow_nonneg (hx.1 i) r)))
  apply ((substitute H G).lagrangian_le_iff hb0).mpr
  intro x hx
  rw [substitute_polynomial H G hr, mul_add, Finset.mul_sum]
  apply le_trans _ (substitutionObjective_le_value H (fun i => (G i).lagrangian)
    (partMass x) (partMass_probability hx))
  unfold substitutionObjective
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  exact normalizedPolynomial_le_mass (G i) (by omega) (fun v => x ⟨i, v⟩) (fun v => hx.1 _)

theorem lagrangian_substitute [∀ i, Nonempty (V i)]
    (H : RGraph I r) (G : ∀ i, RGraph (V i) r) (hr : 2 ≤ r) :
    (substitute H G).lagrangian = substitutionValue H (fun i => (G i).lagrangian) := by
  classical
  apply le_antisymm (lagrangian_substitute_le H G hr)
  obtain ⟨x, hx, hmax⟩ := exists_substitution_maximizer H (fun i => (G i).lagrangian)
  choose y hy hymax using fun i => (G i).exists_lagrangian_maximizer
  let z : Sigma V → ℝ := fun v => x v.1 * y v.1 v.2
  have hmass : partMass z = x := by
    funext i
    simp only [partMass, z, ← Finset.mul_sum, (hy i).2, mul_one]
  have hz : ProbabilityWeights z := by
    refine ⟨fun v => mul_nonneg (hx.1 v.1) ((hy v.1).1 v.2), ?_⟩
    rw [Fintype.sum_sigma]
    change (∑ i, partMass z i) = 1
    rw [hmass]
    exact hx.2
  have hpoly : (r.factorial : ℝ) * (substitute H G).edgePolynomial z =
      substitutionObjective H (fun i => (G i).lagrangian) x := by
    rw [substitute_polynomial H G hr, hmass, mul_add, Finset.mul_sum]
    apply congrArg ((r.factorial : ℝ) * H.edgePolynomial x + ·)
    apply Finset.sum_congr rfl
    intro i _
    change (r.factorial : ℝ) * (G i).edgePolynomial (fun v => x i * y i v) = _
    rw [(G i).edgePolynomial_scale]
    rw [show (r.factorial : ℝ) * (x i ^ r * (G i).edgePolynomial (y i)) =
      x i ^ r * ((r.factorial : ℝ) * (G i).edgePolynomial (y i)) by ring, hymax i]
    ring
  rw [← hmax, ← hpoly]
  exact (substitute H G).normalizedPolynomial_le_lagrangian z hz

theorem substitutionValue_mono (H : RGraph I r) {b c : I → ℝ} (h : ∀ i, b i ≤ c i) :
    substitutionValue H b ≤ substitutionValue H c := by
  apply (substitutionValue_le_iff H b _).mpr
  intro x hx
  apply le_trans _ (substitutionObjective_le_value H c x hx)
  unfold substitutionObjective
  exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (h i) (pow_nonneg (hx.1 i) r)))

theorem sum_powers_le_one (hr : 0 < r) {x : I → ℝ} (hx : ProbabilityWeights x) :
    ∑ i, x i ^ r ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  calc
    _ ≤ ∑ i, x i := by
      apply Finset.sum_le_sum
      intro i _
      rw [pow_succ]
      exact mul_le_of_le_one_left (hx.1 i) (pow_le_one₀ (hx.1 i) (hx.apply_le_one i))
    _ = 1 := hx.2

theorem substitutionValue_le_add (H : RGraph I r) (hr : 0 < r)
    (b c : I → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, b i ≤ c i + ε) :
    substitutionValue H b ≤ substitutionValue H c + ε := by
  apply (substitutionValue_le_iff H b _).mpr
  intro x hx
  have hh : substitutionObjective H b x ≤ substitutionObjective H c x + ε := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      mul_le_mul_of_nonneg_right (h i) (pow_nonneg (hx.1 i) r))
    have he := mul_le_mul_of_nonneg_left (sum_powers_le_one hr hx) hε
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_one] at hs he
    unfold substitutionObjective
    linarith
  have hb := substitutionObjective_le_value H c x hx
  linarith

theorem substitutionValue_abs_sub_le (H : RGraph I r) (hr : 0 < r)
    (b c : I → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, |b i - c i| ≤ ε) :
    |substitutionValue H b - substitutionValue H c| ≤ ε := by
  apply abs_le.mpr
  have hbc := substitutionValue_le_add H hr b c hε (fun i => by have := (abs_le.mp (h i)).2; linarith)
  have hcb := substitutionValue_le_add H hr c b hε (fun i => by have := (abs_le.mp (h i)).1; linarith)
  constructor <;> linarith

end IntervalsTuran.Spectrum
