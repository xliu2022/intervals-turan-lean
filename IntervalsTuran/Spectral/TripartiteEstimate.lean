/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.Family

/-!
# The analytic estimate for the tripartite Cayley gadget

The weighted edge sum is the actual finite sum over the relation
`z = x * s * y`, with `s` ranging over the specified generators.
All spectral conclusions in this module explicitly assume the finite
zero-sum operator bound. They do not assert existence of a family of
graphs with that bound.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.FiniteCayley

noncomputable section

def mass (G : FiniteCayley) (f : G.Vertex → ℝ) : ℝ := ∑ u, f u

def variance (G : FiniteCayley) (f : G.Vertex → ℝ) : ℝ :=
  ∑ u, (G.centered f u) ^ 2

def tripleSum (G : FiniteCayley) (a b c : G.Vertex → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ s ∈ G.generators, a x * b y * c (x * s * y)

theorem mass_comp (G : FiniteCayley) (e : G.Vertex ≃ G.Vertex) (f : G.Vertex → ℝ) :
    G.mass (fun u => f (e u)) = G.mass f :=
  Equiv.sum_comp e f

theorem mean_comp (G : FiniteCayley) (e : G.Vertex ≃ G.Vertex) (f : G.Vertex → ℝ) :
    G.mean (fun u => f (e u)) = G.mean f := by
  unfold mean
  rw [Equiv.sum_comp e f]

theorem l2Norm_comp (G : FiniteCayley) (e : G.Vertex ≃ G.Vertex) (f : G.Vertex → ℝ) :
    G.l2Norm (fun u => f (e u)) = G.l2Norm f := by
  unfold l2Norm
  rw [Equiv.sum_comp e (fun u => (f u) ^ 2)]

theorem centered_comp (G : FiniteCayley) (e : G.Vertex ≃ G.Vertex)
    (f : G.Vertex → ℝ) (u : G.Vertex) :
    G.centered (fun v => f (e v)) u = G.centered f (e u) := by
  simp only [centered, G.mean_comp]

theorem centered_l2Norm_comp (G : FiniteCayley) (e : G.Vertex ≃ G.Vertex)
    (f : G.Vertex → ℝ) :
    G.l2Norm (G.centered (fun v => f (e v))) = G.l2Norm (G.centered f) := by
  have hc : G.centered (fun v => f (e v)) = fun u => G.centered f (e u) :=
    funext (G.centered_comp e f)
  rw [hc]
  exact G.l2Norm_comp e (G.centered f)

theorem variance_nonneg (G : FiniteCayley) (f : G.Vertex → ℝ) : 0 ≤ G.variance f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem centered_l2Norm_sq (G : FiniteCayley) (f : G.Vertex → ℝ) :
    (G.l2Norm (G.centered f)) ^ 2 = G.variance f := by
  exact Real.sq_sqrt (G.variance_nonneg f)

theorem mixing_mass (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (f g : G.Vertex → ℝ) :
    (∑ u, f u * G.adjacency g u) ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass f * G.mass g +
        θ * G.l2Norm (G.centered f) * G.l2Norm (G.centered g) := by
  have heq : (G.valency : ℝ) * (G.order : ℝ) * G.mean f * G.mean g =
      (G.valency : ℝ) / (G.order : ℝ) * G.mass f * G.mass g := by
    dsimp [mean, mass]
    field_simp [G.order_real_ne_zero]
  simpa only [heq] using G.mixing hbound f g

/-- Mixing for the link at a fixed vertex of the second class. -/
theorem link_second_bound (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (a c : G.Vertex → ℝ) (y : G.Vertex) :
    (∑ x, ∑ s ∈ G.generators, a x * c (x * s * y)) ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass c +
        θ * G.l2Norm (G.centered a) * G.l2Norm (G.centered c) := by
  have h := G.mixing_mass hbound a (fun v => c (v * y))
  have hm := G.mass_comp (Equiv.mulRight y) c
  have hl := G.centered_l2Norm_comp (Equiv.mulRight y) c
  change G.mass (fun v => c (v * y)) = G.mass c at hm
  change G.l2Norm (G.centered (fun v => c (v * y))) =
    G.l2Norm (G.centered c) at hl
  simpa only [adjacency, Finset.mul_sum, hm, hl] using h

theorem tripleSum_eq_second_links (G : FiniteCayley) (a b c : G.Vertex → ℝ) :
    G.tripleSum a b c =
      ∑ y, b y * (∑ x, ∑ s ∈ G.generators, a x * c (x * s * y)) := by
  unfold tripleSum
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The first of the three symmetric link estimates, equation (3.2). -/
theorem tripleSum_le_second_error (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (a b c : G.Vertex → ℝ)
    (hb : ∀ y, 0 ≤ b y) :
    G.tripleSum a b c ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass b * G.mass c +
        θ * G.mass b * G.l2Norm (G.centered a) * G.l2Norm (G.centered c) := by
  rw [G.tripleSum_eq_second_links]
  calc
    _ ≤ ∑ y, b y *
        ((G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass c +
          θ * G.l2Norm (G.centered a) * G.l2Norm (G.centered c)) := by
      exact Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (G.link_second_bound hbound a c y) (hb y))
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold mass
      ring

theorem generators_inv_sum (G : FiniteCayley) (f : G.Vertex → ℝ) :
    ∑ s ∈ G.generators, f (s⁻¹) = ∑ s ∈ G.generators, f s := by
  refine Finset.sum_bij (fun s _ => s⁻¹)
    (fun s hs => G.inverse_closed s hs) ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ hab
    exact inv_injective hab
  · intro b hb
    exact ⟨b⁻¹, G.inverse_closed b hb, inv_inv b⟩

theorem link_first_bound (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (b c : G.Vertex → ℝ) (x : G.Vertex) :
    (∑ y, ∑ s ∈ G.generators, b y * c (x * s * y)) ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass b * G.mass c +
        θ * G.l2Norm (G.centered b) * G.l2Norm (G.centered c) := by
  let e : G.Vertex ≃ G.Vertex := (Equiv.inv G.Vertex).trans (Equiv.mulLeft x)
  have h := G.mixing_mass hbound (fun u => b (u⁻¹)) (fun v => c (x * v⁻¹))
  have hmb := G.mass_comp (Equiv.inv G.Vertex) b
  have hlb := G.centered_l2Norm_comp (Equiv.inv G.Vertex) b
  have hmc := G.mass_comp e c
  have hlc := G.centered_l2Norm_comp e c
  change G.mass (fun u => b (u⁻¹)) = G.mass b at hmb
  change G.l2Norm (G.centered (fun u => b (u⁻¹))) = G.l2Norm (G.centered b) at hlb
  change G.mass (fun v => c (x * v⁻¹)) = G.mass c at hmc
  change G.l2Norm (G.centered (fun v => c (x * v⁻¹))) = G.l2Norm (G.centered c) at hlc
  rw [hmb, hlb, hmc, hlc] at h
  have hid : (∑ u, b (u⁻¹) * G.adjacency (fun v => c (x * v⁻¹)) u) =
      ∑ y, ∑ s ∈ G.generators, b y * c (x * s * y) := by
    calc
      _ = ∑ u, ∑ s ∈ G.generators, b (u⁻¹) * c (x * s⁻¹ * u⁻¹) := by
        simp only [adjacency, Finset.mul_sum, mul_inv_rev, mul_assoc]
      _ = ∑ u, ∑ s ∈ G.generators, b (u⁻¹) * c (x * s * u⁻¹) := by
        exact Finset.sum_congr rfl (fun u _ =>
          G.generators_inv_sum (fun s => b (u⁻¹) * c (x * s * u⁻¹)))
      _ = _ := Equiv.sum_comp (Equiv.inv G.Vertex)
        (fun y => ∑ s ∈ G.generators, b y * c (x * s * y))
  rwa [hid] at h

theorem tripleSum_eq_first_links (G : FiniteCayley) (a b c : G.Vertex → ℝ) :
    G.tripleSum a b c =
      ∑ x, a x * (∑ y, ∑ s ∈ G.generators, b y * c (x * s * y)) := by
  unfold tripleSum
  simp only [Finset.mul_sum, mul_assoc]

theorem tripleSum_le_first_error (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (a b c : G.Vertex → ℝ)
    (ha : ∀ x, 0 ≤ a x) :
    G.tripleSum a b c ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass b * G.mass c +
        θ * G.mass a * G.l2Norm (G.centered b) * G.l2Norm (G.centered c) := by
  rw [G.tripleSum_eq_first_links]
  calc
    _ ≤ ∑ x, a x *
        ((G.valency : ℝ) / (G.order : ℝ) * G.mass b * G.mass c +
          θ * G.l2Norm (G.centered b) * G.l2Norm (G.centered c)) := by
      exact Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (G.link_first_bound hbound b c x) (ha x))
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold mass
      ring

theorem link_third_bound (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (a b : G.Vertex → ℝ) (z : G.Vertex) :
    (∑ y, ∑ s ∈ G.generators, b y * a (z * y⁻¹ * s⁻¹)) ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass b +
        θ * G.l2Norm (G.centered a) * G.l2Norm (G.centered b) := by
  have h := G.mixing_mass hbound (fun u => b (u⁻¹)) (fun v => a (z * v))
  have hmb := G.mass_comp (Equiv.inv G.Vertex) b
  have hlb := G.centered_l2Norm_comp (Equiv.inv G.Vertex) b
  have hma := G.mass_comp (Equiv.mulLeft z) a
  have hla := G.centered_l2Norm_comp (Equiv.mulLeft z) a
  change G.mass (fun u => b (u⁻¹)) = G.mass b at hmb
  change G.l2Norm (G.centered (fun u => b (u⁻¹))) = G.l2Norm (G.centered b) at hlb
  change G.mass (fun v => a (z * v)) = G.mass a at hma
  change G.l2Norm (G.centered (fun v => a (z * v))) = G.l2Norm (G.centered a) at hla
  rw [hmb, hlb, hma, hla] at h
  have hid : (∑ u, b (u⁻¹) * G.adjacency (fun v => a (z * v)) u) =
      ∑ y, ∑ s ∈ G.generators, b y * a (z * y⁻¹ * s⁻¹) := by
    calc
      _ = ∑ u, ∑ s ∈ G.generators, b (u⁻¹) * a (z * u * s) := by
        simp only [adjacency, Finset.mul_sum, mul_assoc]
      _ = ∑ y, ∑ s ∈ G.generators, b y * a (z * y⁻¹ * s) := by
        have hi := Equiv.sum_comp (Equiv.inv G.Vertex)
          (fun y => ∑ s ∈ G.generators, b y * a (z * y⁻¹ * s))
        change (∑ u, ∑ s ∈ G.generators, b (u⁻¹) * a (z * (u⁻¹)⁻¹ * s)) = _ at hi
        simpa only [inv_inv] using hi
      _ = _ := by
        exact Finset.sum_congr rfl (fun y _ =>
          (G.generators_inv_sum (fun s => b y * a (z * y⁻¹ * s))).symm)
  rw [hid] at h
  convert h using 1
  ring

theorem tripleSum_eq_third_links (G : FiniteCayley) (a b c : G.Vertex → ℝ) :
    G.tripleSum a b c =
      ∑ z, c z * (∑ y, ∑ s ∈ G.generators, b y * a (z * y⁻¹ * s⁻¹)) := by
  have hchange (y s : G.Vertex) :
      (∑ x, a x * b y * c (x * s * y)) =
        ∑ z, c z * b y * a (z * y⁻¹ * s⁻¹) := by
    have hi := Equiv.sum_comp (Equiv.mulRight (s * y))
      (fun z => a (z * y⁻¹ * s⁻¹) * b y * c z)
    change (∑ x, a ((x * (s * y)) * y⁻¹ * s⁻¹) * b y * c (x * (s * y))) = _ at hi
    simp only [mul_assoc, mul_inv_cancel, mul_one] at hi
    calc
      _ = ∑ z, a (z * y⁻¹ * s⁻¹) * b y * c z := by
        simpa only [mul_assoc] using hi
      _ = _ := Finset.sum_congr rfl (fun _ _ => by ring)
  calc
    _ = ∑ y, ∑ s ∈ G.generators, ∑ x, a x * b y * c (x * s * y) := by
      unfold tripleSum
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
    _ = ∑ y, ∑ s ∈ G.generators, ∑ z, c z * b y * a (z * y⁻¹ * s⁻¹) := by
      exact Finset.sum_congr rfl (fun y _ =>
        Finset.sum_congr rfl (fun s _ => hchange y s))
    _ = _ := by
      symm
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro z _
      ring

theorem tripleSum_le_third_error (G : FiniteCayley) {θ : ℝ}
    (hbound : G.HasZeroSumBound θ) (a b c : G.Vertex → ℝ)
    (hc : ∀ z, 0 ≤ c z) :
    G.tripleSum a b c ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass b * G.mass c +
        θ * G.mass c * G.l2Norm (G.centered a) * G.l2Norm (G.centered b) := by
  rw [G.tripleSum_eq_third_links]
  calc
    _ ≤ ∑ z, c z *
        ((G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass b +
          θ * G.l2Norm (G.centered a) * G.l2Norm (G.centered b)) := by
      exact Finset.sum_le_sum (fun z _ =>
        mul_le_mul_of_nonneg_left (G.link_third_bound hbound a b z) (hc z))
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold mass
      ring

theorem mass_nonneg (G : FiniteCayley) (f : G.Vertex → ℝ)
    (hf : ∀ u, 0 ≤ f u) : 0 ≤ G.mass f :=
  Finset.sum_nonneg (fun u _ => hf u)

theorem variance_eq (G : FiniteCayley) (f : G.Vertex → ℝ) :
    G.variance f = (∑ u, (f u) ^ 2) - (G.mass f) ^ 2 / (G.order : ℝ) := by
  have hpoint (u : G.Vertex) :
      (G.centered f u) ^ 2 = (f u) ^ 2 - 2 * G.mean f * f u + (G.mean f) ^ 2 := by
    unfold centered
    ring
  unfold variance
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp [mean, mass, order]
  have hn : (Fintype.card G.Vertex : ℝ) ≠ 0 := G.order_real_ne_zero
  field_simp [hn]
  ring

/-- An elementary polynomial form of AM--GM for three nonnegative masses. -/
theorem six_mul_three_masses_le {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hsum : A + B + C = 1) :
    6 * A * B * C ≤ 2 / 9 := by
  have hA1 : A ≤ 1 := by linarith
  have hBCeq : B + C = 1 - A := by linarith
  have hBC : 4 * B * C ≤ (1 - A) ^ 2 := by
    rw [← hBCeq]
    nlinarith only [sq_nonneg (B - C)]
  have hmul := mul_le_mul_of_nonneg_left hBC hA
  have hpoly := mul_nonneg (show (0 : ℝ) ≤ 4 / 3 - A by linarith)
    (sq_nonneg (A - 1 / 3))
  linarith only [hmul, hpoly]

theorem weighted_pair_errors_le {A B C x y z : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hsum : A + B + C = 1) :
    2 * (B * x * z + A * y * z + C * x * y) ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  calc
    _ ≤ (A + B + C) * (x ^ 2 + y ^ 2 + z ^ 2) := by
      linarith only [mul_nonneg hA (sq_nonneg (y - z)),
        mul_nonneg hB (sq_nonneg (x - z)), mul_nonneg hC (sq_nonneg (x - y)),
        mul_nonneg hA (sq_nonneg x), mul_nonneg hB (sq_nonneg y),
        mul_nonneg hC (sq_nonneg z)]
    _ = _ := by rw [hsum, one_mul]

/-- The averaged link estimate, before bounding the class masses. -/
theorem tripleSum_le_variance_error (G : FiniteCayley) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : G.HasZeroSumBound θ) (a b c : G.Vertex → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) (hc : ∀ u, 0 ≤ c u)
    (hmass : G.mass a + G.mass b + G.mass c = 1) :
    G.tripleSum a b c ≤
      (G.valency : ℝ) / (G.order : ℝ) * G.mass a * G.mass b * G.mass c +
        θ / 6 * (G.variance a + G.variance b + G.variance c) := by
  have hfirst := G.tripleSum_le_first_error hbound a b c ha
  have hsecond := G.tripleSum_le_second_error hbound a b c hb
  have hthird := G.tripleSum_le_third_error hbound a b c hc
  have hpair := weighted_pair_errors_le
    (x := G.l2Norm (G.centered a)) (y := G.l2Norm (G.centered b))
    (z := G.l2Norm (G.centered c))
    (G.mass_nonneg a ha) (G.mass_nonneg b hb) (G.mass_nonneg c hc) hmass
  have hweighted := mul_le_mul_of_nonneg_left hpair hθ
  rw [G.centered_l2Norm_sq, G.centered_l2Norm_sq, G.centered_l2Norm_sq] at hweighted
  linarith only [hfirst, hsecond, hthird, hweighted]

theorem variance_sum_le (G : FiniteCayley) (a b c : G.Vertex → ℝ)
    (hmass : G.mass a + G.mass b + G.mass c = 1) :
    G.variance a + G.variance b + G.variance c ≤
      ((∑ u, (a u) ^ 2) + (∑ u, (b u) ^ 2) + (∑ u, (c u) ^ 2)) -
        1 / (3 * (G.order : ℝ)) := by
  have hmasssq := congrArg (fun t : ℝ => t ^ 2) hmass
  have hsq : (1 : ℝ) / 3 ≤ (G.mass a) ^ 2 + (G.mass b) ^ 2 + (G.mass c) ^ 2 := by
    linarith only [hmasssq, sq_nonneg (G.mass a - G.mass b),
      sq_nonneg (G.mass a - G.mass c), sq_nonneg (G.mass b - G.mass c)]
  have hn : 0 ≤ (G.order : ℝ) := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hsq hn
  have hdiv' : 1 / (3 * (G.order : ℝ)) ≤
      (G.mass a) ^ 2 / (G.order : ℝ) + (G.mass b) ^ 2 / (G.order : ℝ) +
        (G.mass c) ^ 2 / (G.order : ℝ) := by
    convert hdiv using 1 <;> ring
  rw [G.variance_eq, G.variance_eq, G.variance_eq]
  linarith only [hdiv']

/-- The normalized polynomial estimate of Lemma 3.3 for the actual
tripartite Cayley relation, with `n = G.order` and `m = 3 * n`. -/
theorem normalized_tripleSum_le (G : FiniteCayley) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : G.HasZeroSumBound θ) (a b c : G.Vertex → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) (hc : ∀ u, 0 ≤ c u)
    (hmass : G.mass a + G.mass b + G.mass c = 1) :
    6 * G.tripleSum a b c ≤
      2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) +
        θ * (((∑ u, (a u) ^ 2) + (∑ u, (b u) ^ 2) + (∑ u, (c u) ^ 2)) -
          1 / (3 * (G.order : ℝ))) := by
  have ht := G.tripleSum_le_variance_error hθ hbound a b c ha hb hc hmass
  have hprod := six_mul_three_masses_le
    (G.mass_nonneg a ha) (G.mass_nonneg b hb) (G.mass_nonneg c hc) hmass
  have hcoef : 0 ≤ (G.valency : ℝ) / (G.order : ℝ) := by positivity
  have hleading := mul_le_mul_of_nonneg_left hprod hcoef
  have hvar := mul_le_mul_of_nonneg_left (G.variance_sum_le a b c hmass) hθ
  calc
    _ ≤ ((G.valency : ℝ) / (G.order : ℝ)) * (6 * G.mass a * G.mass b * G.mass c) +
        θ * (G.variance a + G.variance b + G.variance c) := by
      linarith only [ht]
    _ ≤ ((G.valency : ℝ) / (G.order : ℝ)) * (2 / 9) +
        θ * (((∑ u, (a u) ^ 2) + (∑ u, (b u) ^ 2) + (∑ u, (c u) ^ 2)) -
          1 / (3 * (G.order : ℝ))) := add_le_add hleading hvar
    _ = _ := by ring

theorem generator_sum_le_mass (G : FiniteCayley) (c : G.Vertex → ℝ)
    (hc : ∀ z, 0 ≤ c z) (x y : G.Vertex) :
    (∑ s ∈ G.generators, c (x * s * y)) ≤ G.mass c := by
  calc
    _ ≤ ∑ s, c (x * s * y) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => hc (x * s * y))
    _ = _ := Equiv.sum_comp ((Equiv.mulLeft x).trans (Equiv.mulRight y)) c

/-- A tripartite relation is contained in the complete tripartite graph. -/
theorem tripleSum_le_mass_product (G : FiniteCayley) (a b c : G.Vertex → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) (hc : ∀ u, 0 ≤ c u) :
    G.tripleSum a b c ≤ G.mass a * G.mass b * G.mass c := by
  calc
    _ = ∑ x, ∑ y, (a x * b y) * (∑ s ∈ G.generators, c (x * s * y)) := by
      simp only [tripleSum, Finset.mul_sum]
    _ ≤ ∑ x, ∑ y, (a x * b y) * G.mass c := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (G.generator_sum_le_mass c hc x y)
        (mul_nonneg (ha x) (hb y))
    _ = _ := by
      have hi (x : G.Vertex) : (∑ y, (a x * b y) * G.mass c) =
          a x * G.mass b * G.mass c := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        rfl
      simp_rw [hi]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rfl

/-- The bound `2 / 9` uses tripartiteness alone, without a spectral input. -/
theorem normalized_tripleSum_le_two_ninths (G : FiniteCayley) (a b c : G.Vertex → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u) (hc : ∀ u, 0 ≤ c u)
    (hmass : G.mass a + G.mass b + G.mass c = 1) :
    6 * G.tripleSum a b c ≤ 2 / 9 := by
  have ht := G.tripleSum_le_mass_product a b c ha hb hc
  have hp := six_mul_three_masses_le
    (G.mass_nonneg a ha) (G.mass_nonneg b hb) (G.mass_nonneg c hc) hmass
  linarith only [ht, hp]

/-- The uniform vector on the three disjoint group copies attains this
exact value. This supplies the lower evaluation in the outer construction. -/
theorem normalized_tripleSum_uniform (G : FiniteCayley) :
    6 * G.tripleSum (fun _ => 1 / (3 * (G.order : ℝ)))
        (fun _ => 1 / (3 * (G.order : ℝ)))
        (fun _ => 1 / (3 * (G.order : ℝ))) =
      2 * (G.valency : ℝ) / (9 * (G.order : ℝ)) := by
  simp only [tripleSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp [order, valency]
  have hn : (Fintype.card G.Vertex : ℝ) ≠ 0 := G.order_real_ne_zero
  field_simp [hn]
  ring

end

end IntervalsTuran.Spectral.FiniteCayley
