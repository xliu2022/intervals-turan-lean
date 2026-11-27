/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.BipartiteKernel
public import IntervalsTuran.Spectral.TripartiteEstimate
public import IntervalsTuran.Hypergraph.Lagrangian

/-!
# A tripartite hypergraph from a simple bipartite kernel

The three classes are copies of an additive group.  A triple `(x,y,z)`
is an edge precisely when `z ∈ B.neighbors (x + y)`.  The links at the
first two classes are translates of `B`.  Averaging their two spectral
estimates gives the coefficient `3 * θ / 2` in the normalized polynomial
bound; no spectral hypothesis on the third class is needed.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.Spectral.BipartiteKernel

noncomputable section

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def tripleSum (B : BipartiteKernel V) (a b c : V → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z ∈ B.neighbors (x + y), a x * b y * c z

theorem link_second_bound (B : BipartiteKernel V) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) (a c : V → ℝ) (y : V) :
    (∑ x, a x * B.adjacency c (x + y)) ≤
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass a * mass c +
        θ * l2Norm (centered a) * l2Norm (centered c) := by
  have h := B.mixing_mass hbound (fun u => a (u - y)) c
  have hm := mass_comp (Equiv.subRight y) a
  have hl := centered_l2Norm_comp (Equiv.subRight y) a
  change mass (fun u => a (u - y)) = mass a at hm
  change l2Norm (centered (fun u => a (u - y))) = l2Norm (centered a) at hl
  rw [hm, hl] at h
  have heq : (∑ x, a x * B.adjacency c (x + y)) =
      ∑ u, a (u - y) * B.adjacency c u := by
    have hi := Equiv.sum_comp (Equiv.addRight y)
      (fun u => a (u - y) * B.adjacency c u)
    simpa using hi
  rwa [heq]

theorem link_first_bound (B : BipartiteKernel V) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) (b c : V → ℝ) (x : V) :
    (∑ y, b y * B.adjacency c (x + y)) ≤
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass b * mass c +
        θ * l2Norm (centered b) * l2Norm (centered c) := by
  simpa only [add_comm x] using B.link_second_bound hbound b c x

theorem tripleSum_eq_second_links (B : BipartiteKernel V) (a b c : V → ℝ) :
    B.tripleSum a b c = ∑ y, b y * (∑ x, a x * B.adjacency c (x + y)) := by
  unfold tripleSum adjacency
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem tripleSum_eq_first_links (B : BipartiteKernel V) (a b c : V → ℝ) :
    B.tripleSum a b c = ∑ x, a x * (∑ y, b y * B.adjacency c (x + y)) := by
  simp only [tripleSum, adjacency, Finset.mul_sum, mul_assoc]

theorem tripleSum_le_second_error (B : BipartiteKernel V) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) (a b c : V → ℝ) (hb : ∀ y, 0 ≤ b y) :
    B.tripleSum a b c ≤
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass a * mass b * mass c +
        θ * mass b * l2Norm (centered a) * l2Norm (centered c) := by
  rw [B.tripleSum_eq_second_links]
  calc
    _ ≤ ∑ y, b y * ((B.valency : ℝ) / (Fintype.card V : ℝ) * mass a * mass c +
        θ * l2Norm (centered a) * l2Norm (centered c)) :=
      Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (B.link_second_bound hbound a c y) (hb y))
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold mass
      ring

theorem tripleSum_le_first_error (B : BipartiteKernel V) {θ : ℝ}
    (hbound : B.HasZeroSumBound θ) (a b c : V → ℝ) (ha : ∀ x, 0 ≤ a x) :
    B.tripleSum a b c ≤
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass a * mass b * mass c +
        θ * mass a * l2Norm (centered b) * l2Norm (centered c) := by
  rw [B.tripleSum_eq_first_links]
  calc
    _ ≤ ∑ x, a x * ((B.valency : ℝ) / (Fintype.card V : ℝ) * mass b * mass c +
        θ * l2Norm (centered b) * l2Norm (centered c)) :=
      Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (B.link_first_bound hbound b c x) (ha x))
    _ = _ := by
      rw [← Finset.sum_mul]
      unfold mass
      ring

theorem weighted_two_pair_errors_le {A B C x y z : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hsum : A + B + C = 1) :
    2 * (B * x * z + A * y * z) ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  calc
    _ ≤ (A + B + C) * (x ^ 2 + y ^ 2 + z ^ 2) := by
      linarith only [mul_nonneg hB (sq_nonneg (x - z)),
        mul_nonneg hA (sq_nonneg (y - z)), mul_nonneg hA (sq_nonneg x),
        mul_nonneg hC (sq_nonneg x), mul_nonneg hB (sq_nonneg y),
        mul_nonneg hC (sq_nonneg y), mul_nonneg hC (sq_nonneg z)]
    _ = _ := by rw [hsum, one_mul]

theorem tripleSum_le_variance_error (B : BipartiteKernel V) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : B.HasZeroSumBound θ) (a b c : V → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hc : ∀ z, 0 ≤ c z)
    (hmass : mass a + mass b + mass c = 1) :
    B.tripleSum a b c ≤
      (B.valency : ℝ) / (Fintype.card V : ℝ) * mass a * mass b * mass c +
        θ / 4 * (variance a + variance b + variance c) := by
  have hfirst := B.tripleSum_le_first_error hbound a b c ha
  have hsecond := B.tripleSum_le_second_error hbound a b c hb
  have hpair := weighted_two_pair_errors_le
    (x := l2Norm (centered a)) (y := l2Norm (centered b)) (z := l2Norm (centered c))
    (mass_nonneg a ha) (mass_nonneg b hb) (mass_nonneg c hc) hmass
  have hweighted := mul_le_mul_of_nonneg_left hpair hθ
  rw [centered_l2Norm_sq, centered_l2Norm_sq, centered_l2Norm_sq] at hweighted
  linarith only [hfirst, hsecond, hweighted]

theorem variance_sum_le (a b c : V → ℝ) (hmass : mass a + mass b + mass c = 1) :
    variance a + variance b + variance c ≤
      ((∑ x, a x ^ 2) + (∑ y, b y ^ 2) + (∑ z, c z ^ 2)) -
        1 / (3 * (Fintype.card V : ℝ)) := by
  have hmasssq := congrArg (fun t : ℝ => t ^ 2) hmass
  have hsq : (1 : ℝ) / 3 ≤ mass a ^ 2 + mass b ^ 2 + mass c ^ 2 := by
    linarith only [hmasssq, sq_nonneg (mass a - mass b),
      sq_nonneg (mass a - mass c), sq_nonneg (mass b - mass c)]
  have hdiv := div_le_div_of_nonneg_right hsq (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  have hdiv' : 1 / (3 * (Fintype.card V : ℝ)) ≤
      mass a ^ 2 / (Fintype.card V : ℝ) + mass b ^ 2 / (Fintype.card V : ℝ) +
        mass c ^ 2 / (Fintype.card V : ℝ) := by
    convert hdiv using 1 <;> ring
  rw [variance_eq, variance_eq, variance_eq]
  linarith only [hdiv']

theorem normalized_tripleSum_le (B : BipartiteKernel V) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : B.HasZeroSumBound θ) (a b c : V → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hc : ∀ z, 0 ≤ c z)
    (hmass : mass a + mass b + mass c = 1) :
    6 * B.tripleSum a b c ≤
      2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) +
        (3 * θ / 2) * (((∑ x, a x ^ 2) + (∑ y, b y ^ 2) + (∑ z, c z ^ 2)) -
          1 / (3 * (Fintype.card V : ℝ))) := by
  have ht := B.tripleSum_le_variance_error hθ hbound a b c ha hb hc hmass
  have hprod := FiniteCayley.six_mul_three_masses_le
    (mass_nonneg a ha) (mass_nonneg b hb) (mass_nonneg c hc) hmass
  have hcoef : 0 ≤ (B.valency : ℝ) / (Fintype.card V : ℝ) := by positivity
  have hleading := mul_le_mul_of_nonneg_left hprod hcoef
  have hvar := mul_le_mul_of_nonneg_left (variance_sum_le a b c hmass)
    (show 0 ≤ 3 * θ / 2 by positivity)
  calc
    _ ≤ ((B.valency : ℝ) / (Fintype.card V : ℝ)) * (6 * mass a * mass b * mass c) +
        (3 * θ / 2) * (variance a + variance b + variance c) := by linarith only [ht]
    _ ≤ ((B.valency : ℝ) / (Fintype.card V : ℝ)) * (2 / 9) +
        (3 * θ / 2) * (((∑ x, a x ^ 2) + (∑ y, b y ^ 2) + (∑ z, c z ^ 2)) -
          1 / (3 * (Fintype.card V : ℝ))) := add_le_add hleading hvar
    _ = _ := by ring

theorem tripleSum_le_mass_product (B : BipartiteKernel V) (a b c : V → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hc : ∀ z, 0 ≤ c z) :
    B.tripleSum a b c ≤ mass a * mass b * mass c := by
  have hneighbor (x y : V) : (∑ z ∈ B.neighbors (x + y), c z) ≤ mass c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun z _ _ => hc z)
  calc
    _ = ∑ x, ∑ y, (a x * b y) * (∑ z ∈ B.neighbors (x + y), c z) := by
      simp only [tripleSum, Finset.mul_sum]
    _ ≤ ∑ x, ∑ y, (a x * b y) * mass c := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hneighbor x y) (mul_nonneg (ha x) (hb y)))
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, mass]

theorem normalized_tripleSum_le_two_ninths (B : BipartiteKernel V) (a b c : V → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) (hc : ∀ z, 0 ≤ c z)
    (hmass : mass a + mass b + mass c = 1) :
    6 * B.tripleSum a b c ≤ 2 / 9 := by
  have ht := B.tripleSum_le_mass_product a b c ha hb hc
  have hp := FiniteCayley.six_mul_three_masses_le
    (mass_nonneg a ha) (mass_nonneg b hb) (mass_nonneg c hc) hmass
  linarith only [ht, hp]

theorem normalized_tripleSum_uniform (B : BipartiteKernel V) :
    6 * B.tripleSum (fun _ => 1 / (3 * (Fintype.card V : ℝ)))
        (fun _ => 1 / (3 * (Fintype.card V : ℝ)))
        (fun _ => 1 / (3 * (Fintype.card V : ℝ))) =
      2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) := by
  simp only [tripleSum, Finset.sum_const, B.left_regular, Finset.card_univ, nsmul_eq_mul]
  field_simp [card_real_ne_zero (V := V)]
  ring

def gadgetEdge (x y z : V) : Finset (Fin 3 × V) := {(0, x), (1, y), (2, z)}

theorem gadgetEdge_card (x y z : V) : (gadgetEdge x y z).card = 3 := by
  simp [gadgetEdge]

theorem gadgetEdge_eq_iff (x y z x' y' z' : V) :
    gadgetEdge x y z = gadgetEdge x' y' z' ↔ x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    have hx : x = x' := by
      have hm : ((0 : Fin 3), x) ∈ gadgetEdge x' y' z' := by
        rw [← h]
        simp [gadgetEdge]
      simpa [gadgetEdge] using hm
    have hy : y = y' := by
      have hm : ((1 : Fin 3), y) ∈ gadgetEdge x' y' z' := by
        rw [← h]
        simp [gadgetEdge]
      simpa [gadgetEdge] using hm
    have hz : z = z' := by
      have hm : ((2 : Fin 3), z) ∈ gadgetEdge x' y' z' := by
        rw [← h]
        simp [gadgetEdge]
      simpa [gadgetEdge] using hm
    exact ⟨hx, hy, hz⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

abbrev EdgeIndex (B : BipartiteKernel V) := Σ x : V, Σ y : V, ↥(B.neighbors (x + y))

def indexedEdge (B : BipartiteKernel V) (t : B.EdgeIndex) : Finset (Fin 3 × V) :=
  gadgetEdge t.1 t.2.1 t.2.2

theorem indexedEdge_injective (B : BipartiteKernel V) : Function.Injective B.indexedEdge := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  obtain ⟨hx, hy, hz⟩ := (gadgetEdge_eq_iff x y z x' y' z').mp h
  subst x'
  subst y'
  have heq : z = z' := Subtype.ext hz
  subst z'
  rfl

def tripartiteGraph (B : BipartiteKernel V) : RGraph (Fin 3 × V) 3 where
  edges := Finset.univ.image B.indexedEdge
  uniform := by
    intro e he
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
    exact gadgetEdge_card t.1 t.2.1 t.2.2

theorem tripartiteGraph_vertex_card (_B : BipartiteKernel V) :
    Fintype.card (Fin 3 × V) = 3 * Fintype.card V := by
  simp

theorem tripartiteGraph_edge_card (B : BipartiteKernel V) :
    B.tripartiteGraph.edges.card = B.valency * Fintype.card V ^ 2 := by
  rw [tripartiteGraph, Finset.card_image_of_injective _ B.indexedEdge_injective]
  simp only [Finset.card_univ, EdgeIndex, Fintype.card_sigma, Fintype.card_coe,
    B.left_regular, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  ring

theorem prod_gadgetEdge (w : Fin 3 × V → ℝ) (x y z : V) :
    (∏ v ∈ gadgetEdge x y z, w v) = w (0, x) * w (1, y) * w (2, z) := by
  simp [gadgetEdge, mul_assoc]

theorem tripartiteGraph_edgePolynomial (B : BipartiteKernel V) (w : Fin 3 × V → ℝ) :
    B.tripartiteGraph.edgePolynomial w =
      B.tripleSum (fun x => w (0, x)) (fun y => w (1, y)) (fun z => w (2, z)) := by
  unfold RGraph.edgePolynomial tripartiteGraph
  rw [Finset.sum_image (fun a _ b _ hab => B.indexedEdge_injective hab)]
  simp only [indexedEdge, prod_gadgetEdge, EdgeIndex, Fintype.sum_sigma]
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.sum_coe_sort (B.neighbors (x + y))
    (fun z => w (0, x) * w (1, y) * w (2, z))

theorem mass_classes (w : Fin 3 × V → ℝ) :
    mass (fun x => w (0, x)) + mass (fun y => w (1, y)) + mass (fun z => w (2, z)) =
      ∑ v, w v := by
  simp only [mass, Fintype.sum_prod_type, Fin.sum_univ_three]

theorem sum_sq_classes (w : Fin 3 × V → ℝ) :
    (∑ x, w (0, x) ^ 2) + (∑ y, w (1, y) ^ 2) + (∑ z, w (2, z) ^ 2) =
      ∑ v, w v ^ 2 := mass_classes (fun v => w v ^ 2)

theorem tripartiteGraph_lagrangian_le (B : BipartiteKernel V) :
    B.tripartiteGraph.lagrangian ≤ 2 / 9 := by
  apply (B.tripartiteGraph.lagrangian_le_iff (by norm_num)).mpr
  intro w hw
  norm_num only [Nat.factorial] at *
  rw [B.tripartiteGraph_edgePolynomial]
  exact B.normalized_tripleSum_le_two_ninths _ _ _
    (fun x => hw.1 (0, x)) (fun y => hw.1 (1, y)) (fun z => hw.1 (2, z))
    ((mass_classes w).trans hw.2)

theorem tripartiteGraph_normalizedPolynomial_le (B : BipartiteKernel V) {θ : ℝ}
    (hθ : 0 ≤ θ) (hbound : B.HasZeroSumBound θ)
    (w : Fin 3 × V → ℝ) (hw : ProbabilityWeights w) :
    6 * B.tripartiteGraph.edgePolynomial w ≤
      2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) +
        (3 * θ / 2) * ((∑ v, w v ^ 2) - 1 / (3 * (Fintype.card V : ℝ))) := by
  rw [B.tripartiteGraph_edgePolynomial]
  have h := B.normalized_tripleSum_le hθ hbound
    (fun x => w (0, x)) (fun y => w (1, y)) (fun z => w (2, z))
    (fun x => hw.1 (0, x)) (fun y => hw.1 (1, y)) (fun z => hw.1 (2, z))
    ((mass_classes w).trans hw.2)
  rwa [sum_sq_classes] at h

theorem tripartiteGraph_uniform_evaluation (B : BipartiteKernel V) :
    6 * B.tripartiteGraph.edgePolynomial (fun _ => 1 / (3 * (Fintype.card V : ℝ))) =
      2 * (B.valency : ℝ) / (9 * (Fintype.card V : ℝ)) := by
  rw [B.tripartiteGraph_edgePolynomial]
  exact B.normalized_tripleSum_uniform

end

end IntervalsTuran.Spectral.BipartiteKernel
