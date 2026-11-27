module

public import IntervalsTuran.Construction.CompleteGraphs
public import IntervalsTuran.Construction.CompleteJoinWeights
public import IntervalsTuran.Uniformity.MassOptimization

/-!
# Actual finite complete joins

Author and maintainer: Xizhi Liu.

The construction has one copy of the input graph in each part and every edge
meeting more than one part. Finite joins require collision corrections; no
exact Lagrangian join formula is assumed.
-/

@[expose] public section

open scoped BigOperators

namespace IntervalsTuran.RGraph

open Density

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The complete join of copies of `G`, indexed by the finite type `I`. -/
noncomputable def completeJoin (G : RGraph V r) (I : Type*) [Fintype I] [DecidableEq I] :
    RGraph (I × V) r where
  edges := Finset.univ.powersetCard r |>.filter (fun e =>
    e.image Prod.snd ∈ G.edges ∨ ∃ u ∈ e, ∃ v ∈ e, u.1 ≠ v.1)
  uniform _e he := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp]
theorem mem_completeJoin (G : RGraph V r) {I : Type*} [Fintype I] [DecidableEq I]
    (e : Finset (I × V)) :
    e ∈ (G.completeJoin I).edges ↔ e.card = r ∧
      (e.image Prod.snd ∈ G.edges ∨ ∃ u ∈ e, ∃ v ∈ e, u.1 ≠ v.1) := by
  classical
  simp only [completeJoin, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]

theorem completeJoin_part_embedding (G : RGraph V r)
    {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    G.IsEmbedding (G.completeJoin I) (fun v => (i, v)) := by
  classical
  have hinj : Function.Injective (fun v : V => (i, v)) := fun _ _ h => congrArg Prod.snd h
  refine ⟨hinj, ?_⟩
  intro e he
  apply (G.mem_completeJoin _).mpr
  refine ⟨?_, Or.inl ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, G.uniform e he]
  · simpa only [Finset.image_image, Function.comp_def, Finset.image_id'] using he

theorem oneEdge_isHom_completeJoin_iff (G : RGraph V r)
    {I : Type*} [Fintype I] [DecidableEq I] (f : Fin r → I × V) :
    (oneEdge r).IsHom (G.completeJoin I) f ↔ Function.Injective f ∧
      ((oneEdge r).IsHom G (fun a => (f a).2) ∨ ∃ a b, (f a).1 ≠ (f b).1) := by
  classical
  rw [(G.completeJoin I).oneEdge_isHom, G.mem_completeJoin]
  constructor
  · rintro ⟨hcard, hcase⟩
    have hinj : Function.Injective f := by
      have hcard' : (Finset.univ.image f).card = (Finset.univ : Finset (Fin r)).card := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hcard
      have h := Finset.card_image_iff.mp hcard'
      exact fun a b hab => h (Finset.mem_univ a) (Finset.mem_univ b) hab
    refine ⟨hinj, ?_⟩
    rcases hcase with hG | ⟨u, hu, v, hv, huv⟩
    · left
      apply (G.oneEdge_isHom _).mpr
      simpa only [Finset.image_image, Function.comp_def] using hG
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
      exact Or.inr ⟨a, b, huv⟩
  · rintro ⟨hinj, hcase⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · rcases hcase with hG | ⟨a, b, hab⟩
      · left
        simpa only [Finset.image_image, Function.comp_def] using (G.oneEdge_isHom _).mp hG
      · exact Or.inr ⟨f a, Finset.mem_image_of_mem _ (Finset.mem_univ a),
          f b, Finset.mem_image_of_mem _ (Finset.mem_univ b), hab⟩

theorem oneEdge_isHom_complete_iff {W : Type*} [Fintype W] [DecidableEq W]
    (f : Fin r → W) : (oneEdge r).IsHom (complete W r) f ↔ Function.Injective f := by
  rw [(complete W r).oneEdge_isHom]
  simp only [complete, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · intro h
    have hcard : (Finset.univ.image f).card = (Finset.univ : Finset (Fin r)).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using h
    have hi := Finset.card_image_iff.mp hcard
    exact fun a b hab => hi (Finset.mem_univ a) (Finset.mem_univ b) hab
  · intro h
    rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]

theorem oneEdge_homIndicator_completeJoin (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] (f : Fin r → I × V) :
    (oneEdge r).homIndicator (G.completeJoin I) f =
      (oneEdge r).homIndicator (complete (I × V) r) f -
      (∑ i : I, if ∀ a, (f a).1 = i then
        (oneEdge r).homIndicator (complete V r) (fun a => (f a).2) else 0) +
      (∑ i : I, if ∀ a, (f a).1 = i then
        (oneEdge r).homIndicator G (fun a => (f a).2) else 0) := by
  classical
  let a₀ : Fin r := ⟨0, hr⟩
  let i₀ : I := (f a₀).1
  by_cases hconstant : ∀ a, (f a).1 = i₀
  · have hiff (i : I) : (∀ a, (f a).1 = i) ↔ i = i₀ := by
      constructor
      · intro h
        exact (h a₀).symm
      · intro h
        simpa only [h] using hconstant
    have hsum (c : ℝ) : (∑ i : I, if ∀ a, (f a).1 = i then c else 0) = c := by
      simp only [hiff]
      simp
    rw [hsum, hsum]
    have hinj : Function.Injective f ↔ Function.Injective (fun a => (f a).2) := by
      constructor
      · intro h a b hab
        exact h (Prod.ext ((hconstant a).trans (hconstant b).symm) hab)
      · intro h a b hab
        exact h (congrArg Prod.snd hab)
    have hcross : ¬ ∃ a b, (f a).1 ≠ (f b).1 := by
      rintro ⟨a, b, hab⟩
      exact hab ((hconstant a).trans (hconstant b).symm)
    have hcomplete : (oneEdge r).homIndicator (complete (I × V) r) f =
        (oneEdge r).homIndicator (complete V r) (fun a => (f a).2) := by
      simp only [homIndicator, oneEdge_isHom_complete_iff, hinj]
    have hjoin : (oneEdge r).homIndicator (G.completeJoin I) f =
        (oneEdge r).homIndicator G (fun a => (f a).2) := by
      unfold homIndicator
      congr 1
      apply propext
      rw [G.oneEdge_isHom_completeJoin_iff, hinj]
      constructor
      · rintro ⟨_, hg | hc⟩
        · exact hg
        · exact (hcross hc).elim
      · intro hg
        refine ⟨?_, Or.inl hg⟩
        intro a b hab
        exact hg.injOn_edge (by simp [oneEdge])
          (Finset.mem_univ a) (Finset.mem_univ b) hab
    rw [hcomplete, hjoin]
    ring
  · have hnone (i : I) : ¬ ∀ a, (f a).1 = i := by
      intro h
      exact hconstant (fun a => (h a).trans (h a₀).symm)
    have hcross : ∃ a b, (f a).1 ≠ (f b).1 := by
      obtain ⟨a, ha⟩ := not_forall.mp hconstant
      exact ⟨a, a₀, ha⟩
    simp only [ite_eq_right (hnone _), Finset.sum_const_zero, sub_zero, add_zero]
    simp only [homIndicator, G.oneEdge_isHom_completeJoin_iff, hcross,
      or_true, and_true, oneEdge_isHom_complete_iff]

theorem weightedMean_constant_part_oneEdge (G : RGraph V r)
    {I : Type*} [Fintype I] [DecidableEq I] (x : I × V → ℝ) (i : I) :
    weightedMean x (fun f : Fin r → I × V =>
      if ∀ a, (f a).1 = i then
        (oneEdge r).homIndicator G (fun a => (f a).2) else 0) =
      (r.factorial : ℝ) * G.edgePolynomial (fun v => x (i, v)) := by
  classical
  convert! (weightedMean_constant_part x i ((oneEdge r).homIndicator G)).trans
    (weightedMean_oneEdge G _)

/-- The exact finite-join polynomial decomposition. In uniformity three,
expanding the complete-graph terms gives the explicit collision correction
needed by the outer spectral construction. -/
theorem completeJoin_normalizedPolynomial (G : RGraph V r) (hr : 0 < r)
    {I : Type*} [Fintype I] [DecidableEq I] (x : I × V → ℝ) :
    (r.factorial : ℝ) * (G.completeJoin I).edgePolynomial x =
      (r.factorial : ℝ) * (complete (I × V) r).edgePolynomial x -
      (∑ i : I, (r.factorial : ℝ) * (complete V r).edgePolynomial (fun v => x (i, v))) +
      (∑ i : I, (r.factorial : ℝ) * G.edgePolynomial (fun v => x (i, v))) := by
  classical
  calc
    _ = weightedMean x ((oneEdge r).homIndicator (G.completeJoin I)) :=
      (weightedMean_oneEdge _ x).symm
    _ = weightedMean x (fun f : Fin r → I × V =>
        (oneEdge r).homIndicator (complete (I × V) r) f -
        (∑ i : I, if ∀ a, (f a).1 = i then
          (oneEdge r).homIndicator (complete V r) (fun a => (f a).2) else 0) +
        (∑ i : I, if ∀ a, (f a).1 = i then
          (oneEdge r).homIndicator G (fun a => (f a).2) else 0)) :=
      weightedMean_congr x (fun f => G.oneEdge_homIndicator_completeJoin hr f)
    _ = _ := by
      rw [weightedMean_add, weightedMean_sub, weightedMean_sum, weightedMean_sum]
      simp only [weightedMean_constant_part_oneEdge, weightedMean_oneEdge]

end IntervalsTuran.RGraph
