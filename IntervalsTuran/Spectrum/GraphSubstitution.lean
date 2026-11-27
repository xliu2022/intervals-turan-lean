module

public import IntervalsTuran.Hypergraph.LagrangianHom
public import IntervalsTuran.Hypergraph.Relabel

@[expose] public section

/-! # Actual finite hypergraph substitution

Replace each vertex of a base graph by a separate finite child graph. Edges
are the transversal blowup of the base together with the child edges. The
polynomial identity below is exact on finite graphs and arbitrary real weights.
-/

namespace IntervalsTuran.Spectrum

open Finset Density

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I]
variable {V : I → Type v} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable {r : ℕ}

theorem sigma_mk_injective (i : I) : Function.Injective (Sigma.mk i : V i → Sigma V) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

def childEdges (G : ∀ i, RGraph (V i) r) (i : I) : Finset (Finset (Sigma V)) :=
  (G i).edges.image (fun e => e.image (Sigma.mk i))

def withinGraph (G : ∀ i, RGraph (V i) r) : RGraph (Sigma V) r where
  edges := Finset.univ.biUnion (childEdges G)
  uniform e he := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.card_image_of_injective _ (sigma_mk_injective i)]
    exact (G i).uniform d hd

def substitute (H : RGraph I r) (G : ∀ i, RGraph (V i) r) : RGraph (Sigma V) r where
  edges := (H.inverseImage Sigma.fst).edges ∪ (withinGraph G).edges
  uniform e he := by
    rcases Finset.mem_union.mp he with h | h
    · exact (H.inverseImage Sigma.fst).uniform e h
    · exact (withinGraph G).uniform e h

theorem childEdges_projection (G : ∀ i, RGraph (V i) r) (hr : 0 < r)
    (i : I) {e : Finset (Sigma V)} (he : e ∈ childEdges G i) :
    e.image Sigma.fst = {i} := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  have hdne : d.Nonempty := Finset.card_pos.mp (by simpa [(G i).uniform d hd] using hr)
  rw [Finset.image_image]
  exact Finset.image_const hdne i

theorem childEdges_pairwiseDisjoint (G : ∀ i, RGraph (V i) r) (hr : 0 < r) :
    (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint (childEdges G) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have h := (childEdges_projection G hr i hei).symm.trans (childEdges_projection G hr j hej)
  exact hij (Finset.singleton_injective h)

theorem cross_within_disjoint (H : RGraph I r) (G : ∀ i, RGraph (V i) r)
    (hr : 2 ≤ r) : Disjoint (H.inverseImage Sigma.fst).edges (withinGraph G).edges := by
  apply Finset.disjoint_left.mpr
  intro e he hwithin
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hwithin
  have hbase := ((H.mem_inverseImage Sigma.fst e).mp he).2
  rw [childEdges_projection G (by omega) i hi] at hbase
  have h := H.uniform {i} hbase
  simp only [Finset.card_singleton] at h
  omega

theorem withinGraph_polynomial (G : ∀ i, RGraph (V i) r) (hr : 0 < r)
    (x : Sigma V → ℝ) :
    (withinGraph G).edgePolynomial x = ∑ i, (G i).edgePolynomial (fun v => x ⟨i, v⟩) := by
  unfold RGraph.edgePolynomial withinGraph
  rw [Finset.sum_biUnion (childEdges_pairwiseDisjoint G hr)]
  apply Finset.sum_congr rfl
  intro i _
  rw [childEdges, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e _
    exact Finset.prod_image (fun a _ b _ hab => sigma_mk_injective i hab)
  · intro a _ b _ hab
    exact Finset.image_injective (sigma_mk_injective i) hab

def partMass (x : Sigma V → ℝ) (i : I) : ℝ := ∑ v, x ⟨i, v⟩

theorem pushforwardWeight_sigma (x : Sigma V → ℝ) :
    pushforwardWeight Sigma.fst x = partMass x := by
  funext i
  unfold pushforwardWeight partMass
  let e : {v : Sigma V // v.1 = i} ≃ V i :=
    { toFun := fun v => v.property ▸ v.val.2
      invFun := fun v => ⟨⟨i, v⟩, rfl⟩
      left_inv := by rintro ⟨⟨j, v⟩, hj⟩; cases hj; rfl
      right_inv := by intro v; rfl }
  apply Fintype.sum_equiv e
  rintro ⟨⟨j, v⟩, hj⟩
  cases hj
  rfl

theorem substitute_polynomial (H : RGraph I r) (G : ∀ i, RGraph (V i) r)
    (hr : 2 ≤ r) (x : Sigma V → ℝ) :
    (substitute H G).edgePolynomial x =
      H.edgePolynomial (partMass x) + ∑ i, (G i).edgePolynomial (fun v => x ⟨i, v⟩) := by
  change (∑ e ∈ (H.inverseImage Sigma.fst).edges ∪ (withinGraph G).edges,
      ∏ v ∈ e, x v) = _
  rw [Finset.sum_union (cross_within_disjoint H G hr)]
  change (H.inverseImage Sigma.fst).edgePolynomial x + (withinGraph G).edgePolynomial x = _
  rw [H.edgePolynomial_inverseImage, pushforwardWeight_sigma, withinGraph_polynomial G (by omega)]

theorem partMass_probability {x : Sigma V → ℝ} (hx : ProbabilityWeights x) :
    ProbabilityWeights (partMass x) := by
  rw [← pushforwardWeight_sigma]
  exact pushforwardWeight_probability Sigma.fst x hx

theorem child_into_substitute (H : RGraph I r) (G : ∀ i, RGraph (V i) r) (i : I) :
    (G i).IsEmbedding (substitute H G) (Sigma.mk i) := by
  refine ⟨sigma_mk_injective i, ?_⟩
  intro e he
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩

end IntervalsTuran.Spectrum
