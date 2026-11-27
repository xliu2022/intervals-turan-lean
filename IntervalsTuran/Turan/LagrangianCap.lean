module

public import IntervalsTuran.Hypergraph.LagrangianHom
public import IntervalsTuran.Density.FiniteSubfamilyInf
public import IntervalsTuran.Density.FamilyUpper

/-!
# Realizing limits of finite Lagrangians from below

Author and maintainer: Xizhi Liu.

The forbidden family consists of the actual finite hypergraphs whose normalized
Lagrangian exceeds a real threshold.  Its ordinary Turan density realizes every
limit of finite Lagrangians approaching that threshold from below.  Neither
spectrum closedness nor a spectral existence hypothesis is used here.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran

/-- The spectrum of ordinary Turan densities of arbitrary forbidden families. -/
def turanSpectrum (r : ℕ) : Set ℝ := Set.range (@SetFamily.turanDensity r)

namespace SetFamily

variable {r : ℕ}

/-- All finite hypergraphs whose normalized Lagrangian exceeds `x`. -/
def lagrangianCap (r : ℕ) (x : ℝ) : Set (FiniteGraph r) :=
  {G | x < G.2.lagrangian}

theorem free_lagrangianCap_iff {n : ℕ} (G : RGraph (Fin n) r) (x : ℝ) :
    Free (lagrangianCap r x) G ↔ G.lagrangian ≤ x := by
  constructor
  · intro hG
    apply le_of_not_gt
    intro h
    exact hG ⟨n, G⟩ h ⟨id, Function.injective_id, G.isHom_id⟩
  · intro hG A hA
    rintro ⟨f, hf⟩
    exact (not_lt_of_ge (hf.isHom.lagrangian_le.trans hG)) hA

theorem homFree_lagrangianCap_iff {n : ℕ} (G : RGraph (Fin n) r) (x : ℝ) :
    HomFree (lagrangianCap r x) G ↔ G.lagrangian ≤ x := by
  constructor
  · intro hG
    exact (free_lagrangianCap_iff G x).mp hG.free
  · intro hG A hA
    rintro ⟨f, hf⟩
    exact (not_lt_of_ge (hf.lagrangian_le.trans hG)) hA

/-- The finite-subfamily infimum transfers the existing finite weighted lower
bound to arbitrary forbidden families. -/
theorem lagrangian_le_turanDensity_of_homFree (F : Set (FiniteGraph r))
    {n : ℕ} (G : RGraph (Fin n) r) (hG : HomFree F G) :
    G.lagrangian ≤ turanDensity F := by
  rw [turanDensity_eq_sInf_finite]
  apply le_csInf (finiteDensityValues_nonempty F)
  rintro z ⟨E, hE, rfl⟩
  exact G.lagrangian_le_familyTuranDensity E (hG.mono hE)

noncomputable def normalizedExtremalDensity (F : Set (FiniteGraph r)) (n : ℕ) : ℝ :=
  (r.factorial : ℝ) * extremalNumber F n / (n : ℝ) ^ r

theorem normalizedExtremalDensity_eq_factor (F : Set (FiniteGraph r))
    {n : ℕ} (hn : r ≤ n) :
    normalizedExtremalDensity F n = samplingFactor r n * extremalDensity F n := by
  have hc : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hn)
  unfold normalizedExtremalDensity samplingFactor extremalDensity
  field_simp

theorem normalizedExtremalDensity_tendsto (F : Set (FiniteGraph r)) :
    Tendsto (normalizedExtremalDensity F) atTop (𝓝 (turanDensity F)) := by
  have h := (samplingFactor_tendsto r).mul (extremalDensity_tendsto F)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop r] with n hn
  exact (normalizedExtremalDensity_eq_factor F hn).symm

theorem turanDensity_lagrangianCap_le (x : ℝ) (hx : 0 ≤ x) (hr : 0 < r) :
    turanDensity (lagrangianCap r x) ≤ x := by
  apply le_of_tendsto (normalizedExtremalDensity_tendsto (lagrangianCap r x))
  apply Filter.Eventually.of_forall
  intro n
  by_cases hn : n = 0
  · subst n
    simpa [normalizedExtremalDensity, zero_pow (Nat.ne_of_gt hr)] using hx
  by_cases hz : extremalNumber (lagrangianCap r x) n = 0
  · simpa [normalizedExtremalDensity, hz] using hx
  obtain ⟨G, hG, hc⟩ := exists_extremal_of_ne_zero (lagrangianCap r x) n hz
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hl := G.normalizedPolynomial_le_lagrangian _ probabilityWeights_uniform
  rw [← G.oneEdge_homDensity_polynomial] at hl
  have hu := hl.trans ((free_lagrangianCap_iff G x).mp hG)
  simpa [RGraph.oneEdge_homDensity, normalizedExtremalDensity, hc] using hu

/-- An actual limit of finite Lagrangians from below is the ordinary Turan
density of the explicitly defined cap family. -/
theorem turanDensity_lagrangianCap_eq_of_tendsto (hr : 0 < r)
    (G : ℕ → FiniteGraph r) (x : ℝ)
    (hbelow : ∀ n, (G n).2.lagrangian ≤ x)
    (hlim : Tendsto (fun n => (G n).2.lagrangian) atTop (𝓝 x)) :
    turanDensity (lagrangianCap r x) = x := by
  have hx : 0 ≤ x := ((G 0).2.lagrangian_nonneg).trans (hbelow 0)
  apply le_antisymm (turanDensity_lagrangianCap_le x hx hr)
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    lagrangian_le_turanDensity_of_homFree _ (G n).2
      ((homFree_lagrangianCap_iff (G n).2 x).mpr (hbelow n))

end SetFamily

/-- Finite hypergraph Lagrangians approximating a value from below. -/
def BelowLagrangianApprox (r : ℕ) (x : ℝ) : Prop :=
  ∃ G : ℕ → FiniteGraph r,
    (∀ n, (G n).2.lagrangian ≤ x) ∧
      Tendsto (fun n => (G n).2.lagrangian) atTop (𝓝 x)

theorem BelowLagrangianApprox.mem_turanSpectrum {r : ℕ} {x : ℝ}
    (h : BelowLagrangianApprox r x) (hr : 0 < r) : x ∈ turanSpectrum r := by
  obtain ⟨G, hbelow, hlim⟩ := h
  exact ⟨SetFamily.lagrangianCap r x,
    SetFamily.turanDensity_lagrangianCap_eq_of_tendsto hr G x hbelow hlim⟩

theorem BelowLagrangianApprox.nonneg {r : ℕ} {x : ℝ}
    (h : BelowLagrangianApprox r x) : 0 ≤ x := by
  obtain ⟨G, hbelow, _⟩ := h
  exact ((G 0).2.lagrangian_nonneg).trans (hbelow 0)

theorem BelowLagrangianApprox.le_one {r : ℕ} {x : ℝ}
    (h : BelowLagrangianApprox r x) : x ≤ 1 := by
  obtain ⟨G, _, hlim⟩ := h
  exact le_of_tendsto hlim (Filter.Eventually.of_forall fun n => (G n).2.lagrangian_le_one)

end IntervalsTuran
