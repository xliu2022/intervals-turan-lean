module

public import IntervalsTuran.Vendor.AKS.MGG.Spectral

/-!
# A labeled permutation expander from the imported MGG proof

The MGG construction and its spectral theorem are due to the upstream
`girving/aks` project; see `docs/aks-import.json`. This local adapter proves that
every fixed port is a permutation, preserves that property under squaring, and
amplifies the imported normalized bound by sixteen walk steps.

These are permutation multigraphs. No assertion of simplicity or of a Cayley
group structure is made here.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace IntervalsTuran.Spectral.MGG

/-- Every fixed port acts bijectively on vertices. -/
def HasPermutationPorts {n d : ℕ} (G : RegularGraph n d) : Prop :=
  ∀ i : Fin d, Function.Bijective (fun v => G.neighbor v i)

/-- The reverse port of the eight MGG shear maps is independent of the vertex. -/
def reversePort : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

theorem reversePort_involutive : Function.Involutive reversePort := by
  intro i
  fin_cases i <;> rfl

theorem mgg_reversePort_eq (n : ℕ) (v : Fin (n * n)) (i : Fin 8) :
    (mgg n).reversePort v i = reversePort i := by
  fin_cases i <;> rfl

theorem mgg_neighbor_reverse (n : ℕ) (v : Fin (n * n)) (i : Fin 8) :
    (mgg n).neighbor ((mgg n).neighbor v i) (reversePort i) = v := by
  simpa only [mgg_reversePort_eq] using (mgg n).neighbor_reversePort v i

theorem mgg_hasPermutationPorts (n : ℕ) : HasPermutationPorts (mgg n) := by
  intro i
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨fun v => (mgg n).neighbor v (reversePort i), ?_, ?_⟩
  · intro v
    exact mgg_neighbor_reverse n v i
  · intro v
    simpa only [reversePort_involutive i] using
      mgg_neighbor_reverse n v (reversePort i)

theorem HasPermutationPorts.square {n d : ℕ} {G : RegularGraph n d}
    (hG : HasPermutationPorts G) : HasPermutationPorts G.square := by
  intro p
  have hd : 0 < d := Nat.pos_of_ne_zero (by
    intro h
    subst d
    exact Nat.not_lt_zero _ p.isLt)
  let i : Fin d := ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩
  let j : Fin d := ⟨p.val % d, Nat.mod_lt _ hd⟩
  have hcomp := (hG j).comp (hG i)
  simpa only [Function.comp_def, square_neighbor_unfold G _ p hd] using hcomp

theorem HasPermutationPorts.iterSquare {n d : ℕ} {G : RegularGraph n d}
    (hG : HasPermutationPorts G) (p : ℕ) :
    HasPermutationPorts (G.iterSquare p) := by
  induction p with
  | zero => exact hG
  | succ p ih => exact ih.square

/-- Four squarings take sixteen steps and use exactly `2^48` ports. -/
abbrev portDegree : ℕ := iterSquareDeg 8 4

theorem portDegree_eq_two_pow : portDegree = 2 ^ 48 := by
  norm_num [portDegree, iterSquareDeg]

theorem portDegree_eq_eight_pow : portDegree = 8 ^ 16 := by
  norm_num [portDegree, iterSquareDeg]

theorem portDegree_pos : 0 < portDegree :=
  iterSquareDeg_pos (by norm_num : 0 < 8) 4

/-- The sixteen-step MGG permutation multigraph, still on exactly `n^2` vertices. -/
def graph (n : ℕ) : RegularGraph (n * n) portDegree :=
  (mgg n).iterSquare 4

theorem graph_hasPermutationPorts (n : ℕ) : HasPermutationPorts (graph n) :=
  (mgg_hasPermutationPorts n).iterSquare 4

/-- The actual permutation corresponding to a labeled walk. -/
noncomputable def portPerm (n : ℕ) (i : Fin portDegree) :
    Equiv.Perm (Fin (n * n)) :=
  Equiv.ofBijective (fun v => (graph n).neighbor v i) (graph_hasPermutationPorts n i)

@[simp] theorem portPerm_apply (n : ℕ) (i : Fin portDegree) (v : Fin (n * n)) :
    portPerm n i v = (graph n).neighbor v i := rfl

/-- The imported MGG estimate, amplified to a normalized operator norm at most `1/6`. -/
theorem graph_gap_le (n : ℕ) (hn : 3 ≤ n) :
    spectralGap (graph n) ≤ (1 : ℝ) / 6 := by
  have hsqrt : Real.sqrt 2 ≤ (178 : ℝ) / 125 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 178 / 125)).2
    norm_num
  have hbase : spectralGap (mgg n) ≤ (89 : ℝ) / 100 := by
    have h := spectralGap_mgg n hn
    nlinarith
  rw [graph, spectralGap_iterSquare]
  calc
    spectralGap (mgg n) ^ (2 ^ 4) ≤ ((89 : ℝ) / 100) ^ (2 ^ 4) :=
      pow_le_pow_left₀ (spectralGap_nonneg _) hbase _
    _ ≤ (1 : ℝ) / 6 := by norm_num

/-- Zero-sum contraction of the normalized walk operator. -/
theorem walk_norm_le (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin (n * n))) (hf : ∑ v, f v = 0) :
    ‖(graph n).walkCLM f‖ ≤ (1 : ℝ) / 6 * ‖f‖ := by
  have hp : meanCLM (n * n) f = 0 := by
    ext v
    simp [meanCLM_apply, hf]
  have h := (ContinuousLinearMap.le_opNorm
    ((graph n).walkCLM - meanCLM (n * n)) f)
  have h' : ‖(graph n).walkCLM f‖ ≤ spectralGap (graph n) * ‖f‖ := by
    simpa only [ContinuousLinearMap.sub_apply, hp, sub_zero, spectralGap] using h
  exact h'.trans (mul_le_mul_of_nonneg_right (graph_gap_le n hn) (norm_nonneg f))

/-- The unnormalized labeled adjacency operator, expressed only through finite sums. -/
theorem sum_square_le (n : ℕ) (hn : 3 ≤ n)
    (f : Fin (n * n) → ℝ) (hf : ∑ v, f v = 0) :
    (∑ v, (∑ i : Fin portDegree, f (portPerm n i v)) ^ 2) ≤
      ((portDegree : ℝ) / 6) ^ 2 * ∑ v, (f v) ^ 2 := by
  let x : EuclideanSpace ℝ (Fin (n * n)) := WithLp.toLp 2 f
  have hx : ∑ v, x v = 0 := by simpa [x] using hf
  have hnorm := walk_norm_le n hn x hx
  have hsq := (sq_le_sq₀ (norm_nonneg ((graph n).walkCLM x))
    (by positivity : 0 ≤ (1 : ℝ) / 6 * ‖x‖)).2 hnorm
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsq
  simp only [RegularGraph.walkCLM_apply, x, PiLp.toLp_apply] at hsq
  have hd : (portDegree : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt portDegree_pos)
  have hscale :
      (∑ v, (∑ i : Fin portDegree, f (portPerm n i v)) ^ 2) =
        (portDegree : ℝ) ^ 2 *
          ∑ v, ((∑ i : Fin portDegree, f ((graph n).neighbor v i)) /
            (portDegree : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [portPerm_apply]
    field_simp
  rw [hscale]
  calc
    _ ≤ (portDegree : ℝ) ^ 2 * ((1 / 6 : ℝ) ^ 2 * ∑ v, (f v) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((portDegree : ℝ) / 6) ^ 2 * ∑ v, (f v) ^ 2 := by ring

end IntervalsTuran.Spectral.MGG

