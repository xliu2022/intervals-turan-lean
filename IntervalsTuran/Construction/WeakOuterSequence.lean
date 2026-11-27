/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Construction.WeakOuterGraph
public import IntervalsTuran.Spectral.SimpleExpanderFamily
public import IntervalsTuran.Hypergraph.Relabel
public import IntervalsTuran.Hypergraph.LagrangianHom

/-!
# An unconditional smooth sequence of finite three-graph Lagrangians

The sequence uses the formally proved MGG family, its simple finite-field
lift, and the additive tripartite gadget. There is no spectral-existence
parameter in any theorem in this file.
-/

@[expose] public section

open Filter Topology

namespace IntervalsTuran.Spectral.SimpleExpander

noncomputable section

def canonicalFiniteGraph {W : Type} [Fintype W] [DecidableEq W]
    (G : RGraph W 3) : FiniteGraph 3 :=
  ⟨Fintype.card W, G.pullback (Fintype.equivFin W).symm.toEmbedding⟩

theorem canonicalFiniteGraph_lagrangian
    {W : Type} [Fintype W] [DecidableEq W] (G : RGraph W 3) :
    (canonicalFiniteGraph G).2.lagrangian = G.lagrangian := by
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  exact le_antisymm (G.pullback_equiv_embedding e).isHom.lagrangian_le
    (G.pullback_equiv_inverse e).isHom.lagrangian_le

def baseValue : ℝ := Construction.weakOuterBase k

def outerSequence (j : ℕ) : FiniteGraph 3 :=
  canonicalFiniteGraph ((kernel j).weakOuterGraph k)

theorem outerSequence_lagrangian_relabel (j : ℕ) :
    (outerSequence j).2.lagrangian = ((kernel j).weakOuterGraph k).lagrangian := by
  exact canonicalFiniteGraph_lagrangian ((kernel j).weakOuterGraph k)

theorem outerSequence_lagrangian (j : ℕ) :
    (outerSequence j).2.lagrangian =
      Construction.weakOuterValue k (3 * (order j : ℝ)) := by
  rw [outerSequence_lagrangian_relabel]
  have hs : 48 * (k : ℝ) ≤ 3 * (Fintype.card (ZMod (order j)) : ℝ) := by
    simpa only [ZMod.card, Nat.cast_mul, Nat.cast_ofNat] using
      (show ((48 * k : ℕ) : ℝ) ≤ ((3 * order j : ℕ) : ℝ) by
        exact_mod_cast order_large j)
  simpa only [ZMod.card] using
    (kernel j).weakOuterGraph_lagrangian four_le_k (kernel_valency j)
      (kernel_hasZeroSumBound_real j) hs

theorem baseValue_lt_outerSequence (j : ℕ) : baseValue < (outerSequence j).2.lagrangian := by
  rw [outerSequence_lagrangian]
  have hn : (0 : ℝ) < order j := by exact_mod_cast order_pos j
  have hc := Construction.weakOuterCoefficient_pos (show 0 < k by have := four_le_k; omega)
  exact lt_add_of_pos_right _ (div_pos hc (by positivity))

theorem outerSequence_strictAnti : StrictAnti (fun j => (outerSequence j).2.lagrangian) := by
  intro i j hij
  change (outerSequence j).2.lagrangian < (outerSequence i).2.lagrangian
  rw [outerSequence_lagrangian, outerSequence_lagrangian]
  unfold Construction.weakOuterValue
  have hn : (0 : ℝ) < order i := by exact_mod_cast order_pos i
  have hnij : (order i : ℝ) < order j := by exact_mod_cast order_strictMono hij
  have hc := Construction.weakOuterCoefficient_pos (show 0 < k by have := four_le_k; omega)
  have hdiv := div_lt_div_of_pos_left hc
    (mul_pos (show (0 : ℝ) < 3 by norm_num) hn)
    (mul_lt_mul_of_pos_left hnij (by norm_num : (0 : ℝ) < 3))
  linarith only [hdiv]

theorem outerSequence_tendsto :
    Tendsto (fun j => (outerSequence j).2.lagrangian) atTop (𝓝 baseValue) := by
  have hm : Tendsto (fun j => 3 * (order j : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) order_tendsto
  have hinv : Tendsto (fun j => (3 * (order j : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hm
  have h := (tendsto_const_nhds (x := baseValue)).add
    ((tendsto_const_nhds (x := Construction.weakOuterCoefficient k)).mul hinv)
  simpa only [outerSequence_lagrangian, Construction.weakOuterValue, baseValue,
    div_eq_mul_inv, mul_zero, add_zero] using h

theorem outerSequence_gap_ratio (j : ℕ) :
    ((outerSequence j).2.lagrangian - baseValue) /
      ((outerSequence (j + 1)).2.lagrangian - baseValue) =
        (order (j + 1) : ℝ) / (order j : ℝ) := by
  rw [outerSequence_lagrangian, outerSequence_lagrangian]
  unfold Construction.weakOuterValue baseValue
  have hn : (order j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (order_pos j))
  have hn' : (order (j + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (order_pos (j + 1)))
  have hc : Construction.weakOuterCoefficient k ≠ 0 :=
    (Construction.weakOuterCoefficient_pos (show 0 < k by have := four_le_k; omega)).ne'
  simp only [add_sub_cancel_left]
  field_simp [hc, hn, hn']

theorem outerSequence_gap_ratio_tendsto :
    Tendsto (fun j => ((outerSequence j).2.lagrangian - baseValue) /
      ((outerSequence (j + 1)).2.lagrangian - baseValue)) atTop (𝓝 1) := by
  simpa only [outerSequence_gap_ratio] using order_ratio_tendsto

/-- Actual finite witnesses, without a Cayley-family or other spectral premise. -/
theorem exists_smooth_finite_lagrangians :
    ∃ Q : ℕ → FiniteGraph 3,
      (∀ j, baseValue < (Q j).2.lagrangian) ∧
      StrictAnti (fun j => (Q j).2.lagrangian) ∧
      Tendsto (fun j => (Q j).2.lagrangian) atTop (𝓝 baseValue) ∧
      Tendsto (fun j => ((Q j).2.lagrangian - baseValue) /
        ((Q (j + 1)).2.lagrangian - baseValue)) atTop (𝓝 1) :=
  ⟨outerSequence, baseValue_lt_outerSequence, outerSequence_strictAnti,
    outerSequence_tendsto, outerSequence_gap_ratio_tendsto⟩

end
end IntervalsTuran.Spectral.SimpleExpander
