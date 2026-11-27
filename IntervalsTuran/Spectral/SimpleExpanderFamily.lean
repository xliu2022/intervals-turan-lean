/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IntervalsTuran.Spectral.PermutationLift
public import IntervalsTuran.Spectral.KernelRelabel
public import IntervalsTuran.Vendor.AKS.MGG.Adapter
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A smooth family of simple bipartite expanders

The fixed finite field has `2^48` elements. The varying base size is `(j+3)^2`,
so the lifted orders are explicit quadratic polynomials and have consecutive
ratios tending to one. All numerical constants are fixed natural numbers.
-/

@[expose] public section

namespace IntervalsTuran.Spectral.SimpleExpander

open scoped BigOperators Topology
open Filter

/-- The number of sixteen-step MGG ports and the size of the fiber field. -/
def q : ℕ := 2 ^ 48

/-- The degree of the simple lift. -/
def d : ℕ := q * (q - 1)

/-- The parameter used by the product selector. -/
def k : ℕ := d / 5

theorem q_pos : 0 < q := by norm_num [q]

theorem q_large : 37 ≤ q := by norm_num [q]

theorem five_mul_k : 5 * k = d := by norm_num [k, d, q]

theorem four_le_k : 4 ≤ k := by norm_num [k, d, q]

/-- The field used to distinguish all walk ports by simple edges. -/
abbrev PortField := GaloisField 2 48

noncomputable instance portFieldFintype : Fintype PortField := Fintype.ofFinite PortField
noncomputable instance portFieldDecidableEq : DecidableEq PortField := Classical.decEq _

theorem card_portField : Fintype.card PortField = q := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 48 (by decide)

/-- Exact order of the `j`th simple kernel. -/
def order (j : ℕ) : ℕ := (j + 3)^2 * q^2

theorem order_pos (j : ℕ) : 0 < order j := by
  dsimp [order]
  exact mul_pos (pow_pos (by omega) _) (pow_pos q_pos _)

instance order_neZero (j : ℕ) : NeZero (order j) := ⟨ne_of_gt (order_pos j)⟩

theorem order_strictMono : StrictMono order := by
  intro i j hij
  have hp : (i + 3)^2 < (j + 3)^2 := by nlinarith
  exact Nat.mul_lt_mul_of_pos_right hp (pow_pos q_pos _)

theorem order_tendsto_nat : Tendsto order atTop atTop := order_strictMono.tendsto_atTop

theorem order_tendsto : Tendsto (fun j => (order j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp order_tendsto_nat

theorem order_ratio_tendsto :
    Tendsto (fun j => (order (j + 1) : ℝ) / order j) atTop (𝓝 1) := by
  have hratio : Tendsto (fun j : ℕ => ((j : ℝ) + 4) / ((j : ℝ) + 3))
      atTop (𝓝 1) := by
    simpa only [one_mul, div_one, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (4 : ℝ) 3 1 (d := 1) (by norm_num))
  have hq : (q : ℝ)^2 ≠ 0 := by exact_mod_cast (pow_ne_zero 2 (ne_of_gt q_pos))
  have heq (j : ℕ) : (order (j + 1) : ℝ) / order j =
      (((j : ℝ) + 4) / ((j : ℝ) + 3))^2 := by
    simp only [order, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat]
    rw [mul_div_mul_right _ _ hq, div_pow]
    congr 2
    ring
  simp_rw [heq]
  simpa using hratio.pow 2

/-- The first member already satisfies the size requirement of the selector. -/
theorem order_large (j : ℕ) : 48 * k ≤ 3 * order j := by
  have hd : d ≤ q^2 := by
    dsimp [d]
    have hq := q_pos
    rw [pow_two]
    exact Nat.mul_le_mul_left q (Nat.sub_le q 1)
  have hk : 5 * k ≤ q^2 := by rw [five_mul_k]; exact hd
  have hj : 9 ≤ (j + 3)^2 := by
    calc
      9 = (3 : ℕ)^2 := by norm_num
      _ ≤ (j + 3)^2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul_right (q^2) hj
  dsimp [order]
  nlinarith

/-- The original MGG vertex type before adjoining two field coordinates. -/
abbrev BaseVertex (j : ℕ) := Fin ((j + 3) * (j + 3))

abbrev LiftVertex (j : ℕ) := PermutationLift.Vertex (BaseVertex j) PortField

theorem card_liftVertex (j : ℕ) : Fintype.card (LiftVertex j) = order j := by
  simp only [LiftVertex, PermutationLift.Vertex, BaseVertex, Fintype.card_prod,
    Fintype.card_fin, card_portField, order]
  ring

/-- Transfer to a cyclic additive group of exactly the same size. -/
noncomputable def vertexEquiv (j : ℕ) : LiftVertex j ≃ ZMod (order j) :=
  Fintype.equivOfCardEq (by rw [card_liftVertex, ZMod.card])

/-- Each field element labels one of the sixteen-step MGG permutations. -/
noncomputable def portEquiv : PortField ≃ Fin MGG.portDegree :=
  Fintype.equivFinOfCardEq (card_portField.trans MGG.portDegree_eq_two_pow.symm)

noncomputable def ports (j : ℕ) (i : PortField) : Equiv.Perm (BaseVertex j) :=
  MGG.portPerm (j + 3) (portEquiv i)

theorem base_sum_square_le (j : ℕ) (f : BaseVertex j → ℝ) (hf : ∑ v, f v = 0) :
    ∑ v, (PermutationLift.baseOperator (ports j) f v)^2 ≤
      ((Fintype.card PortField : ℝ) / 6)^2 * ∑ v, (f v)^2 := by
  have hsum (v : BaseVertex j) :
      (∑ i : PortField, f (ports j i v)) =
        ∑ i : Fin MGG.portDegree, f (MGG.portPerm (j + 3) i v) :=
    Equiv.sum_comp portEquiv (fun i => f (MGG.portPerm (j + 3) i v))
  simp only [PermutationLift.baseOperator, hsum]
  simpa only [card_portField, MGG.portDegree_eq_two_pow, q] using
    MGG.sum_square_le (j + 3) (by omega) f hf

/-- The actual simple regular kernel on an additive cyclic group. -/
noncomputable def kernel (j : ℕ) : BipartiteKernel (ZMod (order j)) :=
  (PermutationLift.kernel (ports j)).relabel (vertexEquiv j)

@[simp] theorem kernel_valency (j : ℕ) : (kernel j).valency = 5 * k := by
  simp only [kernel, BipartiteKernel.relabel_valency, PermutationLift.kernel_valency,
    card_portField]
  exact five_mul_k.symm

theorem kernel_hasZeroSumBound (j : ℕ) :
    (kernel j).HasZeroSumBound ((5 * k : ℕ) / (6 : ℝ)) := by
  have h := PermutationLift.kernel_hasZeroSumBound_one_sixth (ports j)
    (by simpa only [card_portField] using q_large) (base_sum_square_le j)
  have hr := BipartiteKernel.hasZeroSumBound_relabel
    (PermutationLift.kernel (ports j)) (vertexEquiv j) h
  change (kernel j).HasZeroSumBound _ at hr
  have hdegree : q * (q - 1) = 5 * k := five_mul_k.symm
  simpa only [PermutationLift.kernel_valency, card_portField,
    hdegree] using hr

theorem kernel_hasZeroSumBound_real (j : ℕ) :
    (kernel j).HasZeroSumBound (5 * (k : ℝ) / 6) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using kernel_hasZeroSumBound j

end IntervalsTuran.Spectral.SimpleExpander
