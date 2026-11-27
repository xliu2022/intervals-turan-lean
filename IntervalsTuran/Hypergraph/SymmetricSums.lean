module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic

/-!
# Cubic elementary symmetric identities

Author and maintainer: Xizhi Liu.

Extracted from `TuranUniversality/Weighted/Symmetric.lean`; exact source hash
and extraction details are recorded in `docs/reused-foundation.json`.
-/

@[expose] public section

namespace IntervalsTuran.Weighted


open scoped BigOperators

noncomputable def elementary {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) (k : ℕ) : ℝ :=
  ∑ e ∈ I.powersetCard k, ∏ v ∈ e, z v

theorem multiset_esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

theorem multiset_esymm_cons (a : ℝ) (s : Multiset ℝ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
  rw [← Multiset.sum_map_mul_left]

theorem multiset_second_identity (s : Multiset ℝ) :
    2 * s.esymm 2 = s.sum ^ 2 - (s.map (fun z => z ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [multiset_esymm_cons a s 1, multiset_esymm_one]
    simp only [Multiset.sum_cons, Multiset.map_cons]
    nlinarith

theorem multiset_third_identity (s : Multiset ℝ) :
    6 * s.esymm 3 = s.sum ^ 3 - 3 * s.sum * (s.map (fun z => z ^ 2)).sum +
      2 * (s.map (fun z => z ^ 3)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [multiset_esymm_cons a s 2]
    simp only [Multiset.sum_cons, Multiset.map_cons]
    have hsecond := multiset_second_identity s
    linear_combination ih + 3 * a * hsecond

theorem elementary_second_identity {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) :
    2 * elementary I z 2 = (∑ v ∈ I, z v) ^ 2 - ∑ v ∈ I, (z v) ^ 2 := by
  have h := multiset_second_identity (I.val.map z)
  simpa only [Finset.esymm_map_val, Multiset.map_map, Function.comp_apply,
    Finset.sum_map_val, elementary] using h

theorem elementary_third_identity {V : Type*} [DecidableEq V]
    (I : Finset V) (z : V → ℝ) :
    6 * elementary I z 3 = (∑ v ∈ I, z v) ^ 3 -
      3 * (∑ v ∈ I, z v) * (∑ v ∈ I, (z v) ^ 2) + 2 * ∑ v ∈ I, (z v) ^ 3 := by
  have h := multiset_third_identity (I.val.map z)
  simpa only [Finset.esymm_map_val, Multiset.map_map, Function.comp_apply,
    Finset.sum_map_val, elementary] using h

end IntervalsTuran.Weighted
