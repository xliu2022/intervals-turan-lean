module

public import Mathlib.Data.Nat.Nth
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

/-!
# Dense integer parameters and smooth polynomial orders

Author and maintainer: Xizhi Liu.

An eventual element in every fixed multiplicative interval forces the actual
increasing enumeration to have consecutive ratio tending to one. Nonzero
polynomials preserve this ratio asymptotic. The natural number expression
`q * (q^2 - 1) / 2`, used for odd-field projective special linear group orders,
is treated by an exact cast identity, including its divisibility by two.

This file proves the transfer results. It does not assume or assert a prime
number theorem or an existence theorem for Ramanujan graphs.
-/

@[expose] public section

namespace IntervalsTuran.Spectral

open Set Filter Asymptotics
open scoped Topology Polynomial

noncomputable section

/-- Every multiplicative interval of fixed positive relative length eventually
contains an integer satisfying `P`. The quantifier ranges over real endpoints. -/
def MultiplicativelyDenseAtTop (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    ∃ n : ℕ, P n ∧ x < (n : ℝ) ∧ (n : ℝ) ≤ (1 + ε) * x

namespace MultiplicativelyDenseAtTop

variable {P : ℕ → Prop} (hP : MultiplicativelyDenseAtTop P)

include hP

theorem infinite : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨x, hx, hN⟩ := ((hP 1 (by norm_num)).and (eventually_ge_atTop (N : ℝ))).exists
  obtain ⟨n, hn, hxn, -⟩ := hx
  exact ⟨n, hn, by exact_mod_cast hN.trans_lt hxn⟩

/-- Deleting any bounded set of parameters preserves multiplicative density. -/
theorem above (N : ℕ) : MultiplicativelyDenseAtTop (fun n => P n ∧ N < n) := by
  intro ε hε
  filter_upwards [hP ε hε, eventually_ge_atTop (N : ℝ)] with x hx hN
  obtain ⟨n, hn, hxn, hbound⟩ := hx
  exact ⟨n, ⟨hn, by exact_mod_cast hN.trans_lt hxn⟩, hxn, hbound⟩

theorem nth_strictMono : StrictMono (Nat.nth P) := Nat.nth_strictMono hP.infinite

theorem nth_mem (n : ℕ) : P (Nat.nth P n) := Nat.nth_mem_of_infinite hP.infinite n

theorem nth_tendsto : Tendsto (fun n => (Nat.nth P n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp hP.nth_strictMono.tendsto_atTop

/-- The next enumerated element is no larger than any later admissible witness
in a short multiplicative interval. -/
theorem eventually_nth_succ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (Nat.nth P (n + 1) : ℝ) ≤ (1 + ε) * (Nat.nth P n : ℝ) := by
  filter_upwards [hP.nth_tendsto.eventually (hP ε hε)] with n hn
  obtain ⟨k, hk, hnk, hbound⟩ := hn
  have hnext : Nat.nth P (n + 1) ≤ k := by
    by_contra h
    have hle := Nat.le_nth_of_lt_nth_succ (lt_of_not_ge h) hk
    have hle' : (k : ℝ) ≤ (Nat.nth P n : ℝ) := by exact_mod_cast hle
    exact (not_lt_of_ge hle') hnk
  exact (show (Nat.nth P (n + 1) : ℝ) ≤ k by exact_mod_cast hnext).trans hbound

/-- Consecutive terms of the actual increasing enumeration are asymptotically
equal. No independently supplied ratio assumption is used. -/
theorem nth_ratio_tendsto :
    Tendsto (fun n => (Nat.nth P (n + 1) : ℝ) / (Nat.nth P n : ℝ)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hP.eventually_nth_succ_le (show 0 < ε / 2 by linarith),
    hP.nth_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hpos
  have hmono : (Nat.nth P n : ℝ) ≤ (Nat.nth P (n + 1) : ℝ) := by
    exact_mod_cast hP.nth_strictMono.monotone (Nat.le_succ n)
  have hlo : 1 ≤ (Nat.nth P (n + 1) : ℝ) / (Nat.nth P n : ℝ) :=
    (le_div_iff₀ hpos).mpr (by simpa using hmono)
  have hhi : (Nat.nth P (n + 1) : ℝ) / (Nat.nth P n : ℝ) ≤ 1 + ε / 2 :=
    (div_le_iff₀ hpos).mpr hn
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

/-- A strictly increasing smooth sequence can be chosen above any prescribed
finite threshold, with every parameter still satisfying `P`. -/
theorem exists_sequence_above (N : ℕ) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, P (q n) ∧ N < q n) ∧
      Tendsto (fun n => (q n : ℝ)) atTop atTop ∧
      Tendsto (fun n => (q (n + 1) : ℝ) / (q n : ℝ)) atTop (𝓝 1) :=
  ⟨Nat.nth (fun n => P n ∧ N < n), (hP.above N).nth_strictMono,
    (hP.above N).nth_mem, (hP.above N).nth_tendsto, (hP.above N).nth_ratio_tendsto⟩

end MultiplicativelyDenseAtTop

/-- Every nonzero polynomial preserves consecutive-ratio smoothness along a
sequence tending to infinity. Constants other than zero are allowed. -/
theorem polynomial_ratio_tendsto {q : ℕ → ℝ}
    (hq : Tendsto q atTop atTop)
    (hratio : Tendsto (fun n => q (n + 1) / q n) atTop (𝓝 1))
    (P : ℝ[X]) (hP : P ≠ 0) :
    Tendsto (fun n => P.eval (q (n + 1)) / P.eval (q n)) atTop (𝓝 1) := by
  have hnext := hq.comp (tendsto_add_atTop_nat 1)
  have heq := (P.isEquivalent_atTop_lead.comp_tendsto hnext).div
    (P.isEquivalent_atTop_lead.comp_tendsto hq)
  apply heq.symm.tendsto_nhds
  have hc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  change Tendsto (fun n => (P.leadingCoeff * q (n + 1) ^ P.natDegree) /
    (P.leadingCoeff * q n ^ P.natDegree)) atTop (𝓝 1)
  simpa only [mul_div_mul_left _ _ hc,
    ← div_pow, one_pow] using hratio.pow P.natDegree

/-- The natural cubic expression for the order of PSL(2,q) over odd fields.
No group-order theorem is asserted by this arithmetic definition. -/
def pslOrder (q : ℕ) : ℕ := q * (q - 1) * (q + 1) / 2

theorem pslOrder_eq_standard (q : ℕ) : pslOrder q = q * (q ^ 2 - 1) / 2 := by
  unfold pslOrder
  congr 1
  cases q with
  | zero => simp
  | succ q =>
      simp only [Nat.add_sub_cancel]
      rw [show (q + 1) ^ 2 = q * (q + 2) + 1 by ring, Nat.add_sub_cancel]
      ring

/-- Division by two is exact because two consecutive factors have even product. -/
theorem pslOrder_cast (q : ℕ) :
    (pslOrder q : ℝ) = (q : ℝ) * ((q : ℝ) ^ 2 - 1) / 2 := by
  by_cases hq : q = 0
  · subst q
    norm_num [pslOrder]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
  unfold pslOrder
  rw [Nat.cast_div (dvd_mul_of_dvd_left (Nat.two_dvd_mul_sub_one q) (q + 1)) (by norm_num)]
  push_cast [Nat.cast_sub hq1]
  ring

/-- The cubic order is strictly increasing once its parameter is at least one. -/
theorem pslOrder_strictMonoOn : StrictMonoOn pslOrder (Set.Ici 1) := by
  intro q hq r hr hqr
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqr' : (q : ℝ) < r := by exact_mod_cast hqr
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hcoef : 0 < (r : ℝ) ^ 2 + (r : ℝ) * q + (q : ℝ) ^ 2 - 1 := by
    nlinarith [sq_nonneg (r : ℝ), sq_nonneg ((q : ℝ) - 1),
      mul_nonneg hr0 (Nat.cast_nonneg q)]
  have hprod := mul_pos (sub_pos.mpr hqr') hcoef
  have hcast : (pslOrder q : ℝ) < pslOrder r := by
    rw [pslOrder_cast, pslOrder_cast]
    nlinarith only [hprod]
  exact_mod_cast hcast

theorem pslOrder_pos {q : ℕ} (hq : 2 ≤ q) : 0 < pslOrder q := by
  have h := pslOrder_strictMonoOn (by simp : 1 ∈ Set.Ici (1 : ℕ))
    (show q ∈ Set.Ici (1 : ℕ) from show 1 ≤ q by omega) (show 1 < q by omega)
  simpa [pslOrder] using h

theorem pslOrder_strictMono {q : ℕ → ℕ} (hq : StrictMono q) (hpos : ∀ n, 1 ≤ q n) :
    StrictMono (fun n => pslOrder (q n)) :=
  fun i j hij => pslOrder_strictMonoOn (hpos i) (hpos j) (hq hij)

theorem pslOrder_tendsto {q : ℕ → ℕ} (hq : StrictMono q) (hpos : ∀ n, 1 ≤ q n) :
    Tendsto (fun n => (pslOrder (q n) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (pslOrder_strictMono hq hpos).tendsto_atTop

/-- The PSL2-style natural orders inherit ratio one from their parameters. -/
theorem pslOrder_ratio_tendsto {q : ℕ → ℕ}
    (hq : Tendsto (fun n => (q n : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (q (n + 1) : ℝ) / (q n : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n => (pslOrder (q (n + 1)) : ℝ) / (pslOrder (q n) : ℝ))
      atTop (𝓝 1) := by
  let P : ℝ[X] := Polynomial.C (1 / 2) * (Polynomial.X ^ 3 - Polynomial.X)
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun Q : ℝ[X] => Q.coeff 3) h
    norm_num [P, Polynomial.coeff_C_mul, Polynomial.coeff_X] at hc
  have heval (n : ℕ) : P.eval (q n : ℝ) = (pslOrder (q n) : ℝ) := by
    rw [pslOrder_cast]
    simp only [P, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  simpa only [heval] using polynomial_ratio_tendsto hq hratio P hP

end

end IntervalsTuran.Spectral
