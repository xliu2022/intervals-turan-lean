module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic

/-!
# Smooth decreasing subsequences

The record-minimum argument below replaces the tail-supremum construction in
Lemma 3.8 of Liu--Pikhurko, *Intervals of hypergraph Turán densities*.
The main statement is purely analytic: a positive null sequence whose adjacent
ratios tend to one has a strictly decreasing subsequence with the same property.

Author and maintainer: Xizhi Liu.
-/

public section

open Filter
open scoped Topology

namespace IntervalsTuran

/-- A positive null sequence with asymptotically equal adjacent terms admits a
strictly decreasing subsequence whose adjacent terms are still asymptotically
equal. The subsequence consists of successive new record minima. -/
theorem exists_smooth_strictAnti_subsequence
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n)
    (ha_zero : Tendsto a atTop (𝓝 0))
    (ha_ratio : Tendsto (fun n => a n / a (n + 1)) atTop (𝓝 1)) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ StrictAnti (a ∘ j) ∧
      Tendsto (fun n => a (j n) / a (j (n + 1))) atTop (𝓝 1) := by
  classical
  have hex (n : ℕ) : ∃ m : ℕ, n < m ∧ a m < a n := by
    have he : ∀ᶠ m in atTop, a m < a n :=
      ha_zero.eventually (gt_mem_nhds (ha_pos n))
    obtain ⟨m, hm, hmn⟩ := (he.and (eventually_gt_atTop n)).exists
    exact ⟨m, hmn, hm⟩
  let next (n : ℕ) : ℕ := Nat.find (hex n)
  have hnext (n : ℕ) : n < next n ∧ a (next n) < a n :=
    Nat.find_spec (hex n)
  have hprevious (n : ℕ) : a n ≤ a (next n - 1) := by
    have hn := (hnext n).1
    by_cases heq : next n - 1 = n
    · rw [heq]
    · have hlt : n < next n - 1 := by omega
      have hprev : next n - 1 < next n := by omega
      exact le_of_not_gt fun h => Nat.find_min (hex n) hprev ⟨hlt, h⟩
  let j : ℕ → ℕ := fun n => next^[n] 0
  have hjstep (n : ℕ) : j (n + 1) = next (j n) :=
    Function.iterate_succ_apply' next n 0
  have hjmono : StrictMono j := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hjstep]
    exact (hnext (j n)).1
  have hjanti : StrictAnti (a ∘ j) := by
    apply strictAnti_nat_of_succ_lt
    intro n
    change a (j (n + 1)) < a (j n)
    rw [hjstep]
    exact (hnext (j n)).2
  have hjpred : Tendsto (fun n => j (n + 1) - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp
      (hjmono.tendsto_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : Tendsto (fun n => a (j (n + 1) - 1) / a (j (n + 1)))
      atTop (𝓝 1) := by
    have h := ha_ratio.comp hjpred
    convert h using 1
    ext n
    have hjpos : 1 ≤ j (n + 1) := by
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt (Nat.zero_le (j n)) (hjmono (Nat.lt_succ_self n)))
    simp only [Function.comp_apply, Nat.sub_add_cancel hjpos]
  refine ⟨j, hjmono, hjanti, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    exact (one_le_div (ha_pos (j (n + 1)))).2
      (le_of_lt (hjanti (Nat.lt_succ_self n)))
  · intro n
    apply div_le_div_of_nonneg_right _ (le_of_lt (ha_pos (j (n + 1))))
    rw [hjstep]
    exact hprevious (j n)

/-- The record-minimum conclusion also holds when positivity starts only after
a finite initial segment. The extracted terms are all positive. -/
theorem exists_smooth_strictAnti_subsequence_of_eventually_pos
    {a : ℕ → ℝ} (ha_pos : ∀ᶠ n in atTop, 0 < a n)
    (ha_zero : Tendsto a atTop (𝓝 0))
    (ha_ratio : Tendsto (fun n => a n / a (n + 1)) atTop (𝓝 1)) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ StrictAnti (a ∘ j) ∧
      (∀ n, 0 < a (j n)) ∧
      Tendsto (fun n => a (j n) / a (j (n + 1))) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha_pos
  let b : ℕ → ℝ := fun n => a (n + N)
  have hb_pos (n : ℕ) : 0 < b n := hN (n + N) (by omega)
  have hb_zero : Tendsto b atTop (𝓝 0) :=
    ha_zero.comp (tendsto_add_atTop_nat N)
  have hb_ratio : Tendsto (fun n => b n / b (n + 1)) atTop (𝓝 1) := by
    simpa only [b, Function.comp_def, Nat.add_right_comm] using
      ha_ratio.comp (tendsto_add_atTop_nat N)
  obtain ⟨j, hjmono, hjanti, hjratio⟩ :=
    exists_smooth_strictAnti_subsequence hb_pos hb_zero hb_ratio
  refine ⟨fun n => j n + N, ?_, ?_, ?_, ?_⟩
  · intro i k hik
    exact Nat.add_lt_add_right (hjmono hik) N
  · simpa only [Function.comp_def, b] using hjanti
  · exact fun n => hb_pos (j n)
  · simpa only [b] using hjratio

/-- A version of the smooth extraction lemma adapted to first-order
asymptotics. If `m n * a n → c > 0`, the positive scales `m n` diverge, and
their successive ratios tend to one, then a strictly decreasing subsequence of
`a` can be chosen so that both selected `a`-ratios and scale ratios tend to one.
No monotonicity assumption on the original scale sequence is needed. -/
theorem exists_smooth_strictAnti_subsequence_of_scaled_limit
    {a m : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hm_pos : ∀ n, 0 < m n) (hm_top : Tendsto m atTop atTop)
    (hma : Tendsto (fun n => m n * a n) atTop (𝓝 c))
    (hm_ratio : Tendsto (fun n => m (n + 1) / m n) atTop (𝓝 1)) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ StrictAnti (a ∘ j) ∧
      Tendsto (fun n => a (j n) / a (j (n + 1))) atTop (𝓝 1) ∧
      Tendsto (fun n => m (j (n + 1)) / m (j n)) atTop (𝓝 1) := by
  have ha_pos : ∀ᶠ n in atTop, 0 < a n := by
    filter_upwards [hma.eventually (lt_mem_nhds hc)] with n hn
    exact (mul_pos_iff_of_pos_left (hm_pos n)).mp hn
  have ha_zero : Tendsto a atTop (𝓝 0) := by
    convert hma.div_atTop hm_top using 1
    ext n
    field_simp [ne_of_gt (hm_pos n)]
  have hma_next : Tendsto (fun n => m (n + 1) * a (n + 1)) atTop (𝓝 c) :=
    hma.comp (tendsto_add_atTop_nat 1)
  have hraw : Tendsto
      (fun n => ((m n * a n) / (m (n + 1) * a (n + 1))) *
        (m (n + 1) / m n)) atTop (𝓝 1) := by
    simpa only [Pi.div_apply, div_self (ne_of_gt hc), one_mul] using
      (hma.div hma_next (ne_of_gt hc)).mul hm_ratio
  have ha_ratio : Tendsto (fun n => a n / a (n + 1)) atTop (𝓝 1) := by
    apply Tendsto.congr' (h := hraw)
    filter_upwards [(tendsto_add_atTop_nat 1).eventually ha_pos] with n hn
    field_simp [ne_of_gt (hm_pos n), ne_of_gt (hm_pos (n + 1)), ne_of_gt hn]
  obtain ⟨j, hjmono, hjanti, hjpos, hjratio⟩ :=
    exists_smooth_strictAnti_subsequence_of_eventually_pos ha_pos ha_zero ha_ratio
  have hp : Tendsto (fun n => m (j n) * a (j n)) atTop (𝓝 c) :=
    hma.comp hjmono.tendsto_atTop
  have hp_next : Tendsto (fun n => m (j (n + 1)) * a (j (n + 1)))
      atTop (𝓝 c) := hp.comp (tendsto_add_atTop_nat 1)
  have hselected : Tendsto
      (fun n => (a (j n) / a (j (n + 1))) *
        ((m (j (n + 1)) * a (j (n + 1))) / (m (j n) * a (j n))))
      atTop (𝓝 1) := by
    simpa only [Pi.div_apply, div_self (ne_of_gt hc), mul_one] using
      hjratio.mul (hp_next.div hp (ne_of_gt hc))
  refine ⟨j, hjmono, hjanti, hjratio, ?_⟩
  apply Tendsto.congr' (h := hselected)
  exact Eventually.of_forall fun n => by
    field_simp [ne_of_gt (hm_pos (j n)), ne_of_gt (hm_pos (j (n + 1))),
      ne_of_gt (hjpos n), ne_of_gt (hjpos (n + 1))]

end IntervalsTuran
