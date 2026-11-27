module

public import IntervalsTuran.MainStatement
public import IntervalsTuran.Construction.CompleteJoinClosure
public import IntervalsTuran.Construction.SpectralInterval
public import IntervalsTuran.Turan.TerminalReduction
public import IntervalsTuran.Construction.WeakBaseParameters
public import IntervalsTuran.Construction.WeakOuterSequence

/-!
# The unconditional terminal-interval theorem

Author and maintainer: Xizhi Liu.
Source theorem: Xizhi Liu and Oleg Pikhurko, arXiv:2605.25914v1, Theorem 1.1.

The final `main_theorem` has no spectral-existence hypothesis. Its finite
graph sequence uses the imported MGG spectral theorem, an actual simple
finite-field lift, and the additive tripartite gadget. Recursive interval
filling, suspension and complete-join amplification then give Theorem 1.1.

The earlier Cayley-based implications remain available as separate results.
They retain their explicit hypotheses; the unconditional proof uses the
alternative simple bipartite construction and does not assert an LPS theorem.
-/

@[expose] public section

namespace IntervalsTuran

/-- Balanced complete joins of increasingly many isolated vertices realize the
spectral base value from below. The decreasing spectral sequence is not used
to justify this lower approximation. -/
theorem belowLagrangianApprox_limitValue :
    BelowLagrangianApprox 3 Spectral.limitValue := by
  have h := (belowLagrangianApprox_zero 3).completeJoin (by omega) 30 (by omega)
  convert h using 1 <;> norm_num [Spectral.limitValue]

/-- Actual complete-join closure discharges the numerical amplification
hypothesis; the interval supplied here is an interval of finite-graph limits. -/
theorem terminalIntervalClaim_of_below_lagrangian_interval
    {r : ℕ} (hr : 2 ≤ r) {a b : ℝ} (hab : a < b)
    (hI : Set.Icc a b ⊆ {x | BelowLagrangianApprox r x}) :
    TerminalIntervalClaim r :=
  terminalIntervalClaim_of_join_preserves_below hr
    (fun M hM _ hx => hx.completeJoin (by omega) M (by omega)) hab hI

/-- The whole terminal-interval conclusion follows from the precise smooth
Cayley spectral-family input. This argument is intentionally explicit. -/
theorem main_theorem_of_smooth_spectral_family (F : Spectral.SmoothSpectralFamily) :
    MainTheoremStatement := by
  obtain ⟨v, hv, hI⟩ := F.exists_below_lagrangian_interval belowLagrangianApprox_limitValue
  exact mainTheoremStatement_of_three_interval_and_join_preserves_below
    (fun _ hr M hM _ hx => hx.completeJoin (by omega) M (by omega)) hv hI

/-- An equivalent entry point displaying the one unresolved existence
proposition as a premise. No proof of this premise is supplied by the library. -/
theorem main_theorem_of_spectral_existence
    (hF : Nonempty Spectral.SmoothSpectralFamily) : MainTheoremStatement :=
  hF.elim main_theorem_of_smooth_spectral_family

/-- Expand every spectrum occurrence to the actual ordinary density of an
explicitly quantified forbidden family. The spectral-family input remains
visible in the theorem type. -/
theorem ordinary_density_terminal_interval_of_smooth_spectral_family
    (F : Spectral.SmoothSpectralFamily) :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ forbidden : Set (FiniteGraph r), SetFamily.turanDensity forbidden = x := by
  intro r hr
  exact (terminalIntervalClaim_iff r).mp (main_theorem_of_smooth_spectral_family F r hr)

/-- A nondegenerate interval realized by actual finite-graph limits. This
statement uses the explicit MGG-based sequence and has no spectral premise. -/
theorem exists_three_below_lagrangian_interval :
    ∃ a b : ℝ, a < b ∧ Set.Icc a b ⊆ {x | BelowLagrangianApprox 3 x} := by
  obtain ⟨v, hv, hI⟩ := Construction.weakBase_exists_interval_of_smooth_finite_lagrangians
    Spectral.SimpleExpander.k Spectral.SimpleExpander.four_le_k
    Spectral.SimpleExpander.outerSequence
    Spectral.SimpleExpander.baseValue_lt_outerSequence
    Spectral.SimpleExpander.outerSequence_strictAnti.antitone
    Spectral.SimpleExpander.outerSequence_tendsto
    Spectral.SimpleExpander.outerSequence_gap_ratio_tendsto
  exact ⟨_, v, hv, hI⟩

/-- Liu--Pikhurko, Theorem 1.1: the ordinary Turan spectrum has a terminal
interval in every uniformity at least three. No unproved premise is present. -/
theorem main_theorem : MainTheoremStatement := by
  obtain ⟨a, b, hab, hI⟩ := exists_three_below_lagrangian_interval
  exact mainTheoremStatement_of_three_interval_and_join_preserves_below
    (fun _ hr M hM _ hx => hx.completeJoin (by omega) M (by omega)) hab hI

/-- The unconditional main theorem expanded to ordinary forbidden-family
densities, making both the quantifiers and the intended density visible. -/
theorem ordinary_density_terminal_interval :
    ∀ r : ℕ, 3 ≤ r → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
        ∃ forbidden : Set (FiniteGraph r), SetFamily.turanDensity forbidden = x := by
  intro r hr
  exact (terminalIntervalClaim_iff r).mp (main_theorem r hr)

end IntervalsTuran
