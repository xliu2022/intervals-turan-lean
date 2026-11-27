module

public import IntervalsTuran.Spectral.SmoothOrders
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Prime parameters and the precise prime-distribution input

Author and maintainer: Xizhi Liu.

Dirichlet's theorem in the pinned mathlib produces actual strictly increasing
prime parameters in every reduced arithmetic progression. A separate,
explicit weighted prime-counting limit implies multiplicative density and
then smoothness of the parameters and the natural PSL2-style orders.

The weighted prime-counting limit is not proved or postulated as an axiom
here. Its statement matches the corresponding theorem in newer upstream
`Mathlib.NumberTheory.LSeries.WeakPNT`, absent from this project's fixed pin.
-/

@[expose] public section

namespace IntervalsTuran.Spectral

open Set Filter
open scoped Topology BigOperators

noncomputable section

/-- Weighted counting up to a real endpoint, restricted to positive integers
satisfying the predicate. -/
def weightedCounting (P : ℕ → Prop) (w : ℕ → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter P, w n

/-- A strict increase of the weighted sum forces an admissible parameter in
the intervening interval. No sign assumption on the weights is needed. -/
theorem exists_mem_Ioc_of_weightedCounting_lt {P : ℕ → Prop} {w : ℕ → ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hcount : weightedCounting P w a < weightedCounting P w b) :
    ∃ n : ℕ, P n ∧ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  classical
  by_contra h
  have heq : (Finset.Ioc 0 ⌊a⌋₊).filter P = (Finset.Ioc 0 ⌊b⌋₊).filter P := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h0, hna⟩, hn⟩
      exact ⟨⟨h0, hna.trans (Nat.floor_mono hab)⟩, hn⟩
    · rintro ⟨⟨h0, hnb⟩, hn⟩
      have hnb' : (n : ℝ) ≤ b := (Nat.le_floor_iff (ha.trans hab)).mp hnb
      have hna' : (n : ℝ) ≤ a := by
        by_contra hna
        exact h ⟨n, hn, lt_of_not_ge hna, hnb'⟩
      exact ⟨⟨h0, Nat.le_floor hna'⟩, hn⟩
  unfold weightedCounting at hcount
  rw [heq] at hcount
  exact (lt_irrefl _) hcount

/-- A positive linear asymptotic for a weighted counting function supplies
all fixed multiplicative short intervals, and hence the smooth enumeration
proved in `SmoothOrders`. -/
theorem multiplicativelyDenseAtTop_of_weightedCounting_limit
    {P : ℕ → Prop} {w : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun x : ℝ => weightedCounting P w x / x) atTop (𝓝 c)) :
    MultiplicativelyDenseAtTop P := by
  intro ε hε
  have hs : 0 < 1 + ε := by linarith
  have hscaled := hlim.comp (tendsto_id.const_mul_atTop hs)
  have hscaled' : Tendsto (fun x : ℝ => weightedCounting P w ((1 + ε) * x) / x)
      atTop (𝓝 (c * (1 + ε))) := by
    apply (hscaled.mul_const (1 + ε)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp only [Function.comp_apply, id_eq]
    field_simp [ne_of_gt hx, ne_of_gt hs]
  have hdiff : Tendsto (fun x : ℝ =>
      (weightedCounting P w ((1 + ε) * x) - weightedCounting P w x) / x)
      atTop (𝓝 (c * (1 + ε) - c)) := by
    simpa only [sub_div] using hscaled'.sub hlim
  have hpos : 0 < c * (1 + ε) - c := by nlinarith
  filter_upwards [hdiff.eventually (eventually_gt_nhds hpos),
    eventually_gt_atTop (0 : ℝ)] with x hdiffx hx
  have hcount : weightedCounting P w x < weightedCounting P w ((1 + ε) * x) := by
    exact sub_pos.mp ((div_pos_iff_of_pos_right hx).mp hdiffx)
  exact exists_mem_Ioc_of_weightedCounting_lt hx.le (by nlinarith) hcount

/-- The ordinary prime predicate with a prescribed congruence condition. -/
def primeInProgression (modulus residue n : ℕ) : Prop :=
  n.Prime ∧ n ≡ residue [MOD modulus]

/-- The actual increasing enumeration, after discarding all parameters at or
below a specified threshold. -/
def primeParameters (modulus residue threshold : ℕ) : ℕ → ℕ :=
  Nat.nth (fun n => primeInProgression modulus residue n ∧ threshold < n)

/-- This infinitude proof uses the actual Dirichlet theorem already present
in the fixed mathlib, not an additional prime-distribution hypothesis. -/
theorem infinite_primeParameters {modulus residue : ℕ}
    (hm : modulus ≠ 0) (ha : residue.Coprime modulus) (threshold : ℕ) :
    (Set.ofPred (fun n => primeInProgression modulus residue n ∧ threshold < n)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N threshold) hm ha
  exact ⟨p, ⟨⟨hprime, hmod⟩, (le_max_right N threshold).trans_lt hp⟩,
    (le_max_left N threshold).trans_lt hp⟩

theorem primeParameters_spec {modulus residue : ℕ}
    (hm : modulus ≠ 0) (ha : residue.Coprime modulus) (threshold n : ℕ) :
    primeInProgression modulus residue (primeParameters modulus residue threshold n) ∧
      threshold < primeParameters modulus residue threshold n :=
  Nat.nth_mem_of_infinite (infinite_primeParameters hm ha threshold) n

theorem primeParameters_strictMono {modulus residue : ℕ}
    (hm : modulus ≠ 0) (ha : residue.Coprime modulus) (threshold : ℕ) :
    StrictMono (primeParameters modulus residue threshold) :=
  Nat.nth_strictMono (infinite_primeParameters hm ha threshold)

theorem primeParameters_two_le {modulus residue : ℕ}
    (hm : modulus ≠ 0) (ha : residue.Coprime modulus) (threshold n : ℕ) :
    2 ≤ primeParameters modulus residue threshold n :=
  (primeParameters_spec hm ha threshold n).1.1.two_le

theorem primeParameters_tendsto {modulus residue : ℕ}
    (hm : modulus ≠ 0) (ha : residue.Coprime modulus) (threshold : ℕ) :
    Tendsto (fun n => (primeParameters modulus residue threshold n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (primeParameters_strictMono hm ha threshold).tendsto_atTop

/-- The stronger density input is used precisely here, to pass from an
increasing unbounded prime enumeration to consecutive ratio one. -/
theorem primeParameters_ratio_tendsto {modulus residue : ℕ}
    (hdense : MultiplicativelyDenseAtTop (primeInProgression modulus residue))
    (threshold : ℕ) :
    Tendsto (fun n => (primeParameters modulus residue threshold (n + 1) : ℝ) /
      (primeParameters modulus residue threshold n : ℝ)) atTop (𝓝 1) :=
  (hdense.above threshold).nth_ratio_tendsto

/-- The weighted prime sum used in the theta form of PNT in progressions. -/
def primeProgressionLogSum (modulus residue : ℕ) (x : ℝ) : ℝ :=
  weightedCounting (primeInProgression modulus residue) (fun n => Real.log n) x

/-- Direct interface to the arithmetic-progression theta theorem. The limit
remains an explicit hypothesis until that theorem is imported and checked. -/
theorem multiplicativelyDense_primeProgression_of_logSum_limit
    {modulus residue : ℕ} (hm : modulus ≠ 0)
    (hPNT : Tendsto (fun x : ℝ => primeProgressionLogSum modulus residue x / x)
      atTop (𝓝 (Nat.totient modulus : ℝ)⁻¹)) :
    MultiplicativelyDenseAtTop (primeInProgression modulus residue) := by
  have hc : (0 : ℝ) < (Nat.totient modulus : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  exact multiplicativelyDenseAtTop_of_weightedCounting_limit (inv_pos.mpr hc) hPNT

/-- A concrete progression suitable for the fixed arithmetic parameter
`p = 137`: every chosen prime is greater than 137 and is 1 modulo 4·137. -/
def lpsPrimeSequence : ℕ → ℕ := primeParameters 548 1 137

theorem lpsPrimeSequence_prime (n : ℕ) : (lpsPrimeSequence n).Prime :=
  (primeParameters_spec (by norm_num : (548 : ℕ) ≠ 0) (by norm_num : Nat.Coprime 1 548)
    137 n).1.1

theorem lpsPrimeSequence_gt (n : ℕ) : 137 < lpsPrimeSequence n :=
  (primeParameters_spec (by norm_num : (548 : ℕ) ≠ 0) (by norm_num : Nat.Coprime 1 548)
    137 n).2

theorem lpsPrimeSequence_modEq (n : ℕ) : lpsPrimeSequence n ≡ 1 [MOD 548] :=
  (primeParameters_spec (by norm_num : (548 : ℕ) ≠ 0) (by norm_num : Nat.Coprime 1 548)
    137 n).1.2

theorem lpsPrimeSequence_mod_four (n : ℕ) : lpsPrimeSequence n ≡ 1 [MOD 4] :=
  Nat.ModEq.of_dvd (by norm_num : 4 ∣ 548) (lpsPrimeSequence_modEq n)

theorem lpsPrimeSequence_mod_137 (n : ℕ) : lpsPrimeSequence n ≡ 1 [MOD 137] :=
  Nat.ModEq.of_dvd (by norm_num : 137 ∣ 548) (lpsPrimeSequence_modEq n)

theorem lpsPrimeSequence_strictMono : StrictMono lpsPrimeSequence :=
  primeParameters_strictMono (by norm_num) (by norm_num) 137

theorem lpsPrimeSequence_tendsto :
    Tendsto (fun n => (lpsPrimeSequence n : ℝ)) atTop atTop :=
  primeParameters_tendsto (by norm_num) (by norm_num) 137

theorem lpsPrimeSequence_ratio_tendsto
    (hPNT : Tendsto (fun x : ℝ => primeProgressionLogSum 548 1 x / x)
      atTop (𝓝 (Nat.totient 548 : ℝ)⁻¹)) :
    Tendsto (fun n => (lpsPrimeSequence (n + 1) : ℝ) / (lpsPrimeSequence n : ℝ))
      atTop (𝓝 1) :=
  primeParameters_ratio_tendsto
    (multiplicativelyDense_primeProgression_of_logSum_limit (by norm_num) hPNT) 137

/-- The exact natural cubic orders, before any graph or group construction is
identified with them. -/
def lpsOrderSequence (n : ℕ) : ℕ := pslOrder (lpsPrimeSequence n)

theorem lpsOrderSequence_pos (n : ℕ) : 0 < lpsOrderSequence n :=
  pslOrder_pos (lpsPrimeSequence_prime n).two_le

theorem lpsOrderSequence_strictMono : StrictMono lpsOrderSequence :=
  pslOrder_strictMono lpsPrimeSequence_strictMono (fun n => (lpsPrimeSequence_prime n).pos)

theorem lpsOrderSequence_tendsto :
    Tendsto (fun n => (lpsOrderSequence n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp lpsOrderSequence_strictMono.tendsto_atTop

theorem lpsOrderSequence_ratio_tendsto
    (hPNT : Tendsto (fun x : ℝ => primeProgressionLogSum 548 1 x / x)
      atTop (𝓝 (Nat.totient 548 : ℝ)⁻¹)) :
    Tendsto (fun n => (lpsOrderSequence (n + 1) : ℝ) / (lpsOrderSequence n : ℝ))
      atTop (𝓝 1) :=
  pslOrder_ratio_tendsto lpsPrimeSequence_tendsto (lpsPrimeSequence_ratio_tendsto hPNT)

end

end IntervalsTuran.Spectral
