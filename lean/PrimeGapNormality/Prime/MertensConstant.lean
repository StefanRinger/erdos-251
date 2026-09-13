import PrimeGapNormality.Prime.MertensSecond
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Identification of the Mertens-II constant

This file closes two inputs to the constant identification:

* `log ζ(s) + log (s - 1) → 0` as `s → 1+`;
* dominated convergence of the prime-power correction in the logarithmic
  Euler product.

The remaining Abelian bridge from the already proved discrete Mertens-II
limit to the prime Dirichlet series is stated precisely at the end, but is
not introduced as an assumption.
-/

namespace PrimeGapNormality.Prime

open Filter Finset Set

noncomputable section

/-- Prime Dirichlet series, extended by zero away from primes. -/
def mertensPrimeDirichlet (s : ℝ) : ℝ :=
  ∑' n : ℕ, if n.Prime then (n : ℝ) ^ (-s) else 0

/-- The prime-power correction in the logarithmic Euler product at real
parameter `s`. -/
def mertensPrimeCorrectionDirichletTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then
    -Real.log (1 - (n : ℝ) ^ (-s)) - (n : ℝ) ^ (-s)
  else 0

def mertensPrimeCorrectionDirichlet (s : ℝ) : ℝ :=
  ∑' n : ℕ, mertensPrimeCorrectionDirichletTerm s n

/-- Mathlib's zeta asymptotic in the exact real right-limit form needed for
Mertens' constant. -/
theorem tendsto_log_riemannZeta_add_log_sub_one :
    Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  exact
    log_riemannZeta_add_log_sub_isLittleO_ofReal.tendsto_zero_of_tendsto
      tendsto_const_nhds

private theorem correction_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) - x := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

private theorem correction_le_two_sq {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have hx1 : x < 1 := hxhalf.trans_lt (by norm_num)
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hneglog : -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := by
    linarith
  have hstep :
      -Real.log (1 - x) - x ≤ ((1 - x)⁻¹ - 1) - x :=
    sub_le_sub_right hneglog x
  have hid : ((1 - x)⁻¹ - 1) - x = x ^ 2 / (1 - x) := by
    field_simp [ne_of_gt hpos]
    ring
  have hfrac : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  rw [hid] at hstep
  exact hstep.trans hfrac

private theorem prime_rpow_neg_le_half {n : ℕ} (hn : n.Prime)
    {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ (n : ℝ) ^ (-s) ∧ (n : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hn1 : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn.one_lt
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hpow : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1.le (neg_le_neg hs)
  have hinv : (n : ℝ) ^ (-1 : ℝ) = (n : ℝ)⁻¹ :=
    Real.rpow_neg_one _
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
  have hinvhalf : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hn2
    simpa using h
  rw [hinv] at hpow
  exact ⟨Real.rpow_nonneg (Nat.cast_nonneg n) _, hpow.trans hinvhalf⟩

theorem mertensPrimeCorrectionDirichletTerm_nonneg {s : ℝ} (hs : 1 ≤ s)
    (n : ℕ) :
    0 ≤ mertensPrimeCorrectionDirichletTerm s n := by
  by_cases hn : n.Prime
  · rw [mertensPrimeCorrectionDirichletTerm, if_pos hn]
    obtain ⟨hx0, hxhalf⟩ := prime_rpow_neg_le_half hn hs
    exact correction_nonneg hx0 (hxhalf.trans_lt (by norm_num))
  · simp [mertensPrimeCorrectionDirichletTerm, hn]

theorem mertensPrimeCorrectionDirichletTerm_le {s : ℝ} (hs : 1 ≤ s)
    (n : ℕ) :
    mertensPrimeCorrectionDirichletTerm s n ≤
      2 * ((n : ℝ) ^ 2)⁻¹ := by
  by_cases hn : n.Prime
  · rw [mertensPrimeCorrectionDirichletTerm, if_pos hn]
    obtain ⟨hx0, hxhalf⟩ := prime_rpow_neg_le_half hn hs
    have hcorr := correction_le_two_sq hx0 hxhalf
    have hn1 : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn.one_lt
    have hpow : (n : ℝ) ^ (-s) ≤ (n : ℝ)⁻¹ := by
      calc
        (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1.le (neg_le_neg hs)
        _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
    have hsq : ((n : ℝ) ^ (-s)) ^ 2 ≤ ((n : ℝ)⁻¹) ^ 2 :=
      (sq_le_sq₀ hx0 (inv_nonneg.mpr (Nat.cast_nonneg n))).mpr hpow
    calc
      -Real.log (1 - (n : ℝ) ^ (-s)) - (n : ℝ) ^ (-s) ≤
          2 * ((n : ℝ) ^ (-s)) ^ 2 := hcorr
      _ ≤ 2 * ((n : ℝ)⁻¹) ^ 2 := by gcongr
      _ = 2 * ((n : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
  · simp [mertensPrimeCorrectionDirichletTerm, hn]

private theorem correctionTerm_tendsto (n : ℕ) :
    Tendsto (fun s : ℝ => mertensPrimeCorrectionDirichletTerm s n)
      (nhdsWithin 1 (Ioi 1)) (nhds (mertensPrimeCorrection n)) := by
  by_cases hn : n.Prime
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
    have hpow : Continuous (fun s : ℝ => (n : ℝ) ^ (-s)) :=
      (Real.continuous_const_rpow hn0).comp continuous_neg
    have harg : 1 - (n : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by
      rw [Real.rpow_neg_one]
      exact (one_sub_inv_pos hn).ne'
    have hcont : ContinuousAt
        (fun s : ℝ =>
          -Real.log (1 - (n : ℝ) ^ (-s)) - (n : ℝ) ^ (-s)) 1 :=
      ((continuousAt_const.sub hpow.continuousAt).log harg).neg.sub hpow.continuousAt
    simpa [mertensPrimeCorrectionDirichletTerm, mertensPrimeCorrection, hn,
      Real.rpow_neg_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · simp [mertensPrimeCorrectionDirichletTerm, mertensPrimeCorrection, hn]

/-- Dominated convergence of the prime-power correction at `s = 1+`. -/
theorem tendsto_mertensPrimeCorrectionDirichlet :
    Tendsto mertensPrimeCorrectionDirichlet (nhdsWithin 1 (Ioi 1))
      (nhds mertensPrimeCorrectionConstant) := by
  have hsum : Summable (fun n : ℕ => 2 * ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 2
  change Tendsto
    (fun s : ℝ => ∑' n : ℕ, mertensPrimeCorrectionDirichletTerm s n)
    (nhdsWithin 1 (Ioi 1))
    (nhds (∑' n : ℕ, mertensPrimeCorrection n))
  refine tendsto_tsum_of_dominated_convergence hsum correctionTerm_tendsto ?_
  filter_upwards [self_mem_nhdsWithin] with s hs n
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mertensPrimeCorrectionDirichletTerm_nonneg hs.le n)]
  exact mertensPrimeCorrectionDirichletTerm_le hs.le n

/-- The discrete Mertens-II limit has a unique value. -/
theorem exists_unique_mertensPrimeReciprocalLimit :
    ∃! B : ℝ, Tendsto
      (fun N : ℕ => mertensPrimeReciprocalSum N - Real.log (Real.log N))
      atTop (nhds B) := by
  obtain ⟨B, hB⟩ := exists_tendsto_mertensPrimeReciprocalSum_sub_log_log
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact tendsto_nhds_unique hC hB

/-! ### Real Euler-log series and the exact split into its two pieces -/

/-- The real logarithmic Euler-product summand, extended by zero away from
primes. -/
def mertensEulerLogTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then -Real.log (1 - (n : ℝ) ^ (-s)) else 0

theorem summable_mertensPrimeDirichletTerm {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => if n.Prime then (n : ℝ) ^ (-s) else 0) := by
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le ?_ ?_ hpow
  · intro n
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact le_rfl
  · intro n
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem summable_mertensPrimeCorrectionDirichletTerm {s : ℝ} (hs : 1 ≤ s) :
    Summable (mertensPrimeCorrectionDirichletTerm s) := by
  refine Summable.of_nonneg_of_le
    (mertensPrimeCorrectionDirichletTerm_nonneg hs)
    (mertensPrimeCorrectionDirichletTerm_le hs) ?_
  exact (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 2

private theorem prime_add_correctionTerm_eq {s : ℝ} (n : ℕ) :
    (if n.Prime then (n : ℝ) ^ (-s) else 0) +
        mertensPrimeCorrectionDirichletTerm s n =
      mertensEulerLogTerm s n := by
  by_cases hn : n.Prime
  · simp [mertensPrimeCorrectionDirichletTerm, mertensEulerLogTerm, hn]
  · simp [mertensPrimeCorrectionDirichletTerm, mertensEulerLogTerm, hn]

theorem summable_mertensEulerLogTerm {s : ℝ} (hs : 1 < s) :
    Summable (mertensEulerLogTerm s) := by
  have hp := summable_mertensPrimeDirichletTerm hs
  have hc := summable_mertensPrimeCorrectionDirichletTerm hs.le
  exact (hp.add hc).congr (prime_add_correctionTerm_eq (s := s))

/-- Exact splitting of the real Euler-log series into its prime term and
the dominated prime-power correction. -/
theorem mertensPrime_add_correction_eq_eulerLog {s : ℝ} (hs : 1 < s) :
    mertensPrimeDirichlet s + mertensPrimeCorrectionDirichlet s =
      ∑' n : ℕ, mertensEulerLogTerm s n := by
  have hp := summable_mertensPrimeDirichletTerm hs
  have hc := summable_mertensPrimeCorrectionDirichletTerm hs.le
  rw [mertensPrimeDirichlet, mertensPrimeCorrectionDirichlet,
    ← hp.tsum_add hc]
  exact tsum_congr (prime_add_correctionTerm_eq (s := s))

private theorem complexEulerLogTerm_eq_ofReal {s : ℝ} (hs : 1 < s)
    (p : Nat.Primes) :
    -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) =
      (mertensEulerLogTerm s p : ℂ) := by
  let x : ℝ := (p : ℝ) ^ (-s)
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr p.prop.one_lt
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hx1 : x < 1 := by
    dsimp [x]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos (zero_lt_one.trans hs))
  have hcpow : (p : ℂ) ^ (-(s : ℂ)) = (x : ℂ) := by
    simpa [x] using
      (Complex.ofReal_cpow (Nat.cast_nonneg p) (-s)).symm
  rw [hcpow]
  have hsub : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by
    norm_num
  rw [hsub, ← Complex.ofReal_log (sub_nonneg.mpr hx1.le)]
  simp [mertensEulerLogTerm, p.prop, x]

private theorem tsum_mertensEulerLog_eq_tsum_primes {s : ℝ} :
    (∑' n : ℕ, mertensEulerLogTerm s n) =
      ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) := by
  have hsupp : Function.support (mertensEulerLogTerm s) ⊆ {n : ℕ | n.Prime} := by
    intro n hn
    by_contra hnp
    have hnp' : ¬ n.Prime := by
      simpa only [Set.mem_setOf_eq] using hnp
    have hzero : mertensEulerLogTerm s n = 0 := by
      simp [mertensEulerLogTerm, hnp']
    exact hn hzero
  calc
    (∑' n : ℕ, mertensEulerLogTerm s n) =
        ∑' p : {n : ℕ // n.Prime}, mertensEulerLogTerm s p :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-s)) := by
      exact tsum_congr fun p => by simp [mertensEulerLogTerm, p.prop]

/-- Real zero-extended `ℕ` form of Mathlib's logarithmic Euler product. -/
theorem log_riemannZeta_eq_mertensEulerLog {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re =
      ∑' n : ℕ, mertensEulerLogTerm s n := by
  let R : ℝ := ∑' n : ℕ, mertensEulerLogTerm s n
  have hcomplex :
      (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))) =
        (R : ℂ) := by
    rw [show R = ∑' p : Nat.Primes,
        -Real.log (1 - (p : ℝ) ^ (-s)) by
      exact tsum_mertensEulerLog_eq_tsum_primes]
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun p => by
      simpa [mertensEulerLogTerm, p.property] using
        (complexEulerLogTerm_eq_ofReal hs p)
  have hz := riemannZeta_eulerProduct_exp_log
    (s := (s : ℂ)) (by simpa using hs)
  rw [hcomplex] at hz
  have hre : Real.exp R = (riemannZeta (s : ℂ)).re := by
    have := congrArg Complex.re hz
    simpa [← Complex.ofReal_exp] using this
  calc
    Real.log (riemannZeta (s : ℂ)).re = Real.log (Real.exp R) :=
      congrArg Real.log hre.symm
    _ = R := Real.log_exp R
    _ = ∑' n : ℕ, mertensEulerLogTerm s n := rfl

/-- Exact Euler decomposition into the prime Dirichlet series and the
prime-power correction. -/
theorem log_riemannZeta_eq_mertensPrime_add_correction {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re =
      mertensPrimeDirichlet s + mertensPrimeCorrectionDirichlet s := by
  rw [log_riemannZeta_eq_mertensEulerLog hs,
    ← mertensPrime_add_correction_eq_eulerLog hs]

/-
The remaining constant-identification lemma is the Abelian statement

  ∀ {B : ℝ},
    Tendsto
      (fun N : ℕ => mertensPrimeReciprocalSum N - log (log N))
      atTop (nhds B) →
    Tendsto
      (fun s : ℝ => mertensPrimeDirichlet s + log (s - 1))
      (nhdsWithin 1 (Ioi 1))
      (nhds (B - Real.eulerMascheroniConstant)).

Together with the Euler decomposition and the two proved limits above, it
identifies
`B = gamma - mertensPrimeCorrectionConstant`.  Neither missing statement is
introduced as a proposition or hypothesis in this file.
-/

end

end PrimeGapNormality.Prime
