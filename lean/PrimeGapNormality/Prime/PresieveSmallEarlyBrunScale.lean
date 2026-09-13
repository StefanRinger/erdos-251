import PrimeGapNormality.Prime.PresieveSmallEarlyBrunUniform
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Paper scale for the uniform early Brun estimate

This file supplies the hypothesis-free scale facts needed to apply
`earlyPresieve_survivorCount_abs_sub_main_le_brun` at the small paper
window.  The Brun rank is `floor (sqrt (log G))`; its harmonic envelope
is deliberately the elementary bound `1 + 4 log (max (log G) 1)`.

Both the normalized factorial tail and the CRT-rounding summand tend
to zero.  Consequently the early count has its main term uniformly in
every exposed residue choice.

No prime number theorem, AHL assumption, or Kuperberg assumption occurs.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-- Lean-friendly adjacent Brun rank at physical gap scale `G`. -/
def earlyBrunRank (G : ℝ) : ℕ :=
  ⌊Real.sqrt (Real.log G)⌋₊

/-- Elementary harmonic envelope at physical gap scale `G`. -/
def earlyBrunT (G : ℝ) : ℝ :=
  1 + 4 * Real.log (max (Real.log G) 1)

/-! ## Elementary harmonic bound -/

/-- The prime reciprocal sum is bounded by the full harmonic sum; this
is the public replacement for the private estimate previously buried in
the finite Brun file. -/
theorem earlyBrunHarmonic_primesLE_le_one_add_log (w : ℕ) :
    earlyBrunHarmonic (Nat.primesLE w) ≤ 1 + Real.log w := by
  have hsub : Nat.primesLE w ⊆ Icc 1 w := by
    intro p hp
    exact mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
  calc
    earlyBrunHarmonic (Nat.primesLE w)
        ≤ ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
        inv_nonneg.mpr (Nat.cast_nonneg n)
    _ = (harmonic w : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ ≤ 1 + Real.log w := harmonic_le_one_add_log w

/-- Completely elementary cardinality bound; no prime-counting
asymptotic is used. -/
theorem card_primesLE_le_self (w : ℕ) : (Nat.primesLE w).card ≤ w := by
  have hsub : Nat.primesLE w ⊆ Icc 1 w := by
    intro p hp
    exact mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
  calc
    (Nat.primesLE w).card ≤ (Icc 1 w).card := card_le_card hsub
    _ ≤ w := by simp

theorem earlyBrunT_nonneg (G : ℝ) : 0 ≤ earlyBrunT G := by
  have hmax : (1 : ℝ) ≤ max (Real.log G) 1 := le_max_right _ _
  have hlog : 0 ≤ Real.log (max (Real.log G) 1) := Real.log_nonneg hmax
  unfold earlyBrunT
  positivity

/-! ## Escape and comparison of the paper scales -/

theorem tendsto_earlyBrunRank_atTop :
    Tendsto earlyBrunRank atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

theorem tendsto_earlyBrunRank_windowG_atTop :
    Tendsto (fun X : ℕ => earlyBrunRank (windowG X)) atTop atTop :=
  tendsto_earlyBrunRank_atTop.comp tendsto_windowG_atTop

theorem tendsto_presieveW_windowG_atTop :
    Tendsto (fun X : ℕ => presieveW (windowG X)) atTop atTop := by
  rw [show (fun X : ℕ => presieveW (windowG X)) =
      fun X => ⌊Real.log (windowG X) ^ (4 : ℕ)⌋₊ by
    funext X
    rw [presieveW_eq]]
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_pow_atTop (by omega : (4 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_windowG_atTop))

/-- `earlyBrunT` is negligible relative to `sqrt (log G)`. -/
theorem tendsto_earlyBrunT_div_sqrt_log :
    Tendsto (fun G : ℝ =>
      earlyBrunT G / Real.sqrt (Real.log G)) atTop (nhds 0) := by
  have hinv : Tendsto (fun G : ℝ => (Real.sqrt (Real.log G))⁻¹)
      atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).comp
      Real.tendsto_log_atTop
  have hlog : Tendsto (fun G : ℝ =>
      Real.log (Real.log G) / Real.sqrt (Real.log G)) atTop (nhds 0) :=
    tendsto_log_div_sqrt_atTop.comp Real.tendsto_log_atTop
  have hsum := hinv.add ((tendsto_const_nhds (x := (4 : ℝ))).mul hlog)
  have hsum' : Tendsto (fun G : ℝ =>
      (Real.sqrt (Real.log G))⁻¹ +
        4 * (Real.log (Real.log G) / Real.sqrt (Real.log G)))
      atTop (nhds 0) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with G hG
  have hGpos : 0 < G := (Real.exp_pos 1).trans_le hG
  have ht : (1 : ℝ) ≤ Real.log G := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log G := Real.log_le_log (Real.exp_pos 1) hG
  have hsqrt : Real.sqrt (Real.log G) ≠ 0 :=
    (Real.sqrt_pos.mpr (zero_lt_one.trans_le ht)).ne'
  rw [earlyBrunT, max_eq_left ht]
  field_simp [hsqrt]

theorem eventually_earlyBrun_harmonic_le :
    ∀ᶠ X : ℕ in atTop,
      earlyBrunHarmonic (Nat.primesLE (presieveW (windowG X))) ≤
        earlyBrunT (windowG X) := by
  filter_upwards [tendsto_windowG_atTop.eventually_ge_atTop (Real.exp 1)] with X hG
  let G := windowG X
  let w := presieveW G
  have hGpos : 0 < G := (Real.exp_pos 1).trans_le hG
  have ht : (1 : ℝ) ≤ Real.log G := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log G := Real.log_le_log (Real.exp_pos 1) hG
  have ht0 : 0 ≤ Real.log G := zero_le_one.trans ht
  have hw1 : 1 ≤ w := by
    dsimp only [w]
    rw [presieveW_eq]
    have hone : ((1 : ℕ) : ℝ) ≤ Real.log G ^ (4 : ℕ) := by
      simpa using one_le_pow₀ ht
    exact Nat.le_floor hone
  have hwpos : (0 : ℝ) < w := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hw1)
  have hwle : (w : ℝ) ≤ Real.log G ^ (4 : ℕ) := by
    dsimp only [w]
    rw [presieveW_eq]
    exact Nat.floor_le (pow_nonneg ht0 _)
  have hlogw : Real.log (w : ℝ) ≤ 4 * Real.log (Real.log G) := by
    calc
      Real.log (w : ℝ) ≤ Real.log (Real.log G ^ (4 : ℕ)) :=
        Real.log_le_log hwpos hwle
      _ = 4 * Real.log (Real.log G) := Real.log_pow _ 4
  calc
    earlyBrunHarmonic (Nat.primesLE (presieveW (windowG X)))
        ≤ 1 + Real.log w := earlyBrunHarmonic_primesLE_le_one_add_log w
    _ ≤ 1 + 4 * Real.log (Real.log G) := by
      simpa [add_comm] using add_le_add_left hlogw 1
    _ = earlyBrunT (windowG X) := by
      simp only [earlyBrunT, G, max_eq_left ht]

theorem eventually_two_earlyBrunT_le_rank_add_one :
    ∀ᶠ X : ℕ in atTop,
      2 * earlyBrunT (windowG X) ≤
        (earlyBrunRank (windowG X) : ℝ) + 1 := by
  have hratio := tendsto_earlyBrunT_div_sqrt_log.comp tendsto_windowG_atTop
  filter_upwards [
    hratio.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)),
    tendsto_windowG_atTop.eventually_ge_atTop (Real.exp 1)] with X hsmall hG
  have ht : (1 : ℝ) ≤ Real.log (windowG X) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (windowG X) :=
        Real.log_le_log (Real.exp_pos 1) hG
  have hsqrt : 0 < Real.sqrt (Real.log (windowG X)) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le ht)
  have hratioLt :
      earlyBrunT (windowG X) / Real.sqrt (Real.log (windowG X)) < 1 / 2 := by
    have habs :
        |earlyBrunT (windowG X) / Real.sqrt (Real.log (windowG X))| < 1 / 2 := by
      change dist
        (earlyBrunT (windowG X) / Real.sqrt (Real.log (windowG X))) 0 < 1 / 2
        at hsmall
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsmall
    exact (le_abs_self _).trans_lt habs
  have htwo : 2 * earlyBrunT (windowG X) <
      Real.sqrt (Real.log (windowG X)) := by
    have := (div_lt_iff₀ hsqrt).mp hratioLt
    linarith
  have hfloor := Nat.lt_floor_add_one (Real.sqrt (Real.log (windowG X)))
  exact (htwo.trans (by simpa [earlyBrunRank] using hfloor)).le

/-- The small paper window contains an interval of real length `G`
eventually.  This is exported because it is also the denominator input
for the CRT-rounding part of the Brun error. -/
theorem eventually_windowG_le_ahlSmall_window {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      windowG X ≤ (ahlSmall_window κ X : ℝ) := by
  filter_upwards [eventually_one_le_profileL hκ,
    tendsto_windowG_atTop.eventually_ge_atTop (5 : ℝ)] with X hL hG
  have hGpos : 0 < windowG X := lt_of_lt_of_le (by norm_num) hG
  have hLR : (1 : ℝ) ≤ (profileL κ X : ℝ) := Nat.one_le_cast.mpr hL
  have hargLower :
      (6 / 5 : ℝ) * windowG X ≤
        (6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X := by
    have hc : (6 / 5 : ℝ) ≤ (6 / 5 : ℝ) * (profileL κ X : ℝ) := by
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hGpos.le
  have hGarg : windowG X + 1 ≤
      (6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X := by
    nlinarith [hargLower]
  have hfloor :
      (6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X <
        (ahlSmall_window κ X : ℝ) + 1 := by
    simpa only [ahlSmall_window_eq] using
      Nat.lt_floor_add_one
        ((6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X)
  linarith

/-! ## The finite Brun estimate at the paper scale -/

theorem eventually_earlyPresieve_survivorCount_abs_sub_main_le_brun
    {κ : ℝ} (_hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      ∀ τ : ResidueChoice (presieveW (windowG X)),
        |((earlyPresieveSurvivors (ahlSmall_window κ X)
              (presieveW (windowG X)) τ).card : ℝ) -
            (ahlSmall_window κ X : ℝ) *
              eulerProdNat (presieveW (windowG X))| ≤
          earlyPresieveBrunError (ahlSmall_window κ X)
            (presieveW (windowG X)) (earlyBrunRank (windowG X))
            (earlyBrunT (windowG X)) := by
  filter_upwards [eventually_earlyBrun_harmonic_le,
    eventually_two_earlyBrunT_le_rank_add_one] with X hH hs
  intro τ
  exact earlyPresieve_survivorCount_abs_sub_main_le_brun
    (ahlSmall_window κ X) (presieveW (windowG X))
    (earlyBrunRank (windowG X)) τ hH
    (earlyBrunT_nonneg (windowG X)) hs

/-! ## Normalized factorial tail -/

private theorem real_pow_div_factorial_le_exp_ratio
    (x : ℝ) (k : ℕ) (hx : 0 ≤ x) (hk : 0 < k) :
    x ^ k / (k.factorial : ℝ) ≤
      (Real.exp 1 * x / k) ^ k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul (1 : ℝ) k]
    congr 1
    exact (mul_one (k : ℝ)).symm
  have hst : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp 1 ^ k := by
    have h := Real.pow_div_factorial_le_exp (x := (k : ℝ))
      (Nat.cast_nonneg k) k
    rwa [hexp] at h
  have hnn : 0 ≤ (x / k) ^ k :=
    pow_nonneg (div_nonneg hx hkpos.le) k
  have hscale := mul_le_mul_of_nonneg_right hst hnn
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hfact : (k.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hleft :
      ((k : ℝ) ^ k / (k.factorial : ℝ)) * (x / k) ^ k =
        x ^ k / (k.factorial : ℝ) := by
    rw [div_pow]
    refine (eq_div_iff hfact).mpr ?_
    rw [mul_right_comm, div_mul_cancel₀ _ hfact, ← mul_div_assoc,
      mul_comm ((k : ℝ) ^ k), mul_div_cancel_right₀ _ (pow_ne_zero k hk0)]
  have hright :
      Real.exp 1 ^ k * (x / k) ^ k =
        (Real.exp 1 * x / k) ^ k := by
    rw [← mul_pow]
    congr 1
    rw [← mul_div_assoc]
  rwa [hleft, hright] at hscale

private theorem eventually_earlyBrun_exp_ratio_le_half :
    ∀ᶠ X : ℕ in atTop,
      Real.exp 1 * earlyBrunT (windowG X) /
          (earlyBrunRank (windowG X) + 1 : ℝ) ≤ 1 / 2 := by
  have hratio := tendsto_earlyBrunT_div_sqrt_log.comp tendsto_windowG_atTop
  have hε : 0 < (1 : ℝ) / (2 * Real.exp 1) := by positivity
  filter_upwards [hratio.eventually (Metric.ball_mem_nhds 0 hε),
    tendsto_windowG_atTop.eventually_ge_atTop (Real.exp 1)] with X hsmall hG
  have ht : (1 : ℝ) ≤ Real.log (windowG X) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (windowG X) := Real.log_le_log (Real.exp_pos 1) hG
  have hsqrt : 0 < Real.sqrt (Real.log (windowG X)) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le ht)
  have habs :
      |earlyBrunT (windowG X) / Real.sqrt (Real.log (windowG X))| <
        1 / (2 * Real.exp 1) := by
    change dist
      (earlyBrunT (windowG X) / Real.sqrt (Real.log (windowG X))) 0 <
        1 / (2 * Real.exp 1) at hsmall
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsmall
  have hsmall' :
      earlyBrunT (windowG X) / Real.sqrt (Real.log (windowG X)) <
        1 / (2 * Real.exp 1) := (le_abs_self _).trans_lt habs
  have hmul : 2 * Real.exp 1 * earlyBrunT (windowG X) <
      Real.sqrt (Real.log (windowG X)) := by
    have := (div_lt_iff₀ hsqrt).mp hsmall'
    have hexp : 0 < Real.exp 1 := Real.exp_pos 1
    field_simp [hexp.ne'] at this
    nlinarith
  have hfloor := Nat.lt_floor_add_one (Real.sqrt (Real.log (windowG X)))
  have hrank : Real.sqrt (Real.log (windowG X)) <
      (earlyBrunRank (windowG X) + 1 : ℝ) := by
    simpa [earlyBrunRank] using hfloor
  have hkpos : (0 : ℝ) < (earlyBrunRank (windowG X) + 1 : ℝ) := by
    positivity
  apply (div_le_iff₀ hkpos).mpr
  nlinarith [hmul.trans hrank]

private theorem eventually_log_presieveW_le_rank_add_one :
    ∀ᶠ X : ℕ in atTop,
      Real.log (presieveW (windowG X) : ℝ) ≤
        (earlyBrunRank (windowG X) + 1 : ℝ) := by
  have hratio := tendsto_log_div_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_windowG_atTop)
  filter_upwards [
    hratio.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)),
    tendsto_windowG_atTop.eventually_ge_atTop (Real.exp 1)] with X hsmall hG
  have ht : (1 : ℝ) ≤ Real.log (windowG X) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (windowG X) := Real.log_le_log (Real.exp_pos 1) hG
  have ht0 : 0 ≤ Real.log (windowG X) := zero_le_one.trans ht
  have hw1 : 1 ≤ presieveW (windowG X) := by
    rw [presieveW_eq]
    have hone : ((1 : ℕ) : ℝ) ≤
        Real.log (windowG X) ^ (4 : ℕ) := by
      simpa using one_le_pow₀ ht
    exact Nat.le_floor hone
  have hwpos : (0 : ℝ) < presieveW (windowG X) :=
    Nat.cast_pos.mpr (Nat.zero_lt_of_lt hw1)
  have hwle : (presieveW (windowG X) : ℝ) ≤
      Real.log (windowG X) ^ (4 : ℕ) := by
    rw [presieveW_eq]
    exact Nat.floor_le (pow_nonneg ht0 _)
  have hlogw : Real.log (presieveW (windowG X) : ℝ) ≤
      4 * Real.log (Real.log (windowG X)) := by
    calc
      Real.log (presieveW (windowG X) : ℝ) ≤
          Real.log (Real.log (windowG X) ^ (4 : ℕ)) :=
        Real.log_le_log hwpos hwle
      _ = 4 * Real.log (Real.log (windowG X)) := Real.log_pow _ 4
  have hsqrt : 0 < Real.sqrt (Real.log (windowG X)) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le ht)
  have habs :
      |Real.log (Real.log (windowG X)) /
          Real.sqrt (Real.log (windowG X))| < 1 / 4 := by
    change dist
      (Real.log (Real.log (windowG X)) /
        Real.sqrt (Real.log (windowG X))) 0 < 1 / 4 at hsmall
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsmall
  have hratioLt :
      Real.log (Real.log (windowG X)) /
          Real.sqrt (Real.log (windowG X)) < 1 / 4 :=
    (le_abs_self _).trans_lt habs
  have hfour : 4 * Real.log (Real.log (windowG X)) <
      Real.sqrt (Real.log (windowG X)) := by
    have := (div_lt_iff₀ hsqrt).mp hratioLt
    linarith
  have hfloor := Nat.lt_floor_add_one (Real.sqrt (Real.log (windowG X)))
  exact hlogw.trans (hfour.trans (by simpa [earlyBrunRank] using hfloor)).le

/-- The second summand of `earlyPresieveBrunError`, after cancellation
of the window size and normalization by `V(w)`, tends to zero. -/
theorem tendsto_earlyPresieveBrun_factorialTail_div_eulerProd
    {κ : ℝ} (_hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      (3 * earlyBrunT (windowG X) ^ (earlyBrunRank (windowG X) + 1) /
          ((earlyBrunRank (windowG X) + 1).factorial : ℝ)) /
        eulerProdNat (presieveW (windowG X))) atTop (nhds 0) := by
  let k : ℕ → ℕ := fun X => earlyBrunRank (windowG X) + 1
  have hk : Tendsto k atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      tendsto_earlyBrunRank_windowG_atTop
    exact Eventually.of_forall fun X => by
      dsimp only [k]
      omega
  have hgeom : Tendsto (fun X : ℕ =>
      (3 / eulerProdLowerConst : ℝ) * (k X : ℝ) * (1 / 2 : ℝ) ^ k X)
      atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n)
        atTop (nhds 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul (hbase.comp hk))
  refine squeeze_zero' ?_ ?_ hgeom
  · exact Eventually.of_forall fun X =>
      div_nonneg
        (div_nonneg
          (mul_nonneg (by norm_num)
            (pow_nonneg (earlyBrunT_nonneg (windowG X)) _))
          (Nat.cast_nonneg _))
        (eulerProdNat_pos _).le
  · filter_upwards [
      tendsto_presieveW_windowG_atTop.eventually (eventually_ge_atTop 16),
      eventually_earlyBrun_exp_ratio_le_half,
      eventually_log_presieveW_le_rank_add_one] with X hw16 hratio hlogw
    have hkpos : 0 < k X := by simp [k]
    have htail := real_pow_div_factorial_le_exp_ratio
      (earlyBrunT (windowG X)) (k X) (earlyBrunT_nonneg _) hkpos
    have hpow :
        (Real.exp 1 * earlyBrunT (windowG X) / (k X : ℝ)) ^ k X ≤
          (1 / 2 : ℝ) ^ k X :=
      pow_le_pow_left₀
        (div_nonneg
          (mul_nonneg (Real.exp_pos 1).le (earlyBrunT_nonneg _))
          (Nat.cast_nonneg _)) (by
            dsimp only [k]
            simpa only [Nat.cast_add, Nat.cast_one] using hratio) _
    have htail' :
        earlyBrunT (windowG X) ^ k X / ((k X).factorial : ℝ) ≤
          (1 / 2 : ℝ) ^ k X := htail.trans hpow
    have hwlogpos : 0 < Real.log (presieveW (windowG X) : ℝ) :=
      Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num) hw16))
    have hV := eulerProdNat_ge_mul_inv_log hw16
    have hcpos : 0 < eulerProdLowerConst := Real.exp_pos _
    calc
      (3 * earlyBrunT (windowG X) ^ k X / ((k X).factorial : ℝ)) /
          eulerProdNat (presieveW (windowG X))
          ≤ (3 * (1 / 2 : ℝ) ^ k X) /
              eulerProdNat (presieveW (windowG X)) := by
            apply div_le_div_of_nonneg_right _ (eulerProdNat_pos _).le
            simpa only [mul_div_assoc] using
              (mul_le_mul_of_nonneg_left htail' (by norm_num : (0 : ℝ) ≤ 3))
      _ ≤ (3 * (1 / 2 : ℝ) ^ k X) /
              (eulerProdLowerConst /
                Real.log (presieveW (windowG X) : ℝ)) := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
              (div_pos hcpos hwlogpos) hV
      _ = (3 / eulerProdLowerConst : ℝ) *
              Real.log (presieveW (windowG X) : ℝ) *
                (1 / 2 : ℝ) ^ k X := by
            field_simp [hcpos.ne', hwlogpos.ne']
      _ ≤ (3 / eulerProdLowerConst : ℝ) * (k X : ℝ) *
              (1 / 2 : ℝ) ^ k X := by
            have hc : 0 ≤ (3 / eulerProdLowerConst : ℝ) :=
              div_nonneg (by norm_num) hcpos.le
            have hlogk : Real.log (presieveW (windowG X) : ℝ) ≤ (k X : ℝ) := by
              simpa only [k, Nat.cast_add, Nat.cast_one] using hlogw
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlogk hc)
              (pow_nonneg (by norm_num) _)

/-- The literal factorial summand occurring in
`earlyPresieveBrunError`, divided by the full paper main term. -/
theorem tendsto_earlyPresieveBrun_factorialSummand_div_main
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      (3 * (ahlSmall_window κ X : ℝ) *
          earlyBrunT (windowG X) ^ (earlyBrunRank (windowG X) + 1) /
          ((earlyBrunRank (windowG X) + 1).factorial : ℝ)) /
        ((ahlSmall_window κ X : ℝ) *
          eulerProdNat (presieveW (windowG X)))) atTop (nhds 0) := by
  have htail := tendsto_earlyPresieveBrun_factorialTail_div_eulerProd hκ
  refine htail.congr' ?_
  filter_upwards [eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop (1 : ℝ)] with X hGS hG
  have hSpos : 0 < (ahlSmall_window κ X : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hG) hGS
  have hV0 : eulerProdNat (presieveW (windowG X)) ≠ 0 :=
    eulerProdNat_ne_zero _
  field_simp [hSpos.ne', hV0]

/-- The normalized CRT-rounding summand is reduced, using only
`card (primesLE w) ≤ w`, `S ≥ G`, and the weak Mertens lower bound, to
one explicit elementary majorant. -/
theorem eventually_earlyPresieveBrun_rounding_div_main_le
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop,
      (2 * ((earlyBrunRank (windowG X) : ℝ) + 1) *
          (((Nat.primesLE (presieveW (windowG X))).card : ℝ) + 1) ^
            (earlyBrunRank (windowG X) + 1)) /
          ((ahlSmall_window κ X : ℝ) *
            eulerProdNat (presieveW (windowG X))) ≤
        (2 * ((earlyBrunRank (windowG X) : ℝ) + 1) *
            ((presieveW (windowG X) : ℝ) + 1) ^
              (earlyBrunRank (windowG X) + 1) *
            Real.log (presieveW (windowG X) : ℝ)) /
          (windowG X * eulerProdLowerConst) := by
  filter_upwards [eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop (1 : ℝ),
    tendsto_presieveW_windowG_atTop.eventually (eventually_ge_atTop 16)] with
      X hGS hG hw16
  let G := windowG X
  let S := ahlSmall_window κ X
  let w := presieveW G
  let k := earlyBrunRank G + 1
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hSpos : 0 < (S : ℝ) := lt_of_lt_of_le hGpos hGS
  have hwlog : 0 < Real.log (w : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (lt_of_lt_of_le (by norm_num) hw16))
  have hcpos : 0 < eulerProdLowerConst := Real.exp_pos _
  have hVlower : eulerProdLowerConst / Real.log (w : ℝ) ≤ eulerProdNat w :=
    eulerProdNat_ge_mul_inv_log hw16
  have hVpos : 0 < eulerProdNat w := eulerProdNat_pos w
  have hden : G * (eulerProdLowerConst / Real.log (w : ℝ)) ≤
      (S : ℝ) * eulerProdNat w := by
    exact mul_le_mul hGS hVlower
      (div_nonneg hcpos.le hwlog.le) (Nat.cast_nonneg S)
  have hcardR : (((Nat.primesLE w).card : ℝ) + 1) ≤ (w : ℝ) + 1 := by
    have hc : ((Nat.primesLE w).card : ℝ) ≤ (w : ℝ) :=
      Nat.cast_le.mpr (card_primesLE_le_self w)
    simpa [add_comm] using add_le_add_right hc 1
  have hpow :
      (((Nat.primesLE w).card : ℝ) + 1) ^ k ≤ ((w : ℝ) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) hcardR k
  have hnum :
      2 * (k : ℝ) * (((Nat.primesLE w).card : ℝ) + 1) ^ k ≤
        2 * (k : ℝ) * ((w : ℝ) + 1) ^ k := by
    exact mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
  have hdenpos : 0 < (S : ℝ) * eulerProdNat w := mul_pos hSpos hVpos
  have hlowerpos : 0 < G * (eulerProdLowerConst / Real.log (w : ℝ)) :=
    mul_pos hGpos (div_pos hcpos hwlog)
  calc
    (2 * ((earlyBrunRank (windowG X) : ℝ) + 1) *
          (((Nat.primesLE (presieveW (windowG X))).card : ℝ) + 1) ^
            (earlyBrunRank (windowG X) + 1)) /
          ((ahlSmall_window κ X : ℝ) *
            eulerProdNat (presieveW (windowG X))) =
        (2 * (k : ℝ) * (((Nat.primesLE w).card : ℝ) + 1) ^ k) /
          ((S : ℝ) * eulerProdNat w) := by
            simp only [G, S, w, k, Nat.cast_add, Nat.cast_one]
    _ ≤ (2 * (k : ℝ) * ((w : ℝ) + 1) ^ k) /
          ((S : ℝ) * eulerProdNat w) :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (2 * (k : ℝ) * ((w : ℝ) + 1) ^ k) /
          (G * (eulerProdLowerConst / Real.log (w : ℝ))) :=
      div_le_div_of_nonneg_left
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
          (pow_nonneg (by positivity) _)) hlowerpos hden
    _ = (2 * (k : ℝ) * ((w : ℝ) + 1) ^ k * Real.log (w : ℝ)) /
          (G * eulerProdLowerConst) := by
      field_simp [hGpos.ne', hcpos.ne', hwlog.ne']
    _ = (2 * ((earlyBrunRank (windowG X) : ℝ) + 1) *
            ((presieveW (windowG X) : ℝ) + 1) ^
              (earlyBrunRank (windowG X) + 1) *
            Real.log (presieveW (windowG X) : ℝ)) /
          (windowG X * eulerProdLowerConst) := by
      simp only [G, w, k, Nat.cast_add, Nat.cast_one]

/-- Exact split of the normalized Brun error into the CRT-rounding
edge and the already closed factorial tail. -/
theorem earlyPresieveBrunError_div_main_eq
    {S w s : ℕ} {T : ℝ} (hS : 0 < S) :
    earlyPresieveBrunError S w s T /
        ((S : ℝ) * eulerProdNat w) =
      (2 * ((s : ℝ) + 1) *
          (((Nat.primesLE w).card : ℝ) + 1) ^ (s + 1)) /
          ((S : ℝ) * eulerProdNat w) +
        (3 * T ^ (s + 1) / ((s + 1).factorial : ℝ)) /
          eulerProdNat w := by
  have hSR : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hV : eulerProdNat w ≠ 0 := eulerProdNat_ne_zero w
  unfold earlyPresieveBrunError
  field_simp [hSR, hV]

private theorem eventually_earlyBrun_rank_mul_log_le :
    ∀ᶠ X : ℕ in atTop,
      ((earlyBrunRank (windowG X) : ℝ) + 1) *
          Real.log ((presieveW (windowG X) : ℝ) + 1) ≤
        Real.log (windowG X) / 2 := by
  have hratio := tendsto_earlyBrunT_div_sqrt_log.comp tendsto_windowG_atTop
  filter_upwards [
    hratio.eventually (Metric.ball_mem_nhds (0 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)),
    tendsto_windowG_atTop.eventually_ge_atTop (Real.exp 1)] with X hsmall hG
  let t := Real.log (windowG X)
  have ht : (1 : ℝ) ≤ t := by
    simpa [t] using Real.log_le_log (Real.exp_pos 1) hG
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hrpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr (zero_lt_one.trans_le ht)
  have hr1 : 1 ≤ Real.sqrt t := by
    simpa using Real.sqrt_le_sqrt ht
  have hrsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have habs : |earlyBrunT (windowG X) / Real.sqrt t| < 1 / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, t, Function.comp_apply] using hsmall
  have hT : 4 * earlyBrunT (windowG X) ≤ Real.sqrt t := by
    have h := (div_lt_iff₀ hrpos).mp ((le_abs_self _).trans_lt habs)
    linarith
  have hk : (earlyBrunRank (windowG X) : ℝ) + 1 ≤ 2 * Real.sqrt t := by
    have hf : (earlyBrunRank (windowG X) : ℝ) ≤ Real.sqrt t :=
      Nat.floor_le (Real.sqrt_nonneg _)
    linarith
  have hw : (presieveW (windowG X) : ℝ) + 1 ≤ 2 * t ^ (4 : ℕ) := by
    have hf : (presieveW (windowG X) : ℝ) ≤ t ^ (4 : ℕ) := by
      rw [presieveW_eq]
      exact Nat.floor_le (pow_nonneg ht0 _)
    have hp : (1 : ℝ) ≤ t ^ (4 : ℕ) := one_le_pow₀ ht
    linarith
  have hlog : Real.log ((presieveW (windowG X) : ℝ) + 1) ≤
      earlyBrunT (windowG X) := by
    calc
      Real.log ((presieveW (windowG X) : ℝ) + 1) ≤
          Real.log (2 * t ^ (4 : ℕ)) := Real.log_le_log (by positivity) hw
      _ = Real.log 2 + 4 * Real.log t := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ (zero_lt_one.trans_le ht).ne'),
          Real.log_pow]
        norm_num
      _ ≤ 1 + 4 * Real.log t := by
        have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      _ = earlyBrunT (windowG X) := by
        simp only [earlyBrunT, max_eq_left ht, t]
  have hlog0 : 0 ≤ Real.log ((presieveW (windowG X) : ℝ) + 1) :=
    Real.log_nonneg (by
      have hn : (0 : ℝ) ≤ (presieveW (windowG X) : ℝ) := Nat.cast_nonneg _
      linarith)
  calc
    ((earlyBrunRank (windowG X) : ℝ) + 1) *
        Real.log ((presieveW (windowG X) : ℝ) + 1) ≤
      (2 * Real.sqrt t) * earlyBrunT (windowG X) :=
        mul_le_mul hk hlog hlog0 (by positivity)
    _ ≤ t / 2 := by nlinarith

/-- The elementary CRT majorant vanishes because its exponential cost
is at most `exp ((log G)/2)`, while the denominator contains `G`. -/
theorem tendsto_earlyPresieveBrun_rounding_majorant :
    Tendsto (fun X : ℕ =>
      (2 * ((earlyBrunRank (windowG X) : ℝ) + 1) *
          ((presieveW (windowG X) : ℝ) + 1) ^
            (earlyBrunRank (windowG X) + 1) *
          Real.log (presieveW (windowG X) : ℝ)) /
        (windowG X * eulerProdLowerConst)) atTop (nhds 0) := by
  have hlim : Tendsto (fun X : ℕ =>
      (Real.log (windowG X) * Real.exp (-(1 / 2 : ℝ) * Real.log (windowG X))) /
        eulerProdLowerConst) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      1 (1 / 2) (by norm_num)).comp
        (Real.tendsto_log_atTop.comp tendsto_windowG_atTop)
    simpa using h.div_const eulerProdLowerConst
  have hc : 0 < eulerProdLowerConst := Real.exp_pos _
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [tendsto_presieveW_windowG_atTop.eventually_ge_atTop 1,
      tendsto_windowG_atTop.eventually_ge_atTop 1] with X hw hG
    have hlog : 0 ≤ Real.log (presieveW (windowG X) : ℝ) :=
      Real.log_nonneg (Nat.one_le_cast.mpr hw)
    positivity
  · filter_upwards [eventually_earlyBrun_rank_mul_log_le,
      tendsto_presieveW_windowG_atTop.eventually_ge_atTop 1,
      tendsto_windowG_atTop.eventually_ge_atTop 1] with X hcost hw hG
    let t := Real.log (windowG X)
    let w := presieveW (windowG X)
    let k := earlyBrunRank (windowG X) + 1
    have hGpos : 0 < windowG X := zero_lt_one.trans_le hG
    have ht : 0 ≤ t := Real.log_nonneg hG
    have hwpos : (0 : ℝ) < w := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hw)
    have hlog0 : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hw)
    have hcost' : (k : ℝ) * Real.log ((w : ℝ) + 1) ≤ t / 2 := by
      simpa only [k, w, t, Nat.cast_add, Nat.cast_one] using hcost
    have hpref : 2 * (k : ℝ) * Real.log (w : ℝ) ≤ t := by
      have hlog := Real.log_le_log hwpos (le_add_of_nonneg_right zero_le_one)
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
      linarith
    have hpow : ((w : ℝ) + 1) ^ k ≤ Real.exp (t / 2) := by
      calc
        ((w : ℝ) + 1) ^ k = Real.exp ((k : ℝ) * Real.log ((w : ℝ) + 1)) := by
          rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
        _ ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr hcost'
    have hnum : 2 * (k : ℝ) * ((w : ℝ) + 1) ^ k * Real.log (w : ℝ) ≤
        t * Real.exp (t / 2) := by
      calc
        2 * (k : ℝ) * ((w : ℝ) + 1) ^ k * Real.log (w : ℝ) =
            (2 * (k : ℝ) * Real.log (w : ℝ)) * ((w : ℝ) + 1) ^ k := by ring
        _ ≤ t * Real.exp (t / 2) :=
          mul_le_mul hpref hpow (by positivity) ht
    have hquot := div_le_div_of_nonneg_right hnum (mul_pos hGpos hc).le
    have hrew : (t * Real.exp (t / 2)) / (windowG X * eulerProdLowerConst) =
        (t * Real.exp (-(1 / 2 : ℝ) * t)) / eulerProdLowerConst := by
      have hexp : Real.exp (t / 2) / windowG X = Real.exp (-(1 / 2 : ℝ) * t) := by
        rw [show windowG X = Real.exp t from (Real.exp_log hGpos).symm,
          ← Real.exp_sub]
        congr 1
        ring
      calc
        (t * Real.exp (t / 2)) / (windowG X * eulerProdLowerConst) =
            (t * (Real.exp (t / 2) / windowG X)) / eulerProdLowerConst := by ring
        _ = _ := by rw [hexp]
    rw [hrew] at hquot
    simpa only [k, w, t, Nat.cast_add, Nat.cast_one] using hquot

theorem tendsto_earlyPresieveBrun_rounding_div_main
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      (2 * ((earlyBrunRank (windowG X) : ℝ) + 1) *
          (((Nat.primesLE (presieveW (windowG X))).card : ℝ) + 1) ^
            (earlyBrunRank (windowG X) + 1)) /
        ((ahlSmall_window κ X : ℝ) *
          eulerProdNat (presieveW (windowG X)))) atTop (nhds 0) := by
  refine squeeze_zero' ?_ (eventually_earlyPresieveBrun_rounding_div_main_le hκ)
    tendsto_earlyPresieveBrun_rounding_majorant
  exact Eventually.of_forall fun X => by
    have hV := (eulerProdNat_pos (presieveW (windowG X))).le
    positivity

/-- The complete relative Brun error tends to zero at the small paper
window.  The only hypothesis is the positivity of the window parameter. -/
theorem tendsto_earlyPresieveBrunError_div_main
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      earlyPresieveBrunError (ahlSmall_window κ X)
          (presieveW (windowG X)) (earlyBrunRank (windowG X))
          (earlyBrunT (windowG X)) /
        ((ahlSmall_window κ X : ℝ) *
          eulerProdNat (presieveW (windowG X)))) atTop (nhds 0) := by
  have hsum := (tendsto_earlyPresieveBrun_rounding_div_main hκ).add
    (tendsto_earlyPresieveBrun_factorialTail_div_eulerProd hκ)
  simp only [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop 1] with X hS hG
  have hSpos : 0 < ahlSmall_window κ X := Nat.cast_pos.mp (zero_lt_one.trans_le (hG.trans hS))
  exact (earlyPresieveBrunError_div_main_eq hSpos).symm

/-- Uniform early survivor asymptotics in the form used by the
conditional middle-presieve mean. -/
theorem eventually_earlyPresieve_survivorCount_relative_error_lt
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ∀ τ : ResidueChoice (presieveW (windowG X)),
        |((earlyPresieveSurvivors (ahlSmall_window κ X)
              (presieveW (windowG X)) τ).card : ℝ) -
            (ahlSmall_window κ X : ℝ) *
              eulerProdNat (presieveW (windowG X))| <
          ε * ((ahlSmall_window κ X : ℝ) *
            eulerProdNat (presieveW (windowG X))) := by
  have herr := (tendsto_earlyPresieveBrunError_div_main hκ).eventually
    (gt_mem_nhds hε)
  filter_upwards [herr,
    eventually_earlyPresieve_survivorCount_abs_sub_main_le_brun hκ,
    eventually_windowG_le_ahlSmall_window hκ,
    tendsto_windowG_atTop.eventually_ge_atTop 1] with X hE hcard hS hG
  have hSpos : 0 < (ahlSmall_window κ X : ℝ) :=
    zero_lt_one.trans_le (hG.trans hS)
  have hmain : 0 < (ahlSmall_window κ X : ℝ) *
      eulerProdNat (presieveW (windowG X)) :=
    mul_pos hSpos (eulerProdNat_pos _)
  intro τ
  exact (hcard τ).trans_lt ((div_lt_iff₀ hmain).mp hE)

end

end PrimeGapNormality.Prime
