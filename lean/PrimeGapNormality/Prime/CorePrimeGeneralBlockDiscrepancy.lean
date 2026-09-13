import PrimeGapNormality.Prime.CorePrimePositionQuantitativeComparison
import PrimeGapNormality.Prime.CoreFiniteOrbitDiscrepancy

/-!
# General finite prime-position block discrepancy

This is the quantitative finite consumer with the arithmetic discrepancy
`D(X,c)` left visible.  It assumes neither Kuperberg nor convergence of
`D`.  The rational `(B-1)`-cover converts the proved positive gap-window
comparison to a positive domination statement for the actual position
orbit.

For the analytic orbit step we use

* `eta_X = G_X^(-1/2) + G_X B^(-L_X)`,
* `T_X = floor (log (1/eta_X) / (4 log B))`, and
* `delta_X = eta_X^(1/4)`.

The square-root reserve in the literal definition of `profileL` implies
`eta_X -> 0` even at the endpoint `kappa = 1/log B`.
-/

namespace PrimeGapNormality.Prime.CorePrimeGeneralBlockDiscrepancy

open Filter Finset MeasureTheory Set
open CorePrimeQuantitativeComparison
  CorePrimePositionQuantitativeComparison CoreFiniteOrbitDiscrepancy
open scoped Topology Classical NNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1500000

abbrev Circle := AddCircle (1 : ℝ)

def generalPrimeD (κ c : ℝ) (X : ℕ) : ℝ :=
  corePrimeComparisonQuantity X (ahlSmall_omega κ X)
    (profileL κ X) (profileR (profileL κ X) 20) c

def generalBlockEta (B : ℕ) (κ : ℝ) (X : ℕ) : ℝ :=
  windowG X ^ (-(1 / 2 : ℝ)) +
    windowG X * ((B : ℝ) ^ profileL κ X)⁻¹

def generalBlockTime (B : ℕ) (κ : ℝ) (X : ℕ) : ℕ :=
  ⌊Real.log ((generalBlockEta B κ X)⁻¹) /
      (4 * Real.log (B : ℝ))⌋₊

def generalBlockRamp (B : ℕ) (κ : ℝ) (X : ℕ) : ℝ :=
  generalBlockEta B κ X ^ (1 / 4 : ℝ)

def generalBlockRate (B : ℕ) (κ : ℝ) (X : ℕ) : ℝ :=
  1 / Real.sqrt (Real.log ((generalBlockEta B κ X)⁻¹))

def generalPrimePositionBlockIntervalMass (B X : ℕ) (t : ℝ) : ℝ :=
  orbitIntervalMass B (primePosSeries B : Circle)
    (Nat.primeCounting X) (windowNX X) t

/-! ## Actual positive domination with `D(X,c)` visible -/

/-- The rational cover applied to the actual quantitative positive gap
comparison.  Its threshold precedes every nonnegative Lipschitz test.
There is no hypothesis on the size or limit of `generalPrimeD`. -/
theorem eventually_primePosition_finitePositiveDomination_general
    (B : ℕ) (hB : 2 ≤ B) {κ c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hc : 1 ≤ c) :
    ∃ A E H : ℝ, 0 ≤ A ∧ 0 ≤ E ∧ 0 ≤ H ∧
      ∀ᶠ X : ℕ in atTop,
        0 ≤ generalPrimeD κ c X ∧
        FinitePositiveDomination B (primePosSeries B : Circle)
          (Nat.primeCounting X) (windowNX X) A
          (E * (generalPrimeD κ c X + (profileL κ X : ℝ)⁻¹))
          (H * generalBlockEta B κ X) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hκpos : 0 < κ :=
    (div_pos zero_lt_one hlogB).trans_le hκ
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  obtain ⟨Cvol, Cerr, hCvol, hCerr, hprime⟩ :=
    corePrimeGap_positive_window_quantitative B hB hκ hc
  let q : ℕ := B - 1
  let A : ℝ := Cvol * c * q
  let E : ℝ := Cerr * q
  let H : ℝ := Cerr
  have hq : 0 < q := by dsimp only [q]; omega
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hH : 0 ≤ H := by simpa only [H] using hCerr
  refine ⟨A, E, H, hA, hE, hH, ?_⟩
  filter_upwards [hprime, eventually_one_le_profileL hκpos,
    eventually_ge_atTop 1] with X hprimeX hL hX
  let L := profileL κ X
  let D := generalPrimeD κ c X
  let eta := generalBlockEta B κ X
  have hN : 0 < windowNX X := windowNX_pos (by omega : 0 < X)
  have hD0 : 0 ≤ D := by
    dsimp only [D, generalPrimeD, L]
    exact corePrimeComparisonQuantity_nonneg_general hN hL
      (crtMixProf_le_at κ 20 X) (crtMixProf_odd_at κ 20 X)
  refine ⟨by simpa only [D] using hD0, ?_⟩
  intro f K hf0 hLip
  let cover := rationalCover q hq f
  have hcover0 : ∀ x, 0 ≤ cover x := rationalCover_nonneg hq f hf0
  have hcoverLip : LipschitzWith K cover :=
    rationalCover_lipschitz hq f hLip
  have hbase := hprimeX cover K hcoverLip hcover0
  have hpoint : ∀ n ∈ seqWindow nthPrime X,
      f (primePositionCircleOrbit B n) ≤
        cover (corePrimeGapCircleOrbit B n) := by
    intro n hn
    rw [gapOrbit_eq_mul_positionOrbit hB]
    exact le_rationalCover_mul hq f hf0 _
  have havg : windowAvgReal (seqWindow nthPrime X)
      (fun n => f (primePositionCircleOrbit B n)) ≤
      windowAvgReal (seqWindow nthPrime X)
        (fun n => cover (corePrimeGapCircleOrbit B n)) := by
    unfold windowAvgReal
    exact div_le_div_of_nonneg_right (sum_le_sum hpoint)
      (Nat.cast_nonneg _)
  have hnorm := rationalCover_norm_le hq f
  have hint := rationalCover_integral hq f
  have hscale0 : 0 ≤ D + (L : ℝ)⁻¹ :=
    _root_.add_nonneg hD0 (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hnormTerm :
      (D + (L : ℝ)⁻¹) * ‖cover‖ ≤
        (q : ℝ) * (D + (L : ℝ)⁻¹) * ‖f‖ := by
    have hh := mul_le_mul_of_nonneg_left hnorm hscale0
    exact hh.trans_eq (by ring)
  have hcombined := havg.trans (hbase.trans
    (_root_.add_le_add
      (mul_le_mul_of_nonneg_left hint.le
        (mul_nonneg hCvol (zero_le_one.trans hc)))
      (mul_le_mul_of_nonneg_left
        (_root_.add_le_add hnormTerm le_rfl) hCerr)))
  rw [position_orbitBlockMean_eq_windowAvg]
  dsimp only [A, E, H, L, D, eta, generalBlockEta, cover] at hcombined ⊢
  exact hcombined.trans_eq (by ring)

/-! ## The critical endpoint still has a vanishing phase scale -/

theorem generalBlockEta_pos
    (B : ℕ) (κ : ℝ) (X : ℕ) : 0 < generalBlockEta B κ X := by
  unfold generalBlockEta
  have hG : 0 < windowG X := zero_lt_one.trans_le (crtWindowG_one_le X)
  exact add_pos_of_pos_of_nonneg
    (Real.rpow_pos_of_pos hG _)
    (mul_nonneg hG.le (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)))

/-- The tail component `G B^{-L}` tends to zero at the nonstrict endpoint.
The square-root reserve in `profileL`, rather than a strict inequality in
`kappa`, supplies the decay. -/
theorem tendsto_generalBlock_tail_zero
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Tendsto (fun X : ℕ =>
      windowG X * ((B : ℝ) ^ profileL κ X)⁻¹) atTop (nhds 0) := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hlb : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hκpos : 0 < κ := (div_pos zero_lt_one hlb).trans_le hκ
  have hlogG : Tendsto (fun X => Real.log (windowG X)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_windowG_atTop
  have hinner : Tendsto (fun X => κ * Real.log (windowG X)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hκpos hlogG
  have hsqrt : Tendsto
      (fun X => Real.sqrt (κ * Real.log (windowG X))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hinner
  have hscaled : Tendsto
      (fun X => Real.log (B : ℝ) *
        Real.sqrt (κ * Real.log (windowG X))) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hlb hsqrt
  have hupper : Tendsto (fun X => Real.exp
      (-(Real.log (B : ℝ) * Real.sqrt (κ * Real.log (windowG X)))))
      atTop (nhds 0) := by
    have hneg : Tendsto (fun X => -(
        Real.log (B : ℝ) * Real.sqrt (κ * Real.log (windowG X))))
        atTop atBot := tendsto_neg_atTop_atBot.comp hscaled
    exact Real.tendsto_exp_atBot.comp hneg
  apply squeeze_zero' (Eventually.of_forall fun X =>
    mul_nonneg (zero_le_one.trans (crtWindowG_one_le X))
      (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg B) (profileL κ X)))) _ hupper
  filter_upwards [tendsto_windowG_atTop.eventually_gt_atTop 1] with X hG1
  let G := windowG X
  let ell := Real.log G
  let z := Real.sqrt (κ * ell)
  let L := profileL κ X
  have hG : 0 < G := zero_lt_one.trans hG1
  have hell : 0 ≤ ell := Real.log_nonneg hG1.le
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hκlb : 1 ≤ κ * Real.log (B : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hκ hlb.le
    simpa only [one_div, inv_mul_cancel₀ hlb.ne'] using hh
  have hL : κ * ell + z ≤ (L : ℝ) := by
    dsimp only [L, profileL, z, ell, G]
    exact Nat.le_ceil _
  have hexponent : ell + Real.log (B : ℝ) * z ≤
      (L : ℝ) * Real.log (B : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hL hlb.le
    have hmain := mul_le_mul_of_nonneg_right hκlb hell
    nlinarith
  have hBL : G * Real.exp (Real.log (B : ℝ) * z) ≤ (B : ℝ) ^ L := by
    calc
      G * Real.exp (Real.log (B : ℝ) * z) =
          Real.exp (ell + Real.log (B : ℝ) * z) := by
        change G * Real.exp (Real.log (B : ℝ) * z) =
          Real.exp (Real.log G + Real.log (B : ℝ) * z)
        rw [Real.exp_add, Real.exp_log hG]
      _ ≤ Real.exp ((L : ℝ) * Real.log (B : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = (B : ℝ) ^ L := by
        rw [Real.exp_nat_mul, Real.exp_log hBpos]
  have hinv := one_div_le_one_div_of_le
    (mul_pos hG (Real.exp_pos _)) hBL
  calc
    G * ((B : ℝ) ^ L)⁻¹ ≤
        G * (G * Real.exp (Real.log (B : ℝ) * z))⁻¹ :=
      mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinv) hG.le
    _ = Real.exp (-(Real.log (B : ℝ) * z)) := by
      rw [Real.exp_neg]
      field_simp [hG.ne', (Real.exp_pos _).ne']
    _ = Real.exp (-(Real.log (B : ℝ) *
        Real.sqrt (κ * Real.log (windowG X)))) := by
      simp only [z, ell, G]

theorem tendsto_generalBlockEta_zero
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Tendsto (generalBlockEta B κ) atTop (nhds 0) := by
  have hfirst := (_root_.tendsto_rpow_neg_atTop
    (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_windowG_atTop
  have hsecond := tendsto_generalBlock_tail_zero B hB hκ
  change Tendsto (fun X : ℕ => windowG X ^ (-(1 / 2 : ℝ)) +
    windowG X * ((B : ℝ) ^ profileL κ X)⁻¹) atTop (nhds 0)
  simpa only [add_zero, Function.comp_def] using hfirst.add hsecond

theorem tendsto_generalBlockEta_inv_atTop
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Tendsto (fun X => (generalBlockEta B κ X)⁻¹) atTop atTop := by
  have hwithin : Tendsto (generalBlockEta B κ) atTop (nhdsWithin 0 (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_generalBlockEta_zero B hB hκ,
      Eventually.of_forall fun X => generalBlockEta_pos B κ X⟩
  exact tendsto_inv_nhdsGT_zero.comp hwithin

theorem tendsto_generalBlock_log_inv_atTop
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Tendsto (fun X => Real.log ((generalBlockEta B κ X)⁻¹))
      atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_generalBlockEta_inv_atTop B hB hκ)

theorem tendsto_generalBlockRate_zero
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    Tendsto (generalBlockRate B κ) atTop (nhds 0) := by
  have hsqrt := Real.tendsto_sqrt_atTop.comp
    (tendsto_generalBlock_log_inv_atTop B hB hκ)
  have hinv := tendsto_inv_atTop_zero.comp hsqrt
  change Tendsto (fun X : ℕ =>
    1 / Real.sqrt (Real.log ((generalBlockEta B κ X)⁻¹))) atTop (nhds 0)
  simpa only [one_div, Function.comp_def] using hinv

/-! ## Uniform finite orbit scale bookkeeping -/

structure GeneralBlockScaleBounds
    (B : ℕ) (κ : ℝ) (X : ℕ) : Prop where
  time_pos : 0 < generalBlockTime B κ X
  window_pos : 0 < windowNX X
  ramp_pos : 0 < generalBlockRamp B κ X
  time_term : Real.sqrt (6 / (generalBlockTime B κ X : ℝ)) ≤
    (8 * (Real.log (B : ℝ) + 1)) * generalBlockRate B κ X
  rank_term : (profileL κ X : ℝ)⁻¹ ≤
    (Real.log (B : ℝ) + 1) * generalBlockRate B κ X
  insertion_term : generalBlockEta B κ X *
      ((2 / generalBlockRamp B κ X) *
        (B ^ generalBlockTime B κ X : ℕ)) ≤
    4 * generalBlockRate B κ X
  boundary_term : 2 * (generalBlockTime B κ X : ℝ) /
      (windowNX X : ℝ) ≤ 2 * generalBlockRate B κ X
  ramp_term : 2 * generalBlockRamp B κ X ≤
    2 * generalBlockRate B κ X

private theorem eventually_sqrt_log_le_rpow_eighth :
    ∀ᶠ Z : ℝ in atTop,
      Real.sqrt (Real.log Z) ≤ Z ^ (1 / 8 : ℝ) := by
  have hsmall : ∀ᶠ Z : ℝ in atTop,
      ‖Real.log Z‖ ≤ (1 : ℝ) * ‖Z ^ (1 / 4 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 4)).bound (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 2] with Z hlog hZ
  have hZ0 : 0 < Z := zero_lt_two.trans_le hZ
  have hlog0 : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hbase : Real.log Z ≤ Z ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hZ0.le _), one_mul] using hlog
  apply (Real.sqrt_le_iff).2
  refine ⟨Real.rpow_nonneg hZ0.le _, ?_⟩
  calc
    Real.log Z ≤ Z ^ (1 / 4 : ℝ) := hbase
    _ = (Z ^ (1 / 8 : ℝ)) ^ 2 := by
      rw [sq, ← Real.rpow_add hZ0]
      norm_num

private theorem eventually_log_cube_div_self_le
    (d : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ 3 / (X : ℝ) ≤ d := by
  have hlim : Tendsto (fun X : ℕ =>
      Real.log (X : ℝ) ^ 3 / (X : ℝ)) atTop (nhds 0) := by
    have hh := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 3 (by norm_num)
    simpa only [one_mul, add_zero, Function.comp_def] using
      hh.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact hlim.eventually_le_const hd

theorem eventually_generalBlockScaleBounds
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in atTop, GeneralBlockScaleBounds B κ X := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlb : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hκpos : 0 < κ := (div_pos zero_lt_one hlb).trans_le hκ
  have hZtop := tendsto_generalBlockEta_inv_atTop B hB hκ
  have hutop := tendsto_generalBlock_log_inv_atTop B hB hκ
  have hsqrt := hZtop.eventually eventually_sqrt_log_le_rpow_eighth
  have hdensity := CorePrimeDensity.eventually_seqWindow_card_ge
  have hcube := eventually_log_cube_div_self_le
    (CoreDyadicPrimeCounting.dyadicCountConstant / 2)
    (div_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos (by norm_num))
  filter_upwards [hutop.eventually_ge_atTop
      (max 2 (8 * Real.log (B : ℝ))),
    hZtop.eventually_ge_atTop 2, hsqrt, hdensity, hcube,
    crtWindowG_eventually_eq_log, eventually_ge_atTop 3] with
      X huLarge hZ2 hsqrtZ hcard hcube hGeq hX
  let eta := generalBlockEta B κ X
  let Z := eta⁻¹
  let u := Real.log Z
  let G := windowG X
  let lb := Real.log (B : ℝ)
  let L := profileL κ X
  let T := generalBlockTime B κ X
  let delta := generalBlockRamp B κ X
  let R := generalBlockRate B κ X
  have heta : 0 < eta := by
    dsimp only [eta]
    exact generalBlockEta_pos B κ X
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hZ1 : 1 ≤ Z := by
    dsimp only [Z]
    exact (by linarith : (1 : ℝ) ≤ 2).trans hZ2
  have hu2 : (2 : ℝ) ≤ u := by
    simpa only [u, Z, Function.comp_apply] using
      (le_max_left _ _).trans huLarge
  have hu : 0 < u := zero_lt_two.trans_le hu2
  have hu8 : 8 * lb ≤ u := by
    simpa only [u, Z, lb, Function.comp_apply] using
      (le_max_right _ _).trans huLarge
  have hTupper : (T : ℝ) ≤ u / (4 * lb) := by
    dsimp only [T, generalBlockTime, u, Z, lb, eta]
    exact Nat.floor_le (div_nonneg hu.le (mul_nonneg (by norm_num) hlb.le))
  have hxdef : u / (4 * lb) < (T : ℝ) + 1 := by
    simpa only [T, generalBlockTime, u, Z, lb, eta] using
      Nat.lt_floor_add_one (u / (4 * lb))
  have hTlower : u / (8 * lb) ≤ (T : ℝ) := by
    have htwo : (2 : ℝ) ≤ u / (4 * lb) := by
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hlb)).2
      nlinarith only [hu8]
    have hhalf : u / (8 * lb) ≤ u / (4 * lb) - 1 := by
      have heq : u / (8 * lb) = (u / (4 * lb)) / 2 := by ring
      rw [heq]
      linarith only [htwo]
    linarith
  have hT : 0 < T := by
    have hh : (0 : ℝ) < T :=
      (div_pos hu (mul_pos (by norm_num) hlb)).trans_le hTlower
    exact Nat.cast_pos.mp hh
  have hN : 0 < windowNX X := by
    have hcpos : 0 < CoreDyadicPrimeCounting.dyadicCountConstant *
        ((X : ℝ) / Real.log X) := by
      exact mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
        (div_pos (Nat.cast_pos.mpr (by omega))
          (Real.log_pos (by exact_mod_cast (show 1 < X by omega))))
    have hh : (0 : ℝ) < (seqWindow nthPrime X).card := hcpos.trans_le hcard
    have hreal : (0 : ℝ) < windowNX X := by
      simpa only [seqWindow_nthPrime_card] using hh
    exact Nat.cast_pos.mp hreal
  have hdelta : 0 < delta := by
    dsimp only [delta, generalBlockRamp]
    exact Real.rpow_pos_of_pos heta _
  have hR : 0 < R := by
    dsimp only [R, generalBlockRate, u, Z, eta]
    exact div_pos zero_lt_one (Real.sqrt_pos.mpr hu)
  have htime : Real.sqrt (6 / (T : ℝ)) ≤
      (8 * (lb + 1)) * R := by
    have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    have hTscaled : u ≤ 8 * lb * (T : ℝ) := by
      have hh := (div_le_iff₀
        (mul_pos (by norm_num : (0 : ℝ) < 8) hlb)).mp hTlower
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
    have hcoef : 48 * lb ≤ (8 * (lb + 1)) ^ 2 := by
      nlinarith [sq_nonneg (lb - 1)]
    have hmain : 6 * u ≤ (8 * (lb + 1)) ^ 2 * (T : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_left hTscaled (by norm_num : (0 : ℝ) ≤ 6)
      have h₂ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg T)
      nlinarith
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (by positivity) hR.le, ?_⟩
    have hsquare : ((8 * (lb + 1)) * R) ^ 2 =
        (8 * (lb + 1)) ^ 2 / u := by
      change ((8 * (lb + 1)) * (1 / Real.sqrt u)) ^ 2 = _
      rw [mul_pow, one_div_pow, Real.sq_sqrt hu.le]
      ring
    rw [hsquare]
    exact (div_le_div_iff₀ hTR hu).2 hmain
  have hG : 0 < G := by dsimp only [G]; exact zero_lt_one.trans_le (crtWindowG_one_le X)
  have hG1 : 1 ≤ G := by dsimp only [G]; exact crtWindowG_one_le X
  have hetaBase : G ^ (-(1 / 2 : ℝ)) ≤ eta := by
    dsimp only [eta, generalBlockEta]
    exact le_add_of_nonneg_right (by positivity)
  have hZupper : Z ≤ G ^ (1 / 2 : ℝ) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hG (-(1 / 2 : ℝ))) hetaBase
    dsimp only [Z]
    calc
      eta⁻¹ ≤ (G ^ (-(1 / 2 : ℝ)))⁻¹ := hi
      _ = G ^ (1 / 2 : ℝ) := by rw [Real.rpow_neg hG.le, inv_inv]
  have huG : 2 * u ≤ Real.log G := by
    have hlog := Real.log_le_log hZ hZupper
    rw [Real.log_rpow hG] at hlog
    dsimp only [u, Z]
    linarith
  have hlogGleG : Real.log G ≤ G :=
    (Real.log_le_sub_one_of_pos hG).trans (by linarith)
  have huLeG : u ≤ G := by
    have huLeLog : u ≤ Real.log G := by linarith only [huG, hu]
    exact huLeLog.trans hlogGleG
  have hLbase : κ * Real.log G ≤ (L : ℝ) := by
    dsimp only [L, G]
    exact kappa_log_windowG_le_profileL hκpos.le X
  have hκlb : 1 ≤ κ * lb := by
    have hh := mul_le_mul_of_nonneg_right hκ hlb.le
    simpa only [lb, one_div, inv_mul_cancel₀ hlb.ne'] using hh
  have hLscaled : Real.log G ≤ (L : ℝ) * lb := by
    have hh := mul_le_mul_of_nonneg_right hLbase hlb.le
    have hm := mul_le_mul_of_nonneg_right hκlb (Real.log_nonneg hG1)
    nlinarith
  have hLlower : 2 * u / lb ≤ (L : ℝ) := by
    apply (div_le_iff₀ hlb).2
    exact huG.trans hLscaled
  have hLpos : (0 : ℝ) < L :=
    (div_pos (mul_pos (by norm_num) hu) hlb).trans_le hLlower
  have hrank : (L : ℝ)⁻¹ ≤ (lb + 1) * R := by
    have hinv := one_div_le_one_div_of_le
      (div_pos (mul_pos (by norm_num) hu) hlb) hLlower
    have hsqrtu : Real.sqrt u ≤ u :=
      (Real.sqrt_le_self_iff).2 (Or.inr (by linarith : 1 ≤ u))
    have hcmp : lb / (2 * u) ≤ (lb + 1) / Real.sqrt u := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hu)
        (Real.sqrt_pos.mpr hu)).2
      have hh := mul_le_mul_of_nonneg_left hsqrtu hlb.le
      nlinarith only [hh, hu, hlb, mul_pos hlb hu]
    calc
      (L : ℝ)⁻¹ = 1 / (L : ℝ) := (one_div _).symm
      _ ≤ 1 / (2 * u / lb) := hinv
      _ = lb / (2 * u) := by field_simp [hlb.ne', hu.ne']
      _ ≤ (lb + 1) / Real.sqrt u := hcmp
      _ = (lb + 1) * R := by
        dsimp only [R, generalBlockRate, u, Z, eta]
        ring
  have hBT : ((B ^ T : ℕ) : ℝ) ≤ Z ^ (1 / 4 : ℝ) := by
    have hTlb : (T : ℝ) * lb ≤ u / 4 := by
      have hh := (le_div_iff₀
        (mul_pos (by norm_num : (0 : ℝ) < 4) hlb)).mp hTupper
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      nlinarith only [hh]
    rw [Nat.cast_pow]
    calc
      (B : ℝ) ^ T = Real.exp ((T : ℝ) * lb) := by
        rw [Real.exp_nat_mul, Real.exp_log
          (Nat.cast_pos.mpr (by omega : 0 < B))]
      _ ≤ Real.exp (u / 4) := Real.exp_le_exp.mpr hTlb
      _ = Z ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_def_of_pos hZ]
        congr 1
        dsimp only [u]
        ring
  have hdeltaInv : delta⁻¹ = Z ^ (1 / 4 : ℝ) := by
    change (eta ^ (1 / 4 : ℝ))⁻¹ = (eta⁻¹) ^ (1 / 4 : ℝ)
    rw [Real.inv_rpow heta.le]
  have hetaZ : eta = Z⁻¹ := by dsimp only [Z]; rw [inv_inv]
  have hinsertionRaw : eta * ((2 / delta) * ((B ^ T : ℕ) : ℝ)) ≤
      2 * Z ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, hdeltaInv, hetaZ]
    have hh := mul_le_mul_of_nonneg_left hBT
      (mul_nonneg (inv_nonneg.mpr hZ.le)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg hZ.le (1 / 4 : ℝ))))
    calc
      Z⁻¹ * ((2 * Z ^ (1 / 4 : ℝ)) * ((B ^ T : ℕ) : ℝ)) =
          (Z⁻¹ * (2 * Z ^ (1 / 4 : ℝ))) * ((B ^ T : ℕ) : ℝ) := by ring
      _ ≤ (Z⁻¹ * (2 * Z ^ (1 / 4 : ℝ))) * Z ^ (1 / 4 : ℝ) := hh
      _ =
            2 * (Z ^ (-(1 : ℝ)) * Z ^ (1 / 4 : ℝ) *
              Z ^ (1 / 4 : ℝ)) := by rw [Real.rpow_neg_one]; ring
      _ = 2 * Z ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
        norm_num
  have hpowRate : Z ^ (-(1 / 8 : ℝ)) ≤ R := by
    have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hu)
      (by simpa only [u, Z] using hsqrtZ)
    have heq : Z ^ (-(1 / 8 : ℝ)) = 1 / Z ^ (1 / 8 : ℝ) := by
      simp only [Real.rpow_neg hZ.le, one_div]
    simpa only [heq, R, generalBlockRate, u, Z, eta] using hinv
  have hinsertion : eta * ((2 / delta) * ((B ^ T : ℕ) : ℝ)) ≤
      4 * R := by
    have hpow : Z ^ (-(1 / 2 : ℝ)) ≤ Z ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
    exact hinsertionRaw.trans
      ((mul_le_mul_of_nonneg_left (hpow.trans hpowRate) (by norm_num)).trans
        (by nlinarith [hR.le]))
  have hramp : 2 * delta ≤ 2 * R := by
    have hdeltaEq : delta = Z ^ (-(1 / 4 : ℝ)) := by
      change eta ^ (1 / 4 : ℝ) = Z ^ (-(1 / 4 : ℝ))
      rw [hetaZ, Real.inv_rpow hZ.le, Real.rpow_neg hZ.le]
    have hpow : Z ^ (-(1 / 4 : ℝ)) ≤ Z ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (by simpa only [hdeltaEq] using hpow.trans hpowRate) (by norm_num)
  have hboundary : 2 * (T : ℝ) / (windowNX X : ℝ) ≤ 2 * R := by
    have hmR : (0 : ℝ) < windowNX X := Nat.cast_pos.mpr hN
    have hTX : (T : ℝ) ≤ Real.log (X : ℝ) := by
      have hTu : (T : ℝ) ≤ u := hTupper.trans (by
        apply div_le_self hu.le
        have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
          have hh := Real.one_sub_inv_le_log_of_pos
            (by norm_num : (0 : ℝ) < 2)
          norm_num at hh
          exact hh
        have hlog2B : Real.log 2 ≤ lb := by
          dsimp only [lb]
          exact Real.log_le_log (by norm_num) (by exact_mod_cast hB)
        nlinarith)
      exact hTu.trans (by simpa only [G, hGeq] using huLeG)
    have hratio : (T : ℝ) / (windowNX X : ℝ) ≤
        Real.log (X : ℝ) ^ 2 /
          (CoreDyadicPrimeCounting.dyadicCountConstant * (X : ℝ)) := by
      apply (div_le_div_iff₀ hmR
        (mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
          (Nat.cast_pos.mpr (by omega : 0 < X)))).2
      have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos
        (by exact_mod_cast (show 1 < X by omega))
      have hm' : CoreDyadicPrimeCounting.dyadicCountConstant * (X : ℝ) ≤
          (windowNX X : ℝ) * Real.log (X : ℝ) := by
        apply (div_le_iff₀ hlogX).mp
        simpa only [seqWindow_nthPrime_card, mul_div_assoc] using hcard
      have hscaled := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg T)
      have hTscaled := mul_le_mul_of_nonneg_right hTX
        (mul_nonneg (Nat.cast_nonneg (windowNX X)) hlogX.le)
      nlinarith
    have hsqrtuLogX : Real.sqrt u ≤ Real.log (X : ℝ) := by
      have hsqrtu : Real.sqrt u ≤ u :=
        (Real.sqrt_le_self_iff).2 (Or.inr (by linarith : 1 ≤ u))
      exact hsqrtu.trans (by simpa only [G, hGeq] using huLeG)
    have hsmall : Real.log (X : ℝ) ^ 2 /
        (CoreDyadicPrimeCounting.dyadicCountConstant * (X : ℝ)) ≤ R := by
      dsimp only [R, generalBlockRate, u, Z, eta]
      apply (div_le_div_iff₀
        (mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
          (Nat.cast_pos.mpr (by omega : 0 < X)))
        (Real.sqrt_pos.mpr hu)).2
      have hc := (div_le_iff₀
        (Nat.cast_pos.mpr (by omega : 0 < X) : (0 : ℝ) < X)).mp hcube
      have hmul := mul_le_mul_of_nonneg_left hsqrtuLogX
        (pow_nonneg (Real.log_nonneg
          (show (1 : ℝ) ≤ (X : ℝ) by exact_mod_cast (show 1 ≤ X by omega))) 2)
      nlinarith
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (hratio.trans hsmall)
        (by norm_num : (0 : ℝ) ≤ 2)
  exact {
    time_pos := hT
    window_pos := hN
    ramp_pos := hdelta
    time_term := by simpa only [T, lb, R] using htime
    rank_term := by simpa only [L, lb, R] using hrank
    insertion_term := by simpa only [eta, T, delta, R] using hinsertion
    boundary_term := by simpa only [T, R] using hboundary
    ramp_term := by simpa only [delta, R] using hramp }

/-! ## The general visible-`D` block discrepancy -/

/-- Uniform in the anchored interval endpoint, but with the actual
arithmetic discrepancy left on the right.  No limit or rate for `D` is an
input. -/
theorem primePositionBlock_discrepancy_general
    (B : ℕ) (hB : 2 ≤ B) {κ c : ℝ}
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ X : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        |generalPrimePositionBlockIntervalMass B X t - t| ≤
          C * (generalPrimeD κ c X + generalBlockRate B κ X) := by
  obtain ⟨A, E, H, hA, hE, hH, hdom⟩ :=
    eventually_primePosition_finitePositiveDomination_general B hB hκ hc
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let C : ℝ := E + A * (8 * (Real.log (B : ℝ) + 1)) +
    E * (Real.log (B : ℝ) + 1) + 4 * H + 4
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdom, eventually_generalBlockScaleBounds B hB hκ]
      with X hdomX hs
  intro t ht0 ht1
  have hfinite := abs_orbitIntervalMass_sub_le hB hs.window_pos hs.time_pos
    hA
    (mul_nonneg hE (_root_.add_nonneg hdomX.1
      (inv_nonneg.mpr (Nat.cast_nonneg _))))
    (mul_nonneg hH (generalBlockEta_pos B κ X).le)
    hdomX.2 ht0 ht1 hs.ramp_pos
  unfold generalPrimePositionBlockIntervalMass
  have htime : A * Real.sqrt (6 / (generalBlockTime B κ X : ℝ)) ≤
      A * (8 * (Real.log (B : ℝ) + 1)) * generalBlockRate B κ X := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs.time_term hA
  have hrank : E * (generalPrimeD κ c X + (profileL κ X : ℝ)⁻¹) ≤
      E * generalPrimeD κ c X +
        E * (Real.log (B : ℝ) + 1) * generalBlockRate B κ X := by
    have hh := mul_le_mul_of_nonneg_left hs.rank_term hE
    nlinarith
  have hinsertion :
      (H * generalBlockEta B κ X) *
          ((2 / generalBlockRamp B κ X) *
            (B ^ generalBlockTime B κ X : ℕ)) ≤
        (4 * H) * generalBlockRate B κ X := by
    have hh := mul_le_mul_of_nonneg_left hs.insertion_term hH
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hD0 := hdomX.1
  have hR0 : 0 ≤ generalBlockRate B κ X := by
    unfold generalBlockRate
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hrest0 : 0 ≤
      A * (8 * (Real.log (B : ℝ) + 1)) +
        E * (Real.log (B : ℝ) + 1) + 4 * H + 4 := by
    positivity
  have hcollect :
      E * generalPrimeD κ c X +
          (A * (8 * (Real.log (B : ℝ) + 1)) +
            E * (Real.log (B : ℝ) + 1) + 4 * H + 4) *
              generalBlockRate B κ X ≤
        C * (generalPrimeD κ c X + generalBlockRate B κ X) := by
    dsimp only [C]
    nlinarith [mul_nonneg hrest0 hD0, mul_nonneg hE hR0]
  have hpre :
      A * Real.sqrt (6 / (generalBlockTime B κ X : ℝ)) +
          E * (generalPrimeD κ c X + (profileL κ X : ℝ)⁻¹) +
          (H * generalBlockEta B κ X) *
            ((2 / generalBlockRamp B κ X) *
              (B ^ generalBlockTime B κ X : ℕ)) +
          2 * (generalBlockTime B κ X : ℝ) / (windowNX X : ℝ) +
          2 * generalBlockRamp B κ X ≤
        E * generalPrimeD κ c X +
          (A * (8 * (Real.log (B : ℝ) + 1)) +
            E * (Real.log (B : ℝ) + 1) + 4 * H + 4) *
              generalBlockRate B κ X := by
    nlinarith [htime, hrank, hinsertion, hs.boundary_term, hs.ramp_term]
  exact hfinite.trans (hpre.trans hcollect)

end

end PrimeGapNormality.Prime.CorePrimeGeneralBlockDiscrepancy
