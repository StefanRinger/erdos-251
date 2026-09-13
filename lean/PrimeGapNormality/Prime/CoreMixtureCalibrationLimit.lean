import PrimeGapNormality.Prime.CoreMixtureCalibrationRate

/-!
# Polynomial-saving absorption for mixture calibration

This is the asymptotic consumer of the coarse `C^2` Janossy bound.  It is
used only on the internal model/main calibration term in the
Kuperberg-to-`D` route; it does not alter the actual arithmetic `D` input.
-/

open Filter Finset
open scoped Classical Topology

namespace PrimeGapNormality.Prime

noncomputable section

theorem tendsto_exp_loglog_pow_four_mul_rpow_neg
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    Tendsto (fun x : ℝ =>
      Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε))
      atTop (nhds 0) := by
  have hfrac : Tendsto
      (fun x : ℝ => Real.log (Real.log x) ^ 4 / Real.log x)
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 (by norm_num)).comp
        Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    simp [mul_one, add_zero]
  have hAfrac : Tendsto
      (fun x : ℝ => A *
        (Real.log (Real.log x) ^ 4 / Real.log x)) atTop (nhds 0) := by
    simpa using hfrac.const_mul A
  have hhalf : 0 < ε / 2 := half_pos hε
  have hle : ∀ᶠ x : ℝ in atTop,
      Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε) ≤
        x ^ (-(ε / 2)) := by
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1)),
      hAfrac.eventually (Metric.ball_mem_nhds (0 : ℝ) hhalf)]
        with x hxexp hball
    have hx0 : 0 < x := (Real.exp_pos _).trans hxexp
    have hlogx : Real.exp 1 < Real.log x :=
      (Real.lt_log_iff_exp_lt hx0).mpr hxexp
    have hlogx0 : 0 < Real.log x := (Real.exp_pos _).trans hlogx
    have hll1 : 1 < Real.log (Real.log x) :=
      (Real.lt_log_iff_exp_lt hlogx0).mpr hlogx
    have hll0 : 0 < Real.log (Real.log x) := zero_lt_one.trans hll1
    have hfrac0 : 0 ≤ Real.log (Real.log x) ^ 4 / Real.log x :=
      div_nonneg (pow_nonneg hll0.le 4) hlogx0.le
    have hlt : A * (Real.log (Real.log x) ^ 4 / Real.log x) < ε / 2 := by
      have hnonneg : 0 ≤ A *
          (Real.log (Real.log x) ^ 4 / Real.log x) := mul_nonneg hA hfrac0
      have habs :
          |A * (Real.log (Real.log x) ^ 4 / Real.log x) - 0| < ε / 2 :=
        hball
      rw [sub_zero, abs_of_nonneg hnonneg] at habs
      exact habs
    have hcmp : A * Real.log (Real.log x) ^ 4 ≤
        (ε / 2) * Real.log x := by
      have hdiv : A * Real.log (Real.log x) ^ 4 / Real.log x < ε / 2 := by
        convert hlt using 1
        field_simp [hlogx0.ne']
      exact ((div_lt_iff₀ hlogx0).mp hdiv).le
    have hLHS : Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε) =
        Real.exp (A * Real.log (Real.log x) ^ 4 - ε * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
      congr 1
      ring
    have hRHS : x ^ (-(ε / 2)) =
        Real.exp (-(ε / 2) * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0]
      ring
    rw [hLHS, hRHS]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx.le _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_rpow_neg_atTop hhalf) hnonneg hle

private theorem eventually_two_loglog_pow_six_le_log_limit :
    ∀ᶠ X : ℕ in atTop,
      2 * Real.log (Real.log (X : ℝ)) ^ 6 ≤ Real.log (X : ℝ) := by
  have hreal :=
    (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 6 (by norm_num)).comp
      Real.tendsto_log_atTop
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simp only [one_mul, add_zero, Function.comp_apply] at hnat
  filter_upwards [eventually_ge_atTop 16,
    hnat.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))]
      with X hX hball
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16)
      (Nat.cast_le.mpr hX))
  have hll : 0 < Real.log (Real.log (X : ℝ)) :=
    zero_lt_one.trans (one_lt_log_log_of_sixteen_le hX)
  have hratio0 : 0 ≤
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) :=
    div_nonneg (pow_nonneg hll.le 6) hlog.le
  have hratio :
      Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) < 1 / 2 := by
    have habs :
        |Real.log (Real.log (X : ℝ)) ^ 6 / Real.log (X : ℝ) - 0| < 1 / 2 :=
      hball
    rw [sub_zero, abs_of_nonneg hratio0] at habs
    exact habs
  have := (div_lt_iff₀ hlog).mp hratio
  linarith

private theorem eventually_log_ge_two :
    ∀ᶠ X : ℕ in atTop, (2 : ℝ) ≤ Real.log (X : ℝ) :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop 2)

theorem small_combination_cost_le_exp
    {κ d0 : ℝ} {X : ℕ} (hfit : ProfileFits κ d0 X)
    (hG2 : (2 : ℝ) ≤ Real.log (X : ℝ)) :
    ((((profileR (profileL κ X) d0 + 1) *
        ((ahlSmall_omega κ X).card + 1) ^
          profileR (profileL κ X) d0 : ℕ) : ℝ)) ^ 2 ≤
      Real.exp (10 * Real.log (Real.log (X : ℝ)) ^ 4) := by
  let r := profileR (profileL κ X) d0
  let S := profileS κ X
  let W := (ahlSmall_omega κ X).card
  let G := Real.log (X : ℝ)
  let ell := Real.log G
  have hGpos : 0 < G := zero_lt_two.trans_le hG2
  have hell1 : 1 < ell := by
    dsimp only [ell, G]
    exact one_lt_log_log_of_sixteen_le hfit.1
  have hell0 : 0 ≤ ell := (zero_lt_one.trans hell1).le
  have hWS : W ≤ S := by
    dsimp only [W, S]
    exact (card_le_card (ahlSmall_omega_subset_windowOmega κ X)).trans_eq
      (windowOmega_card κ X)
  have hS : (S : ℝ) ≤ G ^ 2 := by
    simpa only [S, G] using hfit.2.1
  have hbase : (W : ℝ) + 1 ≤ G ^ 4 := by
    have hW : (W : ℝ) ≤ (S : ℝ) := Nat.cast_le.mpr hWS
    have hGsq1 : G ^ 2 + 1 ≤ G ^ 4 := by nlinarith [sq_nonneg (G ^ 2 - 2)]
    linarith
  have hbasepos : 0 < (W : ℝ) + 1 := by positivity
  have hpowexp : ((W : ℝ) + 1) ^ r =
      Real.exp ((r : ℝ) * Real.log ((W : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbasepos, mul_comm]
  have hlogbase : Real.log ((W : ℝ) + 1) ≤ 4 * ell := by
    have hG4 : 0 < G ^ 4 := pow_pos hGpos 4
    have h := Real.log_le_log hbasepos hbase
    have hlogpow : Real.log (G ^ 4) = 4 * ell := by
      dsimp only [ell]
      rw [Real.log_pow]
      norm_num
    rwa [hlogpow] at h
  have hr : (r : ℝ) ≤ ell ^ 3 := by
    have hr1 := hfit.2.2.1
    dsimp only [r, ell, G]
    norm_num only [Nat.cast_add, Nat.cast_one] at hr1
    linarith
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log ((W : ℝ) + 1) :=
    Real.log_nonneg (by
      have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
      linarith)
  have hrlog : (r : ℝ) * Real.log ((W : ℝ) + 1) ≤ 4 * ell ^ 4 := by
    have hm := mul_le_mul hr hlogbase hlog0 (pow_nonneg hell0 3)
    nlinarith
  have hpow : ((W : ℝ) + 1) ^ r ≤ Real.exp (4 * ell ^ 4) := by
    rw [hpowexp]
    exact Real.exp_le_exp.mpr hrlog
  have hr1exp : (r : ℝ) + 1 ≤ Real.exp (ell ^ 4) := by
    have hr1 := hfit.2.2.1
    have h3le4 : ell ^ 3 ≤ ell ^ 4 := by
      exact pow_le_pow_right₀ hell1.le (by omega : 3 ≤ 4)
    have hexp := Real.add_one_le_exp (ell ^ 4)
    dsimp only [r, ell, G] at hr1 ⊢
    norm_num only [Nat.cast_add, Nat.cast_one] at hr1
    exact hr1.trans (h3le4.trans (le_trans (by linarith) hexp))
  have hC : (((r + 1) * (W + 1) ^ r : ℕ) : ℝ) ≤
      Real.exp (5 * ell ^ 4) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    calc
      ((r : ℝ) + 1) * ((W : ℝ) + 1) ^ r ≤
          Real.exp (ell ^ 4) * Real.exp (4 * ell ^ 4) :=
        mul_le_mul hr1exp hpow (pow_nonneg (by positivity) _)
          (Real.exp_nonneg _)
      _ = Real.exp (5 * ell ^ 4) := by rw [← Real.exp_add]; ring_nf
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _)
    (by simpa only [r, W] using hC) 2
  calc
    ((((profileR (profileL κ X) d0 + 1) *
        ((ahlSmall_omega κ X).card + 1) ^
          profileR (profileL κ X) d0 : ℕ) : ℝ)) ^ 2 ≤
        (Real.exp (5 * ell ^ 4)) ^ 2 := hsq
    _ = Real.exp (10 * ell ^ 4) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (10 * Real.log (Real.log (X : ℝ)) ^ 4) := by
      simp only [ell, G]

private theorem log_two_mul_le_two_log_limit {X : ℕ} (hX : 3 ≤ X) :
    Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
  have hx : 0 < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul (by norm_num) hx.ne']
  have hlog : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (Nat.cast_le.mpr (by omega : 2 ≤ X))
  linarith

/-- The exact summed signed-transform calibration term consumed by the
finite `D(X,1)` comparison. -/
noncomputable def coreMixtureJanossyCalibration (κ d0 : ℝ) (X : ℕ) : ℝ :=
  ∑ K ∈ (ahlSmall_omega κ X).powerset.filter
      (fun K => K.card = profileL κ X),
    |coreJanossyTransform (ahlSmall_omega κ X) (rootedMainTerm X)
          (profileL κ X) (profileR (profileL κ X) d0) K /
          (windowNX X : ℝ) -
      Stopped.janossyTrunc (ahlSmall_omega κ X)
        (finiteRootMixUnnorm X (ahlSmall_window κ X))
        (profileL κ X) (profileR (profileL κ X) d0) K|

/-- The actual unnormalized mixture/main Janossy calibration tends to zero
on the small profiles under Kuperberg.  No free `hcal` occurs in the type. -/
theorem tendsto_coreMixtureJanossyCalibration_of_kuperberg
    (hK : KuperbergConj13) {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    Tendsto (coreMixtureJanossyCalibration κ d0) atTop (nhds 0) := by
  obtain ⟨ε, K, hε, hKpos, hbound⟩ := hK
  have hfirst : Tendsto (fun X : ℕ =>
      24 * (Real.exp (13 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-eulerProdLowerConst))) atTop (nhds 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (13 : ℝ)) (ε := eulerProdLowerConst) (by norm_num)
        eulerProdLowerConst_pos).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hc := h.const_mul (24 : ℝ)
    simpa only [Function.comp_apply, mul_zero] using hc
  have hsecond : Tendsto (fun X : ℕ =>
      16 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-(1 : ℝ)))) atTop (nhds 0) := by
    have h :=
      (tendsto_exp_loglog_pow_four_mul_rpow_neg
        (A := (11 : ℝ)) (ε := (1 : ℝ)) (by norm_num) (by norm_num)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
    have hc := h.const_mul (16 : ℝ)
    simpa only [Function.comp_apply, mul_zero] using hc
  have hupper : Tendsto (fun X : ℕ =>
      24 * (Real.exp (13 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-eulerProdLowerConst)) +
      16 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
        (X : ℝ) ^ (-(1 : ℝ)))) atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hle : ∀ᶠ X : ℕ in atTop,
      coreMixtureJanossyCalibration κ d0 X ≤
        24 * (Real.exp (13 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) +
        16 * (Real.exp (11 * Real.log (Real.log (X : ℝ)) ^ 4) *
          (X : ℝ) ^ (-(1 : ℝ))) := by
    filter_upwards [eventually_coreMixture_small_janossy_calibration_le hκ hd0,
      eventually_profileFits hκ hd0,
      eventually_windowNX_ge_half hε hKpos hbound,
      eventually_log_ge_two,
      eventually_two_loglog_pow_six_le_log_limit]
        with X hfinite hfit hN hG2 hloglog
    let r := profileR (profileL κ X) d0
    let G : ℝ := Real.log (X : ℝ)
    let ell : ℝ := Real.log G
    let δ := coreMixtureRelativeError κ d0 X
    let C : ℝ := (((r + 1) * ((ahlSmall_omega κ X).card + 1) ^ r : ℕ) : ℝ)
    have hX3 : 3 ≤ X := le_trans (by norm_num) hfit.1
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hGpos : 0 < G := by dsimp only [G]; exact zero_lt_two.trans_le hG2
    have hell1 : 1 < ell := by
      dsimp only [ell, G]
      exact one_lt_log_log_of_sixteen_le hfit.1
    have hell0 : 0 ≤ ell := (zero_lt_one.trans hell1).le
    have hδ0 : 0 ≤ δ := by
      dsimp only [δ, coreMixtureRelativeError]
      positivity
    have hC : C ^ 2 ≤ Real.exp (10 * ell ^ 4) := by
      dsimp only [C, r, ell, G]
      exact small_combination_cost_le_exp hfit hG2
    have hlog2 : 0 < Real.log (2 * (X : ℝ)) := by
      have hX3r : (3 : ℝ) ≤ X := by exact_mod_cast hX3
      exact Real.log_pos (by nlinarith)
    have hNpos : 0 < (windowNX X : ℝ) :=
      (div_pos hXpos (mul_pos (by norm_num) hlog2)).trans_le hN
    have hXN : (X : ℝ) / (windowNX X : ℝ) ≤ 4 * G := by
      have hmul : (X : ℝ) ≤
          (windowNX X : ℝ) * (2 * Real.log (2 * (X : ℝ))) :=
        (div_le_iff₀ (mul_pos (by norm_num) hlog2)).mp hN
      have hdiv : (X : ℝ) / (windowNX X : ℝ) ≤
          2 * Real.log (2 * (X : ℝ)) := by
        apply (div_le_iff₀ hNpos).mpr
        nlinarith
      exact hdiv.trans (by
        have := log_two_mul_le_two_log_limit hX3
        dsimp only [G]
        linarith)
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ ell ^ 3 := by
      dsimp only [r, ell, G]
      simpa only [Nat.cast_add, Nat.cast_one] using hfit.2.2.1
    have hrsq : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ell ^ 6 := by
      have hr0 : 0 ≤ ((r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc
        ((r + 1 : ℕ) : ℝ) ^ 2 ≤ (ell ^ 3) ^ 2 :=
          pow_le_pow_left₀ hr0 hr1 2
        _ = ell ^ 6 := by ring
    have hrsqG : ((r + 1 : ℕ) : ℝ) ^ 2 ≤ G ^ 2 := by
      have htwo : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ G :=
        (mul_le_mul_of_nonneg_left hrsq (by norm_num)).trans
          (by simpa only [ell, G] using hloglog)
      have hG1 : 1 ≤ G := (by norm_num : (1 : ℝ) ≤ 2).trans hG2
      exact (le_trans (by linarith)
        (le_self_pow₀ hG1 (by omega : 2 ≠ 0)))
    have hδ : δ ≤ 3 * G ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
        (2 : ℝ) / X := by
      dsimp only [δ, coreMixtureRelativeError, r]
      have hrsq' :
          (profileR (profileL κ X) d0 + 1 : ℝ) ^ 2 ≤ G ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hrsqG
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrsq' (by norm_num))
          (Real.rpow_nonneg (Nat.cast_nonneg X) _)) le_rfl
    have hrate : 2 * δ * (X : ℝ) / (windowNX X : ℝ) ≤ 8 * δ * G := by
      rw [mul_div_assoc]
      calc
        2 * δ * ((X : ℝ) / (windowNX X : ℝ)) ≤ 2 * δ * (4 * G) :=
          mul_le_mul_of_nonneg_left hXN (mul_nonneg (by norm_num) hδ0)
        _ = 8 * δ * G := by ring
    have hδG : 8 * δ * G ≤
        24 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
          16 * G * ((X : ℝ)⁻¹) := by
      have hmul := mul_le_mul_of_nonneg_right hδ
        (show (0 : ℝ) ≤ 8 * G by positivity)
      calc
        8 * δ * G = (8 * G) * δ := by ring
        _ ≤ (8 * G) *
            (3 * G ^ 2 * (X : ℝ) ^ (-eulerProdLowerConst) +
              (2 : ℝ) / X) := by simpa only [mul_comm] using hmul
        _ = 24 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
            16 * G * ((X : ℝ)⁻¹) := by rw [div_eq_mul_inv]; ring
    have hGexp : G = Real.exp ell := by
      dsimp only [ell]
      exact (Real.exp_log hGpos).symm
    have hellle4 : ell ≤ ell ^ 4 :=
      le_self_pow₀ hell1.le (by omega : 4 ≠ 0)
    have hGle : G ≤ Real.exp (ell ^ 4) := by
      rw [hGexp]
      exact Real.exp_le_exp.mpr hellle4
    have hG3 : G ^ 3 ≤ Real.exp (3 * ell ^ 4) := by
      calc
        G ^ 3 ≤ (Real.exp (ell ^ 4)) ^ 3 :=
          pow_le_pow_left₀ hGpos.le hGle 3
        _ = Real.exp (3 * ell ^ 4) := by
          rw [← Real.exp_nat_mul]
          norm_num
    have hexp13 : Real.exp (10 * ell ^ 4) * G ^ 3 ≤
        Real.exp (13 * ell ^ 4) := by
      calc
        Real.exp (10 * ell ^ 4) * G ^ 3 ≤
            Real.exp (10 * ell ^ 4) * Real.exp (3 * ell ^ 4) :=
          mul_le_mul_of_nonneg_left hG3 (Real.exp_nonneg _)
        _ = Real.exp (13 * ell ^ 4) := by rw [← Real.exp_add]; ring_nf
    have hexp11 : Real.exp (10 * ell ^ 4) * G ≤
        Real.exp (11 * ell ^ 4) := by
      calc
        Real.exp (10 * ell ^ 4) * G ≤
            Real.exp (10 * ell ^ 4) * Real.exp (ell ^ 4) :=
          mul_le_mul_of_nonneg_left hGle (Real.exp_nonneg _)
        _ = Real.exp (11 * ell ^ 4) := by rw [← Real.exp_add]; ring_nf
    have hboundRate : C ^ 2 *
        (2 * δ * (X : ℝ) / (windowNX X : ℝ)) ≤
        24 * (Real.exp (13 * ell ^ 4) *
          (X : ℝ) ^ (-eulerProdLowerConst)) +
        16 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
      calc
        C ^ 2 * (2 * δ * (X : ℝ) / (windowNX X : ℝ)) ≤
            Real.exp (10 * ell ^ 4) * (8 * δ * G) :=
          mul_le_mul hC hrate
            (div_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hδ0) hXpos.le) hNpos.le)
            (Real.exp_nonneg _)
        _ ≤ Real.exp (10 * ell ^ 4) *
            (24 * G ^ 3 * (X : ℝ) ^ (-eulerProdLowerConst) +
              16 * G * ((X : ℝ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hδG (Real.exp_nonneg _)
        _ = 24 * (Real.exp (10 * ell ^ 4) * G ^ 3) *
              (X : ℝ) ^ (-eulerProdLowerConst) +
            16 * (Real.exp (10 * ell ^ 4) * G) * ((X : ℝ)⁻¹) := by ring
        _ ≤ 24 * (Real.exp (13 * ell ^ 4) *
              (X : ℝ) ^ (-eulerProdLowerConst)) +
            16 * (Real.exp (11 * ell ^ 4) * ((X : ℝ)⁻¹)) := by
          have hfirstBound :
              24 * (Real.exp (10 * ell ^ 4) * G ^ 3) *
                  (X : ℝ) ^ (-eulerProdLowerConst) ≤
                24 * (Real.exp (13 * ell ^ 4) *
                  (X : ℝ) ^ (-eulerProdLowerConst)) := by
            have hi := mul_le_mul_of_nonneg_right hexp13
              (Real.rpow_nonneg hXpos.le (-eulerProdLowerConst))
            have ho := mul_le_mul_of_nonneg_left hi
              (show (0 : ℝ) ≤ 24 by norm_num)
            simpa only [mul_assoc] using ho
          have hsecondBound :
              16 * (Real.exp (10 * ell ^ 4) * G) * ((X : ℝ)⁻¹) ≤
                16 * (Real.exp (11 * ell ^ 4) * ((X : ℝ)⁻¹)) := by
            have hi := mul_le_mul_of_nonneg_right hexp11
              (inv_nonneg.mpr hXpos.le)
            have ho := mul_le_mul_of_nonneg_left hi
              (show (0 : ℝ) ≤ 16 by norm_num)
            simpa only [mul_assoc] using ho
          exact add_le_add hfirstBound hsecondBound
        _ = 24 * (Real.exp (13 * ell ^ 4) *
              (X : ℝ) ^ (-eulerProdLowerConst)) +
            16 * (Real.exp (11 * ell ^ 4) * (X : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_neg_one]
    have hfinite' : coreMixtureJanossyCalibration κ d0 X ≤
        C ^ 2 * (2 * δ * (X : ℝ) / (windowNX X : ℝ)) := by
      simpa only [coreMixtureJanossyCalibration, C, δ, r] using hfinite
    exact hfinite'.trans (hboundRate.trans_eq (by simp only [ell, G]))
  refine squeeze_zero' ?_ hle hupper
  exact Eventually.of_forall fun X => by
    unfold coreMixtureJanossyCalibration
    exact sum_nonneg fun K _ => abs_nonneg _

end

end PrimeGapNormality.Prime
