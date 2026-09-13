import PrimeGapNormality.Prime.CorePrimeGeneralBlockDiscrepancy

/-!
# The two quantitative regimes of the prime block phase error

The original phase error is

`eta = G^(-1/2) + G * B^(-profileL kappa)`.

For `kappa > 1/log B` it has a fixed negative power of `G`.  At equality,
the square-root reserve in the literal ceiling defining `profileL` gives
the exact exponential window stated in the paper.  These are deterministic
profile calculations; no arithmetic discrepancy or distributional input
occurs here.
-/

namespace PrimeGapNormality.Prime.CorePrimeEtaAsymptotics

open Filter Set
open CorePrimeGeneralBlockDiscrepancy
open scoped Topology

noncomputable section

set_option maxHeartbeats 1200000

private theorem log_windowG_atTop :
    Tendsto (fun X : ℕ => Real.log (windowG X)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_windowG_atTop

def strictEtaExponent (B : ℕ) (κ : ℝ) : ℝ :=
  min (1 / 2 : ℝ) (κ * Real.log (B : ℝ) - 1)

theorem strictEtaExponent_pos
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) < κ) :
    0 < strictEtaExponent B κ := by
  have hlb : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hh := (div_lt_iff₀ hlb).mp hκ
  unfold strictEtaExponent
  exact lt_min (by norm_num) (by linarith)

/-! ## Strictly supercritical profiles -/

/-- The literal eta is squeezed between `G^(-1/2)` and twice a fixed
negative power of `G`. -/
theorem eventually_strict_eta_power_bounds
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) < κ) :
    ∀ᶠ X : ℕ in atTop,
      windowG X ^ (-(1 / 2 : ℝ)) ≤ generalBlockEta B κ X ∧
      generalBlockEta B κ X ≤
        2 * windowG X ^ (-strictEtaExponent B κ) := by
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hlb : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hκpos : 0 < κ := (div_pos zero_lt_one hlb).trans hκ
  let gamma : ℝ := κ * Real.log (B : ℝ) - 1
  let alpha : ℝ := strictEtaExponent B κ
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact sub_pos.mpr ((div_lt_iff₀ hlb).mp hκ)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    exact strictEtaExponent_pos B hB hκ
  filter_upwards [tendsto_windowG_atTop.eventually_gt_atTop 1] with X hG1
  let G := windowG X
  let ell := Real.log G
  let L := profileL κ X
  have hG : 0 < G := zero_lt_one.trans hG1
  have hGle : 1 ≤ G := hG1.le
  have hell : 0 ≤ ell := Real.log_nonneg hG1.le
  have hL : κ * ell ≤ (L : ℝ) := by
    dsimp only [L, ell, G]
    exact kappa_log_windowG_le_profileL hκpos.le X
  have hexponent : (1 + gamma) * ell ≤ (L : ℝ) * Real.log (B : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hL hlb.le
    dsimp only [gamma]
    nlinarith
  have hBL : G ^ (1 + gamma) ≤ (B : ℝ) ^ L := by
    rw [Real.rpow_def_of_pos hG]
    calc
      Real.exp (Real.log G * (1 + gamma)) =
          Real.exp ((1 + gamma) * ell) := by
        simp only [ell]
        congr 1
        ring
      _ ≤ Real.exp ((L : ℝ) * Real.log (B : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = (B : ℝ) ^ L := by
        rw [Real.exp_nat_mul, Real.exp_log hBpos]
  have htail : G * ((B : ℝ) ^ L)⁻¹ ≤ G ^ (-gamma) := by
    have hinv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hG _) hBL
    calc
      G * ((B : ℝ) ^ L)⁻¹ ≤ G * (G ^ (1 + gamma))⁻¹ :=
        mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinv) hG.le
      _ = G ^ (-gamma) := by
        rw [Real.rpow_neg hG.le, Real.rpow_add hG, Real.rpow_one]
        field_simp [hG.ne', (Real.rpow_pos_of_pos hG gamma).ne']
  have halphaHalf : alpha ≤ (1 / 2 : ℝ) := by
    dsimp only [alpha, strictEtaExponent]
    exact min_le_left _ _
  have halphaGamma : alpha ≤ gamma := by
    dsimp only [alpha, strictEtaExponent, gamma]
    exact min_le_right _ _
  have hfirst : G ^ (-(1 / 2 : ℝ)) ≤ G ^ (-alpha) :=
    Real.rpow_le_rpow_of_exponent_le hGle (by linarith)
  have hsecond : G ^ (-gamma) ≤ G ^ (-alpha) :=
    Real.rpow_le_rpow_of_exponent_le hGle (by linarith)
  refine ⟨?_, ?_⟩
  · unfold generalBlockEta
    exact le_add_of_nonneg_right
      (mul_nonneg (zero_le_one.trans (crtWindowG_one_le X))
        (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)))
  · dsimp only [generalBlockEta, G, L, alpha]
    exact (_root_.add_le_add hfirst (htail.trans hsecond)).trans_eq
      (by ring)

/-- In the strict regime, `log (1/eta)` is comparable to `log G` with
explicit positive constants depending only on `B,kappa`. -/
theorem strict_log_inv_eta_comparable
    (B : ℕ) (hB : 2 ≤ B) {κ : ℝ}
    (hκ : 1 / Real.log (B : ℝ) < κ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ X : ℕ in atTop,
        c * Real.log (windowG X) ≤
            Real.log ((generalBlockEta B κ X)⁻¹) ∧
        Real.log ((generalBlockEta B κ X)⁻¹) ≤
            C * Real.log (windowG X) := by
  let alpha := strictEtaExponent B κ
  let c := alpha / 2
  let C : ℝ := 1 / 2
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    exact strictEtaExponent_pos B hB hκ
  have hc : 0 < c := by dsimp only [c]; positivity
  have hC : 0 < C := by dsimp only [C]; norm_num
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [eventually_strict_eta_power_bounds B hB hκ,
    log_windowG_atTop.eventually_ge_atTop (2 * Real.log 2 / alpha),
    tendsto_windowG_atTop.eventually_gt_atTop 1] with X hbounds hlarge hG1
  let G := windowG X
  let eta := generalBlockEta B κ X
  change 2 * Real.log 2 / alpha ≤ Real.log G at hlarge
  have hlargeMul : 2 * Real.log 2 ≤ Real.log G * alpha :=
    (div_le_iff₀ halpha).mp hlarge
  have hG : 0 < G := zero_lt_one.trans hG1
  have heta : 0 < eta := generalBlockEta_pos B κ X
  have hupperPos : 0 < 2 * G ^ (-alpha) := by positivity
  have hinvLower := one_div_le_one_div_of_le heta hbounds.2
  have hinvUpper := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hG (-(1 / 2 : ℝ))) hbounds.1
  have hlogLower := Real.log_le_log (inv_pos.mpr hupperPos)
    (by simpa only [one_div] using hinvLower)
  have hlogUpper := Real.log_le_log (inv_pos.mpr heta)
    (by simpa only [one_div] using hinvUpper)
  have hlowerForm : Real.log ((2 * G ^ (-alpha))⁻¹) =
      alpha * Real.log G - Real.log 2 := by
    rw [Real.log_inv, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
    ring
  have hupperForm : Real.log ((G ^ (-(2 : ℝ)⁻¹))⁻¹) =
      (2 : ℝ)⁻¹ * Real.log G := by
    rw [Real.log_inv, Real.log_rpow hG]
    ring
  rw [hlowerForm] at hlogLower
  rw [hupperForm] at hlogUpper
  refine ⟨?_, ?_⟩
  · dsimp only [c]
    exact (by nlinarith only [hlargeMul] : alpha / 2 * Real.log G ≤
      alpha * Real.log G - Real.log 2).trans hlogLower
  · dsimp only [C]
    simpa only [one_div, eta, G] using hlogUpper

/-! ## The critical profile -/

/-- At `kappa=1/log B`, the genuine tail lies in the exact one-ceiling
window claimed in the paper. -/
theorem eventually_critical_tail_exp_bounds
    (B : ℕ) (hB : 2 ≤ B) :
    ∀ᶠ X : ℕ in atTop,
      (B : ℝ)⁻¹ * Real.exp
          (-Real.sqrt (Real.log (B : ℝ) * Real.log (windowG X))) ≤
        windowG X *
          ((B : ℝ) ^ profileL (1 / Real.log (B : ℝ)) X)⁻¹ ∧
      windowG X *
          ((B : ℝ) ^ profileL (1 / Real.log (B : ℝ)) X)⁻¹ ≤
        Real.exp
          (-Real.sqrt (Real.log (B : ℝ) * Real.log (windowG X))) := by
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hlb : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  filter_upwards [tendsto_windowG_atTop.eventually_gt_atTop 1] with X hG1
  let G := windowG X
  let ell := Real.log G
  let lb := Real.log (B : ℝ)
  let a := ell / lb
  let z := Real.sqrt a
  let s := Real.sqrt (lb * ell)
  let L := profileL (1 / lb) X
  have hG : 0 < G := zero_lt_one.trans hG1
  have hell : 0 ≤ ell := Real.log_nonneg hG1.le
  have ha : 0 ≤ a := div_nonneg hell hlb.le
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hroot : lb * z = s := by
    calc
      lb * z = lb * Real.sqrt a := rfl
      _ = (Real.sqrt lb * Real.sqrt lb) * Real.sqrt a := by
        rw [Real.mul_self_sqrt hlb.le]
      _ = Real.sqrt lb * (Real.sqrt lb * Real.sqrt a) := by ring
      _ = Real.sqrt lb * Real.sqrt (lb * a) := by
        rw [Real.sqrt_mul hlb.le]
      _ = Real.sqrt lb * Real.sqrt ell := by
        have haEq : lb * a = ell := by
          dsimp only [a]
          rw [← mul_div_assoc, mul_div_cancel_left₀ ell hlb.ne']
        rw [haEq]
      _ = s := by
        dsimp only [s]
        rw [Real.sqrt_mul hlb.le]
  have harg : (1 / lb) * Real.log G +
      Real.sqrt ((1 / lb) * Real.log G) = a + z := by
    have hquot : (1 / lb) * Real.log G = a := by
      dsimp only [a, ell]
      ring
    rw [hquot]
  have hLlower : a + z ≤ (L : ℝ) := by
    dsimp only [L, profileL]
    rw [harg]
    exact Nat.le_ceil _
  have hLupper : (L : ℝ) ≤ a + z + 1 := by
    dsimp only [L, profileL]
    rw [harg]
    exact (Nat.ceil_lt_add_one (_root_.add_nonneg ha hz)).le
  have hlowerExp : ell + s ≤ (L : ℝ) * lb := by
    have hh := mul_le_mul_of_nonneg_right hLlower hlb.le
    rw [add_mul] at hh
    have haEq : a * lb = ell := by
      dsimp only [a]
      exact div_mul_cancel₀ ell hlb.ne'
    nlinarith [hroot, haEq]
  have hupperExp : (L : ℝ) * lb ≤ ell + s + lb := by
    have hh := mul_le_mul_of_nonneg_right hLupper hlb.le
    rw [add_mul, add_mul, one_mul] at hh
    have haEq : a * lb = ell := by
      dsimp only [a]
      exact div_mul_cancel₀ ell hlb.ne'
    nlinarith [hroot, haEq]
  have htailForm : G * ((B : ℝ) ^ L)⁻¹ =
      Real.exp (ell - (L : ℝ) * lb) := by
    rw [show G = Real.exp ell by
      dsimp only [ell]; exact (Real.exp_log hG).symm,
      show (B : ℝ) ^ L = Real.exp ((L : ℝ) * lb) by
        rw [Real.exp_nat_mul]
        dsimp only [lb]
        rw [Real.exp_log hBpos],
      ← Real.exp_neg]
    rw [← Real.exp_add]
    congr 1 <;> ring
  rw [htailForm]
  constructor
  · rw [show (B : ℝ)⁻¹ = Real.exp (-lb) by
      rw [Real.exp_neg]
      dsimp only [lb]
      rw [Real.exp_log hBpos]]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact Real.exp_le_exp.mpr (by linarith)

/-- Eventually the mesh term `G^(-1/2)` is no larger than the critical
tail.  Hence eta is between the tail and twice the tail. -/
theorem eventually_critical_eta_tail_bounds
    (B : ℕ) (hB : 2 ≤ B) :
    ∀ᶠ X : ℕ in atTop,
      windowG X *
          ((B : ℝ) ^ profileL (1 / Real.log (B : ℝ)) X)⁻¹ ≤
        generalBlockEta B (1 / Real.log (B : ℝ)) X ∧
      generalBlockEta B (1 / Real.log (B : ℝ)) X ≤
        2 * Real.exp
          (-Real.sqrt (Real.log (B : ℝ) * Real.log (windowG X))) ∧
      (B : ℝ)⁻¹ * Real.exp
          (-Real.sqrt (Real.log (B : ℝ) * Real.log (windowG X))) ≤
        generalBlockEta B (1 / Real.log (B : ℝ)) X := by
  have hlb : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  filter_upwards [eventually_critical_tail_exp_bounds B hB,
    log_windowG_atTop.eventually_ge_atTop
      (max (16 * Real.log (B : ℝ)) (4 * Real.log (B : ℝ)))] with X htail hell
  let G := windowG X
  let ell := Real.log G
  let lb := Real.log (B : ℝ)
  let s := Real.sqrt (lb * ell)
  let tail := G * ((B : ℝ) ^ profileL (1 / lb) X)⁻¹
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    exact Real.log_nonneg (crtWindowG_one_le X)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have h16 : 16 * lb ≤ ell := by
    simpa only [ell, G, lb] using (le_max_left _ _).trans hell
  have h4 : 4 * lb ≤ ell := by
    simpa only [ell, G, lb] using (le_max_right _ _).trans hell
  have hsQuarter : s ≤ ell / 4 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨div_nonneg hell0 (by norm_num), ?_⟩
    have hprod := mul_le_mul_of_nonneg_right h16 hell0
    have hsq := Real.sq_sqrt (mul_nonneg hlb.le hell0)
    nlinarith
  have hbaseTail : G ^ (-(1 / 2 : ℝ)) ≤ tail := by
    have hexp : G ^ (-(1 / 2 : ℝ)) = Real.exp (-(ell / 2)) := by
      rw [Real.rpow_def_of_pos
        (zero_lt_one.trans_le (crtWindowG_one_le X))]
      congr 1
      ring
    have hlower := htail.1
    change (B : ℝ)⁻¹ * Real.exp (-s) ≤ tail at hlower
    have hleft : Real.exp (-(ell / 2)) ≤ (B : ℝ)⁻¹ * Real.exp (-s) := by
      rw [show (B : ℝ)⁻¹ = Real.exp (-lb) by
        rw [Real.exp_neg]
        dsimp only [lb]
        rw [Real.exp_log (Nat.cast_pos.mpr (by omega : 0 < B))],
        ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [hexp]
    exact hleft.trans hlower
  have htailUpper : tail ≤ Real.exp (-s) := by
    simpa only [tail, G, lb, s] using htail.2
  have htailLower : (B : ℝ)⁻¹ * Real.exp (-s) ≤ tail := by
    simpa only [tail, G, lb, s] using htail.1
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [tail, generalBlockEta, G, lb]
    exact le_add_of_nonneg_left
      (Real.rpow_nonneg (zero_le_one.trans (crtWindowG_one_le X)) _)
  · change G ^ (-(1 / 2 : ℝ)) + tail ≤ 2 * Real.exp (-s)
    nlinarith
  · unfold generalBlockEta
    exact htailLower.trans (le_add_of_nonneg_left
      (Real.rpow_nonneg (zero_le_one.trans (crtWindowG_one_le X)) _))

/-- At the critical endpoint, `log (1/eta)` is comparable to
`sqrt(log G)`.  The constants are explicit and positive. -/
theorem critical_log_inv_eta_comparable
    (B : ℕ) (hB : 2 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ X : ℕ in atTop,
        c * Real.sqrt (Real.log (windowG X)) ≤
            Real.log ((generalBlockEta B
              (1 / Real.log (B : ℝ)) X)⁻¹) ∧
        Real.log ((generalBlockEta B
              (1 / Real.log (B : ℝ)) X)⁻¹) ≤
            C * Real.sqrt (Real.log (windowG X)) := by
  let lb := Real.log (B : ℝ)
  let c := Real.sqrt lb / 2
  let C := Real.sqrt lb + lb
  have hlb : 0 < lb := by
    dsimp only [lb]
    exact Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [eventually_critical_eta_tail_bounds B hB,
    (Real.tendsto_sqrt_atTop.comp log_windowG_atTop).eventually_ge_atTop
      (max 1 (2 * Real.log 2 / Real.sqrt lb))] with X heta hsqrtLarge
  simp only [Function.comp_apply] at hsqrtLarge
  let G := windowG X
  let ell := Real.log G
  let s := Real.sqrt (lb * ell)
  let eta := generalBlockEta B (1 / lb) X
  have hell : 0 ≤ ell := by
    dsimp only [ell]
    exact Real.log_nonneg (crtWindowG_one_le X)
  have hetaPos : 0 < eta := by
    dsimp only [eta, lb]
    exact generalBlockEta_pos B (1 / Real.log (B : ℝ)) X
  have hsqrtEll1 : 1 ≤ Real.sqrt ell := by
    simpa only [ell, G] using (le_max_left _ _).trans hsqrtLarge
  have hsqrtEllLarge : 2 * Real.log 2 / Real.sqrt lb ≤ Real.sqrt ell := by
    simpa only [ell, G] using (le_max_right _ _).trans hsqrtLarge
  have hsForm : s = Real.sqrt lb * Real.sqrt ell := by
    dsimp only [s]
    exact Real.sqrt_mul hlb.le ell
  have hupperEta : eta ≤ 2 * Real.exp (-s) := by
    simpa only [eta, lb, G, ell, s] using heta.2.1
  have hlowerEta : (B : ℝ)⁻¹ * Real.exp (-s) ≤ eta := by
    simpa only [eta, lb, G, ell, s] using heta.2.2
  have hUpperPos : 0 < 2 * Real.exp (-s) := by positivity
  have hLowerPos : 0 < (B : ℝ)⁻¹ * Real.exp (-s) := by positivity
  have hinvLower := one_div_le_one_div_of_le hetaPos hupperEta
  have hinvUpper := one_div_le_one_div_of_le hLowerPos hlowerEta
  have hlogLower := Real.log_le_log (inv_pos.mpr hUpperPos)
    (by simpa only [one_div] using hinvLower)
  have hlogUpper := Real.log_le_log (inv_pos.mpr hetaPos)
    (by simpa only [one_div] using hinvUpper)
  have hLowerForm : Real.log ((2 * Real.exp (-s))⁻¹) =
      s - Real.log 2 := by
    rw [Real.log_inv, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hUpperForm : Real.log (((B : ℝ)⁻¹ * Real.exp (-s))⁻¹) =
      s + lb := by
    rw [Real.log_inv, Real.log_mul
      (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega))) (Real.exp_pos _).ne',
      Real.log_inv, Real.log_exp]
    dsimp only [lb]
    ring
  rw [hLowerForm] at hlogLower
  rw [hUpperForm] at hlogUpper
  rw [hsForm] at hlogLower hlogUpper
  refine ⟨?_, ?_⟩
  · dsimp only [c]
    have hlower : Real.sqrt lb / 2 * Real.sqrt ell ≤
        Real.sqrt lb * Real.sqrt ell - Real.log 2 := by
      have hsqrtlb : 0 < Real.sqrt lb := Real.sqrt_pos.mpr hlb
      have hmul := (div_le_iff₀ hsqrtlb).mp hsqrtEllLarge
      nlinarith only [hmul]
    exact hlower.trans hlogLower
  · dsimp only [C]
    exact hlogUpper.trans (by
      have hmul := mul_le_mul_of_nonneg_left hsqrtEll1 hlb.le
      nlinarith)

end

end PrimeGapNormality.Prime.CorePrimeEtaAsymptotics
