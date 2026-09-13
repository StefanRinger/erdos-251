import PrimeGapNormality.Prime.CoreRoundedPowerScaling
import PrimeGapNormality.Prime.GapPolyIntEval
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Integer polynomials of rounded powers

For an integer polynomial `P`, the literal rooted sequence is

`P(round(q^alpha)) - P(0)`.

The rounding error is first normalized by `G^alpha`. A finite univariate
coefficient calculation then separates the degree-`d` term and gives a
uniform compact error bounded by an explicit constant times `G^(-alpha)`.
No scaling or growth assertion is assumed.
-/

namespace PrimeGapNormality.Prime.CoreRoundedPolynomialScaling

open Filter Finset Polynomial
open CoreRoundedPowerScaling
open scoped Topology BigOperators Classical

noncomputable section

/-- Literal integer-valued rooted polynomial of a rounded power. -/
def roundedPolynomialIncrement
    (P : ℤ[X]) (kind : RoundKind) (alpha : ℝ) (q : ℕ) : ℤ :=
  P.eval (roundedPower kind alpha q) - P.eval 0

/-- The corresponding real polynomial with its constant term deleted. -/
def rootedRealPolynomial (P : ℤ[X]) : ℝ[X] :=
  mapIntPoly P - C (P.coeff 0 : ℝ)

theorem roundedPower_nonneg
    (kind : RoundKind) {alpha : ℝ} (halpha : 0 < alpha) (q : ℕ) :
    0 ≤ roundedPower kind alpha q := by
  have hpow : 0 ≤ (q : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg q) _
  cases kind with
  | floor => exact Int.floor_nonneg.mpr hpow
  | ceil => exact Int.ceil_nonneg hpow

theorem roundedPower_zero (kind : RoundKind) {alpha : ℝ} (halpha : 0 < alpha) :
    roundedPower kind alpha 0 = 0 := by
  cases kind <;> simp [roundedPower, Real.zero_rpow halpha.ne']

theorem roundedPolynomialIncrement_zero
    (P : ℤ[X]) (kind : RoundKind) {alpha : ℝ} (halpha : 0 < alpha) :
    roundedPolynomialIncrement P kind alpha 0 = 0 := by
  simp only [roundedPolynomialIncrement, roundedPower_zero kind halpha, sub_self]

/-- Cast the literal integer expression to the rooted real polynomial. -/
theorem roundedPolynomialIncrement_cast
    (P : ℤ[X]) (kind : RoundKind) {alpha : ℝ} (halpha : 0 < alpha) (q : ℕ) :
    (roundedPolynomialIncrement P kind alpha q : ℝ) =
      eval (roundedPower kind alpha q : ℝ) (rootedRealPolynomial P) := by
  let x : ℕ := (roundedPower kind alpha q).toNat
  have hx0 : 0 ≤ roundedPower kind alpha q := roundedPower_nonneg kind halpha q
  have hxZ : (x : ℤ) = roundedPower kind alpha q := by
    dsimp only [x]
    exact Int.toNat_of_nonneg hx0
  have hxR : (x : ℝ) = (roundedPower kind alpha q : ℝ) := by exact_mod_cast hxZ
  have heval : eval (roundedPower kind alpha q : ℝ) (mapIntPoly P) =
      ((P.eval (roundedPower kind alpha q) : ℤ) : ℝ) := by
    simpa only [hxR, hxZ] using eval_mapIntPoly P x
  unfold roundedPolynomialIncrement rootedRealPolynomial
  rw [Int.cast_sub, eval_sub, eval_C, heval, ← Polynomial.coeff_zero_eq_eval_zero]

def lowerCoefficientBound (Q : ℝ[X]) (d : ℕ) (D : ℝ) : ℝ :=
  ∑ i ∈ range d, |Q.coeff i| * D ^ i

theorem lowerCoefficientBound_nonneg
    (Q : ℝ[X]) (d : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ lowerCoefficientBound Q d D := by
  unfold lowerCoefficientBound
  exact sum_nonneg fun i _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hD _)

private theorem power_ratio_le_inverse {G : ℝ} (hG : 1 ≤ G) {i d : ℕ}
    (hid : i < d) : G ^ i / G ^ d ≤ 1 / G := by
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  apply (div_le_div_iff₀ (pow_pos hG0 d) hG0).2
  rw [one_mul, ← pow_succ]
  exact pow_le_pow_right₀ hG (Nat.succ_le_of_lt hid)

/-- Finite univariate scaling estimate. It is stated separately so the
rounding and polynomial errors remain auditable. -/
theorem scaled_eval_sub_leading_abs_le
    (Q : ℝ[X]) (d : ℕ) (hd : Q.natDegree ≤ d)
    {D scale z : ℝ} (hD : 0 ≤ D) (hscale : 1 ≤ scale) (hz : |z| ≤ D) :
    |eval (scale * z) Q / scale ^ d - Q.coeff d * z ^ d| ≤
      lowerCoefficientBound Q d D / scale := by
  have hscale0 : 0 < scale := zero_lt_one.trans_le hscale
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd) (scale * z), sum_range_succ,
    add_div]
  have htop : Q.coeff d * (scale * z) ^ d / scale ^ d =
      Q.coeff d * z ^ d := by
    rw [mul_pow]
    field_simp [pow_ne_zero d hscale0.ne']
  rw [htop, add_sub_cancel_right, lowerCoefficientBound,
    Finset.sum_div, Finset.sum_div]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  have hid : i < d := mem_range.mp hi
  rw [mul_pow]
  have hratio0 : 0 ≤ scale ^ i / scale ^ d :=
    div_nonneg (pow_nonneg hscale0.le _) (pow_nonneg hscale0.le _)
  have hratio := power_ratio_le_inverse hscale hid
  have hzpow : |z ^ i| ≤ D ^ i := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg z) hz i
  calc
    |Q.coeff i * (scale ^ i * z ^ i) / scale ^ d| =
        |Q.coeff i| * |z ^ i| * (scale ^ i / scale ^ d) := by
      rw [abs_div, abs_mul, abs_mul]
      simp only [abs_pow, abs_of_nonneg hscale0.le]
      ring
    _ ≤ (|Q.coeff i| * D ^ i) * (1 / scale) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hzpow (abs_nonneg _)) hratio
        hratio0 (mul_nonneg (abs_nonneg _) (pow_nonneg hD _))
    _ = |Q.coeff i| * D ^ i / scale := by ring

private theorem rootedRealPolynomial_natDegree_le
    (P : ℤ[X]) {d : ℕ} (hd : P.natDegree = d) :
    (rootedRealPolynomial P).natDegree ≤ d := by
  have hmap : (mapIntPoly P).natDegree = d := by
    unfold mapIntPoly
    rw [natDegree_map_eq_of_injective Int.cast_injective, hd]
  unfold rootedRealPolynomial
  exact (natDegree_sub_le _ _).trans (max_le hmap.le (by simp))

private theorem rootedRealPolynomial_coeff_top
    (P : ℤ[X]) {d : ℕ} (hd : P.natDegree = d) (hd0 : d ≠ 0) :
    (rootedRealPolynomial P).coeff d = (P.leadingCoeff : ℝ) := by
  unfold rootedRealPolynomial
  rw [coeff_sub, mapIntPoly_coeff, coeff_C, if_neg hd0, sub_zero,
    ← hd, coeff_natDegree]

/-- One explicit compact error constant. -/
def roundedPolynomialErrorConstant (P : ℤ[X]) (alpha A : ℝ) : ℝ :=
  let d := P.natDegree
  let D := A ^ alpha + 1
  lowerCoefficientBound (rootedRealPolynomial P) d D +
    |(P.leadingCoeff : ℝ)| * (d : ℝ) * D ^ (d - 1)

theorem roundedPolynomialErrorConstant_nonneg
    (P : ℤ[X]) {alpha A : ℝ} (hA : 0 ≤ A) :
    0 ≤ roundedPolynomialErrorConstant P alpha A := by
  unfold roundedPolynomialErrorConstant
  apply add_nonneg
  · exact lowerCoefficientBound_nonneg _ _
      (add_nonneg (Real.rpow_nonneg hA _) zero_le_one)
  · positivity

/-- Quantitative uniform expansion on every fixed compact interval
`0 ≤ q/G ≤ A`. -/
theorem roundedPolynomial_compact_error_le
    (P : ℤ[X]) (kind : RoundKind) {alpha A G : ℝ}
    (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (hA : 0 ≤ A) (hG : 1 ≤ G)
    (q : ℕ) (hq : (q : ℝ) ≤ A * G) :
    |G ^ (-(alpha * (P.natDegree : ℝ))) *
          (roundedPolynomialIncrement P kind alpha q : ℝ) -
        (P.leadingCoeff : ℝ) *
          ((q : ℝ) / G) ^ (alpha * (P.natDegree : ℝ))| ≤
      roundedPolynomialErrorConstant P alpha A * G ^ (-alpha) := by
  let d := P.natDegree
  let Q := rootedRealPolynomial P
  let scale := G ^ alpha
  let x := (roundedPower kind alpha q : ℝ)
  let z := x / scale
  let u := ((q : ℝ) / G) ^ alpha
  let D := A ^ alpha + 1
  have hd : P.natDegree = d := rfl
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact Real.rpow_pos_of_pos hG0 alpha
  have hscaleOne : 1 ≤ scale := by
    dsimp only [scale]
    exact Real.one_le_rpow hG halpha.le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hAG0 : 0 ≤ A * G := mul_nonneg hA hG0.le
  have hqpow : (q : ℝ) ^ alpha ≤ (A * G) ^ alpha :=
    Real.rpow_le_rpow hq0 hq halpha.le
  have hAGpow : (A * G) ^ alpha = A ^ alpha * scale := by
    dsimp only [scale]
    exact Real.mul_rpow hA hG0.le
  rw [hAGpow] at hqpow
  have hround := abs_roundedPower_le_rpow_add_one kind q (alpha := alpha)
  have hxBound : |x| ≤ D * scale := by
    dsimp only [x, D]
    calc
      |(roundedPower kind alpha q : ℝ)| ≤ (q : ℝ) ^ alpha + 1 := hround
      _ ≤ A ^ alpha * scale + 1 := _root_.add_le_add hqpow le_rfl
      _ ≤ (A ^ alpha + 1) * scale := by nlinarith
  have hzBound : |z| ≤ D := by
    dsimp only [z]
    rw [abs_div, abs_of_pos hscalePos]
    exact (div_le_iff₀ hscalePos).2 (by simpa only [mul_comm] using hxBound)
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    exact Real.rpow_nonneg (div_nonneg hq0 hG0.le) alpha
  have hqDiv : (q : ℝ) / G ≤ A := by
    exact (div_le_iff₀ hG0).2 (by simpa only [mul_comm] using hq)
  have huA : u ≤ A ^ alpha := by
    dsimp only [u]
    exact Real.rpow_le_rpow (div_nonneg hq0 hG0.le) hqDiv halpha.le
  have huBound : |u| ≤ D := by
    rw [abs_of_nonneg hu0]
    exact huA.trans (le_add_of_nonneg_right zero_le_one)
  have huEq : u = (q : ℝ) ^ alpha / scale := by
    dsimp only [u, scale]
    exact Real.div_rpow hq0 hG0.le alpha
  have hroundError : |z - u| ≤ G ^ (-alpha) := by
    have hh := abs_roundedPower_sub_rpow_le_one kind alpha q
    have heq : |z - u| =
        |x - (q : ℝ) ^ alpha| / scale := by
      dsimp only [z]
      rw [huEq, ← sub_div, abs_div, abs_of_pos hscalePos]
    rw [heq]
    have hs := div_le_div_of_nonneg_right hh hscalePos.le
    simpa only [scale, one_div, ← Real.rpow_neg hG0.le] using hs
  have hpoly := scaled_eval_sub_leading_abs_le Q d
    (rootedRealPolynomial_natDegree_le P hd) (D := D) (z := z)
    (add_nonneg (Real.rpow_nonneg hA _) zero_le_one) hscaleOne hzBound
  have hlead := abs_pow_sub_pow_le z u d
  have hmax : max |z| |u| ≤ D := max_le hzBound huBound
  have hmax0 : 0 ≤ max |z| |u| :=
    (abs_nonneg z).trans (le_max_left |z| |u|)
  have hpowMax : (max |z| |u|) ^ (d - 1) ≤ D ^ (d - 1) :=
    pow_le_pow_left₀ hmax0 hmax _
  have hleadError :
      |(P.leadingCoeff : ℝ) * z ^ d -
          (P.leadingCoeff : ℝ) * u ^ d| ≤
        (|(P.leadingCoeff : ℝ)| * (d : ℝ) * D ^ (d - 1)) *
          G ^ (-alpha) := by
    rw [← mul_sub, abs_mul]
    have hh := hlead.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hroundError (Nat.cast_nonneg d)) hpowMax
      (pow_nonneg hmax0 _) (by positivity))
    exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (by ring)
  have hscaleInv : 1 / scale = G ^ (-alpha) := by
    dsimp only [scale]
    rw [one_div, ← Real.rpow_neg hG0.le]
  have hpoly' :
      |eval (scale * z) Q / scale ^ d - Q.coeff d * z ^ d| ≤
        lowerCoefficientBound Q d D * G ^ (-alpha) := by
    calc
      |eval (scale * z) Q / scale ^ d - Q.coeff d * z ^ d| ≤
          lowerCoefficientBound Q d D / scale := hpoly
      _ = lowerCoefficientBound Q d D * G ^ (-alpha) := by
        rw [div_eq_mul_inv]
        have hh : scale⁻¹ = G ^ (-alpha) := by
          simpa only [one_div] using hscaleInv
        rw [hh]
  have hQtop : Q.coeff d = (P.leadingCoeff : ℝ) := by
    dsimp only [Q, d]
    exact rootedRealPolynomial_coeff_top P rfl (Nat.ne_of_gt (zero_lt_one.trans_le hdeg))
  have hscaledX : scale * z = x := by
    dsimp only [z]
    field_simp [hscalePos.ne']
  have hscalePow : scale ^ d = G ^ (alpha * (d : ℝ)) := by
    dsimp only [scale]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG0.le]
  have huPow : u ^ d = ((q : ℝ) / G) ^ (alpha * (d : ℝ)) := by
    dsimp only [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hq0 hG0.le)]
  have hcast := roundedPolynomialIncrement_cast P kind halpha q
  have hmainEq :
      G ^ (-(alpha * (d : ℝ))) *
          (roundedPolynomialIncrement P kind alpha q : ℝ) =
        eval (scale * z) Q / scale ^ d := by
    calc
      G ^ (-(alpha * (d : ℝ))) *
          (roundedPolynomialIncrement P kind alpha q : ℝ) =
        G ^ (-(alpha * (d : ℝ))) * eval x Q := by
        rw [hcast]
      _ = eval x Q / G ^ (alpha * (d : ℝ)) := by
        rw [Real.rpow_neg hG0.le, div_eq_mul_inv]
        ring
      _ = eval (scale * z) Q / scale ^ d := by
        rw [hscaledX, hscalePow]
  rw [hmainEq, ← huPow, ← hQtop]
  have hlead' :
      |Q.coeff d * z ^ d - Q.coeff d * u ^ d| ≤
        (|(P.leadingCoeff : ℝ)| * (d : ℝ) * D ^ (d - 1)) *
          G ^ (-alpha) := by
    simpa only [hQtop] using hleadError
  exact (abs_sub_le _ (Q.coeff d * z ^ d) _).trans
    ((_root_.add_le_add hpoly' hlead').trans_eq (by
      unfold roundedPolynomialErrorConstant
      dsimp only [Q, d, D]
      ring))

/-- The explicit compact envelope tends to zero, uniformly over all integer
`q` in the compact physical range. -/
theorem eventually_roundedPolynomial_compact_expansion
    (P : ℤ[X]) (kind : RoundKind) {alpha A : ℝ}
    (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree) (hA : 0 ≤ A) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ G : ℝ in atTop, ∀ q : ℕ,
      (q : ℝ) ≤ A * G →
      |G ^ (-(alpha * (P.natDegree : ℝ))) *
          (roundedPolynomialIncrement P kind alpha q : ℝ) -
        (P.leadingCoeff : ℝ) *
          ((q : ℝ) / G) ^ (alpha * (P.natDegree : ℝ))| < ε := by
  intro ε hε
  have hlim := (_root_.tendsto_rpow_neg_atTop halpha).const_mul
    (roundedPolynomialErrorConstant P alpha A)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_lt_const hε, eventually_ge_atTop (1 : ℝ)]
      with G herr hG
  intro q hq
  exact (roundedPolynomial_compact_error_le P kind halpha hdeg hA hG q hq).trans_lt herr

/-- A concrete linear-growth coefficient. -/
def roundedPolynomialLinearConstant (P : ℤ[X]) (alpha : ℝ) : ℝ :=
  roundedPolynomialErrorConstant P alpha 1 + |(P.leadingCoeff : ℝ)| * 2 ^ P.natDegree

theorem roundedPolynomialLinearConstant_nonneg (P : ℤ[X]) {alpha : ℝ} :
    0 ≤ roundedPolynomialLinearConstant P alpha := by
  unfold roundedPolynomialLinearConstant
  exact add_nonneg (roundedPolynomialErrorConstant_nonneg P (by norm_num)) (by positivity)

/-- The rooted rounded-polynomial sequence has genuine linear growth when
`alpha * natDegree P ≤ 1`. -/
theorem roundedPolynomialIncrement_abs_le_linear
    (P : ℤ[X]) (kind : RoundKind) {alpha : ℝ}
    (halpha : 0 < alpha) (hdeg : 1 ≤ P.natDegree)
    (halphaDeg : alpha * (P.natDegree : ℝ) ≤ 1)
    {q : ℕ} (hq : 1 ≤ q) :
    |(roundedPolynomialIncrement P kind alpha q : ℝ)| ≤
      roundedPolynomialLinearConstant P alpha * (q : ℝ) := by
  let a := alpha * (P.natDegree : ℝ)
  have hqR : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqR
  have herror := roundedPolynomial_compact_error_le P kind halpha
    hdeg (A := (1 : ℝ)) (by norm_num) hqR q (by simp)
  have hInvLe : (q : ℝ) ^ (-alpha) ≤ 1 := by
    rw [Real.rpow_neg hqpos.le]
    exact (inv_le_one₀ (Real.rpow_pos_of_pos hqpos alpha)).2
      (Real.one_le_rpow hqR halpha.le)
  have hC0 := roundedPolynomialErrorConstant_nonneg P (alpha := alpha) (by norm_num : (0 : ℝ) ≤ 1)
  have herror' :
      |(q : ℝ) ^ (-a) * (roundedPolynomialIncrement P kind alpha q : ℝ) -
        (P.leadingCoeff : ℝ)| ≤ roundedPolynomialErrorConstant P alpha 1 := by
    have hh := herror.trans (mul_le_mul_of_nonneg_left hInvLe hC0)
    simpa only [a, one_mul, div_self hqpos.ne', Real.one_rpow, mul_one] using hh
  have hnorm :
      |(q : ℝ) ^ (-a) * (roundedPolynomialIncrement P kind alpha q : ℝ)| ≤
        roundedPolynomialErrorConstant P alpha 1 + |(P.leadingCoeff : ℝ)| := by
    calc
      _ = |((q : ℝ) ^ (-a) * (roundedPolynomialIncrement P kind alpha q : ℝ) -
          (P.leadingCoeff : ℝ)) + (P.leadingCoeff : ℝ)| := by
            congr 1
            ring
      _ ≤ |(q : ℝ) ^ (-a) * (roundedPolynomialIncrement P kind alpha q : ℝ) -
          (P.leadingCoeff : ℝ)| + |(P.leadingCoeff : ℝ)| :=
            abs_add_le _ _
      _ ≤ _ := _root_.add_le_add herror' le_rfl
  have hpow : (q : ℝ) ^ a ≤ (q : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hqR halphaDeg
  have hcancel : (q : ℝ) ^ a * (q : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add hqpos]
    simp
  have hnormEq :
      |(q : ℝ) ^ (-a) * (roundedPolynomialIncrement P kind alpha q : ℝ)| =
        (q : ℝ) ^ (-a) *
          |(roundedPolynomialIncrement P kind alpha q : ℝ)| := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hqpos.le _)]
  rw [hnormEq] at hnorm
  have hrecover := mul_le_mul_of_nonneg_left hnorm
    (Real.rpow_nonneg hqpos.le a)
  rw [← mul_assoc, hcancel, one_mul] at hrecover
  have hp : |(P.leadingCoeff : ℝ)| ≤
      |(P.leadingCoeff : ℝ)| * 2 ^ P.natDegree := by
    have htwo : (1 : ℝ) ≤ 2 ^ P.natDegree := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_left htwo (abs_nonneg (P.leadingCoeff : ℝ))
    simpa only [mul_one] using hh
  have hconst : roundedPolynomialErrorConstant P alpha 1 + |(P.leadingCoeff : ℝ)| ≤
      roundedPolynomialLinearConstant P alpha := by
    unfold roundedPolynomialLinearConstant
    exact _root_.add_le_add le_rfl hp
  calc
    |(roundedPolynomialIncrement P kind alpha q : ℝ)| ≤
        (q : ℝ) ^ a *
          (roundedPolynomialErrorConstant P alpha 1 + |(P.leadingCoeff : ℝ)|) := hrecover
    _ ≤ (q : ℝ) *
          (roundedPolynomialErrorConstant P alpha 1 + |(P.leadingCoeff : ℝ)|) :=
      mul_le_mul_of_nonneg_right hpow
        (add_nonneg hC0 (abs_nonneg _))
    _ ≤ (q : ℝ) * roundedPolynomialLinearConstant P alpha :=
      mul_le_mul_of_nonneg_left hconst (Nat.cast_nonneg q)
    _ = roundedPolynomialLinearConstant P alpha * (q : ℝ) := mul_comm _ _

end

end PrimeGapNormality.Prime.CoreRoundedPolynomialScaling
