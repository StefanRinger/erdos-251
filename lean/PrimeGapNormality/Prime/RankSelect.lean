import PrimeGapNormality.Prime.GapAbel
import PrimeGapNormality.Prime.GapPolynomialPhase
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rank selector for a periodic leading coefficient

Paper (eq:rank): at a maximizer residue `r`, the two-term leading
coefficient `η_r = a_{r,R} + (-1)^R a_{r+1,R}/B` is nonzero. The rank

`j = r + k ⌊(log_B(|η| G^R) - J - r) / k⌋`

satisfies `j ≡ r (mod k)` and

`B^J ≤ |η| G^R B^{-j} < B^{J+k}`.

Eventually `1 ≤ j < L` when `L` is at least `κ log G` with
`κ > R / log B` (AHL clock; equivalently `L ≳ κ' log_B G` with
`κ' > R`, or `D / log B` in place of `R / log B`).

Integer/log rounding only: no primes, no Weyl assembly. `J` may be
`ℤ` or `ℕ`. Paper ranks are 1-based (`r ∈ Icc 1 k`, `1 ≤ j < L`).
Lean deletion index is `j - 1` (see `freeGapPolyPoly_leadingCoeff`).

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:rank), (eq:noncancel);
`GapAbel.maxNorm_twoTerm_ge`;
`GapPolynomialPhase.freeGapPolyPoly_leadingCoeff`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Function Polynomial

set_option maxHeartbeats 800000

noncomputable section

/-! ### Base and logarithm helpers -/

private theorem base_cast_ne_zero {B : ℕ} (hB : 2 ≤ B) : (B : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

private theorem one_lt_base {B : ℕ} (hB : 2 ≤ B) : (1 : ℝ) < B :=
  Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : 1 < 2) hB)

private theorem base_pos {B : ℕ} (hB : 2 ≤ B) : (0 : ℝ) < B :=
  lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_base hB)

private theorem log_base_pos {B : ℕ} (hB : 2 ≤ B) : 0 < Real.log B :=
  Real.log_pos (one_lt_base hB)

private theorem k_pos_real {k : ℕ} (hk : 1 ≤ k) : (0 : ℝ) < k :=
  Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hk)

/-- Paper `log_B x = log x / log B`. -/
noncomputable def logB (B : ℕ) (x : ℝ) : ℝ :=
  Real.log x / Real.log B

theorem logB_eq_logb (B : ℕ) (x : ℝ) : logB B x = Real.logb B x :=
  rfl

theorem logB_mul {B : ℕ} {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logB B (x * y) = logB B x + logB B y := by
  unfold logB
  rw [Real.log_mul hx hy, add_div]

theorem logB_pow (B : ℕ) (x : ℝ) (n : ℕ) :
    logB B (x ^ n) = n * logB B x := by
  unfold logB
  rw [Real.log_pow, mul_div_assoc]

theorem logB_zpow {B : ℕ} (hB : 2 ≤ B) (n : ℤ) :
    logB B ((B : ℝ) ^ n) = n := by
  unfold logB
  rw [← Real.rpow_intCast, Real.log_div_log,
    Real.logb_rpow (base_pos hB) (one_lt_base hB).ne']

theorem logB_mul_pow {B R : ℕ} {η G : ℝ} (hη : η ≠ 0) (hG : 0 < G) :
    logB B (|η| * G ^ R) = logB B |η| + (R : ℝ) * logB B G := by
  have hη0 : |η| ≠ 0 := abs_ne_zero.mpr hη
  have hpow0 : G ^ R ≠ 0 := (pow_pos hG R).ne'
  rw [logB_mul hη0 hpow0, logB_pow]

/-- `a * (log G / log B) = (a / log B) * log G`. `mul_div_assoc` is the
opposite association `a * b / c = a * (b / c)`. -/
private theorem mul_log_div_comm (a Glog Blog : ℝ) :
    a * (Glog / Blog) = a / Blog * Glog := by
  rw [← mul_div_assoc, div_mul_eq_mul_div]

theorem le_logB_iff_zpow_le {B : ℕ} (hB : 2 ≤ B) {n : ℤ} {x : ℝ}
    (hx : 0 < x) : (n : ℝ) ≤ logB B x ↔ (B : ℝ) ^ n ≤ x := by
  unfold logB
  rw [Real.log_div_log, Real.le_logb_iff_rpow_le (one_lt_base hB) hx,
    Real.rpow_intCast]

theorem logB_lt_iff_lt_zpow {B : ℕ} (hB : 2 ≤ B) {n : ℤ} {x : ℝ}
    (hx : 0 < x) : logB B x < n ↔ x < (B : ℝ) ^ n := by
  unfold logB
  rw [Real.log_div_log, Real.logb_lt_iff_lt_rpow (one_lt_base hB) hx,
    Real.rpow_intCast]

/-! ### Integer / natural floor rounding -/

/-- Integer rank rounding: `j = r + k ⌊(x - r)/k⌋` satisfies
`j ≤ x < j + k`. -/
theorem int_rank_bounds {k : ℕ} (hk : 1 ≤ k) (x : ℝ) (r : ℤ) :
    ((r + (k : ℤ) * Int.floor ((x - r) / k) : ℤ) : ℝ) ≤ x ∧
      x < ((r + (k : ℤ) * Int.floor ((x - r) / k) : ℤ) : ℝ) + k := by
  have hkpos := k_pos_real hk
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hcancel : (k : ℝ) * ((x - r) / k) = x - r := mul_div_cancel₀ _ hk0
  have hle : (k : ℝ) * Int.floor ((x - r) / k) ≤ x - r := by
    have := mul_le_mul_of_nonneg_left (Int.floor_le ((x - r) / k)) hkpos.le
    rwa [hcancel] at this
  have hlt : x - r < (k : ℝ) * Int.floor ((x - r) / k) + k := by
    have := mul_lt_mul_of_pos_left (Int.lt_floor_add_one ((x - r) / k)) hkpos
    have hmul :
        (k : ℝ) * ((Int.floor ((x - r) / k) : ℝ) + 1) =
          (k : ℝ) * Int.floor ((x - r) / k) + k := by
      rw [mul_add, mul_one]
    rwa [hcancel, hmul] at this
  have hj :
      ((r + (k : ℤ) * Int.floor ((x - r) / k) : ℤ) : ℝ) =
        (r : ℝ) + (k : ℝ) * Int.floor ((x - r) / k) := by
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  constructor
  · rw [hj]
    linarith
  · rw [hj]
    linarith

/-- Natural rank rounding, valid once `(x - r)/k ≥ 0`. -/
theorem nat_rank_bounds {k r : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 ≤ (x - r) / k) :
    ((r + k * Nat.floor ((x - r) / k) : ℕ) : ℝ) ≤ x ∧
      x < ((r + k * Nat.floor ((x - r) / k) : ℕ) : ℝ) + k := by
  have hkpos := k_pos_real hk
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hcancel : (k : ℝ) * ((x - (r : ℝ)) / k) = x - r :=
    mul_div_cancel₀ _ hk0
  have hle : (k : ℝ) * Nat.floor ((x - r) / k) ≤ x - r := by
    have := mul_le_mul_of_nonneg_left (Nat.floor_le hx) hkpos.le
    rwa [hcancel] at this
  have hlt : x - r < (k : ℝ) * Nat.floor ((x - r) / k) + k := by
    have := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one ((x - r) / k)) hkpos
    have hmul :
        (k : ℝ) * ((Nat.floor ((x - r) / k) : ℝ) + 1) =
          (k : ℝ) * Nat.floor ((x - r) / k) + k := by
      rw [mul_add, mul_one]
    rwa [hcancel, hmul] at this
  have hj :
      ((r + k * Nat.floor ((x - r) / k) : ℕ) : ℝ) =
        (r : ℝ) + (k : ℝ) * Nat.floor ((x - r) / k) := by
    rw [Nat.cast_add, Nat.cast_mul]
  constructor
  · rw [hj]
    linarith
  · rw [hj]
    linarith

/-! ### Periodic two-term coefficient `η_r` -/

/-- Paper `η_r = a_{r,R} + (-1)^R a_{r+1,R}/B`. -/
noncomputable def etaResidue (B R : ℕ) (a : ℕ → ℝ) (r : ℕ) : ℝ :=
  a r + (-1 : ℝ) ^ R * a (r + 1) / B

/-- Paper (eq:noncancel): maximizer residues do not cancel.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:noncancel);
`GapAbel.maxNorm_twoTerm_ge`.
Contract: API
Audit: GREEN -/
theorem abs_etaResidue_ge {B k r R : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) :
    (1 - (1 : ℝ) / B) * |a r| ≤ |etaResidue B R a r| := by
  obtain ⟨hplus, hminus⟩ := maxNorm_twoTerm_ge hB hk a ha hr hmax
  unfold etaResidue
  by_cases hE : Even R
  · have h1 : (-1 : ℝ) ^ R = 1 := Even.neg_one_pow hE
    simpa [h1] using hplus
  · have hO : Odd R := Nat.not_even_iff_odd.mp hE
    have h1 : (-1 : ℝ) ^ R = -1 := Odd.neg_one_pow hO
    have hrew :
        a r + (-1 : ℝ) * a (r + 1) / B = a r - a (r + 1) / B := by
      ring
    rw [h1, hrew]
    exact hminus

theorem etaResidue_ne_zero {B k r R : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) (hM : a r ≠ 0) :
    etaResidue B R a r ≠ 0 := by
  have hfac : 0 < 1 - (1 : ℝ) / B := by
    have hB1 := one_lt_base hB
    have : (1 : ℝ) / B < 1 :=
      (div_lt_one (lt_trans (by norm_num : (0 : ℝ) < 1) hB1)).mpr hB1
    linarith
  have hpos : 0 < (1 - (1 : ℝ) / B) * |a r| :=
    mul_pos hfac (abs_pos.mpr hM)
  have hge := abs_etaResidue_ge (R := R) hB hk a ha hr hmax
  exact abs_pos.mp (hpos.trans_le hge)

/-! ### Rank selector (paper (eq:rank)) -/

/-- Integer form of (eq:rank). Uses `Int.floor`, so `j` may be negative
when `G` is not yet large. -/
noncomputable def rankSelectZ (B k r : ℕ) (η G : ℝ) (R : ℕ) (J : ℤ) : ℤ :=
  (r : ℤ) + (k : ℤ) *
    Int.floor ((logB B (|η| * G ^ R) - (J : ℝ) - r) / k)

/-- Natural form of (eq:rank). Uses `Nat.floor` (zero on negatives).
Agrees with `rankSelectZ` once the floor argument is nonnegative. -/
noncomputable def rankSelect (B k r : ℕ) (η G : ℝ) (R : ℕ) (J : ℤ) : ℕ :=
  r + k * Nat.floor ((logB B (|η| * G ^ R) - (J : ℝ) - r) / k)

theorem rankSelect_natJ (B k r : ℕ) (η G : ℝ) (R J : ℕ) :
    rankSelect B k r η G R (J : ℤ) =
      r + k * Nat.floor ((logB B (|η| * G ^ R) - (J : ℝ) - r) / k) :=
  rfl

theorem rankSelect_modEq {B k r R : ℕ} {η G : ℝ} {J : ℤ} :
    rankSelect B k r η G R J ≡ r [MOD k] := by
  unfold rankSelect Nat.ModEq
  exact Nat.add_mul_mod_self_left r k _

theorem rankSelectZ_modEq {B k r R : ℕ} {η G : ℝ} {J : ℤ} :
    rankSelectZ B k r η G R J ≡ r [ZMOD k] := by
  unfold rankSelectZ
  exact Int.modEq_iff_dvd.mpr ⟨-Int.floor
      ((logB B (|η| * G ^ R) - (J : ℝ) - r) / k), by ring⟩

theorem rankSelect_intModEq {B k r R : ℕ} {η G : ℝ} {J : ℤ} :
    (rankSelect B k r η G R J : ℤ) ≡ r [ZMOD k] :=
  Int.modEq_iff_dvd.mpr (Nat.modEq_iff_dvd.mp rankSelect_modEq)

theorem rankSelect_eq_rankSelectZ {B k r R : ℕ} {η G : ℝ} {J : ℤ}
    (hnn : 0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k) :
    (rankSelect B k r η G R J : ℤ) = rankSelectZ B k r η G R J := by
  unfold rankSelect rankSelectZ
  rw [Int.natCast_add, Int.natCast_mul, Int.natCast_floor_eq_floor hnn]

/-! ### Two-sided `B^J` window -/

private theorem zpow_mul_neg_cancel {B : ℕ} (hB : 2 ≤ B) (J j k : ℤ) :
    (B : ℝ) ^ (J + j) * (B : ℝ) ^ (-j) = (B : ℝ) ^ J ∧
      (B : ℝ) ^ (J + j + k) * (B : ℝ) ^ (-j) = (B : ℝ) ^ (J + k) := by
  have hb0 := base_cast_ne_zero hB
  constructor
  · rw [← zpow_add₀ hb0, add_neg_cancel_right]
  · rw [← zpow_add₀ hb0]
    congr 1
    ring

theorem rankSelectZ_le_log {B k r R : ℕ} {η G : ℝ} {J : ℤ}
    (hk : 1 ≤ k) :
    (rankSelectZ B k r η G R J : ℝ) ≤
      logB B (|η| * G ^ R) - J ∧
        logB B (|η| * G ^ R) - J <
          (rankSelectZ B k r η G R J : ℝ) + k := by
  simpa [rankSelectZ] using
    int_rank_bounds hk (logB B (|η| * G ^ R) - (J : ℝ)) r

theorem rankSelect_le_log {B k r R : ℕ} {η G : ℝ} {J : ℤ}
    (hk : 1 ≤ k)
    (hnn : 0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k) :
    (rankSelect B k r η G R J : ℝ) ≤
      logB B (|η| * G ^ R) - J ∧
        logB B (|η| * G ^ R) - J <
          (rankSelect B k r η G R J : ℝ) + k := by
  simpa [rankSelect] using
    nat_rank_bounds (r := r) hk (x := logB B (|η| * G ^ R) - (J : ℝ)) hnn

/-- Paper (eq:rank) scale window, integer rank. -/
theorem rankSelectZ_scale {B k r R : ℕ} {η G : ℝ} {J : ℤ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hη : η ≠ 0) (hG : 1 < G) :
    (B : ℝ) ^ J ≤
        |η| * G ^ R * (B : ℝ) ^ (-rankSelectZ B k r η G R J) ∧
      |η| * G ^ R * (B : ℝ) ^ (-rankSelectZ B k r η G R J) <
        (B : ℝ) ^ (J + k) := by
  have hGpos : (0 : ℝ) < G := lt_trans (by norm_num : (0 : ℝ) < 1) hG
  have hz : 0 < |η| * G ^ R :=
    mul_pos (abs_pos.mpr hη) (pow_pos hGpos R)
  have hj := rankSelectZ_le_log (B := B) (k := k) (r := r) (R := R)
    (η := η) (G := G) (J := J) hk
  set j := rankSelectZ B k r η G R J
  have hsum : (J : ℝ) + j = ((J + j : ℤ) : ℝ) := by
    rw [Int.cast_add]
  have hsumk : (J : ℝ) + (j : ℝ) + k = ((J + j + k : ℤ) : ℝ) := by
    rw [Int.cast_add, Int.cast_add, Int.cast_natCast]
  have hle : ((J + j : ℤ) : ℝ) ≤ logB B (|η| * G ^ R) := by
    linarith [hj.1, hsum]
  have hlt : logB B (|η| * G ^ R) < ((J + j + k : ℤ) : ℝ) := by
    linarith [hj.2, hsumk]
  have hzpowle := (le_logB_iff_zpow_le hB hz).mp hle
  have hzpowlt := (logB_lt_iff_lt_zpow hB hz).mp hlt
  have hneg : 0 < (B : ℝ) ^ (-j) := zpow_pos (base_pos hB) _
  obtain ⟨hmul1, hmul2⟩ := zpow_mul_neg_cancel hB J j k
  constructor
  · have := mul_le_mul_of_nonneg_right hzpowle hneg.le
    rwa [hmul1] at this
  · have := mul_lt_mul_of_pos_right hzpowlt hneg
    rwa [hmul2] at this

/-- Paper (eq:rank) scale window, natural rank (floor argument `≥ 0`). -/
theorem rankSelect_scale {B k r R : ℕ} {η G : ℝ} {J : ℤ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hη : η ≠ 0) (hG : 1 < G)
    (hnn : 0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k) :
    (B : ℝ) ^ J ≤
        |η| * G ^ R *
          (B : ℝ) ^ (-(rankSelect B k r η G R J : ℤ)) ∧
      |η| * G ^ R *
          (B : ℝ) ^ (-(rankSelect B k r η G R J : ℤ)) <
        (B : ℝ) ^ (J + k) := by
  rw [rankSelect_eq_rankSelectZ hnn]
  exact rankSelectZ_scale hB hk hη hG

theorem rankSelect_scale_natJ {B k r R J : ℕ} {η G : ℝ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hη : η ≠ 0) (hG : 1 < G)
    (hnn : 0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k) :
    (B : ℝ) ^ J ≤
        |η| * G ^ R *
          (B : ℝ) ^ (-(rankSelect B k r η G R (J : ℤ) : ℤ)) ∧
      |η| * G ^ R *
          (B : ℝ) ^ (-(rankSelect B k r η G R (J : ℤ) : ℤ)) <
        (B : ℝ) ^ (J + k) := by
  have h := rankSelect_scale (J := (J : ℤ)) hB hk hη hG hnn
  rw [zpow_natCast] at h
  have hr : (B : ℝ) ^ ((J : ℤ) + k) = (B : ℝ) ^ (J + k) := by
    rw [show (J : ℤ) + k = ((J + k : ℕ) : ℤ) from (Int.natCast_add J k).symm,
      zpow_natCast]
  rwa [hr] at h

/-! ### Membership in `Ico 1 L` -/

theorem rankSelect_mem_Ico {B k r R : ℕ} {η G : ℝ} {J : ℤ} {L : ℕ}
    (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hnn : 0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k)
    (hL : logB B (|η| * G ^ R) - (J : ℝ) < L) :
    rankSelect B k r η G R J ∈ Ico 1 L := by
  have hrcc := mem_Icc.mp hr
  have hj := rankSelect_le_log (B := B) (R := R) (η := η) (G := G)
    (J := J) hk hnn
  have h1 : 1 ≤ rankSelect B k r η G R J := by
    unfold rankSelect
    exact le_trans hrcc.1 (Nat.le_add_right _ _)
  have hlt : (rankSelect B k r η G R J : ℝ) < L :=
    lt_of_le_of_lt hj.1 hL
  exact mem_Ico.mpr ⟨h1, Nat.cast_lt.mp hlt⟩

/-- Explicit `j`-existence at a fixed `G > 1`. -/
theorem exists_rankSelect {B k r R : ℕ} {η G : ℝ} {J : ℤ} {L : ℕ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hη : η ≠ 0) (hG : 1 < G)
    (hnn : 0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k)
    (hL : logB B (|η| * G ^ R) - (J : ℝ) < L) :
    ∃ j ∈ Ico 1 L,
      (j : ℤ) ≡ r [ZMOD k] ∧
        (B : ℝ) ^ J ≤ |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
          |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) < (B : ℝ) ^ (J + k) ∧
            j = rankSelect B k r η G R J := by
  refine ⟨rankSelect B k r η G R J, rankSelect_mem_Ico hk hr hnn hL,
    rankSelect_intModEq, ?_⟩
  obtain ⟨hle, hlt⟩ := rankSelect_scale hB hk hη hG hnn
  exact ⟨hle, hlt, rfl⟩

private theorem rankSelect_floorArg_nonneg_of_log
    {B k r R : ℕ} {η G : ℝ} {J : ℤ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hη : η ≠ 0) (hG : 1 < G) (hR : 1 ≤ R)
    (hlog : ((J : ℝ) + r - logB B |η|) * Real.log B / (R : ℝ) ≤
      Real.log G) :
    0 ≤ (logB B (|η| * G ^ R) - (J : ℝ) - r) / k := by
  have hGpos : (0 : ℝ) < G := lt_trans (by norm_num : (0 : ℝ) < 1) hG
  have hkpos := k_pos_real hk
  have hRpos : (0 : ℝ) < R :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hR)
  have hlogB := log_base_pos hB
  have hnum : 0 ≤ logB B (|η| * G ^ R) - (J : ℝ) - r := by
    have heq := logB_mul_pow (B := B) (R := R) hη hGpos
    have hlogBG : (R : ℝ) * logB B G =
        (R : ℝ) * Real.log G / Real.log B := by
      unfold logB
      rw [mul_div_assoc]
    have hT :
        ((J : ℝ) + r - logB B |η|) * Real.log B / (R : ℝ) * (R : ℝ) /
          Real.log B
          = (J : ℝ) + r - logB B |η| := by
      field_simp [hRpos.ne', hlogB.ne']
    have hle :
        (J : ℝ) + r - logB B |η| ≤
          (R : ℝ) * Real.log G / Real.log B := by
      have hmul := mul_le_mul_of_nonneg_right hlog hRpos.le
      have hdiv := div_le_div_of_nonneg_right hmul hlogB.le
      have hright : Real.log G * (R : ℝ) / Real.log B =
          (R : ℝ) * Real.log G / Real.log B := by
        ring
      rwa [hT, hright] at hdiv
    rw [heq, hlogBG]
    linarith
  exact div_nonneg hnum hkpos.le

private theorem rankSelect_log_sub_J_lt_kappa
    {B R : ℕ} {η G : ℝ} {J : ℤ} {κ : ℝ}
    (_hB : 2 ≤ B) (hη : η ≠ 0) (hG : 1 < G)
    (hκ : (R : ℝ) / Real.log B < κ)
    (hlog : (logB B |η| - (J : ℝ)) /
        (κ - (R : ℝ) / Real.log B) + 1 ≤ Real.log G) :
    logB B (|η| * G ^ R) - (J : ℝ) < κ * Real.log G := by
  have hGpos : (0 : ℝ) < G := lt_trans (by norm_num : (0 : ℝ) < 1) hG
  have hδ : 0 < κ - (R : ℝ) / Real.log B := sub_pos.mpr hκ
  have heq := logB_mul_pow (B := B) (R := R) hη hGpos
  have hlogBG : (R : ℝ) * logB B G =
      (R : ℝ) / Real.log B * Real.log G := by
    unfold logB
    exact mul_log_div_comm _ _ _
  have hrew : (logB B |η| - (J : ℝ)) /
        (κ - (R : ℝ) / Real.log B) + 1 =
      ((logB B |η| - (J : ℝ)) + (κ - (R : ℝ) / Real.log B)) /
        (κ - (R : ℝ) / Real.log B) := by
    field_simp [hδ.ne']
  have hdiv : ((logB B |η| - (J : ℝ)) +
        (κ - (R : ℝ) / Real.log B)) /
      (κ - (R : ℝ) / Real.log B) ≤ Real.log G := by
    rwa [← hrew]
  have hlin : (logB B |η| - (J : ℝ)) +
      (κ - (R : ℝ) / Real.log B) ≤
        (κ - (R : ℝ) / Real.log B) * Real.log G :=
    (div_le_iff₀' hδ).mp hdiv
  have hstrict : logB B |η| - (J : ℝ) <
      (κ - (R : ℝ) / Real.log B) * Real.log G :=
    lt_of_lt_of_le (lt_add_of_pos_right _ hδ) hlin
  have hsum : (κ - (R : ℝ) / Real.log B) * Real.log G +
      (R : ℝ) / Real.log B * Real.log G = κ * Real.log G := by
    ring
  have hshift :
      logB B |η| + (R : ℝ) * logB B G - (J : ℝ) =
        logB B |η| - (J : ℝ) + (R : ℝ) * logB B G := by
    ring
  rw [heq, hshift, hlogBG]
  linarith [hstrict, hsum]

/-- Paper (eq:rank): for all large `G`, a rank `j ≡ r (mod k)` lies in
`Ico 1 L` with the two-sided `B^J` window, whenever `L` is at least
`κ log G` and `κ > R / log B`. -/
theorem exists_rankSelect_in_range {B k r R : ℕ} {η : ℝ} {J : ℤ} {κ : ℝ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hη : η ≠ 0) (hR : 1 ≤ R)
    (hκ : (R : ℝ) / Real.log B < κ) :
    ∃ G₀ : ℝ, ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * Real.log G ≤ (L : ℝ) →
        ∃ j ∈ Ico 1 L,
          (j : ℤ) ≡ r [ZMOD k] ∧
            (B : ℝ) ^ J ≤ |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
              |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) <
                (B : ℝ) ^ (J + k) ∧
                j = rankSelect B k r η G R J := by
  set T_floor :=
    ((J : ℝ) + r - logB B |η|) * Real.log B / (R : ℝ)
  set T_upper :=
    (logB B |η| - (J : ℝ)) / (κ - (R : ℝ) / Real.log B) + 1
  set G₀ := max (2 : ℝ) (max (Real.exp T_floor) (Real.exp T_upper))
  refine ⟨G₀, fun G hGle L hL => ?_⟩
  have h2 : (2 : ℝ) ≤ G :=
    (le_max_left (2 : ℝ) (max (Real.exp T_floor) (Real.exp T_upper))).trans
      hGle
  have hG1 : (1 : ℝ) < G := lt_of_lt_of_le (by norm_num) h2
  have hexp_floor : Real.exp T_floor ≤ G :=
    (le_max_left (Real.exp T_floor) (Real.exp T_upper)).trans
      ((le_max_right (2 : ℝ)
          (max (Real.exp T_floor) (Real.exp T_upper))).trans hGle)
  have hexp_upper : Real.exp T_upper ≤ G :=
    (le_max_right (Real.exp T_floor) (Real.exp T_upper)).trans
      ((le_max_right (2 : ℝ)
          (max (Real.exp T_floor) (Real.exp T_upper))).trans hGle)
  have hGpos : (0 : ℝ) < G := lt_trans (by norm_num : (0 : ℝ) < 1) hG1
  have hlog_floor : T_floor ≤ Real.log G :=
    (Real.le_log_iff_exp_le hGpos).mpr hexp_floor
  have hlog_upper : T_upper ≤ Real.log G :=
    (Real.le_log_iff_exp_le hGpos).mpr hexp_upper
  have hnn := rankSelect_floorArg_nonneg_of_log hB hk hη hG1 hR hlog_floor
  have hltκ := rankSelect_log_sub_J_lt_kappa hB hη hG1 hκ hlog_upper
  have hLt : logB B (|η| * G ^ R) - (J : ℝ) < L :=
    hltκ.trans_le hL
  exact exists_rankSelect hB hk hr hη hG1 hnn hLt

/-- Same eventual range with paper `log_B` clock: `κ > R` and
`L ≥ κ log_B G`. -/
theorem exists_rankSelect_in_range_logB
    {B k r R : ℕ} {η : ℝ} {J : ℤ} {κ : ℝ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hη : η ≠ 0) (hR : 1 ≤ R) (hκ : (R : ℝ) < κ) :
    ∃ G₀ : ℝ, ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * logB B G ≤ (L : ℝ) →
        ∃ j ∈ Ico 1 L,
          (j : ℤ) ≡ r [ZMOD k] ∧
            (B : ℝ) ^ J ≤ |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
              |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) <
                (B : ℝ) ^ (J + k) ∧
                j = rankSelect B k r η G R J := by
  have hlogB := log_base_pos hB
  have hκ' : (R : ℝ) / Real.log B < κ / Real.log B :=
    (div_lt_div_iff_of_pos_right hlogB).mpr hκ
  obtain ⟨G₀, hG₀⟩ :=
    exists_rankSelect_in_range (κ := κ / Real.log B) hB hk hr hη hR hκ'
  refine ⟨G₀, fun G hGle L hL => ?_⟩
  have hL' : (κ / Real.log B) * Real.log G ≤ (L : ℝ) := by
    unfold logB at hL
    have : κ * (Real.log G / Real.log B) = (κ / Real.log B) * Real.log G :=
      mul_log_div_comm _ _ _
    rwa [← this]
  exact hG₀ G hGle L hL'

/-- Nonstrict AHL budget `κ ≥ R / log B`: an additive `O(1)` reserve
absorbs `log_B |η| - J`. -/
theorem exists_rankSelect_in_range_ge
    {B k r R : ℕ} {η : ℝ} {J : ℤ} {κ : ℝ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hη : η ≠ 0) (hR : 1 ≤ R)
    (hκ : (R : ℝ) / Real.log B ≤ κ) :
    ∃ G₀ C : ℝ, 0 < C ∧ ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * Real.log G + C ≤ (L : ℝ) →
        ∃ j ∈ Ico 1 L,
          (j : ℤ) ≡ r [ZMOD k] ∧
            (B : ℝ) ^ J ≤ |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
              |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) <
                (B : ℝ) ^ (J + k) ∧
                j = rankSelect B k r η G R J := by
  let C := abs (logB B |η| - (J : ℝ)) + 1
  let G₀ := max (2 : ℝ)
    (Real.exp (((J : ℝ) + r - logB B |η|) * Real.log B / (R : ℝ)))
  refine ⟨G₀, C, ?hC, ?hmain⟩
  case hC =>
    change 0 < abs (logB B |η| - (J : ℝ)) + 1
    linarith [abs_nonneg (logB B |η| - (J : ℝ))]
  case hmain =>
    intro G hGle L hL
    have h2 : (2 : ℝ) ≤ G := (le_max_left _ _).trans hGle
    have hG1 : (1 : ℝ) < G := lt_of_lt_of_le (by norm_num) h2
    have hGpos : (0 : ℝ) < G := lt_trans (by norm_num : (0 : ℝ) < 1) hG1
    have hexp : Real.exp
        (((J : ℝ) + r - logB B |η|) * Real.log B / (R : ℝ)) ≤ G :=
      (le_max_right _ _).trans hGle
    have hlog : ((J : ℝ) + r - logB B |η|) * Real.log B / (R : ℝ) ≤
        Real.log G :=
      (Real.le_log_iff_exp_le hGpos).mpr hexp
    have hnn := rankSelect_floorArg_nonneg_of_log hB hk hη hG1 hR hlog
    have hltL : logB B (|η| * G ^ R) - (J : ℝ) < L := by
      have heq := logB_mul_pow (B := B) (R := R) hη hGpos
      have hlogBG : (R : ℝ) * logB B G =
          (R : ℝ) / Real.log B * Real.log G := by
        unfold logB
        exact mul_log_div_comm _ _ _
      have hRlog : (R : ℝ) / Real.log B * Real.log G ≤
          κ * Real.log G :=
        mul_le_mul_of_nonneg_right hκ (Real.log_pos hG1).le
      have hshift : logB B |η| - (J : ℝ) <
          abs (logB B |η| - (J : ℝ)) + 1 :=
        (le_abs_self (logB B |η| - (J : ℝ))).trans_lt
          (lt_add_one _)
      have hadd :
          logB B |η| + (R : ℝ) * logB B G - (J : ℝ) =
            logB B |η| - (J : ℝ) + (R : ℝ) * logB B G := by
        ring
      have : logB B (|η| * G ^ R) - (J : ℝ) <
          κ * Real.log G + (abs (logB B |η| - (J : ℝ)) + 1) := by
        rw [heq, hadd, hlogBG]
        linarith [hRlog, hshift]
      exact this.trans_le hL
    exact exists_rankSelect hB hk hr hη hG1 hnn hltL

/-- Degree form: `κ > D / log B` with `R ≤ D`. -/
theorem exists_rankSelect_in_range_degree
    {B k r R D : ℕ} {η : ℝ} {J : ℤ} {κ : ℝ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hη : η ≠ 0) (hR : 1 ≤ R) (hRD : R ≤ D)
    (hκ : (D : ℝ) / Real.log B < κ) :
    ∃ G₀ : ℝ, ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * Real.log G ≤ (L : ℝ) →
        ∃ j ∈ Ico 1 L,
          (j : ℤ) ≡ r [ZMOD k] ∧
            (B : ℝ) ^ J ≤ |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
              |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) <
                (B : ℝ) ^ (J + k) ∧
                j = rankSelect B k r η G R J := by
  have hle : (R : ℝ) / Real.log B ≤ (D : ℝ) / Real.log B :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hRD) (log_base_pos hB).le
  exact exists_rankSelect_in_range hB hk hr hη hR (lt_of_le_of_lt hle hκ)

theorem exists_rankSelect_in_range_natJ {B k r R J : ℕ} {η : ℝ} {κ : ℝ}
    (hB : 2 ≤ B) (hk : 1 ≤ k) (hr : r ∈ Icc 1 k)
    (hη : η ≠ 0) (hR : 1 ≤ R)
    (hκ : (R : ℝ) / Real.log B < κ) :
    ∃ G₀ : ℝ, ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * Real.log G ≤ (L : ℝ) →
        ∃ j ∈ Ico 1 L,
          (j : ℤ) ≡ r [ZMOD k] ∧
            (B : ℝ) ^ (J : ℤ) ≤
              |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
              |η| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) <
                (B : ℝ) ^ ((J : ℤ) + k) ∧
                j = rankSelect B k r η G R (J : ℤ) :=
  exists_rankSelect_in_range hB hk hr hη hR hκ

/-- Maximizer-residue form of the eventual selector. -/
theorem exists_rankSelect_in_range_etaResidue
    {B k r R : ℕ} (hB : 2 ≤ B) (hk : 1 ≤ k)
    (a : ℕ → ℝ) (ha : Periodic a k) (hr : r ∈ Icc 1 k)
    (hmax : ∀ i ∈ Icc 1 k, |a i| ≤ |a r|) (hM : a r ≠ 0)
    (hR : 1 ≤ R) {J : ℤ} {κ : ℝ}
    (hκ : (R : ℝ) / Real.log B < κ) :
    ∃ G₀ : ℝ, ∀ G : ℝ, G₀ ≤ G → ∀ L : ℕ,
      κ * Real.log G ≤ (L : ℝ) →
        ∃ j ∈ Ico 1 L,
          (j : ℤ) ≡ r [ZMOD k] ∧
            (B : ℝ) ^ J ≤
              |etaResidue B R a r| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) ∧
              |etaResidue B R a r| * G ^ R * (B : ℝ) ^ (-(j : ℤ)) <
                (B : ℝ) ^ (J + k) ∧
                j = rankSelect B k r (etaResidue B R a r) G R J :=
  exists_rankSelect_in_range hB hk hr
    (etaResidue_ne_zero hB hk a ha hr hmax hM) hR hκ

/-! ### Free-phase leading coefficient as a `zpow` -/

/-- Rephrase `freeGapPolyPoly_leadingCoeff` with `B^(-(j+1))`.
Paper 1-based rank `j` is Lean index `j - 1`. -/
theorem freeGapPolyPoly_leadingCoeff_zpow (P : ℝ[X]) {B j : ℕ}
    (hB : 2 ≤ B) (hR : 1 ≤ natDegree P) (a c : ℝ) :
    leadingCoeff (freeGapPolyPoly P B j a c)
      = leadingCoeff P * (B : ℝ) ^ (-(j + 1 : ℕ) : ℤ) *
        (1 + (-1 : ℝ) ^ natDegree P / B) := by
  rw [freeGapPolyPoly_leadingCoeff P hB hR a c]
  have : ((B : ℝ) ^ (j + 1))⁻¹ = (B : ℝ) ^ (-(j + 1 : ℕ) : ℤ) := by
    rw [zpow_neg, zpow_natCast]
  rw [this]

theorem freeGapPolyPoly_leadingCoeff_paperIndex (P : ℝ[X]) {B j : ℕ}
    (hB : 2 ≤ B) (hR : 1 ≤ natDegree P) (hj : 1 ≤ j) (a c : ℝ) :
    leadingCoeff (freeGapPolyPoly P B (j - 1) a c)
      = leadingCoeff P * (B : ℝ) ^ (-(j : ℤ)) *
        (1 + (-1 : ℝ) ^ natDegree P / B) := by
  rw [freeGapPolyPoly_leadingCoeff_zpow P hB hR a c]
  simp [Nat.sub_add_cancel hj]

end

end PrimeGapNormality.Prime
