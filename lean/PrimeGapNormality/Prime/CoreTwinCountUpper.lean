import PrimeGapNormality.Prime.CoreRoughTupleCount
import PrimeGapNormality.Prime.CoreRoughSieveBudgetLimits
import PrimeGapNormality.Prime.EarlyRootMx
import PrimeGapNormality.Prime.SingularSeriesTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Unconditional upper bound for prime pairs at distance two

This is the fixed two-dimensional beta-sieve application needed by the
paper's sparse binary example.  It uses the literal shift set `{0,2}`, the
fixed cutoff `floor(X^(1/100))`, beta level `19`, and the already proved
finite rough-tuple count.  No growing-rank slope budget and no prime-pair
density hypothesis occurs here.
-/

namespace PrimeGapNormality.Prime.CoreTwinCountUpper

open Finset Filter
open CoreRoughShiftResidues CoreRoughTupleCount CoreRoughSieveBudget
open CoreRoughSieveBudgetLimits
open scoped Topology Classical BigOperators

noncomputable section

def twinShifts : Finset ℕ := {0, 2}

/-- Number of prime starts `m ≤ X` for which `m+2` is also prime. -/
def twinPrimeStartCount (X : ℕ) : ℕ :=
  ((Ico 1 (X + 1)).filter (fun m ↦ Nat.Prime m ∧ Nat.Prime (m + 2))).card

/-- Fixed positive-power cutoff used only for this two-element tuple. -/
def twinSieveCutoff (X : ℕ) : ℕ :=
  ⌊(X : ℝ) ^ (1 / 100 : ℝ)⌋₊

@[simp] theorem twinShifts_card : twinShifts.card = 2 := by
  simp [twinShifts]

theorem twin_residueCount {p : ℕ} (hp : Nat.Prime p) :
    residueCount twinShifts p = if p = 2 then 1 else 2 := by
  by_cases hp2 : p = 2
  · subst p
    unfold twinShifts residueCount
    rw [Finset.image_insert, Finset.image_singleton]
    have htwo : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [htwo]
    simp
  · rw [if_neg hp2]
    apply residueCount_eq_card_of_lt hp
    · intro n hn
      simp only [twinShifts, mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact hp.pos
      · have hp3 : 3 ≤ p := by
          have hpTwo := hp.two_le
          omega
        omega

/-- The exceptional prime `2` costs exactly the leading factor two; every
odd prime local factor is bounded by the square of the ordinary Euler
factor. -/
theorem twinTupleProduct_le (y : ℕ) (hy : 2 ≤ y) :
    finiteTupleSieveProduct twinShifts y ≤ 2 * eulerProdNat y ^ 2 := by
  unfold finiteTupleSieveProduct eulerProdNat
  rw [← Finset.prod_pow]
  calc
    (∏ p ∈ Nat.primesLE y,
        (1 - (residueCount twinShifts p : ℝ) / (p : ℝ))) ≤
      ∏ p ∈ Nat.primesLE y,
        ((if p = 2 then (2 : ℝ) else 1) * (1 - (p : ℝ)⁻¹) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hpMem
        have hp := Nat.prime_of_mem_primesLE hpMem
        rw [twin_residueCount hp]
        split_ifs with hp2
        · norm_num [hp2]
        · have hp3 : 3 ≤ p := by
            have hpTwo := hp.two_le
            omega
          have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
          have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          exact sub_nonneg.mpr ((div_le_one hpR).mpr htwo)
      · intro p hpMem
        have hp := Nat.prime_of_mem_primesLE hpMem
        rw [twin_residueCount hp]
        by_cases hp2 : p = 2
        · subst p
          norm_num
        · simp only [if_neg hp2]
          have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
          have hsquare : 0 ≤ ((p : ℝ)⁻¹) ^ 2 := sq_nonneg _
          rw [div_eq_mul_inv]
          norm_num only [Nat.cast_ofNat, one_mul]
          nlinarith
    _ = (∏ p ∈ Nat.primesLE y, if p = 2 then (2 : ℝ) else 1) *
          ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) ^ 2 := by
      rw [Finset.prod_mul_distrib]
    _ = 2 * ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) ^ 2 := by
      have htwo : 2 ∈ Nat.primesLE y := Nat.mem_primesLE.mpr ⟨hy, Nat.prime_two⟩
      simp [htwo]

private theorem tendsto_twinSieveCutoff_atTop :
    Tendsto twinSieveCutoff atTop atTop := by
  have hh := tendsto_nat_floor_atTop.comp
    ((_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  exact hh.congr' (Eventually.of_forall fun X ↦ rfl)

private theorem eventually_cutoff_data :
    ∀ᶠ X : ℕ in atTop,
      16 ≤ twinSieveCutoff X ∧
      (1 / 200 : ℝ) * Real.log (X : ℝ) ≤
        Real.log (twinSieveCutoff X : ℝ) ∧
      Real.log ((twinSieveCutoff X : ℝ) + 1 / 2) ≤
        (1 / 80 : ℝ) * Real.log (X : ℝ) ∧
      ((twinSieveCutoff X : ℝ) + 1 / 2) ^ (19 : ℕ) ≤
        (cubeRootLevel X : ℝ) := by
  have hX := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hX
  have hpow := (_root_.tendsto_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 100)).comp hX
  filter_upwards [tendsto_twinSieveCutoff_atTop.eventually_ge_atTop 16,
    hpow.eventually_ge_atTop 4,
    hlog.eventually_ge_atTop (400 * Real.log 2),
    eventually_log_cubeRootLevel_ge,
    eventually_ge_atTop (2 : ℕ),
    tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1]
      with X hy hroot hlogLarge hRlog hX2 hRnat
  simp only [Function.comp_apply] at hroot hlogLarge
  have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hlogX0 : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogTwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let t : ℝ := (X : ℝ) ^ (1 / 100 : ℝ)
  change 4 ≤ t at hroot
  have ht0 : 0 < t := Real.rpow_pos_of_pos hX0 _
  have hyUpper : (twinSieveCutoff X : ℝ) ≤ t := by
    exact Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have hfloor := Nat.lt_floor_add_one t
  have hyLower : t / 2 ≤ (twinSieveCutoff X : ℝ) := by
    change t < (twinSieveCutoff X : ℝ) + 1 at hfloor
    linarith
  have hyPos : (0 : ℝ) < twinSieveCutoff X := by exact_mod_cast (by omega : 0 < twinSieveCutoff X)
  have hlogt : Real.log t = (1 / 100 : ℝ) * Real.log (X : ℝ) := by
    dsimp only [t]
    rw [Real.log_rpow hX0]
  have hlogLowerRaw := Real.log_le_log (div_pos ht0 (by norm_num)) hyLower
  rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0), hlogt] at hlogLowerRaw
  have hlogLower : (1 / 200 : ℝ) * Real.log (X : ℝ) ≤
      Real.log (twinSieveCutoff X : ℝ) := by
    nlinarith [hlogTwo0, hlogX0.le]
  have hZUpper : (twinSieveCutoff X : ℝ) + 1 / 2 ≤ 2 * t := by
    linarith
  have hZpos : 0 < (twinSieveCutoff X : ℝ) + 1 / 2 := by positivity
  have hlogZRaw := Real.log_le_log hZpos hZUpper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne', hlogt] at hlogZRaw
  have hlogUpper : Real.log ((twinSieveCutoff X : ℝ) + 1 / 2) ≤
      (1 / 80 : ℝ) * Real.log (X : ℝ) := by
    nlinarith [hlogTwo0, hlogX0.le]
  have hRpos : 0 < (cubeRootLevel X : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hlevel : ((twinSieveCutoff X : ℝ) + 1 / 2) ^ (19 : ℕ) ≤
      (cubeRootLevel X : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos hZpos _) hRpos).mp
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [hlogX0.le]
  exact ⟨hy, hlogLower, hlogUpper, hlevel⟩

private theorem eventually_power_error_bounds :
    ∀ᶠ X : ℕ in atTop,
      (twinSieveCutoff X : ℝ) ≤
          (X : ℝ) / Real.log (X : ℝ) ^ 2 ∧
      (cubeRootLevel X : ℝ) * (1 + Real.log (cubeRootLevel X : ℝ)) ≤
          2 * ((X : ℝ) / Real.log (X : ℝ) ^ 2) := by
  have hlog2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 99 / 100)).eventuallyLE
  have hlog3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 2 / 3)).eventuallyLE
  have hX := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hX
  filter_upwards [hX.eventually hlog2, hX.eventually hlog3,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop (2 : ℕ),
    tendsto_cubeRootLevel_atTop.eventually_ge_atTop 1]
      with X h2 h3 hlog1 hX2 hRnat
  simp only [Function.comp_apply] at hlog1
  have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hlog0 : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlog1
  have h2' : Real.log (X : ℝ) ^ 2 ≤ (X : ℝ) ^ (99 / 100 : ℝ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_ofNat,
      abs_of_nonneg (sq_nonneg (Real.log (X : ℝ))),
      abs_of_nonneg (Real.rpow_nonneg hX0.le (99 / 100 : ℝ))] using h2
  have h3' : Real.log (X : ℝ) ^ 3 ≤ (X : ℝ) ^ (2 / 3 : ℝ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_ofNat,
      abs_of_nonneg (pow_nonneg hlog0.le (3 : ℕ)),
      abs_of_nonneg (Real.rpow_nonneg hX0.le (2 / 3 : ℝ))] using h3
  have hy : (twinSieveCutoff X : ℝ) ≤ (X : ℝ) ^ (1 / 100 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have hsplit1 : (X : ℝ) ^ (1 / 100 : ℝ) *
      (X : ℝ) ^ (99 / 100 : ℝ) = (X : ℝ) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hyTarget : (X : ℝ) ^ (1 / 100 : ℝ) ≤
      (X : ℝ) / Real.log (X : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlog0)).mpr
    calc
      (X : ℝ) ^ (1 / 100 : ℝ) * Real.log (X : ℝ) ^ 2 ≤
          (X : ℝ) ^ (1 / 100 : ℝ) * (X : ℝ) ^ (99 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg hX0.le _)
      _ = (X : ℝ) := hsplit1
  have hR : (cubeRootLevel X : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have hRpos : 0 < (cubeRootLevel X : ℝ) :=
    Nat.cast_pos.mpr (Nat.zero_lt_of_lt hRnat)
  have hlogR : Real.log (cubeRootLevel X : ℝ) ≤ Real.log (X : ℝ) := by
    have hRX : (cubeRootLevel X : ℝ) ≤ X := hR.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ X by omega)) (by norm_num : (1 / 3 : ℝ) ≤ 1))
    exact Real.log_le_log hRpos hRX
  have hlogFactor : 1 + Real.log (cubeRootLevel X : ℝ) ≤
      2 * Real.log (X : ℝ) := by linarith
  have hlogFactor0 : 0 ≤ 1 + Real.log (cubeRootLevel X : ℝ) := by
    have hlogR0 : 0 ≤ Real.log (cubeRootLevel X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hRnat)
    linarith
  have hsplit2 : (X : ℝ) ^ (1 / 3 : ℝ) *
      (X : ℝ) ^ (2 / 3 : ℝ) = (X : ℝ) := by
    rw [← Real.rpow_add hX0]
    norm_num
  have hRTarget : (cubeRootLevel X : ℝ) *
      (1 + Real.log (cubeRootLevel X : ℝ)) ≤
        2 * ((X : ℝ) / Real.log (X : ℝ) ^ 2) := by
    have hfirst := mul_le_mul hR hlogFactor hlogFactor0
      (Real.rpow_nonneg hX0.le _)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hlog0)).mpr
    calc
      (cubeRootLevel X : ℝ) * (1 + Real.log (cubeRootLevel X : ℝ)) *
          Real.log (X : ℝ) ^ 2 ≤
        ((X : ℝ) ^ (1 / 3 : ℝ) * (2 * Real.log (X : ℝ))) *
          Real.log (X : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hfirst (sq_nonneg _)
      _ = 2 * (X : ℝ) ^ (1 / 3 : ℝ) * Real.log (X : ℝ) ^ 3 := by ring
      _ ≤ 2 * (X : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left h3' (by positivity)
      _ = 2 * (X : ℝ) := by rw [mul_assoc, hsplit2]
  exact ⟨hy.trans hyTarget, hRTarget⟩

private theorem primePair_subset_rough (X y : ℕ) :
    (Ico 1 (X + 1)).filter (fun m ↦ Nat.Prime m ∧ Nat.Prime (m + 2)) ⊆
      range (y + 1) ∪ translatedRoughInterval twinShifts y 1 X := by
  intro m hm
  have hmI := mem_Ico.mp (mem_filter.mp hm).1
  have hmprime := (mem_filter.mp hm).2
  by_cases hmy : m ≤ y
  · exact mem_union_left _ (mem_range.mpr (by omega))
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨hmI.1, by omega⟩, ?_⟩
    intro h hh
    simp only [twinShifts, mem_insert, mem_singleton] at hh
    rcases hh with rfl | rfl
    · refine ⟨hmI.1, ?_⟩
      intro p hp hdvd
      have hpm : p = m := (Nat.prime_dvd_prime_iff_eq hp hmprime.1).mp hdvd
      rw [hpm]
      exact lt_of_not_ge hmy
    · refine ⟨by omega, ?_⟩
      intro p hp hdvd
      have hpm : p = m + 2 := (Nat.prime_dvd_prime_iff_eq hp hmprime.2).mp hdvd
      rw [hpm]
      omega

/-- Fully unconditional real upper bound `O(X/log² X)` for prime pairs at
distance two. -/
theorem twinPrimeStartCount_isBigO :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X : ℕ in atTop,
      (twinPrimeStartCount X : ℝ) ≤
        A * ((X : ℝ) / Real.log (X : ℝ) ^ 2) := by
  let A : ℝ := 2 + 80000 * (1 + Real.exp 598) + 2 * Real.exp 20
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  filter_upwards [eventually_cutoff_data, eventually_power_error_bounds,
    eventually_ge_atTop (2 : ℕ)] with X hcut hpower hX2
  let y := twinSieveCutoff X
  let R : ℝ := cubeRootLevel X
  let target : ℝ := (X : ℝ) / Real.log (X : ℝ) ^ 2
  have hroughError := translatedRoughInterval_error_half twinShifts
    (by simp [twinShifts]) hcut.1
      (by simpa only [twinShifts_card, Nat.reduceMul, Nat.reduceAdd] using hcut.2.2.2)
      1 X (by omega)
  have hprod := twinTupleProduct_le y (by omega)
  have hV := earlyMx_V_le_inv_log (show 2 ≤ y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos
    (Nat.one_lt_cast.mpr (by omega))
  have hprodTarget : finiteTupleSieveProduct twinShifts y ≤
      80000 / Real.log (X : ℝ) ^ 2 := by
    have hsquare := pow_le_pow_left₀ (eulerProdNat_pos y).le hV 2
    have hlogcomp := hcut.2.1
    have hlogXpos : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (1 / 200) * Real.log (X : ℝ))
      hlogcomp 2
    calc
      finiteTupleSieveProduct twinShifts y ≤ 2 * eulerProdNat y ^ 2 := hprod
      _ ≤ 2 * (1 / Real.log (y : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by norm_num)
      _ = 2 / Real.log (y : ℝ) ^ 2 := by ring
      _ ≤ 80000 / Real.log (X : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogy) (sq_pos_of_pos hlogXpos)]
        nlinarith
  have hratio0 : 0 ≤ Real.log R / Real.log ((y : ℝ) + 1 / 2) := by
    have hR1 : 1 ≤ R := by
      have hZ1 : (1 : ℝ) ≤ (y : ℝ) + 1 / 2 := by
        have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hcut.1
        linarith
      exact (one_le_pow₀ hZ1).trans hcut.2.2.2
    exact div_nonneg (Real.log_nonneg hR1) (Real.log_nonneg (by nlinarith [show (16 : ℝ) ≤ y by exact_mod_cast hcut.1]))
  have hexp : Real.exp (598 - Real.log R / Real.log ((y : ℝ) + 1 / 2)) ≤
      Real.exp 598 := Real.exp_le_exp.mpr (by linarith)
  have hrough : ((translatedRoughInterval twinShifts y 1 X).card : ℝ) ≤
      (X : ℝ) * finiteTupleSieveProduct twinShifts y * (1 + Real.exp 598) +
        Real.exp 20 * R * (1 + Real.log R) := by
    have hu := (le_abs_self _).trans hroughError
    have hu' : ((translatedRoughInterval twinShifts y 1 X).card : ℝ) ≤
        (X : ℝ) * finiteTupleSieveProduct twinShifts y +
          ((X : ℝ) * finiteTupleSieveProduct twinShifts y *
              Real.exp (598 - Real.log R / Real.log ((y : ℝ) + 1 / 2)) +
            Real.exp 20 * R * (1 + Real.log R)) := by
      norm_num only [twinShifts_card, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hu
      change ((translatedRoughInterval twinShifts y 1 X).card : ℝ) -
          (X : ℝ) * finiteTupleSieveProduct twinShifts y ≤
        (X : ℝ) * finiteTupleSieveProduct twinShifts y *
            Real.exp (598 - Real.log R / Real.log ((y : ℝ) + 1 / 2)) +
          Real.exp 20 * R * (1 + Real.log R) at hu
      linarith
    have hmain0 := mul_nonneg (Nat.cast_nonneg X) (finiteTupleSieveProduct_nonneg twinShifts y)
    have hscale := mul_le_mul_of_nonneg_left hexp hmain0
    nlinarith
  have hpair := card_le_card (primePair_subset_rough X y)
  have hcardUnion := card_union_le (range (y + 1)) (translatedRoughInterval twinShifts y 1 X)
  have hpairNat : twinPrimeStartCount X ≤
      (y + 1) + (translatedRoughInterval twinShifts y 1 X).card := by
    simpa only [twinPrimeStartCount, card_range] using hpair.trans hcardUnion
  have hpairR : (twinPrimeStartCount X : ℝ) ≤
      (y + 1 : ℕ) + (translatedRoughInterval twinShifts y 1 X).card := by
    exact_mod_cast hpairNat
  have hmainTarget : (X : ℝ) * finiteTupleSieveProduct twinShifts y *
      (1 + Real.exp 598) ≤ 80000 * (1 + Real.exp 598) * target := by
    have hh := mul_le_mul_of_nonneg_right hprodTarget
      (mul_nonneg (Nat.cast_nonneg X) (by positivity : 0 ≤ 1 + Real.exp 598))
    calc
      (X : ℝ) * finiteTupleSieveProduct twinShifts y * (1 + Real.exp 598) =
          finiteTupleSieveProduct twinShifts y *
            ((X : ℝ) * (1 + Real.exp 598)) := by ring
      _ ≤ (80000 / Real.log (X : ℝ) ^ 2) *
          ((X : ℝ) * (1 + Real.exp 598)) := hh
      _ = 80000 * (1 + Real.exp 598) * target := by
        dsimp only [target]
        ring
  have haddTarget : Real.exp 20 * R * (1 + Real.log R) ≤
      2 * Real.exp 20 * target := by
    have hh := mul_le_mul_of_nonneg_left hpower.2 (Real.exp_pos 20).le
    dsimp only [R, target]
    nlinarith
  have hyTarget : ((y + 1 : ℕ) : ℝ) ≤ target + 1 := by
    push_cast
    exact _root_.add_le_add hpower.1 le_rfl
  have htarget1 : (1 : ℝ) ≤ target := by
    have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hcut.1
    dsimp only [target]
    nlinarith [hpower.1]
  dsimp only [A]
  nlinarith

end

end PrimeGapNormality.Prime.CoreTwinCountUpper
