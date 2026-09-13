import PrimeGapNormality.Prime.CoreTwinGapDensity
import PrimeGapNormality.Prime.KuperbergAHL
import PrimeGapNormality.Prime.SingularSeriesTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Twin-prime infinitude from the literal Kuperberg hypothesis

This file specializes `KuperbergConj13` to the fixed admissible tuple
`{0,2}`.  Its singular series is proved positive from the finite-prefix /
controlled-tail factorization.  A two-dimensional dyadic logarithmic
integral then dominates Kuperberg's power-saving error.  Thus the
conclusion is not obtained from a separately assumed twin-prime
conjecture.
-/

namespace PrimeGapNormality.Prime.CoreTwinInfinitude

open Finset Filter Asymptotics MeasureTheory
open CoreTwinCountUpper
open scoped Topology Classical BigOperators

noncomputable section

private theorem twin_residueCount {p : ℕ} (hp : Nat.Prime p) :
    residueCount twinShifts p = if p = 2 then 1 else 2 :=
  CoreTwinCountUpper.twin_residueCount hp

/-- The actual two-shift tuple used by the binary example is admissible. -/
theorem twinShifts_hlAdmissible : hlAdmissible twinShifts := by
  intro p hp
  rw [twin_residueCount hp]
  split_ifs with hp2
  · subst p
    norm_num
  · have hp3 : 3 ≤ p := by
      have hp2 := hp.two_le
      omega
    omega

private theorem localHLFactor_twin_pos {p : ℕ} (hp : Nat.Prime p) :
    0 < localHLFactor twinShifts p := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hres : (residueCount twinShifts p : ℝ) < p := by
    exact_mod_cast twinShifts_hlAdmissible p hp
  have hnum : 0 < 1 - (residueCount twinShifts p : ℝ) / p := by
    exact sub_pos.mpr ((div_lt_one hpR).2 hres)
  have hden : 0 < (1 - 1 / (p : ℝ)) ^ twinShifts.card := by
    have hone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact pow_pos (sub_pos.mpr ((div_lt_one hpR).2 hone)) _
  rw [localHLFactor, if_neg (not_le.mpr hp.one_lt)]
  exact div_pos hnum hden

/-- The literal infinite Hardy--Littlewood singular series of `{0,2}`
is strictly positive. -/
theorem twinShifts_singularSeries_pos : 0 < singularSeries twinShifts := by
  have hE : ∀ n ∈ twinShifts, n ≤ 2 := by
    intro n hn
    simp only [twinShifts, mem_insert, mem_singleton] at hn
    omega
  have heq := singularSeries_eq_prefix_mul_tail (E := twinShifts)
    (S := 2) (y := 8) hE (by norm_num) (by simp [twinShifts])
  have htail := singularSeriesTail_tprod_bounds (E := twinShifts)
    (S := 2) (y := 8) hE (by norm_num) (by simp [twinShifts]) (by norm_num)
  rw [heq]
  apply mul_pos
  · apply prod_pos
    intro p hpMem
    exact localHLFactor_twin_pos (Nat.prime_of_mem_primesLE hpMem)
  · have hlower : (0 : ℝ) < 1 - (twinShifts.card : ℝ) ^ 2 / 8 := by
      norm_num [twinShifts]
    exact hlower.trans_le htail.1

/-- The dyadic increment of the two-dimensional logarithmic integral
has its elementary monotonicity lower bound. -/
theorem hlIntegral_two_dyadic_ge {X : ℕ} (hX : 3 ≤ X) :
    (X : ℝ) / Real.log (2 * (X : ℝ)) ^ 2 ≤
      hlIntegral (2 * X : ℝ) 2 - hlIntegral (X : ℝ) 2 := by
  have h2X : 2 ≤ (X : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hX)
  have hab : (X : ℝ) ≤ 2 * (X : ℝ) := by linarith
  have hb : 2 ≤ 2 * (X : ℝ) := by linarith
  have hcast : (2 * X : ℝ) = 2 * (X : ℝ) := by simp
  rw [hcast, hlIntegral_sub 2 h2X hab]
  have h1X : 1 < 2 * (X : ℝ) := by
    have : (1 : ℝ) < X := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hX)
    linarith
  have hlog : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h1X
  have hf : IntervalIntegrable (fun t => Real.log t ^ (-(2 : ℝ))) volume
      (X : ℝ) (2 * (X : ℝ)) := by
    simpa using hlIntegrand_intervalIntegrable 2 h2X hb
  have hg : IntervalIntegrable
      (fun _ : ℝ => (Real.log (2 * (X : ℝ)) ^ 2)⁻¹) volume
      (X : ℝ) (2 * (X : ℝ)) := intervalIntegrable_const
  have hpoint : ∀ t ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)),
      (Real.log (2 * (X : ℝ)) ^ 2)⁻¹ ≤ Real.log t ^ (-(2 : ℝ)) := by
    intro t ht
    have ht2 : 2 ≤ t := h2X.trans ht.1
    have ht1 : 1 < t := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht2
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hle : Real.log t ≤ Real.log (2 * (X : ℝ)) :=
      Real.log_le_log (zero_lt_one.trans ht1) ht.2
    rw [Real.rpow_neg hlogt.le, Real.rpow_two]
    exact inv_anti₀ (pow_pos hlogt 2) (pow_le_pow_left₀ hlogt.le hle 2)
  have hmono := intervalIntegral.integral_mono_on hab hg hf hpoint
  have hconst :
      (∫ t in (X : ℝ)..(2 * (X : ℝ)),
          (Real.log (2 * (X : ℝ)) ^ 2)⁻¹) =
        (2 * (X : ℝ) - (X : ℝ)) *
          (Real.log (2 * (X : ℝ)) ^ 2)⁻¹ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hrewrite :
      (X : ℝ) * (Real.log (2 * (X : ℝ)) ^ 2)⁻¹ =
        (X : ℝ) / Real.log (2 * (X : ℝ)) ^ 2 := by
    rw [div_eq_mul_inv]
  rw [hconst] at hmono
  have hsub : 2 * (X : ℝ) - (X : ℝ) = (X : ℝ) := by ring
  rwa [hsub, hrewrite] at hmono

/-- The fixed pair fits the two elementary size side conditions in
`KuperbergConj13`. -/
def TwinHLFit (X : ℕ) : Prop :=
  16 ≤ X ∧
    (2 : ℝ) ≤ Real.log (X : ℝ) ^ 2 ∧
    (2 : ℝ) ≤ Real.log (Real.log (X : ℝ)) ^ 3

theorem eventually_twinHLFit : ∀ᶠ X : ℕ in atTop, TwinHLFit X := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hloglog : Tendsto (fun X : ℕ => Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_ge_atTop (16 : ℕ), hlog.eventually_ge_atTop 2,
    hloglog.eventually_ge_atTop 2] with X hX hG hGG
  refine ⟨hX, ?_, ?_⟩
  · nlinarith
  · calc
      (2 : ℝ) ≤ (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ Real.log (Real.log (X : ℝ)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hGG 3

private theorem kuperberg_twin_error_at {ε K : ℝ}
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤
                K * (x : ℝ) ^ (1 - ε))
    {X : ℕ} (hfit : TwinHLFit X) :
    |(hlCount X twinShifts : ℝ) - hlMain (X : ℝ) twinShifts| ≤
      K * (X : ℝ) ^ (1 - ε) := by
  apply hbound X twinShifts hfit.1
  · intro h hh
    simp only [twinShifts, mem_insert, mem_singleton] at hh
    rcases hh with rfl | rfl
    · simpa only [Nat.cast_zero] using (sq_nonneg (Real.log (X : ℝ)))
    · exact hfit.2.1
  · simpa [twinShifts] using hfit.2.2
  · exact twinShifts_hlAdmissible

private theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc
    |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

theorem twinRootedError_abs_le {ε K : ℝ}
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤
                K * (x : ℝ) ^ (1 - ε))
    {X : ℕ} (hfitX : TwinHLFit X) (hfit2X : TwinHLFit (2 * X)) :
    |(rootedTupleCount X {2} : ℝ) - rootedMainTerm X {2}| ≤
      K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) := by
  have hroot := rooted_error_eq (X := X) (H := ({2} : Finset ℕ)) (by simp)
  rw [hroot]
  have h2 := kuperberg_twin_error_at hbound hfit2X
  have h1 := kuperberg_twin_error_at hbound hfitX
  have h2' :
      |(hlCount (2 * X) (insert 0 {2}) : ℝ) -
          hlMain (2 * X : ℝ) (insert 0 {2})| ≤
        K * (2 * X : ℝ) ^ (1 - ε) := by
    simpa [twinShifts] using h2
  have h1' :
      |(hlCount X (insert 0 {2}) : ℝ) -
          hlMain (X : ℝ) (insert 0 {2})| ≤
        K * (X : ℝ) ^ (1 - ε) := by
    simpa [twinShifts] using h1
  exact (abs_sub_le_add _ _).trans (by linarith)

private theorem eventually_twin_error_lt_integral_floor {ε K S : ℝ}
    (hε : 0 < ε) (hK : 0 < K) (hS : 0 < S) :
    ∀ᶠ X : ℕ in atTop,
      K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) <
        S * ((X : ℝ) / Real.log (2 * (X : ℝ)) ^ 2) := by
  let C : ℝ := 2 ^ (1 - ε) + 1
  have hC : 0 < C := add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _) zero_le_one
  let c : ℝ := S / (2 * K * C * 2 ^ ε)
  have hc : 0 < c := div_pos hS (mul_pos (mul_pos (mul_pos (by norm_num) hK) hC)
    (Real.rpow_pos_of_pos (by norm_num) _))
  have hsmallReal := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε).bound hc
  have hsmallNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  rw [eventually_atTop] at hsmallNat
  obtain ⟨X0, hX0⟩ := hsmallNat
  filter_upwards [eventually_ge_atTop X0, eventually_ge_atTop (3 : ℕ)] with X hXX0 hX3
  have hsmall := hX0 (2 * X) (hXX0.trans (by omega))
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hlogpos : 0 < Real.log (2 * (X : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) < X := by exact_mod_cast (by omega : 1 < X)
    linarith
  have hpowpos : 0 < (X : ℝ) ^ ε := Real.rpow_pos_of_pos hXpos _
  have hCeq :
      (2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε) =
        C * (X : ℝ) ^ (1 - ε) := by
    simp only [C]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXpos.le]
    ring
  have hsmall' : Real.log (2 * (X : ℝ)) ^ 2 ≤
      c * (2 ^ ε * (X : ℝ) ^ ε) := by
    have hlog0 : 0 ≤ Real.log ((2 * X : ℕ) : ℝ) := Real.log_nonneg (by
      exact_mod_cast (by omega : 1 ≤ 2 * X))
    have hrpow0 : 0 ≤ ((2 * X : ℕ) : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg hlog0 _), abs_of_nonneg hrpow0] at hsmall
    rw [show ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) by simp,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hXpos.le] at hsmall
    simpa only [Real.rpow_ofNat] using hsmall
  have hcoeff : K * C * Real.log (2 * (X : ℝ)) ^ 2 <
      S * (X : ℝ) ^ ε := by
    have hle := mul_le_mul_of_nonneg_left hsmall'
      (mul_nonneg hK.le hC.le)
    have hcollapse : K * C * (c * (2 ^ ε * (X : ℝ) ^ ε)) =
        (S / 2) * (X : ℝ) ^ ε := by
      dsimp [c]
      field_simp [hK.ne', hC.ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ε).ne']
    rw [hcollapse] at hle
    nlinarith
  rw [hCeq, Real.rpow_sub hXpos 1 ε, Real.rpow_one]
  have hlogSq : 0 < Real.log (2 * (X : ℝ)) ^ 2 := sq_pos_of_pos hlogpos
  have herrForm : K * (C * ((X : ℝ) / (X : ℝ) ^ ε)) =
      (K * C * (X : ℝ)) / (X : ℝ) ^ ε := by ring
  have hmainForm : S * ((X : ℝ) / Real.log (2 * (X : ℝ)) ^ 2) =
      (S * (X : ℝ)) / Real.log (2 * (X : ℝ)) ^ 2 := by ring
  rw [herrForm, hmainForm]
  apply (div_lt_div_iff₀ hpowpos hlogSq).2
  nlinarith

/-- Kuperberg's genuine uniform tuple conjecture forces a twin pair in
every sufficiently large dyadic window. -/
theorem eventually_twinRootedTupleCount_pos (hKup : KuperbergConj13) :
    ∀ᶠ X : ℕ in atTop, 0 < rootedTupleCount X {2} := by
  obtain ⟨ε, K, hε, hK, hbound⟩ := hKup
  have hS := twinShifts_singularSeries_pos
  have hdom := eventually_twin_error_lt_integral_floor hε hK hS
  have hfitEventually := eventually_twinHLFit
  rw [eventually_atTop] at hfitEventually
  obtain ⟨X0, hfit⟩ := hfitEventually
  filter_upwards [hdom, eventually_ge_atTop X0, eventually_ge_atTop (16 : ℕ)] with
      X hdomX hXX0 hX16
  have hfitX := hfit X hXX0
  have hfit2X := hfit (2 * X) (hXX0.trans (by omega))
  have herr := twinRootedError_abs_le hbound hfitX hfit2X
  have hint := hlIntegral_two_dyadic_ge (le_trans (by norm_num) hX16)
  have hmain :
      singularSeries twinShifts *
          ((X : ℝ) / Real.log (2 * (X : ℝ)) ^ 2) ≤
        rootedMainTerm X {2} := by
    unfold rootedMainTerm
    simp only [card_singleton, Nat.reduceAdd]
    have heq : insert 0 ({2} : Finset ℕ) = twinShifts := by simp [twinShifts]
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hint hS.le]
  have hcount : (0 : ℝ) < rootedTupleCount X {2} := by
    have habsLower :
        rootedMainTerm X {2} -
            K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) ≤
          (rootedTupleCount X {2} : ℝ) := by
      linarith [neg_le_abs ((rootedTupleCount X {2} : ℝ) - rootedMainTerm X {2})]
    linarith
  exact_mod_cast hcount

/-- Kuperberg implies infinitely many actual prime starts `m` with
both `m` and `m+2` prime. -/
theorem infinite_twinPrimeStarts_of_kuperberg (hKup : KuperbergConj13) :
    Set.Infinite {m : ℕ | Nat.Prime m ∧ Nat.Prime (m + 2)} := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have hevent := eventually_twinRootedTupleCount_pos hKup
  rw [eventually_atTop] at hevent
  obtain ⟨X0, hX0⟩ := hevent
  let X := max X0 (a + 1)
  have hcount : 0 < rootedTupleCount X {2} := hX0 X (le_max_left _ _)
  have hXa : a + 1 ≤ X := le_max_right _ _
  have hnonempty :
      ((Ioc X (2 * X)).filter
        (fun n => Nat.Prime n ∧ ∀ h ∈ ({2} : Finset ℕ), Nat.Prime (n + h))).Nonempty := by
    simpa only [rootedTupleCount, card_pos] using hcount
  obtain ⟨m, hm⟩ := hnonempty
  have hm' := mem_filter.mp hm
  refine ⟨m, ?_, ?_⟩
  · simpa using hm'.2
  · have hmX := (mem_Ioc.mp hm'.1).1
    omega

end

end PrimeGapNormality.Prime.CoreTwinInfinitude
