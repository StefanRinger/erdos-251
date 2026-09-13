import PrimeGapNormality.Prime.StretchedClock.PositiveComparisonLabels
import PrimeGapNormality.Prime.StretchedClock.ClockProfile
import PrimeGapNormality.Prime.StretchedClock.ClockAsymptotics
import PrimeGapNormality.Prime.StretchedClock.PrimeArcAsymptotic

/-! The true prime arc bound supplies every fixed surrogate mesh. -/

namespace PrimeGapNormality.Prime.StretchedClock
open Finset Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000

def labelModulus (B N j : ℕ) : ℕ := B ^ (step B (Nat.sqrt N) + j) - 1

theorem labelModulus_cast {B : ℕ} (hB : 2 ≤ B) (N j : ℕ) :
    (labelModulus B N j : ℝ) =
      (localBase B (Nat.sqrt N) : ℝ) * (B : ℝ) ^ j - 1 := by
  have hpow : 1 ≤ B ^ (step B (Nat.sqrt N) + j) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega : B ≠ 0))
  unfold labelModulus
  rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one]
  simp only [localBase, Nat.cast_pow, pow_add]

theorem labelModulus_coprime_power {B : ℕ} (hB : 2 ≤ B) (N j r : ℕ) :
    (B ^ r).Coprime (labelModulus B N j) := by
  let k := step B (Nat.sqrt N) + j
  have hk : k ≠ 0 := by have := one_le_step hB (Nat.sqrt N); dsimp [k]; omega
  have hpow : 1 ≤ B ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega : B ≠ 0))
  have hco : (B ^ k).Coprime (B ^ k - 1) :=
    (Nat.coprime_self_sub_right hpow).mpr (Nat.coprime_one_right _)
  exact (Nat.Coprime.of_dvd_left (dvd_pow_self B hk) hco).pow_left r

theorem labelModulus_tendsto_atTop {B : ℕ} (hB : 2 ≤ B) (j : ℕ) :
    Tendsto (fun N => (labelModulus B N j : ℝ)) atTop atTop := by
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_gt_atTop (0 : ℕ), hl.eventually_ge_atTop (2 * (b + 1))]
    with N hN hlog
  have hq := half_log_le_localBase_sqrt hB hN
  have hpow : (1 : ℝ) ≤ (B : ℝ) ^ j := one_le_pow₀ (one_lt_base hB).le
  have hm := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (localBase B (Nat.sqrt N)))
  rw [labelModulus_cast hB]
  nlinarith

theorem eventually_labelModulus_le_log_sq {B : ℕ} (hB : 2 ≤ B) (j : ℕ) :
    ∀ᶠ N : ℕ in atTop, (labelModulus B N j : ℝ) ≤ Real.log (N : ℝ) ^ 2 := by
  let C : ℝ := 2 * (B : ℝ) ^ (j + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ), hl.eventually_ge_atTop C] with N hN hlog
  have hqmin : (localBase B (Nat.sqrt N) : ℝ) ≤ localBase B N :=
    Nat.cast_le.mpr (localBase_mono hB (Nat.sqrt_le_self N))
  have hqmax := localBase_le_two_base_mul_log hB hN
  have hpow0 : 0 ≤ (B : ℝ) ^ j := pow_nonneg (base_pos hB).le _
  have hm := mul_le_mul_of_nonneg_right (hqmin.trans hqmax) hpow0
  have he : (2 * (B : ℝ) * Real.log (N : ℝ)) * (B : ℝ) ^ j = C * Real.log (N : ℝ) := by
    dsimp [C]
    rw [pow_succ]
    ring
  rw [he] at hm
  have hlog0 := hC.trans hlog
  have hfinal := mul_le_mul_of_nonneg_right hlog hlog0
  rw [labelModulus_cast hB]
  nlinarith

theorem log_sq_div_sqrt_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Function.comp_apply, Real.rpow_two, Real.sqrt_eq_rpow] using hh

theorem eventually_labelModulus_data {B : ℕ} (hB : 2 ≤ B) (j : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ labelModulus B N j ∧
      (labelModulus B N j : ℝ) ≤ Real.log (N : ℝ) ^ 2 ∧
      1 / Real.sqrt (labelModulus B N j : ℝ) ≤ δ ∧
      (labelModulus B N j : ℝ) * Real.sqrt (N : ℝ) ≤ δ * N := by
  have hinv : Tendsto (fun N => 1 / Real.sqrt (labelModulus B N j : ℝ))
      atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (labelModulus_tendsto_atTop hB j))
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (labelModulus_tendsto_atTop hB j).eventually_ge_atTop 2,
    eventually_labelModulus_le_log_sq hB j, hinv.eventually_le_const hδ,
    log_sq_div_sqrt_tendsto_zero.eventually_le_const hδ] with N hN ha hupper hinv herror
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsqrt := Real.sqrt_pos.mpr hNr
  have hle : Real.log (N : ℝ) ^ 2 ≤ δ * Real.sqrt (N : ℝ) :=
    (div_le_iff₀ hsqrt).mp herror
  have hm := mul_le_mul_of_nonneg_right (hupper.trans hle) hsqrt.le
  have hsq := Real.sq_sqrt hNr.le
  refine ⟨by exact_mod_cast ha, hupper, hinv, ?_⟩
  nlinarith

/-- Uniform finite mesh domination of the true surrogate prefix. The
constant precedes the mesh and N; all arithmetic inputs are discharged. -/
theorem exists_surrogate_mesh_bound {B : ℕ} (hB : 2 ≤ B) :
    ∃ A : ℝ, 0 < A ∧ ∀ M : ℕ, 0 < M → ∀ᶠ N : ℕ in atTop,
      ∀ j < M,
        ((surrogateArcSet B N ((j : ℝ) / M) (((j : ℝ) + 1) / M)).card : ℝ) ≤
          A * (position B N : ℝ) / M := by
  obtain ⟨C, hC, N₀, hprime⟩ := exists_prime_fract_arc_bound
  refine ⟨8 * C + 1, by positivity, ?_⟩
  intro M hM
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  let δ : ℝ := 1 / (2 * M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnorm := normalizedPosition_tendsto_one hB
  have hhalf : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) ≤ normalizedPosition B N :=
    (hnorm.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)).mono fun N hN => hN.le
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop (0 : ℕ),
    eventually_labelModulus_data hB 0 hδ, eventually_labelModulus_data hB 1 hδ,
    hhalf,
    (position_sqrt_div_position_tendsto_zero hB).eventually_le_const (div_pos zero_lt_one hMr)]
      with N hN₀ hN h₀ h₁ hnorm hfirst
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk : (0 : ℝ) < step B N := Nat.cast_pos.mpr (step_pos hB N)
  have hP : (0 : ℝ) < position B N := Nat.cast_pos.mpr (position_pos hB hN)
  have hclock : (N : ℝ) * (step B N : ℝ) ≤ 2 * (position B N : ℝ) := by
    have hh := (le_div_iff₀ (mul_pos hNr hk)).mp hnorm
    change (1 / 2 : ℝ) * ((N : ℝ) * (step B N : ℝ)) ≤ (position B N : ℝ) at hh
    linarith
  have hfirst' : (position B (Nat.sqrt N) : ℝ) ≤ (position B N : ℝ) / M := by
    have hh := (div_le_iff₀ hP).mp hfirst
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
  intro j hj
  let s : ℝ := (j : ℝ) / M
  let t : ℝ := ((j : ℝ) + 1) / M
  have hs : 0 ≤ s := div_nonneg (Nat.cast_nonneg _) hMr.le
  have hst : s ≤ t := div_le_div_of_nonneg_right (by linarith) hMr.le
  have ht : t ≤ 1 := (div_le_one hMr).mpr (by exact_mod_cast (show j + 1 ≤ M by omega))
  have hlen : t - s = 1 / (M : ℝ) := by dsimp [s, t]; ring
  have hlabel (i : ℕ) (hdata : 2 ≤ labelModulus B N i ∧
      (labelModulus B N i : ℝ) ≤ Real.log (N : ℝ) ^ 2 ∧
      1 / Real.sqrt (labelModulus B N i : ℝ) ≤ δ ∧
      (labelModulus B N i : ℝ) * Real.sqrt (N : ℝ) ≤ δ * N)
      (r : ℕ) (hr : r < step B N) :
      ((labelArcSet B N (step B (Nat.sqrt N) + i) r s t).card : ℝ) ≤
        2 * C * N / M := by
    have hp := hprime N hN₀ (labelModulus B N i) (B ^ r) hdata.1 hdata.2.1
      (labelModulus_coprime_power hB N i r) s t hs hst ht
    have hpow : 1 ≤ B ^ (step B (Nat.sqrt N) + i) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega : B ≠ 0))
    have hmod : (labelModulus B N i : ℝ) = (B : ℝ) ^ (step B (Nat.sqrt N) + i) - 1 := by
      rw [labelModulus, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one]
    have hset : labelArcSet B N (step B (Nat.sqrt N) + i) r s t =
        (range N).filter (fun n =>
          s ≤ Int.fract (((B ^ r : ℕ) : ℝ) * (nthPrime n : ℝ) / (labelModulus B N i : ℝ)) ∧
            Int.fract (((B ^ r : ℕ) : ℝ) * (nthPrime n : ℝ) / (labelModulus B N i : ℝ)) < t) := by
      ext n
      simp only [labelArcSet, mem_filter, labelFract, hmod, Nat.cast_pow]
      exact Finset.mem_filter
    have hcount : ((labelArcSet B N (step B (Nat.sqrt N) + i) r s t).card : ℝ) ≤
        C * (N : ℝ) * (t - s + 1 / Real.sqrt (labelModulus B N i : ℝ)) +
          C * (labelModulus B N i : ℝ) * Real.sqrt (N : ℝ) := by
      rw [hset]
      exact hp
    have hmain : C * (N : ℝ) * (1 / (M : ℝ) + 1 / Real.sqrt (labelModulus B N i : ℝ)) ≤
        C * (N : ℝ) * (1 / (M : ℝ) + δ) :=
      mul_le_mul_of_nonneg_left
        (_root_.add_le_add (le_refl (1 / (M : ℝ))) hdata.2.2.1)
        (mul_nonneg hC.le hNr.le)
    have herr : C * (labelModulus B N i : ℝ) * Real.sqrt (N : ℝ) ≤ C * (δ * N) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdata.2.2.2 hC.le
    calc
      _ ≤ C * (N : ℝ) * (1 / (M : ℝ) + 1 / Real.sqrt (labelModulus B N i : ℝ)) +
          C * (labelModulus B N i : ℝ) * Real.sqrt (N : ℝ) := by
        simpa only [hlen] using hcount
      _ ≤ C * (N : ℝ) * (1 / (M : ℝ) + δ) + C * (δ * N) :=
        _root_.add_le_add hmain herr
      _ = 2 * C * N / M := by dsimp [δ]; ring
  have hp := surrogateArcSet_card_le hB N s t
    (by simpa only [Nat.add_zero] using hlabel 0 h₀)
    (hlabel 1 h₁)
  have hcoef := mul_le_mul_of_nonneg_right hclock
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC.le) hMr.le)
  have he : (step B N : ℝ) * (2 * C * N / M + 2 * C * N / M) =
      ((N : ℝ) * step B N) * (4 * C / M) := by ring
  rw [he] at hp
  change ((surrogateArcSet B N s t).card : ℝ) ≤ _
  calc
    _ ≤ (position B (Nat.sqrt N) : ℝ) +
        ((N : ℝ) * step B N) * (4 * C / M) := hp
    _ ≤ (position B N : ℝ) / M +
        (2 * (position B N : ℝ)) * (4 * C / M) :=
      _root_.add_le_add hfirst' hcoef
    _ = (8 * C + 1) * (position B N : ℝ) / M := by ring

end
end PrimeGapNormality.Prime.StretchedClock
