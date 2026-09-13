import PrimeGapNormality.Prime.CoreRoughInitialCount
import PrimeGapNormality.Prime.CoreSequenceDoublingTail

/-!
# Density inversion for the moving-rough enumeration

The actual initial-count asymptotic is evaluated at the literal increasing
enumeration.  The exact identity `A(a n)=n+1` then gives the inverse density
scale.  A second use at `4*a n`, together with the proved dyadic stability of
the Euler factor, yields eventual four-doubling of the enumeration.
-/

namespace PrimeGapNormality.Prime.CoreRoughEnumerationDensity

open Filter Set Finset
open scoped Topology Classical

open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSyntheticScale
  CoreRoughGlobalCutoff CoreRoughCellAsymptotics CoreRoughDyadicDensity
  CoreRoughInitialCount CoreSequenceDoublingTail

noncomputable section

set_option maxHeartbeats 1000000

private theorem tendsto_nat_const_mul_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ ↦ k * n) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro N
  exact ⟨N, fun n hn ↦ hn.trans (Nat.le_mul_of_pos_left n hk)⟩

/-- Literal increasing enumeration of the moving-rough integers. -/
def roughEnumeration (Ψ : ℝ → ℝ) : ℕ → ℕ :=
  movingRoughSequence (zPsi Ψ)

theorem roughEnumeration_strictMono
    {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A) :
    StrictMono (roughEnumeration Ψ) :=
  movingRoughSequence_strictMono hSlope.eventually_zPsi_lt

theorem initialCount_eq_seqCount
    {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A) (X : ℕ) :
    initialCount Ψ X = seqCount (roughEnumeration Ψ) X := by
  unfold initialCount roughEnumeration
  exact_mod_cast initialMovingRoughs_card_eq_seqCount
    hSlope.eventually_zPsi_lt X

private theorem tendsto_nat_div_succ_one :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + 1 : ℕ)) atTop (nhds 1) := by
  have hden : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℕ))
      atTop (nhds 0) := by
    have hh := tendsto_inv_atTop_zero.comp hden
    simpa only [Function.comp_def, one_div] using hh
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  simp only [sub_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n ↦ by
    have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hne]
    push_cast
    ring

private theorem tendsto_enumerated_count_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) /
        ((roughEnumeration Ψ n : ℝ) *
          eulerProdNat (zPsi Ψ (roughEnumeration Ψ n))))
      atTop (nhds 1) := by
  have ha := roughEnumeration_strictMono hSlope
  have hcomp := (tendsto_initialCountNormalized_one hSlope hC hreg).comp
    ha.tendsto_atTop
  apply hcomp.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [Function.comp_def]
    unfold initialCountNormalized
    rw [initialCount_eq_seqCount hSlope, seqCount_apply_self ha]

/-- Literal inverse density along the actual enumeration. -/
theorem tendsto_roughEnumeration_div_densityScale_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun n : ℕ ↦
      (roughEnumeration Ψ n : ℝ) /
        ((n : ℝ) * roughGapScale (zPsi Ψ (roughEnumeration Ψ n))))
      atTop (nhds 1) := by
  have hcount := tendsto_enumerated_count_ratio_one hSlope hC hreg
  have hnratio := tendsto_nat_div_succ_one
  have hforward : Tendsto (fun n : ℕ ↦
      (n : ℝ) /
        ((roughEnumeration Ψ n : ℝ) *
          eulerProdNat (zPsi Ψ (roughEnumeration Ψ n))))
      atTop (nhds 1) := by
    have hh := hcount.mul hnratio
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsucc : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have ha0 : (roughEnumeration Ψ n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (movingRoughSequence_pos hSlope.eventually_zPsi_lt n))
    have hV := (eulerProdNat_pos
      (zPsi Ψ (roughEnumeration Ψ n))).ne'
    field_simp [hsucc, ha0, hV]
  have hinv := hforward.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one] at hinv
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha0 : (roughEnumeration Ψ n : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (movingRoughSequence_pos hSlope.eventually_zPsi_lt n))
  have hV := (eulerProdNat_pos (zPsi Ψ (roughEnumeration Ψ n))).ne'
  unfold roughGapScale
  field_simp [hn0, ha0, hV]

private theorem tendsto_eulerProd_two_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ ↦
      eulerProdNat (zPsi Ψ (2 * X)) / eulerProdNat (zPsi Ψ X))
      atTop (nhds 1) := by
  have hglobalReg : CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C := by
    simpa only [CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative,
      CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative] using hreg
  have hglobal := eventually_global_cutoff_and_primeLoss hSlope hC hglobalReg
  have hhazard := tendsto_dyadicRootHazard_zero (C := C) hSlope
  have hlower : Tendsto (fun X : ℕ ↦ 1 - dyadicRootHazard C Ψ X)
      atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hhazard
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower
    (tendsto_const_nhds (x := (1 : ℝ))) ?_ ?_
  · filter_upwards [hglobal, eventually_ge_atTop 1] with X hX hX1
    have hmem : 2 * X ∈ Set.Icc X (3 * X) := by constructor <;> omega
    have hc := hX (2 * X) hmem
    have hband : (∑ p ∈ Nat.primesLE (zPsi Ψ (2 * X)) \
        Nat.primesLE (zPsi Ψ X),
        (residueCount ({0} : Finset ℕ) p : ℝ) / (p : ℝ)) ≤
        dyadicRootHazard C Ψ X := by
      simpa only [residueCount, Finset.image_singleton, Finset.card_singleton, Nat.cast_one,
        one_div, cutoffPrimeReciprocalLoss, dyadicRootHazard] using hc.2.2
    have hb := CoreRoughEulerStability.finiteTupleSieveProduct_bounds
      ({0} : Finset ℕ) hc.1 hband
    rw [CoreRoughRootCount.singleton_tupleProduct,
      CoreRoughRootCount.singleton_tupleProduct] at hb
    have hV := eulerProdNat_pos (zPsi Ψ X)
    have hdiv := div_le_div_of_nonneg_right hb.1 hV.le
    simpa only [mul_div_assoc, mul_div_cancel_right₀ _ hV.ne'] using hdiv
  · filter_upwards [hglobal, eventually_ge_atTop 1] with X hX hX1
    have hmem : 2 * X ∈ Set.Icc X (3 * X) := by constructor <;> omega
    have hc := hX (2 * X) hmem
    have hband : (∑ p ∈ Nat.primesLE (zPsi Ψ (2 * X)) \
        Nat.primesLE (zPsi Ψ X),
        (residueCount ({0} : Finset ℕ) p : ℝ) / (p : ℝ)) ≤
        dyadicRootHazard C Ψ X := by
      simpa only [residueCount, Finset.image_singleton, Finset.card_singleton, Nat.cast_one,
        one_div, cutoffPrimeReciprocalLoss, dyadicRootHazard] using hc.2.2
    have hb := CoreRoughEulerStability.finiteTupleSieveProduct_bounds
      ({0} : Finset ℕ) hc.1 hband
    rw [CoreRoughRootCount.singleton_tupleProduct,
      CoreRoughRootCount.singleton_tupleProduct] at hb
    exact (div_le_one (eulerProdNat_pos (zPsi Ψ X))).2 hb.2

private theorem tendsto_eulerProd_four_ratio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ ↦
      eulerProdNat (zPsi Ψ (4 * X)) / eulerProdNat (zPsi Ψ X))
      atTop (nhds 1) := by
  have htwo := tendsto_eulerProd_two_ratio_one hSlope hC hreg
  have htwoAtTwo := htwo.comp
    (tendsto_nat_const_mul_atTop 2 (by norm_num))
  have hh := htwoAtTwo.mul htwo
  simp only [one_mul] at hh
  apply hh.congr'
  exact Eventually.of_forall fun X ↦ by
    have hV2 := (eulerProdNat_pos (zPsi Ψ (2 * X))).ne'
    have hVX := (eulerProdNat_pos (zPsi Ψ X)).ne'
    simp only [Function.comp_def]
    field_simp [hV2, hVX] <;> ring

private theorem tendsto_count_four_enumeration_div_succ_four
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun n : ℕ ↦
      initialCount Ψ (4 * roughEnumeration Ψ n) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 4) := by
  have ha := roughEnumeration_strictMono hSlope
  have hfourA : Tendsto (fun n : ℕ ↦ 4 * roughEnumeration Ψ n) atTop atTop :=
    (tendsto_nat_const_mul_atTop 4 (by norm_num)).comp ha.tendsto_atTop
  have hcount := (tendsto_initialCountNormalized_one hSlope hC hreg).comp hfourA
  have hbaseInv := (tendsto_enumerated_count_ratio_one hSlope hC hreg).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  have hV := (tendsto_eulerProd_four_ratio_one hSlope hC hreg).comp ha.tendsto_atTop
  have hh := ((hcount.mul (tendsto_const_nhds (x := (4 : ℝ)))).mul hbaseInv).mul hV
  simp only [one_mul, mul_one, inv_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_def]
  have hsucc : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have ha0 : (roughEnumeration Ψ n : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (movingRoughSequence_pos hSlope.eventually_zPsi_lt n))
  have hV1 := (eulerProdNat_pos (zPsi Ψ (roughEnumeration Ψ n))).ne'
  have hV4 := (eulerProdNat_pos (zPsi Ψ (4 * roughEnumeration Ψ n))).ne'
  unfold initialCountNormalized
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hsucc, ha0, hV1, hV4]

/-- The literal moving-rough enumeration satisfies the paper's eventual
four-doubling bound. -/
theorem eventually_roughEnumeration_fourDoubling
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    EventuallyFourDoubling (roughEnumeration Ψ) := by
  have hratio := tendsto_count_four_enumeration_div_succ_four hSlope hC hreg
  have ha := roughEnumeration_strictMono hSlope
  filter_upwards [hratio.eventually
    (Ioi_mem_nhds (show (3 : ℝ) < 4 by norm_num)), eventually_ge_atTop 1]
      with n hratioN hn
  have hcountEq := initialCount_eq_seqCount hSlope (4 * roughEnumeration Ψ n)
  have hsucc : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcountLarge : (2 * n : ℕ) <
      seqCount (roughEnumeration Ψ) (4 * roughEnumeration Ψ n) := by
    have hmul := (lt_div_iff₀ hsucc).mp hratioN
    rw [hcountEq] at hmul
    norm_num only [Nat.cast_add, Nat.cast_one] at hmul
    exact_mod_cast (show (2 * n : ℝ) <
      (seqCount (roughEnumeration Ψ) (4 * roughEnumeration Ψ n) : ℝ) by
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
  exact (seqCount_lt_iff ha).mp hcountLarge

end

end PrimeGapNormality.Prime.CoreRoughEnumerationDensity
