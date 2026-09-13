import PrimeGapNormality.Prime.CoreDyadicRecurrence
import PrimeGapNormality.Prime.CoreRoughDyadicDensity
import PrimeGapNormality.Prime.CoreRoughPhysicalSlices

/-!
# Full counting asymptotic for the literal moving-rough sequence

The initial count is split at `floor (X/2)` into an earlier initial count,
one actual dyadic root count, and a remainder of length at most one.  After
division by `X V(zPsi(X))`, the first coefficient tends to `1/2` by the
proved global cutoff stability, the dyadic increment tends to `1/2` by the
actual root-density theorem, and the one-point remainder vanishes.  The
abstract contracting recurrence then gives the full counting asymptotic.
-/

namespace PrimeGapNormality.Prime.CoreRoughInitialCount

open Filter Set Finset
open scoped Topology Classical

open CoreMovingRoughSequence CoreRoughThreshold CoreRoughSubpower
  CoreRoughCellAsymptotics CoreRoughGlobalCutoff CoreRoughDyadicDensity
  CoreRoughPhysicalSlices CoreRoughIntervalSlices CoreRoughSyntheticScale

noncomputable section

set_option maxHeartbeats 1200000

def initialCount (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  ((initialMovingRoughs (zPsi Ψ) X).card : ℝ)

def initialCountNormalized (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  initialCount Ψ X / ((X : ℝ) * eulerProdNat (zPsi Ψ X))

def halfMainCoefficient (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  (((X / 2 : ℕ) : ℝ) * eulerProdNat (zPsi Ψ (X / 2))) /
    ((X : ℝ) * eulerProdNat (zPsi Ψ X))

def initialCountRemainder (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  predicateCount (IsMovingRough (zPsi Ψ))
    (1 + 2 * (X / 2)) (X % 2)

def dyadicIncrementNormalized (Ψ : ℝ → ℝ) (X : ℕ) : ℝ :=
  (((rawPhysicalRoots (zPsi Ψ) (X / 2)).card : ℝ) +
      initialCountRemainder Ψ X) /
    ((X : ℝ) * eulerProdNat (zPsi Ψ X))

theorem initialCount_eq_predicate (Ψ : ℝ → ℝ) (X : ℕ) :
    initialCount Ψ X = predicateCount (IsMovingRough (zPsi Ψ)) 1 X := by
  unfold initialCount initialMovingRoughs predicateCount
  apply congrArg (fun s : Finset ℕ ↦ (s.card : ℝ))
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨hn, hrough⟩
    exact ⟨⟨hn.1, by omega⟩, hrough⟩
  · rintro ⟨hn, hrough⟩
    exact ⟨⟨hn.1, by omega⟩, hrough⟩

theorem initialCountRemainder_nonneg (Ψ : ℝ → ℝ) (X : ℕ) :
    0 ≤ initialCountRemainder Ψ X :=
  predicateCount_nonneg _ _ _

theorem initialCountRemainder_le_one (Ψ : ℝ → ℝ) (X : ℕ) :
    initialCountRemainder Ψ X ≤ 1 := by
  have hle := predicateCount_le_length (IsMovingRough (zPsi Ψ))
    (1 + 2 * (X / 2)) (X % 2)
  have hmod : X % 2 ≤ 1 := by omega
  exact hle.trans (by exact_mod_cast hmod)

/-- Exact half-interval count recurrence, including odd `X`. -/
theorem initialCount_half_partition (Ψ : ℝ → ℝ) (X : ℕ) :
    initialCount Ψ X = initialCount Ψ (X / 2) +
      ((rawPhysicalRoots (zPsi Ψ) (X / 2)).card : ℝ) +
        initialCountRemainder Ψ X := by
  let P : ℕ → Prop := IsMovingRough (zPsi Ψ)
  let h := X / 2
  let e := X % 2
  have hX : 2 * h + e = X := by
    dsimp only [h, e]
    omega
  have hfirst : predicateCount P 1 (2 * h) =
      predicateCount P 1 h + predicateCount P (h + 1) h := by
    simpa only [two_mul, Nat.one_add, Nat.add_one] using
      (predicateCount_add P 1 h h)
  have hsecond := predicateCount_add P 1 (2 * h) e
  have hraw := CoreRoughPhysicalSlices.raw_count_eq_predicate h Ψ
  change ((rawPhysicalRoots (zPsi Ψ) h).card : ℝ) =
    predicateCount P (h + 1) h at hraw
  rw [← hraw] at hfirst
  rw [hfirst] at hsecond
  rw [hX] at hsecond
  simpa only [initialCount_eq_predicate, initialCountRemainder, P, h, e,
    add_assoc] using hsecond

/-- Exact normalized affine recurrence. -/
theorem initialCountNormalized_recurrence
    (Ψ : ℝ → ℝ) {X : ℕ} (hX : 0 < X) :
    initialCountNormalized Ψ X =
      halfMainCoefficient Ψ X * initialCountNormalized Ψ (X / 2) +
        dyadicIncrementNormalized Ψ X := by
  have hXcast : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hX.ne'
  have hVX : eulerProdNat (zPsi Ψ X) ≠ 0 := (eulerProdNat_pos _).ne'
  have hden : (X : ℝ) * eulerProdNat (zPsi Ψ X) ≠ 0 :=
    mul_ne_zero hXcast hVX
  unfold initialCountNormalized halfMainCoefficient dyadicIncrementNormalized
  rw [initialCount_half_partition Ψ X]
  by_cases hh : X / 2 = 0
  · have hhCount : initialCount Ψ (X / 2) = 0 := by
      rw [hh]
      simp [initialCount, initialMovingRoughs]
    have hhR : (((X / 2 : ℕ) : ℝ) * eulerProdNat (zPsi Ψ (X / 2))) = 0 := by
      rw [hh]
      simp
    rw [hhCount, hhR, zero_div, zero_mul]
    field_simp [hden, hXcast, hVX] <;> ring
  · have hhalfNat : ((X / 2 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hh
    have hVhalf : eulerProdNat (zPsi Ψ (X / 2)) ≠ 0 :=
      (eulerProdNat_pos _).ne'
    have hhalfDen : (((X / 2 : ℕ) : ℝ) *
        eulerProdNat (zPsi Ψ (X / 2))) ≠ 0 :=
      mul_ne_zero hhalfNat hVhalf
    field_simp [hden, hhalfDen, hXcast, hVX, hhalfNat, hVhalf] <;> ring

private theorem tendsto_half_nat_div :
    Tendsto (fun X : ℕ ↦ ((X / 2 : ℕ) : ℝ) / (X : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := by
  have herror : Tendsto (fun X : ℕ ↦ (1 : ℝ) / (X : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub herror)
    (tendsto_const_nhds (x := (1 / 2 : ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hmod : X % 2 ≤ 1 := by omega
    have hdecomp : (X : ℝ) = 2 * (X / 2 : ℕ) + (X % 2 : ℕ) := by
      exact_mod_cast (by omega : X = 2 * (X / 2) + X % 2)
    apply (le_div_iff₀ hXpos).2
    have hmodR : ((X % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
    field_simp [hXpos.ne']
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hdecomp : (X : ℝ) = 2 * (X / 2 : ℕ) + (X % 2 : ℕ) := by
      exact_mod_cast (by omega : X = 2 * (X / 2) + X % 2)
    apply (div_le_iff₀ hXpos).2
    have hmod0 : (0 : ℝ) ≤ (X % 2 : ℕ) := Nat.cast_nonneg _
    field_simp [hXpos.ne']
    nlinarith

private theorem tendsto_halfEulerRatio_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (fun X : ℕ ↦
      eulerProdNat (zPsi Ψ (X / 2)) / eulerProdNat (zPsi Ψ X))
      atTop (nhds 1) := by
  have hglobalReg : CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative Ψ dΨ C := by
    simpa only [CoreRoughGlobalCutoff.HasEventuallyWeightedDerivative,
      CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative] using hreg
  have hglobalHalf := CoreDyadicRecurrence.halfIndex_tendsto_atTop.eventually
    (eventually_global_cutoff_and_primeLoss hSlope hC hglobalReg)
  have hhazard := (tendsto_dyadicRootHazard_zero (C := C) hSlope).comp
    CoreDyadicRecurrence.halfIndex_tendsto_atTop
  have hratioForward : Tendsto (fun X : ℕ ↦
      eulerProdNat (zPsi Ψ X) / eulerProdNat (zPsi Ψ (X / 2)))
      atTop (nhds 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa only [sub_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub hhazard)
      (tendsto_const_nhds (x := (1 : ℝ))) ?_ ?_
    · filter_upwards [hglobalHalf, eventually_ge_atTop 2] with X hglob hX
      let h := X / 2
      have hhpos : 0 < h := by dsimp only [h]; omega
      have hXmem : X ∈ Set.Icc h (3 * h) := by
        dsimp only [h]
        constructor <;> omega
      have hcut := hglob X hXmem
      have hsingle : finiteTupleSieveProduct ({0} : Finset ℕ) (zPsi Ψ X) =
          eulerProdNat (zPsi Ψ X) := CoreRoughRootCount.singleton_tupleProduct _
      have hsingleH : finiteTupleSieveProduct ({0} : Finset ℕ) (zPsi Ψ h) =
          eulerProdNat (zPsi Ψ h) := CoreRoughRootCount.singleton_tupleProduct _
      have hband : (∑ p ∈ Nat.primesLE (zPsi Ψ X) \ Nat.primesLE (zPsi Ψ h),
          (residueCount ({0} : Finset ℕ) p : ℝ) / (p : ℝ)) ≤
          dyadicRootHazard C Ψ h := by
        simpa only [residueCount, Finset.image_singleton, Finset.card_singleton,
          Nat.cast_one, one_div, cutoffPrimeReciprocalLoss, dyadicRootHazard]
          using hcut.2.2
      have hb := CoreRoughEulerStability.finiteTupleSieveProduct_bounds
        ({0} : Finset ℕ) hcut.1 hband
      rw [hsingle, hsingleH] at hb
      have hVh := eulerProdNat_pos (zPsi Ψ h)
      have hdiv := div_le_div_of_nonneg_right hb.1 hVh.le
      simpa only [h, Function.comp_def, mul_div_assoc,
        mul_div_cancel_right₀ _ hVh.ne'] using hdiv
    · filter_upwards [hglobalHalf, eventually_ge_atTop 2] with X hglob hX
      let h := X / 2
      have hXmem : X ∈ Set.Icc h (3 * h) := by
        dsimp only [h]
        constructor <;> omega
      have hcut := hglob X hXmem
      have hband : (∑ p ∈ Nat.primesLE (zPsi Ψ X) \ Nat.primesLE (zPsi Ψ h),
          (residueCount ({0} : Finset ℕ) p : ℝ) / (p : ℝ)) ≤
          dyadicRootHazard C Ψ h := by
        simpa only [residueCount, Finset.image_singleton, Finset.card_singleton,
          Nat.cast_one, one_div, cutoffPrimeReciprocalLoss, dyadicRootHazard]
          using hcut.2.2
      have hb := CoreRoughEulerStability.finiteTupleSieveProduct_bounds
        ({0} : Finset ℕ) hcut.1 hband
      rw [CoreRoughRootCount.singleton_tupleProduct,
        CoreRoughRootCount.singleton_tupleProduct] at hb
      exact (div_le_one (eulerProdNat_pos (zPsi Ψ (X / 2)))).2 hb.2
  have hinv := hratioForward.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one] at hinv
  apply hinv.congr'
  exact Eventually.of_forall fun X ↦ by
    have hV := (eulerProdNat_pos (zPsi Ψ X)).ne'
    have hVh := (eulerProdNat_pos (zPsi Ψ (X / 2))).ne'
    field_simp [hV, hVh]

theorem tendsto_halfMainCoefficient_half
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (halfMainCoefficient Ψ) atTop (nhds (1 / 2 : ℝ)) := by
  have hh := tendsto_half_nat_div.mul
    (tendsto_halfEulerRatio_one hSlope hC hreg)
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  unfold halfMainCoefficient
  have hXN := (Nat.cast_ne_zero.mpr (by omega : X ≠ 0) : (X : ℝ) ≠ 0)
  have hV := (eulerProdNat_pos (zPsi Ψ X)).ne'
  field_simp [hXN, hV] <;> ring

private theorem tendsto_remainder_div_main_zero
    {Ψ : ℝ → ℝ} {A : ℝ} (hSlope : HasSlopeBudget Ψ A) :
    Tendsto (fun X : ℕ ↦ initialCountRemainder Ψ X /
      ((X : ℝ) * eulerProdNat (zPsi Ψ X))) atTop (nhds 0) := by
  have hlogDiv : Tendsto (fun X : ℕ ↦
      Real.log (X : ℝ) / (X : ℝ)) atTop (nhds 0) := by
    have hreal := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hmajor := hlogDiv.const_mul (1 / eulerProdLowerConst)
  simp only [mul_zero] at hmajor
  refine squeeze_zero' (Eventually.of_forall fun X ↦ by
    exact div_nonneg (initialCountRemainder_nonneg Ψ X)
      (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le)) ?_ hmajor
  filter_upwards [eventually_model_gap_le_log hSlope, eventually_ge_atTop 1]
      with X hG hX
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hrem := initialCountRemainder_le_one Ψ X
  have hmain : initialCountRemainder Ψ X /
      ((X : ℝ) * eulerProdNat (zPsi Ψ X)) ≤
      roughGapScale (zPsi Ψ X) / (X : ℝ) := by
    unfold roughGapScale
    have hV := eulerProdNat_pos (zPsi Ψ X)
    apply (div_le_iff₀ (mul_pos hXpos hV)).2
    field_simp [hXpos.ne', hV.ne']
    nlinarith
  calc
    initialCountRemainder Ψ X /
        ((X : ℝ) * eulerProdNat (zPsi Ψ X)) ≤
        roughGapScale (zPsi Ψ X) / (X : ℝ) := hmain
    _ ≤ (Real.log (X : ℝ) / eulerProdLowerConst) / (X : ℝ) :=
      div_le_div_of_nonneg_right hG hXpos.le
    _ = (1 / eulerProdLowerConst) *
        (Real.log (X : ℝ) / (X : ℝ)) := by ring

theorem tendsto_dyadicIncrementNormalized_half
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (dyadicIncrementNormalized Ψ) atTop (nhds (1 / 2 : ℝ)) := by
  have hroot := (tendsto_rawPhysicalRoots_div_main_one hSlope hC hreg).comp
    CoreDyadicRecurrence.halfIndex_tendsto_atTop
  have hhalf := tendsto_halfMainCoefficient_half hSlope hC hreg
  have hmain := hroot.mul hhalf
  simp only [one_mul] at hmain
  have hrem := tendsto_remainder_div_main_zero hSlope
  have hsum := hmain.add hrem
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  simp only [Function.comp_apply]
  unfold dyadicIncrementNormalized halfMainCoefficient
  have hXN : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hhN : ((X / 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hV : eulerProdNat (zPsi Ψ X) ≠ 0 := (eulerProdNat_pos _).ne'
  have hVh : eulerProdNat (zPsi Ψ (X / 2)) ≠ 0 := (eulerProdNat_pos _).ne'
  field_simp [hXN, hhN, hV, hVh]

/-- Full natural counting function asymptotic. -/
theorem tendsto_initialCountNormalized_one
    {Ψ dΨ : ℝ → ℝ} {A C : ℝ}
    (hSlope : HasSlopeBudget Ψ A) (hC : 0 ≤ C)
    (hreg : CoreRoughCellAsymptotics.HasEventuallyWeightedDerivative Ψ dΨ C) :
    Tendsto (initialCountNormalized Ψ) atTop (nhds 1) := by
  apply CoreDyadicRecurrence.tendsto_one_of_affine_half_recurrence
    (c := (1 / 2 : ℝ)) (by norm_num)
    (tendsto_halfMainCoefficient_half hSlope hC hreg)
    (by simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      tendsto_dyadicIncrementNormalized_half hSlope hC hreg)
  filter_upwards [eventually_ge_atTop 1] with X hX
  exact initialCountNormalized_recurrence Ψ (by omega)

end

end PrimeGapNormality.Prime.CoreRoughInitialCount
