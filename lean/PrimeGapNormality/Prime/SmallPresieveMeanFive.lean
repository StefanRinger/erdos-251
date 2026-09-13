import PrimeGapNormality.Prime.PresieveSelbergCap
import PrimeGapNormality.Prime.FiniteSelbergAsymptoticCap
import PrimeGapNormality.Prime.FiniteRootMixSmallMoments
import PrimeGapNormality.Prime.ExactRootMix
import PrimeGapNormality.Prime.CrtSieveCutoffEulerProdLeInvLog
import PrimeGapNormality.Prime.CrtNestedCutoffVRatio

/-!
# The sharp small-presieve mean cap

The finite Selberg cap gives `(25 / 12) S / log S`.  The explicit Euler
tail lower bound at `S`, together with the cutoff upper bound at `t`, gives
`lateRetention S (sieveCutoff t) <= 2 log S / log t`.  Finally
`S = floor ((6 / 5) L windowG)` and `X < t` make the three constants
multiply to exactly five.
-/

open Filter Finset
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

/-- The small presieve window escapes to infinity when `kappa > 0`. -/
theorem tendsto_ahlSmall_window_atTop {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (ahlSmall_window κ) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun n => ?_
  have h : ∀ᶠ X : ℕ in atTop,
      1 ≤ profileL κ X ∧ (n : ℝ) ≤ windowG X :=
    (eventually_one_le_profileL hκ).and
      (tendsto_windowG_atTop.eventually (eventually_ge_atTop (n : ℝ)))
  rw [eventually_atTop] at h
  obtain ⟨X0, hX0⟩ := h
  refine ⟨X0, fun X hX => ?_⟩
  obtain ⟨hL, hG⟩ := hX0 X hX
  have hcoef : (1 : ℝ) ≤ (6 / 5 : ℝ) * (profileL κ X : ℝ) := by
    have hLR : (1 : ℝ) ≤ (profileL κ X : ℝ) := Nat.one_le_cast.mpr hL
    nlinarith
  have harg : (n : ℝ) ≤
      (6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X := by
    exact hG.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hcoef (ahlSmall_windowG_nonneg X))
  exact Nat.le_floor harg

/-- Uniform sharp upper bound for the conditional mean on every concrete
small-window presieve fibre and every scale in the finite root mix. -/
theorem eventually_small_presieve_mean_le_five_of_euler_tail
    {κ : ℝ} (hκ : 0 < κ)
    (hEuler : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < eulerProdNat n * Real.log n) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X,
      ∀ σ : ResidueChoice (ahlSmall_window κ X),
        ((presieveSurvivors (ahlSmall_window κ X) σ).card : ℝ) *
          lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ))
        ≤ 5 * (profileL κ X : ℝ) := by
  have hSto := tendsto_ahlSmall_window_atTop hκ
  have hcap : ∀ᶠ X : ℕ in atTop,
      ∀ σ : ResidueChoice (ahlSmall_window κ X),
        ((presieveSurvivors (ahlSmall_window κ X) σ).card : ℝ) ≤
          (2 + (1 / 12 : ℝ)) * (ahlSmall_window κ X : ℝ) /
            Real.log (ahlSmall_window κ X) :=
    hSto.eventually
      (eventually_presieveSurvivors_card_le_two_add_eps
        (by norm_num : (0 : ℝ) < 1 / 12))
  have hEulerS : ∀ᶠ X : ℕ in atTop,
      (1 / 2 : ℝ) <
        eulerProdNat (ahlSmall_window κ X) *
          Real.log (ahlSmall_window κ X) :=
    hSto.eventually hEuler
  have hS2 : ∀ᶠ X : ℕ in atTop, 2 ≤ ahlSmall_window κ X :=
    hSto.eventually (eventually_ge_atTop 2)
  filter_upwards [hcap, hEulerS, hS2,
    eventually_profileS_le_sieveCutoff hκ,
    crtNestVR_eventually_exp_sixteen, eventually_ge_atTop 3] with
      X hcapX hEulerX hS2X hprofile hXexp hX3
  intro t ht σ
  let S := ahlSmall_window κ X
  let L := profileL κ X
  let y := sieveCutoff (t : ℝ)
  have htI : t ∈ Ioc X (2 * X) := by simpa [mixScale] using ht
  have hXtNat : X < t := (mem_Ioc.mp htI).1
  have hXt : (X : ℝ) < (t : ℝ) := Nat.cast_lt.mpr hXtNat
  have hX1 : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hX3)
  have ht1 : (1 : ℝ) < t := hX1.trans hXt
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos ht1
  have hlogXt : Real.log (X : ℝ) < Real.log (t : ℝ) :=
    Real.log_lt_log (lt_trans zero_lt_one hX1) hXt
  have hcut : sieveCutoff (X : ℝ) ≤ y :=
    crtNestVR_sieveCutoff_mono hX1 hXt
  have hprofileNat : profileS κ X ≤ sieveCutoff (X : ℝ) :=
    Nat.cast_le.mp hprofile
  have hSy : S ≤ y :=
    (ahlSmall_window_le_profileS κ X).trans (hprofileNat.trans hcut)
  have hVpos : 0 < eulerProdNat S := eulerProdNat_pos S
  have hlogS : 0 < Real.log (S : ℝ) := by
    have htwoR : (2 : ℝ) ≤ S := Nat.cast_le.mpr hS2X
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) htwoR)
  have hInvV : 1 / eulerProdNat S < 2 * Real.log (S : ℝ) := by
    rw [div_lt_iff₀ hVpos]
    nlinarith [hEulerX]
  have htExp : Real.exp 16 ≤ (t : ℝ) := hXexp.trans hXt.le
  have hyV : eulerProdNat y ≤ 1 / Real.log (t : ℝ) :=
    crtCutV_eulerProdNat_le_inv_log htExp
  have hret : lateRetention S y ≤
      2 * Real.log (S : ℝ) / Real.log (t : ℝ) := by
    calc
      lateRetention S y ≤ eulerProdNat y / eulerProdNat S :=
        rootedEulerProdNat_le_div hSy hS2X
      _ = eulerProdNat y * (1 / eulerProdNat S) := by ring
      _ ≤ (1 / Real.log (t : ℝ)) * (1 / eulerProdNat S) :=
        mul_le_mul_of_nonneg_right hyV (one_div_nonneg.mpr hVpos.le)
      _ ≤ (1 / Real.log (t : ℝ)) * (2 * Real.log (S : ℝ)) :=
        mul_le_mul_of_nonneg_left hInvV.le (one_div_nonneg.mpr hlogt.le)
      _ = 2 * Real.log (S : ℝ) / Real.log (t : ℝ) := by ring
  have hretBound0 : 0 ≤
      2 * Real.log (S : ℝ) / Real.log (t : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hlogS.le) hlogt.le
  have hcard := hcapX σ
  have hSarg : (S : ℝ) ≤
      (6 / 5 : ℝ) * (L : ℝ) * Real.log (X : ℝ) := by
    have hfloor : (S : ℝ) ≤
        (6 / 5 : ℝ) * (L : ℝ) * windowG X :=
      Nat.floor_le (ahlSmall_arg_nonneg κ X)
    simpa [S, L, windowG_eq_log hX3] using hfloor
  have hSdiv : (S : ℝ) / Real.log (t : ℝ) ≤ (6 / 5 : ℝ) * (L : ℝ) := by
    apply (div_le_iff₀ hlogt).2
    calc
      (S : ℝ) ≤ (6 / 5 : ℝ) * (L : ℝ) * Real.log (X : ℝ) := hSarg
      _ ≤ (6 / 5 : ℝ) * (L : ℝ) * Real.log (t : ℝ) :=
        mul_le_mul_of_nonneg_left hlogXt.le
          (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  calc
    ((presieveSurvivors S σ).card : ℝ) * lateRetention S y
        ≤ ((presieveSurvivors S σ).card : ℝ) *
            (2 * Real.log (S : ℝ) / Real.log (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hret (Nat.cast_nonneg _)
    _ ≤ ((2 + (1 / 12 : ℝ)) * (S : ℝ) / Real.log (S : ℝ)) *
            (2 * Real.log (S : ℝ) / Real.log (t : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hretBound0
    _ = (25 / 6 : ℝ) * ((S : ℝ) / Real.log (t : ℝ)) := by
      field_simp [hlogS.ne', hlogt.ne']
      <;> ring
    _ ≤ (25 / 6 : ℝ) * ((6 / 5 : ℝ) * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hSdiv (by norm_num)
    _ = 5 * (L : ℝ) := by ring

end

end PrimeGapNormality.Prime
