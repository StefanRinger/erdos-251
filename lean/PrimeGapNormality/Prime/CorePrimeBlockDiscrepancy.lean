import PrimeGapNormality.Prime.CorePrimePositionQuantitativeComparison

/-!
# Uniform physical prime-block discrepancy

At the paper choices

`κ = 4 / log B`, `T = floor ((log G)/(4 log B))`,
`δ = G^(-1/8)`,

the genuine finite orbit discrepancy theorem and the actual positive
prime-position comparison give a star-discrepancy bound
`O_B(1 / sqrt(log G))` on the physical block `(X,2X]`.  The threshold is
chosen before the anchored interval endpoint.
-/

namespace PrimeGapNormality.Prime.CorePrimeBlockDiscrepancy

open Filter Finset MeasureTheory Set
open CorePrimePositionQuantitativeComparison CoreFiniteOrbitDiscrepancy
open scoped Topology Classical

noncomputable section

set_option maxHeartbeats 1200000

abbrev Circle := AddCircle (1 : ℝ)

def primeBlockKappa (B : ℕ) : ℝ := 4 / Real.log (B : ℝ)

def primeBlockTime (B X : ℕ) : ℕ :=
  ⌊Real.log (windowG X) / (4 * Real.log (B : ℝ))⌋₊

def primeBlockRamp (X : ℕ) : ℝ :=
  windowG X ^ (-(1 / 8 : ℝ))

def primeBlockRate (X : ℕ) : ℝ :=
  1 / Real.sqrt (Real.log (windowG X))

def primePositionBlockIntervalMass (B X : ℕ) (t : ℝ) : ℝ :=
  orbitIntervalMass B (primePosSeries B : Circle)
    (Nat.primeCounting X) (windowNX X) t

private theorem eventually_sqrt_log_le_rpow_eighth :
    ∀ᶠ G : ℝ in atTop,
      Real.sqrt (Real.log G) ≤ G ^ (1 / 8 : ℝ) := by
  have hsmall : ∀ᶠ G : ℝ in atTop,
      ‖Real.log G‖ ≤ (1 : ℝ) * ‖G ^ (1 / 4 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 4)).bound (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 2] with G hlog hG
  have hG0 : 0 < G := zero_lt_two.trans_le hG
  have hlog0 : 0 ≤ Real.log G := Real.log_nonneg (by linarith)
  have hpow0 : 0 ≤ G ^ (1 / 8 : ℝ) := Real.rpow_nonneg hG0.le _
  have hbase : Real.log G ≤ G ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hG0.le _), one_mul] using hlog
  apply (Real.sqrt_le_iff).2
  refine ⟨hpow0, ?_⟩
  calc
    Real.log G ≤ G ^ (1 / 4 : ℝ) := hbase
    _ = (G ^ (1 / 8 : ℝ)) ^ 2 := by
      rw [sq, ← Real.rpow_add hG0]
      norm_num

private theorem eventually_log_cube_div_self_le
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ 3 / (X : ℝ) ≤ c := by
  have hlim : Tendsto (fun X : ℕ ↦
      Real.log (X : ℝ) ^ 3 / (X : ℝ)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 3 (by norm_num)
    simpa only [one_mul, add_zero, Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact hlim.eventually_le_const hc

private theorem eventual_block_scale_bounds
    (B : ℕ) (hB : 2 ≤ B) :
    ∀ᶠ X : ℕ in atTop,
      0 < primeBlockTime B X ∧ 0 < windowNX X ∧ 0 < primeBlockRamp X ∧
      Real.sqrt (6 / (primeBlockTime B X : ℝ)) ≤
        (8 * (Real.log (B : ℝ) + 1)) * primeBlockRate X ∧
      (profileL (primeBlockKappa B) X : ℝ)⁻¹ ≤
        (Real.log (B : ℝ) + 1) * primeBlockRate X ∧
      (windowG X ^ (-(1 / 2 : ℝ)) +
          windowG X * ((B : ℝ) ^ profileL (primeBlockKappa B) X)⁻¹) *
          ((2 / primeBlockRamp X) * (B ^ primeBlockTime B X : ℕ)) ≤
        4 * primeBlockRate X ∧
      2 * (primeBlockTime B X : ℝ) / (windowNX X : ℝ) ≤
        2 * primeBlockRate X ∧
      2 * primeBlockRamp X ≤ 2 * primeBlockRate X := by
  have hBr : 1 < (B : ℝ) := by exact_mod_cast (show 1 < B by omega)
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos hBr
  have hslow := tendsto_windowG_atTop.eventually
    eventually_sqrt_log_le_rpow_eighth
  have hdensity := CorePrimeDensity.eventually_seqWindow_card_ge
  have hcube := eventually_log_cube_div_self_le
    (CoreDyadicPrimeCounting.dyadicCountConstant / 2)
    (div_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos (by norm_num))
  filter_upwards [
    (Real.tendsto_log_atTop.comp tendsto_windowG_atTop).eventually_ge_atTop
      (max 2 (8 * Real.log (B : ℝ))),
    tendsto_windowG_atTop.eventually_ge_atTop 2,
    hslow, hdensity, hcube, crtWindowG_eventually_eq_log,
    eventually_ge_atTop 3] with
      X hell hG2 hsqrt hcard hcube hGeq hX
  let G := windowG X
  let ell := Real.log G
  let lb := Real.log (B : ℝ)
  let κ := primeBlockKappa B
  let T := primeBlockTime B X
  let L := profileL κ X
  let δ := primeBlockRamp X
  let R := primeBlockRate X
  have hG0 : 0 < G := zero_lt_two.trans_le hG2
  have hG1 : 1 ≤ G := by linarith
  have hell2 : (2 : ℝ) ≤ ell := by
    simpa only [ell, G, Function.comp_apply] using (le_max_left _ _).trans hell
  have hell0 : 0 < ell := zero_lt_two.trans_le hell2
  have hell8 : 8 * lb ≤ ell := by
    simpa only [ell, G, lb, Function.comp_apply] using
      (le_max_right _ _).trans hell
  have hxdef : (ell / (4 * lb) : ℝ) < (T : ℝ) + 1 := by
    simpa only [T, primeBlockTime, ell, G, lb] using
      Nat.lt_floor_add_one (ell / (4 * lb))
  have hTupper : (T : ℝ) ≤ ell / (4 * lb) := by
    dsimp only [T, primeBlockTime, ell, G, lb]
    exact Nat.floor_le (div_nonneg hell0.le (mul_nonneg (by norm_num) hlogB.le))
  have hx2 : (2 : ℝ) ≤ ell / (4 * lb) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hlogB)).2
    nlinarith [hell8]
  have hTlower : ell / (8 * lb) ≤ (T : ℝ) := by
    have hhalf : ell / (8 * lb) ≤ ell / (4 * lb) - 1 := by
      have heq : ell / (8 * lb) = (ell / (4 * lb)) / 2 := by ring
      rw [heq]
      linarith
    linarith
  have hT : 0 < T := by
    have : (0 : ℝ) < T := (div_pos hell0 (mul_pos (by norm_num) hlogB)).trans_le hTlower
    exact Nat.cast_pos.mp this
  have hN : 0 < windowNX X := by
    have hcpos : 0 < CoreDyadicPrimeCounting.dyadicCountConstant *
        ((X : ℝ) / Real.log X) := by
      exact mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
        (div_pos (Nat.cast_pos.mpr (by omega))
          (Real.log_pos (by exact_mod_cast (show 1 < X by omega))))
    have hcardPos : (0 : ℝ) < ((seqWindow nthPrime X).card : ℝ) :=
      hcpos.trans_le hcard
    have hcardNat : 0 < (seqWindow nthPrime X).card := Nat.cast_pos.mp hcardPos
    simpa only [seqWindow_nthPrime_card] using hcardNat
  have hδ : 0 < δ := by
    dsimp only [δ, primeBlockRamp]
    exact Real.rpow_pos_of_pos hG0 _
  have hsqrtR : Real.sqrt ell ≤ G ^ (1 / 8 : ℝ) := by
    simpa only [ell, G] using hsqrt
  have hRpos : 0 < R := by
    dsimp only [R, primeBlockRate]
    exact div_pos zero_lt_one (Real.sqrt_pos.mpr hell0)
  have hpowRate : G ^ (-(1 / 8 : ℝ)) ≤ R := by
    have hinv := one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr hell0) hsqrtR
    have heq : G ^ (-(1 / 8 : ℝ)) = 1 / G ^ (1 / 8 : ℝ) := by
      simp only [Real.rpow_neg hG0.le, one_div]
    simpa only [heq, R, primeBlockRate] using hinv
  have htime : Real.sqrt (6 / (T : ℝ)) ≤
      (8 * (lb + 1)) * R := by
    have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    have hlb0 : 0 < lb := hlogB
    have hTscaled : ell ≤ 8 * lb * (T : ℝ) := by
      have hh := (div_le_iff₀
        (mul_pos (by norm_num : (0 : ℝ) < 8) hlb0)).mp hTlower
      simpa only [mul_comm] using hh
    have hcoef : 48 * lb ≤ (8 * (lb + 1)) ^ 2 := by
      nlinarith [sq_nonneg (lb - 1)]
    have hmain : 6 * ell ≤ (8 * (lb + 1)) ^ 2 * (T : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_left hTscaled (by norm_num : (0 : ℝ) ≤ 6)
      have h₂ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg T)
      nlinarith
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
        (by linarith : 0 ≤ lb + 1)) hRpos.le, ?_⟩
    dsimp only [R, primeBlockRate]
    calc
      6 / (T : ℝ) ≤ (8 * (lb + 1)) ^ 2 / ell :=
        (div_le_div_iff₀ hTR hell0).2 hmain
      _ = ((8 * (lb + 1)) / Real.sqrt ell) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hell0.le]
      _ = (8 * (lb + 1) * (1 / Real.sqrt ell)) ^ 2 := by ring
  have hLlower : 4 * ell / lb ≤ (L : ℝ) := by
    dsimp only [L, κ, primeBlockKappa]
    have hh := kappa_log_windowG_le_profileL
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlogB.le) X
    simpa only [G, ell, div_mul_eq_mul_div] using hh
  have hLpos : (0 : ℝ) < L := (div_pos (mul_pos (by norm_num) hell0) hlogB).trans_le hLlower
  have hprof : (L : ℝ)⁻¹ ≤ (lb + 1) * R := by
    have hlowerPos : 0 < 4 * ell / lb := div_pos (mul_pos (by norm_num) hell0) hlogB
    have hinv := one_div_le_one_div_of_le hlowerPos hLlower
    have hsqrtEllLe : Real.sqrt ell ≤ ell := (Real.sqrt_le_self_iff).2
      (Or.inr (by linarith : 1 ≤ ell))
    have hcmp : lb / (4 * ell) ≤ (lb + 1) / Real.sqrt ell := by
      apply (div_le_div_iff₀
        (mul_pos (by norm_num : (0 : ℝ) < 4) hell0)
        (Real.sqrt_pos.mpr hell0)).2
      have hmul := mul_le_mul_of_nonneg_left hsqrtEllLe hlogB.le
      nlinarith [mul_nonneg (by linarith : 0 ≤ lb + 1) hell0.le]
    calc
      (L : ℝ)⁻¹ = 1 / (L : ℝ) := (one_div (L : ℝ)).symm
      _ ≤ 1 / (4 * ell / lb) := hinv
      _ = lb / (4 * ell) := by field_simp [hlogB.ne', hell0.ne']
      _ ≤ (lb + 1) / Real.sqrt ell := hcmp
      _ = (lb + 1) * R := by dsimp only [R, primeBlockRate]; ring
  have hBT : ((B ^ T : ℕ) : ℝ) ≤ G ^ (1 / 4 : ℝ) := by
    have hTlb : (T : ℝ) * lb ≤ ell / 4 := by
      have hh := (le_div_iff₀
        (mul_pos (by norm_num : (0 : ℝ) < 4) hlogB)).mp hTupper
      nlinarith
    rw [Nat.cast_pow]
    calc
      (B : ℝ) ^ T = Real.exp ((T : ℝ) * lb) := by
        rw [Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.mpr (by omega : 0 < B))]
      _ ≤ Real.exp (ell / 4) := Real.exp_le_exp.mpr hTlb
      _ = G ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_def_of_pos hG0]
        congr 1
        dsimp only [ell]
        ring
  have hBLinv : ((B : ℝ) ^ L)⁻¹ ≤ G ^ (-(4 : ℝ)) := by
    have hLlb : 4 * ell ≤ (L : ℝ) * lb := by
      exact (div_le_iff₀ hlogB).mp hLlower
    have hBL : G ^ (4 : ℝ) ≤ (B : ℝ) ^ L := by
      have hBexp : (B : ℝ) ^ L = Real.exp ((L : ℝ) * lb) := by
        rw [Real.exp_nat_mul, Real.exp_log (Nat.cast_pos.mpr (by omega : 0 < B))]
      rw [Real.rpow_def_of_pos hG0, hBexp]
      exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hLlb)
    have hinv := one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hG0 4) hBL
    simpa only [one_div, Real.rpow_neg hG0.le] using hinv
  have hδinv : δ⁻¹ = G ^ (1 / 8 : ℝ) := by
    dsimp only [δ, primeBlockRamp]
    rw [Real.rpow_neg hG0.le, inv_inv]
  have hmult : (2 / δ) * ((B ^ T : ℕ) : ℝ) ≤
      2 * G ^ (3 / 8 : ℝ) := by
    rw [div_eq_mul_inv, hδinv]
    have hh := mul_le_mul_of_nonneg_left hBT
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg hG0.le (1 / 8 : ℝ)))
    exact hh.trans_eq (by rw [mul_assoc, ← Real.rpow_add hG0]; norm_num)
  have hphase : G ^ (-(1 / 2 : ℝ)) + G * ((B : ℝ) ^ L)⁻¹ ≤
      G ^ (-(1 / 2 : ℝ)) + G ^ (-(3 : ℝ)) := by
    exact _root_.add_le_add le_rfl ((mul_le_mul_of_nonneg_left hBLinv hG0.le).trans_eq (by
      calc
        G * G ^ (-(4 : ℝ)) = G ^ (1 : ℝ) * G ^ (-(4 : ℝ)) := by
          rw [Real.rpow_one]
        _ = G ^ ((1 : ℝ) + (-4)) := (Real.rpow_add hG0 _ _).symm
        _ = G ^ (-(3 : ℝ)) := by norm_num))
  have hinsertion :
      (G ^ (-(1 / 2 : ℝ)) + G * ((B : ℝ) ^ L)⁻¹) *
          ((2 / δ) * ((B ^ T : ℕ) : ℝ)) ≤ 4 * R := by
    have hmultLower0 : 0 ≤ (2 / δ) * ((B ^ T : ℕ) : ℝ) := by positivity
    have hphaseUpper0 : 0 ≤ G ^ (-(1 / 2 : ℝ)) + G ^ (-(3 : ℝ)) := by
      positivity
    have hh := mul_le_mul hphase hmult hmultLower0 hphaseUpper0
    have hneg : G ^ (-(21 / 8 : ℝ)) ≤ G ^ (-(1 / 8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hG1 (by norm_num)
    calc
      _ ≤ (G ^ (-(1 / 2 : ℝ)) + G ^ (-(3 : ℝ))) *
          (2 * G ^ (3 / 8 : ℝ)) := hh
      _ = 2 * G ^ (-(1 / 8 : ℝ)) + 2 * G ^ (-(21 / 8 : ℝ)) := by
        calc
          _ = 2 * (G ^ (-(1 / 2 : ℝ)) * G ^ (3 / 8 : ℝ)) +
              2 * (G ^ (-(3 : ℝ)) * G ^ (3 / 8 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hG0, ← Real.rpow_add hG0]
            norm_num
      _ ≤ 4 * G ^ (-(1 / 8 : ℝ)) := by
        have hs := mul_le_mul_of_nonneg_left hneg (by norm_num : (0 : ℝ) ≤ 2)
        linarith
      _ ≤ 4 * R := mul_le_mul_of_nonneg_left hpowRate (by norm_num)
  have hTm : 2 * (T : ℝ) / (windowNX X : ℝ) ≤ 2 * R := by
    have hmR : (0 : ℝ) < windowNX X := Nat.cast_pos.mpr hN
    have hTX : (T : ℝ) ≤ Real.log (X : ℝ) := by
      have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have hh := Real.one_sub_inv_le_log_of_pos
          (by norm_num : (0 : ℝ) < 2)
        norm_num at hh
        exact hh
      have hlog2B : Real.log 2 ≤ lb := by
        dsimp only [lb]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast hB)
      have hden : (1 : ℝ) ≤ 4 * lb := by nlinarith
      have hTell : (T : ℝ) ≤ ell := hTupper.trans (by
        exact div_le_self hell0.le hden)
      have hellG : ell ≤ G :=
        (Real.log_le_sub_one_of_pos hG0).trans (by linarith)
      simpa only [G, hGeq] using hTell.trans hellG
    have hratio : (T : ℝ) / (windowNX X : ℝ) ≤
        Real.log (X : ℝ) ^ 2 /
          (CoreDyadicPrimeCounting.dyadicCountConstant * (X : ℝ)) := by
      apply (div_le_div_iff₀ hmR
        (mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
          (Nat.cast_pos.mpr (by omega : 0 < X)))).2
      have hm := hcard
      have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos
        (by exact_mod_cast (show 1 < X by omega))
      have hm' : CoreDyadicPrimeCounting.dyadicCountConstant * (X : ℝ) ≤
          (windowNX X : ℝ) * Real.log (X : ℝ) := by
        apply (div_le_iff₀ hlogX).mp
        simpa only [seqWindow_nthPrime_card, mul_div_assoc] using hm
      have hscaled := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg T)
      have hTscaled := mul_le_mul_of_nonneg_right hTX
        (mul_nonneg (Nat.cast_nonneg (windowNX X)) hlogX.le)
      nlinarith
    have hsqrtlog : Real.sqrt ell ≤ Real.log (X : ℝ) := by
      have := hsqrtR.trans
        (Real.rpow_le_self_of_one_le hG1 (by norm_num : (1 / 8 : ℝ) ≤ 1))
      simpa only [G, hGeq, Real.rpow_one] using this
    have hsmall : Real.log (X : ℝ) ^ 2 /
        (CoreDyadicPrimeCounting.dyadicCountConstant * (X : ℝ)) ≤ R := by
      dsimp only [R, primeBlockRate]
      apply (div_le_div_iff₀
        (mul_pos CoreDyadicPrimeCounting.dyadicCountConstant_pos
          (Nat.cast_pos.mpr (by omega : 0 < X)))
        (Real.sqrt_pos.mpr hell0)).2
      have hc := (div_le_iff₀
        (Nat.cast_pos.mpr (by omega : 0 < X) : (0 : ℝ) < X)).mp hcube
      have hmul := mul_le_mul_of_nonneg_left hsqrtlog
        (pow_nonneg (Real.log_nonneg
          (show (1 : ℝ) ≤ (X : ℝ) by
            exact_mod_cast (show 1 ≤ X by omega))) 2)
      nlinarith
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (hratio.trans hsmall)
        (by norm_num : (0 : ℝ) ≤ 2)
  have hramp : 2 * δ ≤ 2 * R :=
    mul_le_mul_of_nonneg_left (by simpa only [δ, primeBlockRamp, G] using hpowRate)
      (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨hT, hN, hδ,
    by simpa only [T, lb, R] using htime,
    by simpa only [L, lb, R] using hprof,
    by simpa only [G, L, T, δ, R] using hinsertion,
    by simpa only [T, R] using hTm,
    by simpa only [δ, R] using hramp⟩

/-- Uniform star-discrepancy on the actual physical prime block. -/
theorem primePositionBlock_discrepancy_of_kuperberg
    (B : ℕ) (hB : 2 ≤ B) (hK : KuperbergConj13) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ X : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        |primePositionBlockIntervalMass B X t - t| ≤
          C / Real.sqrt (Real.log (windowG X)) := by
  obtain ⟨A, E, H, hA, hE, hH, hdom⟩ :=
    primePosition_finitePositiveDomination_of_kuperberg B hB hK
  let C : ℝ := A * (8 * (Real.log (B : ℝ) + 1)) +
    E * (Real.log (B : ℝ) + 1) + 4 * H + 4
  have hC : 0 ≤ C := by
    have hlogB : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdom, eventual_block_scale_bounds B hB] with X hdomX hs
  intro t ht0 ht1
  have hfinite := abs_orbitIntervalMass_sub_le hB hs.2.1 hs.1
    hA (div_nonneg hE (Nat.cast_nonneg (profileL (primeBlockKappa B) X)))
    (mul_nonneg hH (_root_.add_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (crtWindowG_one_le X)) (-(1 / 2 : ℝ)))
      (mul_nonneg (zero_le_one.trans (crtWindowG_one_le X))
        (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg B) (profileL (primeBlockKappa B) X))))))
    hdomX ht0 ht1 hs.2.2.1
  unfold primePositionBlockIntervalMass
  have htime' : A * Real.sqrt (6 / (primeBlockTime B X : ℝ)) ≤
      A * (8 * (Real.log (B : ℝ) + 1)) * primeBlockRate X := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs.2.2.2.1 hA
  have hprof' : E / (profileL (primeBlockKappa B) X : ℝ) ≤
      E * (Real.log (B : ℝ) + 1) * primeBlockRate X := by
    have hh := mul_le_mul_of_nonneg_left hs.2.2.2.2.1 hE
    simpa only [div_eq_mul_inv, mul_assoc] using hh
  have hinsertion' :
      (H * (windowG X ^ (-(1 / 2 : ℝ)) +
          windowG X * ((B : ℝ) ^ profileL (primeBlockKappa B) X)⁻¹)) *
          ((2 / primeBlockRamp X) * (B ^ primeBlockTime B X : ℕ)) ≤
        (4 * H) * primeBlockRate X := by
    have hh := mul_le_mul_of_nonneg_left hs.2.2.2.2.2.1 hH
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hbound := _root_.add_le_add
    (_root_.add_le_add
      (_root_.add_le_add
        htime' hprof')
      hinsertion')
    (_root_.add_le_add hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2)
  have hfinal :
      A * Real.sqrt (6 / (primeBlockTime B X : ℝ)) +
          E / (profileL (primeBlockKappa B) X : ℝ) +
          (H * (windowG X ^ (-(1 / 2 : ℝ)) +
            windowG X * ((B : ℝ) ^ profileL (primeBlockKappa B) X)⁻¹)) *
              ((2 / primeBlockRamp X) * (B ^ primeBlockTime B X : ℕ)) +
          2 * (primeBlockTime B X : ℝ) / (windowNX X : ℝ) +
          2 * primeBlockRamp X ≤
        C / Real.sqrt (Real.log (windowG X)) := by
    calc
      _ ≤
          A * (8 * (Real.log (B : ℝ) + 1)) * primeBlockRate X +
            E * (Real.log (B : ℝ) + 1) * primeBlockRate X +
            (4 * H) * primeBlockRate X +
            2 * primeBlockRate X + 2 * primeBlockRate X := by
              simpa only [add_assoc] using hbound
      _ = _ := by
        unfold C primeBlockRate
        ring
  exact hfinite.trans hfinal

end

end PrimeGapNormality.Prime.CorePrimeBlockDiscrepancy
