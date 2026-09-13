import PrimeGapNormality.Prime.PresieveSmallGlobalLower

/-!
# The rooted early-presieve first moment

The rooted coordinate at `p` forbids a uniformly chosen *nonzero*
residue.  Its one-point factor is therefore

`(p-2)/(p-1) + 1/(p-1) * 1_{p ∣ n}`.

This positive decomposition is stronger than the generic stopped
Bonferroni estimate needed for arbitrary forbidden classes.  On
expansion over subsets, all coefficients are nonnegative and sum to
one.  For each subset CRT leaves just the rounding error in the count
of one simultaneous residue class; hence the total first-moment error
is at most `1`, independently of the number of exposed primes.

In particular the rooted behaviour at divisors is preserved: if
`p ∣ n`, the local factor is exactly `1`.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

private def earlyMeanBase (p : ℕ) : ℝ :=
  ((p : ℝ) - 2) / ((p : ℝ) - 1)

private def earlyMeanBoost (p : ℕ) : ℝ :=
  1 / ((p : ℝ) - 1)

private def earlyMeanDvdIndicator (p n : ℕ) : ℝ :=
  if p ∣ n then 1 else 0

private def earlyMeanSubsetCoeff (P T : Finset ℕ) : ℝ :=
  (∏ p ∈ T, earlyMeanBoost p) *
    ∏ p ∈ P \ T, earlyMeanBase p

private theorem earlyMean_base_add_boost {p : ℕ} (hp : Nat.Prime p) :
    earlyMeanBase p + earlyMeanBoost p = 1 := by
  have hden : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (Nat.one_lt_cast.mpr hp.one_lt).ne'
  unfold earlyMeanBase earlyMeanBoost
  field_simp [hden]
  ring

private theorem earlyMean_base_nonneg {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ earlyMeanBase p := by
  unfold earlyMeanBase
  have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr hp.one_le : (↑(1 : ℕ) : ℝ) ≤ (p : ℝ))
  exact div_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hp1)

private theorem earlyMean_boost_nonneg {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ earlyMeanBoost p := by
  unfold earlyMeanBoost
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr hp.one_le : (↑(1 : ℕ) : ℝ) ≤ (p : ℝ))
  exact one_div_nonneg.mpr (sub_nonneg.mpr hp1)

private theorem earlyMean_base_add_boost_div {p : ℕ} (hp : Nat.Prime p) :
    earlyMeanBase p + earlyMeanBoost p / p = 1 - (p : ℝ)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hden : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (Nat.one_lt_cast.mpr hp.one_lt).ne'
  unfold earlyMeanBase earlyMeanBoost
  field_simp [hp0, hden]
  ring

/-! ## The exact rooted local factor -/

private theorem earlyMean_filter_card_of_dvd {w n : ℕ}
    (p : SievePrime w) (hpn : p.val ∣ n) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1).card = p.val - 1 := by
  have hmod : n % p.val = 0 := Nat.dvd_iff_mod_eq_zero.mp hpn
  have hall :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1) = univ := by
    apply filter_eq_self.mpr
    intro a _ha
    rw [hmod]
    omega
  rw [hall, card_univ, Fintype.card_fin]

private theorem earlyMean_filter_card_of_not_dvd {w n : ℕ}
    (p : SievePrime w) (hpn : ¬ p.val ∣ n) :
    ((univ : Finset (Fin (p.val - 1))).filter fun a =>
        n % p.val ≠ a.val + 1).card = p.val - 2 := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  have hmod0 : n % p.val ≠ 0 := by
    intro h
    exact hpn (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hmodpos : 0 < n % p.val := Nat.pos_of_ne_zero hmod0
  have hmodlt : n % p.val < p.val := Nat.mod_lt _ hp.pos
  let a0 : Fin (p.val - 1) := ⟨n % p.val - 1, by omega⟩
  have hiff : ∀ a : Fin (p.val - 1),
      n % p.val ≠ a.val + 1 ↔ a ≠ a0 := by
    intro a
    constructor
    · intro h ha
      subst a
      apply h
      dsimp [a0]
      omega
    · intro ha h
      apply ha
      apply Fin.ext
      dsimp [a0]
      omega
  have hfilter :
      (univ : Finset (Fin (p.val - 1))).filter (fun a =>
          n % p.val ≠ a.val + 1) = univ.erase a0 := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    rw [hiff]
    simp
  rw [hfilter, card_erase_of_mem (mem_univ a0), card_univ,
    Fintype.card_fin]
  omega

/-- The one-prime rooted factor, including the automatic survival of
`p`-divisible candidates, in positive-mixture form. -/
private theorem earlyPresieveOneLocalMass_eq_positive_mixture {w n : ℕ}
    (p : SievePrime w) :
    earlyPresieveOneLocalMass p n =
      earlyMeanBase p.val +
        earlyMeanBoost p.val * earlyMeanDvdIndicator p.val n := by
  have hp : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
  rw [earlyPresieveOneLocalMass_eq_card]
  by_cases hpn : p.val ∣ n
  · rw [earlyMean_filter_card_of_dvd p hpn]
    have hden : (p.val : ℝ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (Nat.one_lt_cast.mpr hp.one_lt).ne'
    simp only [earlyMeanDvdIndicator, if_pos hpn, mul_one]
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [div_self hden]
    exact (earlyMean_base_add_boost hp).symm
  · rw [earlyMean_filter_card_of_not_dvd p hpn]
    simp only [earlyMeanDvdIndicator, if_neg hpn, mul_zero, add_zero]
    unfold earlyMeanBase
    rw [Nat.cast_sub hp.two_le, Nat.cast_ofNat,
      Nat.cast_sub hp.one_le, Nat.cast_one]

/-- Exact positive-mixture expression for the rooted one-point weight. -/
private theorem earlyPresieveOneWeight_eq_positive_mixture (w n : ℕ) :
    earlyPresieveOneWeight w n =
      ∏ p ∈ Nat.primesLE w,
        (earlyMeanBase p +
          earlyMeanBoost p * earlyMeanDvdIndicator p n) := by
  unfold earlyPresieveOneWeight
  simp_rw [earlyPresieveOneLocalMass_eq_positive_mixture]
  exact Finset.prod_coe_sort (Nat.primesLE w)
    (fun p : ℕ => earlyMeanBase p +
      earlyMeanBoost p * earlyMeanDvdIndicator p n)

/-! ## Positive subset expansion and CRT rounding -/

private theorem earlyMean_indicator_prod (T : Finset ℕ) (n : ℕ) :
    ∏ p ∈ T, earlyMeanDvdIndicator p n =
      if ∀ p ∈ T, p ∣ n then 1 else 0 := by
  by_cases h : ∀ p ∈ T, p ∣ n
  · have hprod : ∏ p ∈ T, earlyMeanDvdIndicator p n = 1 := by
      apply prod_eq_one
      intro p hp
      simp [earlyMeanDvdIndicator, h p hp]
    rw [if_pos h]
    exact hprod
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p, hpT, hpn⟩ := h
    have hprod : ∏ q ∈ T, earlyMeanDvdIndicator q n = 0 := by
      apply prod_eq_zero hpT
      simp [earlyMeanDvdIndicator, hpn]
    exact hprod

private theorem earlyMean_kernel_expansion (P : Finset ℕ) (n : ℕ) :
    (∏ p ∈ P,
        (earlyMeanBase p +
          earlyMeanBoost p * earlyMeanDvdIndicator p n)) =
      ∑ T ∈ P.powerset,
        earlyMeanSubsetCoeff P T *
          (if ∀ p ∈ T, p ∣ n then 1 else 0) := by
  have hcomm :
      (∏ p ∈ P,
          (earlyMeanBase p +
            earlyMeanBoost p * earlyMeanDvdIndicator p n)) =
        ∏ p ∈ P,
          (earlyMeanBoost p * earlyMeanDvdIndicator p n +
            earlyMeanBase p) := by
    apply prod_congr rfl
    intro p _hp
    ring
  rw [hcomm, prod_add
    (fun p => earlyMeanBoost p * earlyMeanDvdIndicator p n)
    earlyMeanBase P]
  apply sum_congr rfl
  intro T hT
  unfold earlyMeanSubsetCoeff
  rw [prod_mul_distrib, earlyMean_indicator_prod]
  ring

private theorem earlyMean_subsetCoeff_nonneg {P T : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hT : T ⊆ P) :
    0 ≤ earlyMeanSubsetCoeff P T := by
  unfold earlyMeanSubsetCoeff
  exact mul_nonneg
    (prod_nonneg fun p hp => earlyMean_boost_nonneg (hP p (hT hp)))
    (prod_nonneg fun p hp =>
      earlyMean_base_nonneg (hP p (sdiff_subset hp)))

private theorem earlyMean_subsetCoeff_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ T ∈ P.powerset, earlyMeanSubsetCoeff P T = 1 := by
  have h := prod_add earlyMeanBoost earlyMeanBase P
  have hprod : ∏ p ∈ P, (earlyMeanBoost p + earlyMeanBase p) = 1 := by
    apply prod_eq_one
    intro p hp
    rw [add_comm, earlyMean_base_add_boost (hP p hp)]
  calc
    ∑ T ∈ P.powerset, earlyMeanSubsetCoeff P T =
        ∑ T ∈ P.powerset,
          (∏ p ∈ T, earlyMeanBoost p) *
            ∏ p ∈ P \ T, earlyMeanBase p := rfl
    _ = ∏ p ∈ P, (earlyMeanBoost p + earlyMeanBase p) := h.symm
    _ = 1 := hprod

private theorem earlyMean_euler_expansion (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    ∏ p ∈ P, (1 - (p : ℝ)⁻¹) =
      ∑ T ∈ P.powerset,
        earlyMeanSubsetCoeff P T / ∏ p ∈ T, (p : ℝ) := by
  have h := prod_add
    (fun p => earlyMeanBoost p / (p : ℝ)) earlyMeanBase P
  have hleft :
      ∏ p ∈ P, (earlyMeanBoost p / (p : ℝ) + earlyMeanBase p) =
        ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    apply prod_congr rfl
    intro p hp
    rw [add_comm, earlyMean_base_add_boost_div (hP p hp)]
  rw [hleft] at h
  rw [h]
  apply sum_congr rfl
  intro T hT
  have hpos : (∏ p ∈ T, (p : ℝ)) ≠ 0 := by
    exact (prod_ne_zero_iff.mpr fun p hp =>
      Nat.cast_ne_zero.mpr (hP p ((mem_powerset.mp hT) hp)).ne_zero)
  unfold earlyMeanSubsetCoeff
  rw [prod_div_distrib]
  field_simp [hpos]

private theorem earlyMean_card_filter_cast {α : Type*} (s : Finset α)
    (q : α → Prop) [DecidablePred q] :
    (((s.filter q).card : ℕ) : ℝ) =
      ∑ x ∈ s, if q x then (1 : ℝ) else 0 := by
  exact Finset.natCast_card_filter q s

private theorem earlyMean_prime_dvd_prod {T : Finset ℕ} {a : ℕ}
    (ha : Nat.Prime a) (hd : a ∣ ∏ p ∈ T, p) :
    ∃ p ∈ T, a ∣ p := by
  induction T using Finset.induction with
  | empty =>
      have ha1 : a = 1 := Nat.dvd_one.mp (by simpa using hd)
      exact (Nat.not_prime_one (ha1 ▸ ha)).elim
  | @insert p T hp ih =>
      rw [prod_insert hp] at hd
      rcases (Nat.Prime.dvd_mul ha).mp hd with hap | haT
      · exact ⟨p, mem_insert_self p T, hap⟩
      · obtain ⟨q, hqT, haq⟩ := ih haT
        exact ⟨q, mem_insert_of_mem hqT, haq⟩

private theorem earlyMean_prod_primes_dvd_iff {T : Finset ℕ} {n : ℕ}
    (hT : ∀ p ∈ T, Nat.Prime p) :
    (∏ p ∈ T, p) ∣ n ↔ ∀ p ∈ T, p ∣ n := by
  induction T using Finset.induction with
  | empty =>
      simp
  | insert a T ha ih =>
      have hpa : Nat.Prime a := hT a (mem_insert_self a T)
      have hpT : ∀ p ∈ T, Nat.Prime p := fun p hp =>
        hT p (mem_insert_of_mem hp)
      have hnot : ¬a ∣ ∏ p ∈ T, p := by
        intro hadv
        obtain ⟨p, hp, hadp⟩ := earlyMean_prime_dvd_prod hpa hadv
        have heq : a = p :=
          (Nat.prime_dvd_prime_iff_eq hpa (hpT p hp)).mp hadp
        exact ha (heq ▸ hp)
      have hcop : Nat.Coprime a (∏ p ∈ T, p) :=
        hpa.coprime_iff_not_dvd.mpr hnot
      rw [prod_insert ha]
      constructor
      · intro hd p hp
        rcases mem_insert.mp hp with rfl | hpTmem
        · exact (dvd_mul_right _ _).trans hd
        · have hdT : (∏ q ∈ T, q) ∣ n :=
            (dvd_mul_left (∏ q ∈ T, q) _).trans hd
          exact (ih hpT).mp hdT p hpTmem
      · intro hall
        have hda : a ∣ n := hall a (mem_insert_self a T)
        have hdT : (∏ p ∈ T, p) ∣ n :=
          (ih hpT).mpr fun p hp => hall p (mem_insert_of_mem hp)
        exact hcop.mul_dvd_of_dvd_of_dvd hda hdT

private theorem earlyMean_Icc_filter_all_prime_dvd_card {T : Finset ℕ}
    {S : ℕ} (hT : ∀ p ∈ T, Nat.Prime p) :
    ((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card =
      S / ∏ p ∈ T, p := by
  have hI : Icc 1 S = Ioc 0 S := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  have hfilter :
      (Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n) =
        (Icc 1 S).filter (fun n => (∏ p ∈ T, p) ∣ n) := by
    ext n
    simp only [mem_filter]
    exact and_congr_right fun _ => (earlyMean_prod_primes_dvd_iff hT).symm
  rw [hfilter, hI, Nat.Ioc_filter_dvd_card_eq_div]

private theorem earlyMean_cast_div_ge_sub_one {S d : ℕ} (hd : 0 < d) :
    (S : ℝ) / d - 1 ≤ ((S / d : ℕ) : ℝ) := by
  have hmod := Nat.div_add_mod S d
  have hcast :
      (S : ℝ) = (d : ℝ) * ((S / d : ℕ) : ℝ) + ((S % d : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, hmod]
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsplit :
      (S : ℝ) / d = ((S / d : ℕ) : ℝ) + ((S % d : ℕ) : ℝ) / d := by
    rw [hcast, add_div, mul_div_cancel_left₀ _ hdpos.ne']
  have hlt : ((S % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one hdpos]
    exact_mod_cast Nat.mod_lt S hd
  linarith

private theorem earlyMean_subset_rounding {P T : Finset ℕ} {S : ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hT : T ⊆ P) :
    abs (
      (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
        (S : ℝ) / ∏ p ∈ T, (p : ℝ)) ≤ 1 := by
  have hpT : ∀ p ∈ T, Nat.Prime p := fun p hp => hP p (hT hp)
  let d := ∏ p ∈ T, p
  have hd : 0 < d := prod_pos fun p hp => (hpT p hp).pos
  have hcard :
      (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) =
        ((S / d : ℕ) : ℝ) := by
    have hncard := earlyMean_Icc_filter_all_prime_dvd_card (S := S) hpT
    exact_mod_cast hncard
  have hcastProd : (d : ℝ) = ∏ p ∈ T, (p : ℝ) := by
    simp only [d, Nat.cast_prod]
  rw [hcard, ← hcastProd]
  apply abs_le.mpr
  constructor
  · linarith [earlyMean_cast_div_ge_sub_one (S := S) hd]
  · have hup : ((S / d : ℕ) : ℝ) ≤ (S : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    linarith

/-- Uniform absolute first-moment estimate.  This is the rooted
finite-sieve substitute for the paper's adjacent Bonferroni
truncations; its error `1` is stronger than their moving-cutoff error. -/
theorem earlyPresieve_uniformMean_abs_sub_main_le_one (S w : ℕ) :
    |earlyPresieveUniformMean S w -
        (S : ℝ) * eulerProdNat w| ≤ 1 := by
  let P := Nat.primesLE w
  have hP : ∀ p ∈ P, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primesLE hp
  rw [earlyPresieve_uniformMean_eq_exact]
  simp_rw [earlyPresieveOneWeight_eq_positive_mixture,
    earlyMean_kernel_expansion]
  have hsum :
      ∑ n ∈ Icc 1 S, ∑ T ∈ P.powerset,
          earlyMeanSubsetCoeff P T *
            (if ∀ p ∈ T, p ∣ n then 1 else 0) =
        ∑ T ∈ P.powerset, earlyMeanSubsetCoeff P T *
          (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro T _hT
    rw [← mul_sum, earlyMean_card_filter_cast]
  rw [hsum]
  have hEuler := earlyMean_euler_expansion P hP
  change abs (
    ∑ T ∈ P.powerset, earlyMeanSubsetCoeff P T *
        (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
      (S : ℝ) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ 1
  rw [hEuler, mul_sum, ← sum_sub_distrib]
  have hterm : ∀ T ∈ P.powerset,
      |earlyMeanSubsetCoeff P T *
          (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
        (S : ℝ) *
          (earlyMeanSubsetCoeff P T / ∏ p ∈ T, (p : ℝ))| ≤
        earlyMeanSubsetCoeff P T := by
    intro T hT
    have hsub : T ⊆ P := mem_powerset.mp hT
    have hc0 := earlyMean_subsetCoeff_nonneg hP hsub
    have hr := earlyMean_subset_rounding (S := S) hP hsub
    have hre :
        earlyMeanSubsetCoeff P T *
            (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
          (S : ℝ) *
            (earlyMeanSubsetCoeff P T / ∏ p ∈ T, (p : ℝ)) =
          earlyMeanSubsetCoeff P T *
            ((((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
              (S : ℝ) / ∏ p ∈ T, (p : ℝ)) := by
      ring
    rw [hre, abs_mul, abs_of_nonneg hc0]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hc0
  calc
    |∑ T ∈ P.powerset,
        (earlyMeanSubsetCoeff P T *
            (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
          (S : ℝ) *
            (earlyMeanSubsetCoeff P T / ∏ p ∈ T, (p : ℝ)))|
        ≤ ∑ T ∈ P.powerset,
            |earlyMeanSubsetCoeff P T *
                (((Icc 1 S).filter (fun n => ∀ p ∈ T, p ∣ n)).card : ℝ) -
              (S : ℝ) *
                (earlyMeanSubsetCoeff P T / ∏ p ∈ T, (p : ℝ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ P.powerset, earlyMeanSubsetCoeff P T :=
      sum_le_sum hterm
    _ = 1 := earlyMean_subsetCoeff_sum P hP

/-! ## The exact remaining scalar for the moving-cutoff limit -/

/-- Once the elementary scale `S * V(w) → ∞` is supplied, the
absolute error `≤ 1` gives the desired relative asymptotic.  This
isolates the smallest remaining scalar statement; in particular it is
not a mean, variance, or Bonferroni hypothesis.  Positivity of the
denominator is obtained eventually from convergence to `atTop`. -/
theorem tendsto_earlyPresieveUniformMean_div_main_of_main_atTop
    (S w : ℕ → ℕ)
    (hmain : Tendsto (fun X =>
      (S X : ℝ) * eulerProdNat (w X)) atTop atTop) :
    Tendsto (fun X =>
      earlyPresieveUniformMean (S X) (w X) /
        ((S X : ℝ) * eulerProdNat (w X))) atTop (nhds 1) := by
  have hinv : Tendsto (fun X =>
      (((S X : ℝ) * eulerProdNat (w X))⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hmain
  have herr : ∀ X,
      |earlyPresieveUniformMean (S X) (w X) -
        (S X : ℝ) * eulerProdNat (w X)| ≤ 1 := fun X =>
    earlyPresieve_uniformMean_abs_sub_main_le_one (S X) (w X)
  have hpos : ∀ᶠ X in atTop,
      0 < (S X : ℝ) * eulerProdNat (w X) :=
    hmain.eventually
      (show ∀ᶠ y : ℝ in atTop, 0 < y from eventually_gt_atTop 0)
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨Ninv, hNinv⟩ := Metric.tendsto_atTop.mp hinv ε hε
  rw [eventually_atTop] at hpos
  obtain ⟨Npos, hNpos⟩ := hpos
  refine ⟨max Ninv Npos, fun X hX => ?_⟩
  have hden := hNpos X ((le_max_right Ninv Npos).trans hX)
  have hInv := hNinv X ((le_max_left Ninv Npos).trans hX)
  have hdenne : (S X : ℝ) * eulerProdNat (w X) ≠ 0 := hden.ne'
  have hre :
      earlyPresieveUniformMean (S X) (w X) /
          ((S X : ℝ) * eulerProdNat (w X)) - 1 =
        (earlyPresieveUniformMean (S X) (w X) -
          (S X : ℝ) * eulerProdNat (w X)) *
            (((S X : ℝ) * eulerProdNat (w X))⁻¹) := by
    rw [div_eq_mul_inv]
    calc
      earlyPresieveUniformMean (S X) (w X) *
          ((S X : ℝ) * eulerProdNat (w X))⁻¹ - 1 =
        earlyPresieveUniformMean (S X) (w X) *
            ((S X : ℝ) * eulerProdNat (w X))⁻¹ -
          ((S X : ℝ) * eulerProdNat (w X)) *
            ((S X : ℝ) * eulerProdNat (w X))⁻¹ := by
          rw [mul_inv_cancel₀ hdenne]
      _ = (earlyPresieveUniformMean (S X) (w X) -
          (S X : ℝ) * eulerProdNat (w X)) *
            ((S X : ℝ) * eulerProdNat (w X))⁻¹ := by ring
  have hInv' : (((S X : ℝ) * eulerProdNat (w X))⁻¹) < ε := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_pos (inv_pos.mpr hden)] using hInv
  rw [Real.dist_eq, hre, abs_mul,
    abs_of_pos (inv_pos.mpr hden)]
  exact (mul_le_mul_of_nonneg_right (herr X)
    (inv_nonneg.mpr hden.le)).trans_lt (by simpa using hInv')

/-! ## The paper scales -/

/-- At the paper's moving scales the main term escapes to infinity.
The deliberately crude inequality `V(w) ≥ 1/w` already suffices,
because `w = floor ((log (windowG X))^4)` while the small window has
size at least `windowG X` eventually. -/
theorem tendsto_ahlSmall_earlyPresieve_main_atTop
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      (ahlSmall_window κ X : ℝ) *
        eulerProdNat (presieveW (windowG X))) atTop atTop := by
  have hratio : Tendsto (fun X : ℕ =>
      Real.log (windowG X) ^ (4 : ℕ) / windowG X) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 4 one_ne_zero).comp tendsto_windowG_atTop
    refine h.congr' (Eventually.of_forall fun X => ?_)
    simp
  refine tendsto_atTop_atTop.mpr fun A => ?_
  by_cases hA : A ≤ 0
  · refine ⟨0, fun X _hX => ?_⟩
    exact hA.trans
      (mul_nonneg (Nat.cast_nonneg _) (eulerProdNat_pos _).le)
  · have hApos : 0 < A := lt_of_not_ge hA
    have hmetric := Metric.tendsto_atTop.mp hratio (1 / A)
      (one_div_pos.mpr hApos)
    have hmetricEv : ∀ᶠ X : ℕ in atTop,
        dist (Real.log (windowG X) ^ (4 : ℕ) / windowG X) 0 < 1 / A := by
      rw [eventually_atTop]
      exact hmetric
    have hAll : ∀ᶠ X : ℕ in atTop,
        dist (Real.log (windowG X) ^ (4 : ℕ) / windowG X) 0 < 1 / A ∧
          1 ≤ profileL κ X ∧
            max (5 : ℝ) (Real.exp 1) ≤ windowG X :=
      hmetricEv.and ((eventually_one_le_profileL hκ).and
        (tendsto_windowG_atTop.eventually_ge_atTop
          (max (5 : ℝ) (Real.exp 1))))
    rw [eventually_atTop] at hAll
    obtain ⟨N, hN⟩ := hAll
    refine ⟨N, fun X hX => ?_⟩
    obtain ⟨hratioX, hL, hGscale⟩ := hN X hX
    let G := windowG X
    let S := ahlSmall_window κ X
    let w := presieveW G
    have hG5 : (5 : ℝ) ≤ G :=
      (le_max_left (5 : ℝ) (Real.exp 1)).trans hGscale
    have hGexp : Real.exp 1 ≤ G :=
      (le_max_right (5 : ℝ) (Real.exp 1)).trans hGscale
    have hGpos : 0 < G := (Real.exp_pos 1).trans_le hGexp
    have hlog : (1 : ℝ) ≤ Real.log G := by
      calc
        (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log G := Real.log_le_log (Real.exp_pos 1) hGexp
    have hlog0 : 0 ≤ Real.log G := zero_le_one.trans hlog
    have hquot0 : 0 ≤ Real.log G ^ (4 : ℕ) / G :=
      div_nonneg (pow_nonneg hlog0 _) hGpos.le
    have hquot : Real.log G ^ (4 : ℕ) / G < 1 / A := by
      simpa only [G, Real.dist_eq, sub_zero, abs_of_nonneg hquot0] using hratioX
    have hlogDivRaw := (div_lt_iff₀ hGpos).mp hquot
    have hlogDiv : Real.log G ^ (4 : ℕ) < (1 / A) * G := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using hlogDivRaw
    have hAG : A * Real.log G ^ (4 : ℕ) < G := by
      have hlogDiv' : Real.log G ^ (4 : ℕ) < G / A := by
        simpa only [div_eq_mul_inv, one_div, one_mul, mul_one, mul_assoc,
          mul_comm] using hlogDiv
      have hAG' : Real.log G ^ (4 : ℕ) * A < G :=
        (lt_div_iff₀ hApos).mp hlogDiv'
      simpa only [mul_comm] using hAG'
    have hpow1 : (1 : ℝ) ≤ Real.log G ^ (4 : ℕ) := one_le_pow₀ hlog
    have hpow1' : ((1 : ℕ) : ℝ) ≤ Real.log G ^ (4 : ℕ) := by
      simpa using hpow1
    have hw1 : 1 ≤ w := by
      dsimp only [w]
      rw [presieveW_eq]
      exact Nat.le_floor hpow1'
    have hwpos : (0 : ℝ) < w := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hw1)
    have hwle : (w : ℝ) ≤ Real.log G ^ (4 : ℕ) := by
      dsimp only [w]
      rw [presieveW_eq]
      exact Nat.floor_le (pow_nonneg hlog0 _)
    have hAw : A * (w : ℝ) < G :=
      (mul_le_mul_of_nonneg_left hwle hApos.le).trans_lt hAG
    have hLR : (1 : ℝ) ≤ (profileL κ X : ℝ) := Nat.one_le_cast.mpr hL
    have hargLower :
        (6 / 5 : ℝ) * G ≤
          (6 / 5 : ℝ) * (profileL κ X : ℝ) * G := by
      have hc : (6 / 5 : ℝ) ≤
          (6 / 5 : ℝ) * (profileL κ X : ℝ) := by
        nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hGpos.le
    have hGarg : G + 1 ≤
        (6 / 5 : ℝ) * (profileL κ X : ℝ) * G := by
      nlinarith [hargLower]
    have hfloor :
        (6 / 5 : ℝ) * (profileL κ X : ℝ) * G < (S : ℝ) + 1 := by
      simpa only [S, G, ahlSmall_window_eq] using
        Nat.lt_floor_add_one
          ((6 / 5 : ℝ) * (profileL κ X : ℝ) * windowG X)
    have hGS : G ≤ (S : ℝ) := by
      linarith
    have hASdiv : A ≤ (S : ℝ) / (w : ℝ) := by
      apply (le_div_iff₀ hwpos).mpr
      exact hAw.le.trans hGS
    have hV := eulerProdNat_ge_inv w hw1
    calc
      A ≤ (S : ℝ) / (w : ℝ) := hASdiv
      _ = (S : ℝ) * ((w : ℝ)⁻¹) := by rw [div_eq_mul_inv]
      _ ≤ (S : ℝ) * eulerProdNat w :=
        mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)

/-- The early rooted first moment has relative main term `S V(w)` at
the paper cutoff.  No denominator assumption is present: its eventual
positivity follows from the preceding `atTop` limit. -/
theorem tendsto_earlyPresieveUniformMean_div_main
    {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X : ℕ =>
      earlyPresieveUniformMean (ahlSmall_window κ X)
          (presieveW (windowG X)) /
        ((ahlSmall_window κ X : ℝ) *
          eulerProdNat (presieveW (windowG X))))
      atTop (nhds 1) :=
  tendsto_earlyPresieveUniformMean_div_main_of_main_atTop
    (ahlSmall_window κ) (fun X => presieveW (windowG X))
    (tendsto_ahlSmall_earlyPresieve_main_atTop hκ)

end

end PrimeGapNormality.Prime
