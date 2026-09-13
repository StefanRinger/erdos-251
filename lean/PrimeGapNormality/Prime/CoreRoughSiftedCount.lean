import PrimeGapNormality.Prime.CoreRoughMixedCRT
import PrimeGapNormality.Prime.CoreRoughBetaMain
import PrimeGapNormality.Prime.CoreBetaArithmeticWeights
import PrimeGapNormality.Prime.CoreSquarefreeFactorizationCount
import Mathlib.NumberTheory.Primorial

/-!
# Actual signed beta sums for a sifted finite interval

Selected late-prime sublists are used directly. The Boolean Buchstab
sandwich supplies the interval inequalities, and mixed CRT supplies the
main/error comparison with the same coefficients.
-/

namespace PrimeGapNormality.Prime.CoreRoughSiftedCount

open Finset CoreBetaBuchstab CoreBetaLevelSupport CoreBetaArithmeticWeights
open CoreRoughMixedCRT
open scoped Classical
noncomputable section

set_option maxHeartbeats 1200000

def siftedInterval (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ)
    (a S : ℕ) : Finset ℕ := (Ico a (a + S)).filter (avoids B (P ∪ ps.toFinset))

def weightedCount (upper : Bool) (β : ℕ) (R : ℝ)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ) (a S : ℕ) : ℝ :=
  ∑ xs ∈ sublistFinset ps, coefficient upper (test β R) [] xs *
    ((mixedInterval B P xs.toFinset a S).card : ℝ)

def earlyDensity (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) : ℝ :=
  (earlyChoices B P : ℝ) / (CoreRoughResidueCount.residueModulus P : ℝ)

def coefficientError (upper : Bool) (β : ℕ) (R : ℝ)
    (B : ∀ p : ℕ, Finset (Fin p)) (ps : List ℕ) : ℝ :=
  ∑ xs ∈ sublistFinset ps, |coefficient upper (test β R) [] xs| *
    (lateChoices B xs.toFinset : ℝ)

theorem sublist_of_mem {ps xs : List ℕ} (hx : xs ∈ sublistFinset ps) : List.Sublist xs ps :=
  List.mem_sublists'.mp (List.mem_toFinset.mp hx)

theorem main_eq_finset_sum (upper : Bool) (A : List ℕ → Prop) (ps : List ℕ)
    (hn : ps.Nodup) (g : ℕ → ℝ) :
    main upper A [] ps g =
      ∑ xs ∈ sublistFinset ps, coefficient upper A [] xs * product g xs := by
  exact (List.sum_toFinset (fun xs : List ℕ => coefficient upper A [] xs * product g xs)
    (List.nodup_sublists'.mpr hn)).symm

theorem product_boolean (h : ℕ → Prop) (ps : List ℕ) :
    product (fun p : ℕ => if h p then (1 : ℝ) else 0) ps =
      if ∀ p ∈ ps, h p then 1 else 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [product_cons, ih]
    by_cases hp : h p <;> simp [hp]

theorem mixedInterval_card_eq_sum
    (B : ∀ p : ℕ, Finset (Fin p)) (P D : Finset ℕ) (a S : ℕ) :
    ((mixedInterval B P D a S).card : ℝ) =
      ∑ n ∈ Ico a (a + S),
        (if avoids B P n then (1 : ℝ) else 0) * (if hits B D n then 1 else 0) := by
  have heq (n : ℕ) :
      (if avoids B P n then (1 : ℝ) else 0) * (if hits B D n then 1 else 0) =
        if avoids B P n ∧ hits B D n then 1 else 0 := by
    by_cases hP : avoids B P n <;> by_cases hD : hits B D n <;> simp [hP, hD]
  simp_rw [heq]
  rw [← Finset.sum_filter]
  simp [mixedInterval]

theorem weightedCount_eq_sum_main (upper : Bool) (β : ℕ) (R : ℝ)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ)
    (hn : ps.Nodup) (a S : ℕ) :
    weightedCount upper β R B P ps a S =
      ∑ n ∈ Ico a (a + S), (if avoids B P n then (1 : ℝ) else 0) *
        main upper (test β R) [] ps (fun p : ℕ => if hit B p n then 1 else 0) := by
  unfold weightedCount
  simp_rw [mixedInterval_card_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hnI
  rw [main_eq_finset_sum upper (test β R) ps hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs hxs
  rw [product_boolean]
  have hh : hits B xs.toFinset n ↔ ∀ p ∈ xs, hit B p n := by
    simp only [hits, List.mem_toFinset]
  rw [hh]
  ring

/-- The actual interval count is bracketed by the actual signed sums.
This Boolean formulation includes n=0 and never takes divisors of zero. -/
theorem weightedCount_sandwich (β : ℕ) (R : ℝ)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ)
    (hn : ps.Nodup) (a S : ℕ) :
    weightedCount false β R B P ps a S ≤ ((siftedInterval B P ps a S).card : ℝ) ∧
      ((siftedInterval B P ps a S).card : ℝ) ≤ weightedCount true β R B P ps a S := by
  have hcount : ((siftedInterval B P ps a S).card : ℝ) =
      ∑ n ∈ Ico a (a + S), (if avoids B P n then (1 : ℝ) else 0) *
        (if ∀ p ∈ ps, ¬hit B p n then 1 else 0) := by
    have heq (n : ℕ) :
        (if avoids B P n then (1 : ℝ) else 0) *
          (if ∀ p ∈ ps, ¬hit B p n then 1 else 0) =
        if avoids B (P ∪ ps.toFinset) n then 1 else 0 := by
      have hh : avoids B (P ∪ ps.toFinset) n ↔
          avoids B P n ∧ ∀ p ∈ ps, ¬hit B p n := by
        simp only [avoids, mem_union, List.mem_toFinset, or_imp, forall_and]
      rw [hh]
      by_cases hP : avoids B P n <;> by_cases hps : ∀ p ∈ ps, ¬hit B p n <;> simp [hP, hps]
    simp_rw [heq]
    rw [← Finset.sum_filter]
    simp [siftedInterval]
  rw [weightedCount_eq_sum_main false β R B P ps hn,
    weightedCount_eq_sum_main true β R B P ps hn, hcount]
  constructor
  · apply Finset.sum_le_sum
    intro n hnI
    exact mul_le_mul_of_nonneg_left (boolean_sieve_sandwich (test β R) ps (fun p => hit B p n)).1
      (by split_ifs <;> norm_num)
  · apply Finset.sum_le_sum
    intro n hnI
    exact mul_le_mul_of_nonneg_left (boolean_sieve_sandwich (test β R) ps (fun p => hit B p n)).2
      (by split_ifs <;> norm_num)

theorem localProduct_eq_choices_div (B : ∀ p : ℕ, Finset (Fin p))
    (xs : List ℕ) (hn : xs.Nodup) :
    product (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) xs =
      (lateChoices B xs.toFinset : ℝ) / (CoreRoughResidueCount.residueModulus xs.toFinset : ℝ) := by
  unfold product lateChoices CoreRoughResidueCount.residueModulus
  rw [← List.prod_toFinset _ hn, Finset.prod_div_distrib]
  simp only [Nat.cast_prod]

/-- Exact mixed CRT, summed with the actual signed beta coefficients. -/
theorem weightedCount_main_error (upper : Bool) (β : ℕ) (R : ℝ)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ)
    (hn : ps.Nodup) (hdis : Disjoint P ps.toFinset)
    (hprime : ∀ p ∈ P ∪ ps.toFinset, Nat.Prime p) (a S : ℕ) :
    |weightedCount upper β R B P ps a S -
      (S : ℝ) * earlyDensity B P *
        main upper (test β R) [] ps (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ))| ≤
      (earlyChoices B P : ℝ) * coefficientError upper β R B ps := by
  have hterm (xs : List ℕ) (hx : xs ∈ sublistFinset ps) :
      |((mixedInterval B P xs.toFinset a S).card : ℝ) -
        (S : ℝ) * earlyDensity B P *
          product (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) xs| ≤
        (earlyChoices B P : ℝ) * (lateChoices B xs.toFinset : ℝ) := by
    have hs := sublist_of_mem hx
    have hsub : xs.toFinset ⊆ ps.toFinset := fun p hp =>
      List.mem_toFinset.mpr (hs.subset (List.mem_toFinset.mp hp))
    have hd : Disjoint P xs.toFinset := hdis.mono_right hsub
    have hp : ∀ p : ↥(P ∪ xs.toFinset), Nat.Prime p.1 := fun p =>
      hprime p.1 ((Finset.union_subset_union (Subset.refl P) hsub) p.2)
    have hh := mixedInterval_count_error B P xs.toFinset hd hp a S
    rw [localProduct_eq_choices_div B xs (List.Pairwise.sublist hs hn)]
    convert hh using 1 <;>
      simp only [earlyDensity, CoreRoughResidueCount.residueModulus, div_eq_mul_inv, mul_inv] <;> ring
  rw [weightedCount, main_eq_finset_sum upper (test β R) ps hn,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ xs ∈ sublistFinset ps,
        |coefficient upper (test β R) [] xs| *
          ((earlyChoices B P : ℝ) * (lateChoices B xs.toFinset : ℝ)) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro xs hx
      have hid : coefficient upper (test β R) [] xs *
          ((mixedInterval B P xs.toFinset a S).card : ℝ) -
          (S : ℝ) * earlyDensity B P *
            (coefficient upper (test β R) [] xs *
              product (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) xs) =
        coefficient upper (test β R) [] xs *
          (((mixedInterval B P xs.toFinset a S).card : ℝ) -
            (S : ℝ) * earlyDensity B P *
              product (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) xs) := by ring
      rw [hid, abs_mul]
      exact mul_le_mul_of_nonneg_left (hterm xs hx) (abs_nonneg _)
    _ = _ := by
      rw [coefficientError, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xs hx
      ring

/-- The error support consists of distinct squarefree products below the
actual real level. Its mass is bounded by the existing ordered-factorization
sum, not by the number of all prime subsets. -/
theorem coefficientError_le_factorization
    {β : ℕ} (hβ : 1 ≤ β) {Z R : ℝ} (hZ : 1 ≤ Z) (hR : 1 < R)
    (hlevel : Z ^ β ≤ R) (upper : Bool)
    (B : ∀ p : ℕ, Finset (Fin p)) (ps : List ℕ)
    (hdec : ps.Pairwise (fun p q => q < p)) (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hbelow : ∀ (p : ℕ), p ∈ ps → (p : ℝ) < Z)
    {k : ℕ} (hk : 1 ≤ k) (hν : ∀ p ∈ ps, (B p).card ≤ k) :
    coefficientError upper β R B ps ≤
      (⌈R⌉₊ : ℝ) * (1 + Real.log (⌈R⌉₊ : ℝ)) ^ (k - 1) := by
  let T := (sublistFinset ps).filter (fun xs : List ℕ => coefficient upper (test β R) [] xs ≠ 0)
  have heq : (∑ xs ∈ T, |coefficient upper (test β R) [] xs| *
      (lateChoices B xs.toFinset : ℝ)) = coefficientError upper β R B ps := by
    unfold coefficientError
    apply Finset.sum_subset (filter_subset _ _)
    intro xs hx hnot
    have hc : coefficient upper (test β R) [] xs = 0 := by
      by_contra hc
      exact hnot (mem_filter.mpr ⟨hx, hc⟩)
    simp [hc]
  have hprodMem : ∀ xs ∈ T, xs.prod ∈ Ico 1 ⌈R⌉₊ := by
    intro xs hx
    have hxs := mem_filter.mp hx
    have hs := sublist_of_mem hxs.1
    have hpos : 0 < xs.prod := List.prod_pos (fun p hp => (hprime p (hs.subset hp)).pos)
    have hlt := coefficient_ne_zero_product_lt hβ hZ hR hlevel upper xs
      (List.Pairwise.sublist hs hdec) (fun p hp => hprime p (hs.subset hp))
      (fun p hp => hbelow p (hs.subset hp)) hxs.2
    have hreal : (xs.prod : ℝ) < R := by simpa [natProduct, product] using hlt
    exact mem_Ico.mpr ⟨hpos, Nat.lt_ceil.mpr hreal⟩
  have hpoint : ∀ xs ∈ T, (lateChoices B xs.toFinset : ℝ) ≤
      (CoreOrderedFactorizationBound.orderedFactorizationCount k xs.prod : ℝ) := by
    intro xs hx
    have hs := sublist_of_mem (mem_filter.mp hx).1
    have hp : List.Perm xs xs.prod.primeFactorsList :=
      Nat.primeFactorsList_unique rfl (fun p hp => hprime p (hs.subset hp))
    have hf : xs.toFinset = xs.prod.primeFactors := by
      ext p
      change p ∈ xs.toFinset ↔ p ∈ xs.prod.primeFactorsList.toFinset
      simp only [List.mem_toFinset]
      exact hp.mem_iff
    have hh := CoreSquarefreeFactorizationCount.prod_primeFactors_le_orderedFactorizationCount
      hk (squarefree_prod_of_prime_sublist hdec hprime hs) (fun p => (B p).card)
      (fun p hp => hν p (hs.subset (List.mem_toFinset.mp (hf.symm ▸ hp))))
    exact_mod_cast (show lateChoices B xs.toFinset ≤
      CoreOrderedFactorizationBound.orderedFactorizationCount k xs.prod from by
        simpa only [lateChoices, hf] using hh)
  have hinj : Set.InjOn List.prod (T : Set (List ℕ)) := by
    intro xs hx ys hy hxy
    exact sublist_prod_injective hdec hprime (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy
  rw [← heq]
  calc
    _ ≤ ∑ xs ∈ T, (CoreOrderedFactorizationBound.orderedFactorizationCount k xs.prod : ℝ) := by
      apply Finset.sum_le_sum
      intro xs hx
      exact (mul_le_of_le_one_left (Nat.cast_nonneg _)
        (coefficient_abs_le_one upper (test β R) [] xs)).trans (hpoint xs hx)
    _ = ∑ d ∈ T.image List.prod, (CoreOrderedFactorizationBound.orderedFactorizationCount k d : ℝ) :=
      (Finset.sum_image (f := fun d : ℕ ↦
        (CoreOrderedFactorizationBound.orderedFactorizationCount k d : ℝ)) hinj).symm
    _ ≤ ∑ d ∈ Ico 1 ⌈R⌉₊, (CoreOrderedFactorizationBound.orderedFactorizationCount k d : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨xs, hx, rfl⟩ := mem_image.mp hd
        exact hprodMem xs hx
      · intro d hd hn
        exact Nat.cast_nonneg _
    _ ≤ _ := CoreOrderedFactorizationBound.orderedFactorizationSum_lt_le k ⌈R⌉₊ hk
      (Nat.one_le_ceil_iff.mpr (zero_lt_one.trans hR))

/-- The genuine finite interval count estimate with explicit early choices.
The remaining ceiling in the additive term is only the exact conversion
of the strict real support d<R to a natural finite sum. -/
theorem siftedInterval_error
    {c y k : ℕ} (hc : c ≤ y) (hy : 16 ≤ y) (hk : 1 ≤ k)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ)
    (hdec : ps.Pairwise (fun p q => q < p))
    (hps : ps.toFinset = CoreRoughDimensionProduct.dimensionPrimeBand c y k)
    (hdis : Disjoint P ps.toFinset)
    (hprime : ∀ p ∈ P ∪ ps.toFinset, Nat.Prime p)
    (hν : ∀ p ∈ ps, (B p).card ≤ k)
    {Z R : ℝ} (hZlo : (y : ℝ) < Z) (hZhi : Z ≤ (y : ℝ) + 1)
    (hlevel : Z ^ (9 * k + 1) ≤ R) (a S : ℕ) :
    |((siftedInterval B P ps a S).card : ℝ) -
      (S : ℝ) * earlyDensity B P *
        euler (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) ps| ≤
      (S : ℝ) * earlyDensity B P *
        euler (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) ps *
          Real.exp (299 * (k : ℝ) - Real.log R / Real.log Z) +
      (earlyChoices B P : ℝ) * (⌈R⌉₊ : ℝ) *
        (1 + Real.log (⌈R⌉₊ : ℝ)) ^ (k - 1) := by
  let g := fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)
  let M := (S : ℝ) * earlyDensity B P
  let E := Real.exp (299 * (k : ℝ) - Real.log R / Real.log Z)
  let T := (⌈R⌉₊ : ℝ) * (1 + Real.log (⌈R⌉₊ : ℝ)) ^ (k - 1)
  have hn : ps.Nodup := hdec.imp (fun h => Ne.symm h.ne)
  have hprime' : ∀ p ∈ ps, Nat.Prime p := fun p hp =>
    hprime p (mem_union_right P (List.mem_toFinset.mpr hp))
  have hν' : ∀ p ∈ CoreRoughDimensionProduct.dimensionPrimeBand c y k, (B p).card ≤ k := by
    intro p hp
    exact hν p (List.mem_toFinset.mp (hps.symm ▸ hp))
  have hbelow : ∀ (p : ℕ), p ∈ ps → (p : ℝ) < Z := by
    intro p hp
    have hmem : p ∈ CoreRoughDimensionProduct.dimensionPrimeBand c y k :=
      hps ▸ List.mem_toFinset.mpr hp
    exact (Nat.cast_le.mpr (CoreRoughRealCutDimension.mem_dimensionPrimeBand_iff.mp hmem).2.2).trans_lt hZlo
  have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hy
  have hZ : 1 < Z := by linarith
  have hR : 1 < R := hZ.trans_le
    ((le_self_pow₀ hZ.le (by omega : 9 * k + 1 ≠ 0)).trans hlevel)
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hweight (upper : Bool) :
      |weightedCount upper (9 * k + 1) R B P ps a S - M * euler g ps| ≤
        (earlyChoices B P : ℝ) * T + M * (E * euler g ps) := by
    have hcrt := weightedCount_main_error upper (9 * k + 1) R B P ps hn hdis hprime a S
    have herr := coefficientError_le_factorization (by omega : 1 ≤ 9 * k + 1)
      hZ.le hR hlevel upper B ps hdec hprime' hbelow hk hν
    have hcrt' := hcrt.trans (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg _))
    have hbeta := CoreRoughBetaMain.main_abs_sub_euler_le hc hy hk
      (fun p => (B p).card) hν' ps hdec hps hZlo hZhi hlevel upper
    have hbeta' := mul_le_mul_of_nonneg_left hbeta hM
    calc
      _ ≤ |weightedCount upper (9 * k + 1) R B P ps a S -
          M * main upper (test (9 * k + 1) R) [] ps g| +
          |M * main upper (test (9 * k + 1) R) [] ps g - M * euler g ps| :=
        abs_sub_le _ _ _
      _ ≤ (earlyChoices B P : ℝ) * T + M * (E * euler g ps) := by
        apply _root_.add_le_add hcrt'
        rw [← mul_sub, abs_mul, abs_of_nonneg hM]
        exact hbeta'
  have hlo := (abs_le.mp (hweight false)).1
  have hhi := (abs_le.mp (hweight true)).2
  have hs := weightedCount_sandwich (9 * k + 1) R B P ps hn a S
  apply abs_le.mpr
  dsimp only [M, E, T, g] at hlo hhi
  constructor <;> nlinarith [hs.1, hs.2]

theorem ceil_envelope_le {k : ℕ} (hk : 1 ≤ k) {R : ℝ} (hR : 1 < R) :
    (⌈R⌉₊ : ℝ) * (1 + Real.log (⌈R⌉₊ : ℝ)) ^ (k - 1) ≤
      Real.exp (k : ℝ) * R * (1 + Real.log R) ^ (k - 1) := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hceil : (⌈R⌉₊ : ℝ) ≤ 2 * R := by
    have hh := Nat.ceil_lt_add_one hR0.le
    linarith
  have hcpos : 0 < (⌈R⌉₊ : ℝ) := hR0.trans_le (Nat.le_ceil R)
  have hlogR : 0 ≤ Real.log R := (Real.log_pos hR).le
  have hlog : 1 + Real.log (⌈R⌉₊ : ℝ) ≤ 2 * (1 + Real.log R) := by
    have hh := Real.log_le_log hcpos hceil
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR0.ne'] at hh
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hbase : 0 ≤ 1 + Real.log (⌈R⌉₊ : ℝ) := by
    have hc1 : 1 ≤ (⌈R⌉₊ : ℝ) := hR.le.trans (Nat.le_ceil R)
    exact add_nonneg zero_le_one (Real.log_nonneg hc1)
  have hpow := pow_le_pow_left₀ hbase hlog (k - 1)
  have htwo : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
    have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    simpa only [← Real.exp_nat_mul, mul_one] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hh k
  calc
    _ ≤ (2 * R) * (2 * (1 + Real.log R)) ^ (k - 1) :=
      mul_le_mul hceil hpow (pow_nonneg hbase _) (by positivity)
    _ = 2 ^ k * R * (1 + Real.log R) ^ (k - 1) := by
      have hp : (2 : ℝ) ^ k = 2 ^ (k - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      rw [mul_pow, hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htwo hR0.le) (pow_nonneg (by linarith) _)

theorem earlyChoices_le_exp {k : ℕ} (B : ∀ p : ℕ, Finset (Fin p))
    (P : Finset ℕ) (hP : P ⊆ Nat.primesLE (4 * k)) :
    (earlyChoices B P : ℝ) ≤ Real.exp (8 * (k : ℝ)) := by
  have hchoice : earlyChoices B P ≤ ∏ p ∈ P, p :=
    Finset.prod_le_prod' (fun p hp => Nat.sub_le p (B p).card)
  have hprod : (∏ p ∈ P, p : ℕ) ≤ ∏ p ∈ Nat.primesLE (4 * k), p :=
    Finset.prod_le_prod_of_subset_of_one_le hP (fun p hp => Nat.zero_le p)
      (fun p hp hn => (Nat.mem_primesLE.mp hp).2.one_lt.le)
  have hprim : (earlyChoices B P : ℝ) ≤ (4 : ℝ) ^ (4 * k) := by
    exact_mod_cast hchoice.trans (hprod.trans
      (by simpa only [primorial_eq_prod_primesLE] using primorial_le_four_pow (4 * k)))
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 2
    rw [← Real.exp_nat_mul] at hh
    norm_num only [Nat.cast_ofNat, mul_one] at hh
    exact hh
  calc
    _ ≤ (Real.exp 2) ^ (4 * k) :=
      hprim.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hfour (4 * k))
    _ = Real.exp (8 * (k : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Absolute-constant additive error in the paper's real-level convention.
The exponent ten is deliberately generous. -/
theorem early_ceil_error_le {k : ℕ} (hk : 1 ≤ k) {R : ℝ} (hR : 1 < R)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE (4 * k)) :
    (earlyChoices B P : ℝ) * (⌈R⌉₊ : ℝ) * (1 + Real.log (⌈R⌉₊ : ℝ)) ^ (k - 1) ≤
      Real.exp (10 * (k : ℝ)) * R * (1 + Real.log R) ^ (k - 1) := by
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hfac : 0 ≤ R * (1 + Real.log R) ^ (k - 1) :=
    mul_nonneg hR0.le (pow_nonneg (by linarith [Real.log_pos hR]) _)
  calc
    _ = (earlyChoices B P : ℝ) *
        ((⌈R⌉₊ : ℝ) * (1 + Real.log (⌈R⌉₊ : ℝ)) ^ (k - 1)) := by ring
    _ ≤ (earlyChoices B P : ℝ) *
        (Real.exp (k : ℝ) * R * (1 + Real.log R) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left (ceil_envelope_le hk hR) (Nat.cast_nonneg _)
    _ ≤ Real.exp (8 * (k : ℝ)) *
        (Real.exp (k : ℝ) * R * (1 + Real.log R) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_right (earlyChoices_le_exp B P hP)
        (by simpa only [mul_assoc] using mul_nonneg (Real.exp_pos (k : ℝ)).le hfac)
    _ = Real.exp (9 * (k : ℝ)) * (R * (1 + Real.log R) ^ (k - 1)) := by
      calc
        _ = (Real.exp (8 * (k : ℝ)) * Real.exp (k : ℝ)) *
            (R * (1 + Real.log R) ^ (k - 1)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2 <;> ring
    _ ≤ Real.exp (10 * (k : ℝ)) * (R * (1 + Real.log R) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)) hfac
    _ = _ := by ring

theorem siftedInterval_error_absolute
    {c y k : ℕ} (hc : c ≤ y) (hy : 16 ≤ y) (hk : 1 ≤ k)
    (B : ∀ p : ℕ, Finset (Fin p)) (P : Finset ℕ) (ps : List ℕ)
    (hdec : ps.Pairwise (fun p q => q < p))
    (hps : ps.toFinset = CoreRoughDimensionProduct.dimensionPrimeBand c y k)
    (hdis : Disjoint P ps.toFinset) (hP : P ⊆ Nat.primesLE (4 * k))
    (hprime : ∀ p ∈ P ∪ ps.toFinset, Nat.Prime p)
    (hν : ∀ p ∈ ps, (B p).card ≤ k)
    {Z R : ℝ} (hZlo : (y : ℝ) < Z) (hZhi : Z ≤ (y : ℝ) + 1)
    (hlevel : Z ^ (9 * k + 1) ≤ R) (a S : ℕ) :
    |((siftedInterval B P ps a S).card : ℝ) -
      (S : ℝ) * earlyDensity B P *
        euler (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) ps| ≤
      (S : ℝ) * earlyDensity B P *
        euler (fun p : ℕ => ((B p).card : ℝ) / (p : ℝ)) ps *
          Real.exp (299 * (k : ℝ) - Real.log R / Real.log Z) +
      Real.exp (10 * (k : ℝ)) * R * (1 + Real.log R) ^ (k - 1) := by
  have hyR : (16 : ℝ) ≤ y := by exact_mod_cast hy
  have hZ : 1 < Z := by linarith
  have hR : 1 < R := hZ.trans_le
    ((le_self_pow₀ hZ.le (by omega : 9 * k + 1 ≠ 0)).trans hlevel)
  exact (siftedInterval_error hc hy hk B P ps hdec hps hdis hprime hν hZlo hZhi hlevel a S).trans
    (_root_.add_le_add le_rfl (early_ceil_error_le hk hR B P hP))

end
end PrimeGapNormality.Prime.CoreRoughSiftedCount
