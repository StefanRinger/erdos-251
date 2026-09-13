import PrimeGapNormality.Prime.PresieveSmallEarlyMean
import PrimeGapNormality.Prime.SelbergCrtInterval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum

/-!
# Uniform Brun estimate on every rooted early-presieve fibre

For a fixed early residue choice `τ`, this file applies adjacent
Bonferroni ranks to the number of forbidden classes hit by a candidate.
Every intersection occurring in the truncation is one CRT class modulo
the product of a set of distinct primes, and therefore has interval
rounding error at most one.

The resulting error is completely explicit.  If

`H = ∑_{p∈P} 1/p ≤ T` and `2T ≤ s+1`,

then the survivor count differs from `S ∏_{p∈P}(1-1/p)` by at most

`2(s+1)(#P+1)^(s+1) + 3 S T^(s+1)/(s+1)!`.

The pointwise remainder at rank `s` is precisely the magnitude of the
next, adjacent rank `s+1`; thus both Bonferroni directions are retained.
No averaging in `τ`, AHL, or Kuperberg hypothesis is used.
-/

open Filter Finset
open scoped Topology Classical Function

namespace PrimeGapNormality.Prime

noncomputable section

/-! ## Explicit symmetric sums and error -/

/-- Elementary symmetric sum of reciprocal moduli. -/
def earlyBrunElemSym (P : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ U ∈ P.powersetCard k, ∏ p ∈ U, (p : ℝ)⁻¹

/-- Harmonic mass of the exposed prime coordinates. -/
def earlyBrunHarmonic (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (p : ℝ)⁻¹

/-- Explicit finite Brun/CRT error.  The first summand pays all CRT
rounding errors through the adjacent rank; the second pays the
elementary-symmetric tail. -/
def earlyPresieveBrunError (S w s : ℕ) (T : ℝ) : ℝ :=
  2 * ((s : ℝ) + 1) * (((Nat.primesLE w).card : ℝ) + 1) ^ (s + 1) +
    3 * (S : ℝ) * T ^ (s + 1) / ((s + 1).factorial : ℝ)

theorem earlyPresieveBrunError_nonneg {S w s : ℕ} {T : ℝ}
    (hT : 0 ≤ T) :
    0 ≤ earlyPresieveBrunError S w s T := by
  unfold earlyPresieveBrunError
  positivity

private theorem earlyBrun_harmonic_nonneg (P : Finset ℕ) :
    0 ≤ earlyBrunHarmonic P :=
  sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem earlyBrun_elemSym_nonneg (P : Finset ℕ) (k : ℕ) :
    0 ≤ earlyBrunElemSym P k :=
  sum_nonneg fun U _ => prod_nonneg fun p _ =>
    inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem earlyBrun_elemSym_erase_le {P : Finset ℕ} {k p : ℕ}
    (hp : p ∈ P) :
    earlyBrunElemSym (P.erase p) k ≤ earlyBrunElemSym P k := by
  have hsub : (P.erase p).powersetCard k ⊆ P.powersetCard k := by
    intro U hU
    exact mem_powersetCard.mpr
      ⟨(mem_powersetCard.mp hU).1.trans (erase_subset p P),
        (mem_powersetCard.mp hU).2⟩
  exact sum_le_sum_of_subset_of_nonneg hsub fun U _ _ =>
    prod_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem earlyBrun_sum_powersetCard_mem {P : Finset ℕ}
    {k p : ℕ} (hp : p ∈ P) (f : Finset ℕ → ℝ) :
    ∑ U ∈ (P.powersetCard (k + 1)).filter (fun U => p ∈ U), f U =
      ∑ V ∈ (P.erase p).powersetCard k, f (insert p V) := by
  refine sum_bij'
      (fun U _ => U.erase p) (fun V _ => insert p V) ?_ ?_ ?_ ?_ ?_
  · intro U hU
    have ⟨hUpow, hpU⟩ := mem_filter.mp hU
    have ⟨hUsub, hUcard⟩ := mem_powersetCard.mp hUpow
    refine mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      exact mem_erase.mpr
        ⟨ne_of_mem_erase hx, hUsub (mem_of_mem_erase hx)⟩
    · rw [card_erase_of_mem hpU, hUcard]
      omega
  · intro V hV
    have ⟨hVsub, hVcard⟩ := mem_powersetCard.mp hV
    have hpV : p ∉ V := fun h =>
      (mem_erase.mp (hVsub h)).1 rfl
    refine mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, mem_insert_self _ _⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hxV
      · exact hp
      · exact mem_of_mem_erase (hVsub hxV)
    · rw [card_insert_of_notMem hpV, hVcard]
  · intro U hU
    exact insert_erase (mem_filter.mp hU).2
  · intro V hV
    have hpV : p ∉ V := fun h =>
      (mem_erase.mp ((mem_powersetCard.mp hV).1 h)).1 rfl
    exact erase_insert hpV
  · intro U hU
    rw [insert_erase (mem_filter.mp hU).2]

private theorem earlyBrun_elemSym_succ_mul {P : Finset ℕ} (k : ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    ((k + 1 : ℕ) : ℝ) * earlyBrunElemSym P (k + 1) ≤
      earlyBrunHarmonic P * earlyBrunElemSym P k := by
  have hswap :
      ∑ U ∈ P.powersetCard (k + 1),
          ∑ p ∈ U, ∏ q ∈ U, (q : ℝ)⁻¹ =
        ∑ p ∈ P, ∑ V ∈ (P.erase p).powersetCard k,
          ∏ q ∈ insert p V, (q : ℝ)⁻¹ := by
    have hite :
        ∑ U ∈ P.powersetCard (k + 1),
            ∑ p ∈ U, ∏ q ∈ U, (q : ℝ)⁻¹ =
          ∑ U ∈ P.powersetCard (k + 1),
            ∑ p ∈ P, if p ∈ U then ∏ q ∈ U, (q : ℝ)⁻¹ else 0 := by
      refine sum_congr rfl fun U hU => ?_
      have hUsub := (mem_powersetCard.mp hU).1
      rw [← sum_filter, filter_mem_eq_inter,
        inter_eq_right.mpr hUsub]
    rw [hite, sum_comm]
    refine sum_congr rfl fun p hp => ?_
    rw [← sum_filter]
    exact earlyBrun_sum_powersetCard_mem hp _
  have hcard : ∀ U ∈ P.powersetCard (k + 1),
      ((k + 1 : ℕ) : ℝ) * ∏ q ∈ U, (q : ℝ)⁻¹ =
        ∑ _p ∈ U, ∏ q ∈ U, (q : ℝ)⁻¹ := by
    intro U hU
    have hUc := (mem_powersetCard.mp hU).2
    simpa [hUc, nsmul_eq_mul] using
      (show (U.card : ℝ) * ∏ q ∈ U, (q : ℝ)⁻¹ =
          ∑ _p ∈ U, ∏ q ∈ U, (q : ℝ)⁻¹ by
        rw [← nsmul_eq_mul, ← sum_const])
  have hleft :
      ((k + 1 : ℕ) : ℝ) * earlyBrunElemSym P (k + 1) =
        ∑ U ∈ P.powersetCard (k + 1),
          ∑ p ∈ U, ∏ q ∈ U, (q : ℝ)⁻¹ := by
    unfold earlyBrunElemSym
    rw [mul_sum]
    exact sum_congr rfl hcard
  rw [hleft, hswap]
  have hterm : ∀ p ∈ P,
      ∑ V ∈ (P.erase p).powersetCard k,
          ∏ q ∈ insert p V, (q : ℝ)⁻¹ =
        (p : ℝ)⁻¹ * earlyBrunElemSym (P.erase p) k := by
    intro p hp
    have hpV : ∀ V ∈ (P.erase p).powersetCard k, p ∉ V := by
      intro V hV hmem
      exact (mem_erase.mp ((mem_powersetCard.mp hV).1 hmem)).1 rfl
    have hprod : ∀ V ∈ (P.erase p).powersetCard k,
        ∏ q ∈ insert p V, (q : ℝ)⁻¹ =
          (p : ℝ)⁻¹ * ∏ q ∈ V, (q : ℝ)⁻¹ := by
      intro V hV
      exact prod_insert (hpV V hV)
    rw [sum_congr rfl hprod, ← mul_sum]
    rfl
  rw [sum_congr rfl hterm]
  have hle : ∀ p ∈ P,
      (p : ℝ)⁻¹ * earlyBrunElemSym (P.erase p) k ≤
        (p : ℝ)⁻¹ * earlyBrunElemSym P k := fun p hp =>
    mul_le_mul_of_nonneg_left (earlyBrun_elemSym_erase_le hp)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  refine (sum_le_sum hle).trans_eq ?_
  rw [← sum_mul]
  rfl

private theorem earlyBrun_elemSym_le_pow_div_factorial
    {P : Finset ℕ} (k : ℕ) (hP : ∀ p ∈ P, 0 < p) :
    earlyBrunElemSym P k ≤
      earlyBrunHarmonic P ^ k / (k.factorial : ℝ) := by
  induction k with
  | zero => simp [earlyBrunElemSym, earlyBrunHarmonic]
  | succ k ih =>
    have hmul := earlyBrun_elemSym_succ_mul k hP
    have hfac : (((k + 1).factorial : ℕ) : ℝ) =
        ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      simp [Nat.factorial_succ]
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr k.succ_pos
    have hnn : 0 ≤ earlyBrunHarmonic P := earlyBrun_harmonic_nonneg P
    have hnum := hmul.trans <| by
      have h := mul_le_mul_of_nonneg_left ih hnn
      have hrew : earlyBrunHarmonic P *
            (earlyBrunHarmonic P ^ k / (k.factorial : ℝ)) =
          earlyBrunHarmonic P ^ (k + 1) / (k.factorial : ℝ) := by
        rw [pow_succ]
        field_simp
      exact h.trans (le_of_eq hrew)
    have hdiv := div_le_div_of_nonneg_right hnum hkpos.le
    have hleft :
        ((k + 1 : ℕ) : ℝ) * earlyBrunElemSym P (k + 1) /
            ((k + 1 : ℕ) : ℝ) = earlyBrunElemSym P (k + 1) := by
      field_simp [hkpos.ne']
    have hright :
        (earlyBrunHarmonic P ^ (k + 1) / (k.factorial : ℝ)) /
            ((k + 1 : ℕ) : ℝ) =
          earlyBrunHarmonic P ^ (k + 1) /
            (((k + 1).factorial : ℕ) : ℝ) := by
      rw [hfac]
      field_simp [hkpos.ne']
    rwa [hleft, hright] at hdiv

private theorem earlyBrun_factorial_mul_pow_le {s k : ℕ}
    (h : s + 1 ≤ k) :
    (s + 1).factorial * (s + 2) ^ (k - (s + 1)) ≤ k.factorial := by
  refine Nat.le_induction ?_ ?_ k h
  · simp
  · intro k hk ih
    have hge : s + 2 ≤ k + 1 := by omega
    calc
      (s + 1).factorial * (s + 2) ^ (k + 1 - (s + 1)) =
          ((s + 1).factorial * (s + 2) ^ (k - (s + 1))) *
            (s + 2) := by
              rw [show k + 1 - (s + 1) = k - (s + 1) + 1 by omega,
                pow_succ]
              ring
      _ ≤ k.factorial * (s + 2) := Nat.mul_le_mul_right _ ih
      _ ≤ k.factorial * (k + 1) := Nat.mul_le_mul_left _ hge
      _ = (k + 1).factorial := by rw [Nat.factorial_succ, Nat.mul_comm]

private theorem earlyBrun_sum_half_pow_le (N : ℕ) :
    ∑ j ∈ range N, ((1 : ℝ) / 2) ^ j ≤ 2 := by
  have hx : ((1 : ℝ) / 2) ≠ 1 := by norm_num
  have hsum := geom_sum_eq hx N
  rw [hsum]
  have hden0 : ((1 : ℝ) / 2 - 1) ≠ 0 := by norm_num
  have hrew :
      (((1 : ℝ) / 2) ^ N - 1) / ((1 : ℝ) / 2 - 1) =
        2 * (1 - ((1 : ℝ) / 2) ^ N) := by
    field_simp [hden0]
    ring
  rw [hrew]
  have hpow0 : 0 ≤ ((1 : ℝ) / 2) ^ N := pow_nonneg (by norm_num) _
  have hle : 2 * (1 - ((1 : ℝ) / 2) ^ N) ≤ 2 * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  simpa using hle

private theorem earlyBrun_elemSym_tail_le {P : Finset ℕ}
    {s : ℕ} {T : ℝ} (hP : ∀ p ∈ P, 0 < p)
    (hT : earlyBrunHarmonic P ≤ T) (hT0 : 0 ≤ T)
    (hs : 2 * T ≤ (s : ℝ) + 1) :
    ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
      2 * T ^ (s + 1) / ((s + 1).factorial : ℝ) := by
  have hterm : ∀ k ∈ Icc (s + 1) P.card,
      earlyBrunElemSym P k ≤
        (T ^ (s + 1) / ((s + 1).factorial : ℝ)) *
          ((1 : ℝ) / 2) ^ (k - (s + 1)) := by
    intro k hk
    have hks := (mem_Icc.mp hk).1
    have hek := (earlyBrun_elemSym_le_pow_div_factorial k hP).trans
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (earlyBrun_harmonic_nonneg P) hT k)
        (Nat.cast_nonneg _))
    have hfact := earlyBrun_factorial_mul_pow_le hks
    have hspos : (0 : ℝ) < (s + 1).factorial :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
    have hkpos : (0 : ℝ) < k.factorial :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hfactR :
        ((s + 1).factorial : ℝ) * ((s : ℝ) + 2) ^ (k - (s + 1)) ≤
          (k.factorial : ℝ) := by exact_mod_cast hfact
    have hratio : T / ((s : ℝ) + 2) ≤ 1 / 2 := by
      apply (div_le_iff₀ hs2).mpr
      linarith
    have hratio0 : 0 ≤ T / ((s : ℝ) + 2) :=
      div_nonneg hT0 hs2.le
    calc
      earlyBrunElemSym P k ≤ T ^ k / (k.factorial : ℝ) := hek
      _ ≤ T ^ k /
          (((s + 1).factorial : ℝ) *
            ((s : ℝ) + 2) ^ (k - (s + 1))) :=
        div_le_div_of_nonneg_left (pow_nonneg hT0 _)
          (mul_pos hspos (pow_pos hs2 _)) hfactR
      _ = (T ^ (s + 1) / ((s + 1).factorial : ℝ)) *
          (T / ((s : ℝ) + 2)) ^ (k - (s + 1)) := by
        rw [show T ^ k = T ^ (s + 1) * T ^ (k - (s + 1)) by
          rw [← pow_add, Nat.add_sub_cancel' hks], div_pow]
        field_simp [hspos.ne', (pow_pos hs2 _).ne']
      _ ≤ (T ^ (s + 1) / ((s + 1).factorial : ℝ)) *
          ((1 : ℝ) / 2) ^ (k - (s + 1)) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hratio0 hratio _)
          (div_nonneg (pow_nonneg hT0 _) hspos.le)
  have hsum := sum_le_sum hterm
  have hinj : Set.InjOn (fun k : ℕ => k - (s + 1))
      (Icc (s + 1) P.card : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (mem_Icc.mp ha).1
    have hb' := (mem_Icc.mp hb).1
    calc
      a = (s + 1) + (a - (s + 1)) :=
        (Nat.add_sub_of_le ha').symm
      _ = (s + 1) + (b - (s + 1)) := congrArg ((s + 1) + ·) hab
      _ = b := Nat.add_sub_of_le hb'
  have hsub :
      (Icc (s + 1) P.card).image (fun k => k - (s + 1)) ⊆
        range (P.card + 1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
    have hkupper := (mem_Icc.mp hk).2
    exact mem_range.mpr
      ((Nat.sub_le k (s + 1)).trans_lt (Nat.lt_succ_of_le hkupper))
  have hgeom :
      ∑ k ∈ Icc (s + 1) P.card,
          ((1 : ℝ) / 2) ^ (k - (s + 1)) ≤ 2 := by
    have himg :
        ∑ k ∈ Icc (s + 1) P.card,
            ((1 : ℝ) / 2) ^ (k - (s + 1)) =
          ∑ j ∈ (Icc (s + 1) P.card).image
              (fun k => k - (s + 1)), ((1 : ℝ) / 2) ^ j :=
      (sum_image hinj).symm
    rw [himg]
    exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
      pow_nonneg (by norm_num) _).trans (earlyBrun_sum_half_pow_le _)
  calc
    ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
        ∑ k ∈ Icc (s + 1) P.card,
          (T ^ (s + 1) / ((s + 1).factorial : ℝ)) *
            ((1 : ℝ) / 2) ^ (k - (s + 1)) := hsum
    _ = (T ^ (s + 1) / ((s + 1).factorial : ℝ)) *
        ∑ k ∈ Icc (s + 1) P.card,
          ((1 : ℝ) / 2) ^ (k - (s + 1)) := by rw [mul_sum]
    _ ≤ (T ^ (s + 1) / ((s + 1).factorial : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left hgeom
        (div_nonneg (pow_nonneg hT0 _) (Nat.cast_nonneg _))
    _ = 2 * T ^ (s + 1) / ((s + 1).factorial : ℝ) := by ring

/-! ## Adjacent Bonferroni and CRT rounding -/

private def earlyBrunHitCount (P : Finset ℕ) (σ : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  (P.filter fun p => n % p = σ p % p).card

private theorem earlyBrun_hitCount_eq_zero_iff {P : Finset ℕ}
    {σ : ℕ → ℕ} {n : ℕ} :
    earlyBrunHitCount P σ n = 0 ↔
      ∀ p ∈ P, n % p ≠ σ p % p := by
  simp [earlyBrunHitCount, filter_eq_empty_iff]

private theorem earlyBrun_signed_choose_partial {r s : ℕ}
    (hr : 1 ≤ r) :
    ∑ j ∈ range (s + 1), (-1 : ℝ) ^ j * (r.choose j : ℝ) =
      (-1 : ℝ) ^ s * ((r - 1).choose s : ℝ) := by
  have hz := Int.alternating_sum_range_choose_eq_choose
    (n := r - 1) (m := s)
  have hr' : r = r - 1 + 1 := (Nat.sub_add_cancel hr).symm
  rw [← hr'] at hz
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast] using hcast

/-- The difference between a rank-`s` truncation and the survivor
indicator is controlled by the adjacent rank `s+1`. -/
private theorem earlyBrun_bonferroni_pointwise (r s : ℕ) :
    |(if r = 0 then (1 : ℝ) else 0) -
        ∑ j ∈ range (s + 1), (-1 : ℝ) ^ j * (r.choose j : ℝ)| ≤
      (r.choose (s + 1) : ℝ) := by
  rcases r with _ | r
  · have hterm : ∀ j ∈ range (s + 1),
        (-1 : ℝ) ^ j * ((0 : ℕ).choose j : ℝ) =
          if j = 0 then (1 : ℝ) else 0 := by
      intro j hj
      cases j with
      | zero => simp
      | succ j =>
        simp [Nat.choose_eq_zero_of_lt (Nat.succ_pos j)]
    have hsum :
        ∑ j ∈ range (s + 1),
            (-1 : ℝ) ^ j * ((0 : ℕ).choose j : ℝ) = 1 := by
      rw [sum_congr rfl hterm, sum_ite_eq']
      simp [mem_range]
    simp [hsum]
  · have hr : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hsum := earlyBrun_signed_choose_partial (r := r + 1) (s := s) hr
    have hz : (if r + 1 = 0 then (1 : ℝ) else 0) = 0 := by simp
    rw [hz, hsum, zero_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
    have hpas : (r + 1).choose (s + 1) =
        r.choose s + r.choose (s + 1) := Nat.choose_succ_succ r s
    have hle : (((r + 1 - 1).choose s : ℕ) : ℝ) ≤
        (((r + 1).choose (s + 1) : ℕ) : ℝ) := by
      simp only [Nat.add_sub_cancel]
      rw [hpas, Nat.cast_add]
      exact le_add_of_nonneg_right
        (show (0 : ℝ) ≤ (r.choose (s + 1) : ℝ) from Nat.cast_nonneg _)
    have hnon : (0 : ℝ) ≤ ((r + 1 - 1).choose s : ℝ) :=
      Nat.cast_nonneg _
    rw [abs_of_nonneg hnon]
    exact hle

private theorem earlyBrun_choose_hitCount {P : Finset ℕ}
    {σ : ℕ → ℕ} {n k : ℕ} :
    ((earlyBrunHitCount P σ n).choose k : ℝ) =
      ∑ U ∈ P.powersetCard k,
        if ∀ p ∈ U, n % p = σ p % p then (1 : ℝ) else 0 := by
  let H := P.filter fun p => n % p = σ p % p
  have hsub : H ⊆ P := filter_subset _ _
  have hpow : H.powersetCard k =
      (P.powersetCard k).filter (fun U => U ⊆ H) := by
    ext U
    simp only [mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨hUH, hc⟩
      exact ⟨⟨hUH.trans hsub, hc⟩, hUH⟩
    · rintro ⟨⟨_hUP, hc⟩, hUH⟩
      exact ⟨hUH, hc⟩
  rw [show earlyBrunHitCount P σ n = H.card by rfl,
    ← card_powersetCard, hpow, Finset.natCast_card_filter]
  refine sum_congr rfl fun U hU => ?_
  have hiff : U ⊆ H ↔ ∀ p ∈ U, n % p = σ p % p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr
        ⟨(mem_powersetCard.mp hU).1 hp, h p hp⟩
  simp only [hiff]

private theorem earlyBrun_sum_choose_hitCount {P : Finset ℕ}
    {σ : ℕ → ℕ} {J : Finset ℕ} {k : ℕ} :
    ∑ n ∈ J, ((earlyBrunHitCount P σ n).choose k : ℝ) =
      ∑ U ∈ P.powersetCard k,
        (((J.filter fun n => ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) := by
  simp_rw [earlyBrun_choose_hitCount]
  rw [sum_comm]
  refine sum_congr rfl fun U _ => ?_
  rw [Finset.natCast_card_filter]

private theorem earlyBrun_modeq_prod_of_primes {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {x y : ℕ}
    (h : ∀ p ∈ P, x % p = y % p) :
    x % (∏ p ∈ P, p) = y % (∏ p ∈ P, p) := by
  induction P using Finset.induction with
  | empty => simp only [prod_empty, Nat.mod_one]
  | @insert a P ha ih =>
    have hP' : ∀ p ∈ P, Nat.Prime p := fun p hp =>
      hP p (mem_insert_of_mem hp)
    have haP := hP a (mem_insert_self a P)
    have hcop : Nat.Coprime (∏ p ∈ P, p) a := by
      rw [Nat.coprime_prod_left_iff]
      intro p hp
      exact (Nat.coprime_primes (hP' p hp) haP).mpr fun hpa =>
        ha (hpa ▸ hp)
    rw [prod_insert ha]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp
      ⟨(show x ≡ y [MOD a] from h a (mem_insert_self a P)),
        (show x ≡ y [MOD ∏ p ∈ P, p] from
          ih hP' (fun p hp => h p (mem_insert_of_mem hp)))⟩

/-- CRT rounding for one simultaneous forbidden-class intersection. -/
theorem earlyBrun_intersection_abs_sub_div {U : Finset ℕ}
    {σ : ℕ → ℕ} {a S : ℕ} (hU : ∀ p ∈ U, Nat.Prime p) :
    |((((Ico a (a + S)).filter fun n =>
          ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) -
        (S : ℝ) / ∏ p ∈ U, (p : ℝ)| ≤ 1 := by
  let I := {p // p ∈ U}
  let modulus : I → ℕ := fun p => p.val
  let residue : I → ℕ := fun p => σ p.val
  have hnz : ∀ p ∈ (univ : Finset I), modulus p ≠ 0 := by
    intro p _
    exact (hU p.val p.property).ne_zero
  have hpair : Set.Pairwise (univ : Finset I)
      (Function.onFun Nat.Coprime modulus) := by
    intro p _ q _ hpq
    exact (Nat.coprime_primes (hU p.val p.property)
      (hU q.val q.property)).mpr fun hpqv =>
        hpq (Subtype.ext hpqv)
  let c := Nat.chineseRemainderOfFinset residue modulus
    (univ : Finset I) hnz hpair
  let M := ∏ p ∈ U, p
  have hM : 1 ≤ M := by
    exact Nat.one_le_iff_ne_zero.mpr
      (prod_ne_zero_iff.mpr fun p hp => (hU p hp).ne_zero)
  have hc : ∀ p ∈ U, c % p = σ p % p := by
    intro p hp
    change c.val % p = σ p % p
    exact c.property ⟨p, hp⟩ (mem_univ _)
  have hiff : ∀ n,
      (∀ p ∈ U, n % p = σ p % p) ↔ n % M = c % M := by
    intro n
    constructor
    · intro hn
      exact earlyBrun_modeq_prod_of_primes hU fun p hp =>
        (hn p hp).trans (hc p hp).symm
    · intro hn p hp
      have hpdvd : p ∣ M := dvd_prod_of_mem (fun q => q) hp
      exact (Nat.ModEq.of_dvd hpdvd
        (show n ≡ c [MOD M] from hn)).trans (hc p hp)
  have hfilter :
      (Ico a (a + S)).filter (fun n =>
          ∀ p ∈ U, n % p = σ p % p) =
        (Ico a (a + S)).filter (fun n => n % M = c % M) := by
    ext n
    simp only [mem_filter, hiff n]
  rw [hfilter]
  have hround := selbergCrt_card_mod_abs_le a S M c hM
  have hcast : (M : ℝ) = ∏ p ∈ U, (p : ℝ) := by
    simp [M, Nat.cast_prod]
  simpa [hcast] using hround

private theorem earlyBrun_sum_choose_le (n s : ℕ) :
    ∑ k ∈ range (s + 1), (n.choose k : ℝ) ≤
      ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s := by
  have hterm : ∀ k ∈ range (s + 1),
      (n.choose k : ℝ) ≤ ((n : ℝ) + 1) ^ s := by
    intro k hk
    have hks : k ≤ s := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by
      have hcast : ((n.choose k : ℕ) : ℝ) ≤ ((n ^ k : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.choose_le_pow n k)
      simpa [Nat.cast_pow] using hcast
    have h2 : (n : ℝ) ^ k ≤ ((n : ℝ) + 1) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k
    have h3 : ((n : ℝ) + 1) ^ k ≤ ((n : ℝ) + 1) ^ s :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hks
    exact h1.trans (h2.trans h3)
  refine (sum_le_sum hterm).trans_eq ?_
  rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

private theorem earlyBrun_powerset_eq_biUnion_powersetCard
    {α : Type*} [DecidableEq α] (P : Finset α) :
    P.powerset =
      (range (P.card + 1)).biUnion (fun k => P.powersetCard k) := by
  ext U
  simp only [mem_biUnion, mem_powerset, mem_powersetCard, mem_range]
  constructor
  · intro hU
    exact ⟨U.card, Nat.lt_succ_of_le (card_le_card hU), hU, rfl⟩
  · rintro ⟨k, _hk, hU, rfl⟩
    exact hU

private theorem earlyBrun_powersetCard_pairwiseDisjoint
    {α : Type*} [DecidableEq α] (P : Finset α) {I : Finset ℕ} :
    (I : Set ℕ).PairwiseDisjoint (fun k => P.powersetCard k) := by
  intro i _ j _ hij
  show Disjoint (P.powersetCard i) (P.powersetCard j)
  rw [Finset.disjoint_left]
  intro U hUi hUj
  exact hij ((mem_powersetCard.mp hUi).2.symm.trans
    (mem_powersetCard.mp hUj).2)

private theorem earlyBrun_prod_expansion (P : Finset ℕ) :
    ∏ p ∈ P, (1 - (p : ℝ)⁻¹) =
      ∑ k ∈ range (P.card + 1),
        (-1 : ℝ) ^ k * earlyBrunElemSym P k := by
  have hprod := Finset.prod_sub (fun _p : ℕ => (1 : ℝ))
    (fun p => (p : ℝ)⁻¹) P
  have hpowerset :
      ∏ p ∈ P, (1 - (p : ℝ)⁻¹) =
        ∑ U ∈ P.powerset,
          (-1 : ℝ) ^ U.card * ∏ p ∈ U, (p : ℝ)⁻¹ := by
    simpa using hprod
  rw [hpowerset, earlyBrun_powerset_eq_biUnion_powersetCard,
    sum_biUnion (earlyBrun_powersetCard_pairwiseDisjoint P)]
  refine sum_congr rfl fun k _ => ?_
  unfold earlyBrunElemSym
  rw [mul_sum]
  refine sum_congr rfl fun U hU => ?_
  rw [(mem_powersetCard.mp hU).2]

private def earlyBrunAvoiders (P : Finset ℕ) (σ : ℕ → ℕ)
    (J : Finset ℕ) : Finset ℕ :=
  J.filter fun n => ∀ p ∈ P, n % p ≠ σ p % p

/-! ## The generic fixed-residue theorem -/

/-- Uniform finite Brun estimate for any choice of one residue class
at each prime in `P`.  The theorem is uniform in `σ` and in the start
of the interval. -/
theorem earlyBrun_avoidCount_abs_sub_euler_le
    {P : Finset ℕ} {σ : ℕ → ℕ} {a S s : ℕ} {T : ℝ}
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hT : earlyBrunHarmonic P ≤ T) (hT0 : 0 ≤ T)
    (hs : 2 * T ≤ (s : ℝ) + 1) :
    |((earlyBrunAvoiders P σ (Ico a (a + S))).card : ℝ) -
        (S : ℝ) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹)| ≤
      2 * ((s : ℝ) + 1) * ((P.card : ℝ) + 1) ^ (s + 1) +
        3 * (S : ℝ) * T ^ (s + 1) /
          ((s + 1).factorial : ℝ) := by
  let J := Ico a (a + S)
  let N : ℝ := (earlyBrunAvoiders P σ J).card
  let V : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  have hpPos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  have hN :
      N = ∑ n ∈ J,
        if earlyBrunHitCount P σ n = 0 then (1 : ℝ) else 0 := by
    unfold N earlyBrunAvoiders
    rw [Finset.natCast_card_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hav : ∀ p ∈ P, n % p ≠ σ p % p
    · have hz : earlyBrunHitCount P σ n = 0 :=
        by
          unfold earlyBrunHitCount
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro p hp hhit
          exact (hav p hp) hhit
      rw [if_pos hz]
      exact if_pos hav
    · have hz : earlyBrunHitCount P σ n ≠ 0 := fun hz =>
        hav (earlyBrun_hitCount_eq_zero_iff.mp hz)
      rw [if_neg hz]
      exact if_neg hav
  let I : ℝ :=
    ∑ n ∈ J, ∑ j ∈ range (s + 1),
      (-1 : ℝ) ^ j * ((earlyBrunHitCount P σ n).choose j : ℝ)
  let Es : ℝ :=
    ∑ j ∈ range (s + 1),
      (-1 : ℝ) ^ j * earlyBrunElemSym P j
  have hI :
      I = ∑ j ∈ range (s + 1), (-1 : ℝ) ^ j *
        ∑ U ∈ P.powersetCard j,
          (((J.filter fun n =>
            ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) := by
    unfold I
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_sum, earlyBrun_sum_choose_hitCount]
  have hNIraw :
      |N - I| ≤
        ∑ U ∈ P.powersetCard (s + 1),
          (((J.filter fun n =>
            ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) := by
    have hpoint : ∀ n ∈ J,
        |(if earlyBrunHitCount P σ n = 0 then (1 : ℝ) else 0) -
          ∑ j ∈ range (s + 1), (-1 : ℝ) ^ j *
            ((earlyBrunHitCount P σ n).choose j : ℝ)| ≤
          ((earlyBrunHitCount P σ n).choose (s + 1) : ℝ) :=
      fun n _ => earlyBrun_bonferroni_pointwise _ _
    have hsum :=
      (abs_sum_le_sum_abs (s := J)
        (fun n =>
          (if earlyBrunHitCount P σ n = 0 then (1 : ℝ) else 0) -
            ∑ j ∈ range (s + 1), (-1 : ℝ) ^ j *
              ((earlyBrunHitCount P σ n).choose j : ℝ))).trans
        (sum_le_sum hpoint)
    have hsum' : |N - I| ≤
        ∑ n ∈ J,
          ((earlyBrunHitCount P σ n).choose (s + 1) : ℝ) := by
      rw [hN]
      unfold I
      rw [← sum_sub_distrib]
      exact hsum
    exact hsum'.trans_eq
      (earlyBrun_sum_choose_hitCount
        (P := P) (σ := σ) (J := J) (k := s + 1))
  have hnext :
      ∑ U ∈ P.powersetCard (s + 1),
          (((J.filter fun n =>
            ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) ≤
        (S : ℝ) * earlyBrunElemSym P (s + 1) +
          (P.card.choose (s + 1) : ℝ) := by
    have hterm : ∀ U ∈ P.powersetCard (s + 1),
        (((J.filter fun n =>
          ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) ≤
          (S : ℝ) * ∏ p ∈ U, (p : ℝ)⁻¹ + 1 := by
      intro U hU
      have hpU : ∀ p ∈ U, Nat.Prime p := fun p hp =>
        hP p ((mem_powersetCard.mp hU).1 hp)
      have hround := earlyBrun_intersection_abs_sub_div
        (U := U) (σ := σ) (a := a) (S := S) hpU
      have hinv : (S : ℝ) / ∏ p ∈ U, (p : ℝ) =
          (S : ℝ) * ∏ p ∈ U, (p : ℝ)⁻¹ := by
        rw [div_eq_mul_inv, Finset.prod_inv_distrib]
      have hupper := (abs_le.mp hround).2
      simpa [J, hinv, add_comm] using hupper
    refine (sum_le_sum hterm).trans_eq ?_
    rw [sum_add_distrib, ← mul_sum]
    simp [earlyBrunElemSym, sum_const, nsmul_eq_mul,
      card_powersetCard]
  have hNI : |N - I| ≤
      (S : ℝ) * earlyBrunElemSym P (s + 1) +
        (P.card.choose (s + 1) : ℝ) := hNIraw.trans hnext
  have hIEs : |I - (S : ℝ) * Es| ≤
      ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) := by
    rw [hI]
    unfold Es
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro j hj
    have heq :
        (-1 : ℝ) ^ j *
              ∑ U ∈ P.powersetCard j,
                (((J.filter fun n =>
                  ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) -
            (S : ℝ) * ((-1 : ℝ) ^ j * earlyBrunElemSym P j) =
          (-1 : ℝ) ^ j *
            ∑ U ∈ P.powersetCard j,
              ((((J.filter fun n =>
                    ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) -
                (S : ℝ) * ∏ p ∈ U, (p : ℝ)⁻¹) := by
      have hmul : (S : ℝ) * ((-1 : ℝ) ^ j * earlyBrunElemSym P j) =
          (-1 : ℝ) ^ j * ((S : ℝ) * earlyBrunElemSym P j) := by ring
      have hsym : (S : ℝ) * earlyBrunElemSym P j =
          ∑ U ∈ P.powersetCard j,
            (S : ℝ) * ∏ p ∈ U, (p : ℝ)⁻¹ := by
        simp [earlyBrunElemSym, mul_sum]
      rw [hmul, hsym, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [heq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hterm : ∀ U ∈ P.powersetCard j,
        |((((J.filter fun n =>
            ∀ p ∈ U, n % p = σ p % p).card : ℕ) : ℝ) -
          (S : ℝ) * ∏ p ∈ U, (p : ℝ)⁻¹)| ≤ 1 := by
      intro U hU
      have hpU : ∀ p ∈ U, Nat.Prime p := fun p hp =>
        hP p ((mem_powersetCard.mp hU).1 hp)
      have hround := earlyBrun_intersection_abs_sub_div
        (U := U) (σ := σ) (a := a) (S := S) hpU
      have hinv : (S : ℝ) / ∏ p ∈ U, (p : ℝ) =
          (S : ℝ) * ∏ p ∈ U, (p : ℝ)⁻¹ := by
        rw [div_eq_mul_inv, Finset.prod_inv_distrib]
      simpa [J, hinv] using hround
    have habs := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    have hones : ∑ _U ∈ P.powersetCard j, (1 : ℝ) =
        (P.card.choose j : ℝ) := by
      simp [sum_const, nsmul_eq_mul, card_powersetCard]
    exact habs.trans_eq hones
  have hEsV : |Es - V| ≤
      ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k := by
    have hV := earlyBrun_prod_expansion P
    by_cases hsc : s + 1 ≤ P.card
    · have hdisj : Disjoint (range (s + 1))
          (Icc (s + 1) P.card) := by
        rw [disjoint_left]
        intro k hk1 hk2
        have hklt : k < s + 1 := mem_range.mp hk1
        have hkge : s + 1 ≤ k := (mem_Icc.mp hk2).1
        exact (not_lt_of_ge hkge) hklt
      have hU : range (s + 1) ∪ Icc (s + 1) P.card =
          range (P.card + 1) := by
        ext k
        simp only [mem_union, mem_range, mem_Icc]
        omega
      have hsplit : V = Es +
          ∑ k ∈ Icc (s + 1) P.card,
            (-1 : ℝ) ^ k * earlyBrunElemSym P k := by
        unfold V Es
        rw [hV, ← hU, sum_union hdisj]
      rw [abs_sub_comm, hsplit]
      ring_nf
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
      intro k _
      simpa [abs_mul,
        abs_of_nonneg (earlyBrun_elemSym_nonneg P k)]
    · have hempty : Icc (s + 1) P.card = ∅ :=
        Icc_eq_empty_of_lt (Nat.not_le.mp hsc)
      have hsub : range (P.card + 1) ⊆ range (s + 1) :=
        by
          intro j hj
          have hjlt : j < P.card + 1 := mem_range.mp hj
          have hsc' : P.card < s + 1 := Nat.lt_of_not_ge hsc
          exact mem_range.mpr (by omega)
      have hzero : ∀ j ∈ range (s + 1),
          j ∉ range (P.card + 1) → earlyBrunElemSym P j = 0 := by
        intro j _hj hjP
        have hjgt : P.card < j := Nat.lt_of_not_ge fun hle =>
          hjP (mem_range.mpr (Nat.lt_succ_of_le hle))
        have hpempty : P.powersetCard j = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro U hU
          have hdata := mem_powersetCard.mp hU
          have hcardle : j ≤ P.card := by
            simpa [hdata.2] using card_le_card hdata.1
          exact (not_le_of_gt hjgt) hcardle
        simp [earlyBrunElemSym, hpempty]
      have hlow : Es = V := by
        unfold Es V
        rw [hV]
        symm
        exact sum_subset hsub fun j hjS hjP => by
          simp [hzero j hjS hjP]
      simp [hempty, hlow]
  have htail := earlyBrun_elemSym_tail_le hpPos hT hT0 hs
  have hC : (P.card.choose (s + 1) : ℝ) ≤
      ((P.card : ℝ) + 1) ^ (s + 1) := by
    have hchoose : (P.card.choose (s + 1) : ℝ) ≤
        (P.card : ℝ) ^ (s + 1) := by
      have hcast : ((P.card.choose (s + 1) : ℕ) : ℝ) ≤
          ((P.card ^ (s + 1) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.choose_le_pow P.card (s + 1))
      simpa [Nat.cast_pow] using hcast
    exact hchoose.trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _)
  have hlowC := earlyBrun_sum_choose_le P.card s
  have hlowC' : ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) ≤
      ((s : ℝ) + 1) * ((P.card : ℝ) + 1) ^ (s + 1) := by
    have hbase : (1 : ℝ) ≤ (P.card : ℝ) + 1 := by linarith
    have hpow : ((P.card : ℝ) + 1) ^ s ≤
        ((P.card : ℝ) + 1) ^ (s + 1) :=
      pow_le_pow_right₀ hbase (Nat.le_succ s)
    have hfac : 0 ≤ (s : ℝ) + 1 := by linarith
    exact hlowC.trans (mul_le_mul_of_nonneg_left hpow hfac)
  have hnextSym : earlyBrunElemSym P (s + 1) ≤
      T ^ (s + 1) / ((s + 1).factorial : ℝ) :=
    (earlyBrun_elemSym_le_pow_div_factorial (s + 1) hpPos).trans
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (earlyBrun_harmonic_nonneg P) hT _)
        (Nat.cast_nonneg _))
  have htriangle : |N - (S : ℝ) * V| ≤
      |N - I| + |I - (S : ℝ) * Es| +
        |(S : ℝ) * Es - (S : ℝ) * V| := by
    calc
      |N - (S : ℝ) * V| ≤ |N - I| + |I - (S : ℝ) * V| :=
        by
          simpa only [abs_sub_comm N I] using
            (abs_sub_le N I ((S : ℝ) * V))
      _ ≤ |N - I| +
          (|I - (S : ℝ) * Es| +
            |(S : ℝ) * Es - (S : ℝ) * V|) :=
        by
          exact add_le_add (le_refl |N - I|)
            (abs_sub_le I ((S : ℝ) * Es) ((S : ℝ) * V))
      _ = |N - I| + |I - (S : ℝ) * Es| +
          |(S : ℝ) * Es - (S : ℝ) * V| := by
            simpa [add_assoc]
  have hscaled : |(S : ℝ) * Es - (S : ℝ) * V| ≤
      (S : ℝ) *
        ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left hEsV (Nat.cast_nonneg _)
  have hraw : |N - (S : ℝ) * V| ≤
      ((S : ℝ) * earlyBrunElemSym P (s + 1) +
        (P.card.choose (s + 1) : ℝ)) +
      ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) +
      (S : ℝ) *
        ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k := by
    linarith [htriangle, hNI, hIEs, hscaled]
  have hroundPack : (P.card.choose (s + 1) : ℝ) +
      ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) ≤
        2 * ((s : ℝ) + 1) * ((P.card : ℝ) + 1) ^ (s + 1) := by
    have hpow0 : 0 ≤ ((P.card : ℝ) + 1) ^ (s + 1) :=
      pow_nonneg (by positivity) _
    have hC' : (P.card.choose (s + 1) : ℝ) ≤
        ((s : ℝ) + 1) * ((P.card : ℝ) + 1) ^ (s + 1) :=
      hC.trans (by nlinarith)
    linarith
  have hnextScaled : (S : ℝ) * earlyBrunElemSym P (s + 1) ≤
      (S : ℝ) * T ^ (s + 1) / ((s + 1).factorial : ℝ) := by
    have := mul_le_mul_of_nonneg_left hnextSym (Nat.cast_nonneg S)
    simpa [mul_div_assoc] using this
  have htailScaled : (S : ℝ) *
      ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
        2 * (S : ℝ) * T ^ (s + 1) /
          ((s + 1).factorial : ℝ) := by
    calc
      (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
          (S : ℝ) * (2 * T ^ (s + 1) /
            ((s + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg S)
      _ = 2 * (S : ℝ) * T ^ (s + 1) /
          ((s + 1).factorial : ℝ) := by ring
  let R : ℝ :=
    2 * ((s : ℝ) + 1) * ((P.card : ℝ) + 1) ^ (s + 1)
  let F : ℝ :=
    (S : ℝ) * T ^ (s + 1) / ((s + 1).factorial : ℝ)
  have hroundPack' : (P.card.choose (s + 1) : ℝ) +
      ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) ≤ R := by
    simpa [R] using hroundPack
  have hnextScaled' : (S : ℝ) * earlyBrunElemSym P (s + 1) ≤ F := by
    simpa [F] using hnextScaled
  have htailScaled' : (S : ℝ) *
      ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤ 2 * F := by
    calc
      (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
          2 * (S : ℝ) * T ^ (s + 1) /
            ((s + 1).factorial : ℝ) := htailScaled
      _ = 2 * F := by
        simp only [F]
        ring
  have hmajor :
      ((S : ℝ) * earlyBrunElemSym P (s + 1) +
        (P.card.choose (s + 1) : ℝ)) +
      ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) +
      (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
        F + R + 2 * F := by
    calc
      ((S : ℝ) * earlyBrunElemSym P (s + 1) +
          (P.card.choose (s + 1) : ℝ)) +
          ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) +
          (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k =
        (S : ℝ) * earlyBrunElemSym P (s + 1) +
          ((P.card.choose (s + 1) : ℝ) +
            ∑ j ∈ range (s + 1), (P.card.choose j : ℝ)) +
          (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k := by ring
      _ ≤ (S : ℝ) * earlyBrunElemSym P (s + 1) + R +
          (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k :=
        by
          exact add_le_add
            (add_le_add (le_refl _) hroundPack')
            (le_refl _)
      _ ≤ F + R + 2 * F := by
        exact add_le_add
          (add_le_add hnextScaled' (le_refl R))
          htailScaled'
  exact hraw.trans (by
    calc
      ((S : ℝ) * earlyBrunElemSym P (s + 1) +
          (P.card.choose (s + 1) : ℝ)) +
          ∑ j ∈ range (s + 1), (P.card.choose j : ℝ) +
          (S : ℝ) * ∑ k ∈ Icc (s + 1) P.card, earlyBrunElemSym P k ≤
        F + R + 2 * F := hmajor
      _ = 2 * ((s : ℝ) + 1) * ((P.card : ℝ) + 1) ^ (s + 1) +
          3 * (S : ℝ) * T ^ (s + 1) /
            ((s + 1).factorial : ℝ) := by
        simp only [F, R]
        ring)

/-! ## The rooted early-presieve adapter -/

private def earlyBrunResidue (w : ℕ) (τ : ResidueChoice w)
    (p : ℕ) : ℕ :=
  residueOfChoice w τ p

private theorem earlyPresieveSurvivors_eq_earlyBrunAvoiders
    (S w : ℕ) (τ : ResidueChoice w) :
    earlyPresieveSurvivors S w τ =
      earlyBrunAvoiders (Nat.primesLE w) (earlyBrunResidue w τ)
        (Ico 1 (1 + S)) := by
  ext n
  simp only [earlyPresieveSurvivors, earlyPresieveSurvives,
    earlyBrunAvoiders, mem_filter, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨⟨hn1, hnS⟩, hn⟩
    refine ⟨⟨hn1, by omega⟩, ?_⟩
    intro p hp
    have hp' := hn ⟨p, hp⟩
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primesLE hp
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hreslt : (τ ⟨p, hp⟩).val + 1 < p := by
      have hv : (τ ⟨p, hp⟩).val < p - 1 := (τ ⟨p, hp⟩).isLt
      omega
    simp only [earlyBrunResidue, residueOfChoice, dif_pos hp]
    rw [Nat.mod_eq_of_lt hreslt]
    exact hp'
  · rintro ⟨⟨hn1, hnS⟩, hn⟩
    refine ⟨⟨hn1, by omega⟩, ?_⟩
    intro p
    have hp' := hn p.val p.property
    have hpPrime : Nat.Prime p.val := Nat.prime_of_mem_primesLE p.property
    have hp2 : 2 ≤ p.val := hpPrime.two_le
    have hreslt : (τ p).val + 1 < p.val := by
      have hv : (τ p).val < p.val - 1 := (τ p).isLt
      omega
    simp only [earlyBrunResidue, residueOfChoice, dif_pos p.property] at hp'
    rw [Nat.mod_eq_of_lt hreslt] at hp'
    exact hp'

/-- Paper-form finite uniform Brun estimate for every fixed early
choice `τ`.  All measures and normalisations are unfolded: the left
side is the literal cardinality of the exposed survivor set. -/
theorem earlyPresieve_survivorCount_abs_sub_main_le_brun
    (S w s : ℕ) (τ : ResidueChoice w) {T : ℝ}
    (hT : earlyBrunHarmonic (Nat.primesLE w) ≤ T)
    (hT0 : 0 ≤ T) (hs : 2 * T ≤ (s : ℝ) + 1) :
    |((earlyPresieveSurvivors S w τ).card : ℝ) -
        (S : ℝ) * eulerProdNat w| ≤
      earlyPresieveBrunError S w s T := by
  have hP : ∀ p ∈ Nat.primesLE w, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primesLE hp
  have h := earlyBrun_avoidCount_abs_sub_euler_le
    (P := Nat.primesLE w) (σ := earlyBrunResidue w τ)
    (a := 1) (S := S) (s := s) hP hT hT0 hs
  rw [earlyPresieveSurvivors_eq_earlyBrunAvoiders]
  simpa [eulerProdNat, earlyPresieveBrunError] using h

end

end PrimeGapNormality.Prime
