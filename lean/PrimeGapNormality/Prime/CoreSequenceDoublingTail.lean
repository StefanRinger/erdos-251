import PrimeGapNormality.Prime.TailMass
import PrimeGapNormality.Prime.PosMassScale
import PrimeGapNormality.Prime.CoreCyclicSeriesConvergence
import PrimeGapNormality.Prime.StatisticalCriterion
import Mathlib.Data.Nat.Log

/-!
# Deterministic tails from eventual doubling

An eventual bound `a(2n) ≤ 4 a(n)` for an increasing integer sequence gives
an explicit quadratic scale bound.  Combining that bound with the positive
tail-mass telescope controls every finite block of shifted first-gap tails.
There is no density or rough-number input in this file.
-/

namespace PrimeGapNormality.Prime.CoreSequenceDoublingTail

open Finset Filter CoreCyclic
open scoped BigOperators Topology

noncomputable section

/-- Eventual four-doubling, isolated as the deterministic hypothesis. -/
def EventuallyFourDoubling (a : ℕ → ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, a (2 * n) ≤ 4 * a n

private theorem doubling_iterate
    {a : ℕ → ℕ} {n0 : ℕ}
    (hdouble : ∀ n, n0 ≤ n → a (2 * n) ≤ 4 * a n)
    {v : ℕ} (hv : n0 ≤ v) (q : ℕ) :
    a (2 ^ q * v) ≤ 4 ^ q * a v := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hpow : 1 ≤ 2 ^ q := Nat.one_le_pow q 2 (by norm_num)
      have hvq : n0 ≤ 2 ^ q * v := by
        exact hv.trans (by
          simpa only [one_mul] using Nat.mul_le_mul_right v hpow)
      calc
        a (2 ^ (q + 1) * v) = a (2 * (2 ^ q * v)) := by
          congr 1
          rw [pow_succ']
          ring
        _ ≤ 4 * a (2 ^ q * v) := hdouble _ hvq
        _ ≤ 4 * (4 ^ q * a v) := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (q + 1) * a v := by rw [pow_succ']; ring

private theorem pow_clog_two_le_two_mul (m : ℕ) (hm : 1 ≤ m) :
    2 ^ Nat.clog 2 m ≤ 2 * m := by
  by_cases hm1 : m = 1
  · subst m
    simp
  · have hmgt : 1 < m := lt_of_le_of_ne hm (Ne.symm hm1)
    let q := Nat.clog 2 m
    have hq : 0 < q := Nat.clog_pos (by norm_num) hmgt
    have hp : 2 ^ q.pred < m := Nat.pow_pred_clog_lt_self (by norm_num) hmgt
    have hqeq : q = q.pred + 1 := (Nat.succ_pred_eq_of_pos hq).symm
    calc
      2 ^ Nat.clog 2 m = 2 ^ q := rfl
      _ = 2 ^ q.pred * 2 := by
        nth_rw 1 [hqeq]
        rw [pow_succ]
      _ ≤ m * 2 := Nat.mul_le_mul_right 2 hp.le
      _ = 2 * m := Nat.mul_comm _ _

private theorem four_pow_clog_le (m : ℕ) (hm : 1 ≤ m) :
    4 ^ Nat.clog 2 m ≤ 4 * m ^ 2 := by
  have hpow := Nat.pow_le_pow_left (pow_clog_two_le_two_mul m hm) 2
  calc
    4 ^ Nat.clog 2 m = (2 ^ Nat.clog 2 m) ^ 2 := by
      simp only [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
      rw [Nat.mul_comm]
    _ ≤ (2 * m) ^ 2 := hpow
    _ = 4 * m ^ 2 := by ring

/-- Uniform finite dilation bound above a threshold where doubling holds. -/
theorem scale_bound
    {a : ℕ → ℕ} (ha : StrictMono a) {n0 v m : ℕ}
    (hdouble : ∀ n, n0 ≤ n → a (2 * n) ≤ 4 * a n)
    (hv : n0 ≤ v) (hm : 1 ≤ m) :
    a (m * v) ≤ 4 * m ^ 2 * a v := by
  let q := Nat.clog 2 m
  have hmq : m ≤ 2 ^ q := Nat.le_pow_clog (by norm_num) m
  have hindex : m * v ≤ 2 ^ q * v := Nat.mul_le_mul_right v hmq
  have hiter := doubling_iterate hdouble hv q
  calc
    a (m * v) ≤ a (2 ^ q * v) := ha.monotone hindex
    _ ≤ 4 ^ q * a v := hiter
    _ ≤ (4 * m ^ 2) * a v :=
      Nat.mul_le_mul_right (a v) (four_pow_clog_le m hm)
    _ = 4 * m ^ 2 * a v := rfl

/-- Eventual doubling supplies one genuine threshold for every later base
point and every positive integer dilation. -/
theorem exists_scale_bound
    {a : ℕ → ℕ} (ha : StrictMono a) (hdouble : EventuallyFourDoubling a) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ v, n0 ≤ v → ∀ m, 1 ≤ m →
      a (m * v) ≤ 4 * m ^ 2 * a v := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdouble
  let n0 := max 1 N
  refine ⟨n0, le_max_left _ _, ?_⟩
  intro v hv m hm
  apply scale_bound ha (n0 := n0)
  · intro n hn
    exact hN n ((le_max_right 1 N).trans hn)
  · exact hv
  · exact hm

/-- A convenient global quadratic majorant extracted from the eventual
doubling threshold. -/
theorem exists_global_quadratic_bound
    {a : ℕ → ℕ} (ha : StrictMono a) (hdouble : EventuallyFourDoubling a) :
    ∃ A : ℕ, ∀ n, a n ≤ A * (n + 1) ^ 2 := by
  obtain ⟨n0, hn0, hscale⟩ := exists_scale_bound ha hdouble
  refine ⟨4 * a n0, ?_⟩
  intro n
  by_cases hn : n < n0
  · have han := ha.monotone hn.le
    calc
      a n ≤ a n0 := han
      _ ≤ (4 * a n0) * (n + 1) ^ 2 := by
        have hsq : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
        nlinarith [Nat.zero_le (a n0)]
  · have hn0n : n0 ≤ n := Nat.not_lt.mp hn
    have hnpos : 1 ≤ n := hn0.trans hn0n
    have hindex : n ≤ n * n0 := Nat.le_mul_of_pos_right n (by omega : 0 < n0)
    calc
      a n ≤ a (n * n0) := ha.monotone hindex
      _ ≤ 4 * n ^ 2 * a n0 := hscale n0 le_rfl n hnpos
      _ ≤ (4 * a n0) * (n + 1) ^ 2 := by
        have hsquare : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
        nlinarith [Nat.zero_le (a n0)]

/-- Eventual four-doubling implies actual polynomial growth of the sequence
values. -/
theorem sequence_hasPolynomialGrowth
    {a : ℕ → ℕ} (ha : StrictMono a) (hdouble : EventuallyFourDoubling a) :
    HasPolynomialGrowth (fun n ↦ (a n : ℝ)) := by
  obtain ⟨A, hA⟩ := exists_global_quadratic_bound ha hdouble
  refine ⟨A, 2, Nat.cast_nonneg _, ?_⟩
  intro n
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  dsimp only
  exact_mod_cast hA n

/-- The actual gap sequence inherits polynomial growth, rather than taking
it as a separate hypothesis. -/
theorem sequenceGap_hasPolynomialGrowth
    {a : ℕ → ℕ} (ha : StrictMono a) (hdouble : EventuallyFourDoubling a) :
    HasPolynomialGrowth (fun n ↦ (seqGap a n : ℝ)) := by
  obtain ⟨A, hA⟩ := exists_global_quadratic_bound ha hdouble
  refine ⟨4 * A, 2, by positivity, ?_⟩
  intro n
  have hgap : seqGap a n ≤ a (n + 1) := Nat.sub_le _ _
  have hnext := hA (n + 1)
  have hidx : n + 2 ≤ 2 * (n + 1) := by omega
  have hfinal : seqGap a n ≤ (4 * A) * (n + 1) ^ 2 := by
    calc
      seqGap a n ≤ a (n + 1) := hgap
      _ ≤ A * (n + 2) ^ 2 := by simpa only [Nat.add_assoc] using hnext
      _ ≤ A * (2 * (n + 1)) ^ 2 :=
        Nat.mul_le_mul_left A (Nat.pow_le_pow_left hidx 2)
      _ = (4 * A) * (n + 1) ^ 2 := by ring
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  dsimp only
  exact_mod_cast hfinal

/-- Geometric summability of the positions, derived from the same quadratic
bound and valid for every real `rho>1`. -/
theorem sequence_div_pow_summable
    {a : ℕ → ℕ} (ha : StrictMono a) (hdouble : EventuallyFourDoubling a)
    {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ ↦ (a n : ℝ) / rho ^ n) := by
  obtain ⟨A, hA⟩ := exists_global_quadratic_bound ha hdouble
  have hdom : Summable (fun n : ℕ ↦
      ((A : ℝ) * rho) * (((n + 1 : ℕ) : ℝ) ^ 2 / rho ^ (n + 1))) :=
    ((summable_succ_sq_div_pow hrho 0).congr fun n => by
      simp only [Nat.zero_add]).mul_left ((A : ℝ) * rho)
  apply Summable.of_nonneg_of_le
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)
  · intro n
    have hcast : (a n : ℝ) ≤ (A : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2) := by
      exact_mod_cast hA n
    have hden : 0 ≤ rho ^ n := pow_nonneg (by positivity) _
    calc
      (a n : ℝ) / rho ^ n ≤
          ((A : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2)) / rho ^ n :=
        div_le_div_of_nonneg_right hcast hden
      _ = ((A : ℝ) * rho) *
          (((n + 1 : ℕ) : ℝ) ^ 2 / rho ^ (n + 1)) := by
        field_simp [(show rho ≠ 0 by positivity)] <;> ring
  · exact hdom

/-- Later shifted positions are controlled by the base value with the
quadratic dilation factor used in the tail sum. -/
theorem shifted_position_bound
    {a : ℕ → ℕ} (ha : StrictMono a) {n0 v L h : ℕ}
    (hn0 : 1 ≤ n0)
    (hdouble : ∀ n, n0 ≤ n → a (2 * n) ≤ 4 * a n)
    (hv : n0 ≤ v) (hL : L ≤ v) :
    a (v + L + h) ≤ 4 * (h + 2) ^ 2 * a v := by
  have hvpos : 0 < v := hn0.trans hv
  have hh : h ≤ h * v := Nat.le_mul_of_pos_right h hvpos
  have hindex : v + L + h ≤ (h + 2) * v := by
    calc
      v + L + h ≤ v + v + h := by omega
      _ ≤ v + v + h * v := Nat.add_le_add_left hh (v + v)
      _ = (h + 2) * v := by ring
  exact (ha.monotone hindex).trans
    (scale_bound ha hdouble hv (by omega : 1 ≤ h + 2))

/-- The fixed real constant left after summing the quadratic geometric
majorant. -/
def doublingTailConstant (rho : ℝ) : ℝ :=
  4 * ∑' j : ℕ, (((2 + j + 1 : ℕ) : ℝ) ^ 2 / rho ^ (j + 1))

/-- Exact finite tail-mass inequality.  The block may start anywhere below
`v`; its shifted tails cost only a fixed `rho`-constant times `a(v)`. -/
theorem sum_seqGapTail_Icc_le
    {a : ℕ → ℕ} (ha : StrictMono a) (hfour : EventuallyFourDoubling a)
    {rho : ℝ} (hrho : 1 < rho) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ {u v L : ℕ}, n0 ≤ v → u ≤ v → L ≤ v →
      (∑ n ∈ Icc u v, seqGapTail rho a (n + L)) ≤
        doublingTailConstant rho * (a v : ℝ) := by
  obtain ⟨n0, hn0, _hscale⟩ := exists_scale_bound ha hfour
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfour
  let n1 := max n0 N
  have hn1 : 1 ≤ n1 := hn0.trans (le_max_left _ _)
  have hdouble : ∀ n, n1 ≤ n → a (2 * n) ≤ 4 * a n :=
    fun n hn ↦ hN n ((le_max_right n0 N).trans hn)
  refine ⟨n1, hn1, ?_⟩
  intro u v L hv huv hLv
  have hv0 : n0 ≤ v := (le_max_left n0 N).trans hv
  have hsumA := sequence_div_pow_summable ha hfour hrho
  let t : Finset ℕ := (Icc u v).image (fun n ↦ n + L)
  have hinj : Set.InjOn (fun n : ℕ ↦ n + L) (Icc u v : Set ℕ) := by
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have ht : t ⊆ range (v + L + 1) := by
    intro i hi
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (Nat.lt_succ_of_le
      (Nat.add_le_add_right (mem_Icc.mp hn).2 L))
  have hgap : (fun k : ℕ ↦ (seqGap a k : ℝ)) =
      fun k ↦ (a (k + 1) : ℝ) - (a k : ℝ) := by
    funext k
    unfold seqGap
    rw [Nat.cast_sub (ha.monotone (Nat.le_succ k))]
  have htail := sum_gapTail_le_posMass (n := 0) hrho
    (fun k ↦ (a k : ℝ)) hsumA
    (fun i j hij ↦ Nat.cast_le.mpr (ha.monotone hij))
    (fun _ ↦ Nat.cast_nonneg _) t ht
  rw [← hgap] at htail
  simp only [Nat.zero_add] at htail
  have himage :
      (∑ i ∈ t, gapTail rho (fun k ↦ (seqGap a k : ℝ)) i) =
        ∑ n ∈ Icc u v,
          gapTail rho (fun k ↦ (seqGap a k : ℝ)) (n + L) :=
    sum_image hinj
  have hblock :
      (∑ n ∈ Icc u v, seqGapTail rho a (n + L)) ≤
        posMass rho (fun k ↦ (a k : ℝ)) (v + L + 1) := by
    have := himage.symm.trans_le htail
    simpa only [seqGapTail, gapTail] using this
  have hgeom : Summable (fun j : ℕ ↦
      (((2 + j + 1 : ℕ) : ℝ) ^ 2 / rho ^ (j + 1))) :=
    summable_succ_sq_div_pow hrho 2
  have hterm (j : ℕ) :
      (a (v + L + 1 + j) : ℝ) / rho ^ (j + 1) ≤
        (4 * (a v : ℝ)) *
          (((2 + j + 1 : ℕ) : ℝ) ^ 2 / rho ^ (j + 1)) := by
    have hnat := shifted_position_bound ha hn1 hdouble hv hLv (h := 1 + j)
    have hleftIndex : v + L + (1 + j) = v + L + 1 + j := by omega
    rw [hleftIndex] at hnat
    have hidx : 1 + j + 2 = 2 + j + 1 := by omega
    rw [hidx] at hnat
    have hcast : (a (v + L + 1 + j) : ℝ) ≤
        4 * (((2 + j + 1 : ℕ) : ℝ) ^ 2) * (a v : ℝ) := by
      exact_mod_cast hnat
    have hden : 0 ≤ rho ^ (j + 1) := pow_nonneg (by positivity) _
    calc
      (a (v + L + 1 + j) : ℝ) / rho ^ (j + 1) ≤
          (4 * (((2 + j + 1 : ℕ) : ℝ) ^ 2) * (a v : ℝ)) /
            rho ^ (j + 1) := div_le_div_of_nonneg_right hcast hden
      _ = _ := by ring
  have hright : Summable (fun j : ℕ ↦
      (4 * (a v : ℝ)) *
        (((2 + j + 1 : ℕ) : ℝ) ^ 2 / rho ^ (j + 1))) :=
    hgeom.mul_left (4 * (a v : ℝ))
  have hleft : Summable (fun j : ℕ ↦
      (a (v + L + 1 + j) : ℝ) / rho ^ (j + 1)) :=
    Summable.of_nonneg_of_le
      (fun j ↦ div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
      hterm hright
  have hmass : posMass rho (fun k ↦ (a k : ℝ)) (v + L + 1) ≤
      doublingTailConstant rho * (a v : ℝ) := by
    unfold posMass doublingTailConstant
    have htsum := hleft.tsum_le_tsum hterm hright
    rw [hgeom.tsum_mul_left] at htsum
    exact htsum.trans_eq (by ring)
  exact hblock.trans hmass

end
end PrimeGapNormality.Prime.CoreSequenceDoublingTail
