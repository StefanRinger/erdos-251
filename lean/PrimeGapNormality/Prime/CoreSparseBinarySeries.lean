import PrimeGapNormality.BFree.Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sparse binary series

This file isolates the digital statement used by the paper's twin-gap
example.  It makes no assertion about prime gaps.  For an arbitrary bit
sequence with zero asymptotic density of ones, the literal binary series is
rational exactly when only finitely many ones occur, and it is not normal in
base two.

The proof uses the actual convergent series and its shifted tails.  Rationality
puts every tail on one fixed integer lattice.  Zero density supplies
arbitrarily late zero blocks; if ones occur infinitely often, a positive tail
after such a block is simultaneously smaller than the lattice spacing.
The nonnormality proof identifies the actual base-two digit cylinder along
the orbit, with zero density excluding the ambiguous eventually-all-ones
expansion.
-/

namespace PrimeGapNormality.Prime.CoreSparseBinarySeries

open Finset Filter Set
open scoped Topology Classical BigOperators

noncomputable section

/-- An ordinary natural-valued bit sequence. -/
def IsBitSequence (a : ℕ → ℕ) : Prop :=
  ∀ n, a n = 0 ∨ a n = 1

/-- Number of ones among the first `N` bits. -/
def oneCount (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n ↦ a n = 1)).card

/-- The rightful zero-density hypothesis for the sparse example. -/
def HasZeroOneDensity (a : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ ↦ (oneCount a N : ℝ) / N) atTop (𝓝 0)

/-- Literal `0.a₀a₁a₂…` binary series. -/
def binarySeries (a : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (a n : ℝ) / (2 : ℝ) ^ (n + 1)

/-- Binary tail beginning with bit `a n`, rescaled back to the unit
interval. -/
def binaryTail (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, (a (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)

private theorem binaryGeometric_summable :
    Summable (fun n : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  have h := summable_geometric_two.mul_left ((1 : ℝ) / 2)
  apply h.congr
  intro n
  rw [pow_succ]
  simp only [one_div, mul_inv, inv_pow]
  ring

private theorem binaryGeometric_tsum :
    (∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ (n + 1)) = 1 := by
  rw [show (fun n : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ (n + 1)) =
      fun n ↦ ((1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ n by
    funext n
    rw [pow_succ]
    simp only [one_div, mul_inv, inv_pow]
    ring, tsum_mul_left, tsum_geometric_two]
  norm_num

private theorem bit_le_one {a : ℕ → ℕ} (hbits : IsBitSequence a) (n : ℕ) :
    a n ≤ 1 := by
  rcases hbits n with h | h <;> omega

/-- Every literal bit series is summable. -/
theorem binarySeries_summable {a : ℕ → ℕ} (hbits : IsBitSequence a) :
    Summable (fun n : ℕ ↦ (a n : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
    binaryGeometric_summable
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast bit_le_one hbits n) (by positivity)

/-- Every shifted binary tail is summable. -/
theorem binaryTail_summable {a : ℕ → ℕ} (hbits : IsBitSequence a) (n : ℕ) :
    Summable (fun j : ℕ ↦ (a (n + j) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  refine Summable.of_nonneg_of_le (fun j ↦ by positivity) (fun j ↦ ?_)
    binaryGeometric_summable
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast bit_le_one hbits (n + j)) (by positivity)

theorem binaryTail_nonneg (a : ℕ → ℕ) (n : ℕ) :
    0 ≤ binaryTail a n :=
  tsum_nonneg fun _ ↦ by positivity

theorem binaryTail_le_one {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (n : ℕ) :
    binaryTail a n ≤ 1 := by
  unfold binaryTail
  rw [← binaryGeometric_tsum]
  exact Summable.tsum_le_tsum
    (fun j ↦ div_le_div_of_nonneg_right
      (by exact_mod_cast bit_le_one hbits (n + j)) (by positivity))
    (binaryTail_summable hbits n) binaryGeometric_summable

/-- Removing even one future binary digit makes the rescaled tail strictly
smaller than one. -/
theorem binaryTail_lt_one_of_zero {a : ℕ → ℕ}
    (hbits : IsBitSequence a) {n j : ℕ} (hz : a (n + j) = 0) :
    binaryTail a n < 1 := by
  unfold binaryTail
  rw [← binaryGeometric_tsum]
  apply Summable.tsum_lt_tsum_of_nonneg
    (fun i ↦ by positivity)
    (fun i ↦ div_le_div_of_nonneg_right
      (by exact_mod_cast bit_le_one hbits (n + i)) (by positivity))
    (i := j)
  · simpa [hz] using
      (show (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (j + 1) by positivity)
  · exact binaryGeometric_summable

/-- Exact left-shift recurrence of the actual tails. -/
theorem binaryTail_recurrence {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (n : ℕ) :
    binaryTail a n = (a n : ℝ) / 2 + binaryTail a (n + 1) / 2 := by
  have hs := binaryTail_summable hbits n
  unfold binaryTail at hs ⊢
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.add_zero, Nat.zero_add, pow_one]
  apply congrArg (fun x : ℝ ↦ (a n : ℝ) / 2 + x)
  rw [← tsum_div_const]
  apply tsum_congr
  intro j
  rw [show n + (j + 1) = n + 1 + j by omega, show j + 1 + 1 = j + 2 by omega,
    pow_succ]
  ring

/-- A one occurring anywhere in the future makes the corresponding tail
positive. -/
theorem binaryTail_pos_of_one {a : ℕ → ℕ}
    (hbits : IsBitSequence a) {n j : ℕ} (ho : a (n + j) = 1) :
    0 < binaryTail a n := by
  unfold binaryTail
  apply (binaryTail_summable hbits n).tsum_pos (fun i ↦ by positivity) j
  simpa [ho] using
    (show (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (j + 1) by positivity)

/-- A block of `K` zeros suppresses the rescaled tail by `2⁻ᵏ`. -/
theorem binaryTail_le_invPow_of_zeroBlock {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (n K : ℕ)
    (hz : ∀ j, j < K → a (n + j) = 0) :
    binaryTail a n ≤ (2 : ℝ)⁻¹ ^ K := by
  induction K generalizing n with
  | zero => simpa using binaryTail_le_one hbits n
  | succ K ih =>
      have hzero : a n = 0 := by simpa using hz 0 (Nat.zero_lt_succ K)
      have hz' : ∀ j, j < K → a (n + 1 + j) = 0 := by
        intro j hj
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hz (j + 1) (Nat.succ_lt_succ hj)
      rw [binaryTail_recurrence hbits n, hzero]
      simp only [Nat.cast_zero, zero_div, zero_add]
      calc
        binaryTail a (n + 1) / 2 ≤ (2 : ℝ)⁻¹ ^ K / 2 :=
          div_le_div_of_nonneg_right (ih (n + 1) hz') (by norm_num)
        _ = (2 : ℝ)⁻¹ ^ (K + 1) := by rw [pow_succ]; ring

/-- Zero one-density supplies zero blocks of every positive length after
every prescribed index. -/
theorem exists_zeroBlock_after_of_zeroDensity {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hzero : HasZeroOneDensity a)
    (M K : ℕ) (hK : 0 < K) :
    ∃ n, M ≤ n ∧ ∀ j, j < K → a (n + j) = 0 := by
  classical
  let eps : ℝ := 1 / (2 * (K : ℝ))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (oneCount a N : ℝ) / N < eps := by
    have hball := hzero.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)
    filter_upwards [hball] with N hN
    have habs : |(oneCount a N : ℝ) / N| < eps := by
      simpa only [Real.dist_eq, sub_zero] using hN
    exact (le_abs_self _).trans_lt habs
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 hsmall)
  let L : ℕ := N₀ + M + 1
  let N : ℕ := M + L * K
  have hL : 0 < L := by dsimp only [L]; omega
  have hML : M < L * K := by
    have hML' : M < L := by dsimp only [L]; omega
    exact hML'.trans_le (Nat.le_mul_of_pos_right L hK)
  have hN₀N : N₀ ≤ N := by
    have hN₀L : N₀ ≤ L := by dsimp only [L]; omega
    have hLK : L ≤ L * K := Nat.le_mul_of_pos_right L hK
    dsimp only [N]
    omega
  have hsmallN : (oneCount a N : ℝ) / N < eps := hN₀ N hN₀N
  have hNpos : 0 < N := by dsimp only [N]; omega
  have hNlt : N < 2 * (L * K) := by dsimp only [N]; omega
  have hcountlt : oneCount a N < L := by
    have hmul := (div_lt_iff₀ (Nat.cast_pos.mpr hNpos)).mp hsmallN
    have hfrac : eps * (N : ℝ) < (L : ℝ) := by
      have hNltR : (N : ℝ) < 2 * ((L : ℝ) * (K : ℝ)) := by
        exact_mod_cast hNlt
      dsimp only [eps]
      have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
      calc
        1 / (2 * (K : ℝ)) * (N : ℝ) <
            1 / (2 * (K : ℝ)) * (2 * ((L : ℝ) * (K : ℝ))) :=
          mul_lt_mul_of_pos_left hNltR (by positivity)
        _ = (L : ℝ) := by field_simp [hKR.ne'] <;> ring
    have hcountR : (oneCount a N : ℝ) < L := hmul.trans hfrac
    exact_mod_cast hcountR
  by_contra hblock
  have hsome : ∀ i : Fin L,
      ∃ u, u < K ∧ a (M + i.1 * K + u) = 1 := by
    intro i
    by_contra hnone
    apply hblock
    refine ⟨M + i.1 * K, by omega, ?_⟩
    intro u hu
    have hne : a (M + i.1 * K + u) ≠ 1 := by
      intro hone
      exact hnone ⟨u, hu, hone⟩
    exact (hbits (M + i.1 * K + u)).resolve_right hne
  let pick : Fin L → ℕ := fun i ↦ Classical.choose (hsome i)
  have hpick_lt : ∀ i, pick i < K := fun i ↦ (Classical.choose_spec (hsome i)).1
  have hpick_one : ∀ i, a (M + i.1 * K + pick i) = 1 :=
    fun i ↦ (Classical.choose_spec (hsome i)).2
  let embed : Fin L →
      {n // n ∈ (range N).filter (fun n ↦ a n = 1)} := fun i ↦
    ⟨M + i.1 * K + pick i, by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr ?_, hpick_one i⟩
      have hi : i.1 + 1 ≤ L := Nat.succ_le_iff.mpr i.2
      have hblockEnd : i.1 * K + pick i < L * K := by
        calc
          i.1 * K + pick i < i.1 * K + K := Nat.add_lt_add_left (hpick_lt i) _
          _ = (i.1 + 1) * K := by simp [Nat.add_mul]
          _ ≤ L * K := Nat.mul_le_mul_right K hi
      dsimp only [N]
      omega⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Subtype.val hij
    change M + i.1 * K + pick i = M + j.1 * K + pick j at hv
    have hv' : i.1 * K + pick i = j.1 * K + pick j := by omega
    have hquot (u : Fin L) : (u.1 * K + pick u) / K = u.1 := by
      calc
        (u.1 * K + pick u) / K = (pick u + K * u.1) / K := by
          rw [Nat.mul_comm, Nat.add_comm]
        _ = pick u / K + u.1 := Nat.add_mul_div_left _ _ hK
        _ = u.1 := by rw [Nat.div_eq_of_lt (hpick_lt u), zero_add]
    have hd := congrArg (fun x : ℕ ↦ x / K) hv'
    rwa [hquot i, hquot j] at hd
  have hcard : L ≤ ((range N).filter (fun n ↦ a n = 1)).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective embed hembed
  exact (not_le_of_gt hcountlt) hcard

/-- Under zero density, every shifted tail is the actual fractional part of
the base-two orbit. -/
theorem fract_two_pow_mul_binarySeries {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hzero : HasZeroOneDensity a) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * binarySeries a) = binaryTail a n := by
  have htail_lt : ∀ m, binaryTail a m < 1 := by
    intro m
    obtain ⟨u, hmu, hu⟩ := exists_zeroBlock_after_of_zeroDensity
      hbits hzero m 1 (by omega)
    have hmn : m ≤ u := hmu
    have hbit : a (m + (u - m)) = 0 := by
      rw [Nat.add_sub_of_le hmn]
      simpa using hu 0 (by omega)
    exact binaryTail_lt_one_of_zero hbits hbit
  induction n with
  | zero =>
      have htail0 : binaryTail a 0 = binarySeries a := by
        unfold binaryTail binarySeries
        congr 1
        funext j
        simp
      rw [pow_zero, one_mul, ← htail0]
      exact Int.fract_eq_self.mpr ⟨binaryTail_nonneg a 0, htail_lt 0⟩
  | succ n ih =>
      have hrec := binaryTail_recurrence hbits n
      apply Int.fract_eq_iff.mpr
      refine ⟨binaryTail_nonneg a (n + 1), htail_lt (n + 1), ?_⟩
      obtain ⟨z, hz⟩ := (Int.fract_eq_iff.mp ih).2.2
      refine ⟨2 * z + (a n : ℤ), ?_⟩
      rw [pow_succ]
      push_cast
      have hnext : binaryTail a (n + 1) =
          2 * binaryTail a n - (a n : ℝ) := by linarith
      rw [hnext]
      have hz' : (2 : ℝ) ^ n * binarySeries a - binaryTail a n = (z : ℝ) := hz
      linarith

private theorem orbit_mem_oneCylinder_iff {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hzero : HasZeroOneDensity a) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * binarySeries a) ∈
        PrimeGapNormality.BFree.digitCylinder 2 1 1 ↔ a n = 1 := by
  rw [fract_two_pow_mul_binarySeries hbits hzero n]
  unfold PrimeGapNormality.BFree.digitCylinder
  norm_num only [pow_one, Nat.cast_ofNat, Nat.cast_one]
  rcases hbits n with hbit | hbit
  · rw [binaryTail_recurrence hbits n, hbit]
    simp only [Nat.cast_zero, zero_div, zero_add, Set.mem_Ico]
    constructor
    · intro h
      have hlt : binaryTail a (n + 1) / 2 < 1 / 2 := by
        exact div_lt_div_of_pos_right
          (by
            obtain ⟨u, hnu, hu⟩ := exists_zeroBlock_after_of_zeroDensity
              hbits hzero (n + 1) 1 (by omega)
            have hidx : a (n + 1 + (u - (n + 1))) = 0 := by
              rw [Nat.add_sub_of_le hnu]
              simpa using hu 0 (by omega)
            exact binaryTail_lt_one_of_zero hbits hidx)
          (by norm_num)
      linarith
    · intro h
      omega
  · rw [binaryTail_recurrence hbits n, hbit]
    simp only [Nat.cast_one, Set.mem_Ico]
    constructor
    · intro h
      trivial
    · intro h
      constructor
      · have := binaryTail_nonneg a (n + 1)
        linarith
      · obtain ⟨u, hnu, hu⟩ := exists_zeroBlock_after_of_zeroDensity
            hbits hzero (n + 1) 1 (by omega)
        have hidx : a (n + 1 + (u - (n + 1))) = 0 := by
          rw [Nat.add_sub_of_le hnu]
          simpa using hu 0 (by omega)
        have := binaryTail_lt_one_of_zero hbits hidx
        linarith

/-- Zero one-density contradicts the actual length-one base-two cylinder
frequency required by `BFree.IsNormal`. -/
theorem binarySeries_not_isNormal_two {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hzero : HasZeroOneDensity a) :
    ¬ PrimeGapNormality.BFree.IsNormal 2 (binarySeries a) := by
  intro hnormal
  have hone := hnormal 1 1 (by norm_num)
  have hfilter : ∀ N : ℕ,
      (range N).filter (fun n ↦
        Int.fract ((2 : ℝ) ^ n * binarySeries a) ∈
          PrimeGapNormality.BFree.digitCylinder 2 1 1) =
        (range N).filter (fun n ↦ a n = 1) := by
    intro N
    apply filter_congr
    intro n hn
    exact orbit_mem_oneCylinder_iff hbits hzero n
  have hone' : Tendsto (fun N : ℕ ↦ (oneCount a N : ℝ) / N)
      atTop (𝓝 ((2 : ℝ)⁻¹)) := by
    norm_num only [Nat.cast_ofNat, pow_one] at hone
    simpa only [oneCount, hfilter, one_div] using hone
  have heq := tendsto_nhds_unique hzero hone'
  norm_num at heq

/-- Finite support gives a rational literal binary series. -/
theorem binarySeries_rational_of_finite_support {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hfinite : Set.Finite {n | a n = 1}) :
    ∃ q : ℚ, binarySeries a = (q : ℝ) := by
  let S : Finset ℕ := hfinite.toFinset
  have hsum : binarySeries a =
      ∑ n ∈ S, (a n : ℝ) / (2 : ℝ) ^ (n + 1) := by
    unfold binarySeries
    rw [tsum_eq_sum (s := S)]
    intro n hn
    have hne : a n ≠ 1 := by
      intro hone
      apply hn
      exact hfinite.mem_toFinset.mpr hone
    have hz := (hbits n).resolve_right hne
    simp [hz]
  refine ⟨∑ n ∈ S, (a n : ℚ) / (2 : ℚ) ^ (n + 1), ?_⟩
  rw [hsum]
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]

/-- With zero one-density, rationality of the literal binary series is
equivalent to finiteness of its one-support. -/
theorem binarySeries_rational_iff_support_finite {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hzero : HasZeroOneDensity a) :
    (∃ q : ℚ, binarySeries a = (q : ℝ)) ↔ Set.Finite {n | a n = 1} := by
  constructor
  · intro hrat
    by_contra hfinite
    have hinf : Set.Infinite {n | a n = 1} := hfinite
    obtain ⟨q, hq⟩ := hrat
    let Q : ℕ := q.den
    have hQ : 0 < Q := by dsimp only [Q]; exact q.den_pos
    have hlat : ∀ n, ∃ z : ℤ, (Q : ℝ) * binaryTail a n = z := by
      intro n
      induction n with
      | zero =>
          refine ⟨q.num, ?_⟩
          have htail : binaryTail a 0 = binarySeries a := by
            unfold binaryTail binarySeries
            congr 1
            funext j
            simp
          rw [htail, hq]
          dsimp only [Q]
          exact_mod_cast q.den_mul_eq_num
      | succ n ih =>
          obtain ⟨z, hz⟩ := ih
          refine ⟨2 * z - (Q : ℤ) * (a n : ℤ), ?_⟩
          have hrec := binaryTail_recurrence hbits n
          have hnext : binaryTail a (n + 1) =
              2 * binaryTail a n - (a n : ℝ) := by linarith
          rw [hnext, mul_sub]
          have htwo : (Q : ℝ) * (2 * binaryTail a n) =
              2 * ((Q : ℝ) * binaryTail a n) := by ring
          rw [htwo, hz]
          push_cast
          ring
    obtain ⟨n, hn0, hblock⟩ := exists_zeroBlock_after_of_zeroDensity
      hbits hzero 0 Q hQ
    obtain ⟨m, hmone, hnm⟩ := hinf.exists_gt (n + Q)
    have htailpos : 0 < binaryTail a n := by
      apply binaryTail_pos_of_one hbits
        (j := m - n)
      rw [Nat.add_sub_of_le (by omega : n ≤ m)]
      exact hmone
    have htailUpper : binaryTail a n ≤ (2 : ℝ)⁻¹ ^ Q :=
      binaryTail_le_invPow_of_zeroBlock hbits n Q hblock
    obtain ⟨z, hz⟩ := hlat n
    have hzposR : (0 : ℝ) < (z : ℝ) := by
      rw [← hz]
      exact mul_pos (Nat.cast_pos.mpr hQ) htailpos
    have hzone : (1 : ℝ) ≤ (z : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr (Int.cast_pos.mp hzposR))
    have htailLower : 1 / (Q : ℝ) ≤ binaryTail a n := by
      apply (div_le_iff₀ (Nat.cast_pos.mpr hQ)).mpr
      rw [mul_comm, hz]
      exact hzone
    have hpowR : (Q : ℝ) < (2 : ℝ) ^ Q := by
      exact_mod_cast Q.lt_two_pow_self
    have hinv : (2 : ℝ)⁻¹ ^ Q < 1 / (Q : ℝ) := by
      simpa only [inv_pow, one_div] using
        one_div_lt_one_div_of_lt (Nat.cast_pos.mpr hQ) hpowR
    exact (not_lt_of_ge (htailLower.trans htailUpper)) hinv
  · exact binarySeries_rational_of_finite_support hbits

/-- Equivalent paper form: under zero density, the sparse binary series is
irrational exactly when ones occur infinitely often. -/
theorem binarySeries_irrational_iff_support_infinite {a : ℕ → ℕ}
    (hbits : IsBitSequence a) (hzero : HasZeroOneDensity a) :
    Irrational (binarySeries a) ↔ Set.Infinite {n | a n = 1} := by
  constructor
  · intro hirr
    by_contra hinf
    have hfinite : Set.Finite {n | a n = 1} := Set.not_infinite.mp hinf
    obtain ⟨q, hq⟩ := binarySeries_rational_of_finite_support hbits hfinite
    exact hirr ⟨q, hq.symm⟩
  · intro hinf
    intro hrat
    obtain ⟨q, hq⟩ := hrat
    have hfinite := (binarySeries_rational_iff_support_finite hbits hzero).mp
      ⟨q, hq.symm⟩
    exact hinf hfinite

end

end PrimeGapNormality.Prime.CoreSparseBinarySeries
