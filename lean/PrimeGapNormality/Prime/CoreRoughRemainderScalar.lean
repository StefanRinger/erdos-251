import PrimeGapNormality.Prime.FiniteRootMixSmallMomentBound
import PrimeGapNormality.Prime.CrtMixUnnormRemainderLe

/-!
# Public scalar envelope for the actual rough model

The finite proofs below are reproduced from the already checked private
lemmas in FiniteRootMixSmallRemainder.lean, without changing that imported
source or using private-name internals. No stronger Stirling theorem is
reproved: Real.pow_div_factorial_le_exp is the sole analytic ingredient.
-/

namespace PrimeGapNormality.Prime.CoreRoughRemainderScalar
open Filter Finset
open scoped Topology
noncomputable section

theorem profileR_twenty_bounds (L : ℕ) :
    20 * L ≤ profileR L 20 ∧ profileR L 20 ≤ 20 * L + 1 := by
  have hcast : (20 : ℝ) * (L : ℝ) = ((20 * L : ℕ) : ℝ) := by
    norm_num
  have hceil : ⌈(20 : ℝ) * (L : ℝ)⌉₊ = 20 * L := by
    rw [hcast, Nat.ceil_natCast]
  have hmax : max L (20 * L) = 20 * L := max_eq_right (by omega)
  dsimp [profileR]
  rw [hceil, hmax]
  split_ifs <;> omega

/-- The elementary Stirling consequence `n^k/k! ≤ (e n/k)^k`. -/
theorem nat_pow_div_factorial_le_exp_ratio (n k : ℕ) (hk : 0 < k) :
    (n : ℝ) ^ k / (k.factorial : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / k) ^ k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul (1 : ℝ) k]
    congr 1
    exact (mul_one (k : ℝ)).symm
  have hst : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp 1 ^ k := by
    have h := Real.pow_div_factorial_le_exp (x := (k : ℝ))
      (Nat.cast_nonneg k) k
    rwa [hexp] at h
  have hnn : 0 ≤ ((n : ℝ) / k) ^ k :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg n) hkpos.le) k
  have hscale := mul_le_mul_of_nonneg_right hst hnn
  have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
  have hfact : (k.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hleft :
      ((k : ℝ) ^ k / (k.factorial : ℝ)) * ((n : ℝ) / k) ^ k =
        (n : ℝ) ^ k / (k.factorial : ℝ) := by
    rw [div_pow]
    refine (eq_div_iff hfact).mpr ?_
    rw [mul_right_comm, div_mul_cancel₀ _ hfact, ← mul_div_assoc,
      mul_comm ((k : ℝ) ^ k), mul_div_cancel_right₀ _ (pow_ne_zero k hk0)]
  have hright :
      Real.exp 1 ^ k * ((n : ℝ) / k) ^ k =
        (Real.exp 1 * (n : ℝ) / k) ^ k := by
    rw [← mul_pow]
    congr 1
    rw [← mul_div_assoc]
  rwa [hleft, hright] at hscale

theorem small_remainder_scalar_nonneg (L : ℕ) :
    0 ≤ ((profileR L 20).choose (L - 1) : ℝ) *
      ((5 : ℝ) * L) ^ (profileR L 20 + 1) /
        ((profileR L 20 + 1).factorial : ℝ) :=
  div_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg L)) _))
    (Nat.cast_nonneg _)

theorem small_remainder_scalar_le_half_pow (L : ℕ) (hL : 2 ≤ L) :
    ((profileR L 20).choose (L - 1) : ℝ) *
        ((5 : ℝ) * L) ^ (profileR L 20 + 1) /
          ((profileR L 20 + 1).factorial : ℝ)
      ≤ (1 / 2 : ℝ) ^ L := by
  let r := profileR L 20
  let k := L - 1
  let j := r + 1
  have hrlo : 20 * L ≤ r := (profileR_twenty_bounds L).1
  have hrhi : r ≤ 20 * L + 1 := (profileR_twenty_bounds L).2
  have hkpos : 0 < k := by omega
  have hkL : k ≤ L := Nat.sub_le L 1
  have hLk : L ≤ 2 * k := by omega
  have hjpos : 0 < j := Nat.succ_pos r
  have hjlo : 20 * L ≤ j := hrlo.trans (Nat.le_succ r)
  have hr21 : r ≤ 21 * L := by omega
  have hchoose0 : (r.choose k : ℝ) ≤ (r : ℝ) ^ k / (k.factorial : ℝ) :=
    choose_le_pow_div_real r k
  have hchooseExp := nat_pow_div_factorial_le_exp_ratio r k hkpos
  have hkRpos : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hratioChoose : Real.exp 1 * (r : ℝ) / k ≤ 126 := by
    apply (div_le_iff₀ hkRpos).2
    have her : Real.exp 1 * (r : ℝ) ≤ 3 * (r : ℝ) :=
      mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hr0
    have hr21R : (r : ℝ) ≤ 21 * (L : ℝ) := by exact_mod_cast hr21
    have hLkR : (L : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hLk
    nlinarith
  have hchoose : (r.choose k : ℝ) ≤ (126 : ℝ) ^ L := by
    calc
      (r.choose k : ℝ) ≤ (r : ℝ) ^ k / (k.factorial : ℝ) := hchoose0
      _ ≤ (Real.exp 1 * (r : ℝ) / k) ^ k := hchooseExp
      _ ≤ (126 : ℝ) ^ k :=
        pow_le_pow_left₀
          (div_nonneg (mul_nonneg (Real.exp_pos 1).le hr0) hkRpos.le)
          hratioChoose k
      _ ≤ (126 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hkL
  have hmomentExp := nat_pow_div_factorial_le_exp_ratio (5 * L) j hjpos
  have hjRpos : (0 : ℝ) < j := Nat.cast_pos.mpr hjpos
  have hratioMoment : Real.exp 1 * ((5 * L : ℕ) : ℝ) / j ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hjRpos).2
    have hfive0 : (0 : ℝ) ≤ (5 * L : ℕ) := Nat.cast_nonneg _
    have he : Real.exp 1 * ((5 * L : ℕ) : ℝ) ≤
        3 * ((5 * L : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hfive0
    have hjloR : (20 * L : ℕ) ≤ j := hjlo
    have hjloR' : ((20 * L : ℕ) : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hjloR
    calc
      Real.exp 1 * ((5 * L : ℕ) : ℝ)
          ≤ 3 * ((5 * L : ℕ) : ℝ) := he
      _ = 15 * (L : ℝ) := by push_cast; ring
      _ ≤ (3 / 4 : ℝ) * (j : ℝ) := by
        push_cast at hjloR'
        nlinarith
  have hmoment :
      ((5 : ℝ) * L) ^ j / (j.factorial : ℝ) ≤ (3 / 4 : ℝ) ^ j := by
    have hbase0 : 0 ≤ Real.exp 1 * ((5 * L : ℕ) : ℝ) / j :=
      div_nonneg (mul_nonneg (Real.exp_pos 1).le (Nat.cast_nonneg _)) hjRpos.le
    calc
      ((5 : ℝ) * L) ^ j / (j.factorial : ℝ) =
          ((5 * L : ℕ) : ℝ) ^ j / (j.factorial : ℝ) := by norm_num
      _ ≤ (Real.exp 1 * ((5 * L : ℕ) : ℝ) / j) ^ j := hmomentExp
      _ ≤ (3 / 4 : ℝ) ^ j := pow_le_pow_left₀ hbase0 hratioMoment j
  have hpowj : (3 / 4 : ℝ) ^ j ≤ (3 / 4 : ℝ) ^ (20 * L) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjlo
    rw [hd, pow_add]
    have hdle : (3 / 4 : ℝ) ^ d ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdle (pow_nonneg (by norm_num) (20 * L))
  have hbase : (126 : ℝ) * (3 / 4 : ℝ) ^ 20 ≤ 1 / 2 := by norm_num
  calc
    (r.choose k : ℝ) * ((5 : ℝ) * L) ^ j / (j.factorial : ℝ) =
        (r.choose k : ℝ) *
          (((5 : ℝ) * L) ^ j / (j.factorial : ℝ)) := by ring
    _ ≤ (126 : ℝ) ^ L *
          (((5 : ℝ) * L) ^ j / (j.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hchoose
        (div_nonneg (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg L)) _)
          (Nat.cast_nonneg _))
    _ ≤ (126 : ℝ) ^ L * (3 / 4 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hmoment (pow_nonneg (by norm_num) L)
    _ ≤ (126 : ℝ) ^ L * (3 / 4 : ℝ) ^ (20 * L) :=
      mul_le_mul_of_nonneg_left hpowj (pow_nonneg (by norm_num) L)
    _ = ((126 : ℝ) * (3 / 4 : ℝ) ^ 20) ^ L := by
      rw [pow_mul, mul_pow]
    _ ≤ (1 / 2 : ℝ) ^ L :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 20)) hbase L

theorem tendsto_small_remainder_scalar :
    Tendsto (fun L : ℕ =>
      ((profileR L 20).choose (L - 1) : ℝ) *
        ((5 : ℝ) * L) ^ (profileR L 20 + 1) /
          ((profileR L 20 + 1).factorial : ℝ)) atTop (nhds 0) := by
  have hhalf : Tendsto (fun L : ℕ => (1 / 2 : ℝ) ^ L) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  refine squeeze_zero' (Eventually.of_forall small_remainder_scalar_nonneg) ?_ hhalf
  filter_upwards [eventually_ge_atTop 2] with L hL
  exact small_remainder_scalar_le_half_pow L hL


end
end PrimeGapNormality.Prime.CoreRoughRemainderScalar

