import PrimeGapNormality.Prime.FiniteSelbergWeights
import PrimeGapNormality.Prime.SelbergCrtInterval
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite Selberg interval cap

This module assembles the paper's optimal finite weights with the uniform
one-residue interval count.  The first lemmas record the exact normalization
at `1`, support, and the `R²` bound for the total rounding cost.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeGapNormality.Prime

noncomputable section

set_option maxHeartbeats 800000

private theorem finiteSelberg_inner_one_eq_term_div (R m : ℕ) :
    (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R m =
      selbergJR_term m / selbergJR R := by
  rw [finiteSelbergY, selbergJR_term]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The finite optimal Selberg weight is normalized by `lambda 1 = 1`. -/
theorem finiteSelbergWeight_one {R : ℕ} (hR : 1 ≤ R) :
    finiteSelbergWeight R 1 = 1 := by
  have hJ : selbergJR R ≠ 0 := (selbergJR_pos hR).ne'
  rw [finiteSelbergWeight, Nat.cast_one, one_mul, Nat.div_one]
  simp only [one_mul]
  calc
    ∑ m ∈ Icc 1 R,
        (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R m =
        ∑ m ∈ Icc 1 R, selbergJR_term m / selbergJR R := by
          apply sum_congr rfl
          intro m hm
          exact finiteSelberg_inner_one_eq_term_div R m
    _ = selbergJR R / selbergJR R := by
      rw [← sum_div, selbergJR]
    _ = 1 := div_self hJ

/-- Cancelling the positive index `d` exposes the finite Möbius transform
which must be reindexed in the divisor-inversion proof. -/
theorem finiteSelbergWeight_div_eq_inner {R d : ℕ}
    (hd : d ∈ Icc 1 R) :
    finiteSelbergWeight R d / (d : ℝ) =
      ∑ m ∈ Icc 1 (R / d),
        (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hd).1)
  rw [finiteSelbergWeight, mul_div_cancel_left₀ _ hd0]

/-- The divisor sum of the real-cast Möbius function is the delta mass at
`1`. -/
theorem finiteSelberg_sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) =
      if n = 1 then 1 else 0 := by
  have hconv :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  have happ := congrArg (fun f : ArithmeticFunction ℝ => f n) hconv
  rw [ArithmeticFunction.coe_zeta_mul_apply] at happ
  simpa [ArithmeticFunction.one_apply] using happ

/-- Equivalent reversed-divisor form of the Möbius delta identity. -/
theorem finiteSelberg_sum_moebius_div_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) =
      if n = 1 then 1 else 0 := by
  calc
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) =
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) :=
      Nat.sum_div_divisors n
        (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ))
    _ = if n = 1 then 1 else 0 := finiteSelberg_sum_moebius_divisors n

/-- Expansion of the left side of finite divisor inversion.  The remaining
step is the finite hyperbola reindexing `(d,m) ↦ d*m`. -/
theorem finiteSelberg_divisor_inversion_lhs {R r : ℕ} :
    ∑ d ∈ Icc 1 R with r ∣ d,
        finiteSelbergWeight R d / (d : ℝ) =
      ∑ d ∈ Icc 1 R with r ∣ d,
        ∑ m ∈ Icc 1 (R / d),
          (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (d * m) := by
  apply sum_congr rfl
  intro d hd
  exact finiteSelbergWeight_div_eq_inner (mem_filter.mp hd).1

/-- Finite Dirichlet-hyperbola reindexing, with all positivity and cutoff
conditions explicit. -/
theorem finiteSelberg_sum_hyperbola (T : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ k ∈ Icc 1 T, ∑ m ∈ Icc 1 (T / k), F k m =
      ∑ q ∈ Icc 1 T, ∑ k ∈ q.divisors, F k (q / k) := by
  let source : Finset (Σ _k : ℕ, ℕ) :=
    (Icc 1 T).sigma fun k => Icc 1 (T / k)
  let target : Finset (Σ q : ℕ, ℕ) :=
    (Icc 1 T).sigma fun q => q.divisors
  calc
    ∑ k ∈ Icc 1 T, ∑ m ∈ Icc 1 (T / k), F k m =
        ∑ x ∈ source, F x.1 x.2 := by
          exact Finset.sum_sigma' (Icc 1 T) (fun k => Icc 1 (T / k)) F
    _ = ∑ y ∈ target, F y.2 (y.1 / y.2) := by
      refine Finset.sum_bij'
        (s := source) (t := target)
        (f := fun x => F x.1 x.2)
        (g := fun y => F y.2 (y.1 / y.2))
        (fun x _ => ⟨x.1 * x.2, x.1⟩)
        (fun y _ => ⟨y.2, y.1 / y.2⟩) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        have hx' :
            x.1 ∈ Icc 1 T ∧ x.2 ∈ Icc 1 (T / x.1) := by
          simpa [source] using hx
        rcases hx' with ⟨hk, hm⟩
        have hkpos : 0 < x.1 :=
          Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1
        have hmpos : 0 < x.2 :=
          Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hm).1
        have hprodle : x.1 * x.2 ≤ T := by
          have := (Nat.le_div_iff_mul_le hkpos).mp (mem_Icc.mp hm).2
          simpa [Nat.mul_comm] using this
        have hi :
            x.1 * x.2 ∈ Icc 1 T ∧ x.1 ∈ (x.1 * x.2).divisors :=
          ⟨mem_Icc.mpr
            ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hkpos.ne' hmpos.ne'), hprodle⟩,
          Nat.mem_divisors.mpr ⟨dvd_mul_right x.1 x.2,
            Nat.mul_ne_zero hkpos.ne' hmpos.ne'⟩⟩
        simpa [target] using hi
      · intro y hy
        have hy' : y.1 ∈ Icc 1 T ∧ y.2 ∈ y.1.divisors := by
          simpa [target] using hy
        rcases hy' with ⟨hq, hk⟩
        have hqpos : 0 < y.1 :=
          Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hq).1
        have hkpos : 0 < y.2 := Nat.pos_of_mem_divisors hk
        have hkdvd : y.2 ∣ y.1 := Nat.dvd_of_mem_divisors hk
        have hkleq : y.2 ≤ y.1 := Nat.le_of_dvd hqpos hkdvd
        have hj :
            y.2 ∈ Icc 1 T ∧ y.1 / y.2 ∈ Icc 1 (T / y.2) :=
          ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hkpos.ne',
            hkleq.trans (mem_Icc.mp hq).2⟩,
          mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
              (Nat.div_pos hkleq hkpos).ne',
            Nat.div_le_div_right (mem_Icc.mp hq).2⟩⟩
        simpa [source] using hj
      · intro x hx
        have hx' :
            x.1 ∈ Icc 1 T ∧ x.2 ∈ Icc 1 (T / x.1) := by
          simpa [source] using hx
        rcases hx' with ⟨hk, hm⟩
        have hkpos : 0 < x.1 :=
          Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (Nat.mul_div_right x.2 hkpos)
      · intro y hy
        have hy' : y.1 ∈ Icc 1 T ∧ y.2 ∈ y.1.divisors := by
          simpa [target] using hy
        rcases hy' with ⟨hq, hk⟩
        have hkdvd : y.2 ∣ y.1 := Nat.dvd_of_mem_divisors hk
        apply Sigma.ext
        · exact Nat.mul_div_cancel' hkdvd
        · rfl
      · intro x hx
        have hx' :
            x.1 ∈ Icc 1 T ∧ x.2 ∈ Icc 1 (T / x.1) := by
          simpa [source] using hx
        rcases hx' with ⟨hk, hm⟩
        have hkpos : 0 < x.1 :=
          Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1
        rw [Nat.mul_div_right x.2 hkpos]
    _ = ∑ q ∈ Icc 1 T, ∑ k ∈ q.divisors, F k (q / k) := by
      exact (Finset.sum_sigma' (Icc 1 T) (fun q => q.divisors)
        (fun q k => F k (q / k))).symm

/-- Reindex the positive multiples of `r` up to `R` by their quotient by
`r`. -/
theorem finiteSelberg_sum_multiples {R r : ℕ} (hr : r ∈ Icc 1 R)
    (G : ℕ → ℝ) :
    ∑ d ∈ Icc 1 R with r ∣ d, G d =
      ∑ k ∈ Icc 1 (R / r), G (r * k) := by
  have hrpos : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hr).1
  apply Finset.sum_bij'
    (fun d _ => d / r)
    (fun k _ => r * k)
  · intro d hd
    have hd' := mem_filter.mp hd
    have hdpos : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd'.1).1
    have hrd : r ∣ d := hd'.2
    have hrle : r ≤ d := Nat.le_of_dvd hdpos hrd
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.div_pos hrle hrpos).ne',
      Nat.div_le_div_right (mem_Icc.mp hd'.1).2⟩
  · intro k hk
    have hk' := mem_Icc.mp hk
    have hkpos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk'.1
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hrpos.ne' hkpos.ne'), ?_⟩, dvd_mul_right r k⟩
    have hle := (Nat.le_div_iff_mul_le hrpos).mp hk'.2
    simpa [Nat.mul_comm] using hle
  · intro d hd
    have hrd : r ∣ d := (mem_filter.mp hd).2
    exact Nat.mul_div_cancel' hrd
  · intro k hk
    exact Nat.mul_div_right k hrpos
  · intro d hd
    have hrd : r ∣ d := (mem_filter.mp hd).2
    rw [Nat.mul_div_cancel' hrd]

/-- Exact finite divisor inversion for the paper-optimal Selberg weights. -/
theorem finiteSelberg_divisor_inversion {R r : ℕ} (hr : r ∈ Icc 1 R) :
    ∑ d ∈ Icc 1 R with r ∣ d,
      finiteSelbergWeight R d / (d : ℝ) = finiteSelbergY R r := by
  rw [finiteSelberg_divisor_inversion_lhs]
  rw [finiteSelberg_sum_multiples hr]
  let T := R / r
  have hrpos : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hr).1
  have hT : 1 ≤ T := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.div_pos (mem_Icc.mp hr).2 hrpos).ne'
  calc
    ∑ k ∈ Icc 1 (R / r),
        ∑ m ∈ Icc 1 (R / (r * k)),
          (ArithmeticFunction.moebius m : ℝ) * finiteSelbergY R (r * k * m) =
      ∑ q ∈ Icc 1 T, ∑ k ∈ q.divisors,
        (ArithmeticFunction.moebius (q / k) : ℝ) * finiteSelbergY R (r * q) := by
          calc
            _ = ∑ q ∈ Icc 1 T, ∑ k ∈ q.divisors,
                (ArithmeticFunction.moebius (q / k) : ℝ) *
                  finiteSelbergY R (r * (k * (q / k))) := by
              simpa [T, Nat.div_div_eq_div_mul, mul_assoc] using
                finiteSelberg_sum_hyperbola T
                  (fun k m => (ArithmeticFunction.moebius m : ℝ) *
                    finiteSelbergY R (r * (k * m)))
            _ = _ := by
              apply sum_congr rfl
              intro q hq
              apply sum_congr rfl
              intro k hk
              rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)]
    _ = ∑ q ∈ Icc 1 T,
        (if q = 1 then 1 else 0) * finiteSelbergY R (r * q) := by
      apply sum_congr rfl
      intro q hq
      rw [← sum_mul, finiteSelberg_sum_moebius_div_divisors]
    _ = finiteSelbergY R r := by
      simp [hT]

/-- Evaluation of the diagonal quadratic in the finite Selberg variables. -/
theorem finiteSelberg_diagonalY_eq {R : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ Icc 1 R, (r.totient : ℝ) * finiteSelbergY R r ^ 2 =
      1 / selbergJR R := by
  have hJ : selbergJR R ≠ 0 := (selbergJR_pos hR).ne'
  calc
    ∑ r ∈ Icc 1 R, (r.totient : ℝ) * finiteSelbergY R r ^ 2 =
        ∑ r ∈ Icc 1 R, selbergJR_term r / selbergJR R ^ 2 := by
      apply sum_congr rfl
      intro r hr
      have hrpos : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hr).1
      have hphi : (r.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hrpos).ne'
      rw [finiteSelbergY, selbergJR_term]
      field_simp
    _ = selbergJR R / selbergJR R ^ 2 := by
      rw [← sum_div, selbergJR]
    _ = 1 / selbergJR R := by
      field_simp

/-- On positive indices bounded by `R`, the classical identity
`gcd(d,e) = ∑_{r∣d, r∣e} φ(r)` may be summed over the common divisors
inside `Icc 1 R`. -/
theorem finiteSelberg_gcd_eq_sum_totient {R d e : ℕ}
    (hd : d ∈ Icc 1 R) (he : e ∈ Icc 1 R) :
    (Nat.gcd d e : ℝ) =
      ∑ r ∈ Icc 1 R with r ∣ d ∧ r ∣ e, (r.totient : ℝ) := by
  have hd0 : d ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hd).1
  have hg0 : Nat.gcd d e ≠ 0 := Nat.gcd_ne_zero_left hd0
  have hfin :
      (Icc 1 R).filter (fun r => r ∣ d ∧ r ∣ e) = (Nat.gcd d e).divisors := by
    ext r
    constructor
    · intro hr
      have hr' := mem_filter.mp hr
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd_iff.mpr hr'.2, hg0⟩
    · intro hr
      have hrg : r ∣ Nat.gcd d e := Nat.dvd_of_mem_divisors hr
      have hcommon := Nat.dvd_gcd_iff.mp hrg
      have hrpos : 0 < r := Nat.pos_of_mem_divisors hr
      have hrle : r ≤ R :=
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hcommon.1).trans (mem_Icc.mp hd).2
      exact mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hrpos.ne', hrle⟩, hcommon⟩
  rw [hfin, ← Nat.cast_sum, Nat.sum_totient]

private theorem finiteSelberg_div_lcm_eq_gcd_mul_div {d e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (a b : ℝ) :
    a * b / (Nat.lcm d e : ℝ) =
      (Nat.gcd d e : ℝ) * (a / d) * (b / e) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd)
  have he0 : (e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp he)
  have hl0 : (Nat.lcm d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_ne_zero
      (Nat.one_le_iff_ne_zero.mp hd) (Nat.one_le_iff_ne_zero.mp he))
  have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) =
      (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hinv : ((Nat.lcm d e : ℝ))⁻¹ =
      (Nat.gcd d e : ℝ) * (d : ℝ)⁻¹ * (e : ℝ)⁻¹ := by
    field_simp
    nlinarith [hgl]
  simp only [div_eq_mul_inv, hinv]
  ring

theorem finiteSelberg_quadratic_eq_gcd_form {R : ℕ} (hR : 1 ≤ R) :
    ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      finiteSelbergWeight R d * finiteSelbergWeight R e /
        (Nat.lcm d e : ℝ) =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        (Nat.gcd d e : ℝ) *
          (finiteSelbergWeight R d / d) * (finiteSelbergWeight R e / e) := by
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  exact finiteSelberg_div_lcm_eq_gcd_mul_div
    (mem_Icc.mp hd).1 (mem_Icc.mp he).1 _ _

/-- Finite gcd diagonalization on the positive box `Icc 1 R`. -/
theorem finiteSelberg_gcd_diagonal (R : ℕ) (a : ℕ → ℝ) :
    ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      (Nat.gcd d e : ℝ) * a d * a e =
      ∑ r ∈ Icc 1 R, (r.totient : ℝ) *
        (∑ d ∈ Icc 1 R with r ∣ d, a d) ^ 2 := by
  calc
    ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        (Nat.gcd d e : ℝ) * a d * a e =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        ∑ r ∈ Icc 1 R,
          if r ∣ d ∧ r ∣ e then (r.totient : ℝ) * a d * a e else 0 := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      rw [finiteSelberg_gcd_eq_sum_totient hd he, sum_filter, sum_mul, sum_mul]
      apply sum_congr rfl
      intro r hr
      split_ifs <;> ring
    _ = ∑ d ∈ Icc 1 R, ∑ r ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          if r ∣ d ∧ r ∣ e then (r.totient : ℝ) * a d * a e else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
    _ = ∑ r ∈ Icc 1 R, ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          if r ∣ d ∧ r ∣ e then (r.totient : ℝ) * a d * a e else 0 := by
      rw [sum_comm]
    _ = ∑ r ∈ Icc 1 R, (r.totient : ℝ) *
        (∑ d ∈ Icc 1 R with r ∣ d, a d) ^ 2 := by
      apply sum_congr rfl
      intro r hr
      let b : ℕ → ℝ := fun d => if r ∣ d then a d else 0
      have hfilter :
          ∑ d ∈ Icc 1 R with r ∣ d, a d = ∑ d ∈ Icc 1 R, b d := by
        unfold b
        rw [sum_filter]
      rw [hfilter, pow_two]
      have hpoint : ∀ d e : ℕ,
          (if r ∣ d ∧ r ∣ e then
              (r.totient : ℝ) * a d * a e
            else (0 : ℝ)) =
            (r.totient : ℝ) * b d * b e := by
        intro d e
        by_cases hrd : r ∣ d <;> by_cases hre : r ∣ e <;>
          simp [b, hrd, hre]
      have hsum :
          (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
            (if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) * a d * a e
              else (0 : ℝ))) =
            ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
              (r.totient : ℝ) * b d * b e := by
        apply sum_congr rfl
        intro d hd
        apply sum_congr rfl
        intro e he
        exact hpoint d e
      rw [hsum]
      have hfactor :
          (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
            (r.totient : ℝ) * b d * b e) =
            (r.totient : ℝ) *
              (∑ d ∈ Icc 1 R, b d) * (∑ e ∈ Icc 1 R, b e) := by
        calc
          (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
              (r.totient : ℝ) * b d * b e) =
              ∑ d ∈ Icc 1 R,
                ((r.totient : ℝ) * b d) *
                  (∑ e ∈ Icc 1 R, b e) := by
            apply sum_congr rfl
            intro d hd
            rw [← Finset.mul_sum]
          _ = (∑ d ∈ Icc 1 R, (r.totient : ℝ) * b d) *
                (∑ e ∈ Icc 1 R, b e) := by
            rw [Finset.sum_mul]
          _ = (r.totient : ℝ) *
                (∑ d ∈ Icc 1 R, b d) *
                (∑ e ∈ Icc 1 R, b e) := by
            rw [← Finset.mul_sum]
      simpa only [mul_assoc] using hfactor

/-- The exact quadratic value of the finite optimal Selberg weights. -/
theorem finiteSelberg_quadratic_eq {R : ℕ} (hR : 1 ≤ R) :
    ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      finiteSelbergWeight R d * finiteSelbergWeight R e /
        (Nat.lcm d e : ℝ) = 1 / selbergJR R := by
  calc
    ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e /
          (Nat.lcm d e : ℝ) =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        (Nat.gcd d e : ℝ) *
          (finiteSelbergWeight R d / d) * (finiteSelbergWeight R e / e) :=
      finiteSelberg_quadratic_eq_gcd_form hR
    _ = ∑ r ∈ Icc 1 R, (r.totient : ℝ) *
        (∑ d ∈ Icc 1 R with r ∣ d,
          finiteSelbergWeight R d / d) ^ 2 :=
      finiteSelberg_gcd_diagonal R (fun d => finiteSelbergWeight R d / d)
    _ = ∑ r ∈ Icc 1 R, (r.totient : ℝ) * finiteSelbergY R r ^ 2 := by
      apply sum_congr rfl
      intro r hr
      rw [finiteSelberg_divisor_inversion hr]
    _ = 1 / selbergJR R := finiteSelberg_diagonalY_eq hR

/-- The divisor polynomial centered at the common CRT residue. -/
def finiteSelbergDivisorSum (R : ℕ) (c : ℤ) (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 R,
    finiteSelbergWeight R d * selbergCrt_indicator d c n

theorem finiteSelberg_indicator_mul (d e : ℕ) (c : ℤ) (n : ℕ) :
    selbergCrt_indicator d c n * selbergCrt_indicator e c n =
      selbergCrt_indicator (Nat.lcm d e) c n := by
  have hiff :
      ((d : ℤ) ∣ ((n : ℤ) - c) ∧ (e : ℤ) ∣ ((n : ℤ) - c)) ↔
        ((Nat.lcm d e : ℕ) : ℤ) ∣ ((n : ℤ) - c) := by
    simp only [selbergCrt_dvd_iff_modEq]
    simpa using (Int.modEq_and_modEq_iff_modEq_lcm
      (a := (n : ℤ)) (b := c) (m := (d : ℤ)) (n := (e : ℤ)))
  unfold selbergCrt_indicator
  by_cases hd : (d : ℤ) ∣ ((n : ℤ) - c)
  · by_cases he : (e : ℤ) ∣ ((n : ℤ) - c)
    · rw [if_pos hd, if_pos he, if_pos (hiff.mp ⟨hd, he⟩)]
      norm_num
    · have hlcm : ¬ ((Nat.lcm d e : ℕ) : ℤ) ∣ ((n : ℤ) - c) := by
        intro hlcm
        exact he (hiff.mpr hlcm).2
      rw [if_pos hd, if_neg he, if_neg hlcm]
      norm_num
  · have hlcm : ¬ ((Nat.lcm d e : ℕ) : ℤ) ∣ ((n : ℤ) - c) := by
      intro hlcm
      exact hd (hiff.mpr hlcm).1
    rw [if_neg hd, if_neg hlcm]
    norm_num

private theorem finiteSelberg_term_eq_zero_of_ne_one
    {A : Finset ℕ} {R c n d : ℕ}
    (hcenter : ∀ p ∈ Nat.primesLE R, ∀ n ∈ A, n % p ≠ c % p)
    (hn : n ∈ A) (hd : d ∈ Icc 1 R) (hd1 : d ≠ 1) :
    finiteSelbergWeight R d * selbergCrt_indicator d (c : ℤ) n = 0 := by
  by_cases hlam : finiteSelbergWeight R d = 0
  · simp [hlam]
  · obtain ⟨p, hpprime, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have hpR : p ∈ Nat.primesLE R := Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hd).1) hpd).trans
          (mem_Icc.mp hd).2, hpprime⟩
    unfold selbergCrt_indicator
    by_cases hdiv : (d : ℤ) ∣ ((n : ℤ) - (c : ℤ))
    · have hpdZ : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
      have hpdiv : (p : ℤ) ∣ ((n : ℤ) - (c : ℤ)) := hpdZ.trans hdiv
      have hmodZ : (n : ℤ) ≡ (c : ℤ) [ZMOD (p : ℤ)] :=
        (selbergCrt_dvd_iff_modEq p (c : ℤ) n).mp hpdiv
      have hmodN : n ≡ c [MOD p] := Int.natCast_modEq_iff.mp hmodZ
      exact (hcenter p hpR n hn hmodN).elim
    · simp [hdiv]

theorem finiteSelbergDivisorSum_eq_one_on
    {A : Finset ℕ} {R c n : ℕ} (hR : 1 ≤ R)
    (hcenter : ∀ p ∈ Nat.primesLE R, ∀ n ∈ A, n % p ≠ c % p)
    (hn : n ∈ A) :
    finiteSelbergDivisorSum R (c : ℤ) n = 1 := by
  unfold finiteSelbergDivisorSum
  rw [sum_eq_single 1]
  · simp [finiteSelbergWeight_one hR, selbergCrt_indicator]
  · intro d hd hd1
    exact finiteSelberg_term_eq_zero_of_ne_one hcenter hn hd hd1
  · intro hnot
    have hmem : (1 : ℕ) ∈ Icc 1 R :=
      mem_Icc.mpr ⟨Nat.le_refl 1, hR⟩
    exact (hnot hmem).elim

theorem finiteSelberg_sum_divisorSum_sq_expand (S R c : ℕ) :
    ∑ n ∈ Icc 1 S, finiteSelbergDivisorSum R (c : ℤ) n ^ 2 =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e *
          ∑ n ∈ Icc 1 S,
            selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := by
  calc
    ∑ n ∈ Icc 1 S, finiteSelbergDivisorSum R (c : ℤ) n ^ 2 =
      ∑ n ∈ Icc 1 S, ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e *
          selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := by
      apply sum_congr rfl
      intro n hn
      unfold finiteSelbergDivisorSum
      rw [pow_two, sum_mul]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      calc
        (finiteSelbergWeight R d * selbergCrt_indicator d (c : ℤ) n) *
            (finiteSelbergWeight R e * selbergCrt_indicator e (c : ℤ) n) =
          (finiteSelbergWeight R d * finiteSelbergWeight R e) *
            (selbergCrt_indicator d (c : ℤ) n *
              selbergCrt_indicator e (c : ℤ) n) := by ring
        _ = (finiteSelbergWeight R d * finiteSelbergWeight R e) *
            selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := by
          rw [finiteSelberg_indicator_mul]
        _ = finiteSelbergWeight R d * finiteSelbergWeight R e *
            selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := rfl
    _ = ∑ d ∈ Icc 1 R, ∑ n ∈ Icc 1 S, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e *
          selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := by
      rw [sum_comm]
    _ = ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R, ∑ n ∈ Icc 1 S,
        finiteSelbergWeight R d * finiteSelbergWeight R e *
          selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := by
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
    _ = ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e *
          ∑ n ∈ Icc 1 S,
            selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      rw [mul_sum]

private theorem finiteSelberg_Icc_eq_Ico (S : ℕ) :
    Icc 1 S = Ico 1 (1 + S) := by
  rw [Nat.add_comm]
  exact (Ico_add_one_right_eq_Icc 1 S).symm

/-- The optimal weights are supported on `1 ≤ d ≤ R`; the upper support
condition is the part used to make the interval rounding error finite. -/
theorem finiteSelbergWeight_eq_zero_of_not_mem_Icc {R d : ℕ}
    (hd : d ∉ Icc 1 R) :
    finiteSelbergWeight R d = 0 := by
  by_cases hd0 : d = 0
  · subst d
    simp [finiteSelbergWeight]
  · have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hRd : R < d := by
      by_contra hnot
      exact hd (mem_Icc.mpr ⟨hdpos, Nat.le_of_not_gt hnot⟩)
    exact finiteSelbergWeight_eq_zero_of_lt hRd

/-- The `l¹` norm of the coefficients on their finite support is at most
the length `R` of that support. -/
theorem finiteSelbergWeight_sum_abs_le (R : ℕ) (hR : 1 ≤ R) :
    ∑ d ∈ Icc 1 R, |finiteSelbergWeight R d| ≤ (R : ℝ) := by
  calc
    ∑ d ∈ Icc 1 R, |finiteSelbergWeight R d| ≤
        ∑ d ∈ Icc 1 R, (1 : ℝ) := by
          exact sum_le_sum fun d hd => finiteSelbergWeight_abs_le_one hR
    _ = (R : ℝ) := by simp [Nat.card_Icc]

/-- Squared form of the total interval-rounding cost. -/
theorem finiteSelbergWeight_sum_abs_sq_le (R : ℕ) (hR : 1 ≤ R) :
    (∑ d ∈ Icc 1 R, |finiteSelbergWeight R d|) ^ 2 ≤ (R : ℝ) ^ 2 := by
  have hsum0 : 0 ≤ ∑ d ∈ Icc 1 R, |finiteSelbergWeight R d| :=
    sum_nonneg fun _ _ => abs_nonneg _
  exact (sq_le_sq₀ hsum0 (Nat.cast_nonneg R)).2
    (finiteSelbergWeight_sum_abs_le R hR)

/-- Abstract form of the rounding estimate: if every pair contributes an
error of absolute value at most one, the optimal weights make the total
error at most `R²`. -/
theorem finiteSelbergWeight_double_error_le (R : ℕ) (hR : 1 ≤ R)
    (E : ℕ → ℕ → ℝ)
    (hE : ∀ d ∈ Icc 1 R, ∀ e ∈ Icc 1 R, |E d e| ≤ 1) :
    |∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e * E d e| ≤ (R : ℝ) ^ 2 := by
  calc
    |∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
        finiteSelbergWeight R d * finiteSelbergWeight R e * E d e| ≤
        ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          |finiteSelbergWeight R d * finiteSelbergWeight R e * E d e| := by
            refine (abs_sum_le_sum_abs _ _).trans ?_
            exact sum_le_sum fun d hd => abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          |finiteSelbergWeight R d| * |finiteSelbergWeight R e| := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      rw [abs_mul, abs_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hE d hd e he)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ d ∈ Icc 1 R, |finiteSelbergWeight R d|) ^ 2 := by
      rw [pow_two, sum_mul]
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
    _ ≤ (R : ℝ) ^ 2 := finiteSelbergWeight_sum_abs_sq_le R hR

/-- The concrete interval-count rounding term satisfies the abstract `R²`
estimate. -/
theorem finiteSelberg_interval_rounding_le (S R c : ℕ) (hR : 1 ≤ R) :
    |∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      finiteSelbergWeight R d * finiteSelbergWeight R e *
        ((∑ n ∈ Ico 1 (1 + S),
            selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n) -
          (S : ℝ) / Nat.lcm d e)| ≤ (R : ℝ) ^ 2 := by
  apply finiteSelbergWeight_double_error_le R hR
  intro d hd e he
  have hd0 : d ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hd).1
  have he0 : e ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_Icc.mp he).1
  have hlcm : 1 ≤ Nat.lcm d e :=
    Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero hd0 he0)
  simpa [Nat.add_comm] using
    selbergCrt_sum_indicator_lcm_abs_le 1 S d e (c : ℤ) hlcm

theorem finiteSelberg_sum_divisorSum_sq_le (S R c : ℕ) (hR : 1 ≤ R) :
    ∑ n ∈ Icc 1 S, finiteSelbergDivisorSum R (c : ℤ) n ^ 2 ≤
      (S : ℝ) / selbergJR R + (R : ℝ) ^ 2 := by
  let E : ℝ :=
    ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
      finiteSelbergWeight R d * finiteSelbergWeight R e *
        ((∑ n ∈ Icc 1 S,
            selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n) -
          (S : ℝ) / Nat.lcm d e)
  have hround : |E| ≤ (R : ℝ) ^ 2 := by
    dsimp [E]
    simpa only [finiteSelberg_Icc_eq_Ico S] using
      finiteSelberg_interval_rounding_le S R c hR
  have hEle : E ≤ (R : ℝ) ^ 2 := (le_abs_self E).trans hround
  have hdecomp :
      ∑ n ∈ Icc 1 S, finiteSelbergDivisorSum R (c : ℤ) n ^ 2 =
        (S : ℝ) *
          (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
            finiteSelbergWeight R d * finiteSelbergWeight R e /
              (Nat.lcm d e : ℝ)) + E := by
    rw [finiteSelberg_sum_divisorSum_sq_expand]
    dsimp [E]
    calc
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          finiteSelbergWeight R d * finiteSelbergWeight R e *
            ∑ n ∈ Icc 1 S,
              selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n =
        ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
          ((S : ℝ) *
              (finiteSelbergWeight R d * finiteSelbergWeight R e /
                (Nat.lcm d e : ℝ)) +
            finiteSelbergWeight R d * finiteSelbergWeight R e *
              ((∑ n ∈ Icc 1 S,
                  selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n) -
                (S : ℝ) / Nat.lcm d e)) := by
          apply sum_congr rfl
          intro d hd
          apply sum_congr rfl
          intro e he
          ring
      _ = (S : ℝ) *
          (∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
            finiteSelbergWeight R d * finiteSelbergWeight R e /
              (Nat.lcm d e : ℝ)) +
          ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 R,
            finiteSelbergWeight R d * finiteSelbergWeight R e *
              ((∑ n ∈ Icc 1 S,
                  selbergCrt_indicator (Nat.lcm d e) (c : ℤ) n) -
                (S : ℝ) / Nat.lcm d e) := by
        simp_rw [sum_add_distrib]
        rw [mul_sum]
        apply congrArg₂ (fun x y : ℝ => x + y)
        · apply sum_congr rfl
          intro d hd
          rw [mul_sum]
        · rfl
  rw [hdecomp, finiteSelberg_quadratic_eq hR]
  have hmain : (S : ℝ) * (1 / selbergJR R) = (S : ℝ) / selbergJR R := by
    ring
  rw [hmain]
  simpa only [add_comm] using add_le_add_left hEle ((S : ℝ) / selbergJR R)

/-- CRT consolidates the independently chosen forbidden prime residues into
one center.  No bound on the center or on the prime product is needed by the
interval argument. -/
theorem finiteSelberg_exists_crtCenter {A : Finset ℕ} {R : ℕ}
    (havoid : ∀ p ∈ Nat.primesLE R, ∃ c : ℕ,
      ∀ n ∈ A, n % p ≠ c % p) :
    ∃ c : ℕ, ∀ p ∈ Nat.primesLE R, ∀ n ∈ A,
      n % p ≠ c % p := by
  classical
  let residue : ∀ p : ℕ, p ∈ Nat.primesLE R → ℕ :=
    fun p hp => Classical.choose (havoid p hp)
  have hresidue : ∀ p : ℕ, ∀ hp : p ∈ Nat.primesLE R,
      ∀ n ∈ A, n % p ≠ residue p hp % p := by
    intro p hp
    exact Classical.choose_spec (havoid p hp)
  let modulus : {p // p ∈ Nat.primesLE R} → ℕ := fun p => p.1
  let chosen : {p // p ∈ Nat.primesLE R} → ℕ := fun p => residue p.1 p.2
  have hnonzero : ∀ p ∈ (Finset.univ : Finset {p // p ∈ Nat.primesLE R}),
      modulus p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primesLE p.2).ne_zero
  have hpair : Set.Pairwise
      (Finset.univ : Finset {p // p ∈ Nat.primesLE R})
        (Function.onFun Nat.Coprime modulus) := by
    intro p hp q hq hpq
    apply (Nat.coprime_primes
      (Nat.prime_of_mem_primesLE p.2) (Nat.prime_of_mem_primesLE q.2)).mpr
    intro hpqval
    exact hpq (Subtype.ext hpqval)
  let center := Nat.chineseRemainderOfFinset chosen modulus Finset.univ hnonzero hpair
  refine ⟨center, ?_⟩
  intro p hp n hn
  have hcenter := center.property ⟨p, hp⟩ (mem_univ _)
  have havoid' := hresidue p hp n hn
  intro hnc
  apply havoid'
  exact hnc.trans hcenter

/-- Uniform finite Selberg upper bound on a positive integer block. -/
theorem finiteSelberg_card_le {A : Finset ℕ} {S R : ℕ}
    (hR : 1 ≤ R) (hRS : R ≤ S) (hA : A ⊆ Icc 1 S)
    (havoid : ∀ p ∈ Nat.primesLE R, ∃ c : ℕ,
      ∀ n ∈ A, n % p ≠ c % p) :
    (A.card : ℝ) ≤ (S : ℝ) / selbergJR R + (R : ℝ) ^ 2 := by
  obtain ⟨c, hcenter⟩ := finiteSelberg_exists_crtCenter havoid
  calc
    (A.card : ℝ) = ∑ n ∈ A, (1 : ℝ) := by simp
    _ = ∑ n ∈ A, finiteSelbergDivisorSum R (c : ℤ) n ^ 2 := by
      apply sum_congr rfl
      intro n hn
      rw [finiteSelbergDivisorSum_eq_one_on hR hcenter hn]
      norm_num
    _ ≤ ∑ n ∈ Icc 1 S, finiteSelbergDivisorSum R (c : ℤ) n ^ 2 := by
      exact sum_le_sum_of_subset_of_nonneg hA
        (fun n hnIcc hnA => sq_nonneg (finiteSelbergDivisorSum R (c : ℤ) n))
    _ ≤ (S : ℝ) / selbergJR R + (R : ℝ) ^ 2 :=
      finiteSelberg_sum_divisorSum_sq_le S R c hR

end

end PrimeGapNormality.Prime
