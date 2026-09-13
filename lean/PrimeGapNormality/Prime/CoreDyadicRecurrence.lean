import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# A contracting recurrence along an earlier index

This elementary Tauberian step is intended for initial-count asymptotics:
after dividing by the Euler main term, splitting at floor(X/2) gives a
contraction plus an error tending to zero. No density conclusion is assumed
here or attributed to the lemma until the actual arithmetic recurrence is
supplied.
-/

namespace PrimeGapNormality.Prime.CoreDyadicRecurrence

open Filter Finset
open scoped Topology
noncomputable section

theorem bounded_of_earlier_contraction {f : ℕ → ℝ} {d : ℕ → ℕ} {q R : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hR : 0 ≤ R)
    (hrec : ∀ᶠ n : ℕ in atTop, d n < n ∧ |f n| ≤ q * |f (d n)| + R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n, |f n| ≤ M := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hrec
  let M := (∑ n ∈ range N, |f n|) + R / (1 - q)
  have hden : 0 < 1 - q := by linarith
  have hsum : 0 ≤ ∑ n ∈ range N, |f n| := sum_nonneg fun _ _ => abs_nonneg _
  have hMr : R / (1 - q) ≤ M := by dsimp only [M]; linarith
  have hM0 : 0 ≤ M := (div_nonneg hR hden.le).trans hMr
  refine ⟨M, hM0, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < N
      · have hsingle : |f n| ≤ ∑ j ∈ range N, |f j| :=
          Finset.single_le_sum (f := fun j => |f j|)
            (fun j hj => abs_nonneg (f j)) (mem_range.mpr hn)
        exact hsingle.trans (by
          dsimp only [M]
          exact le_add_of_nonneg_right (div_nonneg hR hden.le))
      · have hr := hN n (by omega)
        have hprev := ih (d n) hr.1
        have hRM : R ≤ M * (1 - q) := (div_le_iff₀ hden).mp hMr
        calc
          |f n| ≤ q * |f (d n)| + R := hr.2
          _ ≤ q * M + R := _root_.add_le_add (mul_le_mul_of_nonneg_left hprev hq0) le_rfl
          _ ≤ M := by nlinarith

/-- Fixed finite iterations are valid once the predecessor map tends to
infinity; no uniform-in-depth error assumption is used. -/
theorem eventually_iterated_bound {f : ℕ → ℝ} {d : ℕ → ℕ} {q ε M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (hd : Tendsto d atTop atTop) (hM : ∀ n, |f n| ≤ M)
    (hrec : ∀ᶠ n : ℕ in atTop, |f n| ≤ q * |f (d n)| + ε) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ q ^ k * M + ε / (1 - q) := by
  have hden : 0 < 1 - q := by linarith
  induction k with
  | zero =>
      exact Eventually.of_forall fun n => by
        simp only [pow_zero, one_mul]
        exact (hM n).trans (le_add_of_nonneg_right (div_nonneg hε hden.le))
  | succ k ih =>
      filter_upwards [hrec, hd.eventually ih] with n hr hp
      calc
        |f n| ≤ q * |f (d n)| + ε := hr
        _ ≤ q * (q ^ k * M + ε / (1 - q)) + ε :=
          _root_.add_le_add (mul_le_mul_of_nonneg_left hp hq0) le_rfl
        _ = q ^ (k + 1) * M + ε / (1 - q) := by
          rw [pow_succ']
          field_simp [hden.ne']
          ring

theorem tendsto_zero_of_earlier_contraction
    {f e : ℕ → ℝ} {d : ℕ → ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hd : Tendsto d atTop atTop)
    (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ᶠ n : ℕ in atTop,
      d n < n ∧ |f n| ≤ q * |f (d n)| + |e n|) :
    Tendsto f atTop (𝓝 0) := by
  have heabs : Tendsto (fun n => |e n|) atTop (𝓝 0) := by
    simpa only [abs_zero] using he.abs
  have hboundedRec : ∀ᶠ n : ℕ in atTop,
      d n < n ∧ |f n| ≤ q * |f (d n)| + 1 := by
    filter_upwards [hrec, heabs.eventually_le_const (by norm_num : (0 : ℝ) < 1)]
      with n hr hn
    exact ⟨hr.1, hr.2.trans (_root_.add_le_add le_rfl hn)⟩
  obtain ⟨M, hM0, hM⟩ := bounded_of_earlier_contraction hq0 hq1
    (by norm_num : (0 : ℝ) ≤ 1) hboundedRec
  have hpow : Tendsto (fun k : ℕ => q ^ k * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const M
  apply Metric.tendsto_atTop.mpr
  intro η hη
  have hden : 0 < 1 - q := by linarith
  let ε := η * (1 - q) / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨k, hk⟩ := eventually_atTop.mp
    (hpow.eventually_lt_const (by positivity : (0 : ℝ) < η / 2))
  have hstep : ∀ᶠ n : ℕ in atTop, |f n| ≤ q * |f (d n)| + ε := by
    filter_upwards [hrec, heabs.eventually_le_const hε] with n hr hn
    exact hr.2.trans (_root_.add_le_add le_rfl hn)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_iterated_bound hq0 hq1 hε.le hd hM hstep k)
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero]
  have hεeq : ε / (1 - q) = η / 2 := by
    dsimp only [ε]
    field_simp [hden.ne']
  have hh := hN n hn
  rw [hεeq] at hh
  linarith [hk k le_rfl]

theorem halfIndex_tendsto_atTop :
    Tendsto (fun n : ℕ => n / 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)

theorem tendsto_zero_of_half_recurrence {f e : ℕ → ℝ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ᶠ n : ℕ in atTop, |f n| ≤ q * |f (n / 2)| + |e n|) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_zero_of_earlier_contraction hq0 hq1 halfIndex_tendsto_atTop he
  filter_upwards [hrec, eventually_ge_atTop 1] with n hn hpos
  exact ⟨Nat.div_lt_self (by omega) (by norm_num), hn⟩

/-- Normalized initial counts obey this affine recurrence when the two
adjacent half-interval main terms have their expected asymptotics. -/
theorem tendsto_one_of_affine_half_recurrence
    {u a b : ℕ → ℝ} {c : ℝ} (hc : |c| < 1)
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 (1 - c)))
    (hrec : ∀ᶠ n : ℕ in atTop, u n = a n * u (n / 2) + b n) :
    Tendsto u atTop (𝓝 1) := by
  let q : ℝ := (|c| + 1) / 2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hcq : |c| < q := by dsimp only [q]; linarith
  have herr : Tendsto (fun n => a n + b n - 1) atTop (𝓝 0) := by
    have hh := (ha.add hb).sub_const 1
    simpa only [add_sub_cancel, sub_self] using hh
  have hbound : ∀ᶠ n : ℕ in atTop,
      |u n - 1| ≤ q * |u (n / 2) - 1| + |a n + b n - 1| := by
    filter_upwards [hrec, ha.abs.eventually_le_const hcq] with n hn han
    have hid : u n - 1 = a n * (u (n / 2) - 1) + (a n + b n - 1) := by
      rw [hn]
      ring
    rw [hid]
    calc
      _ ≤ |a n * (u (n / 2) - 1)| + |a n + b n - 1| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        exact _root_.add_le_add (mul_le_mul_of_nonneg_right han (abs_nonneg _)) le_rfl
  have hzero := tendsto_zero_of_half_recurrence hq0 hq1 herr hbound
  have hh := hzero.add_const 1
  simpa only [sub_add_cancel, zero_add] using hh

end
end PrimeGapNormality.Prime.CoreDyadicRecurrence
