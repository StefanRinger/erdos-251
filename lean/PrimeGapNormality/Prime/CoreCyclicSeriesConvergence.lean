import PrimeGapNormality.Prime.CoreCyclicTelescope
import PrimeGapNormality.Prime.PrimeSeries

/-!
The analytic completion of the finite cyclic telescope identity.  The only
input on a gap sequence is an explicit polynomial-growth estimate.  In
particular, no convergence or prime-distribution hypothesis is hidden in the
normal-form statement.

The final specialization uses the proved Chebyshev bound on `nthPrime` to
verify polynomial growth of the actual prime gaps.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open Filter Finset MvPolynomial
open scoped BigOperators Topology

noncomputable section

/-- A sequence has a global polynomial majorant.  Keeping the coefficient
nonnegative makes the elementary closure lemmas usable as a public API. -/
def HasPolynomialGrowth (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧
    ∀ n : ℕ, |f n| ≤ C * (((n + 1 : ℕ) : ℝ) ^ d)

theorem hasPolynomialGrowth_const (c : ℝ) :
    HasPolynomialGrowth fun _ : ℕ ↦ c := by
  refine ⟨|c|, 0, abs_nonneg c, ?_⟩
  intro n
  simp

theorem HasPolynomialGrowth.add {f g : ℕ → ℝ}
    (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth fun n ↦ f n + g n := by
  obtain ⟨C, d, hC, hf⟩ := hf
  obtain ⟨D, e, hD, hg⟩ := hg
  refine ⟨C + D, max d e, add_nonneg hC hD, ?_⟩
  intro n
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hd : x ^ d ≤ x ^ max d e := pow_le_pow_right₀ hx (le_max_left d e)
  have he : x ^ e ≤ x ^ max d e := pow_le_pow_right₀ hx (le_max_right d e)
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ C * x ^ d + D * x ^ e := add_le_add (hf n) (hg n)
    _ ≤ C * x ^ max d e + D * x ^ max d e :=
      add_le_add (mul_le_mul_of_nonneg_left hd hC)
        (mul_le_mul_of_nonneg_left he hD)
    _ = (C + D) * x ^ max d e := by ring

theorem HasPolynomialGrowth.mul {f g : ℕ → ℝ}
    (hf : HasPolynomialGrowth f) (hg : HasPolynomialGrowth g) :
    HasPolynomialGrowth fun n ↦ f n * g n := by
  obtain ⟨C, d, hC, hf⟩ := hf
  obtain ⟨D, e, hD, hg⟩ := hg
  refine ⟨C * D, d + e, mul_nonneg hC hD, ?_⟩
  intro n
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hfd := hf n
  have hge := hg n
  have hmul : |f n| * |g n| ≤ (C * x ^ d) * (D * x ^ e) :=
    mul_le_mul hfd hge (abs_nonneg _) (mul_nonneg hC (pow_nonneg (by positivity) _))
  rw [abs_mul]
  calc
    |f n| * |g n| ≤ (C * x ^ d) * (D * x ^ e) := hmul
    _ = (C * D) * x ^ (d + e) := by rw [pow_add]; ring

theorem HasPolynomialGrowth.shift {f : ℕ → ℝ}
    (hf : HasPolynomialGrowth f) (a : ℕ) :
    HasPolynomialGrowth fun n ↦ f (n + a) := by
  obtain ⟨C, d, hC, hf⟩ := hf
  refine ⟨C * (((a + 1 : ℕ) : ℝ) ^ d), d,
    mul_nonneg hC (pow_nonneg (by positivity) _), ?_⟩
  intro n
  have hnat : n + a + 1 ≤ (a + 1) * (n + 1) := by
    nlinarith [Nat.zero_le (n * a)]
  have hcast : (((n + a + 1 : ℕ) : ℝ)) ≤
      ((a + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n + a + 1 : ℕ)) hcast d
  calc
    |f (n + a)| ≤ C * (((n + a + 1 : ℕ) : ℝ) ^ d) := hf (n + a)
    _ ≤ C * ((((a + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ d) :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = (C * (((a + 1 : ℕ) : ℝ) ^ d)) * (((n + 1 : ℕ) : ℝ) ^ d) := by
      rw [mul_pow]
      ring

/-- Polynomial growth is stable under evaluating a fixed rational
multivariate polynomial on the translated windows of a polynomially growing
sequence. -/
theorem hasPolynomialGrowth_eval₂ (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (p : LocalPoly) :
    HasPolynomialGrowth fun n ↦
      eval₂ (algebraMap ℚ ℝ) (fun j ↦ g (n + j)) p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa using hasPolynomialGrowth_const ((algebraMap ℚ ℝ) c)
  | add p q hp hq =>
      simpa only [eval₂_add] using hp.add hq
  | mul_X p j hp =>
      have hj : HasPolynomialGrowth fun n ↦ g (n + j) := hg.shift j
      simpa only [eval₂_mul, eval₂_X] using hp.mul hj

/-- A selector through finitely many polynomially bounded sequences remains
polynomially bounded. -/
theorem hasPolynomialGrowth_fin_choice {k : ℕ} (hk : 0 < k)
    (f : Fin k → ℕ → ℝ) (hf : ∀ s, HasPolynomialGrowth (f s))
    (s : ℕ → Fin k) : HasPolynomialGrowth fun n ↦ f (s n) n := by
  classical
  let C : Fin k → ℝ := fun i ↦ Classical.choose (hf i)
  let d : Fin k → ℕ := fun i ↦ Classical.choose (Classical.choose_spec (hf i))
  have hC (i : Fin k) : 0 ≤ C i :=
    (Classical.choose_spec (Classical.choose_spec (hf i))).1
  have hbound (i : Fin k) (n : ℕ) :
      |f i n| ≤ C i * (((n + 1 : ℕ) : ℝ) ^ d i) :=
    (Classical.choose_spec (Classical.choose_spec (hf i))).2 n
  let D : ℕ := univ.sup d
  refine ⟨∑ i, C i, D, sum_nonneg fun i _ ↦ hC i, ?_⟩
  intro n
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hd : d (s n) ≤ D := Finset.le_sup (f := d) (mem_univ (s n))
  have hpow : x ^ d (s n) ≤ x ^ D := pow_le_pow_right₀ hx hd
  have hterm : C (s n) ≤ ∑ i, C i :=
    single_le_sum (fun i _ ↦ hC i) (mem_univ (s n))
  calc
    |f (s n) n| ≤ C (s n) * x ^ d (s n) := hbound (s n) n
    _ ≤ C (s n) * x ^ D := mul_le_mul_of_nonneg_left hpow (hC (s n))
    _ ≤ (∑ i, C i) * x ^ D :=
      mul_le_mul_of_nonneg_right hterm (pow_nonneg (by positivity) _)

/-- Every finite periodic tuple of local rational polynomials has polynomial
growth on a polynomially growing input sequence. -/
theorem localValue_hasPolynomialGrowth {k : ℕ} (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) :
    HasPolynomialGrowth fun n ↦ localValue hk r g F n := by
  let f : Fin k → ℕ → ℝ := fun s n ↦
    eval₂ (algebraMap ℚ ℝ) (fun j ↦ g (n + j)) (F s)
  have hf : ∀ s, HasPolynomialGrowth (f s) := fun s ↦
    hasPolynomialGrowth_eval₂ g hg (F s)
  simpa only [localValue, f] using
    hasPolynomialGrowth_fin_choice hk f hf (phaseAt hk r)

private theorem core_inv_base_norm_lt_one {B : ℕ} (hB : 2 ≤ B) :
    ‖((B : ℝ)⁻¹)‖ < 1 := by
  have hB1 : (1 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hB)
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ))]
  exact inv_lt_one_of_one_lt₀ hB1

private theorem summable_succ_pow_geometric {B d : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ d) * (B : ℝ)⁻¹ ^ n := by
  have hr := core_inv_base_norm_lt_one hB
  have hpow := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d hr
  have hshift :=
    (summable_nat_add_iff
      (f := fun n : ℕ ↦ (n : ℝ) ^ d * (B : ℝ)⁻¹ ^ n) 1).2 hpow
  refine (hshift.mul_left (B : ℝ)).congr fun n ↦ ?_
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num, pow_add]
  field_simp [hB0]

private theorem polynomial_geometric_majorant (C : ℝ) {B d : ℕ}
    (hB : 2 ≤ B) :
    Summable fun n : ℕ ↦
      (C / B) * ((((n + 1 : ℕ) : ℝ) ^ d) * (B : ℝ)⁻¹ ^ n) :=
  (summable_succ_pow_geometric (B := B) (d := d) hB).mul_left (C / B)

/-- Polynomial growth is sufficient for absolute summability against the
base-`B` digit weight. -/
theorem HasPolynomialGrowth.summable_div_pow {f : ℕ → ℝ}
    (hf : HasPolynomialGrowth f) {B : ℕ} (hB : 2 ≤ B) :
    Summable fun n : ℕ ↦ f n / (B : ℝ) ^ (n + 1) := by
  obtain ⟨C, d, hC, hf⟩ := hf
  have hdom := polynomial_geometric_majorant C (B := B) (d := d) hB
  refine Summable.of_norm_bounded hdom fun n ↦ ?_
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hden : 0 ≤ (B : ℝ) ^ (n + 1) := pow_nonneg (by positivity) _
  have hbound : |f n| / (B : ℝ) ^ (n + 1) ≤
      (C * (((n + 1 : ℕ) : ℝ) ^ d)) / (B : ℝ) ^ (n + 1) :=
    div_le_div_of_nonneg_right (hf n) hden
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) ^ (n + 1))]
  calc
    |f n| / (B : ℝ) ^ (n + 1) ≤
        (C * (((n + 1 : ℕ) : ℝ) ^ d)) / (B : ℝ) ^ (n + 1) := hbound
    _ = (C / B) * ((((n + 1 : ℕ) : ℝ) ^ d) * (B : ℝ)⁻¹ ^ n) := by
      rw [pow_succ, inv_pow]
      field_simp [hB0]

/-- A polynomial boundary divided by the restarted geometric denominator
tends to zero, uniformly for every fixed starting index. -/
theorem HasPolynomialGrowth.tendsto_shift_div_pow {f : ℕ → ℝ}
    (hf : HasPolynomialGrowth f) {B : ℕ} (hB : 2 ≤ B) (a : ℕ) :
    Tendsto (fun N : ℕ ↦ f (a + N) / (B : ℝ) ^ N) atTop (𝓝 0) := by
  have hs : Summable fun N : ℕ ↦ f (a + N) / (B : ℝ) ^ (N + 1) :=
    by simpa only [Nat.add_comm] using (hf.shift a).summable_div_pow hB
  have ht := hs.tendsto_atTop_zero
  have hfun : (fun N : ℕ ↦ f (a + N) / (B : ℝ) ^ N) =
      fun N : ℕ ↦ (B : ℝ) * (f (a + N) / (B : ℝ) ^ (N + 1)) := by
    funext N
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp [hB0]
  rw [hfun]
  simpa using ht.const_mul (B : ℝ)

set_option maxHeartbeats 800000 in
/-- Absolute convergence of the actual local series. -/
theorem localSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) (a : ℕ) :
    Summable fun n : ℕ ↦
      localValue hk r g F (a + n) / (B : ℝ) ^ (n + 1) :=
  by
    simpa only [Nat.add_comm] using
      ((localValue_hasPolynomialGrowth hk r g hg F).shift a).summable_div_pow hB

/-- The actual primitive boundary in `finiteSeries_normalForm` vanishes. -/
theorem primitive_boundary_tendsto_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) (a : ℕ) :
    Tendsto (fun N : ℕ ↦
      localValue hk r g (primitive hB hk F) (a + N) / (B : ℝ) ^ N)
      atTop (𝓝 0) :=
  (localValue_hasPolynomialGrowth hk r g hg (primitive hB hk F)).tendsto_shift_div_pow hB a

/-- Infinite cyclic normal form, obtained only after proving convergence and
the primitive boundary limit. -/
theorem infiniteSeries_normalForm {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (hg : HasPolynomialGrowth g)
    (F : PeriodicLocal k) (a : ℕ) :
    (∑' n : ℕ, localValue hk r g F (a + n) / (B : ℝ) ^ (n + 1)) -
        (∑' n : ℕ, localValue hk r g (normalForm hB hk F) (a + n) /
          (B : ℝ) ^ (n + 1)) =
      localValue hk r g (primitive hB hk F) a := by
  have hsF := localSeries_summable hB hk r g hg F a
  have hsR := localSeries_summable hB hk r g hg (normalForm hB hk F) a
  have hsum : Tendsto
      (fun N : ℕ ↦ finiteSeries B hk r g F a N -
        finiteSeries B hk r g (normalForm hB hk F) a N)
      atTop
      (𝓝 ((∑' n : ℕ, localValue hk r g F (a + n) / (B : ℝ) ^ (n + 1)) -
        (∑' n : ℕ, localValue hk r g (normalForm hB hk F) (a + n) /
          (B : ℝ) ^ (n + 1)))) := by
    simpa only [finiteSeries] using hsF.hasSum.tendsto_sum_nat.sub hsR.hasSum.tendsto_sum_nat
  have hboundary : Tendsto
      (fun N : ℕ ↦ localValue hk r g (primitive hB hk F) a -
        localValue hk r g (primitive hB hk F) (a + N) / (B : ℝ) ^ N)
      atTop (𝓝 (localValue hk r g (primitive hB hk F) a)) := by
    simpa using tendsto_const_nhds.sub
      (primitive_boundary_tendsto_zero hB hk r g hg F a)
  apply tendsto_nhds_unique hsum
  exact hboundary.congr' (Eventually.of_forall fun N ↦
    (finiteSeries_normalForm hB hk r g F a N).symm)

/-- Rational evaluation of the boundary before embedding into the reals. -/
def localBoundaryRat {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℤ) (F : PeriodicLocal k) (a : ℕ) : ℚ :=
  eval₂ (RingHom.id ℚ) (fun j ↦ (g (a + j) : ℚ))
    (primitive hB hk F (phaseAt hk r a))

theorem localBoundaryRat_cast {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℤ) (F : PeriodicLocal k) (a : ℕ) :
    (localBoundaryRat hB hk r g F a : ℝ) =
      localValue hk r (fun n ↦ (g n : ℝ)) (primitive hB hk F) a := by
  rw [localBoundaryRat, localValue]
  have h := eval₂_comp_left (algebraMap ℚ ℝ) (RingHom.id ℚ)
    (fun j ↦ (g (a + j) : ℚ)) (primitive hB hk F (phaseAt hk r a))
  change (algebraMap ℚ ℝ)
      (eval₂ (RingHom.id ℚ) (fun j ↦ (g (a + j) : ℚ))
        (primitive hB hk F (phaseAt hk r a))) = _
  rw [h]
  congr 1

/-- For an integer input sequence, the infinite normal-form discrepancy is
the explicitly displayed rational primitive boundary. -/
theorem infiniteSeries_normalForm_eq_rat {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℤ)
    (hg : HasPolynomialGrowth fun n ↦ (g n : ℝ))
    (F : PeriodicLocal k) (a : ℕ) :
    (∑' n : ℕ, localValue hk r (fun m ↦ (g m : ℝ)) F (a + n) /
        (B : ℝ) ^ (n + 1)) -
        (∑' n : ℕ,
          localValue hk r (fun m ↦ (g m : ℝ)) (normalForm hB hk F) (a + n) /
            (B : ℝ) ^ (n + 1)) =
      (localBoundaryRat hB hk r g F a : ℝ) := by
  rw [localBoundaryRat_cast]
  exact infiniteSeries_normalForm hB hk r _ hg F a

/-- The actual prime-gap sequence has quadratic growth, with no analytic
prime-index hypothesis. -/
theorem primeGap_hasPolynomialGrowth :
    HasPolynomialGrowth fun n ↦ (primeGap n : ℝ) := by
  refine ⟨576, 2, by norm_num, ?_⟩
  intro n
  have hgap : primeGap n ≤ nthPrime (n + 1) := primeGap_le_nthPrime_succ n
  have hnth : nthPrime (n + 1) ≤ 144 * (n + 2) ^ 2 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using nthPrime_le_succ_sq (n + 1)
  have hidx : n + 2 ≤ 2 * (n + 1) := by omega
  have hfinal : primeGap n ≤ 576 * (n + 1) ^ 2 := by
    calc
      primeGap n ≤ nthPrime (n + 1) := hgap
      _ ≤ 144 * (n + 2) ^ 2 := hnth
      _ ≤ 144 * (2 * (n + 1)) ^ 2 :=
        Nat.mul_le_mul_left 144 (Nat.pow_le_pow_left hidx 2)
      _ = 576 * (n + 1) ^ 2 := by ring
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  dsimp
  exact_mod_cast hfinal

theorem primeGap_localSeries_summable {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : PeriodicLocal k) (a : ℕ) :
    Summable fun n : ℕ ↦
      localValue hk r (fun m ↦ (primeGap m : ℝ)) F (a + n) /
        (B : ℝ) ^ (n + 1) :=
  localSeries_summable hB hk r _ primeGap_hasPolynomialGrowth F a

/-- The infinite canonical identity for the actual prime gaps; convergence
and rationality are conclusions, not hypotheses. -/
theorem primeGap_infiniteSeries_normalForm {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (F : PeriodicLocal k) (a : ℕ) :
    (∑' n : ℕ, localValue hk r (fun m ↦ (primeGap m : ℝ)) F (a + n) /
        (B : ℝ) ^ (n + 1)) -
        (∑' n : ℕ,
          localValue hk r (fun m ↦ (primeGap m : ℝ)) (normalForm hB hk F) (a + n) /
            (B : ℝ) ^ (n + 1)) =
      (localBoundaryRat hB hk r (fun n ↦ (primeGap n : ℤ)) F a : ℝ) := by
  apply infiniteSeries_normalForm_eq_rat hB hk r (fun n ↦ (primeGap n : ℤ))
  simpa only [Int.cast_natCast] using primeGap_hasPolynomialGrowth

end

end PrimeGapNormality.Prime.CoreCyclic
