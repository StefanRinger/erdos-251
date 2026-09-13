import PrimeGapNormality.Prime.CoreSelbergPositiveInsertion
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Positive insertion for a compact family of polynomial phases

A fixed degree bound and coefficient continuity on a compact parameter
set give one derivative bound on the padded slot interval. Clamping gives
a globally Lipschitz real test, to which the proved uniform Selberg
insertion theorem applies. The outer phase stays circle-valued throughout;
no real lift, independence, or polynomial nonconstancy is needed.
-/

namespace PrimeGapNormality.Prime.CoreCompactPolynomialInsertion

open Set Filter Finset MeasureTheory
open scoped Topology NNReal Polynomial BoundedContinuousFunction

noncomputable section

abbrev Circle := AddCircle (1 : ℝ)

variable {α : Type*} [TopologicalSpace α]

/-- Joint derivative continuity follows from the actual finite coefficient
expansion, even when the degree drops at some parameter values. -/
theorem derivative_eval_continuousOn
    (Q : α → ℝ[X]) (S : Set α) (d : ℕ)
    (hd : ∀ y ∈ S, (Q y).natDegree ≤ d)
    (hcoeff : ∀ n, ContinuousOn (fun y => (Q y).coeff n) S)
    (A : ℝ) :
    ContinuousOn (fun z : α × ℝ => (Q z.1).derivative.eval z.2)
      (S ×ˢ Icc 0 (A + 1)) := by
  have hsum : ContinuousOn (fun z : α × ℝ =>
      ∑ n ∈ range (d + 1), (Q z.1).coeff (n + 1) * ((n + 1 : ℕ) : ℝ) * z.2 ^ n)
      (S ×ˢ Icc 0 (A + 1)) := by
    apply continuousOn_finsetSum
    intro n _
    exact (((hcoeff (n + 1)).comp continuous_fst.continuousOn
      (fun z hz => hz.1)).mul continuousOn_const).mul
        (continuous_snd.continuousOn.pow n)
  apply hsum.congr
  intro z hz
  have hdeg : (Q z.1).derivative.natDegree < d + 1 :=
    lt_of_le_of_lt (((Q z.1).natDegree_derivative_le.trans (Nat.sub_le _ _)).trans
      (hd z.1 hz.1)) (Nat.lt_succ_self d)
  change (Q z.1).derivative.eval z.2 =
    ∑ n ∈ range (d + 1), (Q z.1).coeff (n + 1) * ((n + 1 : ℕ) : ℝ) * z.2 ^ n
  rw [Polynomial.eval_eq_sum_range' hdeg]
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.coeff_derivative]
  simp only [Nat.cast_add, Nat.cast_one]

/-- One Lipschitz constant for every polynomial on the padded compact slot. -/
theorem exists_uniform_polynomial_lipschitz
    (Q : α → ℝ[X]) {S : Set α} (hS : IsCompact S) (d : ℕ)
    (hd : ∀ y ∈ S, (Q y).natDegree ≤ d)
    (hcoeff : ∀ n, ContinuousOn (fun y => (Q y).coeff n) S)
    (A : ℝ) :
    ∃ D : ℝ≥0, ∀ y ∈ S, LipschitzOnWith D (Q y).eval (Icc 0 (A + 1)) := by
  obtain ⟨M, hM⟩ := (hS.prod isCompact_Icc).exists_bound_of_continuousOn
    (derivative_eval_continuousOn Q S d hd hcoeff A)
  let D : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  refine ⟨D, ?_⟩
  intro y hy
  apply (convex_Icc (0 : ℝ) (A + 1)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (Q y).hasDerivWithinAt t _)
  intro t ht
  have hbound : ‖(Q y).derivative.eval t‖ ≤ (D : ℝ) :=
    (hM (y, t) ⟨hy, ht⟩).trans (le_max_left _ _)
  exact_mod_cast hbound

def clamp (A t : ℝ) : ℝ := max 0 (min t (A + 1))

theorem clamp_mem {A : ℝ} (hA : 0 ≤ A) (t : ℝ) : clamp A t ∈ Icc 0 (A + 1) :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clamp_eq {A t : ℝ} (ht : t ∈ Icc 0 (A + 1)) : clamp A t = t := by
  rw [clamp, min_eq_left ht.2, max_eq_right ht.1]

theorem clamp_lipschitz (A : ℝ) : LipschitzWith 1 (clamp A) :=
  (LipschitzWith.id.min_const (A + 1)).const_max 0

theorem clamped_polynomial_lipschitz (P : ℝ[X]) {A : ℝ} (hA : 0 ≤ A) {D : ℝ≥0}
    (hP : LipschitzOnWith D P.eval (Icc 0 (A + 1))) :
    LipschitzWith D (fun t => P.eval (clamp A t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc : dist (clamp A x) (clamp A y) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul] using (clamp_lipschitz A).dist_le_mul x y
  exact (hP.dist_le_mul _ (clamp_mem hA x) _ (clamp_mem hA y)).trans
    (mul_le_mul_of_nonneg_left hc D.coe_nonneg)

private theorem circle_dist_coe_le (x y : ℝ) :
    dist (x : Circle) (y : Circle) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

/-- Translation is performed on the circle itself, not using a lift. -/
theorem phase_lipschitz (q : ℝ → ℝ) {D : ℝ≥0} (hq : LipschitzWith D q)
    {C : ℝ} (hC : 0 ≤ C) (O : Circle) {θ : ℝ} (hθ : |θ| ≤ C) :
    LipschitzWith (⟨C, hC⟩ * D)
      (fun t => O + ((θ * q t : ℝ) : Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_add_left]
  calc
    dist ((θ * q x : ℝ) : Circle) ((θ * q y : ℝ) : Circle) ≤
        |θ * q x - θ * q y| := circle_dist_coe_le _ _
    _ = |θ| * dist (q x) (q y) := by rw [← mul_sub, abs_mul, Real.dist_eq]
    _ ≤ C * ((D : ℝ) * dist x y) :=
      mul_le_mul hθ (hq.dist_le_mul x y) dist_nonneg hC
    _ = ((⟨C, hC⟩ * D : ℝ≥0) : ℝ) * dist x y := by
      change C * ((D : ℝ) * dist x y) = (C * (D : ℝ)) * dist x y
      ring

/-- Actual positive Selberg insertion, uniformly over the compact
coefficient family, every circle phase and every bounded scale.
The same bound works for constant and degree-dropping polynomials. -/
theorem eventually_positive_polynomial_insertion
    (Q : α → ℝ[X]) {S : Set α} (hS : IsCompact S) (d : ℕ)
    (hd : ∀ y ∈ S, (Q y).natDegree ≤ d)
    (hcoeff : ∀ n, ContinuousOn (fun y => (Q y).coeff n) S)
    {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (f : Circle →ᵇ ℝ) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf0 : ∀ x, 0 ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ G : ℝ in atTop, ∀ y ∈ S, ∀ (O : Circle) (θ : ℝ), θ ∈ Icc 1 C →
      ∀ (a : ℕ) (W : ℝ) (E : Finset ℕ),
        0 ≤ W → W ≤ A →
        (∀ n ∈ E, a < n ∧ (n : ℝ) - a < W * G) →
        CoreSelberg.AvoidsResidues E ⌊G⌋₊ →
        (∑ n ∈ E, f (O + ((θ * (Q y).eval (((n : ℝ) - a) / G) : ℝ) : Circle))) ≤
          3 * G / Real.log G *
            ((∫ t in 0..W, f (O + ((θ * (Q y).eval t : ℝ) : Circle))) + ε) := by
  obtain ⟨D, hD⟩ := exists_uniform_polynomial_lipschitz Q hS d hd hcoeff A
  let K' : ℝ≥0 := K * (⟨C, hC⟩ * D)
  filter_upwards [CoreSelberg.eventually_positive_insertion
    (K := K') hA (norm_nonneg f) hε, eventually_ge_atTop (1 : ℝ)] with G hsel hG
  intro y hy O θ hθ a W E hW hWA hE havoid
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  let g : ℝ → ℝ := fun t => f (O + ((θ * (Q y).eval (clamp A t) : ℝ) : Circle))
  have hθabs : |θ| ≤ C := by
    rw [abs_of_nonneg (zero_le_one.trans hθ.1)]
    exact hθ.2
  have hgLip : LipschitzWith K' g :=
    hK.comp (phase_lipschitz _
      (clamped_polynomial_lipschitz (Q y) hA.le (hD y hy)) hC O hθabs)
  have hgBound : ∀ t ∈ Icc 0 (A + 1), 0 ≤ g t ∧ g t ≤ ‖f‖ := by
    intro t _
    exact ⟨hf0 _, f.apply_le_norm _⟩
  have hmain := hsel a W E g hW hWA hE havoid hgLip hgBound
  have hsum : (∑ n ∈ E, g (((n : ℝ) - a) / G)) =
      ∑ n ∈ E, f (O + ((θ * (Q y).eval (((n : ℝ) - a) / G) : ℝ) : Circle)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hna : (a : ℝ) < n := by exact_mod_cast (hE n hn).1
    have ht : ((n : ℝ) - a) / G ∈ Icc 0 (A + 1) := by
      refine ⟨div_nonneg (sub_nonneg.mpr hna.le) hG0.le, ?_⟩
      have htW := (div_lt_iff₀ hG0).2 (hE n hn).2
      linarith
    dsimp only [g]
    rw [clamp_eq ht]
  have hint : (∫ t in 0..W, g t) =
      ∫ t in 0..W, f (O + ((θ * (Q y).eval t : ℝ) : Circle)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hW] at ht
    have ht' : t ∈ Icc 0 (A + 1) := ⟨ht.1, by linarith [ht.2]⟩
    dsimp only [g]
    rw [clamp_eq ht']
  rw [hsum, hint] at hmain
  exact hmain

end

end PrimeGapNormality.Prime.CoreCompactPolynomialInsertion
