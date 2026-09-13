import PrimeGapNormality.Prime.Coupling
import PrimeGapNormality.Prime.ModelMoments
import PrimeGapNormality.Prime.StatisticalCriterion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bernoulli / presieve short-pattern comparison (model only)

Paper v0.3 Appendix B, “Whole-window Bernoulli coupling” and (eq:S) on
the **specified random sieve**, not on `nthPrime`. A bounded test `F`
that vanishes when the `L`-th rooted point exceeds `S` has mixture mean
close to the independent-Bernoulli product mean. The error is the
Coupling total variation `remainingPrimeCouplingTV`, or a named
discrepancy hypothesis (not an axiom).

This file does **not** prove `ShortPatternS nthPrime`. The optional
window-average glue takes a StoppedPrime-scale transfer bound and a
model-versus-mixture bound as hypotheses.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` (eq:S), (eq:coupling),
  (eq:rho); `lean/PrimeGapNormality/Prime/Coupling.lean`;
  `lean/PrimeGapNormality/Prime/StatisticalCriterion.lean`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Polynomial

set_option maxHeartbeats 800000

/-! ### Rooted offsets of a finite survivor set -/

/-- Root `x_0 = 0`. For `k ≥ 1`, the `k`-th increasing survivor of `U`,
or the sentinel `⌊S⌋₊ + 1` if fewer than `k` points are present. The
sentinel is strictly larger than `S`, so a span-cut test vanishes. -/
noncomputable def configOffset (U : Finset ℕ) (S : ℝ) (k : ℕ) : ℕ :=
  if k = 0 then 0
  else (U.sort (· ≤ ·)).getD (k - 1) (⌊S⌋₊ + 1)

private theorem getD_eq_getElem_default {l : List ℕ} {i d : ℕ}
    (hi : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem getD_eq_default_of_le {l : List ℕ} {i d : ℕ}
    (hi : l.length ≤ i) : l.getD i d = d := by
  have hnone : l[i]? = none := getElem?_neg l i (Nat.not_lt.mpr hi)
  rw [List.getD_eq_getElem?_getD, hnone]
  rfl

theorem configOffset_zero (U : Finset ℕ) (S : ℝ) : configOffset U S 0 = 0 :=
  rfl

theorem configOffset_of_le_card {U : Finset ℕ} {S : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hcard : k ≤ U.card) :
    configOffset U S k = (U.sort (· ≤ ·))[k - 1]'(by
      rw [length_sort]
      omega) := by
  have hk0 : k ≠ 0 := by omega
  have hi : k - 1 < (U.sort (· ≤ ·)).length := by
    rw [length_sort]
    omega
  simp only [configOffset, hk0, ↓reduceIte]
  exact getD_eq_getElem_default hi

theorem configOffset_of_card_lt {U : Finset ℕ} {S : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hcard : U.card < k) :
    configOffset U S k = ⌊S⌋₊ + 1 := by
  have hk0 : k ≠ 0 := by omega
  have hi : (U.sort (· ≤ ·)).length ≤ k - 1 := by
    rw [length_sort]
    omega
  simp only [configOffset, hk0, ↓reduceIte]
  exact getD_eq_default_of_le hi

/-- The sentinel used when the `L`-th point is missing exceeds `S`. -/
theorem lt_configOffset_of_card_lt {U : Finset ℕ} {S : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hcard : U.card < L) :
    S < configOffset U S L := by
  rw [configOffset_of_card_lt hL hcard]
  have : S < (⌊S⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one S
  exact_mod_cast this

theorem configOffset_mem {U : Finset ℕ} {S : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hcard : k ≤ U.card) :
    configOffset U S k ∈ U := by
  rw [configOffset_of_le_card hk hcard]
  exact (mem_sort (· ≤ ·)).mp (List.getElem_mem _)

theorem configOffset_le_of_mem_le {U : Finset ℕ} {S : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hcard : L ≤ U.card)
    (hU : ∀ x ∈ U, (x : ℝ) ≤ S) :
    (configOffset U S L : ℝ) ≤ S :=
  hU _ (configOffset_mem hL hcard)

/-! ### Admissible short-pattern tests (paper (eq:S)) -/

/-- Bounded tests of the first `L` offsets that vanish on `{x_L > S}`. -/
def IsAdmissibleShortPattern (L : ℕ) (S : ℝ) (F : (ℕ → ℕ) → ℂ) : Prop :=
  (∀ v, ‖F v‖ ≤ 1) ∧ (∀ v, S < v L → F v = 0)

/-- Span cut matching `truncatedPhaseTestCut`. -/
noncomputable def spanCut (L : ℕ) (S : ℝ) (F : (ℕ → ℕ) → ℂ) (v : ℕ → ℕ) : ℂ :=
  if S < v L then 0 else F v

theorem spanCut_norm (L : ℕ) (S : ℝ) (F : (ℕ → ℕ) → ℂ)
    (hF : ∀ v, ‖F v‖ ≤ 1) (v : ℕ → ℕ) :
    ‖spanCut L S F v‖ ≤ 1 := by
  unfold spanCut
  split_ifs
  · simp
  · exact hF v

theorem spanCut_span (L : ℕ) (S : ℝ) (F : (ℕ → ℕ) → ℂ)
    (v : ℕ → ℕ) (hv : S < v L) :
    spanCut L S F v = 0 := by
  simp [spanCut, hv]

theorem spanCut_admissible (L : ℕ) (S : ℝ) (F : (ℕ → ℕ) → ℂ)
    (hF : ∀ v, ‖F v‖ ≤ 1) :
    IsAdmissibleShortPattern L S (spanCut L S F) :=
  ⟨spanCut_norm L S F hF, spanCut_span L S F⟩

theorem truncatedPhaseTestCut_admissible (P : ℝ[X]) (B L : ℕ) (S : ℝ)
    (τ : ℤ) :
    IsAdmissibleShortPattern L S (truncatedPhaseTestCut P B L S τ) :=
  ⟨truncatedPhaseTestCut_norm P B L S τ, truncatedPhaseTestCut_span P B L S τ⟩

theorem IsAdmissibleShortPattern.norm {L : ℕ} {S : ℝ} {F : (ℕ → ℕ) → ℂ}
    (h : IsAdmissibleShortPattern L S F) (v : ℕ → ℕ) : ‖F v‖ ≤ 1 :=
  h.1 v

theorem IsAdmissibleShortPattern.span {L : ℕ} {S : ℝ} {F : (ℕ → ℕ) → ℂ}
    (h : IsAdmissibleShortPattern L S F) {v : ℕ → ℕ} (hv : S < v L) :
    F v = 0 :=
  h.2 v hv

/-! ### Independent Bernoulli configuration masses -/

/-- Homogeneous independent thinning mass on subsets of `A`. Agrees with
`bernoulliThin` / `independentDeleteMass` on `A.powerset`. -/
noncomputable def bernoulliConfigMass (A : Finset ℕ) (ρ : ℝ) (B : Finset ℕ) : ℝ :=
  if B ⊆ A then ρ ^ B.card * (1 - ρ) ^ (A.card - B.card) else 0

theorem bernoulliConfigMass_eq {A B : Finset ℕ} {ρ : ℝ} (hBA : B ⊆ A) :
    bernoulliConfigMass A ρ B = ρ ^ B.card * (1 - ρ) ^ (A.card - B.card) :=
  if_pos hBA

theorem bernoulliConfigMass_eq_thin (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (B : Finset ℕ) :
    bernoulliConfigMass A ρ B = bernoulliThin A ρ hρ0 hρ1 B := by
  unfold bernoulliConfigMass bernoulliThin
  rfl

theorem bernoulliConfigMass_eq_independent {A B : Finset ℕ} {ρ : ℝ}
    (hBA : B ⊆ A) :
    bernoulliConfigMass A ρ B = independentDeleteMass A.card ρ B.card := by
  rw [bernoulliConfigMass_eq hBA, independentDeleteMass]

theorem bernoulliConfigMass_nonneg (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (B : Finset ℕ) :
    0 ≤ bernoulliConfigMass A ρ B := by
  unfold bernoulliConfigMass
  split_ifs
  · exact mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg (sub_nonneg.mpr hρ1) _)
  · exact le_rfl

theorem bernoulliConfigMass_sum (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∑ B ∈ A.powerset, bernoulliConfigMass A ρ B = 1 := by
  have h : ∀ B ∈ A.powerset,
      bernoulliConfigMass A ρ B = bernoulliThin A ρ hρ0 hρ1 B :=
    fun B _ => bernoulliConfigMass_eq_thin A hρ0 hρ1 B
  rw [sum_congr rfl h, bernoulliThin_sum A hρ0 hρ1]

/-- Independent-Bernoulli mean of a rooted short-pattern test. -/
noncomputable def bernoulliShortPatternMean (A : Finset ℕ) (ρ S : ℝ)
    (F : (ℕ → ℕ) → ℂ) : ℂ :=
  ∑ B ∈ A.powerset, (bernoulliConfigMass A ρ B : ℂ) * F (configOffset B S)

/-- Mixture of independent-Bernoulli short-pattern means. Paper `ω_X`
applied to the comparison law, not to `nthPrime`. -/
noncomputable def mixtureBernoulliMean (m : SieveMixture) (A : Finset ℕ)
    (ρ : ℕ → ℝ) (S : ℝ) (F : (ℕ → ℕ) → ℂ) : ℂ :=
  mixtureMean m (fun y => bernoulliShortPatternMean A (ρ y) S F)

/-! ### Bounded tests are Lipschitz in discrete TV -/

theorem abs_weighted_sub_le_tvHalf {ι : Type*} (s : Finset ι)
    (μ ν : ι → ℝ) (F : ι → ℂ) (hF : ∀ i ∈ s, ‖F i‖ ≤ 1) :
    ‖∑ i ∈ s, (μ i : ℂ) * F i - ∑ i ∈ s, (ν i : ℂ) * F i‖ ≤
      2 * tvHalf s μ ν := by
  have hterm : ∀ i ∈ s,
      (μ i : ℂ) * F i - (ν i : ℂ) * F i =
        ((μ i - ν i : ℝ) : ℂ) * F i := by
    intro i _
    rw [← sub_mul, Complex.ofReal_sub]
  have hsum :
      ∑ i ∈ s, (μ i : ℂ) * F i - ∑ i ∈ s, (ν i : ℂ) * F i =
        ∑ i ∈ s, ((μ i - ν i : ℝ) : ℂ) * F i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl hterm
  rw [hsum]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hnorm :
      ‖∑ i ∈ s, ((μ i - ν i : ℝ) : ℂ) * F i‖ ≤ ∑ i ∈ s, |μ i - ν i| := by
    have hpt : ∀ i ∈ s,
        ‖((μ i - ν i : ℝ) : ℂ) * F i‖ ≤ |μ i - ν i| := by
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hF i hi
      exact mul_le_of_le_one_right (abs_nonneg _) this
    exact (norm_sum_le _ _).trans (sum_le_sum hpt)
  unfold tvHalf
  have hmul : 2 * ((∑ i ∈ s, |μ i - ν i|) / 2) = ∑ i ∈ s, |μ i - ν i| :=
    mul_div_cancel₀ _ h2
  exact hnorm.trans (le_of_eq hmul.symm)

theorem abs_configMean_sub_bernoulli_tv (A : Finset ℕ) (μ : Finset ℕ → ℝ)
    (ρ S : ℝ) (F : (ℕ → ℕ) → ℂ) (hF : ∀ v, ‖F v‖ ≤ 1) :
    ‖∑ B ∈ A.powerset, (μ B : ℂ) * F (configOffset B S) -
        bernoulliShortPatternMean A ρ S F‖ ≤
      2 * tvHalf A.powerset μ (bernoulliConfigMass A ρ) :=
  abs_weighted_sub_le_tvHalf A.powerset μ (bernoulliConfigMass A ρ)
    (fun B => F (configOffset B S)) fun _ _ => hF _

theorem abs_bernoulliShortPatternMean_sub_tv (A : Finset ℕ)
    (ρ ρ' S : ℝ) (F : (ℕ → ℕ) → ℂ) (hF : ∀ v, ‖F v‖ ≤ 1) :
    ‖bernoulliShortPatternMean A ρ S F -
        bernoulliShortPatternMean A ρ' S F‖ ≤
      2 * tvHalf A.powerset (bernoulliConfigMass A ρ)
        (bernoulliConfigMass A ρ') := by
  simpa [bernoulliShortPatternMean] using
    abs_weighted_sub_le_tvHalf A.powerset (bernoulliConfigMass A ρ)
      (bernoulliConfigMass A ρ') (fun B => F (configOffset B S))
      fun _ _ => hF _

/-! ### Categorical deletion on labelled subsets -/

/-- Categorical (at most one) deletion mass of a labelled subset `B ⊆ A`.
Matches `categoricalDeleteMass` on cardinalities. -/
noncomputable def categoricalDeleteOn (A : Finset ℕ) (q : ℝ) (B : Finset ℕ) : ℝ :=
  if B ⊆ A then
    if B.card = 0 then 1 - (A.card : ℝ) * q
    else if B.card = 1 then q
    else 0
  else
    0

theorem categoricalDeleteOn_eq_mass {A B : Finset ℕ} {q : ℝ} (hBA : B ⊆ A) :
    categoricalDeleteOn A q B = categoricalDeleteMass A.card q B.card := by
  simp [categoricalDeleteOn, categoricalDeleteMass, hBA]

theorem categoricalDeleteOn_nonneg {A : Finset ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hm : (A.card : ℝ) * q ≤ 1) (B : Finset ℕ) :
    0 ≤ categoricalDeleteOn A q B := by
  unfold categoricalDeleteOn
  split_ifs with _ h0 h1
  · exact sub_nonneg.mpr hm
  · exact hq0
  · exact le_rfl
  · exact le_rfl

/-- Labelled categorical-versus-Bernoulli TV equals the cardinality TV
from `Coupling`. -/
theorem tvHalf_categoricalDeleteOn_eq (A : Finset ℕ) (q : ℝ) :
    tvHalf A.powerset (categoricalDeleteOn A q) (bernoulliConfigMass A q)
      = categoricalVsIndependentTV A.card q := by
  unfold tvHalf categoricalVsIndependentTV
  have hB : ∀ B ∈ A.powerset,
      |categoricalDeleteOn A q B - bernoulliConfigMass A q B| =
        |categoricalDeleteMass A.card q B.card -
          independentDeleteMass A.card q B.card| := by
    intro B hB
    have hBA : B ⊆ A := mem_powerset.mp hB
    rw [categoricalDeleteOn_eq_mass hBA, bernoulliConfigMass_eq_independent hBA]
  rw [sum_congr rfl hB]
  rw [sum_powerset_apply_card (fun k =>
    |categoricalDeleteMass A.card q k - independentDeleteMass A.card q k|)]
  simp [nsmul_eq_mul]

theorem tvHalf_categoricalDeleteOn_le {A : Finset ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    tvHalf A.powerset (categoricalDeleteOn A q) (bernoulliConfigMass A q)
      ≤ (A.card : ℝ) * (A.card - 1 : ℕ) * q ^ 2 := by
  rw [tvHalf_categoricalDeleteOn_eq]
  simpa [categoricalVsIndependentTV] using categorical_tv_le hq0 hq1 A.card

/-! ### Remaining-prime coupling budget (paper (eq:coupling)) -/

/-- Sum of per-prime categorical-versus-independent TVs on `|A|`
candidates, over primes in `(z, y]`. Paper (eq:coupling) before the
`S²/z₀` comparison. -/
noncomputable def remainingPrimeCouplingTV (A : Finset ℕ) (z y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE y \ Nat.primesLE z,
    categoricalVsIndependentTV A.card (palmHitProb p)

theorem remainingPrimeCouplingTV_nonneg (A : Finset ℕ) (z y : ℕ) :
    0 ≤ remainingPrimeCouplingTV A z y :=
  sum_nonneg fun _ _ => by
    unfold categoricalVsIndependentTV
    exact div_nonneg
      (sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      (by norm_num)

private theorem one_lt_of_two_le {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) < n :=
  Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : 1 < 2) hn)

/-- `1/n² ≤ 1/(n-1) - 1/n` for `n ≥ 2`. Unique name: `ResidueMcDiarmid`
already declares `inv_sq_le_inv_pred_sub` in this namespace. -/
theorem modelShort_inv_sq_le_inv_pred_sub {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / n := by
  have hnR : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hpred : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hprod : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hpred
  have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hn0
  have hle : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by
    have : (n : ℝ) - 1 ≤ n := by linarith
    have hmul := mul_le_mul_of_nonneg_left this hnpos.le
    have hnn : (n : ℝ) * n = (n : ℝ) ^ 2 := by ring
    rwa [hnn] at hmul
  have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ ((n : ℝ) * ((n : ℝ) - 1))⁻¹ :=
    (inv_le_inv₀ hsq hprod).mpr hle
  have hleft : (1 : ℝ) / (n : ℝ) ^ 2 = ((n : ℝ) ^ 2)⁻¹ := one_div _
  have hmid : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
      ((n : ℝ) * ((n : ℝ) - 1))⁻¹ := one_div _
  have hsplit : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) =
      1 / ((n : ℝ) - 1) - 1 / n := by
    field_simp [hn0, hn1]
    ring
  rw [hleft]
  exact hinv.trans (hmid.symm.trans hsplit).le

private theorem sum_inv_pred_sub_telescope {z M : ℕ} (_hz : 2 ≤ z)
    (hM : z ≤ M) :
    ∑ n ∈ Icc z M, (1 / ((n : ℝ) - 1) - 1 / n) =
      1 / ((z : ℝ) - 1) - 1 / M := by
  refine Nat.le_induction ?base ?step M hM
  · simp [Icc_self]
  · intro M hM ih
    have hinsert : Icc z (M + 1) = insert (M + 1) (Icc z M) :=
      (insert_Icc_right_eq_Icc_add_one (show z ≤ M + 1 by omega)).symm
    have hnot : M + 1 ∉ Icc z M := by
      simp [mem_Icc]
    rw [hinsert, sum_insert hnot, ih]
    have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := Nat.cast_succ M
    rw [hcast]
    have hpred : (M : ℝ) + 1 - 1 = M := by ring
    rw [hpred]
    ring

/-- Harmonic comparison `∑_{n=z}^{M} 1/n² ≤ 1/(z-1)`. -/
theorem sum_inv_sq_Icc_le {z M : ℕ} (hz : 2 ≤ z) :
    ∑ n ∈ Icc z M, (1 : ℝ) / n ^ 2 ≤ 1 / ((z : ℝ) - 1) := by
  by_cases hM : z ≤ M
  · have hpt : ∀ n ∈ Icc z M,
        (1 : ℝ) / n ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / n := by
      intro n hn
      have hn' : 2 ≤ n := le_trans hz (mem_Icc.mp hn).1
      exact modelShort_inv_sq_le_inv_pred_sub hn'
    have hsum := sum_le_sum hpt
    have htele := sum_inv_pred_sub_telescope hz hM
    have htail : 0 ≤ (1 : ℝ) / M := div_nonneg zero_le_one (Nat.cast_nonneg _)
    exact hsum.trans (htele.trans_le (sub_le_self _ htail))
  · have hempty : Icc z M = ∅ := Finset.Icc_eq_empty_iff.mpr hM
    rw [hempty, sum_empty]
    have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by
      have : (1 : ℝ) < z := one_lt_of_two_le hz
      linarith
    exact div_nonneg zero_le_one hz1.le

private theorem mem_pred_Icc_of_mem_sdiff {z y p : ℕ}
    (hp : p ∈ Nat.primesLE y \ Nat.primesLE z) :
    p - 1 ∈ Icc z (y - 1) := by
  have hpY : p ∈ Nat.primesLE y := sdiff_subset hp
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE hpY
  have hle : p ≤ y := (Nat.mem_primesLE.mp hpY).1
  have hnot : p ∉ Nat.primesLE z := (mem_sdiff.mp hp).2
  have hgt : z < p := Nat.not_le.mp fun hle' =>
    hnot (Nat.mem_primesLE.mpr ⟨hle', hp'⟩)
  exact mem_Icc.mpr ⟨Nat.le_pred_of_lt hgt, Nat.sub_le_sub_right hle 1⟩

theorem palmHitProb_sq_eq {p : ℕ} (hp : 2 ≤ p) :
    palmHitProb p ^ 2 = (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
  have hden : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := one_lt_of_two_le hp
    linarith
  simp only [palmHitProb, hcast]
  field_simp [hden]

theorem sum_palmHitProb_sq_le {z y : ℕ} (_hz : 2 ≤ z) :
    ∑ p ∈ Nat.primesLE y \ Nat.primesLE z, palmHitProb p ^ 2
      ≤ ∑ n ∈ Icc z (y - 1), (1 : ℝ) / n ^ 2 := by
  let s := Nat.primesLE y \ Nat.primesLE z
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (s : Set ℕ) := by
    intro a ha b hb h
    have ha2 : 2 ≤ a :=
      (Nat.prime_of_mem_primesLE (sdiff_subset ha)).two_le
    have hb2 : 2 ≤ b :=
      (Nat.prime_of_mem_primesLE (sdiff_subset hb)).two_le
    have ha1 : 1 ≤ a := le_trans (by decide : 1 ≤ 2) ha2
    have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb2
    rw [← Nat.sub_add_cancel ha1, ← Nat.sub_add_cancel hb1]
    exact congrArg (fun n => n + 1) h
  have hpt : ∀ p ∈ s,
      palmHitProb p ^ 2 = (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
    intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    exact palmHitProb_sq_eq hp'.two_le
  let g : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2
  have hsum :
      ∑ p ∈ s, palmHitProb p ^ 2 =
        ∑ n ∈ s.image (fun p : ℕ => p - 1), g n := by
    have hpt' : ∀ p ∈ s, (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ^ 2 = g (p - 1) :=
      fun _ _ => rfl
    rw [sum_congr rfl hpt, sum_congr rfl hpt']
    exact (sum_image hinj).symm
  have hsub : s.image (fun p : ℕ => p - 1) ⊆ Icc z (y - 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact mem_pred_Icc_of_mem_sdiff hp
  have hnn : ∀ n ∈ Icc z (y - 1), 0 ≤ g n := fun n _ =>
    div_nonneg zero_le_one (sq_nonneg _)
  rw [hsum]
  exact sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnn n hn

/-- Coupling budget: `∑_p TV_p ≤ |A|(|A|-1) ∑ (p-1)^{-2}`. -/
theorem remainingPrimeCouplingTV_le (A : Finset ℕ) {z y : ℕ} (hz : 2 ≤ z) :
    remainingPrimeCouplingTV A z y
      ≤ (A.card : ℝ) * (A.card - 1 : ℕ) *
          ∑ n ∈ Icc z (y - 1), (1 : ℝ) / n ^ 2 := by
  unfold remainingPrimeCouplingTV
  let s := Nat.primesLE y \ Nat.primesLE z
  have hq0 : ∀ p ∈ s, 0 ≤ palmHitProb p := fun p hp =>
    palmHitProb_nonneg (Nat.prime_of_mem_primesLE (sdiff_subset hp)).two_le
  have hq1 : ∀ p ∈ s, palmHitProb p ≤ 1 := fun p hp =>
    palmHitProb_le_one (Nat.prime_of_mem_primesLE (sdiff_subset hp)).two_le
  have hsum := sum_categorical_tv_le s A.card hq0 hq1
  have hsq := sum_palmHitProb_sq_le (z := z) (y := y) hz
  have hnn : 0 ≤ (A.card : ℝ) * (A.card - 1 : ℕ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfactor :
      ∑ p ∈ s, (A.card : ℝ) * (A.card - 1 : ℕ) * palmHitProb p ^ 2 =
        (A.card : ℝ) * (A.card - 1 : ℕ) * ∑ p ∈ s, palmHitProb p ^ 2 :=
    (mul_sum s (fun p => palmHitProb p ^ 2)
      ((A.card : ℝ) * (A.card - 1 : ℕ))).symm
  have hmul := mul_le_mul_of_nonneg_left hsq hnn
  exact hsum.trans (hfactor.trans_le hmul)

theorem card_mul_pred_le_sq (m : ℕ) :
    (m : ℝ) * (m - 1 : ℕ) ≤ (m : ℝ) ^ 2 := by
  have hle : (m - 1 : ℕ) ≤ m := Nat.sub_le _ _
  have h1 : ((m - 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr hle
  have := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg m)
  have hsq : (m : ℝ) * m = m ^ 2 := by ring
  rwa [hsq] at this

theorem card_le_of_subset_Icc {A : Finset ℕ} {S : ℕ} (hA : A ⊆ Icc 1 S) :
    A.card ≤ S := by
  have := card_le_card hA
  have hcard : (Icc 1 S).card = S := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  rwa [hcard] at this

/-- Paper `≪ S² / z₀`: finite form `≤ S² / (z-1)` on `A ⊆ [1,S]`. -/
theorem remainingPrimeCouplingTV_le_sq {A : Finset ℕ} {z y S : ℕ}
    (hA : A ⊆ Icc 1 S) (hz : 2 ≤ z) :
    remainingPrimeCouplingTV A z y ≤ (S : ℝ) ^ 2 / ((z : ℝ) - 1) := by
  have hmain := remainingPrimeCouplingTV_le (A := A) (z := z) (y := y) hz
  have hsq := sum_inv_sq_Icc_le (z := z) (M := y - 1) hz
  have hnn : 0 ≤ (A.card : ℝ) * (A.card - 1 : ℕ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hsq hnn
  have hbound := hmain.trans h1
  have hcard : (A.card : ℝ) * (A.card - 1 : ℕ) ≤ (S : ℝ) ^ 2 := by
    have hm := card_mul_pred_le_sq A.card
    have hAS : (A.card : ℝ) ≤ S := Nat.cast_le.mpr (card_le_of_subset_Icc hA)
    have hsqA : (A.card : ℝ) ^ 2 ≤ (S : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hAS 2
    exact hm.trans hsqA
  have hz1 : (0 : ℝ) < (z : ℝ) - 1 := by
    have : (1 : ℝ) < z := one_lt_of_two_le hz
    linarith
  have hden : 0 ≤ 1 / ((z : ℝ) - 1) := div_nonneg zero_le_one hz1.le
  have hscale :
      (A.card : ℝ) * (A.card - 1 : ℕ) * (1 / ((z : ℝ) - 1)) ≤
        (S : ℝ) ^ 2 * (1 / ((z : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_right hcard hden
  have hrew :
      (S : ℝ) ^ 2 * (1 / ((z : ℝ) - 1)) = (S : ℝ) ^ 2 / ((z : ℝ) - 1) := by
    field_simp [hz1.ne']
  exact hbound.trans (hscale.trans (le_of_eq hrew))

/-! ### Named discrepancy hypotheses (not axioms) -/

/-- Config-mass TV against independent Bernoulli thinning is at most `δ`.
Named hypothesis, not an `axiom`. -/
def BernoulliDiscrepancy (A : Finset ℕ) (μ : Finset ℕ → ℝ) (ρ δ : ℝ) : Prop :=
  0 ≤ δ ∧ tvHalf A.powerset μ (bernoulliConfigMass A ρ) ≤ δ

/-- Paper coupling comparison: survivor TV is at most the summed
categorical-versus-independent TVs of the remaining primes. -/
def CouplingDiscrepancy (A : Finset ℕ) (μ : Finset ℕ → ℝ) (z y : ℕ) : Prop :=
  BernoulliDiscrepancy A μ (rootedEulerProdNat z y)
    (remainingPrimeCouplingTV A z y)

/-- Rooted sieve mean versus independent Bernoulli mean, uniformly over
admissible short-pattern tests. Named hypothesis, not an `axiom`. -/
def RootedSieveVsBernoulli (y : ℕ) (A : Finset ℕ) (ρ : ℝ) (L : ℕ) (S δ : ℝ) :
    Prop :=
  0 ≤ δ ∧
    ∀ F : (ℕ → ℕ) → ℂ, IsAdmissibleShortPattern L S F →
      ‖rootedSieveMean y F - bernoulliShortPatternMean A ρ S F‖ ≤ δ

/-- Mixture of rooted-sieve means versus mixture of Bernoulli means. -/
def MixtureVsBernoulli (ω : SieveMixture) (A : Finset ℕ) (ρ : ℕ → ℝ)
    (L : ℕ) (S δ : ℝ) : Prop :=
  0 ≤ δ ∧
    ∀ F : (ℕ → ℕ) → ℂ, IsAdmissibleShortPattern L S F →
      ‖mixtureMean ω (fun y => rootedSieveMean y F) -
          mixtureBernoulliMean ω A ρ S F‖ ≤ δ

theorem remainingPrimeCouplingTV_eq_tvHalf_sum (A : Finset ℕ) (z y : ℕ) :
    remainingPrimeCouplingTV A z y =
      ∑ p ∈ Nat.primesLE y \ Nat.primesLE z,
        tvHalf A.powerset (categoricalDeleteOn A (palmHitProb p))
          (bernoulliConfigMass A (palmHitProb p)) := by
  unfold remainingPrimeCouplingTV
  refine sum_congr rfl fun p _ => (tvHalf_categoricalDeleteOn_eq A _).symm

theorem abs_configMean_sub_bernoulli_of_discrepancy
    {A : Finset ℕ} {μ : Finset ℕ → ℝ} {ρ S δ : ℝ} {F : (ℕ → ℕ) → ℂ}
    (hF : ∀ v, ‖F v‖ ≤ 1) (hδ : BernoulliDiscrepancy A μ ρ δ) :
    ‖∑ B ∈ A.powerset, (μ B : ℂ) * F (configOffset B S) -
        bernoulliShortPatternMean A ρ S F‖ ≤ 2 * δ := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  exact (abs_configMean_sub_bernoulli_tv A μ ρ S F hF).trans
    (mul_le_mul_of_nonneg_left hδ.2 h2)

theorem abs_configMean_sub_bernoulli_of_coupling
    {A : Finset ℕ} {μ : Finset ℕ → ℝ} {z y : ℕ} {S : ℝ} {F : (ℕ → ℕ) → ℂ}
    (hF : ∀ v, ‖F v‖ ≤ 1) (hC : CouplingDiscrepancy A μ z y) :
    ‖∑ B ∈ A.powerset, (μ B : ℂ) * F (configOffset B S) -
        bernoulliShortPatternMean A (rootedEulerProdNat z y) S F‖ ≤
      2 * remainingPrimeCouplingTV A z y :=
  abs_configMean_sub_bernoulli_of_discrepancy hF hC

theorem abs_configMean_sub_bernoulli_admissible
    {A : Finset ℕ} {μ : Finset ℕ → ℝ} {ρ S δ : ℝ} {L : ℕ}
    {F : (ℕ → ℕ) → ℂ} (hF : IsAdmissibleShortPattern L S F)
    (hδ : BernoulliDiscrepancy A μ ρ δ) :
    ‖∑ B ∈ A.powerset, (μ B : ℂ) * F (configOffset B S) -
        bernoulliShortPatternMean A ρ S F‖ ≤ 2 * δ :=
  abs_configMean_sub_bernoulli_of_discrepancy (fun v => hF.norm v) hδ

/-- Admissible tests vanish on configurations with fewer than `L` points. -/
theorem admissible_eq_zero_of_card_lt {U : Finset ℕ} {L : ℕ} {S : ℝ}
    {F : (ℕ → ℕ) → ℂ} (hF : IsAdmissibleShortPattern L S F)
    (hL : 1 ≤ L) (hcard : U.card < L) :
    F (configOffset U S) = 0 :=
  hF.span (lt_configOffset_of_card_lt hL hcard)

/-! ### Mixture Lipschitz and pointwise coupling -/

theorem abs_mixtureMean_sub_le (m : SieveMixture) (μ ν : ℕ → ℂ)
    (δ : ℕ → ℝ) (_hδ : ∀ y ∈ m.support, 0 ≤ δ y)
    (h : ∀ y ∈ m.support, ‖μ y - ν y‖ ≤ δ y) :
    ‖mixtureMean m μ - mixtureMean m ν‖ ≤
      ∑ y ∈ m.support, m.weight y * δ y := by
  unfold mixtureMean
  have hterm : ∀ y ∈ m.support,
      (m.weight y : ℂ) * μ y - (m.weight y : ℂ) * ν y =
        (m.weight y : ℂ) * (μ y - ν y) := fun y _ => by
    rw [← mul_sub]
  have hsum :
      ∑ y ∈ m.support, (m.weight y : ℂ) * μ y -
          ∑ y ∈ m.support, (m.weight y : ℂ) * ν y =
        ∑ y ∈ m.support, (m.weight y : ℂ) * (μ y - ν y) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl hterm
  rw [hsum]
  have hpt : ∀ y ∈ m.support,
      ‖(m.weight y : ℂ) * (μ y - ν y)‖ ≤ m.weight y * δ y := by
    intro y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (m.weight_nonneg y hy)]
    exact mul_le_mul_of_nonneg_left (h y hy) (m.weight_nonneg y hy)
  exact (norm_sum_le _ _).trans (sum_le_sum hpt)

theorem abs_mixtureMean_sub_const (m : SieveMixture) (μ ν : ℕ → ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ y ∈ m.support, ‖μ y - ν y‖ ≤ δ) :
    ‖mixtureMean m μ - mixtureMean m ν‖ ≤ δ := by
  have hpt : ∀ y ∈ m.support, ‖μ y - ν y‖ ≤ δ := h
  have hδy : ∀ y ∈ m.support, 0 ≤ δ := fun _ _ => hδ
  have hsum := abs_mixtureMean_sub_le m μ ν (fun _ => δ) hδy hpt
  have hrew :
      ∑ y ∈ m.support, m.weight y * δ = δ := by
    rw [← sum_mul, m.weight_sum, one_mul]
  rwa [hrew] at hsum

theorem mixtureVsBernoulli_of_pointwise
    (ω : SieveMixture) (A : Finset ℕ) (ρ : ℕ → ℝ) (L : ℕ) (S δ : ℝ)
    (h : ∀ y ∈ ω.support, RootedSieveVsBernoulli y A (ρ y) L S δ) :
    MixtureVsBernoulli ω A ρ L S δ := by
  obtain ⟨y0, hy0⟩ := ω.support_nonempty
  refine ⟨(h y0 hy0).1, fun F hF => ?_⟩
  have hpt : ∀ y ∈ ω.support,
      ‖rootedSieveMean y F - bernoulliShortPatternMean A (ρ y) S F‖ ≤ δ :=
    fun y hy => (h y hy).2 F hF
  simpa [mixtureBernoulliMean] using
    abs_mixtureMean_sub_const ω (fun y => rootedSieveMean y F)
      (fun y => bernoulliShortPatternMean A (ρ y) S F) (h y0 hy0).1 hpt

/-- Unpack `MixtureVsBernoulli` at an admissible test. -/
theorem abs_mixtureMean_sub_mixtureBernoulli
    {ω : SieveMixture} {A : Finset ℕ} {ρ : ℕ → ℝ} {L : ℕ} {S δ : ℝ}
    {F : (ℕ → ℕ) → ℂ} (hF : IsAdmissibleShortPattern L S F)
    (h : MixtureVsBernoulli ω A ρ L S δ) :
    ‖mixtureMean ω (fun y => rootedSieveMean y F) -
        mixtureBernoulliMean ω A ρ S F‖ ≤ δ :=
  h.2 F hF

/-- Mixture of labelled config means versus the independent-Bernoulli
mixture, uniformly from a discrepancy hypothesis. -/
theorem abs_mixture_configMean_sub_bernoulli
    (ω : SieveMixture) (A : Finset ℕ) (μ : ℕ → Finset ℕ → ℝ) (ρ : ℕ → ℝ)
    {S δ : ℝ} (F : (ℕ → ℕ) → ℂ)
    (hF : ∀ v, ‖F v‖ ≤ 1) (hδ : 0 ≤ δ)
    (h : ∀ y ∈ ω.support, BernoulliDiscrepancy A (μ y) (ρ y) δ) :
    ‖mixtureMean ω (fun y =>
          ∑ B ∈ A.powerset, (μ y B : ℂ) * F (configOffset B S)) -
        mixtureBernoulliMean ω A ρ S F‖ ≤ 2 * δ := by
  have h2 : (0 : ℝ) ≤ 2 * δ := mul_nonneg (by norm_num) hδ
  have hpt : ∀ y ∈ ω.support,
      ‖∑ B ∈ A.powerset, (μ y B : ℂ) * F (configOffset B S) -
          bernoulliShortPatternMean A (ρ y) S F‖ ≤ 2 * δ :=
    fun y hy => abs_configMean_sub_bernoulli_of_discrepancy hF (h y hy)
  simpa [mixtureBernoulliMean] using
    abs_mixtureMean_sub_const ω
      (fun y => ∑ B ∈ A.powerset, (μ y B : ℂ) * F (configOffset B S))
      (fun y => bernoulliShortPatternMean A (ρ y) S F) h2 hpt

/-- Same comparison with the Coupling remaining-prime TV budget. -/
theorem abs_mixture_configMean_sub_bernoulli_of_coupling
    (ω : SieveMixture) (A : Finset ℕ) (μ : ℕ → Finset ℕ → ℝ)
    (z y : ℕ) {S : ℝ} (F : (ℕ → ℕ) → ℂ)
    (hF : ∀ v, ‖F v‖ ≤ 1)
    (hC : ∀ y' ∈ ω.support, CouplingDiscrepancy A (μ y') z y) :
    ‖mixtureMean ω (fun y' =>
          ∑ B ∈ A.powerset, (μ y' B : ℂ) * F (configOffset B S)) -
        mixtureBernoulliMean ω A (fun _ => rootedEulerProdNat z y) S F‖ ≤
      2 * remainingPrimeCouplingTV A z y := by
  have hδ0 := remainingPrimeCouplingTV_nonneg A z y
  have h2 : (0 : ℝ) ≤ 2 * remainingPrimeCouplingTV A z y :=
    mul_nonneg (by norm_num) hδ0
  have hpt : ∀ y' ∈ ω.support,
      ‖∑ B ∈ A.powerset, (μ y' B : ℂ) * F (configOffset B S) -
          bernoulliShortPatternMean A (rootedEulerProdNat z y) S F‖ ≤
        2 * remainingPrimeCouplingTV A z y :=
    fun y' hy' => abs_configMean_sub_bernoulli_of_coupling hF (hC y' hy')
  simpa [mixtureBernoulliMean] using
    abs_mixtureMean_sub_const ω
      (fun y' => ∑ B ∈ A.powerset, (μ y' B : ℂ) * F (configOffset B S))
      (fun y' => bernoulliShortPatternMean A (rootedEulerProdNat z y) S F)
      h2 hpt

/-- Cardinality-weighted categorical deletion masses sum to one. -/
theorem categoricalDeleteMass_weighted_sum (m : ℕ) (q : ℝ) :
    ∑ k ∈ range (m + 1), (m.choose k : ℝ) * categoricalDeleteMass m q k = 1 := by
  by_cases hm : m = 0
  · subst hm
    simp [categoricalDeleteMass, range_one]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have h01 := pair_zero_one_subset_range hmpos
    have hrest :
        ∑ k ∈ range (m + 1) \ {0, 1},
            (m.choose k : ℝ) * categoricalDeleteMass m q k = 0 := by
      refine sum_eq_zero fun k hk => ?_
      have hk2 : 2 ≤ k := mem_two_of_mem_sdiff_zero_one hk
      rw [categoricalDeleteMass_of_two_le m q hk2, mul_zero]
    have hpair :
        ∑ k ∈ ({0, 1} : Finset ℕ),
            (m.choose k : ℝ) * categoricalDeleteMass m q k = 1 := by
      rw [sum_pair (by decide : (0 : ℕ) ≠ 1), Nat.choose_zero_right,
        Nat.choose_one_right, categoricalDeleteMass_zero, categoricalDeleteMass_one]
      ring
    have hsplit :=
      (sum_sdiff h01 :
        ∑ k ∈ range (m + 1) \ {0, 1},
            (m.choose k : ℝ) * categoricalDeleteMass m q k +
          ∑ k ∈ ({0, 1} : Finset ℕ),
            (m.choose k : ℝ) * categoricalDeleteMass m q k =
          ∑ k ∈ range (m + 1),
            (m.choose k : ℝ) * categoricalDeleteMass m q k)
    linarith [hsplit, hrest, hpair]

theorem categoricalDeleteOn_sum (A : Finset ℕ) (q : ℝ) :
    ∑ B ∈ A.powerset, categoricalDeleteOn A q B = 1 := by
  have hB : ∀ B ∈ A.powerset,
      categoricalDeleteOn A q B = categoricalDeleteMass A.card q B.card :=
    fun B hB => categoricalDeleteOn_eq_mass (mem_powerset.mp hB)
  rw [sum_congr rfl hB]
  rw [sum_powerset_apply_card (fun k => categoricalDeleteMass A.card q k)]
  simpa [nsmul_eq_mul] using categoricalDeleteMass_weighted_sum A.card q

/-- Two-factor product TV, specialised to labelled categorical versus
Bernoulli deletion. The general remaining-prime product is recorded as
`CouplingDiscrepancy`. -/
theorem tvHalf_two_prime_le {A : Finset ℕ} {q1 q2 : ℝ}
    (hq10 : 0 ≤ q1) (hq11 : q1 ≤ 1) (hq20 : 0 ≤ q2) (_hq21 : q2 ≤ 1)
    (_hm1 : (A.card : ℝ) * q1 ≤ 1) (hm2 : (A.card : ℝ) * q2 ≤ 1) :
    tvHalf (A.powerset ×ˢ A.powerset)
        (fun p => categoricalDeleteOn A q1 p.1 * categoricalDeleteOn A q2 p.2)
        (fun p => bernoulliConfigMass A q1 p.1 * bernoulliConfigMass A q2 p.2)
      ≤ tvHalf A.powerset (categoricalDeleteOn A q1) (bernoulliConfigMass A q1) +
          tvHalf A.powerset (categoricalDeleteOn A q2)
            (bernoulliConfigMass A q2) := by
  have hν0 : ∀ B ∈ A.powerset, 0 ≤ categoricalDeleteOn A q2 B := fun B _ =>
    categoricalDeleteOn_nonneg hq20 hm2 B
  have hμ'0 : ∀ B ∈ A.powerset, 0 ≤ bernoulliConfigMass A q1 B := fun B _ =>
    bernoulliConfigMass_nonneg A hq10 hq11 B
  have hν1 : ∑ B ∈ A.powerset, categoricalDeleteOn A q2 B = 1 :=
    categoricalDeleteOn_sum A q2
  have hμ'1 : ∑ B ∈ A.powerset, bernoulliConfigMass A q1 B = 1 :=
    bernoulliConfigMass_sum A hq10 hq11
  exact tvHalf_mul_le A.powerset A.powerset
    (categoricalDeleteOn A q1) (bernoulliConfigMass A q1)
    (categoricalDeleteOn A q2) (bernoulliConfigMass A q2)
    hν0 hμ'0 hν1 hμ'1

/-! ### Window average versus mixture (hypotheses, not `ShortPatternS`) -/

/-- Triangle glue: a transfer bound plus a model-versus-mixture bound
yield the short-pattern comparison at one scale. The hypotheses may come
from `StoppedPrime` L¹ control and `MixtureVsBernoulli`; this does
**not** prove `ShortPatternS nthPrime`. -/
theorem windowAvg_sub_mixtureMean_le {a : ℕ → ℕ} {X : ℕ}
    (ω : SieveMixture) (F : (ℕ → ℕ) → ℂ) (model : ℂ) {ε1 ε2 : ℝ}
    (h1 : ‖windowAvg (seqWindow a X)
            (fun n => F (fun k => seqOffset a n k)) - model‖ ≤ ε1)
    (h2 : ‖model - mixtureMean ω (fun y => rootedSieveMean y F)‖ ≤ ε2) :
    ‖windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
        mixtureMean ω (fun y => rootedSieveMean y F)‖ ≤ ε1 + ε2 := by
  set actual :=
    windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k))
  set mix := mixtureMean ω (fun y => rootedSieveMean y F)
  have hdecomp : (actual - model) + (model - mix) = actual - mix := by
    ring
  have htri : ‖actual - mix‖ ≤ ‖actual - model‖ + ‖model - mix‖ := by
    rw [← hdecomp]
    exact norm_add_le _ _
  exact htri.trans (add_le_add h1 h2)

/-- Same glue with the Bernoulli mixture as the comparison law. -/
theorem windowAvg_sub_mixtureBernoulliMean_le {a : ℕ → ℕ} {X : ℕ}
    (ω : SieveMixture) (A : Finset ℕ) (ρ : ℕ → ℝ) (S : ℝ)
    (F : (ℕ → ℕ) → ℂ) (model : ℂ) {ε1 ε2 : ℝ}
    (h1 : ‖windowAvg (seqWindow a X)
            (fun n => F (fun k => seqOffset a n k)) - model‖ ≤ ε1)
    (h2 : ‖model - mixtureBernoulliMean ω A ρ S F‖ ≤ ε2) :
    ‖windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
        mixtureBernoulliMean ω A ρ S F‖ ≤ ε1 + ε2 := by
  set actual :=
    windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k))
  set mix := mixtureBernoulliMean ω A ρ S F
  have hdecomp : (actual - model) + (model - mix) = actual - mix := by
    ring
  have htri : ‖actual - mix‖ ≤ ‖actual - model‖ + ‖model - mix‖ := by
    rw [← hdecomp]
    exact norm_add_le _ _
  exact htri.trans (add_le_add h1 h2)

/-- If the StoppedPrime-scale L¹ transfer is `≤ ε1` and the model is
within `ε2` of the sieve mixture, the actual window mean is within
`ε1+ε2` of that mixture. Still a hypothesis theorem: no claim that
`ShortPatternS` holds for `nthPrime`. -/
theorem actual_window_close_to_mixture
    {a : ℕ → ℕ} {X : ℕ} {ω : SieveMixture} {L : ℕ} {S ε1 ε2 : ℝ}
    (F : (ℕ → ℕ) → ℂ) (model : ℂ)
    (_hF : IsAdmissibleShortPattern L S F)
    (h1 : ‖windowAvg (seqWindow a X)
            (fun n => F (fun k => seqOffset a n k)) - model‖ ≤ ε1)
    (h2 : ‖model - mixtureMean ω (fun y => rootedSieveMean y F)‖ ≤ ε2) :
    ‖windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
        mixtureMean ω (fun y => rootedSieveMean y F)‖ ≤ ε1 + ε2 :=
  windowAvg_sub_mixtureMean_le ω F model h1 h2

theorem actual_window_close_to_mixture_of
    {a : ℕ → ℕ} {X : ℕ} {ω : SieveMixture} {A : Finset ℕ}
    {ρ : ℕ → ℝ} {L : ℕ} {S ε1 ε2 : ℝ} (F : (ℕ → ℕ) → ℂ)
    (hF : IsAdmissibleShortPattern L S F)
    (hStopped : ‖windowAvg (seqWindow a X)
          (fun n => F (fun k => seqOffset a n k)) -
        mixtureBernoulliMean ω A ρ S F‖ ≤ ε1)
    (hModel : MixtureVsBernoulli ω A ρ L S ε2) :
    ‖windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
        mixtureMean ω (fun y => rootedSieveMean y F)‖ ≤ ε1 + ε2 := by
  have hmix := hModel.2 F hF
  have hdecomp :
      windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
          mixtureMean ω (fun y => rootedSieveMean y F) =
        (windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
            mixtureBernoulliMean ω A ρ S F) +
          (mixtureBernoulliMean ω A ρ S F -
            mixtureMean ω (fun y => rootedSieveMean y F)) := by
    ring
  have htri := norm_add_le
    (windowAvg (seqWindow a X) (fun n => F (fun k => seqOffset a n k)) -
      mixtureBernoulliMean ω A ρ S F)
    (mixtureBernoulliMean ω A ρ S F -
      mixtureMean ω (fun y => rootedSieveMean y F))
  have hrev : ‖mixtureBernoulliMean ω A ρ S F -
        mixtureMean ω (fun y => rootedSieveMean y F)‖ =
      ‖mixtureMean ω (fun y => rootedSieveMean y F) -
        mixtureBernoulliMean ω A ρ S F‖ :=
    norm_sub_rev _ _
  rw [hdecomp]
  exact htri.trans (add_le_add hStopped (hrev.trans_le hmix))

/-- Retention `ϑ_y = ∏_{z < p ≤ y} (1-1/(p-1))` lies in `(0,1]`. -/
theorem rootedEulerProdNat_le_one {z y : ℕ} (hz : 2 ≤ z) :
    rootedEulerProdNat z y ≤ 1 := by
  refine prod_le_one ?h0 ?h1
  · intro p hp
    have hp3 : 3 ≤ p := by
      have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
      have hnotin : p ∉ Nat.primesLE z := (mem_sdiff.mp hp).2
      have : ¬ p ≤ z := fun hle => hnotin (Nat.mem_primesLE.mpr ⟨hle, hp'⟩)
      omega
    have hp3R : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    have : (1 : ℝ) < p - 1 := by linarith
    have : ((p : ℝ) - 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  · intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE (sdiff_subset hp)
    have hp2 : 2 ≤ p := hp'.two_le
    have hp2R : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp2
    have hden : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    exact sub_le_self _ (inv_nonneg.mpr hden)

end PrimeGapNormality.Prime

