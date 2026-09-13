import PrimeGapNormality.Prime.CoreFiniteOrbitDiscrepancy
import PrimeGapNormality.Prime.CoreSequenceResiduePassage
import PrimeGapNormality.Prime.CoreCircleDigitCylinders
import PrimeGapNormality.Prime.ChebyshevNthPrime
import PrimeGapNormality.Prime.PrimeSTD
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform physical blocks to actual prefix star discrepancy

The finite proof is the integer-halving construction of PhysicalWindowST,
with a logarithmic rounding count exposed quantitatively. No geometric
partition of sequence indices is substituted for prime-value windows.
-/

namespace PrimeGapNormality.Prime.CorePrimeGlobalDiscrepancy
open Finset Filter MeasureTheory
open CoreFiniteOrbitDiscrepancy CoreCircleIntervalRamps CoreFiniteOrbitBoundary
open scoped Classical Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem abs_sum_le_card (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) :
    |∑ n ∈ s, f n| ≤ (s.card : ℝ) := by
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun n _ => hf n).trans_eq (by simp))

private theorem halve_drop_card {a : ℕ → ℕ} (ha : StrictMono a) (b : ℕ) :
    (Ico (seqCount a (2 * (b / 2))) (seqCount a b)).card ≤ 1 := by
  apply card_le_one.2
  intro n hn m hm
  have hnb := (seqCount_lt_iff ha).1 (mem_Ico.1 hn).2
  have hmb := (seqCount_lt_iff ha).1 (mem_Ico.1 hm).2
  have hnl : 2 * (b / 2) < a n := by
    by_contra hh
    have hh' := (seqCount_lt_iff ha).2 (Nat.not_lt.mp hh)
    exact (not_lt_of_ge (mem_Ico.1 hn).1) hh'
  have hml : 2 * (b / 2) < a m := by
    by_contra hh
    have hh' := (seqCount_lt_iff ha).2 (Nat.not_lt.mp hh)
    exact (not_lt_of_ge (mem_Ico.1 hm).1) hh'
  have hmod := Nat.div_add_mod b 2
  have hmodlt := Nat.mod_lt b (by norm_num : 0 < 2)
  have hnval : a n = b := by omega
  have hmval : a m = b := by omega
  exact ha.injective (hnval.trans hmval.symm)

private theorem prefix_split (f : ℕ → ℝ) {n₀ n₁ n₂ : ℕ}
    (h01 : n₀ ≤ n₁) (h12 : n₁ ≤ n₂) :
    (∑ n ∈ range n₂, f n) = (∑ n ∈ range n₀, f n) +
      (∑ n ∈ Ico n₀ n₁, f n) + (∑ n ∈ Ico n₁ n₂, f n) := by
  calc
    _ = (∑ n ∈ range n₁, f n) + ∑ n ∈ Ico n₁ n₂, f n :=
      (sum_range_add_sum_Ico f h12).symm
    _ = _ := by rw [← sum_range_add_sum_Ico f h01]

/-- Quantitative integer-halving inequality, uniform for any bounded
centered test. Only retained physical windows X0≤X≤b are used. -/
theorem abs_prefix_sum_le_of_blocks {a : ℕ → ℕ} (ha : StrictMono a)
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    {X₀ : ℕ} (hX₀ : 1 ≤ X₀) (b : ℕ)
    (hblock : ∀ X, X₀ ≤ X → X ≤ b →
      |∑ n ∈ seqWindow a X, f n| ≤ δ * ((seqWindow a X).card : ℝ)) :
    |∑ n ∈ range (seqCount a b), f n| ≤
      δ * (seqCount a b : ℝ) + (seqCount a (2 * X₀) : ℝ) + (Nat.log 2 b + 1 : ℕ) := by
  revert hblock
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro hblock
    by_cases hstop : b / 2 < X₀
    · have hb : b < 2 * X₀ := by omega
      have hcount := Nat.cast_le (α := ℝ).2 (seqCount_mono (a := a) hb.le)
      have hraw := abs_sum_le_card (range (seqCount a b)) f hf
      simp only [card_range] at hraw
      have hδn : 0 ≤ δ * (seqCount a b : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
      have hlog : 0 ≤ ((Nat.log 2 b + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · have hhalf : X₀ ≤ b / 2 := Nat.not_lt.mp hstop
      have hb : 0 < b := by omega
      have hlt : b / 2 < b := Nat.div_lt_self hb (by norm_num : 1 < 2)
      have hi := ih (b / 2) hlt (fun X hx hx' => hblock X hx (hx'.trans hlt.le))
      let n₀ := seqCount a (b / 2)
      let n₁ := seqCount a (2 * (b / 2))
      let n₂ := seqCount a b
      have h01 : n₀ ≤ n₁ := seqCount_mono (by omega)
      have h12 : n₁ ≤ n₂ := seqCount_mono (Nat.mul_div_le b 2)
      have hw := hblock (b / 2) hhalf hlt.le
      rw [CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha, Nat.card_Ico] at hw
      have hd := (abs_sum_le_card (Ico n₁ n₂) f hf).trans
        ((Nat.cast_le (α := ℝ).2 (halve_drop_card ha b)).trans_eq Nat.cast_one)
      have hsplit := prefix_split f h01 h12
      have htri : |∑ n ∈ range n₂, f n| ≤
          |∑ n ∈ range n₀, f n| + |∑ n ∈ Ico n₀ n₁, f n| + |∑ n ∈ Ico n₁ n₂, f n| := by
        rw [hsplit]
        exact (abs_add_le _ _).trans (_root_.add_le_add (abs_add_le _ _) le_rfl)
      have hc : δ * (n₀ : ℝ) + δ * ((n₁ - n₀ : ℕ) : ℝ) ≤ δ * (n₂ : ℝ) := by
        rw [Nat.cast_sub h01]
        have hh := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ).2 h12) hδ
        nlinarith
      have hlog : Nat.log 2 (b / 2) + 1 + 1 = Nat.log 2 b + 1 := by
        have hp := Nat.log_pos (by norm_num : 1 < 2) (show 2 ≤ b by omega)
        rw [Nat.log_div_base]
        omega
      have hlogR : ((Nat.log 2 (b / 2) + 1 : ℕ) : ℝ) + 1 = ((Nat.log 2 b + 1 : ℕ) : ℝ) := by
        exact_mod_cast hlog
      change |∑ n ∈ range n₀, f n| ≤ δ * (n₀ : ℝ) +
        (seqCount a (2 * X₀) : ℝ) + (Nat.log 2 (b / 2) + 1 : ℕ) at hi
      change |∑ n ∈ Ico n₀ n₁, f n| ≤ δ * ((n₁ - n₀ : ℕ) : ℝ) at hw
      change |∑ n ∈ range n₂, f n| ≤ _
      linarith

def intervalIndicator (B : ℕ) (β : AddCircle (1 : ℝ)) (t : ℝ) (n : ℕ) : ℝ :=
  (anchoredCircleInterval t).indicator (fun _ => (1 : ℝ)) (B ^ n • β)

theorem intervalIndicator_bounds (B : ℕ) (β : AddCircle (1 : ℝ)) (t : ℝ) (n : ℕ) :
    0 ≤ intervalIndicator B β t n ∧ intervalIndicator B β t n ≤ 1 := by
  unfold intervalIndicator Set.indicator
  split_ifs <;> norm_num

theorem centered_indicator_abs_le (B : ℕ) (β : AddCircle (1 : ℝ)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) (n : ℕ) : |intervalIndicator B β t n - t| ≤ 1 := by
  have hi := intervalIndicator_bounds B β t n
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem intervalMass_eq_sum (B : ℕ) (β : AddCircle (1 : ℝ)) (a m : ℕ) (t : ℝ) :
    orbitIntervalMass B β a m t = (∑ n ∈ range m, intervalIndicator B β t (a + n)) / (m : ℝ) := rfl

theorem prime_block_centered_sum_le (B : ℕ) (β : AddCircle (1 : ℝ)) (X : ℕ) {t δ : ℝ}
    (h : |orbitIntervalMass B β (Nat.primeCounting X) (windowNX X) t - t| ≤ δ) :
    |∑ n ∈ seqWindow nthPrime X, (intervalIndicator B β t n - t)| ≤ δ * (windowNX X : ℝ) := by
  by_cases hN : windowNX X = 0
  · have he : seqWindow nthPrime X = ∅ := card_eq_zero.1 (by simpa only [seqWindow_nthPrime_card] using hN)
    simp only [he, sum_empty, abs_zero, hN, Nat.cast_zero, mul_zero, le_refl]
  · have hNr : (windowNX X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
    have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (windowNX X) : (0 : ℝ) ≤ _)
    have he : (∑ n ∈ seqWindow nthPrime X, (intervalIndicator B β t n - t)) =
        (orbitIntervalMass B β (Nat.primeCounting X) (windowNX X) t - t) * (windowNX X : ℝ) := by
      rw [CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount nthPrime_strictMono,
        seqCount_nthPrime, seqCount_nthPrime, sum_Ico_eq_sum_range, sum_sub_distrib, intervalMass_eq_sum]
      simp only [sum_const, nsmul_eq_mul, card_range, windowNX]
      have hNr' : (((2 * X).primeCounting - X.primeCounting : ℕ) : ℝ) ≠ 0 := hNr
      field_simp [hNr'] <;> ring
    have habsN : |(windowNX X : ℝ)| = (windowNX X : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [he, abs_mul]
    rw [habsN]
    exact hh

/-- Actual prime-index prefix estimate with a freely chosen stopping
cutoff. It preserves uniformity in t and does not assume prefix density. -/
theorem prime_prefix_interval_bound (B : ℕ) (β : AddCircle (1 : ℝ)) {N X₀ : ℕ}
    (hN : 0 < N) (hX₀ : 1 ≤ X₀) {δ : ℝ} (hδ : 0 ≤ δ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hblock : ∀ X, X₀ ≤ X → X ≤ nthPrime (N - 1) →
      |orbitIntervalMass B β (Nat.primeCounting X) (windowNX X) t - t| ≤ δ) :
    |orbitIntervalMass B β 0 N t - t| ≤ δ +
      ((Nat.primeCounting (2 * X₀) : ℝ) + (Nat.log 2 (nthPrime (N - 1)) + 1 : ℕ)) / N := by
  have hh := abs_prefix_sum_le_of_blocks nthPrime_strictMono
    (fun n => intervalIndicator B β t n - t) (centered_indicator_abs_le B β ht) hδ hX₀
    (nthPrime (N - 1)) (fun X hx hxb => by
      simpa only [seqWindow_nthPrime_card] using prime_block_centered_sum_le B β X (hblock X hx hxb))
  rw [seqCount_apply_self nthPrime_strictMono, Nat.sub_add_cancel hN,
    seqCount_nthPrime] at hh
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have he : orbitIntervalMass B β 0 N t - t =
      (∑ n ∈ range N, (intervalIndicator B β t n - t)) / N := by
    rw [intervalMass_eq_sum, sum_sub_distrib]
    simp only [Nat.zero_add, sum_const, card_range, nsmul_eq_mul]
    field_simp [hn]
  rw [he, abs_div]
  have habsN : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [habsN]
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)).trans_eq (by field_simp [hn] <;> ring)

/-- The usual star discrepancy of the literal fractional-part orbit. -/
def starDiscrepancy (B : ℕ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup ((fun t : ℝ => |orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N t - t|) '' Set.Icc 0 1)

theorem intervalIndicator_eq_fract (B : ℕ) (α t : ℝ) (n : ℕ) :
    intervalIndicator B (α : AddCircle (1 : ℝ)) t n =
      if Int.fract ((B : ℝ) ^ n * α) < t then 1 else 0 := by
  have horbit : B ^ n • (α : AddCircle (1 : ℝ)) =
      (((B : ℝ) ^ n * α : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_pow]
  unfold intervalIndicator anchoredCircleInterval Set.indicator
  rw [horbit]
  simp

theorem prefixMass_eq_count (B : ℕ) (α t : ℝ) (N : ℕ) :
    orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N t =
      (((range N).filter (fun n => Int.fract ((B : ℝ) ^ n * α) < t)).card : ℝ) / N := by
  rw [intervalMass_eq_sum]
  simp only [Nat.zero_add, intervalIndicator_eq_fract, sum_boole]

theorem prefixMass_bounds (B : ℕ) (β : AddCircle (1 : ℝ)) (N : ℕ) (t : ℝ) :
    0 ≤ orbitIntervalMass B β 0 N t ∧ orbitIntervalMass B β 0 N t ≤ 1 := by
  rw [intervalMass_eq_sum]
  constructor
  · exact div_nonneg (sum_nonneg fun n _ => (intervalIndicator_bounds B β t _).1) (Nat.cast_nonneg _)
  · by_cases hN : N = 0
    · simp [hN]
    · apply (div_le_one (Nat.cast_pos.2 (Nat.pos_of_ne_zero hN))).2
      exact (sum_le_sum fun n _ => (intervalIndicator_bounds B β t _).2).trans_eq (by simp)

theorem interval_error_le_one (B : ℕ) (α : ℝ) (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    |orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N t - t| ≤ 1 := by
  have h := prefixMass_bounds B (α : AddCircle (1 : ℝ)) N t
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

theorem starDiscrepancy_le (B : ℕ) (α : ℝ) (N : ℕ) {D : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, |orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N t - t| ≤ D) :
    starDiscrepancy B α N ≤ D := by
  apply csSup_le
  · exact ⟨_, ⟨0, by simp, rfl⟩⟩
  · rintro y ⟨t, ht, rfl⟩
    exact h t ht

theorem interval_error_le_star (B : ℕ) (α : ℝ) (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    |orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N t - t| ≤ starDiscrepancy B α N := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact interval_error_le_one B α N ht
  · exact ⟨t, ht, rfl⟩

def digitWordCount (B : ℕ) (α : ℝ) (N r v : ℕ) : ℕ :=
  ((range N).filter (fun n => Int.fract ((B : ℝ) ^ n * α) ∈
    PrimeGapNormality.BFree.digitCylinder B r v)).card

private theorem interval_count_sub (u : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (((range N).filter (fun n => a ≤ u n ∧ u n < b)).card : ℝ) =
      (((range N).filter (fun n => u n < b)).card : ℝ) -
        (((range N).filter (fun n => u n < a)).card : ℝ) := by
  have hpoint (n : ℕ) :
      (if a ≤ u n ∧ u n < b then (1 : ℝ) else 0) =
        (if u n < b then 1 else 0) - (if u n < a then 1 else 0) := by
    by_cases ha : u n < a
    · have hb : u n < b := ha.trans_le hab
      simp only [not_le_of_gt ha, false_and, ha, hb, if_true, if_false, sub_self]
    · have ha' : a ≤ u n := le_of_not_gt ha
      by_cases hb : u n < b <;> simp [ha, ha', hb]
  have hh := sum_congr (s₁ := range N) (s₂ := range N) rfl (fun n _ => hpoint n)
  simpa only [sum_sub_distrib, sum_boole] using hh

/-- Uniform in both word length and word. No factor depending on r is
introduced: every word is one half-open interval. -/
theorem digitWordCount_error_le (B : ℕ) (hB : 2 ≤ B) (α : ℝ) {N : ℕ} (hN : 0 < N)
    (r v : ℕ) (hv : v < B ^ r) :
    |(digitWordCount B α N r v : ℝ) - (N : ℝ) * ((B : ℝ) ^ r)⁻¹| ≤
      2 * (N : ℝ) * starDiscrepancy B α N := by
  have hd : 0 < (B : ℝ) ^ r := pow_pos (Nat.cast_pos.2 (by omega)) _
  let a : ℝ := (v : ℝ) / (B : ℝ) ^ r
  let b : ℝ := (v + 1 : ℝ) / (B : ℝ) ^ r
  have ha0 : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hd.le
  have hvle : (v : ℝ) ≤ (v : ℝ) + 1 := by linarith
  have hab : a ≤ b := div_le_div_of_nonneg_right hvle hd.le
  have hb1 : b ≤ 1 := by
    apply (div_le_one hd).2
    exact_mod_cast Nat.succ_le_of_lt hv
  have hdiff : b - a = ((B : ℝ) ^ r)⁻¹ := by dsimp [a, b]; field_simp [hd.ne'] <;> ring
  have he := interval_count_sub (fun n => Int.fract ((B : ℝ) ^ n * α)) N hab
  have hcount : (digitWordCount B α N r v : ℝ) =
      (((range N).filter (fun n => Int.fract ((B : ℝ) ^ n * α) < b)).card : ℝ) -
        (((range N).filter (fun n => Int.fract ((B : ℝ) ^ n * α) < a)).card : ℝ) := by
    simpa only [digitWordCount, PrimeGapNormality.BFree.digitCylinder, Set.mem_Ico, a, b] using he
  have ha := interval_error_le_star B α N (t := a) ⟨ha0, hab.trans hb1⟩
  have hb := interval_error_le_star B α N (t := b) ⟨ha0.trans hab, hb1⟩
  have htri := (abs_sub
    (orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N b - b)
    (orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N a - a)).trans (_root_.add_le_add hb ha)
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have heq : (digitWordCount B α N r v : ℝ) - (N : ℝ) * ((B : ℝ) ^ r)⁻¹ =
      (N : ℝ) * ((orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N b - b) -
        (orbitIntervalMass B (α : AddCircle (1 : ℝ)) 0 N a - a)) := by
    rw [hcount, prefixMass_eq_count, prefixMass_eq_count, ← hdiff]
    field_simp [hNr]
    <;> ring
  rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact (mul_le_mul_of_nonneg_left htri (Nat.cast_nonneg _)).trans_eq (by ring)

/-- Stop the physical-value halving at sqrt(N), not sqrt(p_N). This
smaller cutoff still gives the same log-log rate and simplifies the early
prefix estimate to at most 2sqrt(N)+1 anchors. -/
def stoppingCutoff (N : ℕ) : ℕ := ⌊Real.sqrt (N : ℝ)⌋₊

theorem stoppingCutoff_le (N : ℕ) : (stoppingCutoff N : ℝ) ≤ Real.sqrt (N : ℝ) :=
  Nat.floor_le (Real.sqrt_nonneg _)

theorem stoppingCutoff_ge_half {N : ℕ} (hN : 4 ≤ N) :
    Real.sqrt (N : ℝ) / 2 ≤ (stoppingCutoff N : ℝ) := by
  have hs : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg N)).2
    exact_mod_cast hN
  have hf := Nat.lt_floor_add_one (Real.sqrt (N : ℝ))
  change Real.sqrt (N : ℝ) < (stoppingCutoff N : ℝ) + 1 at hf
  linarith

theorem tendsto_stoppingCutoff : Tendsto stoppingCutoff atTop atTop := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro m
  filter_upwards [hs.eventually_ge_atTop (m : ℝ)] with N hN
  exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).2 hN

def headError (N : ℕ) : ℝ :=
  (2 * Real.sqrt (N : ℝ) + 2 +
    (Real.log 144 + 2 * Real.log (N : ℝ)) / Real.log 2) / N

theorem prime_rounding_cost_le_headError {N : ℕ} (hN : 0 < N) :
    ((Nat.primeCounting (2 * stoppingCutoff N) : ℝ) +
      (Nat.log 2 (nthPrime (N - 1)) + 1 : ℕ)) / N ≤ headError N := by
  have hp : nthPrime (N - 1) ≤ 144 * N ^ 2 := by
    simpa only [Nat.sub_add_cancel hN] using nthPrime_le_succ_sq (N - 1)
  have hpr : (0 : ℝ) < nthPrime (N - 1) :=
    Nat.cast_pos.2 (by have hh := nthPrime_ge_add_two (N - 1); omega)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hlogp : Real.log (nthPrime (N - 1) : ℝ) ≤ Real.log 144 + 2 * Real.log (N : ℝ) := by
    have hh := Real.log_le_log hpr (Nat.cast_le (α := ℝ).2 hp)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Real.log_mul (by norm_num : (144 : ℝ) ≠ 0) (pow_ne_zero 2 hNr.ne'), Real.log_pow,
      Nat.cast_ofNat] using hh
  have hnatlog : (Nat.log 2 (nthPrime (N - 1)) : ℝ) ≤
      (Real.log 144 + 2 * Real.log (N : ℝ)) / Real.log 2 :=
    (Real.natLog_le_logb _ _).trans
      (div_le_div_of_nonneg_right hlogp (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  have hpi : Nat.primeCounting (2 * stoppingCutoff N) ≤ 2 * stoppingCutoff N + 1 := by
    rw [← seqCount_nthPrime]
    unfold seqCount
    exact (card_filter_le _ _).trans_eq (card_range _)
  have hpicast := Nat.cast_le (α := ℝ).2 hpi
  have hcut := stoppingCutoff_le N
  apply div_le_div_of_nonneg_right _ hNr.le
  push_cast at hpicast ⊢
  linarith

theorem headError_nonneg (N : ℕ) : 0 ≤ headError N := by
  unfold headError
  have hlogN := Real.log_natCast_nonneg N
  have hlog144 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 144)
  have hlog2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  positivity

/-- The omitted prefix and all odd-halving rounding terms are negligible
on the required log-log scale, using only the quadratic nth-prime bound. -/
theorem tendsto_headError_mul_sqrt_loglog :
    Tendsto (fun N : ℕ => headError N * Real.sqrt (Real.log (Real.log (N : ℝ)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hh
  have h2 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, one_mul, add_zero, pow_one] using hh
  have h3 : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, one_mul, add_zero] using hh
  have hmajor := ((h1.const_mul 2).add (h2.const_mul (2 + Real.log 144 / Real.log 2))).add
    (h3.const_mul (2 / Real.log 2))
  simp only [mul_zero, add_zero] at hmajor
  apply squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (headError_nonneg N) (Real.sqrt_nonneg _)) _ hmajor
  filter_upwards [(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2,
    eventually_ge_atTop 1] with N hl hN
  simp only [Function.comp_apply] at hl
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hl0 : 0 < Real.log (N : ℝ) := by linarith
  have hell0 : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith)
  have hsq := Real.sq_sqrt hell0
  have hs0 := Real.sqrt_nonneg (Real.log (Real.log (N : ℝ)))
  have hlog := Real.log_le_sub_one_of_pos hl0
  have hs : Real.sqrt (Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (Real.log (Real.log (N : ℝ))) - 1)]
  have hdiv : Real.sqrt (N : ℝ) / N = 1 / Real.sqrt (N : ℝ) := by
    apply (div_eq_div_iff hNr.ne' (Real.sqrt_pos.2 hNr).ne').2
    nlinarith [Real.sq_sqrt hNr.le]
  refine (mul_le_mul_of_nonneg_left hs (headError_nonneg N)).trans_eq ?_
  calc
    headError N * Real.log (N : ℝ) =
        2 * Real.log (N : ℝ) * (Real.sqrt (N : ℝ) / N) +
          (2 + Real.log 144 / Real.log 2) * (Real.log (N : ℝ) / N) +
          (2 / Real.log 2) * (Real.log (N : ℝ) ^ 2 / N) := by unfold headError; ring
    _ = _ := by rw [hdiv]; ring

/-- Every retained physical scale has a common log-log denominator. -/
theorem eventually_block_rate_comparison {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt (Real.log (Real.log (N : ℝ))) ∧
      ∀ X : ℕ, stoppingCutoff N ≤ X →
        C / Real.sqrt (Real.log (windowG X)) ≤
          2 * C / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hll := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_ge_atTop 4, hlog.eventually_ge_atTop (4 * Real.log 2),
    hll.eventually_gt_atTop (max 0 (2 * Real.log 4))] with N hN hl hell
  simp only [Function.comp_apply] at hl hell
  have hn : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hepos : 0 < Real.log (Real.log (N : ℝ)) := lt_of_le_of_lt (le_max_left _ _) hell
  refine ⟨Real.sqrt_pos.2 hepos, ?_⟩
  intro X hX
  have hs : Real.sqrt (N : ℝ) / 2 ≤ (X : ℝ) :=
    (stoppingCutoff_ge_half hN).trans (Nat.cast_le (α := ℝ).2 hX)
  have hspos : 0 < Real.sqrt (N : ℝ) / 2 := by positivity
  have hlogX := Real.log_le_log hspos hs
  rw [Real.log_div (Real.sqrt_pos.2 hn).ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_sqrt hn.le] at hlogX
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : Real.log (N : ℝ) / 4 ≤ windowG X := by
    have hxg : Real.log (X : ℝ) ≤ windowG X := le_max_left _ _
    linarith
  have hllower := Real.log_le_log (show 0 < Real.log (N : ℝ) / 4 by positivity) hscale
  rw [Real.log_div hlogNpos.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hllower
  have heg : Real.log (Real.log (N : ℝ)) ≤ 2 * Real.log (windowG X) := by
    have he4 := lt_of_le_of_lt (le_max_right _ _) hell
    linarith
  have hgpos : 0 < Real.log (windowG X) := by linarith
  have hsq := Real.sqrt_le_sqrt (show Real.log (Real.log (N : ℝ)) ≤ 4 * Real.log (windowG X) by linarith)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hsq
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsqrt4] at hsq
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hgpos) (Real.sqrt_pos.2 hepos)).2
  have hh := mul_le_mul_of_nonneg_left hsq hC
  nlinarith

/-- General quantitative block-to-prefix consumer. The block premise is
an honest intermediate; the prime Kuperberg endpoint discharges it. -/
theorem star_rate_of_prime_blocks (B : ℕ) (α : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hblock : ∀ᶠ X in atTop, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |orbitIntervalMass B (α : AddCircle (1 : ℝ)) (Nat.primeCounting X) (windowNX X) t - t| ≤
        C / Real.sqrt (Real.log (windowG X))) :
    ∀ᶠ N in atTop, starDiscrepancy B α N ≤
      (2 * C + 1) / Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hblock
  filter_upwards [tendsto_stoppingCutoff.eventually_ge_atTop (max X₀ 1),
    eventually_ge_atTop 1, eventually_block_rate_comparison hC,
    tendsto_headError_mul_sqrt_loglog.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with N hcut hN hrate hhead
  have hNp : 0 < N := by omega
  have hcut1 : 1 ≤ stoppingCutoff N := (le_max_right _ _).trans hcut
  have hhead' : headError N ≤ 1 / Real.sqrt (Real.log (Real.log (N : ℝ))) :=
    (le_div_iff₀ hrate.1).2 hhead
  apply starDiscrepancy_le
  intro t ht
  have hh := prime_prefix_interval_bound B (α : AddCircle (1 : ℝ)) hNp hcut1
    (show 0 ≤ 2 * C / Real.sqrt (Real.log (Real.log (N : ℝ))) by positivity) ht
    (fun X hx _ => (hX₀ X ((le_max_left _ _).trans (hcut.trans hx)) t ht).trans (hrate.2 X hx))
  exact (hh.trans (_root_.add_le_add le_rfl ((prime_rounding_cost_le_headError hNp).trans hhead'))).trans_eq (by ring)

end
end PrimeGapNormality.Prime.CorePrimeGlobalDiscrepancy
