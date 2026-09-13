import PrimeGapNormality.Prime.EndAPI
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

/-!
# Kuperberg 1.3 adapter for the aggregated AHL budget

Direct implication from Kuperberg's indicator conjecture to `AHL`,
following the paper subtraction of (eq:khl) at `2X` and `X`. AHL
remains the generic interface; this file is only the adapter.

Source: `rounds/round104/01_gpt_paper_v0_2.tex`
subsection "Direct implication from Kuperberg's conjecture";
`lean/PrimeGapNormality/Prime/EndAPI.lean`; R104/07.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset Filter Topology intervalIntegral MeasureTheory

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-! ### Elementary comparisons -/

private theorem posPart_le_abs (x : ℝ) : x⁺ ≤ |x| :=
  sup_le (le_abs_self x) (abs_nonneg x)

private theorem two_mul_cast (X : ℕ) : (2 * X : ℝ) = 2 * (X : ℝ) := by
  simp

private theorem windowG_log_nonneg (X : ℕ) : 0 ≤ Real.log (windowG X) :=
  Real.log_nonneg (le_max_right _ _)

private theorem windowG_one_le (X : ℕ) : 1 ≤ windowG X :=
  le_max_right _ _

theorem one_lt_log_of_three_le {X : ℕ} (hX : 3 ≤ X) :
    1 < Real.log (X : ℝ) := by
  have hpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have : Real.exp 1 < (X : ℝ) := hexp.trans_le (Nat.cast_le.mpr hX)
  exact (Real.lt_log_iff_exp_lt hpos).mpr this

theorem windowG_eq_log {X : ℕ} (hX : 3 ≤ X) : windowG X = Real.log (X : ℝ) :=
  max_eq_left (one_lt_log_of_three_le hX).le

theorem log_sixteen_gt_exp_one : Real.exp 1 < Real.log (16 : ℝ) := by
  have hpow : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h16 : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h16, Real.log_pow]
    norm_cast
  have hmul : (4 : ℝ) * 0.6931471803 < 4 * Real.log 2 :=
    mul_lt_mul_of_pos_left Real.log_two_gt_d9 (by norm_num)
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [hpow]
  linarith

theorem one_lt_log_log_of_sixteen_le {X : ℕ} (hX : 16 ≤ X) :
    1 < Real.log (Real.log (X : ℝ)) := by
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hpos : 0 < Real.log (X : ℝ) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_log_of_three_le hX3)
  have h16 : Real.log (16 : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num) (Nat.cast_le.mpr hX)
  have : Real.exp 1 < Real.log (X : ℝ) := log_sixteen_gt_exp_one.trans_le h16
  exact (Real.lt_log_iff_exp_lt hpos).mpr this

theorem one_le_log_log_pow_three {X : ℕ} (hX : 16 ≤ X) :
    (1 : ℝ) ≤ Real.log (Real.log (X : ℝ)) ^ 3 := by
  have h : 1 < Real.log (Real.log (X : ℝ)) := one_lt_log_log_of_sixteen_le hX
  have : (1 : ℝ) ^ 3 ≤ Real.log (Real.log (X : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h.le 3
  simpa using this

/-! ### Profile bounds -/

theorem profileL_cast_le {κ : ℝ} (hκ : 0 ≤ κ) (X : ℕ) :
    (profileL κ X : ℝ) ≤
      κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) + 1 := by
  set a := κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X))
  have ha : 0 ≤ a :=
    add_nonneg (mul_nonneg hκ (windowG_log_nonneg X)) (Real.sqrt_nonneg _)
  exact (Nat.ceil_lt_add_one (R := ℝ) ha).le

theorem profileS_cast_le (κ : ℝ) (X : ℕ) :
    (profileS κ X : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X := by
  have hL : 0 ≤ (profileL κ X : ℝ) := Nat.cast_nonneg _
  have hG : 0 ≤ windowG X := le_trans (by norm_num : (0 : ℝ) ≤ 1) (windowG_one_le X)
  have hnn : 0 ≤ (4 : ℝ) * (profileL κ X : ℝ) * windowG X :=
    mul_nonneg (mul_nonneg (by norm_num) hL) hG
  exact Nat.floor_le hnn

theorem profileR_le (L : ℕ) (d0 : ℝ) :
    profileR L d0 ≤ max L ⌈d0 * (L : ℝ)⌉₊ + 1 := by
  dsimp [profileR]
  split_ifs <;> omega

theorem profileR_ge (L : ℕ) (d0 : ℝ) : L ≤ profileR L d0 := by
  dsimp [profileR]
  split_ifs <;> omega

theorem profileR_cast_le (L : ℕ) {d0 : ℝ} (hd0 : 0 ≤ d0) :
    (profileR L d0 : ℝ) ≤ (L : ℝ) + d0 * (L : ℝ) + 2 := by
  have hnat := profileR_le L d0
  have hceil : (⌈d0 * (L : ℝ)⌉₊ : ℝ) ≤ d0 * (L : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hd0 (Nat.cast_nonneg L))).le
  have ht : (max L ⌈d0 * (L : ℝ)⌉₊ : ℝ) ≤ max (L : ℝ) (d0 * (L : ℝ) + 1) :=
    max_le_max le_rfl hceil
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hrest : 0 ≤ d0 * (L : ℝ) + 1 :=
    add_nonneg (mul_nonneg hd0 (Nat.cast_nonneg L)) zero_le_one
  have hmax : max (L : ℝ) (d0 * (L : ℝ) + 1) ≤ (L : ℝ) + d0 * (L : ℝ) + 1 := by
    apply max_le
    · linarith
    · linarith
  have : (profileR L d0 : ℝ) ≤ (max L ⌈d0 * (L : ℝ)⌉₊ : ℝ) + 1 := by
    exact_mod_cast hnat
  linarith

theorem windowOmega_card (κ : ℝ) (X : ℕ) :
    (windowOmega κ X).card = profileS κ X := by
  simp [windowOmega]

theorem zero_notMem_windowOmega (κ : ℝ) (X : ℕ) : 0 ∉ windowOmega κ X := by
  simp [windowOmega]

theorem zero_notMem_of_subset_windowOmega {κ : ℝ} {X : ℕ} {H : Finset ℕ}
    (hH : H ⊆ windowOmega κ X) : 0 ∉ H :=
  fun h => zero_notMem_windowOmega κ X (hH h)

theorem le_profileS_of_mem_windowOmega {κ : ℝ} {X : ℕ} {h : ℕ}
    (hh : h ∈ windowOmega κ X) : h ≤ profileS κ X :=
  (mem_Icc.mp hh).2

/-! ### Window identity -/

theorem prime_pattern_insert_zero (n : ℕ) (H : Finset ℕ) :
    (∀ h ∈ insert 0 H, Nat.Prime (n + h)) ↔
      Nat.Prime n ∧ ∀ h ∈ H, Nat.Prime (n + h) := by
  simp

theorem hlCount_mono {x y : ℕ} (hxy : x ≤ y) (E : Finset ℕ) :
    hlCount x E ≤ hlCount y E := by
  refine card_le_card (filter_subset_filter _ ?_)
  intro n hn
  rw [Finset.mem_range] at hn ⊢
  exact lt_of_lt_of_le hn (Nat.succ_le_succ hxy)

theorem range_sdiff_range_eq_Ioc (X : ℕ) :
    Finset.range (2 * X + 1) \ Finset.range (X + 1) = Finset.Ioc X (2 * X) := by
  ext n
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · intro h
    exact ⟨Nat.succ_le_iff.mp (le_of_not_gt h.2), Nat.lt_succ_iff.mp h.1⟩
  · intro h
    exact ⟨Nat.lt_succ_iff.mpr h.2, not_lt.mpr (Nat.succ_le_iff.mpr h.1)⟩

theorem filter_sdiff_eq {α : Type*} [DecidableEq α] (s t : Finset α) (P : α → Prop)
    [DecidablePred P] : (s \ t).filter P = s.filter P \ t.filter P := by
  ext x
  constructor
  · intro hx
    have hstP : x ∈ s \ t ∧ P x := mem_filter.mp hx
    have hst : x ∈ s ∧ x ∉ t := mem_sdiff.mp hstP.1
    exact mem_sdiff.mpr
      ⟨mem_filter.mpr ⟨hst.1, hstP.2⟩,
        fun ht => hst.2 (mem_filter.mp ht).1⟩
  · intro hx
    have hstP : x ∈ s.filter P ∧ x ∉ t.filter P := mem_sdiff.mp hx
    have hsP : x ∈ s ∧ P x := mem_filter.mp hstP.1
    refine mem_filter.mpr
      ⟨mem_sdiff.mpr ⟨hsP.1, fun ht => hstP.2 (mem_filter.mpr ⟨ht, hsP.2⟩)⟩, hsP.2⟩

/-- Paper window identity: `C_X(H)` is the difference of cumulative
Hardy–Littlewood counts at `2X` and `X`. Lean `Ioc X (2X)` matches
`range (2X+1) \ range (X+1)` exactly. -/
theorem rootedTupleCount_eq_hlCount_sub (X : ℕ) (H : Finset ℕ) :
    rootedTupleCount X H =
      hlCount (2 * X) (insert 0 H) - hlCount X (insert 0 H) := by
  unfold rootedTupleCount hlCount
  set E := insert 0 H
  set Q : ℕ → Prop := fun n => ∀ h ∈ E, Nat.Prime (n + h)
  have hP : ∀ n,
      (Nat.Prime n ∧ ∀ h ∈ H, Nat.Prime (n + h)) ↔ Q n := by
    intro n
    simpa [Q, E] using (prime_pattern_insert_zero n H).symm
  have hfilter :
      ((Ioc X (2 * X)).filter fun n => Nat.Prime n ∧ ∀ h ∈ H, Nat.Prime (n + h)) =
        (Ioc X (2 * X)).filter Q := by
    ext n
    simp [hP]
  rw [hfilter]
  have hr : Finset.range (X + 1) ⊆ Finset.range (2 * X + 1) := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  have hsdiff := range_sdiff_range_eq_Ioc X
  have hfil := filter_sdiff_eq (Finset.range (2 * X + 1)) (Finset.range (X + 1)) Q
  have hsub : (Finset.range (X + 1)).filter Q ⊆ (Finset.range (2 * X + 1)).filter Q :=
    filter_subset_filter _ hr
  rw [← hsdiff, hfil, card_sdiff_of_subset hsub]

theorem rootedMainTerm_eq_hlMain_sub (X : ℕ) {H : Finset ℕ} (h0 : 0 ∉ H) :
    rootedMainTerm X H =
      hlMain (2 * X : ℝ) (insert 0 H) - hlMain (X : ℝ) (insert 0 H) := by
  unfold rootedMainTerm hlMain
  have hc : (insert 0 H).card = H.card + 1 := card_insert_of_notMem h0
  simp [hc]

theorem rooted_error_eq {X : ℕ} {H : Finset ℕ} (h0 : 0 ∉ H) :
    (rootedTupleCount X H : ℝ) - rootedMainTerm X H =
      ((hlCount (2 * X) (insert 0 H) : ℝ) - hlMain (2 * X : ℝ) (insert 0 H)) -
        ((hlCount X (insert 0 H) : ℝ) - hlMain (X : ℝ) (insert 0 H)) := by
  have hwin := rootedTupleCount_eq_hlCount_sub X H
  have hmain := rootedMainTerm_eq_hlMain_sub X h0
  have hle : hlCount X (insert 0 H) ≤ hlCount (2 * X) (insert 0 H) :=
    hlCount_mono (by omega) _
  rw [hwin, hmain, Nat.cast_sub hle]
  ring

/-! ### One-point case `E = {0}` -/

theorem hlCount_singleton_zero (x : ℕ) :
    hlCount x {0} = Nat.primeCounting x := by
  unfold hlCount Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp

theorem hlAdmissible_singleton_zero : hlAdmissible {0} := by
  intro p hp
  haveI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  unfold residueCount
  rw [image_singleton, card_singleton]
  exact hp.one_lt

theorem localHLFactor_singleton_zero (n : ℕ) : localHLFactor {0} n = 1 := by
  unfold localHLFactor
  split_ifs with h
  · rfl
  · have hn : 2 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge h)
    haveI : NeZero n := ⟨by omega⟩
    have hrc : residueCount {0} n = 1 := by
      unfold residueCount
      rw [image_singleton, card_singleton]
    have hc : ({0} : Finset ℕ).card = 1 := card_singleton _
    rw [hrc, hc]
    have hne : (1 : ℝ) - 1 / n ≠ 0 := by
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have : (1 : ℝ) - 1 / n = (n - 1) / n := by field_simp
      rw [this]
      apply div_ne_zero _ hn0
      have : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith
    rw [pow_one]
    convert div_self hne
    norm_cast

theorem singularSeries_singleton_zero : singularSeries {0} = 1 := by
  unfold singularSeries
  have hfun :
      (fun n : ℕ => if Nat.Prime n then localHLFactor {0} n else 1) =
        fun _ => (1 : ℝ) := by
    funext n
    split_ifs
    · exact localHLFactor_singleton_zero n
    · rfl
  rw [hfun, tprod_one]

theorem hlMain_singleton_zero (x : ℝ) : hlMain x {0} = hlIntegral x 1 := by
  unfold hlMain
  rw [singularSeries_singleton_zero, card_singleton, one_mul]

/-- Unconditional Chebyshev lower bound on `π(n)`. Mathlib's constants
satisfy `2 log 2 = log 4`, so they do not by themselves give
`N_X ≫ X / log X`. -/
theorem primeCounting_ge_chebyshev (n : ℕ) :
    ((n : ℝ) * Real.log 2 - Real.log (n + 1 : ℝ)) / Real.log n ≤
      (Nat.primeCounting n : ℝ) :=
  Chebyshev.pi_ge n

theorem windowNX_pos {X : ℕ} (hX : 0 < X) : 0 < windowNX X := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul X (ne_of_gt hX)
  have hsub : Nat.primesLE X ⊆ Nat.primesLE (2 * X) :=
    Nat.primesLE_mono (by omega : X ≤ 2 * X)
  have hpX : p ∉ Nat.primesLE X := by
    simp [Nat.mem_primesLE, hp, not_le.mpr hlt]
  have hp2 : p ∈ Nat.primesLE (2 * X) := Nat.mem_primesLE.mpr ⟨hle, hp⟩
  have hss : Nat.primesLE X ⊂ Nat.primesLE (2 * X) := by
    refine (ssubset_iff_subset_ne).2 ⟨hsub, ?_⟩
    intro heq
    exact hpX (heq.symm ▸ hp2)
  have hcard := card_lt_card hss
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard
  exact Nat.sub_pos_of_lt hcard

/-! ### Integrals for the one-point main term -/

theorem continuousOn_hlIntegrand (k : ℕ) {s : Set ℝ}
    (hs : ∀ t ∈ s, 2 ≤ t) :
    ContinuousOn (fun t : ℝ => Real.log t ^ (-(k : ℝ))) s := by
  refine ContinuousOn.rpow_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hs t ht)).ne'
  · intro t ht
    refine Or.inl ?_
    have ht1 : 1 < t := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hs t ht)
    exact (Real.log_pos ht1).ne'

theorem hlIntegrand_intervalIntegrable (k : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => Real.log t ^ (-(k : ℝ))) volume a b := by
  refine (continuousOn_hlIntegrand k ?_).intervalIntegrable
  intro t ht
  have ht' : t ∈ Set.Icc (min a b) (max a b) := ht
  exact (le_min ha hb).trans ht'.1

theorem hlIntegral_sub {a b : ℝ} (k : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    hlIntegral b k - hlIntegral a k =
      ∫ t in a..b, Real.log t ^ (-(k : ℝ)) := by
  have hb : 2 ≤ b := ha.trans hab
  have I2a := hlIntegrand_intervalIntegrable k (by norm_num : (2 : ℝ) ≤ 2) ha
  have Iab := hlIntegrand_intervalIntegrable k ha hb
  have hadj := integral_add_adjacent_intervals I2a Iab
  unfold hlIntegral
  linarith

theorem hlIntegral_one_dyadic_ge {X : ℕ} (hX : 3 ≤ X) :
    hlIntegral (2 * X : ℝ) 1 - hlIntegral (X : ℝ) 1 ≥
      (X : ℝ) / Real.log (2 * (X : ℝ)) := by
  have h2X : 2 ≤ (X : ℝ) := by exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hX)
  have hab : (X : ℝ) ≤ 2 * (X : ℝ) := by
    have : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
    linarith
  have hb : 2 ≤ 2 * (X : ℝ) := by linarith
  have hcast : (2 * X : ℝ) = 2 * (X : ℝ) := two_mul_cast X
  rw [hcast, hlIntegral_sub 1 h2X hab]
  have h1X : 1 < 2 * (X : ℝ) := by
    have : (1 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hX)
    linarith
  have hlog : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h1X
  have hf :
      IntervalIntegrable (fun t => Real.log t ^ (-(1 : ℝ))) volume (X : ℝ) (2 * (X : ℝ)) := by
    simpa using hlIntegrand_intervalIntegrable 1 h2X hb
  have hg : IntervalIntegrable (fun _ : ℝ => (Real.log (2 * (X : ℝ)))⁻¹)
      volume (X : ℝ) (2 * (X : ℝ)) :=
    intervalIntegrable_const
  have hpoint : ∀ t ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)),
      (Real.log (2 * (X : ℝ)))⁻¹ ≤ Real.log t ^ (-(1 : ℝ)) := by
    intro t ht
    have ht2 : 2 ≤ t := h2X.trans ht.1
    have ht1 : 1 < t := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ht2
    have hlogt : 0 < Real.log t := Real.log_pos ht1
    have hle : Real.log t ≤ Real.log (2 * (X : ℝ)) :=
      Real.log_le_log (lt_trans (by norm_num : (0 : ℝ) < 1) ht1) ht.2
    rw [Real.rpow_neg_one]
    exact inv_anti₀ hlogt hle
  have hmono := integral_mono_on hab hg hf hpoint
  have hconst :
      (∫ t in (X : ℝ)..(2 * (X : ℝ)), (Real.log (2 * (X : ℝ)))⁻¹) =
        (2 * (X : ℝ) - (X : ℝ)) * (Real.log (2 * (X : ℝ)))⁻¹ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hsub : 2 * (X : ℝ) - (X : ℝ) = (X : ℝ) := by ring
  have : (X : ℝ) * (Real.log (2 * (X : ℝ)))⁻¹ =
      (X : ℝ) / Real.log (2 * (X : ℝ)) := by
    field_simp [hlog.ne']
  linarith

/-- One-point Kuperberg: `|π(x) - ∫_2^x dt/log t| ≤ K x^{1-ε}` for `x ≥ 16`. -/
theorem kuperberg_one_point (hK : KuperbergConj13) {x : ℕ} (hx : 16 ≤ x) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧
      |(Nat.primeCounting x : ℝ) - hlMain (x : ℝ) {0}| ≤ K * (x : ℝ) ^ (1 - ε) := by
  obtain ⟨ε, K, hε, hKpos, hbound⟩ := hK
  refine ⟨ε, K, hε, hKpos, ?_⟩
  have hcard : (({0} : Finset ℕ).card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 := by
    rw [card_singleton]
    exact_mod_cast (one_le_log_log_pow_three hx)
  have hdiam : ∀ h ∈ ({0} : Finset ℕ), (h : ℝ) ≤ Real.log (x : ℝ) ^ 2 := by
    intro h hh
    have : h = 0 := mem_singleton.mp hh
    subst this
    simpa using sq_nonneg (Real.log (x : ℝ))
  have := hbound x {0} hx hdiam hcard hlAdmissible_singleton_zero
  simpa [hlCount_singleton_zero] using this

/-! ### Inadmissible tuples -/

theorem exists_covering_prime {E : Finset ℕ} (h : ¬ hlAdmissible E) :
    ∃ p : ℕ, Nat.Prime p ∧ residueCount E p = p ∧ p ≤ E.card := by
  simp only [hlAdmissible, not_forall, Classical.not_imp] at h
  obtain ⟨p, hp, hpE⟩ := h
  have hpE' : p ≤ residueCount E p := le_of_not_gt hpE
  have : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have hle_univ : residueCount E p ≤ Fintype.card (ZMod p) := by
    haveI := this
    exact card_le_univ _
  rw [ZMod.card] at hle_univ
  have heq : residueCount E p = p := le_antisymm hle_univ hpE'
  have hleE : residueCount E p ≤ E.card := card_image_le
  exact ⟨p, hp, heq, heq ▸ hleE⟩

theorem no_prime_tuple_of_covering {E : Finset ℕ} {p n : ℕ}
    (hp : Nat.Prime p) (hcov : residueCount E p = p) (hn : p < n)
    (hpat : ∀ h ∈ E, Nat.Prime (n + h)) : False := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  have him : E.image (fun h : ℕ => (h : ZMod p)) = univ := by
    refine eq_univ_of_card _ ?_
    rw [ZMod.card]
    exact hcov
  have hmem : -(n : ZMod p) ∈ E.image (fun h : ℕ => (h : ZMod p)) := by
    rw [him]
    exact mem_univ _
  obtain ⟨h, hE, hh⟩ := mem_image.mp hmem
  have hsum : ((n + h : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, hh, add_neg_cancel]
  have hdvd : p ∣ n + h := (ZMod.natCast_eq_zero_iff (n + h) p).mp hsum
  have hpr : Nat.Prime (n + h) := hpat h hE
  have heq : p = n + h := (Nat.prime_dvd_prime_iff_eq hp hpr).mp hdvd
  have hlt : p < n + h := hn.trans_le (Nat.le_add_right n h)
  exact (ne_of_lt hlt) heq

theorem rootedTupleCount_eq_zero_of_covering {X : ℕ} {H : Finset ℕ} {p : ℕ}
    (hp : Nat.Prime p) (hcov : residueCount (insert 0 H) p = p) (hX : p ≤ X) :
    rootedTupleCount X H = 0 := by
  unfold rootedTupleCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro n hn hpat
  have hnX : X < n := (mem_Ioc.mp hn).1
  have hnp : p < n := lt_of_le_of_lt hX hnX
  have hroot : Nat.Prime n := hpat.1
  have hall : ∀ h ∈ insert 0 H, Nat.Prime (n + h) := by
    intro h hh
    rcases mem_insert.mp hh with rfl | hh'
    · simpa using hroot
    · exact hpat.2 h hh'
  exact no_prime_tuple_of_covering hp hcov hnp hall

theorem rootedTupleCount_eq_zero_of_not_hlAdmissible {X : ℕ} {H : Finset ℕ}
    (_h0 : 0 ∉ H) (hadm : ¬ hlAdmissible (insert 0 H))
    (hX : (insert 0 H).card ≤ X) : rootedTupleCount X H = 0 := by
  obtain ⟨p, hp, hcov, hpE⟩ := exists_covering_prime hadm
  exact rootedTupleCount_eq_zero_of_covering hp hcov (le_trans hpE hX)

theorem singularSeries_eq_zero_of_not_hlAdmissible {E : Finset ℕ}
    (h : ¬ hlAdmissible E) : singularSeries E = 0 := by
  obtain ⟨p, hp, hcov, _⟩ := exists_covering_prime h
  unfold singularSeries
  refine tprod_of_exists_eq_zero ⟨p, ?_⟩
  have hp1 : ¬ p ≤ 1 := not_le.mpr hp.one_lt
  unfold localHLFactor
  simp [hp, hp1, hcov]
  left
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  simp [div_self hp0]

theorem rootedMainTerm_eq_zero_of_not_hlAdmissible {X : ℕ} {H : Finset ℕ}
    (hadm : ¬ hlAdmissible (insert 0 H)) : rootedMainTerm X H = 0 := by
  unfold rootedMainTerm
  have hS : singularSeries (insert 0 H) = 0 :=
    singularSeries_eq_zero_of_not_hlAdmissible hadm
  rw [hS]
  ring

theorem rooted_error_eq_zero_of_not_hlAdmissible {X : ℕ} {H : Finset ℕ}
    (h0 : 0 ∉ H) (hadm : ¬ hlAdmissible (insert 0 H))
    (hX : (insert 0 H).card ≤ X) :
    (rootedTupleCount X H : ℝ) - rootedMainTerm X H = 0 := by
  rw [rootedTupleCount_eq_zero_of_not_hlAdmissible h0 hadm hX,
    rootedMainTerm_eq_zero_of_not_hlAdmissible hadm]
  simp

/-! ### Binomial envelope -/

theorem card_j_subsets_windowOmega (κ : ℝ) (X j : ℕ) :
    ((windowOmega κ X).powerset.filter fun H => H.card = j).card =
      (profileS κ X).choose j := by
  rw [← powersetCard_eq_filter, card_powersetCard, windowOmega_card]

theorem ahlLayer_le_choose_mul (κ : ℝ) (X j L : ℕ) {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ H ⊆ windowOmega κ X, H.card = j →
      (((-1 : ℝ) ^ (j - L + 1)) *
        ((rootedTupleCount X H : ℝ) - rootedMainTerm X H))⁺ ≤ B) :
    ahlLayer κ X j L ≤ ((profileS κ X).choose j : ℝ) * B := by
  unfold ahlLayer
  have hset :
      (windowOmega κ X).powerset.filter (fun H => H.card = j) =
        (windowOmega κ X).powersetCard j :=
    (powersetCard_eq_filter).symm
  rw [hset]
  have hle : ∀ H ∈ (windowOmega κ X).powersetCard j,
      (((-1 : ℝ) ^ (j - L + 1)) *
        ((rootedTupleCount X H : ℝ) - rootedMainTerm X H))⁺ ≤ B := by
    intro H hH
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hH
    exact hB H hsub hcard
  have hsum := sum_le_card_nsmul _ _ B hle
  have hcard : ((windowOmega κ X).powersetCard j).card = (profileS κ X).choose j := by
    rw [card_powersetCard, windowOmega_card]
  rw [hcard, nsmul_eq_mul] at hsum
  exact hsum

theorem choose_le_two_pow_of_le {j r L : ℕ} (hjr : j ≤ r) :
    ((j - 1).choose (L - 1) : ℝ) ≤ (2 : ℝ) ^ r := by
  have hnat : (j - 1).choose (L - 1) ≤ 2 ^ (j - 1) := Nat.choose_le_two_pow _ _
  have hjr' : j - 1 ≤ r := le_trans (Nat.sub_le j 1) hjr
  have hpow : 2 ^ (j - 1) ≤ 2 ^ r := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) hjr'
  exact_mod_cast (le_trans hnat hpow)

theorem choose_card_le_pow_succ {S j r : ℕ} (hjr : j ≤ r) :
    (S.choose j : ℝ) ≤ ((S + 1 : ℕ) : ℝ) ^ r := by
  have h1 : S.choose j ≤ S ^ j := Nat.choose_le_pow S j
  have h2 : S ^ j ≤ (S + 1) ^ j := pow_le_pow_left' (Nat.le_succ S) j
  have h3 : (S + 1) ^ j ≤ (S + 1) ^ r :=
    pow_le_pow_right' (Nat.succ_le_succ (Nat.zero_le S)) hjr
  exact_mod_cast (h1.trans (h2.trans h3))

theorem ahlLayer_nonneg (κ : ℝ) (X j L : ℕ) : 0 ≤ ahlLayer κ X j L := by
  unfold ahlLayer
  exact sum_nonneg fun _ _ => posPart_nonneg _

theorem ahlBudget_nonneg (κ d0 : ℝ) (X : ℕ) : 0 ≤ ahlBudget κ d0 X := by
  unfold ahlBudget
  split_ifs
  · exact zero_le_one
  · refine mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) ?_
    exact sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (ahlLayer_nonneg κ X j _)

/-! ### Profile inside Kuperberg's range -/

/-- Diameter, order and covering constraints needed to subtract
Kuperberg at `X` and `2X` on every `H ⊆ Ω_X` of size `≤ r`. -/
def ProfileFits (κ d0 : ℝ) (X : ℕ) : Prop :=
  16 ≤ X ∧
    (profileS κ X : ℝ) ≤ Real.log (X : ℝ) ^ 2 ∧
      (profileR (profileL κ X) d0 + 1 : ℝ) ≤ Real.log (Real.log (X : ℝ)) ^ 3 ∧
        profileR (profileL κ X) d0 + 1 ≤ X

theorem tendsto_windowG_atTop : Tendsto windowG atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards with X
  exact le_max_left _ _

private theorem tendsto_log_div_id :
    Tendsto (fun g : ℝ => Real.log g / g) atTop (nhds 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)

private theorem tendsto_inv_id :
    Tendsto (fun g : ℝ => (1 : ℝ) / g) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (1 : ℝ)

private theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hx' : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsq : x ≤ x ^ 2 := le_self_pow₀ hx (by omega : 2 ≠ 0)
  have : Real.sqrt x ≤ Real.sqrt (x ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hx0] at this

private theorem eventually_four_profile_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ g : ℝ in atTop,
      1 ≤ Real.log g ∧
        1 ≤ κ * Real.log g ∧
          4 * (κ * Real.log g + Real.sqrt (κ * Real.log g) + 1) ≤ g := by
  have hsum :
      Tendsto (fun g : ℝ => (8 * κ) * (Real.log g / g) + 4 / g) atTop (nhds 0) := by
    have h1 := (tendsto_log_div_id.const_mul (8 * κ))
    have h2 : Tendsto (fun g : ℝ => (4 : ℝ) / g) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (4 : ℝ)
    simpa using h1.add h2
  have hthr : 0 < max (1 : ℝ) (1 / κ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (Real.exp (max 1 (1 / κ))),
    hsum.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with g hg0 hgexp hball
  have hg1 : 1 < g :=
    (Real.one_lt_exp_iff.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_max_left 1 (1 / κ)))).trans_le hgexp
  have hlog1 : 1 ≤ Real.log g :=
    (Real.le_log_iff_exp_le (lt_trans (by norm_num) hg1)).mpr
      (le_trans (Real.exp_le_exp.mpr (le_max_left 1 (1 / κ))) hgexp)
  have hκlog : 1 ≤ κ * Real.log g := by
    have : 1 / κ ≤ Real.log g :=
      (Real.le_log_iff_exp_le (lt_trans (by norm_num) hg1)).mpr
        (le_trans (Real.exp_le_exp.mpr (le_max_right 1 (1 / κ))) hgexp)
    calc
      (1 : ℝ) = κ * (1 / κ) := by field_simp [hκ.ne']
      _ ≤ κ * Real.log g := mul_le_mul_of_nonneg_left this hκ.le
  have hsqrt : Real.sqrt (κ * Real.log g) ≤ κ * Real.log g :=
    sqrt_le_self_of_one_le hκlog
  have hnn :
      0 ≤ (8 * κ) * (Real.log g / g) + 4 / g :=
    add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hκ.le)
        (div_nonneg (le_trans (by norm_num) hlog1) hg0.le))
      (div_nonneg (by norm_num) hg0.le)
  have hlt : (8 * κ) * (Real.log g / g) + 4 / g < 1 := by
    have : |((8 * κ) * (Real.log g / g) + 4 / g) - 0| < 1 := hball
    rw [sub_zero, abs_of_nonneg hnn] at this
    exact this
  have hmain : 8 * κ * Real.log g + 4 < g := by
    have heq : ((8 * κ) * Real.log g + 4) / g =
        (8 * κ) * (Real.log g / g) + 4 / g := by
      field_simp [hg0.ne']
    exact (div_lt_one hg0).mp (heq.symm ▸ hlt)
  have : 4 * (κ * Real.log g + Real.sqrt (κ * Real.log g) + 1) ≤
      8 * κ * Real.log g + 4 := by
    have := add_le_add_left hsqrt (κ * Real.log g + 1)
    linarith
  exact ⟨hlog1, hκlog, this.trans hmain.le⟩

private theorem eventually_linear_le_cube {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ t : ℝ in atTop, A * t + B ≤ t ^ 3 := by
  have h1 : Tendsto (fun t : ℝ => A / t ^ 2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_pow_atTop (by omega : (2 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul A
  have h2 : Tendsto (fun t : ℝ => B / t ^ 3) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_pow_atTop (by omega : (3 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul B
  have hsum : Tendsto (fun t : ℝ => A / t ^ 2 + B / t ^ 3) atTop (nhds 0) := by
    simpa using h1.add h2
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hsum.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with t ht0 hball
  have hnn :
      0 ≤ A / t ^ 2 + B / t ^ 3 :=
    add_nonneg (div_nonneg hA (pow_nonneg ht0.le 2)) (div_nonneg hB (pow_nonneg ht0.le 3))
  have hlt : A / t ^ 2 + B / t ^ 3 < 1 := by
    have : |(A / t ^ 2 + B / t ^ 3) - 0| < 1 := hball
    rwa [sub_zero, abs_of_nonneg hnn] at this
  have hdiv : (A * t + B) / t ^ 3 = A / t ^ 2 + B / t ^ 3 := by
    have ht : t ≠ 0 := ht0.ne'
    have hpow : t ^ 3 = t * t ^ 2 := by ring
    rw [add_div, hpow, mul_comm A t, mul_div_mul_left A (t ^ 2) ht]
  have : (A * t + B) / t ^ 3 < 1 := by
    rwa [hdiv]
  exact (div_lt_one (pow_pos ht0 3)).mp this |>.le

private theorem eventually_r_cast_le {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ∀ᶠ g : ℝ in atTop,
      (1 + d0) * (κ * Real.log g + Real.sqrt (κ * Real.log g) + 1) + 3 ≤
        Real.log g ^ 3 := by
  have hA : 0 ≤ (1 + d0) * 2 * κ :=
    mul_nonneg (mul_nonneg (add_nonneg zero_le_one hd0.le) (by norm_num)) hκ.le
  have hB : 0 ≤ (1 + d0) + 3 :=
    add_nonneg (add_nonneg zero_le_one hd0.le) (by norm_num)
  filter_upwards [eventually_four_profile_le hκ,
    Real.tendsto_log_atTop.eventually (eventually_linear_le_cube hA hB)] with g hg hcube
  have hκlog := hg.2.1
  have hsqrt : Real.sqrt (κ * Real.log g) ≤ κ * Real.log g :=
    sqrt_le_self_of_one_le hκlog
  have hfac : 0 ≤ 1 + d0 := add_nonneg zero_le_one hd0.le
  have hLHS :
      (1 + d0) * (κ * Real.log g + Real.sqrt (κ * Real.log g) + 1) + 3 ≤
        (1 + d0) * (2 * κ * Real.log g + 1) + 3 := by
    have : κ * Real.log g + Real.sqrt (κ * Real.log g) + 1 ≤
        2 * κ * Real.log g + 1 := by linarith
    linarith [mul_le_mul_of_nonneg_left this hfac]
  have hlin : (1 + d0) * (2 * κ * Real.log g + 1) + 3 =
      ((1 + d0) * 2 * κ) * Real.log g + ((1 + d0) + 3) := by ring
  rw [hlin] at hLHS
  exact hLHS.trans hcube

private theorem eventually_loglog_pow_lt :
    ∀ᶠ X : ℕ in atTop, Real.log (Real.log (X : ℝ)) ^ 3 < (X : ℝ) := by
  have hcub : Tendsto (fun x : ℝ => Real.log x ^ 3 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 (by norm_num)
  have hnat := hcub.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 16,
    hnat.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with X hX hball
  have hxpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 16) hX)
  have hlog : 0 < Real.log (X : ℝ) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_log_of_three_le (le_trans (by norm_num) hX))
  have hll : 0 < Real.log (Real.log (X : ℝ)) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_log_log_of_sixteen_le hX)
  have hle : Real.log (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) :=
    (Real.log_le_sub_one_of_pos hlog).trans (by linarith)
  have hpow : Real.log (Real.log (X : ℝ)) ^ 3 ≤ Real.log (X : ℝ) ^ 3 :=
    pow_le_pow_left₀ hll.le hle 3
  have hnn : 0 ≤ Real.log (X : ℝ) ^ 3 / (X : ℝ) :=
    div_nonneg (pow_nonneg hlog.le 3) hxpos.le
  have hlt : Real.log (X : ℝ) ^ 3 / (X : ℝ) < 1 := by
    have : |(Real.log (X : ℝ) ^ 3 / (X : ℝ)) - 0| < 1 := hball
    rwa [sub_zero, abs_of_nonneg hnn] at this
  have : Real.log (X : ℝ) ^ 3 < (X : ℝ) := (div_lt_one hxpos).mp hlt
  exact hpow.trans_lt this

theorem eventually_profileFits {κ d0 : ℝ} (hκ : 0 < κ) (hd0 : 0 < d0) :
    ∀ᶠ X : ℕ in atTop, ProfileFits κ d0 X := by
  filter_upwards [eventually_ge_atTop 16,
    tendsto_windowG_atTop.eventually (eventually_four_profile_le hκ),
    tendsto_windowG_atTop.eventually (eventually_r_cast_le hκ hd0),
    eventually_loglog_pow_lt] with X hX hfours hrs hcub
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hGeq : windowG X = Real.log (X : ℝ) := windowG_eq_log hX3
  have hGnn : 0 ≤ windowG X := le_trans (by norm_num : (0 : ℝ) ≤ 1) (windowG_one_le X)
  have hL := profileL_cast_le hκ.le X
  have hS := profileS_cast_le κ X
  have hSle : (profileS κ X : ℝ) ≤ Real.log (X : ℝ) ^ 2 := by
    have h4 : 4 * (κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) + 1) ≤
        windowG X := hfours.2.2
    have hmul : 4 * (profileL κ X : ℝ) * windowG X ≤
        4 * (κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) + 1) *
          windowG X :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL (by norm_num)) hGnn
    have : 4 * (κ * Real.log (windowG X) + Real.sqrt (κ * Real.log (windowG X)) + 1) *
        windowG X ≤ windowG X * windowG X :=
      mul_le_mul_of_nonneg_right h4 hGnn
    calc
      (profileS κ X : ℝ) ≤ 4 * (profileL κ X : ℝ) * windowG X := hS
      _ ≤ windowG X * windowG X := hmul.trans this
      _ = Real.log (X : ℝ) ^ 2 := by
        rw [hGeq]
        ring
  have hR := profileR_cast_le (profileL κ X) hd0.le
  have hr1 : (profileR (profileL κ X) d0 : ℝ) + 1 ≤
      Real.log (Real.log (X : ℝ)) ^ 3 := by
    have hfac : 0 ≤ 1 + d0 := add_nonneg zero_le_one hd0.le
    have hrbound : (profileR (profileL κ X) d0 : ℝ) + 1 ≤
        (1 + d0) * (profileL κ X : ℝ) + 3 := by
      linarith [hR]
    have hL' : (1 + d0) * (profileL κ X : ℝ) + 3 ≤
        (1 + d0) * (κ * Real.log (windowG X) +
          Real.sqrt (κ * Real.log (windowG X)) + 1) + 3 := by
      linarith [mul_le_mul_of_nonneg_left hL hfac]
    have heq : Real.log (windowG X) ^ 3 = Real.log (Real.log (X : ℝ)) ^ 3 := by
      rw [hGeq]
    exact (hrbound.trans (hL'.trans hrs)).trans_eq heq
  have hrX : profileR (profileL κ X) d0 + 1 ≤ X := by
    have hcast : (profileR (profileL κ X) d0 : ℝ) + 1 < (X : ℝ) :=
      hr1.trans_lt hcub
    exact_mod_cast hcast.le
  exact ⟨hX, hSle, hr1, hrX⟩

/-! ### Kuperberg error on a window tuple -/

private theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc
    |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

private theorem posPart_signed_error_le_abs (n : ℕ) (e : ℝ) :
    (((-1 : ℝ) ^ n) * e)⁺ ≤ |e| := by
  have h := posPart_le_abs (((-1 : ℝ) ^ n) * e)
  have habs : |((-1 : ℝ) ^ n) * e| = |e| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rwa [habs] at h

private theorem log_le_log_two_mul {X : ℕ} (hX : 16 ≤ X) :
    Real.log (X : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
  have hxpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 16) hX)
  have hle : (X : ℝ) ≤ ((2 * X : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
  exact Real.log_le_log hxpos hle

private theorem kuperberg_err_singleton {ε K : ℝ}
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε))
    {x : ℕ} (hx : 16 ≤ x) :
    |(Nat.primeCounting x : ℝ) - hlMain (x : ℝ) {0}| ≤ K * (x : ℝ) ^ (1 - ε) := by
  have hdiam : ∀ h ∈ ({0} : Finset ℕ), (h : ℝ) ≤ Real.log (x : ℝ) ^ 2 := by
    intro h hh
    simp only [mem_singleton] at hh
    subst hh
    simpa using sq_nonneg (Real.log (x : ℝ))
  have hcard : (({0} : Finset ℕ).card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 := by
    rw [card_singleton]
    exact_mod_cast (one_le_log_log_pow_three hx)
  have := hbound x {0} hx hdiam hcard hlAdmissible_singleton_zero
  simpa [hlCount_singleton_zero] using this

/-- Dyadic window error from subtracting Kuperberg at `2X` and `X`.
Mathlib Chebyshev does not give `N_X ≫ X / log X` (the constants cancel
on a dyadic interval), so the adapter uses the one-point case of
Kuperberg for the `N_X` lower bound. -/
theorem rooted_error_abs_le_kuperberg {ε K κ d0 : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε))
    {X : ℕ} (hfit : ProfileFits κ d0 X) {H : Finset ℕ}
    (hH : H ⊆ windowOmega κ X)
    (hj : H.card ≤ profileR (profileL κ X) d0) :
    |(rootedTupleCount X H : ℝ) - rootedMainTerm X H| ≤
      K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) := by
  have hX := hfit.1
  have h0 : 0 ∉ H := zero_notMem_of_subset_windowOmega hH
  have hcardE : (insert 0 H).card = H.card + 1 := card_insert_of_notMem h0
  have hcardle : (insert 0 H).card ≤ X := by
    have : H.card + 1 ≤ profileR (profileL κ X) d0 + 1 := Nat.succ_le_succ hj
    rw [hcardE]
    exact this.trans hfit.2.2.2
  by_cases hadm : hlAdmissible (insert 0 H)
  · have herr := rooted_error_eq (X := X) h0
    rw [herr]
    refine (abs_sub_le_add _ _).trans ?_
    have hdiamX : ∀ h ∈ insert 0 H, (h : ℝ) ≤ Real.log (X : ℝ) ^ 2 := by
      intro h hh
      rcases mem_insert.mp hh with rfl | hH'
      · simpa using sq_nonneg (Real.log (X : ℝ))
      · have : (h : ℝ) ≤ (profileS κ X : ℝ) :=
          Nat.cast_le.mpr (le_profileS_of_mem_windowOmega (hH hH'))
        exact this.trans hfit.2.1
    have hcardRX : ((insert 0 H).card : ℝ) ≤ Real.log (Real.log (X : ℝ)) ^ 3 := by
      have : ((insert 0 H).card : ℝ) = (H.card + 1 : ℕ) := by
        rw [hcardE]
      rw [this, Nat.cast_add_one]
      have : (H.card : ℝ) + 1 ≤ (profileR (profileL κ X) d0 : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ hj
      exact this.trans hfit.2.2.1
    have hXerr := hbound X (insert 0 H) hX hdiamX hcardRX hadm
    have h2X : 16 ≤ 2 * X := le_trans hX (by omega)
    have hlogle := log_le_log_two_mul hX
    have hlogpos : 0 < Real.log (X : ℝ) :=
      lt_trans (by norm_num : (0 : ℝ) < 1)
        (one_lt_log_of_three_le (le_trans (by norm_num) hX))
    have hdiam2 : ∀ h ∈ insert 0 H, (h : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) ^ 2 := by
      intro h hh
      have h1 := hdiamX h hh
      have hsq : Real.log (X : ℝ) ^ 2 ≤ Real.log ((2 * X : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ hlogpos.le hlogle 2
      exact h1.trans hsq
    have hcardR2 : ((insert 0 H).card : ℝ) ≤
        Real.log (Real.log ((2 * X : ℕ) : ℝ)) ^ 3 := by
      have hll : Real.log (Real.log (X : ℝ)) ≤
          Real.log (Real.log ((2 * X : ℕ) : ℝ)) :=
        Real.log_le_log hlogpos hlogle
      have hllpos : 0 ≤ Real.log (Real.log (X : ℝ)) :=
        le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1)
          (one_lt_log_log_of_sixteen_le hX))
      have : Real.log (Real.log (X : ℝ)) ^ 3 ≤
          Real.log (Real.log ((2 * X : ℕ) : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hllpos hll 3
      exact hcardRX.trans this
    have h2err := hbound (2 * X) (insert 0 H) h2X hdiam2 hcardR2 hadm
    have h2cast : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by simp
    have h2err' :
        |(hlCount (2 * X) (insert 0 H) : ℝ) -
            hlMain (2 * (X : ℝ)) (insert 0 H)| ≤
          K * (2 * (X : ℝ)) ^ (1 - ε) := by
      simpa [h2cast] using h2err
    have hsum :
        K * (2 * (X : ℝ)) ^ (1 - ε) + K * (X : ℝ) ^ (1 - ε) =
          K * ((2 * (X : ℝ)) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) := by ring
    exact (add_le_add h2err' hXerr).trans_eq hsum
  · have hz := rooted_error_eq_zero_of_not_hlAdmissible h0 hadm hcardle
    rw [hz, abs_zero]
    exact mul_nonneg hK (add_nonneg
      (Real.rpow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg X)) _)
      (Real.rpow_nonneg (Nat.cast_nonneg X) _))

/-! ### Layer, `N_X`, envelope, and `AHL` -/

theorem ahlLayer_le_kuperberg {ε K κ d0 : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε))
    {X j L : ℕ} (hfit : ProfileFits κ d0 X)
    (hj : j ≤ profileR (profileL κ X) d0) :
    ahlLayer κ X j L ≤
      ((profileS κ X).choose j : ℝ) *
        (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))) := by
  refine ahlLayer_le_choose_mul κ X j L ?_ ?_
  · exact mul_nonneg hK
      (add_nonneg
        (Real.rpow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg X)) _)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _))
  · intro H hH hcard
    exact (posPart_signed_error_le_abs (j - L + 1) _).trans
      (rooted_error_abs_le_kuperberg hK hbound hfit hH (hcard.symm ▸ hj))

theorem windowNX_ge_kuperberg {ε K : ℝ}
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε))
    {X : ℕ} (hX : 16 ≤ X) :
    (X : ℝ) / Real.log (2 * (X : ℝ)) -
        K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) ≤
      (windowNX X : ℝ) := by
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hπ : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) :=
    Nat.monotone_primeCounting (by omega : X ≤ 2 * X)
  rw [windowNX, Nat.cast_sub hπ]
  set a := (Nat.primeCounting (2 * X) : ℝ)
  set b := (Nat.primeCounting X : ℝ)
  set ma := hlMain (2 * X : ℝ) {0}
  set mb := hlMain (X : ℝ) {0}
  have ha : ma - |a - ma| ≤ a := by linarith [neg_le_abs (a - ma)]
  have hb : -mb - |b - mb| ≤ -b := by linarith [le_abs_self (b - mb)]
  have hdiff : a - b ≥ (ma - mb) - |a - ma| - |b - mb| := by linarith
  have hmain : ma - mb = hlIntegral (2 * X : ℝ) 1 - hlIntegral (X : ℝ) 1 := by
    simp [ma, mb, hlMain_singleton_zero]
  have hge : (X : ℝ) / Real.log (2 * (X : ℝ)) ≤ ma - mb := by
    rw [hmain]
    exact hlIntegral_one_dyadic_ge hX3
  have herr2 := kuperberg_err_singleton hbound (le_trans hX (by omega : X ≤ 2 * X))
  have herr1 := kuperberg_err_singleton hbound hX
  have herr2' : |a - ma| ≤ K * (2 * X : ℝ) ^ (1 - ε) := by
    simpa [a, ma] using herr2
  have herr1' : |b - mb| ≤ K * (X : ℝ) ^ (1 - ε) := by
    simpa [b, mb] using herr1
  linarith [hdiff, hge, herr2', herr1']

private theorem tendsto_log_div_rpow {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (nhds 0) := by
  have hbase : Tendsto (fun y : ℝ => Real.log y / y) atTop (nhds 0) :=
    tendsto_log_div_id
  have hcomp := hbase.comp (tendsto_rpow_atTop hε)
  have hmul : Tendsto (fun x : ℝ => ε⁻¹ * (Real.log (x ^ ε) / x ^ ε)) atTop (nhds 0) := by
    simpa using hcomp.const_mul ε⁻¹
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hε0 : ε ≠ 0 := hε.ne'
  rw [Real.log_rpow hx]
  field_simp [hε0]

private theorem tendsto_log_two_mul_div_rpow {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => Real.log (2 * x) / x ^ ε) atTop (nhds 0) := by
  have hlog := tendsto_log_div_rpow hε
  have hconst : Tendsto (fun x : ℝ => Real.log 2 * x ^ (-ε)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hε).const_mul (Real.log 2)
  have h2 : Tendsto (fun x : ℝ => Real.log 2 / x ^ ε) atTop (nhds 0) := by
    apply hconst.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hsum : Tendsto (fun x : ℝ => Real.log 2 / x ^ ε + Real.log x / x ^ ε)
      atTop (nhds 0) := by
    simpa using h2.add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]

theorem eventually_windowNX_ge_half {ε K : ℝ} (hε : 0 < ε) (hKpos : 0 < K)
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε)) :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) ≤ (windowNX X : ℝ) := by
  have hDpos : 0 < K * ((2 : ℝ) ^ (1 - ε) + 1) := by
    have : 0 < (2 : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_pos hKpos (add_pos_of_pos_of_nonneg this (by norm_num))
  have hratio : Tendsto
      (fun x : ℝ => (2 * (K * ((2 : ℝ) ^ (1 - ε) + 1))) * (Real.log (2 * x) / x ^ ε))
      atTop (nhds 0) := by
    simpa using
      (tendsto_log_two_mul_div_rpow hε).const_mul (2 * (K * ((2 : ℝ) ^ (1 - ε) + 1)))
  filter_upwards [eventually_ge_atTop 16,
    (hratio.comp tendsto_natCast_atTop_atTop).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with X hX hball
  have hge := windowNX_ge_kuperberg hbound hX
  have hxpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 16) hX)
  have hlog : 0 < Real.log (2 * (X : ℝ)) := by
    have : 1 < 2 * (X : ℝ) := by
      have : (1 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 16) hX)
      linarith
    exact Real.log_pos this
  have h2Xpow : (2 * X : ℝ) ^ (1 - ε) = (2 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε) := by
    rw [two_mul_cast, Real.mul_rpow (by norm_num) hxpos.le]
  have hErr :
      K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) =
        (K * ((2 : ℝ) ^ (1 - ε) + 1)) * (X : ℝ) ^ (1 - ε) := by
    rw [h2Xpow]
    ring
  rw [hErr] at hge
  set D := K * ((2 : ℝ) ^ (1 - ε) + 1)
  have hD : 0 < D := hDpos
  have hnn : 0 ≤ (2 * D) * (Real.log (2 * (X : ℝ)) / (X : ℝ) ^ ε) :=
    mul_nonneg (mul_nonneg (by norm_num) hD.le)
      (div_nonneg (le_of_lt hlog) (Real.rpow_nonneg hxpos.le _))
  have hlt : (2 * D) * (Real.log (2 * (X : ℝ)) / (X : ℝ) ^ ε) < 1 := by
    have : |((2 * D) * (Real.log (2 * (X : ℝ)) / (X : ℝ) ^ ε)) - 0| < 1 := hball
    rwa [sub_zero, abs_of_nonneg hnn] at this
  have hxε : 0 < (X : ℝ) ^ ε := Real.rpow_pos_of_pos hxpos _
  have hpow : 2 * D * Real.log (2 * (X : ℝ)) ≤ (X : ℝ) ^ ε := by
    have : (2 * D * Real.log (2 * (X : ℝ))) / (X : ℝ) ^ ε < 1 := by
      convert hlt using 1
      field_simp [hxε.ne']
    exact (div_lt_one hxε).mp this |>.le
  have hsmall : D * (X : ℝ) ^ (1 - ε) ≤
      (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) := by
    have hden : 0 < 2 * Real.log (2 * (X : ℝ)) := mul_pos (by norm_num) hlog
    refine (le_div_iff₀ hden).mpr ?_
    have hrpow : (X : ℝ) ^ ε * (X : ℝ) ^ (1 - ε) = (X : ℝ) := by
      rw [← Real.rpow_add hxpos, add_comm, sub_add_cancel, Real.rpow_one]
    have : (2 * D * Real.log (2 * (X : ℝ))) * (X : ℝ) ^ (1 - ε) ≤
        (X : ℝ) ^ ε * (X : ℝ) ^ (1 - ε) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hxpos.le _)
    calc
      D * (X : ℝ) ^ (1 - ε) * (2 * Real.log (2 * (X : ℝ))) =
        (2 * D * Real.log (2 * (X : ℝ))) * (X : ℝ) ^ (1 - ε) := by ring
      _ ≤ (X : ℝ) ^ ε * (X : ℝ) ^ (1 - ε) := this
      _ = (X : ℝ) := hrpow
  have : (X : ℝ) / Real.log (2 * (X : ℝ)) -
      (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) ≤ (windowNX X : ℝ) := by
    linarith [hge, hsmall]
  have hhalf : (X : ℝ) / Real.log (2 * (X : ℝ)) -
      (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) =
      (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) := by
    field_simp [hlog.ne']
    ring
  rwa [hhalf] at this

theorem ahlBudget_le_kuperberg_envelope {ε K κ d0 : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ (x : ℕ) (E : Finset ℕ),
      16 ≤ x →
        (∀ h ∈ E, (h : ℝ) ≤ Real.log (x : ℝ) ^ 2) →
          (E.card : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 3 →
            hlAdmissible E →
              |(hlCount x E : ℝ) - hlMain (x : ℝ) E| ≤ K * (x : ℝ) ^ (1 - ε))
    {X : ℕ} (hfit : ProfileFits κ d0 X)
    (hN : (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) ≤ (windowNX X : ℝ)) :
    ahlBudget κ d0 X ≤
      (2 * K * ((2 : ℝ) ^ (1 - ε) + 1) *
          Real.log (2 * (X : ℝ)) *
          (profileR (profileL κ X) d0 + 1 : ℝ) *
          (2 * ((profileS κ X : ℝ) + 1)) ^ profileR (profileL κ X) d0) *
        (X : ℝ) ^ (-ε) := by
  set L := profileL κ X
  set r := profileR L d0
  set S := profileS κ X
  have hX := hfit.1
  have hxpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 16) hX)
  have hlog : 0 < Real.log (2 * (X : ℝ)) := by
    have : 1 < 2 * (X : ℝ) := by
      have : (1 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 16) hX)
      linarith
    exact Real.log_pos this
  have hNpos : 0 < (windowNX X : ℝ) :=
    lt_of_lt_of_le (div_pos hxpos (mul_pos (by norm_num) hlog)) hN
  have hNne : windowNX X ≠ 0 := (Nat.cast_pos.mp hNpos).ne'
  have hinv : (1 : ℝ) / (windowNX X : ℝ) ≤
      (2 * Real.log (2 * (X : ℝ))) / (X : ℝ) := by
    have hdenpos : 0 < (X : ℝ) / (2 * Real.log (2 * (X : ℝ))) :=
      div_pos hxpos (mul_pos (by norm_num) hlog)
    have := one_div_le_one_div_of_le hdenpos hN
    have hrew : (1 : ℝ) / ((X : ℝ) / (2 * Real.log (2 * (X : ℝ)))) =
        (2 * Real.log (2 * (X : ℝ))) / (X : ℝ) := by
      field_simp [hxpos.ne', hlog.ne']
    rwa [hrew] at this
  have hErr0 : 0 ≤ K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)) :=
    mul_nonneg hK
      (add_nonneg
        (Real.rpow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg X)) _)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _))
  have hterm : ∀ j ∈ Icc L r,
      ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤
        (2 : ℝ) ^ r * ((S : ℝ) + 1) ^ r *
          (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))) := by
    intro j hj
    have hjr : j ≤ r := (mem_Icc.mp hj).2
    have hlayer := ahlLayer_le_kuperberg (L := L) hK hbound hfit hjr
    have hch := choose_le_two_pow_of_le (L := L) hjr
    have hSj := choose_card_le_pow_succ (S := S) hjr
    have hS1 : ((S + 1 : ℕ) : ℝ) = (S : ℝ) + 1 := Nat.cast_add_one _
    have hleft : ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤
        (2 : ℝ) ^ r * (S.choose j : ℝ) *
          (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))) := by
      have := mul_le_mul hch hlayer (ahlLayer_nonneg _ _ _ _) (pow_nonneg (by norm_num) _)
      linarith
    have hright : (S.choose j : ℝ) ≤ ((S : ℝ) + 1) ^ r := by
      simpa [hS1] using hSj
    calc
      ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤
          (2 : ℝ) ^ r * (S.choose j : ℝ) *
            (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))) := hleft
      _ = (2 : ℝ) ^ r * ((S.choose j : ℝ) *
            (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)))) := by ring
      _ ≤ (2 : ℝ) ^ r * (((S : ℝ) + 1) ^ r *
            (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hright hErr0)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r)
      _ = (2 : ℝ) ^ r * ((S : ℝ) + 1) ^ r *
            (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))) := by ring
  have hform : ahlBudget κ d0 X =
      (1 / (windowNX X : ℝ)) *
        ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L := by
    unfold ahlBudget
    simp [hNne, L, r]
  rw [hform]
  have hsum := sum_le_card_nsmul (Icc L r)
    (fun j => ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L)
    ((2 : ℝ) ^ r * ((S : ℝ) + 1) ^ r *
      (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)))) hterm
  have hcard : ((Icc L r).card : ℝ) ≤ (r + 1 : ℝ) := by
    have hceq : (Icc L r).card = r + 1 - L := Nat.card_Icc L r
    have hle : r + 1 - L ≤ r + 1 := Nat.sub_le _ _
    rw [hceq]
    exact_mod_cast hle
  have hU :
      (2 : ℝ) ^ r * ((S : ℝ) + 1) ^ r *
          (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))) =
        (2 * ((S : ℝ) + 1)) ^ r *
          (K * ((2 : ℝ) ^ (1 - ε) + 1) * (X : ℝ) ^ (1 - ε)) := by
    have h2Xpow : (2 * X : ℝ) ^ (1 - ε) = (2 : ℝ) ^ (1 - ε) * (X : ℝ) ^ (1 - ε) := by
      rw [two_mul_cast, Real.mul_rpow (by norm_num) hxpos.le]
    rw [h2Xpow, (mul_pow (2 : ℝ) ((S : ℝ) + 1) r).symm]
    ring
  have hxpow : (X : ℝ) ^ (1 - ε) / (X : ℝ) = (X : ℝ) ^ (-ε) := by
    have : -ε = (1 - ε) - 1 := by ring
    rw [this, Real.rpow_sub_one hxpos.ne']
  have hsum' : ∑ j ∈ Icc L r, ((j - 1).choose (L - 1) : ℝ) * ahlLayer κ X j L ≤
      (r + 1 : ℝ) * ((2 : ℝ) ^ r * ((S : ℝ) + 1) ^ r *
        (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε)))) := by
    have := hsum
    rw [nsmul_eq_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_right hcard
      (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_one) _)) hErr0))
  have hmul := mul_le_mul hinv hsum'
    (sum_nonneg fun _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (ahlLayer_nonneg _ _ _ _))
    (div_nonneg (mul_nonneg (by norm_num) hlog.le) hxpos.le)
  have halg :
      ((2 * Real.log (2 * (X : ℝ))) / (X : ℝ)) *
        ((r + 1 : ℝ) * ((2 : ℝ) ^ r * ((S : ℝ) + 1) ^ r *
          (K * ((2 * X : ℝ) ^ (1 - ε) + (X : ℝ) ^ (1 - ε))))) =
      (2 * K * ((2 : ℝ) ^ (1 - ε) + 1) * Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) *
          (2 * ((S : ℝ) + 1)) ^ r) * (X : ℝ) ^ (-ε) := by
    rw [hU]
    calc
      (2 * Real.log (2 * (X : ℝ)) / (X : ℝ)) *
          ((r + 1 : ℝ) * ((2 * ((S : ℝ) + 1)) ^ r *
            (K * ((2 : ℝ) ^ (1 - ε) + 1) * (X : ℝ) ^ (1 - ε)))) =
        (2 * K * ((2 : ℝ) ^ (1 - ε) + 1) * Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) *
            (2 * ((S : ℝ) + 1)) ^ r) * ((X : ℝ) ^ (1 - ε) / (X : ℝ)) := by
        field_simp [hxpos.ne']
      _ = (2 * K * ((2 : ℝ) ^ (1 - ε) + 1) * Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) *
            (2 * ((S : ℝ) + 1)) ^ r) * (X : ℝ) ^ (-ε) := by
        rw [hxpow]
  exact hmul.trans_eq halg

private theorem eventually_two_sq_le_pow_four :
    ∀ᶠ t : ℝ in atTop, 2 * (t ^ 2 + 1) ≤ t ^ 4 := by
  have h1 : Tendsto (fun t : ℝ => (2 : ℝ) / t ^ 2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_pow_atTop (by omega : (2 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul (2 : ℝ)
  have h2 : Tendsto (fun t : ℝ => (2 : ℝ) / t ^ 4) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_pow_atTop (by omega : (4 : ℕ) ≠ 0)).inv_tendsto_atTop).const_mul (2 : ℝ)
  have hsum : Tendsto (fun t : ℝ => (2 : ℝ) / t ^ 2 + 2 / t ^ 4) atTop (nhds 0) := by
    simpa using h1.add h2
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hsum.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with t ht0 hball
  have hnn : 0 ≤ (2 : ℝ) / t ^ 2 + 2 / t ^ 4 :=
    add_nonneg (div_nonneg (by norm_num) (pow_nonneg ht0.le 2))
      (div_nonneg (by norm_num) (pow_nonneg ht0.le 4))
  have hlt : (2 : ℝ) / t ^ 2 + 2 / t ^ 4 < 1 := by
    have : |((2 : ℝ) / t ^ 2 + 2 / t ^ 4) - 0| < 1 := hball
    rwa [sub_zero, abs_of_nonneg hnn] at this
  have ht : t ≠ 0 := ht0.ne'
  have hdiv : (2 * (t ^ 2 + 1)) / t ^ 4 = (2 : ℝ) / t ^ 2 + 2 / t ^ 4 := by
    have hpow : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    rw [mul_add, add_div, mul_one]
    have hA : 2 * t ^ 2 / t ^ 4 = (2 : ℝ) / t ^ 2 := by
      rw [hpow]
      field_simp [ht, pow_ne_zero 2 ht]
    rw [hA]
  exact (div_lt_one (pow_pos ht0 4)).mp (by rwa [hdiv]) |>.le

private theorem eventually_linlog_le_pow_four :
    ∀ᶠ u : ℝ in atTop, Real.log 2 + u + 3 * Real.log u ≤ u ^ 4 := by
  have hc : Tendsto (fun u : ℝ => Real.log 2 / u ^ 4) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega : (4 : ℕ) ≠ 0))
  have hid : Tendsto (fun u : ℝ => (1 : ℝ) / u ^ 3) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega : (3 : ℕ) ≠ 0))
  have hlog : Tendsto (fun u : ℝ => Real.log u / u ^ 4) atTop (nhds 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.log u / u) atTop (nhds 0) :=
      tendsto_log_div_id
    have h3 : Tendsto (fun u : ℝ => (u ^ 3)⁻¹) atTop (nhds 0) :=
      (tendsto_pow_atTop (by omega : (3 : ℕ) ≠ 0)).inv_tendsto_atTop
    have hmul : Tendsto (fun x : ℝ => Real.log x / x * (x ^ 3)⁻¹) atTop (nhds 0) := by
      simpa using h1.mul h3
    refine Tendsto.congr' ?_ hmul
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have : u ≠ 0 := hu.ne'
    field_simp [this, pow_ne_zero 3 this]
  have hfun : Tendsto (fun u : ℝ =>
      (Real.log 2 + u + 3 * Real.log u) / u ^ 4) atTop (nhds 0) := by
    have hsum : Tendsto
        (fun u : ℝ => Real.log 2 / u ^ 4 + (1 / u ^ 3 + 3 * (Real.log u / u ^ 4)))
        atTop (nhds 0) := by
      simpa using hc.add (hid.add (hlog.const_mul (3 : ℝ)))
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hu0 : u ≠ 0 := hu.ne'
    have hpow : u ^ 4 ≠ 0 := pow_ne_zero 4 hu0
    field_simp [hu0, hpow]
    ring
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hfun.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
    with u hu1 hball
  have hu0 : 0 < u := lt_trans (by norm_num) hu1
  have hlt : (Real.log 2 + u + 3 * Real.log u) / u ^ 4 < 1 :=
    (le_abs_self _).trans_lt (by
      have : |((Real.log 2 + u + 3 * Real.log u) / u ^ 4) - 0| < 1 := hball
      rwa [sub_zero] at this)
  exact (div_lt_one (pow_pos hu0 4)).mp hlt |>.le

private theorem log_two_mul_le_two_log {X : ℕ} (hX : 3 ≤ X) :
    Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
  have hx : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
  rw [Real.log_mul (by norm_num) hx.ne']
  have : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by norm_num)
      (Nat.cast_le.mpr (le_trans (by omega : 2 ≤ 3) hX))
  linarith

private theorem comb_envelope_le_exp {κ d0 : ℝ} {X : ℕ}
    (hfit : ProfileFits κ d0 X)
    (hsq : 2 * (Real.log (X : ℝ) ^ 2 + 1) ≤ Real.log (X : ℝ) ^ 4)
    (hlin : Real.log 2 + Real.log (Real.log (X : ℝ)) +
      3 * Real.log (Real.log (Real.log (X : ℝ))) ≤
        Real.log (Real.log (X : ℝ)) ^ 4) :
    Real.log (2 * (X : ℝ)) * (profileR (profileL κ X) d0 + 1 : ℝ) *
      (2 * ((profileS κ X : ℝ) + 1)) ^ profileR (profileL κ X) d0 ≤
    Real.exp (5 * Real.log (Real.log (X : ℝ)) ^ 4) := by
  set L := profileL κ X
  set r := profileR L d0
  set S := profileS κ X
  have hX := hfit.1
  have hX3 : 3 ≤ X := le_trans (by norm_num) hX
  have hlogX : 1 < Real.log (X : ℝ) := one_lt_log_of_three_le hX3
  have hll : 1 < Real.log (Real.log (X : ℝ)) := one_lt_log_log_of_sixteen_le hX
  have hS : (S : ℝ) ≤ Real.log (X : ℝ) ^ 2 := hfit.2.1
  have hr1 : (r + 1 : ℝ) ≤ Real.log (Real.log (X : ℝ)) ^ 3 := hfit.2.2.1
  have h2S : 2 * ((S : ℝ) + 1) ≤ Real.log (X : ℝ) ^ 4 := by
    have : 2 * ((S : ℝ) + 1) ≤ 2 * (Real.log (X : ℝ) ^ 2 + 1) := by linarith
    exact this.trans hsq
  have hbasepos : 0 < 2 * ((S : ℝ) + 1) := by
    have : 0 ≤ (S : ℝ) := Nat.cast_nonneg _
    linarith
  have hpowexp : (2 * ((S : ℝ) + 1)) ^ r =
      Real.exp ((r : ℝ) * Real.log (2 * ((S : ℝ) + 1))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbasepos, mul_comm]
  have hlogle : Real.log (2 * ((S : ℝ) + 1)) ≤
      4 * Real.log (Real.log (X : ℝ)) := by
    have hlogpos : 0 < Real.log (X : ℝ) := lt_trans (by norm_num) hlogX
    have hpowpos : 0 < Real.log (X : ℝ) ^ 4 := pow_pos hlogpos 4
    have := Real.log_le_log hbasepos h2S
    have hlogpow : Real.log (Real.log (X : ℝ) ^ 4) =
        4 * Real.log (Real.log (X : ℝ)) := Real.log_pow _ 4
    rwa [hlogpow] at this
  have hrlog : (r : ℝ) * Real.log (2 * ((S : ℝ) + 1)) ≤
      4 * Real.log (Real.log (X : ℝ)) ^ 4 := by
    have hr : (r : ℝ) ≤ Real.log (Real.log (X : ℝ)) ^ 3 := by
      have : (r : ℝ) ≤ (r + 1 : ℝ) := by linarith
      exact this.trans hr1
    have hnn : 0 ≤ Real.log (2 * ((S : ℝ) + 1)) := Real.log_nonneg (by linarith)
    have := mul_le_mul hr hlogle hnn (pow_nonneg (le_of_lt (lt_trans (by norm_num) hll)) 3)
    have : Real.log (Real.log (X : ℝ)) ^ 3 * (4 * Real.log (Real.log (X : ℝ))) =
        4 * Real.log (Real.log (X : ℝ)) ^ 4 := by ring
    linarith
  have hexp : (2 * ((S : ℝ) + 1)) ^ r ≤
      Real.exp (4 * Real.log (Real.log (X : ℝ)) ^ 4) := by
    rw [hpowexp]
    exact Real.exp_le_exp.mpr hrlog
  have hpre : Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) ≤
      2 * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) ^ 3 := by
    have h1 := log_two_mul_le_two_log hX3
    have hnn : 0 ≤ (r : ℝ) + 1 := add_nonneg (Nat.cast_nonneg _) zero_le_one
    exact mul_le_mul h1 hr1 hnn (mul_nonneg (by norm_num) (le_of_lt (lt_trans (by norm_num) hlogX)))
  have hprodpos : 0 < 2 * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) ^ 3 :=
    mul_pos (mul_pos (by norm_num) (lt_trans (by norm_num) hlogX)) (pow_pos (lt_trans (by norm_num) hll) 3)
  have hlogprod : Real.log (2 * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) ^ 3) =
      Real.log 2 + Real.log (Real.log (X : ℝ)) +
        3 * Real.log (Real.log (Real.log (X : ℝ))) := by
    have hx0 : 0 < Real.log (X : ℝ) := lt_trans (by norm_num) hlogX
    have hll0 : 0 < Real.log (Real.log (X : ℝ)) := lt_trans (by norm_num) hll
    have hre : 2 * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) ^ 3 =
        2 * (Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) ^ 3) := by ring
    rw [hre, Real.log_mul (by norm_num) (mul_pos hx0 (pow_pos hll0 3)).ne',
      Real.log_mul hx0.ne' (pow_pos hll0 3).ne', Real.log_pow]
    ring
  have hpreexp : 2 * Real.log (X : ℝ) * Real.log (Real.log (X : ℝ)) ^ 3 ≤
      Real.exp (Real.log (Real.log (X : ℝ)) ^ 4) := by
    have := (Real.log_le_iff_le_exp hprodpos).mp (hlogprod.symm ▸ hlin)
    exact this
  have : Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) * (2 * ((S : ℝ) + 1)) ^ r ≤
      Real.exp (Real.log (Real.log (X : ℝ)) ^ 4) *
        Real.exp (4 * Real.log (Real.log (X : ℝ)) ^ 4) := by
    have h1X : 1 < 2 * (X : ℝ) := by
      have : (1 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 16) hX)
      linarith
    have hnn1 : 0 ≤ Real.log (2 * (X : ℝ)) * (r + 1 : ℝ) :=
      mul_nonneg (le_of_lt (Real.log_pos h1X))
        (add_nonneg (Nat.cast_nonneg r) zero_le_one)
    exact mul_le_mul (hpre.trans hpreexp) hexp
      (pow_nonneg (le_of_lt hbasepos) _) (Real.exp_nonneg _)
  have hsumexp : Real.exp (Real.log (Real.log (X : ℝ)) ^ 4) *
      Real.exp (4 * Real.log (Real.log (X : ℝ)) ^ 4) =
      Real.exp (5 * Real.log (Real.log (X : ℝ)) ^ 4) := by
    rw [← Real.exp_add]
    ring_nf
  exact this.trans_eq hsumexp

private theorem tendsto_exp_loglog_pow_mul_rpow_neg {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    Tendsto (fun x : ℝ => Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε))
      atTop (nhds 0) := by
  have hfrac : Tendsto (fun x : ℝ => Real.log (Real.log x) ^ 4 / Real.log x)
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 (by norm_num)).comp
      Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    simp [mul_one, add_zero]
  have hAfrac : Tendsto
      (fun x : ℝ => A * (Real.log (Real.log x) ^ 4 / Real.log x)) atTop (nhds 0) := by
    simpa using hfrac.const_mul A
  have hhalf : 0 < ε / 2 := half_pos hε
  have hle : ∀ᶠ x : ℝ in atTop,
      Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε) ≤ x ^ (-(ε / 2)) := by
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1)),
      hAfrac.eventually (Metric.ball_mem_nhds (0 : ℝ) hhalf)] with x hxexp hball
    have hx0 : 0 < x := (Real.exp_pos _).trans hxexp
    have hlogx : Real.exp 1 < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr hxexp
    have hlogx0 : 0 < Real.log x := (Real.exp_pos _).trans hlogx
    have hll1 : 1 < Real.log (Real.log x) := (Real.lt_log_iff_exp_lt hlogx0).mpr hlogx
    have hllpos : 0 < Real.log (Real.log x) := lt_trans (by norm_num) hll1
    have hfracnn : 0 ≤ Real.log (Real.log x) ^ 4 / Real.log x :=
      div_nonneg (pow_nonneg hllpos.le 4) hlogx0.le
    have hAnn : 0 ≤ A * (Real.log (Real.log x) ^ 4 / Real.log x) :=
      mul_nonneg hA hfracnn
    have hlt : A * (Real.log (Real.log x) ^ 4 / Real.log x) < ε / 2 :=
      (le_abs_self _).trans_lt (by
        have : |(A * (Real.log (Real.log x) ^ 4 / Real.log x)) - 0| < ε / 2 := hball
        rwa [sub_zero] at this)
    have hcmp : A * Real.log (Real.log x) ^ 4 ≤ (ε / 2) * Real.log x := by
      have : A * Real.log (Real.log x) ^ 4 / Real.log x < ε / 2 := by
        convert hlt using 1
        field_simp [hlogx0.ne']
      exact (div_lt_iff₀ hlogx0).mp this |>.le
    have hxpow : x ^ (-ε) = Real.exp (Real.log x * (-ε)) :=
      Real.rpow_def_of_pos hx0 (-ε)
    have hLHS : Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε) =
        Real.exp (A * Real.log (Real.log x) ^ 4 - ε * Real.log x) := by
      rw [hxpow, ← Real.exp_add]
      ring_nf
    have hRHS : x ^ (-(ε / 2)) = Real.exp (-(ε / 2) * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0 (-(ε / 2))]
      ring_nf
    rw [hLHS, hRHS]
    exact Real.exp_le_exp.mpr (by linarith [hcmp])
  have hnn : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.exp (A * Real.log (Real.log x) ^ 4) * x ^ (-ε) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx0
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hx0.le _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_rpow_neg_atTop (half_pos hε)) hnn hle

end

end PrimeGapNormality.Prime

