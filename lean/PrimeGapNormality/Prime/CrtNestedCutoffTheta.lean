import PrimeGapNormality.Prime.EulerProd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nested cutoffs: `1 − Θ ≤ 1 − R + 1/(y₁ − 1)`

For `2 ≤ y1 ≤ y2`, paper `Θ = ∏_{y1 < p ≤ y2} (1 − 1/(p−1))` is
`rootedEulerProdNat y1 y2`, and `R = V(y2)/V(y1)` is
`eulerProdNat y2 / eulerProdNat y1`. Exact identity
`rootedEulerProdNat_eq` gives `Θ = R * ∏ (1 − 1/(p−1)²)`. Then
`0 ≤ R ≤ 1` and each factor in `[0, 1]` yield the finite product
bound `1 − R ∏(1−a_p) ≤ 1 − R + ∑ a_p`. The prime sum is at most
the integer sum over `n > y1`, compared with
`∫_{(y1−1)}^{(y2−1)} t⁻² dt ≤ 1/(y1−1)` via mathlib
`AntitoneOn.sum_le_integral_Ico`.

Does **not** claim (C1) L1, (C4) `O(L/G)`, `M1 ≤ 12L`,
`HLMismatchVanishes`, or that the kernel is closed. Does not import
MixZeta, SingletonLi, ExactRootWindowClose, RootedCutoffTypicalOsc,
WeylOf*, or CrtHLMismatchVanishing.

**Compiled.**
1. `0 ≤ V(y2)/V(y1) ≤ 1` when `y1 ≤ y2`.
2. Each factor `1 − 1/(p−1)² ∈ [0, 1]` for primes `p > y1 ≥ 2`.
3. Finite product: `1 − R ∏(1−a_i) ≤ 1 − R + ∑ a_i`.
4. `∑_{y1 < p ≤ y2} 1/(p−1)² ≤ 1/(y1−1)`.
5. Combined (C3): `1 − Θ ≤ 1 − R + 1/(y1−1)`.

**Not compiled.** (C1) L1. (C4) `O(L/G)`. `M1 ≤ 12L`.
`HLMismatchVanishes`. Kernel close.

**Remaining hyps.** Binders `2 ≤ y1` and `y1 ≤ y2`. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `0 ≤ R ≤ 1` (`y1 ≤ y2`) | theorem (`crtNestTh_div_nonneg_le_one`) |
| `1 − 1/(p−1)² ∈ [0, 1]` (`p > y1 ≥ 2`) | theorem (`crtNestTh_factor_nonneg_le_one`) |
| `1 − ∏(1−a_i) ≤ ∑ a_i` | theorem (`crtNestTh_one_sub_prod_le`) |
| `1 − R ∏(1−a_i) ≤ 1 − R + ∑ a_i` | theorem (`crtNestTh_one_sub_prod_mul_le`) |
| `∑ 1/(p−1)² ≤ 1/(y1−1)` | theorem (`crtNestTh_sum_inv_sq_le`) |
| `1 − Θ ≤ 1 − R + 1/(y1−1)` | theorem (`crtNestTh_one_sub_le`) |
| (C1) L1 / (C4) `O(L/G)` / `M1 ≤ 12L` | not claimed |
| `HLMismatchVanishes` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round115/09_grok_mixture_gate_and_cutoff_bridge.md` §2 (C3);
`EulerProd.rootedEulerProdNat_eq`, `eulerProdNat_div`, `eulerProdNat_mono`.
Contract: API
Audit: GREEN
-/

open Finset
open scoped Interval

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### `0 ≤ R ≤ 1` from anti-monotonicity of `V` -/

/-- Paper `R = V(y2)/V(y1)`. Remaining: `y1 ≤ y2`. -/
theorem crtNestTh_div_nonneg_le_one {y1 y2 : ℕ} (hy12 : y1 ≤ y2) :
    0 ≤ eulerProdNat y2 / eulerProdNat y1 ∧
      eulerProdNat y2 / eulerProdNat y1 ≤ 1 := by
  have hpos : 0 < eulerProdNat y1 := eulerProdNat_pos y1
  exact ⟨div_nonneg (eulerProdNat_pos y2).le hpos.le,
    (div_le_one hpos).mpr (eulerProdNat_mono hy12)⟩

/-! ### Factors `1 − 1/(p−1)² ∈ [0, 1]` -/

private theorem crtNestTh_mem_sdiff {y1 y2 p : ℕ}
    (hp : p ∈ Nat.primesLE y2 \ Nat.primesLE y1) :
    Nat.Prime p ∧ y1 < p ∧ p ≤ y2 := by
  have hy := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
  have hnot : p ∉ Nat.primesLE y1 := (mem_sdiff.mp hp).2
  have hgt : y1 < p := Nat.not_le.mp fun hle =>
    hnot (Nat.mem_primesLE.mpr ⟨hle, hy.2⟩)
  exact ⟨hy.2, hgt, hy.1⟩

private theorem crtNestTh_sdiff_subset_Icc (y1 y2 : ℕ) :
    Nat.primesLE y2 \ Nat.primesLE y1 ⊆ Icc (y1 + 1) y2 := by
  intro p hp
  have hp' := crtNestTh_mem_sdiff hp
  exact mem_Icc.mpr ⟨Nat.succ_le_of_lt hp'.2.1, hp'.2.2⟩

/-- Weights `a_p = 1/(p−1)²` lie in `[0, 1]` for primes `p > y1 ≥ 2`. -/
theorem crtNestTh_inv_pred_sq_nonneg_le_one {y1 p : ℕ}
    (hy1 : 2 ≤ y1) (_hp : Nat.Prime p) (hpy : y1 < p) :
    0 ≤ ((p : ℝ) - 1)⁻¹ ^ 2 ∧ ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 := by
  have hp3n : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_lt hy1 hpy)
  have hp3 : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3n
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hnn : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hle : ((p : ℝ) - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
  exact ⟨sq_nonneg _, pow_le_one₀ hnn hle⟩

/-- Each extra Euler factor `1 − 1/(p−1)²` lies in `[0, 1]`.
Remaining: `Nat.Prime p` and `y1 < p`, with `2 ≤ y1`. -/
theorem crtNestTh_factor_nonneg_le_one {y1 p : ℕ}
    (hy1 : 2 ≤ y1) (hp : Nat.Prime p) (hpy : y1 < p) :
    0 ≤ 1 - ((p : ℝ) - 1)⁻¹ ^ 2 ∧ 1 - ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 := by
  have h := crtNestTh_inv_pred_sq_nonneg_le_one hy1 hp hpy
  exact ⟨sub_nonneg.mpr h.2, sub_le_self _ h.1⟩

/-! ### Finite product: `1 − ∏(1−a_i) ≤ ∑ a_i`, then with a factor `R` -/

/-- Standard finite product comparison, by induction on `Finset`. -/
theorem crtNestTh_one_sub_prod_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ 1) →
      1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  refine s.induction_on ?_ ?_
  · intro _ _
    simp
  · intro a s ha ih hf0 hf1
    rw [prod_insert ha, sum_insert ha]
    have ih' : 1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i :=
      ih (fun i hi => hf0 i (mem_insert_of_mem hi))
        (fun i hi => hf1 i (mem_insert_of_mem hi))
    have ha0 : 0 ≤ f a := hf0 a (mem_insert_self _ _)
    have hP1 : ∏ i ∈ s, (1 - f i) ≤ 1 :=
      prod_le_one (fun i hi => sub_nonneg.mpr (hf1 i (mem_insert_of_mem hi)))
        (fun i hi => sub_le_self _ (hf0 i (mem_insert_of_mem hi)))
    have hexp :
        1 - (1 - f a) * ∏ i ∈ s, (1 - f i) =
          (1 - ∏ i ∈ s, (1 - f i)) + f a * ∏ i ∈ s, (1 - f i) := by
      ring
    rw [hexp]
    have h2 : f a * ∏ i ∈ s, (1 - f i) ≤ f a :=
      mul_le_of_le_one_right ha0 hP1
    linarith

/-- `1 − R * ∏(1−a_i) ≤ 1 − R + ∑ a_i` when `0 ≤ R ≤ 1` and
`0 ≤ a_i ≤ 1`. -/
theorem crtNestTh_one_sub_prod_mul_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (R : ℝ) (f : ι → ℝ) (_hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    1 - R * ∏ i ∈ s, (1 - f i) ≤ 1 - R + ∑ i ∈ s, f i := by
  have hP1 : ∏ i ∈ s, (1 - f i) ≤ 1 :=
    prod_le_one (fun i hi => sub_nonneg.mpr (hf1 i hi))
      (fun i hi => sub_le_self _ (hf0 i hi))
  have hprod := crtNestTh_one_sub_prod_le s f hf0 hf1
  have hexp : 1 - R * ∏ i ∈ s, (1 - f i) =
      1 - R + R * (1 - ∏ i ∈ s, (1 - f i)) := by
    ring
  rw [hexp]
  have hRmul :
      R * (1 - ∏ i ∈ s, (1 - f i)) ≤ 1 - ∏ i ∈ s, (1 - f i) :=
    mul_le_of_le_one_left (sub_nonneg.mpr hP1) hR1
  have hsum :
      1 - R + R * (1 - ∏ i ∈ s, (1 - f i)) ≤
        1 - R + (1 - ∏ i ∈ s, (1 - f i)) :=
    add_le_add (le_refl (1 - R)) hRmul
  exact hsum.trans (add_le_add (le_refl (1 - R)) hprod)

/-! ### Prime sum `∑ 1/(p−1)² ≤ 1/(y1−1)` via sum–integral comparison -/

private theorem crtNestTh_inv_sq_eq_zpow (t : ℝ) :
    t⁻¹ ^ 2 = t ^ (-2 : ℤ) := by
  simp [inv_pow, zpow_natCast, zpow_neg]

private theorem crtNestTh_inv_sq_antitoneOn {a b : ℕ}
    (ha : 1 ≤ a) (_hab : a ≤ b) :
    AntitoneOn (fun t : ℝ => t⁻¹ ^ 2)
      (Set.Icc (a : ℝ) (b : ℝ)) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := le_trans (Nat.one_le_cast.mpr ha) hx.1
  have hy1 : (1 : ℝ) ≤ y := le_trans (Nat.one_le_cast.mpr ha) hy.1
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx1
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy1
  have hinv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hxy
  exact pow_le_pow_left₀ (inv_nonneg.mpr hy0.le) hinv 2

private theorem crtNestTh_zero_notMem_uIcc {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (0 : ℝ) ∉ [[(a : ℝ), (b : ℝ)]] := by
  rw [Set.uIcc_of_le (Nat.cast_le.mpr hab)]
  intro hmem
  have : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  linarith [hmem.1]

private theorem crtNestTh_integral_inv_sq {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in (a : ℝ)..(b : ℝ), t⁻¹ ^ 2 = (a : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
  have h0 := crtNestTh_zero_notMem_uIcc ha hab
  have hcongr :
      Set.EqOn (fun t : ℝ => t⁻¹ ^ 2) (fun t : ℝ => t ^ (-2 : ℤ))
        [[(a : ℝ), (b : ℝ)]] := fun t _ht => crtNestTh_inv_sq_eq_zpow t
  have hrew :
      ∫ t in (a : ℝ)..(b : ℝ), t⁻¹ ^ 2 =
        ∫ t in (a : ℝ)..(b : ℝ), t ^ (-2 : ℤ) :=
    intervalIntegral.integral_congr hcongr
  have hz :
      ∫ t in (a : ℝ)..(b : ℝ), t ^ (-2 : ℤ) =
        ((b : ℝ) ^ ((-2 : ℤ) + 1) - (a : ℝ) ^ ((-2 : ℤ) + 1)) /
          ((-2 : ℤ) + 1) :=
    integral_zpow (Or.inr ⟨by norm_num, h0⟩)
  have hn : (-2 : ℤ) + 1 = (-1 : ℤ) := by norm_num
  have hden : ((-2 : ℤ) : ℝ) + 1 = (-1 : ℝ) := by norm_num
  rw [hrew, hz, hn, zpow_neg_one, zpow_neg_one, hden]
  ring

private theorem crtNestTh_sum_Icc_eq_Ico {y1 y2 : ℕ}
    (hy1 : 2 ≤ y1) (hI : y1 + 1 ≤ y2) :
    ∑ n ∈ Icc (y1 + 1) y2, ((n : ℝ) - 1)⁻¹ ^ 2 =
      ∑ i ∈ Ico (y1 - 1) (y2 - 1), ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
  have h3 : 3 ≤ y1 + 1 := Nat.succ_le_succ hy1
  refine sum_nbij (fun n => n - 2) ?_ ?_ ?_ ?_
  · intro n hn
    have hn' := mem_Icc.mp hn
    have hn3 : 3 ≤ n := h3.trans hn'.1
    have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 3) hn3
    have hlo : y1 - 1 ≤ n - 2 := by
      have := hn2
      have := hn'.1
      have := hy1
      omega
    have hhi : n - 2 < y2 - 1 := by
      have := hn'.2
      have := hI
      have := hy1
      omega
    exact mem_Ico.mpr ⟨hlo, hhi⟩
  · intro a ha b hb h
    have ha3 : 3 ≤ a := h3.trans (mem_Icc.mp ha).1
    have hb3 : 3 ≤ b := h3.trans (mem_Icc.mp hb).1
    have ha2 : 2 ≤ a := le_trans (by decide : (2 : ℕ) ≤ 3) ha3
    have hb2 : 2 ≤ b := le_trans (by decide : (2 : ℕ) ≤ 3) hb3
    calc
      a = a - 2 + 2 := (Nat.sub_add_cancel ha2).symm
      _ = b - 2 + 2 := congrArg (fun n : ℕ => n + 2) h
      _ = b := Nat.sub_add_cancel hb2
  · intro i hi
    have hi' := mem_Ico.mp hi
    have hlo : y1 + 1 ≤ i + 2 := by
      have := Nat.add_le_add_right hi'.1 2
      have heq : y1 - 1 + 2 = y1 + 1 := by omega
      rwa [heq] at this
    have hhi : i + 2 ≤ y2 := by omega
    refine ⟨i + 2, mem_Icc.mpr ⟨hlo, hhi⟩, Nat.add_sub_cancel _ _⟩
  · intro n hn
    have hn' := mem_Icc.mp hn
    have hn3 : 3 ≤ n := h3.trans hn'.1
    have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 3) hn3
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    have hi : n - 2 + 1 = n - 1 := by omega
    rw [hi, hcast]

private theorem crtNestTh_y1_sub_one_cast {y1 : ℕ} (hy1 : 2 ≤ y1) :
    ((y1 - 1 : ℕ) : ℝ) = (y1 : ℝ) - 1 := by
  have h : 1 ≤ y1 := (by decide : (1 : ℕ) ≤ 2).trans hy1
  rw [Nat.cast_sub h, Nat.cast_one]

private theorem crtNestTh_one_div_y1_sub_one_nonneg {y1 : ℕ}
    (hy1 : 2 ≤ y1) : 0 ≤ 1 / ((y1 : ℝ) - 1) := by
  have : (2 : ℝ) ≤ y1 := Nat.cast_le.mpr hy1
  exact div_nonneg zero_le_one (by linarith)

private theorem crtNestTh_sum_Icc_inv_pred_sq_le {y1 y2 : ℕ}
    (hy1 : 2 ≤ y1) :
    ∑ n ∈ Icc (y1 + 1) y2, ((n : ℝ) - 1)⁻¹ ^ 2 ≤
      1 / ((y1 : ℝ) - 1) := by
  by_cases hI : y1 + 1 ≤ y2
  · have hy12 : y1 ≤ y2 := le_trans (Nat.le_succ y1) hI
    have ha : 1 ≤ y1 - 1 := by omega
    have hab : y1 - 1 ≤ y2 - 1 := Nat.sub_le_sub_right hy12 1
    have hanti := crtNestTh_inv_sq_antitoneOn ha hab
    have hsum :=
      AntitoneOn.sum_le_integral_Ico (a := y1 - 1) (b := y2 - 1)
        (f := fun t : ℝ => t⁻¹ ^ 2) hab hanti
    have hinter := crtNestTh_integral_inv_sq ha hab
    have htail : 0 ≤ ((y2 - 1 : ℕ) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hle :
        ((y1 - 1 : ℕ) : ℝ)⁻¹ - ((y2 - 1 : ℕ) : ℝ)⁻¹ ≤
          ((y1 - 1 : ℕ) : ℝ)⁻¹ :=
      sub_le_self _ htail
    have hcast := crtNestTh_y1_sub_one_cast hy1
    calc
      ∑ n ∈ Icc (y1 + 1) y2, ((n : ℝ) - 1)⁻¹ ^ 2
          = ∑ i ∈ Ico (y1 - 1) (y2 - 1),
              ((i + 1 : ℕ) : ℝ)⁻¹ ^ 2 :=
            crtNestTh_sum_Icc_eq_Ico hy1 hI
      _ ≤ ∫ t in ((y1 - 1 : ℕ) : ℝ)..((y2 - 1 : ℕ) : ℝ),
            t⁻¹ ^ 2 :=
          hsum
      _ = ((y1 - 1 : ℕ) : ℝ)⁻¹ - ((y2 - 1 : ℕ) : ℝ)⁻¹ := hinter
      _ ≤ ((y1 - 1 : ℕ) : ℝ)⁻¹ := hle
      _ = 1 / ((y1 : ℝ) - 1) := by rw [hcast, inv_eq_one_div]
  · have hempty : Icc (y1 + 1) y2 = ∅ :=
      Icc_eq_empty_of_lt (Nat.not_le.mp hI)
    rw [hempty, sum_empty]
    exact crtNestTh_one_div_y1_sub_one_nonneg hy1

/-- Prime sum versus integers `n > y1` and
`∫_{(y1−1)}^{(y2−1)} t⁻² dt ≤ 1/(y1−1)`. Remaining: `2 ≤ y1`. -/
theorem crtNestTh_sum_inv_sq_le {y1 y2 : ℕ} (hy1 : 2 ≤ y1) :
    ∑ p ∈ Nat.primesLE y2 \ Nat.primesLE y1,
        ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 / ((y1 : ℝ) - 1) := by
  have hsub := crtNestTh_sdiff_subset_Icc y1 y2
  have hnn : ∀ n ∈ Icc (y1 + 1) y2, 0 ≤ ((n : ℝ) - 1)⁻¹ ^ 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by
      have := (mem_Icc.mp hn).1
      omega
    have hden : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn1
      linarith
    exact pow_nonneg (inv_nonneg.mpr hden) 2
  have hprimes :
      ∑ p ∈ Nat.primesLE y2 \ Nat.primesLE y1,
          ((p : ℝ) - 1)⁻¹ ^ 2 ≤
        ∑ n ∈ Icc (y1 + 1) y2, ((n : ℝ) - 1)⁻¹ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnn n hn
  exact hprimes.trans (crtNestTh_sum_Icc_inv_pred_sq_le hy1)

/-! ### Combined nested-cutoff bound (C3) -/

/-- Paper (C3): `1 − Θ ≤ 1 − R + 1/(y1−1)` for nested cutoffs
`2 ≤ y1 ≤ y2`. Does **not** claim (C1) or (C4). -/
theorem crtNestTh_one_sub_le {y1 y2 : ℕ} (hy1 : 2 ≤ y1)
    (hy12 : y1 ≤ y2) :
    1 - rootedEulerProdNat y1 y2 ≤
      1 - eulerProdNat y2 / eulerProdNat y1 + 1 / ((y1 : ℝ) - 1) := by
  rw [rootedEulerProdNat_eq hy12]
  have hR := crtNestTh_div_nonneg_le_one hy12
  have ha0 : ∀ p ∈ Nat.primesLE y2 \ Nat.primesLE y1,
      0 ≤ ((p : ℝ) - 1)⁻¹ ^ 2 := fun _ _ => sq_nonneg _
  have ha1 : ∀ p ∈ Nat.primesLE y2 \ Nat.primesLE y1,
      ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 := fun p hp =>
    (crtNestTh_inv_pred_sq_nonneg_le_one hy1
      (crtNestTh_mem_sdiff hp).1 (crtNestTh_mem_sdiff hp).2.1).2
  have hmul :=
    crtNestTh_one_sub_prod_mul_le
      (Nat.primesLE y2 \ Nat.primesLE y1)
      (eulerProdNat y2 / eulerProdNat y1)
      (fun p => ((p : ℝ) - 1)⁻¹ ^ 2) hR.1 hR.2 ha0 ha1
  exact hmul.trans
    (add_le_add (le_refl (1 - eulerProdNat y2 / eulerProdNat y1))
      (crtNestTh_sum_inv_sq_le (y2 := y2) hy1))

end

end PrimeGapNormality.Prime
