import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# CRT interval rounding on `S` consecutive integers

Paper / R117/07 §1.1: on any interval of `S` consecutive integers the
occupancy of one residue class modulo `m ≥ 1` differs from `S / m` by
at most one. Honest rounding: Mathlib `Int.Ico_filter_modEq_card`
(`⌈(b-v)/m⌉ - ⌈(a-v)/m⌉`) and the real comparison
`|(⌈x⌉ - ⌈y⌉) - (x-y)| < 1`. No new axioms.

Consequently the expansion error is

    |∑_{n ∈ I} 1[ℓ ∣ n−c] − S/ℓ| ≤ 1

for `ℓ ≥ 1`. The `lcm(d,e)` case is the same statement with parameter
`ℓ = Nat.lcm d e`. This leaf does **not** sum `λ_d λ_e`, does **not**
bound `(∑ |λ_d|)²`, and does **not** claim `|A| ≤ S/J(R)+R²`.

Does **not** import `SelbergLambdaSq`, `SelbergHarmonicJ`,
`EulerVLogHalf`, `SieveCirc`, MixZeta, or SingletonLi.
Does **not** compile `E choose(N^circ,j)`, `V log > 1/2`, `J(R)`,
`S^circ`, kernel, (C4), or `PrimeCountingNormalization`.

**Compiled.**
1. Interval `Ico a (a+S)` has cardinality `S` (`ℕ` and `ℤ`).
2. Exact ceil count of one residue in an integer interval of length `S`.
3. `|(⌈x⌉ - ⌈y⌉) - (x-y)| < 1` on `ℝ`.
4. `|#{x ∈ Ico a (a+S) | x ≡ c [ZMOD ℓ]} − S/ℓ| ≤ 1`.
5. Same occupancy on `ℕ`, residue `n ≡ r [MOD m]` / `n % m = r % m`.
6. Nat sandwich `S/m ≤ count ≤ S/m+1`.
7. Indicator `1[ℓ ∣ n−c]` and sum-card identity.
8. Expansion error `|∑ 1[ℓ ∣ n−c] − S/ℓ| ≤ 1`.
9. Same error with `ℓ = Nat.lcm d e` (`1 ≤ lcm`).

**Not compiled.** Selberg cap `|A| ≤ S/J(R)+R²`. Weights `λ_d`.
`|λ_d| ≤ 1`. Harmonic `J(R)`. `V(S^circ) log S^circ > 1/2`.
Inner `5L` moments. Stop comparison. Kernel close. (C4).
`PrimeCountingNormalization`.

**Remaining hyps.** Binders `1 ≤ m` / `1 ≤ ℓ` (and `1 ≤ d.lcm e` for
the lcm form). No position restriction: the integer form is uniform
in the start `a : ℤ`. Kernel not closed.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `#(Ico a (a+S)) = S` | theorem |
| exact ceil occupancy | theorem (`selbergCrt_intCount_eq_ceil`) |
| `|(⌈x⌉-⌈y⌉)-(x-y)| < 1` | theorem (`selbergCrt_ceil_error`) |
| `|intCount − S/ℓ| ≤ 1` | theorem (`selbergCrt_intCount_abs_le`) |
| `|#{n ≡ r [MOD m]} − S/m| ≤ 1` | theorem (`selbergCrt_residueCount_abs_le`) |
| same with `n % m = r % m` | theorem (`selbergCrt_card_mod_abs_le`) |
| `S/m ≤ count ≤ S/m+1` | theorem |
| `|∑ 1[ℓ ∣ n−c] − S/ℓ| ≤ 1` | theorem (`selbergCrt_sum_indicator_abs_le`) |
| same for `ℓ = lcm(d,e)` | theorem (`selbergCrt_sum_indicator_lcm_abs_le`) |
| `|A| ≤ S/J(R)+R²` | not claimed |
| `∑ λ_d λ_e / lcm` / `(∑|λ_d|)²` | not claimed |
| `J(R)` / `V log > 1/2` / `5L` | not claimed |
| kernel closed | not claimed |

Does not claim the kernel is closed.

Source: `rounds/round117/07_selberg_rewrite_redteam.md` §1.1;
`rounds/round118/09_grok_v012_delta.md` P3.
Contract: API
-/

open Finset

namespace PrimeGapNormality.Prime

noncomputable section

set_option maxHeartbeats 400000

/-! ### Length of a consecutive block -/

/-- A block of `S` consecutive naturals has cardinality `S`. -/
theorem selbergCrt_Ico_card (a S : ℕ) : (Ico a (a + S)).card = S := by
  rw [Nat.card_Ico, Nat.add_sub_cancel_left]

/-- A block of `S` consecutive integers has cardinality `S`. -/
theorem selbergCrt_intIco_card (a : ℤ) (S : ℕ) :
    (Ico a (a + S)).card = S := by
  rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]

private theorem selbergCrt_one_le_iff_pos {m : ℕ} : 1 ≤ m ↔ 0 < m :=
  Nat.succ_le_iff

private theorem selbergCrt_pos_of_one_le {m : ℕ} (hm : 1 ≤ m) : 0 < m :=
  (selbergCrt_one_le_iff_pos).mp hm

private theorem selbergCrt_int_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : (0 : ℤ) < ℓ :=
  Int.natCast_pos.mpr (selbergCrt_pos_of_one_le hℓ)

/-! ### Occupancy counts -/

/-- Numbers in `[a, a+S)` congruent to `c` modulo `ℓ`. -/
def selbergCrt_intCount (a : ℤ) (S ℓ : ℕ) (c : ℤ) : ℕ :=
  #{x ∈ Ico a (a + S) | x ≡ c [ZMOD (ℓ : ℤ)]}

/-- Numbers in `[a, a+S)` congruent to `r` modulo `m`. -/
def selbergCrt_residueCount (a S m r : ℕ) : ℕ :=
  #{n ∈ Ico a (a + S) | n ≡ r [MOD m]}

theorem selbergCrt_intCount_eq (a : ℤ) (S ℓ : ℕ) (c : ℤ) :
    selbergCrt_intCount a S ℓ c =
      #{x ∈ Ico a (a + S) | x ≡ c [ZMOD (ℓ : ℤ)]} :=
  rfl

theorem selbergCrt_residueCount_eq (a S m r : ℕ) :
    selbergCrt_residueCount a S m r =
      #{n ∈ Ico a (a + S) | n ≡ r [MOD m]} :=
  rfl

theorem selbergCrt_modEq_iff_mod (n r m : ℕ) :
    n ≡ r [MOD m] ↔ n % m = r % m :=
  Iff.rfl

theorem selbergCrt_residueCount_eq_mod (a S m r : ℕ) :
    selbergCrt_residueCount a S m r =
      #{n ∈ Ico a (a + S) | n % m = r % m} :=
  rfl

/-! ### Ceil rounding error -/

/-- Honest ceil comparison: the difference of ceils tracks `x-y`
with error strictly less than `1`. -/
theorem selbergCrt_ceil_error (x y : ℝ) :
    |((⌈x⌉ : ℝ) - (⌈y⌉ : ℝ)) - (x - y)| < 1 := by
  have hx0 : x ≤ ⌈x⌉ := Int.le_ceil x
  have hx1 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hy0 : y ≤ ⌈y⌉ := Int.le_ceil y
  have hy1 : (⌈y⌉ : ℝ) < y + 1 := Int.ceil_lt_add_one y
  have hdiff :
      ((⌈x⌉ : ℝ) - (⌈y⌉ : ℝ)) - (x - y) =
        ((⌈x⌉ : ℝ) - x) - ((⌈y⌉ : ℝ) - y) := by
    ring
  rw [hdiff]
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-! ### Exact ceil formula on `ℤ` -/

private theorem selbergCrt_quot_le (a : ℤ) (S ℓ : ℕ) (c : ℤ) :
    (((a - c : ℤ) : ℚ) / (ℓ : ℚ)) ≤
      (((a + (S : ℤ) - c : ℤ) : ℚ) / (ℓ : ℚ)) := by
  have hle : a - c ≤ a + (S : ℤ) - c := by
    have : a ≤ a + (S : ℤ) := le_add_of_nonneg_right (Nat.cast_nonneg S)
    exact sub_le_sub_right this c
  have hℓ : (0 : ℚ) ≤ ℓ := Nat.cast_nonneg ℓ
  exact div_le_div_of_nonneg_right (Int.cast_le.mpr hle) hℓ

private theorem selbergCrt_quot_sub (a : ℤ) (S ℓ : ℕ) (c : ℤ) :
    (((a + (S : ℤ) - c : ℤ) : ℚ) / (ℓ : ℚ)) -
        (((a - c : ℤ) : ℚ) / (ℓ : ℚ)) =
      (S : ℚ) / ℓ := by
  have hAB :
      (((a + (S : ℤ) - c : ℤ) : ℚ) - ((a - c : ℤ) : ℚ)) = (S : ℚ) := by
    have hZ : (a + (S : ℤ) - c) - (a - c) = (S : ℤ) := by ring
    rw [← Int.cast_sub, hZ, Int.cast_natCast]
  rw [← sub_div, hAB]

/-- Exact occupancy via Mathlib ceil (honest `ℚ`-rounding). -/
theorem selbergCrt_intCount_eq_ceil (a : ℤ) (S ℓ : ℕ) (c : ℤ)
    (hℓ : 1 ≤ ℓ) :
    (selbergCrt_intCount a S ℓ c : ℤ) =
      ⌈(((a + (S : ℤ) - c : ℤ) : ℚ) / (ℓ : ℚ))⌉ -
        ⌈(((a - c : ℤ) : ℚ) / (ℓ : ℚ))⌉ := by
  have hℓZ : (0 : ℤ) < ℓ := selbergCrt_int_pos hℓ
  have hcard := Int.Ico_filter_modEq_card a (a + (S : ℤ)) hℓZ c
  have hnn :
      0 ≤
        ⌈(((a + (S : ℤ) - c : ℤ) : ℚ) / (ℓ : ℚ))⌉ -
          ⌈(((a - c : ℤ) : ℚ) / (ℓ : ℚ))⌉ :=
    sub_nonneg.mpr (Int.ceil_mono (selbergCrt_quot_le a S ℓ c))
  unfold selbergCrt_intCount
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at hcard hnn ⊢
  rw [max_eq_left hnn] at hcard
  exact_mod_cast hcard

/-! ### Integer CRT interval error -/

private theorem selbergCrt_quot_sub_real (a : ℤ) (S ℓ : ℕ) (c : ℤ) :
    (((a + (S : ℤ) - c : ℤ) : ℝ) / (ℓ : ℝ) -
        ((a - c : ℤ) : ℝ) / (ℓ : ℝ)) =
      (S : ℝ) / ℓ := by
  have hZ : ((a + (S : ℤ) - c : ℤ) : ℝ) - ((a - c : ℤ) : ℝ) = (S : ℝ) := by
    have hZ' : (a + (S : ℤ) - c) - (a - c) = (S : ℤ) := by ring
    rw [← Int.cast_sub, hZ', Int.cast_natCast]
  rw [← sub_div, hZ]

private theorem selbergCrt_intCount_abs_lt (a : ℤ) (S ℓ : ℕ) (c : ℤ)
    (hℓ : 1 ≤ ℓ) :
    |((selbergCrt_intCount a S ℓ c : ℝ) - (S : ℝ) / ℓ)| < 1 := by
  set x : ℚ := ((a + (S : ℤ) - c : ℤ) : ℚ) / (ℓ : ℚ)
  set y : ℚ := ((a - c : ℤ) : ℚ) / (ℓ : ℚ)
  have hcardZ := selbergCrt_intCount_eq_ceil a S ℓ c hℓ
  have hcardR : (selbergCrt_intCount a S ℓ c : ℝ) = (⌈x⌉ : ℝ) - ⌈y⌉ := by
    dsimp [x, y]
    exact_mod_cast hcardZ
  have herr : |((⌈x⌉ : ℝ) - (⌈y⌉ : ℝ)) - (S : ℝ) / ℓ| < 1 := by
    have h := selbergCrt_ceil_error (x : ℝ) (y : ℝ)
    rw [Rat.ceil_cast x, Rat.ceil_cast y] at h
    have hxy : (x : ℝ) - (y : ℝ) = (S : ℝ) / ℓ := by
      dsimp [x, y]
      rw [Rat.cast_div, Rat.cast_div]
      exact selbergCrt_quot_sub_real a S ℓ c
    rwa [hxy] at h
  rw [hcardR]
  exact herr

/-- Uniform CRT interval error on `ℤ`: occupancy minus `S/ℓ` is at
most `1` in absolute value. Position of the interval is free. -/
theorem selbergCrt_intCount_abs_le (a : ℤ) (S ℓ : ℕ) (c : ℤ)
    (hℓ : 1 ≤ ℓ) :
    |((selbergCrt_intCount a S ℓ c : ℝ) - (S : ℝ) / ℓ)| ≤ 1 :=
  le_of_lt (selbergCrt_intCount_abs_lt a S ℓ c hℓ)

/-! ### Embedding `ℕ` into `ℤ` -/

theorem selbergCrt_Ico_map (a S : ℕ) :
    (Ico a (a + S)).map Nat.castEmbedding = Ico (a : ℤ) ((a : ℤ) + S) := by
  ext x
  simp only [mem_map, mem_Ico, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨n, ⟨hle, hlt⟩, rfl⟩
    refine ⟨Nat.cast_le.mpr hle, ?_⟩
    have : (n : ℤ) < (a + S : ℕ) := Nat.cast_lt.mpr hlt
    rwa [Nat.cast_add] at this
  · intro hx
    have hx0 : (0 : ℤ) ≤ x := le_trans (Nat.cast_nonneg a) hx.1
    refine ⟨x.toNat, ⟨?_, ?_⟩, Int.toNat_of_nonneg hx0⟩
    · exact Nat.cast_le.mp (by
        rw [Int.toNat_of_nonneg hx0]
        exact hx.1)
    · have hlt : (x.toNat : ℤ) < (a : ℤ) + S := by
        rw [Int.toNat_of_nonneg hx0]
        exact hx.2
      have : (x.toNat : ℤ) < (a + S : ℕ) := by
        rwa [Nat.cast_add]
      exact Nat.cast_lt.mp this

private theorem selbergCrt_Ico_filter_map (a S ℓ : ℕ) (c : ℤ) :
    ((Ico a (a + S)).filter
        (fun n : ℕ => (n : ℤ) ≡ c [ZMOD (ℓ : ℤ)])).map Nat.castEmbedding =
      (Ico (a : ℤ) ((a : ℤ) + S)).filter
        (fun x : ℤ => x ≡ c [ZMOD (ℓ : ℤ)]) := by
  rw [← selbergCrt_Ico_map]
  ext x
  simp only [mem_map, mem_filter, Nat.castEmbedding_apply]
  constructor
  · rintro ⟨n, ⟨hn, hcong⟩, rfl⟩
    exact ⟨⟨n, hn, rfl⟩, hcong⟩
  · rintro ⟨⟨n, hn, rfl⟩, hcong⟩
    exact ⟨n, ⟨hn, hcong⟩, rfl⟩

theorem selbergCrt_residueCount_eq_intCount (a S m r : ℕ) :
    selbergCrt_residueCount a S m r =
      selbergCrt_intCount (a : ℤ) S m (r : ℤ) := by
  have hfilter :
      (Ico a (a + S)).filter (fun n : ℕ => n ≡ r [MOD m]) =
        (Ico a (a + S)).filter
          (fun n : ℕ => (n : ℤ) ≡ (r : ℤ) [ZMOD (m : ℤ)]) := by
    ext n
    simp only [mem_filter, Int.natCast_modEq_iff]
  unfold selbergCrt_residueCount
  rw [hfilter]
  have hmap := selbergCrt_Ico_filter_map a S m (r : ℤ)
  have hcard := congrArg card hmap
  rw [card_map] at hcard
  unfold selbergCrt_intCount
  exact hcard

/-! ### Natural CRT interval error -/

/-- Occupancy of one residue class on `S` consecutive naturals differs
from `S/m` by at most `1`. -/
theorem selbergCrt_residueCount_abs_le (a S m r : ℕ) (hm : 1 ≤ m) :
    |((selbergCrt_residueCount a S m r : ℝ) - (S : ℝ) / m)| ≤ 1 := by
  rw [selbergCrt_residueCount_eq_intCount]
  exact selbergCrt_intCount_abs_le (a : ℤ) S m (r : ℤ) hm

/-- Same occupancy written with `%`. -/
theorem selbergCrt_card_mod_abs_le (a S m r : ℕ) (hm : 1 ≤ m) :
    |((#{n ∈ Ico a (a + S) | n % m = r % m} : ℝ) - (S : ℝ) / m)| ≤ 1 := by
  simpa [selbergCrt_residueCount_eq_mod] using
    selbergCrt_residueCount_abs_le a S m r hm

/-- Equivalent form on `Ico a b` with `a ≤ b`. -/
theorem selbergCrt_residueCount_Ico_abs_le {a b m r : ℕ}
    (hm : 1 ≤ m) (hle : a ≤ b) :
    |((#{n ∈ Ico a b | n ≡ r [MOD m]} : ℝ) - ((b - a : ℕ) : ℝ) / m)| ≤
      1 := by
  have hb : b = a + (b - a) := (Nat.add_sub_cancel' hle).symm
  rw [hb]
  simpa [selbergCrt_residueCount] using
    selbergCrt_residueCount_abs_le a (b - a) m r hm

/-! ### Nat sandwich `⌊S/m⌋ ≤ count ≤ ⌊S/m⌋+1` -/

private theorem selbergCrt_div_lt_add_one (S m : ℕ) (hm : 0 < m) :
    (S : ℝ) / m < (S / m : ℕ) + 1 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmod : S % m < m := Nat.mod_lt S hm
  have hdecomp : S = m * (S / m) + S % m := (Nat.div_add_mod S m).symm
  have hlt : S < m * (S / m) + m :=
    lt_of_eq_of_lt hdecomp (Nat.add_lt_add_left hmod (m * (S / m)))
  have hsucc : m * (S / m) + m = m * (S / m + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hmul : S < m * (S / m + 1) := by
    rwa [hsucc] at hlt
  have hmulR : (S : ℝ) < (m : ℝ) * ((S / m : ℕ) + 1) := by
    exact_mod_cast hmul
  have : (S : ℝ) < ((S / m : ℕ) + 1) * (m : ℝ) := by
    rwa [mul_comm] at hmulR
  exact (div_lt_iff₀ hm0).mpr this

/-- Integer lower bound: at least `S/m` hits (Nat division). -/
theorem selbergCrt_div_le_residueCount (a S m r : ℕ) (hm : 1 ≤ m) :
    S / m ≤ selbergCrt_residueCount a S m r := by
  have hlt : |((selbergCrt_residueCount a S m r : ℝ) - (S : ℝ) / m)| < 1 := by
    rw [selbergCrt_residueCount_eq_intCount]
    exact selbergCrt_intCount_abs_lt (a : ℤ) S m (r : ℤ) hm
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (selbergCrt_pos_of_one_le hm)
  have hmul : ((S / m : ℕ) : ℝ) * (m : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self S m
  have hfloor : ((S / m : ℕ) : ℝ) ≤ (S : ℝ) / m := (le_div_iff₀ hm0).mpr hmul
  have h1 : ((S / m : ℕ) : ℝ) <
      (selbergCrt_residueCount a S m r : ℝ) + 1 := by
    have := (abs_lt.mp hlt).1
    linarith
  have h2 : ((S / m : ℕ) : ℝ) <
      ((selbergCrt_residueCount a S m r + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact h1
  exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp h2)

/-- Integer upper bound: at most `S/m+1` hits (Nat division). -/
theorem selbergCrt_residueCount_le_div_add_one (a S m r : ℕ)
    (hm : 1 ≤ m) :
    selbergCrt_residueCount a S m r ≤ S / m + 1 := by
  have habs := selbergCrt_residueCount_abs_le a S m r hm
  have hm0 : 0 < m := selbergCrt_pos_of_one_le hm
  have hC : (selbergCrt_residueCount a S m r : ℝ) ≤ (S : ℝ) / m + 1 := by
    have := (abs_le.mp habs).2
    linarith
  have hfrac := selbergCrt_div_lt_add_one S m hm0
  have hR : (selbergCrt_residueCount a S m r : ℝ) <
      ((S / m : ℕ) : ℝ) + 2 := by
    linarith
  have h2 : ((S / m : ℕ) : ℝ) + 2 = ((S / m + 2 : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    norm_num
  have hR' : (selbergCrt_residueCount a S m r : ℝ) <
      ((S / m + 2 : ℕ) : ℝ) := by
    rwa [← h2]
  have hlt : selbergCrt_residueCount a S m r < S / m + 2 :=
    Nat.cast_lt.mp hR'
  have hs : S / m + 2 = Nat.succ (S / m + 1) := rfl
  rw [hs] at hlt
  exact Nat.lt_succ_iff.mp hlt

/-! ### Indicator `1[ℓ ∣ n−c]` -/

/-- Paper indicator `1[ℓ ∣ n−c]` with integer difference. -/
def selbergCrt_indicator (ℓ : ℕ) (c : ℤ) (n : ℕ) : ℝ :=
  if (ℓ : ℤ) ∣ ((n : ℤ) - c) then (1 : ℝ) else 0

theorem selbergCrt_dvd_iff_modEq (ℓ : ℕ) (c : ℤ) (n : ℕ) :
    (ℓ : ℤ) ∣ ((n : ℤ) - c) ↔ (n : ℤ) ≡ c [ZMOD (ℓ : ℤ)] := by
  rw [Int.modEq_iff_dvd, ← neg_sub (n : ℤ) c, dvd_neg]

theorem selbergCrt_indicator_eq_modEq (ℓ : ℕ) (c : ℤ) (n : ℕ) :
    selbergCrt_indicator ℓ c n =
      if (n : ℤ) ≡ c [ZMOD (ℓ : ℤ)] then (1 : ℝ) else 0 := by
  unfold selbergCrt_indicator
  simp [selbergCrt_dvd_iff_modEq]

theorem selbergCrt_sum_indicator_eq_card (a S ℓ : ℕ) (c : ℤ) :
    ∑ n ∈ Ico a (a + S), selbergCrt_indicator ℓ c n =
      (((Ico a (a + S)).filter
          (fun n : ℕ => (ℓ : ℤ) ∣ ((n : ℤ) - c))).card : ℝ) := by
  simp only [selbergCrt_indicator, sum_boole]

theorem selbergCrt_sum_indicator_eq_intCount (a S ℓ : ℕ) (c : ℤ) :
    ∑ n ∈ Ico a (a + S), selbergCrt_indicator ℓ c n =
      (selbergCrt_intCount (a : ℤ) S ℓ c : ℝ) := by
  have hpred :
      (Ico a (a + S)).filter
          (fun n : ℕ => (ℓ : ℤ) ∣ ((n : ℤ) - c)) =
        (Ico a (a + S)).filter
          (fun n : ℕ => (n : ℤ) ≡ c [ZMOD (ℓ : ℤ)]) := by
    ext n
    simp only [mem_filter, selbergCrt_dvd_iff_modEq]
  rw [selbergCrt_sum_indicator_eq_card, hpred]
  have hmap := selbergCrt_Ico_filter_map a S ℓ c
  have hcard := congrArg card hmap
  rw [card_map] at hcard
  unfold selbergCrt_intCount
  exact_mod_cast hcard

/-- Expansion rounding: after writing `1[ℓ ∣ n−c]`, the interval
sum differs from `S/ℓ` by at most `1`. Not a sum over `λ_d λ_e`. -/
theorem selbergCrt_sum_indicator_abs_le (a S ℓ : ℕ) (c : ℤ)
    (hℓ : 1 ≤ ℓ) :
    |(∑ n ∈ Ico a (a + S), selbergCrt_indicator ℓ c n) - (S : ℝ) / ℓ| ≤
      1 := by
  rw [selbergCrt_sum_indicator_eq_intCount]
  exact selbergCrt_intCount_abs_le (a : ℤ) S ℓ c hℓ

/-- `lcm`-parameter form of the expansion error. No double sum over
pairs `(d,e)`. -/
theorem selbergCrt_sum_indicator_lcm_abs_le (a S d e : ℕ) (c : ℤ)
    (hℓ : 1 ≤ Nat.lcm d e) :
    |(∑ n ∈ Ico a (a + S), selbergCrt_indicator (Nat.lcm d e) c n) -
        (S : ℝ) / Nat.lcm d e| ≤ 1 :=
  selbergCrt_sum_indicator_abs_le a S (Nat.lcm d e) c hℓ

end

end PrimeGapNormality.Prime
