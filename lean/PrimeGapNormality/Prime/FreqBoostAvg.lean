import PrimeGapNormality.Prime.Fourier
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Frequency-boost Cesàro wrapper on a finite index set

Public interval wrapper

  `‖Avg_I e(C^h q U) − Avg_I e(q U)‖ ≤ 2 h k / card(I)`

for nonempty finite `I : Finset ℕ` (typically an interval),
`h k : ℕ`, integer base `C`, real frequency `q`, and `U : ℕ → ℝ`.

The `2hk/|I|` size is the index-shift cost, not a kernel, Weyl,
or (C4) remainder. At most `s = h k` entry and `s` exit points
on an interval (symmetric difference of `I` and `I + s`); each
unimodular summand contributes at most `1` before dividing by
`|I|`. Lower total degrees are **not** subtracted here (montage).

Does **not** import PeriodicKernel, ModesImplyWindowCount,
PrimeCountingNormalization, MixZeta, SingletonLi, or WeylMontageST.
Does **not** claim IntegerShiftCov, kernel close, Weyl-Montage,
or (C4). Geometric identity `C^h U n = U(n+hk)` remains a
hypothesis `hgeom` (highest homogeneous action, no lower
degrees).

**Compiled.**
1. `‖e t‖ = 1`.
2. `Avg I f = (∑_{n ∈ I} f n) / |I|` in `ℂ`.
3. Shift identity via symmetric difference of index sets;
   unimodular sums ⇒ `‖∑_I f(·+s) − ∑_I f‖ ≤ 2 · card(I+s \ I)`.
4. If `card(I+s \ I) ≤ s`, then
   `‖Avg I (f(·+s)) − Avg I f‖ ≤ 2 s / |I|`
   (`‖f n‖ ≤ 1`, `I` nonempty).
5. For `I = Ico a b`, `card(I+s \ I) ≤ s` (at most `s`
   entry/exit points).
6. Interval form of (4), no extra sdiff binder.
7. `hgeom` ⇒ `e(C^h q U n) = e(q U(n+hk))`.
8. Public wrapper on a general nonempty `Finset` (remaining:
   `hgeom` and `card(I+hk \ I) ≤ hk`).
9. Public interval wrapper on `Ico a b` (`hgeom`, `a < b`).

**Not compiled.** Kernel close. Weyl-Montage. (C4). Lower-degree
phase error. `IntegerShiftCov`. `ModesImplyWindowCount` /
`m_X → ∞`. PrimeCountingNormalization.

**Remaining hyps.** Geometric identity `hgeom`. On a general
`Finset`, the sdiff bound `card(I+hk \ I) ≤ hk` (theorem for
`Ico`). `I` nonempty (`a < b` on `Ico`).

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `‖e t‖ = 1` | theorem |
| unimodular shift via sdiff, cost `2 · card(I+s \ I)` | theorem |
| `card(Ico a b + s \ Ico a b) ≤ s` | theorem |
| `‖Avg (f(·+s)) − Avg f‖ ≤ 2s/\|I\|` (`‖f‖≤1`, sdiff `≤ s`) | theorem |
| same on `Ico a b` | theorem (`a < b`) |
| `hgeom` ⇒ `e(C^h q U n) = e(q U(n+hk))` | theorem |
| public Finset wrapper `≤ 2hk/\|I\|` | theorem (`hgeom`, sdiff `≤ hk`) |
| public `Ico` wrapper `≤ 2hk/\|I\|` | theorem (`hgeom`, `a < b`) |
| `hgeom` itself | remaining (not claimed from PeriodicKernel) |
| lower-degree phase error | not claimed (montage) |
| kernel / Weyl-Montage / (C4) | not claimed |

Does not claim the kernel is closed.
Does not claim Weyl-Montage or (C4).

Source: `rounds/round118/09_grok_v012_delta.md` P2;
`rounds/round118/02_fixed_rank_lean_and_normality.md` (1.1)–(1.2);
`PrimeGapNormality.Prime.Fourier.e`.
Contract: API
Audit: GREEN
-/

open Finset

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Circle character and Cesàro mean -/

private theorem freqBoost_two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

/-- Circle character has unit modulus. -/
theorem freqBoost_norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [freqBoost_two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

/-- Cesàro mean of a complex sequence on a finite index set. -/
noncomputable def freqBoost_avg (I : Finset ℕ) (f : ℕ → ℂ) : ℂ :=
  (∑ n ∈ I, f n) / (I.card : ℂ)

/-! ### Unimodular shift via symmetric difference -/

private theorem freqBoost_sum_sub_eq_sdiff (s t : Finset ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ s, g n - ∑ n ∈ t, g n =
      ∑ n ∈ s \ t, g n - ∑ n ∈ t \ s, g n := by
  have hs : ∑ n ∈ s, g n = ∑ n ∈ s \ t, g n + ∑ n ∈ s ∩ t, g n := by
    have hunion : (s \ t) ∪ (s ∩ t) = s := sdiff_union_inter s t
    have hdisj : Disjoint (s \ t) (s ∩ t) := disjoint_sdiff_inter s t
    rw [← sum_union hdisj, hunion]
  have ht : ∑ n ∈ t, g n = ∑ n ∈ t \ s, g n + ∑ n ∈ t ∩ s, g n := by
    have hunion : (t \ s) ∪ (t ∩ s) = t := sdiff_union_inter t s
    have hdisj : Disjoint (t \ s) (t ∩ s) := disjoint_sdiff_inter t s
    rw [← sum_union hdisj, hunion]
  have hinter : s ∩ t = t ∩ s := inter_comm _ _
  rw [hs, ht, hinter]
  abel

private theorem freqBoost_norm_sum_le_card (s : Finset ℕ) (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) : ‖∑ n ∈ s, g n‖ ≤ (s.card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ n ∈ s, ‖g n‖ ≤ ∑ n ∈ s, (1 : ℝ) :=
    sum_le_sum fun _ _ => hg _
  have hc : (∑ n ∈ s, (1 : ℝ)) = (s.card : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_one]
  exact h1.trans_eq hc

private theorem freqBoost_sum_shift_eq_image (I : Finset ℕ) (f : ℕ → ℂ)
    (s : ℕ) :
    ∑ n ∈ I, f (n + s) = ∑ m ∈ I.image (fun n => n + s), f m := by
  exact (sum_image fun _ _ _ _ hxy => Nat.add_right_cancel hxy).symm

private theorem freqBoost_sdiff_card_eq_of_card_eq {s t : Finset ℕ}
    (h : s.card = t.card) : (s \ t).card = (t \ s).card := by
  have hs : (s \ t).card + (s ∩ t).card = s.card := by
    rw [← card_union_of_disjoint (disjoint_sdiff_inter s t),
      sdiff_union_inter s t]
  have ht : (t \ s).card + (t ∩ s).card = t.card := by
    rw [← card_union_of_disjoint (disjoint_sdiff_inter t s),
      sdiff_union_inter t s]
  have hinter : s ∩ t = t ∩ s := inter_comm s t
  rw [hinter] at hs
  have hs' : (s \ t).card + (t ∩ s).card = t.card := hs.trans h
  have heq :
      (s \ t).card + (t ∩ s).card = (t \ s).card + (t ∩ s).card :=
    hs'.trans ht.symm
  exact Nat.add_right_cancel heq

private theorem freqBoost_image_add_card (I : Finset ℕ) (s : ℕ) :
    (I.image (fun n => n + s)).card = I.card := by
  refine card_image_of_injective I ?_
  intro x y hxy
  exact Nat.add_right_cancel hxy

/-- Unimodular Cesàro shift. Remaining: `card(I+s \ I) ≤ s`.
On an interval this sdiff bound is a theorem
(`freqBoost_Ico_sdiff_card_le`). Does **not** claim a kernel. -/
theorem freqBoost_shift_avg_norm_le (I : Finset ℕ) (f : ℕ → ℂ) (s : ℕ)
    (hI : I.Nonempty) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hsdiff : (I.image (fun n => n + s) \ I).card ≤ s) :
    ‖freqBoost_avg I (fun n => f (n + s)) - freqBoost_avg I f‖
      ≤ 2 * (s : ℝ) / I.card := by
  have hpos : 0 < I.card := card_pos.mpr hI
  unfold freqBoost_avg
  rw [← sub_div, norm_div]
  have hnc : ‖(I.card : ℂ)‖ = (I.card : ℝ) := by simp
  rw [hnc]
  have hsum := freqBoost_sum_shift_eq_image I f s
  have hdiff :
      ∑ n ∈ I, f (n + s) - ∑ n ∈ I, f n =
        ∑ n ∈ I.image (fun n => n + s) \ I, f n
          - ∑ n ∈ I \ I.image (fun n => n + s), f n := by
    rw [hsum]
    exact freqBoost_sum_sub_eq_sdiff _ _ _
  have hA :=
    freqBoost_norm_sum_le_card (I.image (fun n => n + s) \ I) f hf
  have hB :=
    freqBoost_norm_sum_le_card (I \ I.image (fun n => n + s)) f hf
  have htri :
      ‖∑ n ∈ I, f (n + s) - ∑ n ∈ I, f n‖ ≤
        ((I.image (fun n => n + s) \ I).card : ℝ)
          + ((I \ I.image (fun n => n + s)).card : ℝ) := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add hA hB)
  have hcardEq := freqBoost_image_add_card I s
  have hs2 :
      ((I \ I.image (fun n => n + s)).card : ℝ) ≤ (s : ℝ) := by
    have hceq :
        (I \ I.image (fun n => n + s)).card =
          (I.image (fun n => n + s) \ I).card :=
      freqBoost_sdiff_card_eq_of_card_eq hcardEq.symm
    exact Nat.cast_le.mpr (hceq.trans_le hsdiff)
  have h1 :
      ((I.image (fun n => n + s) \ I).card : ℝ) ≤ (s : ℝ) :=
    Nat.cast_le.mpr hsdiff
  have h2s :
      ((I.image (fun n => n + s) \ I).card : ℝ)
          + ((I \ I.image (fun n => n + s)).card : ℝ)
        ≤ 2 * (s : ℝ) := by
    have hss : (s : ℝ) + s = 2 * (s : ℝ) := by ring
    exact (add_le_add h1 hs2).trans_eq hss
  have hbd : ‖∑ n ∈ I, f (n + s) - ∑ n ∈ I, f n‖ ≤ 2 * (s : ℝ) :=
    htri.trans h2s
  exact div_le_div_of_nonneg_right hbd (Nat.cast_pos.mpr hpos).le

/-! ### Interval geometry: at most `s` entry/exit points -/

private theorem freqBoost_image_add_Ico (a b s : ℕ) :
    (Ico a b).image (fun n => n + s) = Ico (a + s) (b + s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    have hnI := mem_Ico.mp hn
    exact mem_Ico.mpr
      ⟨Nat.add_le_add_right hnI.1 s, Nat.add_lt_add_right hnI.2 s⟩
  · intro hx
    have hxI := mem_Ico.mp hx
    have hs : s ≤ x := le_trans (Nat.le_add_left s a) hxI.1
    refine mem_image.mpr ⟨x - s, mem_Ico.mpr ⟨?_, ?_⟩, Nat.sub_add_cancel hs⟩
    · have hle : a + s ≤ (x - s) + s := by
        rw [Nat.sub_add_cancel hs]
        exact hxI.1
      exact Nat.le_of_add_le_add_right hle
    · have hlt : x - s + s < b + s := by
        rw [Nat.sub_add_cancel hs]
        exact hxI.2
      exact Nat.lt_of_add_lt_add_right hlt

private theorem freqBoost_Ico_add_sdiff_subset (a b s : ℕ) :
    Ico (a + s) (b + s) \ Ico a b ⊆ Ico b (b + s) := by
  intro x hx
  have hxmem := mem_sdiff.mp hx
  have hxR := mem_Ico.mp hxmem.1
  have hxL : x ∉ Ico a b := hxmem.2
  rw [mem_Ico]
  refine ⟨?_, hxR.2⟩
  rcases lt_or_ge x b with hxb | hxb
  · have hnot : ¬ (a ≤ x ∧ x < b) := fun h => hxL (mem_Ico.mpr h)
    have hna : ¬ a ≤ x := fun ha => hnot ⟨ha, hxb⟩
    have ha : a ≤ x := le_trans (Nat.le_add_right a s) hxR.1
    exact (hna ha).elim
  · exact hxb

/-- On `Ico a b`, shifting indices by `s` changes at most `s`
points. Does **not** claim a kernel. -/
theorem freqBoost_Ico_sdiff_card_le (a b s : ℕ) :
    ((Ico a b).image (fun n => n + s) \ Ico a b).card ≤ s := by
  rw [freqBoost_image_add_Ico]
  have hle :
      (Ico (a + s) (b + s) \ Ico a b).card ≤ (Ico b (b + s)).card :=
    card_le_card (freqBoost_Ico_add_sdiff_subset a b s)
  have hcard : (Ico b (b + s)).card = s := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  exact hle.trans_eq hcard

private theorem freqBoost_Ico_nonempty {a b : ℕ} (h : a < b) :
    (Ico a b).Nonempty :=
  ⟨a, mem_Ico.mpr ⟨le_rfl, h⟩⟩

/-- Interval form of the unimodular shift bound. Remaining:
`a < b`. Does **not** claim a kernel. -/
theorem freqBoost_shift_avg_norm_le_Ico {a b : ℕ} (hI : a < b)
    (f : ℕ → ℂ) (s : ℕ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖freqBoost_avg (Ico a b) (fun n => f (n + s))
        - freqBoost_avg (Ico a b) f‖
      ≤ 2 * (s : ℝ) / (Ico a b).card :=
  freqBoost_shift_avg_norm_le (Ico a b) f s (freqBoost_Ico_nonempty hI) hf
    (freqBoost_Ico_sdiff_card_le a b s)

/-! ### Highest homogeneous geometric action -/

/-- Pure highest homogeneous action: `e(C^h q U n) = e(q U(n+hk))`.
Remaining: `hgeom`. Lower total degrees are not subtracted. -/
theorem freqBoost_e_geom (h k : ℕ) (C : ℕ) (q : ℝ) (U : ℕ → ℝ)
    (hgeom : ∀ n, (C ^ h : ℝ) * U n = U (n + h * k)) (n : ℕ) :
    e ((C ^ h : ℝ) * q * U n) = e (q * U (n + h * k)) := by
  have hmul : (C ^ h : ℝ) * q * U n = q * U (n + h * k) := by
    calc
      (C ^ h : ℝ) * q * U n
          = q * (C ^ h : ℝ) * U n := by
            rw [mul_comm (C ^ h : ℝ) q]
      _ = q * ((C ^ h : ℝ) * U n) := by rw [mul_assoc]
      _ = q * U (n + h * k) := by rw [hgeom n]
  exact congrArg e hmul

/-- Public Finset wrapper. Remaining: geometric identity `hgeom`
and `card(I+hk \ I) ≤ hk` (theorem on `Ico`). Does **not**
subtract lower total degrees. Does **not** claim kernel,
Weyl-Montage, or (C4). -/
theorem freqBoost_avg_e_norm_le {I : Finset ℕ} (hI : I.Nonempty)
    (h k : ℕ) (C : ℕ) (q : ℝ) (U : ℕ → ℝ)
    (hgeom : ∀ n, (C ^ h : ℝ) * U n = U (n + h * k))
    (hsdiff : (I.image (fun n => n + h * k) \ I).card ≤ h * k) :
    ‖freqBoost_avg I (fun n => e ((C ^ h : ℝ) * q * U n))
        - freqBoost_avg I (fun n => e (q * U n))‖
      ≤ 2 * ((h * k : ℕ) : ℝ) / I.card := by
  have hf : ∀ n, ‖e (q * U n)‖ ≤ 1 := fun n =>
    (freqBoost_norm_e (q * U n)).le
  have hrew :
      freqBoost_avg I (fun n => e (q * U (n + h * k))) =
        freqBoost_avg I (fun n => e ((C ^ h : ℝ) * q * U n)) := by
    refine congrArg (freqBoost_avg I) ?_
    funext n
    exact (freqBoost_e_geom h k C q U hgeom n).symm
  rw [← hrew]
  exact freqBoost_shift_avg_norm_le I (fun n => e (q * U n)) (h * k) hI hf
    hsdiff

/-- Public interval wrapper on `Ico a b`. Remaining: `hgeom` and
`a < b`. Does **not** subtract lower total degrees. Does **not**
claim kernel, Weyl-Montage, or (C4). -/
theorem freqBoost_avg_e_norm_le_Ico {a b : ℕ} (hI : a < b)
    (h k : ℕ) (C : ℕ) (q : ℝ) (U : ℕ → ℝ)
    (hgeom : ∀ n, (C ^ h : ℝ) * U n = U (n + h * k)) :
    ‖freqBoost_avg (Ico a b) (fun n => e ((C ^ h : ℝ) * q * U n))
        - freqBoost_avg (Ico a b) (fun n => e (q * U n))‖
      ≤ 2 * ((h * k : ℕ) : ℝ) / (Ico a b).card :=
  freqBoost_avg_e_norm_le (freqBoost_Ico_nonempty hI) h k C q U hgeom
    (freqBoost_Ico_sdiff_card_le a b (h * k))

end

end PrimeGapNormality.Prime
