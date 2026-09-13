import PrimeGapNormality.Prime.ChebyshevNthPrime
import PrimeGapNormality.Prime.ConditionT
import PrimeGapNormality.Prime.PosMassScale
import PrimeGapNormality.Prime.PrimeIndex
import PrimeGapNormality.Prime.StatisticalCriterion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Chebyshev/Bertrand substitutes for paper S/T/D on `nthPrime`

Specialises `StatisticalCriterion` `ShortPatternS` / `GapTailT` /
`IndexPassageD` to `a = nthPrime`, using only mathlib Chebyshev and
Bertrand. There is no prime-number theorem (`π(x) ∼ x / log x`).

## What compiles

1. Identifications: `seqCount nthPrime = π`, dyadic `seqWindow nthPrime`
   equals `primeIndexBlock`, and `seqGapTail` is `gapTail` on prime gaps.
2. Chebyshev inversion `p_n ≤ 4 (n+1)(log(n+2)+1)` upgrades
   `F_ρ(n)` from `O_ρ(n²)` to `O_ρ(n log n)`, and likewise for `T_ρ`.
3. Dyadic condition T: the tailmass comparison
   `Avg_{I_X} T_ρ(n+L) ≤ F_ρ(π(2X)+L) / m_X` with Bertrand `m_X ≥ 1`.
   With the Chebyshev-log mass this is `O_ρ(X)`, hence
   `GapTailT nthPrime ρ (fun X => X)` (linear scale), **not**
   `GapTailT` at `G = log X`.
4. Triad window `(X, 3X]`: eventually
   `π(3X) - π(X) ≥ (log 2 / 4) · X / log(3X)`, and the tailmass
   average on that window is `O_ρ(log X)`.
5. Index D sandwich: `1-ε ≤ π(2 p_M)/(M+1) ≤ 4+ε`. Equivalent
   restatement of `PrimeIndex.chebyshev_index_passage` in
   `IndexPassageD` language. The window-size ratio stays in `[0, 3+ε]`.

## Blockers (no axiom, `IndexPassageD` not silently weakened)

- `GapTailT nthPrime ρ (fun X => Real.log X)` on dyadic `seqWindow`
  blocked because: Chebyshev leading constants cancel on `(X, 2X]`
  (`2 log 2 - log 4 = 0`), so `m_X ≥ 1` only (Bertrand). Even with
  `F_ρ(n) = O_ρ(n log n)` the dyadic average is `O_ρ(X)`, not
  `O_ρ(log X)`. Closing `≪_ρ log X` on `I_X` needs
  `m_X ≫ X / log X` (PNT-scale).
- `IndexPassageD nthPrime` blocked because: `π(2 p_M) = 2M + o(M)`
  is `π(2 p_M)/(M+1) → 2`, which needs PNT-scale; Chebyshev only
  gives the ratio eventually in `[1-ε, 4+ε]`.
- `ShortPatternS nthPrime` is not claimed: AHL/Kuperberg transfer of
  admissible short-pattern tests onto genuine prime windows is not a
  Chebyshev theorem (see `ModelShortPattern`, `StoppedAHL`).

Source: `StatisticalCriterion`; `ConditionT`; `WindowDensity`
(triad constants, re-proved here to avoid the `All` import);
`PosMassScale`; `PrimeIndex`; `ChebyshevNthPrime`; EndAPI `nthPrime`.
Contract: API
Audit: GREEN
-/

open Finset Filter
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Elementary comparisons -/

private theorem rho_pos {ρ : ℝ} (hρ : 1 < ρ) : 0 < ρ :=
  lt_trans (by norm_num) hρ

private theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

private theorem nat_eq_of_forall_lt_iff {m n : ℕ}
    (h : ∀ k, k < m ↔ k < n) : m = n := by
  have hm : ¬ m < n := fun hmn => Nat.lt_irrefl m ((h m).mpr hmn)
  have hn : ¬ n < m := fun hnm => Nat.lt_irrefl n ((h n).mp hnm)
  omega

private theorem one_le_log_of_three_le {X : ℕ} (hX : 3 ≤ X) :
    (1 : ℝ) ≤ Real.log X := by
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
    rwa [Real.log_exp] at h
  have hle : Real.log 3 ≤ Real.log X :=
    Real.log_le_log (by positivity : (0 : ℝ) < 3) (by exact_mod_cast hX)
  exact h3.trans hle

private theorem add_one_le_mul_succ (n j : ℕ) :
    n + j + 1 ≤ (n + 1) * (j + 1) := by
  have heq : (n + 1) * (j + 1) = n * j + n + j + 1 := by ring
  rw [heq, Nat.add_assoc (n * j), Nat.add_assoc (n * j)]
  exact Nat.le_add_left (n + j + 1) (n * j)

private theorem add_two_le_mul_succ (n j : ℕ) :
    n + j + 2 ≤ (n + 2) * (j + 1) := by
  have heq : (n + 2) * (j + 1) = n * j + n + 2 * j + 2 := by ring
  rw [heq]
  have hle : n + j + 2 ≤ n + 2 * j + 2 := by
    have hj : j ≤ 2 * j := Nat.le_mul_of_pos_left j (by omega : 0 < 2)
    omega
  have hassoc : n * j + n + 2 * j + 2 = n * j + (n + 2 * j + 2) := by
    simp [Nat.add_assoc]
  rw [hassoc]
  exact hle.trans (Nat.le_add_left (n + 2 * j + 2) (n * j))

private theorem sqrt_le_add {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ x + 1 := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hnn : 0 ≤ (Real.sqrt x - 1) ^ 2 := sq_nonneg _
  have hexp : (Real.sqrt x - 1) ^ 2 =
      Real.sqrt x ^ 2 - 2 * Real.sqrt x + 1 := by
    ring
  have : 0 ≤ x - 2 * Real.sqrt x + 1 := by
    rwa [hexp, hsq] at hnn
  have h2 : 2 * Real.sqrt x ≤ x + 1 := by linarith
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  linarith

private theorem add_sqrt_le {x : ℝ} (hx : 0 ≤ x) :
    x + Real.sqrt x ≤ 2 * x + 1 := by
  linarith [sqrt_le_add hx]

/-! ### Identifications with `StatisticalCriterion` -/

/-- `A(x) = π(x)` on the prime enumeration. -/
theorem seqCount_nthPrime (x : ℕ) :
    seqCount nthPrime x = Nat.primeCounting x := by
  have h : ∀ n, n < seqCount nthPrime x ↔ n < Nat.primeCounting x := fun n =>
    (seqCount_lt_iff nthPrime_strictMono).trans (nthPrime_le_iff_lt_primeCounting n x)
  exact nat_eq_of_forall_lt_iff h

theorem seqWindow_nthPrime_eq_primeIndexBlock (X : ℕ) :
    seqWindow nthPrime X = primeIndexBlock X := by
  ext n
  simp only [seqWindow, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · intro h
    exact mem_primeIndexBlock_iff.mpr ⟨h.2.1, h.2.2⟩
  · intro h
    have h' := mem_primeIndexBlock_iff.mp h
    exact ⟨le_trans (strictMono_le_id nthPrime_strictMono n) h'.2, h'.1, h'.2⟩

theorem seqWindow_nthPrime_card (X : ℕ) :
    (seqWindow nthPrime X).card = windowNX X := by
  rw [seqWindow_nthPrime_eq_primeIndexBlock, card_primeIndexBlock_eq_windowNX]

/-- Bertrand: dyadic `I_X` is nonempty for `X > 0`. -/
theorem card_seqWindow_nthPrime_pos {X : ℕ} (hX : 0 < X) :
    0 < (seqWindow nthPrime X).card := by
  rw [seqWindow_nthPrime_eq_primeIndexBlock]
  exact card_primeIndexBlock_pos hX

theorem seqWindow_nthPrime_at_self (M : ℕ) :
    (seqWindow nthPrime (nthPrime M)).card =
      Nat.primeCounting (2 * nthPrime M) - (M + 1) := by
  rw [seqWindow_card nthPrime_strictMono, seqCount_nthPrime]

theorem seqGapTail_nthPrime (ρ : ℝ) (n : ℕ) :
    seqGapTail ρ nthPrime n = gapTail ρ (fun k => (primeGap k : ℝ)) n := by
  simp [seqGapTail, gapTail, seqGap_nthPrime]

/-- Dilated paper window `{n : X < a_n ≤ kX}`. -/
def seqWindowMul (a : ℕ → ℕ) (k X : ℕ) : Finset ℕ :=
  (range (k * X + 1)).filter (fun n => X < a n ∧ a n ≤ k * X)

theorem seqWindowMul_two (a : ℕ → ℕ) : seqWindowMul a 2 = seqWindow a :=
  rfl

theorem seqWindowMul_mono_left {a : ℕ → ℕ} {k l X : ℕ} (h : k ≤ l) :
    seqWindowMul a k X ⊆ seqWindowMul a l X := by
  intro n hn
  simp only [seqWindowMul, mem_filter, mem_range, Nat.lt_succ_iff] at hn ⊢
  refine ⟨le_trans hn.1 (Nat.mul_le_mul_right X h), hn.2.1,
    le_trans hn.2.2 (Nat.mul_le_mul_right X h)⟩

theorem mem_seqWindowMul_nthPrime_iff {k X n : ℕ} :
    n ∈ seqWindowMul nthPrime k X ↔
      X < nthPrime n ∧ nthPrime n ≤ k * X := by
  simp only [seqWindowMul, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h => ⟨h.2.1, h.2.2⟩
  · intro h
    exact ⟨le_trans (strictMono_le_id nthPrime_strictMono n) h.2, h.1, h.2⟩

theorem seqWindowMul_nthPrime_eq_Ico (k X : ℕ) :
    seqWindowMul nthPrime k X =
      Ico (Nat.primeCounting X) (Nat.primeCounting (k * X)) := by
  ext n
  rw [mem_seqWindowMul_nthPrime_iff, mem_Ico]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have : ¬ nthPrime n ≤ X := not_le.mpr h.1
      rw [nthPrime_le_iff_succ_le_pi, not_le] at this
      exact Nat.lt_succ_iff.mp this
    · exact Nat.lt_of_succ_le ((nthPrime_le_iff_succ_le_pi n (k * X)).1 h.2)
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← not_le, nthPrime_le_iff_succ_le_pi, not_le]
      exact Nat.lt_succ_of_le h.1
    · exact (nthPrime_le_iff_succ_le_pi n (k * X)).2 (Nat.succ_le_of_lt h.2)

theorem card_seqWindowMul_nthPrime (k X : ℕ) :
    (seqWindowMul nthPrime k X).card =
      Nat.primeCounting (k * X) - Nat.primeCounting X := by
  rw [seqWindowMul_nthPrime_eq_Ico, Nat.card_Ico]

theorem card_seqWindowMul_nthPrime_cast {k X : ℕ} (hk : 1 ≤ k) :
    ((seqWindowMul nthPrime k X).card : ℝ) =
      (Nat.primeCounting (k * X) : ℝ) - Nat.primeCounting X := by
  have hle : Nat.primeCounting X ≤ Nat.primeCounting (k * X) :=
    Nat.monotone_primeCounting (Nat.le_mul_of_pos_left X (by omega))
  rw [card_seqWindowMul_nthPrime, Nat.cast_sub hle]

/-- Bertrand on `(X, 2X]` plus monotonicity in the dilation. -/
theorem card_seqWindowMul_nthPrime_pos {k X : ℕ} (hk : 2 ≤ k) (hX : 0 < X) :
    0 < (seqWindowMul nthPrime k X).card := by
  have h2 : 0 < (seqWindowMul nthPrime 2 X).card := by
    simpa [seqWindowMul_two] using card_seqWindow_nthPrime_pos hX
  exact lt_of_lt_of_le h2
    (card_le_card (seqWindowMul_mono_left (a := nthPrime) (k := 2) (X := X) hk))

/-! ### Chebyshev-log scale of `F_ρ` and `T_ρ` -/

/-- Explicit factor: `F_ρ(n) ≤ 4 C_geom(ρ) (n+1)(log(n+2)+1)`. -/
noncomputable def posMassChebyshevCoeff (ρ : ℝ) : ℝ :=
  4 * posMassGeomCoeff ρ

theorem posMassChebyshevCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) :
    0 ≤ posMassChebyshevCoeff ρ :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (posMassGeomCoeff_nonneg hρ)

private theorem nthPrime_shift_le_geom (n j : ℕ) :
    ((n + j + 1 : ℕ) : ℝ) * (Real.log ((n + j + 2 : ℕ) : ℝ) + 1) ≤
      ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
        ((j + 1 : ℕ) : ℝ) ^ 2 := by
  have hidx : n + j + 1 ≤ (n + 1) * (j + 1) := add_one_le_mul_succ n j
  have hidxR : ((n + j + 1 : ℕ) : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hidx
  have hn2pos : (0 : ℝ) < (n + j + 2 : ℕ) := by
    exact_mod_cast (Nat.succ_pos (n + j + 1))
  have hle : n + j + 2 ≤ (n + 2) * (j + 1) := add_two_le_mul_succ n j
  have hleR : ((n + j + 2 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hlogle : Real.log ((n + j + 2 : ℕ) : ℝ) ≤
      Real.log ((n + 2 : ℕ) : ℝ) + Real.log ((j + 1 : ℕ) : ℝ) := by
    have hlog := Real.log_le_log hn2pos hleR
    have hn0 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero (n + 1))
    have hj0 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero j)
    rwa [Real.log_mul hn0 hj0] at hlog
  have hlog1 : Real.log ((n + j + 2 : ℕ) : ℝ) + 1 ≤
      (Real.log ((n + 2 : ℕ) : ℝ) + 1) * (Real.log ((j + 1 : ℕ) : ℝ) + 1) := by
    have hnlog : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hjlog : 0 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hstep :
        Real.log ((n + 2 : ℕ) : ℝ) + Real.log ((j + 1 : ℕ) : ℝ) + 1 ≤
          (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
            (Real.log ((j + 1 : ℕ) : ℝ) + 1) := by
      have hdiff :
          (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
              (Real.log ((j + 1 : ℕ) : ℝ) + 1) -
            (Real.log ((n + 2 : ℕ) : ℝ) + Real.log ((j + 1 : ℕ) : ℝ) + 1) =
            Real.log ((n + 2 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ) := by
        ring
      have hnn : 0 ≤
          Real.log ((n + 2 : ℕ) : ℝ) * Real.log ((j + 1 : ℕ) : ℝ) :=
        mul_nonneg hnlog hjlog
      linarith [hdiff, hnn]
    have hmid :
        Real.log ((n + j + 2 : ℕ) : ℝ) + 1 ≤
          Real.log ((n + 2 : ℕ) : ℝ) + Real.log ((j + 1 : ℕ) : ℝ) + 1 :=
      _root_.add_le_add hlogle (le_rfl : (1 : ℝ) ≤ 1)
    exact hmid.trans hstep
  have hjlog : Real.log ((j + 1 : ℕ) : ℝ) + 1 ≤ ((j + 1 : ℕ) : ℝ) := by
    have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
    have := Real.log_le_sub_one_of_pos hjpos
    linarith
  have hnn2 : 0 ≤ Real.log ((n + j + 2 : ℕ) : ℝ) + 1 :=
    add_nonneg (Real.log_natCast_nonneg _) (by norm_num)
  have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hj1 : 0 ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnlog1 : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) + 1 :=
    add_nonneg (Real.log_natCast_nonneg _) (by norm_num)
  have hprod1 :=
    mul_le_mul hidxR hlog1 hnn2 (mul_nonneg hn1 hj1)
  have hR :
      ((n + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) *
          ((Real.log ((n + 2 : ℕ) : ℝ) + 1) * (Real.log ((j + 1 : ℕ) : ℝ) + 1)) ≤
        ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
          ((j + 1 : ℕ) : ℝ) ^ 2 := by
    have hmid : ((j + 1 : ℕ) : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) + 1) ≤
        ((j + 1 : ℕ) : ℝ) ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hjlog hj1
    have : ((n + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) *
          ((Real.log ((n + 2 : ℕ) : ℝ) + 1) * (Real.log ((j + 1 : ℕ) : ℝ) + 1)) =
        ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
          (((j + 1 : ℕ) : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) + 1)) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hmid (mul_nonneg hn1 hnlog1)
  exact hprod1.trans hR

private theorem nthPrime_div_pow_le_chebyshev_sq {ρ : ℝ} (hρ : 1 < ρ)
    (n j : ℕ) :
    (nthPrime (n + j) : ℝ) / ρ ^ (j + 1) ≤
      4 * (((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1)) *
        (((j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) := by
  have hbound := nthPrime_le_succ_mul_log (n + j)
  have hden : 0 ≤ ρ ^ (j + 1) := pow_nonneg (rho_pos hρ).le _
  have hnum :
      (nthPrime (n + j) : ℝ) ≤
        4 * (((n + j + 1 : ℕ) : ℝ) * (Real.log ((n + j + 2 : ℕ) : ℝ) + 1)) := by
    simpa [mul_assoc] using hbound
  have hdiv := div_le_div_of_nonneg_right hnum hden
  have hgeom := nthPrime_shift_le_geom n j
  have hgeom' :
      4 * (((n + j + 1 : ℕ) : ℝ) * (Real.log ((n + j + 2 : ℕ) : ℝ) + 1)) /
          ρ ^ (j + 1) ≤
        4 * (((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
          ((j + 1 : ℕ) : ℝ) ^ 2) / ρ ^ (j + 1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom (by norm_num)) hden
  have hrew :
      4 * (((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1) *
          ((j + 1 : ℕ) : ℝ) ^ 2) / ρ ^ (j + 1) =
        4 * (((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1)) *
          (((j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) := by
    ring
  exact hdiv.trans (hgeom'.trans_eq hrew)

/-- Chebyshev inversion plus geometric squares: `F_ρ(n) = O_ρ(n log n)`. -/
theorem posMass_nthPrime_le_chebyshev_log {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      posMassChebyshevCoeff ρ * ((n + 1 : ℕ) : ℝ) *
        (Real.log ((n + 2 : ℕ) : ℝ) + 1) := by
  set c : ℝ := ((n + 1 : ℕ) : ℝ) * (Real.log ((n + 2 : ℕ) : ℝ) + 1)
  have hc : 0 ≤ c :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
  have hterm : ∀ j : ℕ,
      (nthPrime (n + j) : ℝ) / ρ ^ (j + 1) ≤
        (4 * c) * (((0 + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) := by
    intro j
    have h := nthPrime_div_pow_le_chebyshev_sq hρ n j
    have hj : ((j + 1 : ℕ) : ℝ) = ((0 + j + 1 : ℕ) : ℝ) := by
      simp [Nat.zero_add]
    simpa [c, hj] using h
  have hdom : Summable fun j : ℕ =>
      (4 * c) * (((0 + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) :=
    (summable_succ_sq_div_pow hρ 0).mul_left (4 * c)
  have hf := summable_posMass_nthPrime hρ n
  have hle := hf.tsum_le_tsum hterm hdom
  have htsum :
      ∑' j : ℕ, (4 * c) * (((0 + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1)) =
        (4 * c) * ∑' j : ℕ, ((0 + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1) :=
    (summable_succ_sq_div_pow hρ 0).tsum_mul_left (4 * c)
  have hgeom : ∑' j : ℕ, ((0 + j + 1 : ℕ) : ℝ) ^ 2 / ρ ^ (j + 1) ≤
      posMassGeomCoeff ρ := by
    have h := tsum_succ_sq_div_pow_le hρ 0
    have hsq : ((0 + 1 : ℕ) : ℝ) ^ 2 = (1 : ℝ) := by
      simp
    simpa [hsq, mul_one] using h
  have hmass : posMass ρ (fun k => (nthPrime k : ℝ)) n ≤
      (4 * c) * posMassGeomCoeff ρ := by
    rw [posMass]
    refine hle.trans ?_
    rw [htsum]
    exact mul_le_mul_of_nonneg_left hgeom (mul_nonneg (by norm_num) hc)
  have hrew : (4 * c) * posMassGeomCoeff ρ =
      posMassChebyshevCoeff ρ * ((n + 1 : ℕ) : ℝ) *
        (Real.log ((n + 2 : ℕ) : ℝ) + 1) := by
    unfold posMassChebyshevCoeff c
    ring
  exact hmass.trans_eq hrew

theorem gapTail_prime_le_chebyshev_log {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    gapTail ρ (fun k => (primeGap k : ℝ)) n ≤
      posMassChebyshevCoeff ρ * ((n + 2 : ℕ) : ℝ) *
        (Real.log ((n + 3 : ℕ) : ℝ) + 1) := by
  have h1 := gapTail_prime_le_posMass_succ hρ n
  have h2 := posMass_nthPrime_le_chebyshev_log hρ (n + 1)
  have hN : n + 1 + 1 = n + 2 := by omega
  have hM : n + 1 + 2 = n + 3 := by omega
  have h2' : posMass ρ (fun k => (nthPrime k : ℝ)) (n + 1) ≤
      posMassChebyshevCoeff ρ * ((n + 2 : ℕ) : ℝ) *
        (Real.log ((n + 3 : ℕ) : ℝ) + 1) := by
    simpa [hN, hM] using h2
  exact h1.trans h2'

theorem seqGapTail_nthPrime_le_chebyshev_log {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    seqGapTail ρ nthPrime n ≤
      posMassChebyshevCoeff ρ * ((n + 2 : ℕ) : ℝ) *
        (Real.log ((n + 3 : ℕ) : ℝ) + 1) := by
  rw [seqGapTail_nthPrime]
  exact gapTail_prime_le_chebyshev_log hρ n

/-! ### Tailmass comparison on dyadic and dilated windows -/

private theorem primeCounting_pred_add {k X L : ℕ}
    (hπ : 1 ≤ Nat.primeCounting (k * X)) :
    Nat.primeCounting (k * X) - 1 + L + 1 = Nat.primeCounting (k * X) + L := by
  omega

/-- Paper display after `lem:tailmass`, on any dilated prime window. -/
theorem conditionT_seqWindowMul_nthPrime {ρ : ℝ} (hρ : 1 < ρ)
    (k X L : ℕ) (hm : 0 < (seqWindowMul nthPrime k X).card) :
    windowAvgReal (seqWindowMul nthPrime k X)
        (fun n => seqGapTail ρ nthPrime (n + L)) ≤
      posMass ρ (fun t => (nthPrime t : ℝ))
          (Nat.primeCounting (k * X) + L) /
        ((seqWindowMul nthPrime k X).card : ℝ) := by
  have hπ : 1 ≤ Nat.primeCounting (k * X) := by
    have hlt : Nat.primeCounting X < Nat.primeCounting (k * X) := by
      have hpos : 0 <
          Nat.primeCounting (k * X) - Nat.primeCounting X := by
        rwa [card_seqWindowMul_nthPrime] at hm
      exact tsub_pos_iff_lt.mp hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hs : seqWindowMul nthPrime k X ⊆
      Icc (Nat.primeCounting X) (Nat.primeCounting (k * X) - 1) := by
    intro n hn
    rw [mem_Icc]
    have hIco := mem_Ico.mp ((seqWindowMul_nthPrime_eq_Ico k X) ▸ hn)
    exact ⟨hIco.1, Nat.le_pred_of_lt hIco.2⟩
  have hle : ∀ n ∈ seqWindowMul nthPrime k X,
      n ≤ Nat.primeCounting (k * X) - 1 :=
    fun n hn => (mem_Icc.mp (hs hn)).2
  have hsum :=
    sum_primeGapTail_of_le_le_posMass (L := L) hρ hle
  have hfun :
      ∑ n ∈ seqWindowMul nthPrime k X, seqGapTail ρ nthPrime (n + L) =
        ∑ n ∈ seqWindowMul nthPrime k X,
          gapTail ρ (fun t => (primeGap t : ℝ)) (n + L) :=
    sum_congr rfl fun n _ => seqGapTail_nthPrime ρ (n + L)
  have hdiv :=
    div_le_div_of_nonneg_right (hfun.trans_le hsum)
      (Nat.cast_nonneg (seqWindowMul nthPrime k X).card)
  have hN := primeCounting_pred_add (L := L) hπ
  unfold windowAvgReal
  rwa [hN] at hdiv

theorem conditionT_seqWindow_nthPrime {ρ : ℝ} (hρ : 1 < ρ) (X L : ℕ)
    (hm : 0 < (seqWindow nthPrime X).card) :
    windowAvgReal (seqWindow nthPrime X)
        (fun n => seqGapTail ρ nthPrime (n + L)) ≤
      posMass ρ (fun t => (nthPrime t : ℝ))
          (Nat.primeCounting (2 * X) + L) /
        ((seqWindow nthPrime X).card : ℝ) := by
  simpa [seqWindowMul_two] using
    conditionT_seqWindowMul_nthPrime hρ 2 X L (by simpa [seqWindowMul_two] using hm)

theorem conditionT_seqWindowMul_nthPrime_chebyshev_log {ρ : ℝ} (hρ : 1 < ρ)
    (k X L : ℕ) (hm : 0 < (seqWindowMul nthPrime k X).card) :
    windowAvgReal (seqWindowMul nthPrime k X)
        (fun n => seqGapTail ρ nthPrime (n + L)) ≤
      posMassChebyshevCoeff ρ *
          ((Nat.primeCounting (k * X) + L + 1 : ℕ) : ℝ) *
          (Real.log ((Nat.primeCounting (k * X) + L + 2 : ℕ) : ℝ) + 1) /
        ((seqWindowMul nthPrime k X).card : ℝ) := by
  have hT := conditionT_seqWindowMul_nthPrime hρ k X L hm
  have hF :=
    posMass_nthPrime_le_chebyshev_log hρ (Nat.primeCounting (k * X) + L)
  have hden : 0 ≤ ((seqWindowMul nthPrime k X).card : ℝ) := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hF hden
  exact hT.trans hdiv

/-! ### Profile and logarithmic limits -/

theorem tendsto_log_nat_atTop :
    Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_log_div_self :
    Tendsto (fun X : ℕ => Real.log X / X) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact (h0.comp tendsto_natCast_atTop_atTop).congr fun X => by
    rw [Function.comp_apply]

private theorem tendsto_log_sq_div_self :
    Tendsto (fun X : ℕ => Real.log X ^ 2 / X) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) := by
    simpa [one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 (by norm_num)
  exact (h0.comp tendsto_natCast_atTop_atTop).congr fun X => by
    rw [Function.comp_apply]

private theorem tendsto_log_two_mul_div_self :
    Tendsto (fun X : ℕ => Real.log (2 * (X : ℝ)) / X) atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => Real.log (2 * (X : ℝ)) / X) =ᶠ[atTop]
        fun X => Real.log 2 / X + Real.log X / X := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hx : (0 : ℝ) < X := Nat.cast_pos.mpr hX
    rw [Real.log_mul (by norm_num) hx.ne', add_div]
  have hsum : Tendsto (fun X : ℕ => Real.log 2 / X + Real.log X / X)
      atTop (nhds (0 + 0)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).add tendsto_log_div_self
  have hsum0 : Tendsto (fun X : ℕ => Real.log 2 / X + Real.log X / X)
      atTop (nhds 0) := by
    simpa using hsum
  exact hsum0.congr' hfun.symm

private theorem tendsto_log_mul_log_two_mul_div_self :
    Tendsto (fun X : ℕ => Real.log X * Real.log (2 * (X : ℝ)) / X)
      atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => Real.log X * Real.log (2 * (X : ℝ)) / X) =ᶠ[atTop]
        fun X => Real.log 2 * (Real.log X / X) + Real.log X ^ 2 / X := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hx : (0 : ℝ) < X := Nat.cast_pos.mpr hX
    have hlog := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'
    rw [hlog, mul_add, add_div]
    ring
  have hsum :
      Tendsto (fun X : ℕ =>
          Real.log 2 * (Real.log X / X) + Real.log X ^ 2 / X)
        atTop (nhds (Real.log 2 * 0 + 0)) :=
    (tendsto_log_div_self.const_mul (Real.log 2)).add tendsto_log_sq_div_self
  have hsum0 :
      Tendsto (fun X : ℕ =>
          Real.log 2 * (Real.log X / X) + Real.log X ^ 2 / X)
        atTop (nhds 0) := by
    simpa using hsum
  exact hsum0.congr' hfun.symm

private theorem stdProfileL_cast_le {ρ G : ℝ} (hG : 0 ≤ logρ ρ G) :
    (stdProfileL ρ G : ℝ) ≤ logρ ρ G + Real.sqrt (logρ ρ G) + 1 := by
  have ha : 0 ≤ logρ ρ G + Real.sqrt (logρ ρ G) :=
    add_nonneg hG (Real.sqrt_nonneg _)
  simpa [stdProfileL] using (Nat.ceil_lt_add_one (R := ℝ) ha).le

private theorem logρ_id_nonneg {ρ : ℝ} {X : ℕ} (hρ : 1 < ρ) (hX : 3 ≤ X) :
    0 ≤ logρ ρ (X : ℝ) := by
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  exact div_nonneg (Real.log_nonneg hx.le) (Real.log_pos hρ).le

private theorem logρ_log_nonneg {ρ : ℝ} {X : ℕ} (hρ : 1 < ρ) (hX : 3 ≤ X) :
    0 ≤ logρ ρ (Real.log X) :=
  div_nonneg (Real.log_nonneg (one_le_log_of_three_le hX)) (Real.log_pos hρ).le

private theorem tendsto_three_mul_atTop :
    Tendsto (fun X : ℕ => 3 * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left 3 h) fun n =>
      ⟨n, Nat.le_mul_of_pos_left n (by omega : 0 < 3)⟩

private theorem tendsto_two_mul_atTop :
    Tendsto (fun X : ℕ => 2 * X) atTop atTop :=
  tendsto_atTop_atTop_of_monotone
    (fun _ _ h => Nat.mul_le_mul_left 2 h) fun n =>
      ⟨n, Nat.le_mul_of_pos_left n (by omega : 0 < 2)⟩

private theorem eventually_stdProfileL_id_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      (stdProfileL ρ (X : ℝ) : ℝ) + 1 ≤
        (X : ℝ) / Real.log (2 * (X : ℝ)) := by
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  have hnum : Tendsto (fun X : ℕ =>
      (2 * Real.log X / Real.log ρ + 3) * Real.log (2 * (X : ℝ)) / X)
      atTop (nhds 0) := by
    have hfun :
        (fun X : ℕ =>
            (2 * Real.log X / Real.log ρ + 3) * Real.log (2 * (X : ℝ)) / X) =
          (fun X : ℕ =>
            (2 / Real.log ρ) * (Real.log X * Real.log (2 * (X : ℝ)) / X) +
              3 * (Real.log (2 * (X : ℝ)) / X)) := by
      funext X
      ring
    rw [hfun]
    have hsum :
        Tendsto (fun X : ℕ =>
            (2 / Real.log ρ) * (Real.log X * Real.log (2 * (X : ℝ)) / X) +
              3 * (Real.log (2 * (X : ℝ)) / X))
          atTop (nhds ((2 / Real.log ρ) * 0 + 3 * 0)) :=
      (tendsto_log_mul_log_two_mul_div_self.const_mul (2 / Real.log ρ)).add
        (tendsto_log_two_mul_div_self.const_mul (3 : ℝ))
    simpa using hsum
  have hsmall : ∀ᶠ X : ℕ in atTop,
      (2 * Real.log X / Real.log ρ + 3) * Real.log (2 * (X : ℝ)) / X < 1 :=
    hnum.eventually_lt_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 3] with X hlt hX
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have h2X : (1 : ℝ) < 2 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2) hx.le)
  have hlog2X : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h2X
  have hlogρ0 : 0 ≤ logρ ρ (X : ℝ) := logρ_id_nonneg hρ hX
  have hL := stdProfileL_cast_le hlogρ0
  have hL2 : (stdProfileL ρ (X : ℝ) : ℝ) ≤
      2 * logρ ρ (X : ℝ) + 2 := by
    have h1 :
        logρ ρ (X : ℝ) + Real.sqrt (logρ ρ (X : ℝ)) + 1 ≤
          2 * logρ ρ (X : ℝ) + 1 + 1 :=
      _root_.add_le_add (add_sqrt_le hlogρ0) (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (X : ℝ) + 1 + 1 = 2 * logρ ρ (X : ℝ) + 2 := by
      ring
    exact hL.trans (h1.trans_eq heq)
  have hbound : (stdProfileL ρ (X : ℝ) : ℝ) + 1 ≤
      2 * Real.log X / Real.log ρ + 3 := by
    have h1 : (stdProfileL ρ (X : ℝ) : ℝ) + 1 ≤
        2 * logρ ρ (X : ℝ) + 2 + 1 :=
      _root_.add_le_add hL2 (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (X : ℝ) + 2 + 1 =
        2 * Real.log X / Real.log ρ + 3 := by
      simp only [logρ, mul_div_assoc]
      ring
    exact h1.trans_eq heq
  have hmul : ((stdProfileL ρ (X : ℝ) : ℝ) + 1) * Real.log (2 * (X : ℝ)) / X ≤
      (2 * Real.log X / Real.log ρ + 3) * Real.log (2 * (X : ℝ)) / X :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbound hlog2X.le) hx0.le
  have hprod : ((stdProfileL ρ (X : ℝ) : ℝ) + 1) * Real.log (2 * (X : ℝ)) / X < 1 :=
    lt_of_le_of_lt hmul hlt
  have hmul' : ((stdProfileL ρ (X : ℝ) : ℝ) + 1) * Real.log (2 * (X : ℝ)) < X :=
    (div_lt_one hx0).mp hprod
  exact le_of_lt ((lt_div_iff₀ hlog2X).mpr hmul')

private theorem tendsto_log_three_mul_div_self :
    Tendsto (fun X : ℕ => Real.log (3 * (X : ℝ)) / X) atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => Real.log (3 * (X : ℝ)) / X) =ᶠ[atTop]
        fun X => Real.log 3 / X + Real.log X / X := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hx : (0 : ℝ) < X := Nat.cast_pos.mpr hX
    rw [Real.log_mul (by norm_num) hx.ne', add_div]
  have hsum : Tendsto (fun X : ℕ => Real.log 3 / X + Real.log X / X)
      atTop (nhds (0 + 0)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 3)).add tendsto_log_div_self
  have hsum0 : Tendsto (fun X : ℕ => Real.log 3 / X + Real.log X / X)
      atTop (nhds 0) := by
    simpa using hsum
  exact hsum0.congr' hfun.symm

private theorem tendsto_log_log_div_self :
    Tendsto (fun X : ℕ => Real.log (Real.log X) / X) atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => Real.log (Real.log X) / X) =ᶠ[atTop]
        fun X => (Real.log (Real.log X) / Real.log X) * (Real.log X / X) := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    have hlog : 0 < Real.log X :=
      Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
        (by exact_mod_cast hX))
    have hx0 : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hlog.ne', hx0]
  have hinner : Tendsto (fun X : ℕ => Real.log (Real.log X) / Real.log X)
      atTop (nhds 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      simpa [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
    exact (h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr
      fun X => by
        rw [Function.comp_apply, Function.comp_apply]
  have hmul : Tendsto (fun X : ℕ =>
      (Real.log (Real.log X) / Real.log X) * (Real.log X / X))
      atTop (nhds (0 * 0)) :=
    hinner.mul tendsto_log_div_self
  have hmul0 : Tendsto (fun X : ℕ =>
      (Real.log (Real.log X) / Real.log X) * (Real.log X / X))
      atTop (nhds 0) := by
    simpa using hmul
  exact hmul0.congr' hfun.symm

private theorem tendsto_log_log_mul_log_three_div_self :
    Tendsto (fun X : ℕ =>
        Real.log (Real.log X) * Real.log (3 * (X : ℝ)) / X)
      atTop (nhds 0) := by
  have hfun :
      (fun X : ℕ => Real.log (Real.log X) * Real.log (3 * (X : ℝ)) / X) =ᶠ[atTop]
        fun X =>
          Real.log (Real.log X) * (Real.log 3 / X) +
            Real.log (Real.log X) * (Real.log X / X) := by
    filter_upwards [eventually_ge_atTop 3] with X hX
    have hx : (0 : ℝ) < X :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
    have hlog := Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx.ne'
    rw [hlog, mul_add, add_div]
    ring
  have hB :
      Tendsto (fun X : ℕ => Real.log (Real.log X) * (Real.log X / X))
        atTop (nhds 0) := by
    have hfun2 :
        (fun X : ℕ => Real.log (Real.log X) * (Real.log X / X)) =ᶠ[atTop]
          fun X =>
            (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X) := by
      filter_upwards [eventually_ge_atTop 3] with X hX
      have hlog : Real.log X ≠ 0 :=
        (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
          (by exact_mod_cast hX))).ne'
      have hx0 : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hlog, hx0]
    have h1 : Tendsto (fun X : ℕ => Real.log (Real.log X) / Real.log X)
        atTop (nhds 0) := by
      have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
        simpa [pow_one, one_mul, add_zero] using
          Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
      exact (h0.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr
        fun X => by
          rw [Function.comp_apply, Function.comp_apply]
    have hmul : Tendsto (fun X : ℕ =>
        (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X))
        atTop (nhds (0 * 0)) :=
      h1.mul tendsto_log_sq_div_self
    have hmul0 : Tendsto (fun X : ℕ =>
        (Real.log (Real.log X) / Real.log X) * (Real.log X ^ 2 / X))
        atTop (nhds 0) := by
      simpa using hmul
    exact hmul0.congr' hfun2.symm
  have hA' : Tendsto (fun X : ℕ => Real.log (Real.log X) * (Real.log 3 / X))
      atTop (nhds 0) := by
    have hfunA :
        (fun X : ℕ => Real.log (Real.log X) * (Real.log 3 / X)) =
          (fun X : ℕ => Real.log 3 * (Real.log (Real.log X) / X)) := by
      funext X
      ring
    rw [hfunA]
    have hmul : Tendsto (fun X : ℕ => Real.log 3 * (Real.log (Real.log X) / X))
        atTop (nhds (Real.log 3 * 0)) :=
      tendsto_log_log_div_self.const_mul (Real.log 3)
    simpa using hmul
  have hsum :
      Tendsto (fun X : ℕ =>
          Real.log (Real.log X) * (Real.log 3 / X) +
            Real.log (Real.log X) * (Real.log X / X))
        atTop (nhds (0 + 0)) :=
    hA'.add hB
  have hsum0 :
      Tendsto (fun X : ℕ =>
          Real.log (Real.log X) * (Real.log 3 / X) +
            Real.log (Real.log X) * (Real.log X / X))
        atTop (nhds 0) := by
    simpa using hsum
  exact hsum0.congr' hfun.symm

private theorem eventually_stdProfileL_log_le {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
        (X : ℝ) / Real.log (3 * (X : ℝ)) := by
  have hnum : Tendsto (fun X : ℕ =>
      (2 * Real.log (Real.log X) / Real.log ρ + 3) *
        Real.log (3 * (X : ℝ)) / X) atTop (nhds 0) := by
    have hfun :
        (fun X : ℕ =>
            (2 * Real.log (Real.log X) / Real.log ρ + 3) *
              Real.log (3 * (X : ℝ)) / X) =
          (fun X : ℕ =>
            (2 / Real.log ρ) *
                (Real.log (Real.log X) * Real.log (3 * (X : ℝ)) / X) +
              3 * (Real.log (3 * (X : ℝ)) / X)) := by
      funext X
      ring
    rw [hfun]
    have hsum :
        Tendsto (fun X : ℕ =>
            (2 / Real.log ρ) *
                (Real.log (Real.log X) * Real.log (3 * (X : ℝ)) / X) +
              3 * (Real.log (3 * (X : ℝ)) / X))
          atTop (nhds ((2 / Real.log ρ) * 0 + 3 * 0)) :=
      (tendsto_log_log_mul_log_three_div_self.const_mul (2 / Real.log ρ)).add
        (tendsto_log_three_mul_div_self.const_mul (3 : ℝ))
    simpa using hsum
  have hsmall : ∀ᶠ X : ℕ in atTop,
      (2 * Real.log (Real.log X) / Real.log ρ + 3) *
          Real.log (3 * (X : ℝ)) / X < 1 :=
    hnum.eventually_lt_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 3] with X hlt hX
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have h3X : (1 : ℝ) < 3 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 3) hx.le)
  have hlog3X : 0 < Real.log (3 * (X : ℝ)) := Real.log_pos h3X
  have hlogρ0 : 0 ≤ logρ ρ (Real.log X) := logρ_log_nonneg hρ hX
  have hL := stdProfileL_cast_le hlogρ0
  have hL2 : (stdProfileL ρ (Real.log X) : ℝ) ≤
      2 * logρ ρ (Real.log X) + 2 := by
    have h1 :
        logρ ρ (Real.log X) + Real.sqrt (logρ ρ (Real.log X)) + 1 ≤
          2 * logρ ρ (Real.log X) + 1 + 1 :=
      _root_.add_le_add (add_sqrt_le hlogρ0) (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (Real.log X) + 1 + 1 =
        2 * logρ ρ (Real.log X) + 2 := by
      ring
    exact hL.trans (h1.trans_eq heq)
  have hbound : (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
      2 * Real.log (Real.log X) / Real.log ρ + 3 := by
    have h1 : (stdProfileL ρ (Real.log X) : ℝ) + 1 ≤
        2 * logρ ρ (Real.log X) + 2 + 1 :=
      _root_.add_le_add hL2 (le_rfl : (1 : ℝ) ≤ 1)
    have heq : 2 * logρ ρ (Real.log X) + 2 + 1 =
        2 * Real.log (Real.log X) / Real.log ρ + 3 := by
      simp only [logρ, mul_div_assoc]
      ring
    exact h1.trans_eq heq
  have hmul :
      ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log (3 * (X : ℝ)) / X ≤
        (2 * Real.log (Real.log X) / Real.log ρ + 3) *
          Real.log (3 * (X : ℝ)) / X :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbound hlog3X.le) hx0.le
  have hprod :
      ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log (3 * (X : ℝ)) / X < 1 :=
    lt_of_le_of_lt hmul hlt
  have hmul' : ((stdProfileL ρ (Real.log X) : ℝ) + 1) * Real.log (3 * (X : ℝ)) < X :=
    (div_lt_one hx0).mp hprod
  exact le_of_lt ((lt_div_iff₀ hlog3X).mpr hmul')

/-! ### Dyadic `GapTailT` at linear scale -/

/-- `O_ρ(1)` factor in the dyadic linear-scale tail bound. -/
noncomputable def gapTailLinearCoeff (ρ : ℝ) : ℝ :=
  2 * (2 * (Real.log 4 + 1) + 1) * posMassChebyshevCoeff ρ

theorem gapTailLinearCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) :
    0 ≤ gapTailLinearCoeff ρ := by
  unfold gapTailLinearCoeff
  have hC := posMassChebyshevCoeff_nonneg hρ
  have hlog : 0 ≤ Real.log 4 := Real.log_natCast_nonneg 4
  have hinner : 0 ≤ 2 * (Real.log 4 + 1) + 1 := by positivity
  exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hinner) hC

/-- Everything in `GapTailT nthPrime ρ (fun X => log X)` except the
`O(log X)` average, which is dyadically blocked. -/
theorem gapTailT_nthPrime_log_data {ρ : ℝ} (hρ : 1 < ρ) :
    1 < ρ ∧
      Tendsto (fun X : ℕ => Real.log X) atTop atTop ∧
      Summable (fun n : ℕ => (nthPrime n : ℝ) / ρ ^ n) ∧
      ∀ᶠ X : ℕ in atTop, 0 < (seqWindow nthPrime X).card :=
  ⟨hρ, tendsto_log_nat_atTop, nthPrime_div_pow_summable hρ, by
    filter_upwards [eventually_ge_atTop 1] with X hX
    exact card_seqWindow_nthPrime_pos hX⟩

/-- Honest dyadic substitute: `GapTailT` holds with `G(X) = X`, not
`G(X) = log X`. -/
theorem gapTailT_nthPrime_linear {ρ : ℝ} (hρ : 1 < ρ) :
    GapTailT nthPrime ρ (fun X => (X : ℝ)) := by
  refine ⟨hρ, tendsto_natCast_atTop_atTop, nthPrime_div_pow_summable hρ, ?_⟩
  refine ⟨gapTailLinearCoeff ρ, gapTailLinearCoeff_nonneg hρ, ?_⟩
  have hπ :=
    tendsto_two_mul_atTop.eventually
      (eventually_primeCounting_le_nat (by positivity : (0 : ℝ) < 1))
  have hL := eventually_stdProfileL_id_le hρ
  have hlogbig :
      ∀ᶠ X : ℕ in atTop,
        2 * (Real.log 4 + 1) + 1 ≤ Real.log (2 * (X : ℝ)) := by
    have h :=
      (Real.tendsto_log_atTop.comp
          (tendsto_natCast_atTop_atTop.comp tendsto_two_mul_atTop)).eventually_ge_atTop
        (2 * (Real.log 4 + 1) + 1)
    filter_upwards [h] with X hle
    have hle' : 2 * (Real.log 4 + 1) + 1 ≤ Real.log ((2 * X : ℕ) : ℝ) := by
      simpa [Function.comp_apply] using hle
    have hlogeq : Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 * (X : ℝ)) := by
      simp
    rwa [hlogeq] at hle'
  filter_upwards [hπ, hL, hlogbig, eventually_ge_atTop 3] with
    X hπ2 hLle hKlog hX
  have hm : 0 < (seqWindow nthPrime X).card :=
    card_seqWindow_nthPrime_pos (lt_of_lt_of_le (by omega : 0 < 3) hX)
  refine ⟨hm, ?_⟩
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have h2X : (1 : ℝ) < 2 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2) hx.le)
  have hlog2X : 0 < Real.log (2 * (X : ℝ)) := Real.log_pos h2X
  have hcast : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by simp
  have hπ2' : (Nat.primeCounting (2 * X) : ℝ) ≤
      (Real.log 4 + 1) * (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) := by
    have hlogeq : Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 * (X : ℝ)) := by simp
    simpa [hcast, hlogeq] using hπ2
  set L := stdProfileL ρ (X : ℝ)
  set N : ℕ := Nat.primeCounting (2 * X) + L
  have hN1 : ((N + 1 : ℕ) : ℝ) =
      (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 := by
    dsimp only [N]
    rw [Nat.cast_add_one (Nat.primeCounting (2 * X) + L), Nat.cast_add]
  have hK : (2 * (Real.log 4 + 1) + 1) * (X : ℝ) /
        Real.log (2 * (X : ℝ)) ≤ (X : ℝ) := by
    rw [div_le_iff₀ hlog2X, mul_comm (X : ℝ)]
    exact mul_le_mul_of_nonneg_right hKlog hx0.le
  have hNbd : ((N + 1 : ℕ) : ℝ) ≤
      (2 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (2 * (X : ℝ)) := by
    have hL1 : (L : ℝ) + 1 ≤ (X : ℝ) / Real.log (2 * (X : ℝ)) := hLle
    have hπbd : (Nat.primeCounting (2 * X) : ℝ) ≤
        2 * (Real.log 4 + 1) * (X : ℝ) / Real.log (2 * (X : ℝ)) := by
      have : (Real.log 4 + 1) * (2 * (X : ℝ)) / Real.log (2 * (X : ℝ)) =
          2 * (Real.log 4 + 1) * (X : ℝ) / Real.log (2 * (X : ℝ)) := by
        ring
      exact hπ2'.trans_eq this
    have hadd := _root_.add_le_add hπbd hL1
    have hsum :
        2 * (Real.log 4 + 1) * (X : ℝ) / Real.log (2 * (X : ℝ)) +
            (X : ℝ) / Real.log (2 * (X : ℝ)) =
          (2 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (2 * (X : ℝ)) := by
      ring
    have hassoc : (Nat.primeCounting (2 * X) : ℝ) + (L : ℝ) + 1 =
        (Nat.primeCounting (2 * X) : ℝ) + ((L : ℝ) + 1) := by
      ring
    rw [hN1, hassoc]
    exact hadd.trans_eq hsum
  have hN1X : ((N + 1 : ℕ) : ℝ) ≤ (X : ℝ) := hNbd.trans hK
  have hN2le : ((N + 2 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    have hN2 : ((N + 2 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + 1 :=
      Nat.cast_add_one (N + 1)
    have hmid : ((N + 1 : ℕ) : ℝ) + 1 ≤ (X : ℝ) + 1 :=
      _root_.add_le_add hN1X (le_rfl : (1 : ℝ) ≤ 1)
    have hX1 : (X : ℝ) + 1 ≤ 2 * (X : ℝ) := by
      linarith [hx]
    rw [hN2]
    exact hmid.trans hX1
  have hlogN : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
      Real.log (2 * (X : ℝ)) + 1 := by
    have hpos : (0 : ℝ) < (N + 2 : ℕ) := by
      exact_mod_cast (Nat.succ_pos (N + 1))
    exact _root_.add_le_add (Real.log_le_log hpos hN2le)
      (le_rfl : (1 : ℝ) ≤ 1)
  have hlogge1 : (1 : ℝ) ≤ Real.log (2 * (X : ℝ)) :=
    le_trans (one_le_log_of_three_le hX)
      (Real.log_le_log hx0 (le_mul_of_one_le_left hx0.le (by norm_num : (1 : ℝ) ≤ 2)))
  have hprod :
      ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        2 * (2 * (Real.log 4 + 1) + 1) * (X : ℝ) := by
    have h1 : ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        ((2 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (2 * (X : ℝ))) *
          (Real.log (2 * (X : ℝ)) + 1) :=
      mul_le_mul hNbd hlogN
        (add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
        (div_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤
            2 * (Real.log 4 + 1) + 1) hx0.le) hlog2X.le)
    have h2 :
        ((2 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (2 * (X : ℝ))) *
            (Real.log (2 * (X : ℝ)) + 1) =
          (2 * (Real.log 4 + 1) + 1) * (X : ℝ) *
            (1 + 1 / Real.log (2 * (X : ℝ))) := by
      have h0 : Real.log (2 * (X : ℝ)) ≠ 0 := hlog2X.ne'
      field_simp [h0]
    have h3 : 1 + 1 / Real.log (2 * (X : ℝ)) ≤ 2 := by
      have : 1 / Real.log (2 * (X : ℝ)) ≤ 1 :=
        (div_le_one hlog2X).mpr hlogge1
      linarith
    have h4 :
        (2 * (Real.log 4 + 1) + 1) * (X : ℝ) *
            (1 + 1 / Real.log (2 * (X : ℝ))) ≤
          2 * (2 * (Real.log 4 + 1) + 1) * (X : ℝ) := by
      have hnn : 0 ≤ (2 * (Real.log 4 + 1) + 1) * (X : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left h3 hnn
      have heq : (2 * (Real.log 4 + 1) + 1) * (X : ℝ) * 2 =
          2 * (2 * (Real.log 4 + 1) + 1) * (X : ℝ) := by ring
      exact hmul.trans_eq heq
    exact h1.trans (h2.trans_le h4)
  have hnum :
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        gapTailLinearCoeff ρ * (X : ℝ) := by
    have hassoc :
        posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
            (Real.log ((N + 2 : ℕ) : ℝ) + 1) =
          posMassChebyshevCoeff ρ *
            (((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1)) := by
      ring
    have hmul :=
      mul_le_mul_of_nonneg_left hprod (posMassChebyshevCoeff_nonneg hρ)
    have hRHS :
        posMassChebyshevCoeff ρ *
            (2 * (2 * (Real.log 4 + 1) + 1) * (X : ℝ)) =
          gapTailLinearCoeff ρ * (X : ℝ) := by
      unfold gapTailLinearCoeff
      ring
    exact hassoc.trans_le (hmul.trans_eq hRHS)
  have hcard1 : (1 : ℝ) ≤ (seqWindow nthPrime X).card := by
    exact_mod_cast (Nat.succ_le_of_lt hm)
  have hnn : 0 ≤
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
        (Real.log ((N + 2 : ℕ) : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (posMassChebyshevCoeff_nonneg hρ) (Nat.cast_nonneg _))
      (add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
  have hdiv := div_le_self hnn hcard1
  have hT' : windowAvgReal (seqWindow nthPrime X)
        (fun n => seqGapTail ρ nthPrime (n + L)) ≤
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) /
        ((seqWindow nthPrime X).card : ℝ) := by
    simpa [seqWindowMul_two, N] using
      (conditionT_seqWindowMul_nthPrime_chebyshev_log hρ 2 X L
        (by simpa [seqWindowMul_two] using hm))
  exact hT'.trans (hdiv.trans hnum)

/-! ### Triad Chebyshev density `(X, 3X]` -/

private theorem three_mul_log_two_sub_log_four :
    (3 : ℝ) * Real.log 2 - Real.log 4 = Real.log 2 := by
  rw [← two_mul_log_two_eq_log_four]
  ring

private theorem tendsto_log_three_mul_div_log :
    Tendsto (fun X : ℕ => Real.log (3 * (X : ℝ)) / Real.log X)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun X : ℕ => (Real.log X)⁻¹) atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop).congr fun X => by
      rw [Function.comp_apply]
  have hc0 : Tendsto (fun X : ℕ => Real.log 3 * (Real.log X)⁻¹)
      atTop (nhds (Real.log 3 * 0)) :=
    hinv.const_mul (Real.log 3)
  have hc : Tendsto (fun X : ℕ => Real.log 3 / Real.log X) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hc0
  have hadd : Tendsto (fun X : ℕ =>
      (1 : ℝ) + Real.log 3 / Real.log X) atTop (nhds (1 + 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).add hc
  have hadd1 : Tendsto (fun X : ℕ =>
      (1 : ℝ) + Real.log 3 / Real.log X) atTop (nhds 1) := by
    simpa using hadd
  apply hadd1.congr'
  filter_upwards [eventually_ge_atTop 3] with X hX
  have hx : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < 3) hX)
  have hlogpos : Real.log X ≠ 0 :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
      (by exact_mod_cast hX))).ne'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx.ne', add_div,
    div_self hlogpos, add_comm]

private theorem tendsto_nat_div_log :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) atTop atTop := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (nhds 0) :=
    tendsto_log_div_self
  have hpos : ∀ᶠ n : ℕ in atTop, Real.log n / (n : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hn)
    exact div_pos (Real.log_pos hn1) (lt_trans (by norm_num) hn1)
  have hwithin :
      Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hlog, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr' (Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply]
  try simp only [one_div]
  exact inv_div (Real.log (n : ℝ)) (n : ℝ)

private theorem seqWindowMul_ge_pi_sub {k X : ℕ} {ε : ℝ} (hk : 1 ≤ k)
    (hπle : (Nat.primeCounting X : ℝ) ≤
      (Real.log 4 + ε) * (X : ℝ) / Real.log X) :
    (((k * X : ℕ) : ℝ) * Real.log 2 -
          Real.log ((k * X + 1 : ℕ) : ℝ)) /
        Real.log (k * X : ℝ) -
      (Real.log 4 + ε) * (X : ℝ) / Real.log X ≤
      ((seqWindowMul nthPrime k X).card : ℝ) := by
  have hge : (((k * X : ℕ) : ℝ) * Real.log 2 -
        Real.log ((k * X + 1 : ℕ) : ℝ)) /
      Real.log (k * X : ℝ) ≤
        (Nat.primeCounting (k * X) : ℝ) := by
    simpa [Nat.cast_add_one (k * X)] using Chebyshev.pi_ge (k * X)
  exact (sub_le_sub hge hπle).trans_eq
    (card_seqWindowMul_nthPrime_cast hk).symm

private theorem chebyshev_window_algebra {k X : ℕ} {ε : ℝ}
    (hk0 : 0 < k) (hx0 : 0 < (X : ℝ))
    (hlogX : 0 < Real.log X) (hlogkX : 0 < Real.log ((k : ℝ) * X)) :
    (((k * X : ℕ) : ℝ) * Real.log 2 -
          Real.log ((k * X + 1 : ℕ) : ℝ)) /
        Real.log (k * X : ℝ) -
      (Real.log 4 + ε) * (X : ℝ) / Real.log X =
      ((k : ℝ) * Real.log 2 - Real.log 4 - ε) * (X : ℝ) /
          Real.log ((k : ℝ) * X) -
        (Real.log 4 + ε) * Real.log k * (X : ℝ) /
          (Real.log ((k : ℝ) * X) * Real.log X) -
        Real.log ((k * X + 1 : ℕ) : ℝ) / Real.log ((k : ℝ) * X) := by
  have hcast : ((k * X : ℕ) : ℝ) = (k : ℝ) * (X : ℝ) := by simp
  have hlogkXeq : Real.log ((k : ℝ) * X) = Real.log k + Real.log X :=
    Real.log_mul (Nat.cast_ne_zero.mpr (ne_of_gt hk0)) hx0.ne'
  have hlogpos : Real.log ((k : ℝ) * X) ≠ 0 := hlogkX.ne'
  have hlogX0 : Real.log X ≠ 0 := hlogX.ne'
  simp only [hcast]
  field_simp [hlogpos, hlogX0]
  rw [hlogkXeq]
  ring

private theorem log_succ_le_two_log {k X : ℕ}
    (hk : 3 ≤ k) (hXk : k + 1 ≤ X) :
    Real.log ((k * X + 1 : ℕ) : ℝ) ≤ 2 * Real.log X := by
  have hX2 : 2 ≤ X := le_trans (by omega : 2 ≤ k + 1) hXk
  have hx1 : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hX2)
  have hpos : (0 : ℝ) < ((k * X + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos (k * X))
  have hle : k * X + 1 ≤ X * X := by
    have h1 : k * X + 1 ≤ (k + 1) * X := by
      have : 1 ≤ X := le_trans (by omega : 1 ≤ 2) hX2
      calc
        k * X + 1 ≤ k * X + X := Nat.add_le_add_left this (k * X)
        _ = (k + 1) * X := by rw [← Nat.succ_mul]
    have h2 : (k + 1) * X ≤ X * X := Nat.mul_le_mul_right X hXk
    exact h1.trans h2
  have hleR : ((k * X + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ 2 := by
    have : ((k * X + 1 : ℕ) : ℝ) ≤ ((X * X : ℕ) : ℝ) := Nat.cast_le.mpr hle
    simpa [sq, Nat.cast_mul] using this
  have hlogle : Real.log ((k * X + 1 : ℕ) : ℝ) ≤ Real.log ((X : ℝ) ^ 2) :=
    Real.log_le_log hpos hleR
  have hpow : Real.log ((X : ℝ) ^ 2) = 2 * Real.log X := by
    rw [Real.log_pow (X : ℝ) 2]
    norm_cast
  exact hlogle.trans_eq hpow

/-- For each fixed `k ≥ 3` and each `ε` with
`ε < k log 2 - log 4`, eventually
`π(kX) - π(X) ≥ ((k log 2 - log 4 - ε) / 2) · X / log(kX)`. -/
private theorem eventually_seqWindowMul_ge {k : ℕ} {ε : ℝ}
    (hk : 3 ≤ k) (hε : 0 < ε)
    (hc : ε < (k : ℝ) * Real.log 2 - Real.log 4) :
    ∀ᶠ X : ℕ in atTop,
      ((k : ℝ) * Real.log 2 - Real.log 4 - ε) / 2 *
          (X : ℝ) / Real.log ((k : ℝ) * X) ≤
        ((seqWindowMul nthPrime k X).card : ℝ) := by
  set c : ℝ := (k : ℝ) * Real.log 2 - Real.log 4 - ε
  have hcpos : 0 < c := sub_pos.mpr hc
  have hk1 : 1 ≤ k := le_trans (by omega : 1 ≤ 3) hk
  have hk0 : 0 < k := lt_of_lt_of_le (by omega : 0 < 3) hk
  have hkR : (1 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hk)
  have hlogk : 0 < Real.log k := Real.log_pos hkR
  have hC : 0 < Real.log 4 + ε :=
    add_pos (by
      rw [← two_mul_log_two_eq_log_four]
      exact mul_pos (by norm_num) log_two_pos) hε
  have hπX := eventually_primeCounting_le_nat hε
  have hlogXbig :
      ∀ᶠ X : ℕ in atTop,
        (Real.log 4 + ε) * Real.log k / Real.log X ≤ c / 4 := by
    have hden :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (4 * (Real.log 4 + ε) * Real.log k / c)
    filter_upwards [hden, eventually_ge_atTop 3] with X hX hn
    have hx1 : (1 : ℝ) < X := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hn)
    have hlogX : 0 < Real.log X := Real.log_pos hx1
    have hnum : 0 ≤ (Real.log 4 + ε) * Real.log k :=
      mul_nonneg hC.le hlogk.le
    have hcmp :
        (Real.log 4 + ε) * Real.log k / Real.log X ≤
          (Real.log 4 + ε) * Real.log k /
            (4 * (Real.log 4 + ε) * Real.log k / c) := by
      have hc' : 0 < 4 * (Real.log 4 + ε) * Real.log k / c :=
        div_pos (mul_pos (mul_pos (by norm_num) hC) hlogk) hcpos
      exact div_le_div_of_nonneg_left hnum hc' hX
    have hsimp :
        (Real.log 4 + ε) * Real.log k /
            (4 * (Real.log 4 + ε) * Real.log k / c) =
          c / 4 := by
      have hne : (Real.log 4 + ε) * Real.log k ≠ 0 :=
        mul_ne_zero hC.ne' hlogk.ne'
      field_simp [hne, hcpos.ne']
    exact hcmp.trans_eq hsimp
  have hXlog :
      ∀ᶠ X : ℕ in atTop, 8 / c ≤ (X : ℝ) / Real.log X :=
    tendsto_nat_div_log.eventually_ge_atTop (8 / c)
  filter_upwards [hπX, hlogXbig, hXlog, eventually_ge_atTop (k + 1)] with
    X hπle hlogsmall hdiv hXk
  have hX2 : 2 ≤ X := le_trans (by omega : 2 ≤ k + 1) hXk
  have hx1 : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hX2)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx1
  have hlogX : 0 < Real.log X := Real.log_pos hx1
  have hXpos : 0 < X := lt_of_lt_of_le (by omega : 0 < 2) hX2
  have hkX2 : 2 ≤ k * X :=
    le_trans (by omega : 2 ≤ 3) (Nat.mul_le_mul hk (Nat.succ_le_of_lt hXpos))
  have hkXR : (1 : ℝ) < (k * X : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hkX2)
  have hcast : ((k * X : ℕ) : ℝ) = (k : ℝ) * (X : ℝ) := by simp
  have hlogkX : 0 < Real.log ((k : ℝ) * X) := by
    simpa [hcast] using Real.log_pos hkXR
  have hcmp := seqWindowMul_ge_pi_sub (k := k) (X := X) (ε := ε) hk1 hπle
  have halg :=
    chebyshev_window_algebra (k := k) (X := X) (ε := ε) hk0 hx0 hlogX hlogkX
  rw [halg] at hcmp
  have herr1 :
      (Real.log 4 + ε) * Real.log k * (X : ℝ) /
          (Real.log ((k : ℝ) * X) * Real.log X) ≤
        (c / 4) * (X : ℝ) / Real.log ((k : ℝ) * X) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hlogsmall
        (div_nonneg (Nat.cast_nonneg X) hlogkX.le)
    have hL :
        (Real.log 4 + ε) * Real.log k / Real.log X *
            ((X : ℝ) / Real.log ((k : ℝ) * X)) =
          (Real.log 4 + ε) * Real.log k * (X : ℝ) /
            (Real.log ((k : ℝ) * X) * Real.log X) := by
      have hlogpos : Real.log ((k : ℝ) * X) ≠ 0 := hlogkX.ne'
      have hlogX0 : Real.log X ≠ 0 := hlogX.ne'
      field_simp [hlogpos, hlogX0]
    have hR :
        (c / 4) * ((X : ℝ) / Real.log ((k : ℝ) * X)) =
          (c / 4) * (X : ℝ) / Real.log ((k : ℝ) * X) := by
      ring
    rwa [hL, hR] at hmul
  have herr2 :
      Real.log ((k * X + 1 : ℕ) : ℝ) / Real.log ((k : ℝ) * X) ≤
        (c / 4) * (X : ℝ) / Real.log ((k : ℝ) * X) := by
    have hlogsucc := log_succ_le_two_log hk hXk
    have h8 : 8 * Real.log X ≤ c * (X : ℝ) := by
      rw [div_le_div_iff₀ hcpos hlogX] at hdiv
      linarith
    have htwo : 2 * Real.log X ≤ (c / 4) * (X : ℝ) := by linarith [h8]
    have hnum : Real.log ((k * X + 1 : ℕ) : ℝ) ≤ (c / 4) * (X : ℝ) :=
      hlogsucc.trans htwo
    exact div_le_div_of_nonneg_right hnum hlogkX.le
  have htarget :
      c / 2 * (X : ℝ) / Real.log ((k : ℝ) * X) ≤
        c * (X : ℝ) / Real.log ((k : ℝ) * X) -
          (Real.log 4 + ε) * Real.log k * (X : ℝ) /
            (Real.log ((k : ℝ) * X) * Real.log X) -
          Real.log ((k * X + 1 : ℕ) : ℝ) / Real.log ((k : ℝ) * X) := by
    set d : ℝ := Real.log ((k : ℝ) * X)
    set a : ℝ := c / 2 * (X : ℝ) / d
    set A : ℝ := c * (X : ℝ) / d
    set e1 : ℝ :=
      (Real.log 4 + ε) * Real.log k * (X : ℝ) / (d * Real.log X)
    set e2 : ℝ := Real.log ((k * X + 1 : ℕ) : ℝ) / d
    set q : ℝ := (c / 4) * (X : ℝ) / d
    have hsum : q + q = a := by
      change
        (c / 4) * (X : ℝ) / Real.log ((k : ℝ) * X) +
            (c / 4) * (X : ℝ) / Real.log ((k : ℝ) * X) =
          c / 2 * (X : ℝ) / Real.log ((k : ℝ) * X)
      ring
    have hA : A = a + a := by
      change
        c * (X : ℝ) / Real.log ((k : ℝ) * X) =
          c / 2 * (X : ℝ) / Real.log ((k : ℝ) * X) +
            c / 2 * (X : ℝ) / Real.log ((k : ℝ) * X)
      ring
    have hup : e1 + e2 ≤ q + q := _root_.add_le_add herr1 herr2
    have hup' : e1 + e2 ≤ a := hup.trans_eq hsum
    have hcomb : a + (e1 + e2) ≤ a + a :=
      _root_.add_le_add_right hup' a
    have hcomb' : a + (e1 + e2) ≤ A := by
      rw [hA]
      exact hcomb
    rw [le_sub_iff_add_le, le_sub_iff_add_le]
    simpa [add_assoc, add_left_comm, add_comm] using hcomb'
  exact htarget.trans hcmp

/-- Best Chebyshev-scale dilated window: eventually
`π(3X) - π(X) ≥ (log 2 / 4) · X / log(3X)`. -/
theorem eventually_seqWindowMul_three_ge :
    ∀ᶠ X : ℕ in atTop,
      Real.log 2 / 4 * (X : ℝ) / Real.log (3 * (X : ℝ)) ≤
        ((seqWindowMul nthPrime 3 X).card : ℝ) := by
  have hε : 0 < Real.log 2 / 2 := div_pos log_two_pos (by norm_num)
  have hc : Real.log 2 / 2 < (3 : ℝ) * Real.log 2 - Real.log 4 := by
    rw [three_mul_log_two_sub_log_four]
    linarith [log_two_pos]
  have h := eventually_seqWindowMul_ge (k := 3) (ε := Real.log 2 / 2)
    (by omega) hε hc
  have hC :
      ((3 : ℝ) * Real.log 2 - Real.log 4 - Real.log 2 / 2) / 2 =
        Real.log 2 / 4 := by
    rw [three_mul_log_two_sub_log_four]
    ring
  filter_upwards [h] with X hX
  have hlog : Real.log ((3 : ℝ) * X) = Real.log (3 * (X : ℝ)) := by simp
  simpa [hC, hlog] using hX

/-! ### Triad tail average `O_ρ(log X)` -/

/-- `O_ρ(1)` factor in the triad logarithmic tail bound. -/
noncomputable def gapTailTriadLogCoeff (ρ : ℝ) : ℝ :=
  posMassChebyshevCoeff ρ * 16 * (3 * (Real.log 4 + 1) + 1) / Real.log 2

theorem gapTailTriadLogCoeff_nonneg {ρ : ℝ} (hρ : 1 < ρ) :
    0 ≤ gapTailTriadLogCoeff ρ := by
  unfold gapTailTriadLogCoeff
  have hC := posMassChebyshevCoeff_nonneg hρ
  have hlog4 : 0 ≤ Real.log 4 := Real.log_natCast_nonneg 4
  have hinter : 0 ≤ 3 * (Real.log 4 + 1) + 1 := by positivity
  have hnum : 0 ≤
      posMassChebyshevCoeff ρ * 16 * (3 * (Real.log 4 + 1) + 1) :=
    mul_nonneg (mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 16)) hinter
  exact div_nonneg hnum log_two_pos.le

/-- Strongest Chebyshev-scale substitute for paper T: on the triad
window `(X, 3X]`, the gap-tail average is `O_ρ(log X)`. This is not
`GapTailT` (that proposition is locked to dyadic `seqWindow`). -/
theorem eventually_gapTail_avg_triad_le_log {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ X : ℕ in atTop,
      0 < (seqWindowMul nthPrime 3 X).card ∧
        windowAvgReal (seqWindowMul nthPrime 3 X)
            (fun n => seqGapTail ρ nthPrime
              (n + stdProfileL ρ (Real.log X))) ≤
          gapTailTriadLogCoeff ρ * Real.log X := by
  have hπ :=
    tendsto_three_mul_atTop.eventually
      (eventually_primeCounting_le_nat (by positivity : (0 : ℝ) < 1))
  have hL := eventually_stdProfileL_log_le hρ
  have hden := eventually_seqWindowMul_three_ge
  have hlogratio :
      ∀ᶠ X : ℕ in atTop,
        Real.log (3 * (X : ℝ)) ≤ 2 * Real.log X := by
    filter_upwards [tendsto_log_three_mul_div_log.eventually_lt_const
        (by norm_num : (1 : ℝ) < 2), eventually_ge_atTop 3] with X hle hX
    have hlog : 0 < Real.log X :=
      Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
        (by exact_mod_cast hX))
    exact le_of_lt ((div_lt_iff₀ hlog).mp hle)
  have hlogbig3 :
      ∀ᶠ X : ℕ in atTop,
        3 * (Real.log 4 + 1) + 1 ≤ 3 * Real.log (3 * (X : ℝ)) := by
    have h :=
      (Real.tendsto_log_atTop.comp
          (tendsto_natCast_atTop_atTop.comp tendsto_three_mul_atTop)).eventually_ge_atTop
        ((3 * (Real.log 4 + 1) + 1) / 3)
    filter_upwards [h] with X hX
    have h3 : (0 : ℝ) ≤ 3 := by norm_num
    have hmul := mul_le_mul_of_nonneg_left hX h3
    have hrew : 3 * ((3 * (Real.log 4 + 1) + 1) / 3) =
        3 * (Real.log 4 + 1) + 1 := by
      have : (3 : ℝ) ≠ 0 := by norm_num
      field_simp [this]
    simp only [Function.comp_apply] at hmul
    have hlog : Real.log ((3 * X : ℕ) : ℝ) = Real.log (3 * (X : ℝ)) := by
      simp
    rwa [hrew, hlog] at hmul
  filter_upwards [hπ, hL, hden, hlogratio, hlogbig3, eventually_ge_atTop 3] with
    X hπ3 hLle hdenX hlogle hKlog hX
  have hm : 0 < (seqWindowMul nthPrime 3 X).card :=
    card_seqWindowMul_nthPrime_pos (by omega) (lt_of_lt_of_le (by omega : 0 < 3) hX)
  refine ⟨hm, ?_⟩
  have hx : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hX)
  have hx0 : (0 : ℝ) < X := lt_trans (by norm_num) hx
  have h3XR : (1 : ℝ) < 3 * (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3)
      (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 3) hx.le)
  have hlog3X : 0 < Real.log (3 * (X : ℝ)) := Real.log_pos h3XR
  have hlogXpos : 0 < Real.log X := Real.log_pos hx
  have hcast : ((3 * X : ℕ) : ℝ) = 3 * (X : ℝ) := by simp
  have hπ3' : (Nat.primeCounting (3 * X) : ℝ) ≤
      (Real.log 4 + 1) * (3 * (X : ℝ)) / Real.log (3 * (X : ℝ)) := by
    have hlogeq : Real.log ((3 * X : ℕ) : ℝ) = Real.log (3 * (X : ℝ)) := by simp
    simpa [hcast, hlogeq] using hπ3
  set L := stdProfileL ρ (Real.log X)
  have hT := conditionT_seqWindowMul_nthPrime_chebyshev_log hρ 3 X L hm
  set N : ℕ := Nat.primeCounting (3 * X) + L
  have hN1 : ((N + 1 : ℕ) : ℝ) =
      (Nat.primeCounting (3 * X) : ℝ) + (L : ℝ) + 1 := by
    dsimp only [N]
    rw [Nat.cast_add_one (Nat.primeCounting (3 * X) + L), Nat.cast_add]
  have hK : (3 * (Real.log 4 + 1) + 1) * (X : ℝ) /
        Real.log (3 * (X : ℝ)) ≤ 3 * (X : ℝ) := by
    rw [div_le_iff₀ hlog3X]
    have hmul := mul_le_mul_of_nonneg_right hKlog hx0.le
    have heq : 3 * Real.log (3 * (X : ℝ)) * (X : ℝ) =
        3 * (X : ℝ) * Real.log (3 * (X : ℝ)) := by
      ring
    exact hmul.trans_eq heq
  have hNbd : ((N + 1 : ℕ) : ℝ) ≤
      (3 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) := by
    have hL1 : (L : ℝ) + 1 ≤ (X : ℝ) / Real.log (3 * (X : ℝ)) := hLle
    have hπbd : (Nat.primeCounting (3 * X) : ℝ) ≤
        3 * (Real.log 4 + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) := by
      have : (Real.log 4 + 1) * (3 * (X : ℝ)) / Real.log (3 * (X : ℝ)) =
          3 * (Real.log 4 + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) := by
        ring
      exact hπ3'.trans_eq this
    have hadd := _root_.add_le_add hπbd hL1
    have hsum :
        3 * (Real.log 4 + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) +
            (X : ℝ) / Real.log (3 * (X : ℝ)) =
          (3 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) := by
      ring
    have hassoc : (Nat.primeCounting (3 * X) : ℝ) + (L : ℝ) + 1 =
        (Nat.primeCounting (3 * X) : ℝ) + ((L : ℝ) + 1) := by
      ring
    rw [hN1, hassoc]
    exact hadd.trans_eq hsum
  have hN2le : ((N + 2 : ℕ) : ℝ) ≤ 4 * (X : ℝ) := by
    have hN2 : ((N + 2 : ℕ) : ℝ) = ((N + 1 : ℕ) : ℝ) + 1 :=
      Nat.cast_add_one (N + 1)
    have hK1 : ((N + 1 : ℕ) : ℝ) + 1 ≤
        (3 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) + 1 :=
      _root_.add_le_add hNbd (le_rfl : (1 : ℝ) ≤ 1)
    have hmid : (3 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (3 * (X : ℝ)) + 1 ≤
        3 * (X : ℝ) + 1 :=
      _root_.add_le_add hK (le_rfl : (1 : ℝ) ≤ 1)
    have h4 : 3 * (X : ℝ) + 1 ≤ 4 * (X : ℝ) := by
      linarith [hx]
    rw [hN2]
    exact hK1.trans (hmid.trans h4)
  have hlogN : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
      2 * Real.log (3 * (X : ℝ)) := by
    have hpos : (0 : ℝ) < (N + 2 : ℕ) := by
      exact_mod_cast (Nat.succ_pos (N + 1))
    have h1 : Real.log ((N + 2 : ℕ) : ℝ) ≤ Real.log (4 * (X : ℝ)) :=
      Real.log_le_log hpos hN2le
    have hlog4X : Real.log (4 * (X : ℝ)) = Real.log 4 + Real.log X :=
      Real.log_mul (by norm_num) hx0.ne'
    have hlog4 : Real.log 4 ≤ 2 * Real.log 3 := by
      have hle : (4 : ℝ) ≤ (3 : ℝ) ^ 2 := by norm_num
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hle
      have hpow : Real.log ((3 : ℝ) ^ 2) = 2 * Real.log 3 := by
        rw [Real.log_pow (3 : ℝ) 2]
        norm_cast
      exact this.trans_eq hpow
    have hlogX1 : (1 : ℝ) ≤ Real.log X := one_le_log_of_three_le hX
    have hsum : Real.log 4 + Real.log X + 1 ≤
        2 * Real.log 3 + 2 * Real.log X := by
      have hleft : Real.log 4 + 1 ≤ 2 * Real.log 3 + Real.log X :=
        _root_.add_le_add hlog4 hlogX1
      have heq : Real.log 4 + Real.log X + 1 =
          Real.log 4 + 1 + Real.log X := by
        ring
      have hright : 2 * Real.log 3 + Real.log X + Real.log X =
          2 * Real.log 3 + 2 * Real.log X := by
        ring
      have hmid := _root_.add_le_add hleft (le_rfl : Real.log X ≤ Real.log X)
      exact (le_of_eq heq).trans (hmid.trans_eq hright)
    have h3Xeq : 2 * Real.log (3 * (X : ℝ)) =
        2 * Real.log 3 + 2 * Real.log X := by
      have := Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne'
      rw [this]
      ring
    have hcomb : Real.log ((N + 2 : ℕ) : ℝ) + 1 ≤
        Real.log 4 + Real.log X + 1 :=
      _root_.add_le_add (h1.trans_eq hlog4X) (le_rfl : (1 : ℝ) ≤ 1)
    exact hcomb.trans (hsum.trans_eq h3Xeq.symm)
  have hprod :
      ((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) := by
    have h1 := mul_le_mul hNbd hlogN
      (add_nonneg (Real.log_natCast_nonneg _) (by norm_num))
      (div_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤
          3 * (Real.log 4 + 1) + 1) hx0.le) hlog3X.le)
    have h2 :
        ((3 * (Real.log 4 + 1) + 1) * (X : ℝ) / Real.log (3 * (X : ℝ))) *
            (2 * Real.log (3 * (X : ℝ))) =
          2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) := by
      have h0 : Real.log (3 * (X : ℝ)) ≠ 0 := hlog3X.ne'
      field_simp [h0]
    exact h1.trans (le_of_eq h2)
  have hFnum :
      posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
          (Real.log ((N + 2 : ℕ) : ℝ) + 1) ≤
        posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) := by
    have hassoc :
        posMassChebyshevCoeff ρ * ((N + 1 : ℕ) : ℝ) *
            (Real.log ((N + 2 : ℕ) : ℝ) + 1) =
          posMassChebyshevCoeff ρ *
            (((N + 1 : ℕ) : ℝ) * (Real.log ((N + 2 : ℕ) : ℝ) + 1)) := by
      ring
    have hmul :=
      mul_le_mul_of_nonneg_left hprod (posMassChebyshevCoeff_nonneg hρ)
    have hRHS :
        posMassChebyshevCoeff ρ * (2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ)) =
          posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) *
            (X : ℝ) := by
      ring
    exact hassoc.trans_le (hmul.trans_eq hRHS)
  have hmR : (0 : ℝ) < (seqWindowMul nthPrime 3 X).card := by
    exact_mod_cast hm
  have hdenpos : 0 < Real.log 2 / 4 * (X : ℝ) / Real.log (3 * (X : ℝ)) :=
    div_pos (mul_pos (div_pos log_two_pos (by norm_num)) hx0) hlog3X
  have havg :
      windowAvgReal (seqWindowMul nthPrime 3 X)
          (fun n => seqGapTail ρ nthPrime (n + L)) ≤
        posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) /
          ((seqWindowMul nthPrime 3 X).card : ℝ) := by
    have hden' : 0 ≤ ((seqWindowMul nthPrime 3 X).card : ℝ) := Nat.cast_nonneg _
    exact hT.trans (div_le_div_of_nonneg_right hFnum hden')
  have hinv : 1 / ((seqWindowMul nthPrime 3 X).card : ℝ) ≤
      1 / (Real.log 2 / 4 * (X : ℝ) / Real.log (3 * (X : ℝ))) :=
    one_div_le_one_div_of_le hdenpos hdenX
  have hquot :
      posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) /
          ((seqWindowMul nthPrime 3 X).card : ℝ) ≤
        posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) *
          (Real.log (3 * (X : ℝ)) / (Real.log 2 / 4 * (X : ℝ))) := by
    have hnn : 0 ≤
        posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (posMassChebyshevCoeff_nonneg hρ)
          (by norm_num : (0 : ℝ) ≤ 2))
        (by positivity : (0 : ℝ) ≤ 3 * (Real.log 4 + 1) + 1))
        hx0.le
    have : posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) /
          ((seqWindowMul nthPrime 3 X).card : ℝ) =
        (posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ)) *
          (1 / ((seqWindowMul nthPrime 3 X).card : ℝ)) := by
      field_simp [hmR.ne']
    rw [this]
    have hinv' :
        1 / (Real.log 2 / 4 * (X : ℝ) / Real.log (3 * (X : ℝ))) =
          Real.log (3 * (X : ℝ)) / (Real.log 2 / 4 * (X : ℝ)) := by
      have ha : Real.log 2 / 4 * (X : ℝ) ≠ 0 :=
        (mul_pos (div_pos log_two_pos (by norm_num)) hx0).ne'
      field_simp [ha, hlog3X.ne']
    rw [← hinv']
    exact mul_le_mul_of_nonneg_left hinv hnn
  have hsimp :
      posMassChebyshevCoeff ρ * 2 * (3 * (Real.log 4 + 1) + 1) * (X : ℝ) *
          (Real.log (3 * (X : ℝ)) / (Real.log 2 / 4 * (X : ℝ))) =
        posMassChebyshevCoeff ρ * 8 * (3 * (Real.log 4 + 1) + 1) /
            Real.log 2 * Real.log (3 * (X : ℝ)) := by
    have hx0' : (X : ℝ) ≠ 0 := hx0.ne'
    have h2 : Real.log 2 ≠ 0 := log_two_pos.ne'
    field_simp [hx0', h2]
    ring
  have hfinal :
      posMassChebyshevCoeff ρ * 8 * (3 * (Real.log 4 + 1) + 1) /
            Real.log 2 * Real.log (3 * (X : ℝ)) ≤
        gapTailTriadLogCoeff ρ * Real.log X := by
    have hnnC : 0 ≤
        posMassChebyshevCoeff ρ * 8 * (3 * (Real.log 4 + 1) + 1) / Real.log 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (posMassChebyshevCoeff_nonneg hρ)
          (by norm_num : (0 : ℝ) ≤ 8))
        (by positivity : (0 : ℝ) ≤ 3 * (Real.log 4 + 1) + 1))
        log_two_pos.le
    have hmul := mul_le_mul_of_nonneg_left hlogle hnnC
    have heq : posMassChebyshevCoeff ρ * 8 * (3 * (Real.log 4 + 1) + 1) /
            Real.log 2 * (2 * Real.log X) =
        gapTailTriadLogCoeff ρ * Real.log X := by
      unfold gapTailTriadLogCoeff
      ring
    exact hmul.trans_eq heq
  exact havg.trans (hquot.trans (hsimp.trans_le hfinal))

/-! ### Index D: identification and Chebyshev sandwich, not PNT -/

theorem indexPassageD_nthPrime_iff :
    IndexPassageD nthPrime ↔ IndexPassage nthPrime := by
  unfold IndexPassageD IndexPassage
  have hfun :
      (fun M : ℕ =>
          ((seqCount nthPrime (2 * nthPrime M) : ℝ) - 2 * (M : ℝ)) / (M : ℝ)) =
        fun M =>
          ((Nat.primeCounting (2 * nthPrime M) : ℝ) - 2 * (M : ℝ)) / (M : ℝ) := by
    funext M
    rw [seqCount_nthPrime]
  rw [hfun]

theorem indexPassageD_nthPrime_iff_tendsto_two :
    IndexPassageD nthPrime ↔
      Tendsto (fun M : ℕ =>
        (seqCount nthPrime (2 * nthPrime M) : ℝ) / M) atTop (nhds 2) := by
  rw [indexPassageD_nthPrime_iff]
  have h := indexPassage_iff_tendsto_two nthPrime
  have hfun :
      (fun M : ℕ => (Nat.primeCounting (2 * nthPrime M) : ℝ) / M) =
        fun M => (seqCount nthPrime (2 * nthPrime M) : ℝ) / M := by
    funext M
    rw [seqCount_nthPrime]
  rwa [hfun] at h

/-- Chebyshev form of D: `1-ε ≤ π(2 p_M)/(M+1) ≤ 4+ε`. This is not
`IndexPassageD nthPrime` (`π(2 p_M) = 2M + o(M)`). -/
theorem chebyshev_indexPassageD {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      1 - ε ≤
          (seqCount nthPrime (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ∧
        (seqCount nthPrime (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) ≤
          4 + ε := by
  simpa [seqCount_nthPrime] using chebyshev_index_passage hε

/-- Window-size consequence of the Chebyshev sandwich: eventually
`|I_{p_M}| / (M+1) ≤ 3+ε`. Paper D wants this ratio `→ 1`. -/
theorem chebyshev_seqWindow_card_div {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      ((seqWindow nthPrime (nthPrime M)).card : ℝ) / ((M : ℝ) + 1) ≤
        3 + ε := by
  filter_upwards [chebyshev_indexPassageD hε, eventually_ge_atTop 1] with M hM hM1
  have hcard := seqWindow_nthPrime_at_self M
  have hK : M + 1 ≤ Nat.primeCounting (2 * nthPrime M) := by
    have := le_seqCount_two nthPrime_strictMono M
    rwa [seqCount_nthPrime] at this
  have hcast :
      ((seqWindow nthPrime (nthPrime M)).card : ℝ) =
        (Nat.primeCounting (2 * nthPrime M) : ℝ) - ((M : ℝ) + 1) := by
    rw [hcard, Nat.cast_sub hK, Nat.cast_add_one M]
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hrew :
      ((seqWindow nthPrime (nthPrime M)).card : ℝ) / ((M : ℝ) + 1) =
        (seqCount nthPrime (2 * nthPrime M) : ℝ) / ((M : ℝ) + 1) - 1 := by
    rw [hcast, seqCount_nthPrime]
    have hne : (M : ℝ) + 1 ≠ 0 := hMpos.ne'
    field_simp [hne]
  rw [hrew]
  linarith [hM.2]

end PrimeGapNormality.Prime
