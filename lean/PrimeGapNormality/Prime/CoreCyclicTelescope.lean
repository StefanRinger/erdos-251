import PrimeGapNormality.Prime.CoreCyclicNormalForm
import PrimeGapNormality.Prime.CoreCyclicCanonical
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.FieldSimp

/-!
The exact finite boundary formula from the frozen paper, equation
`localboundary`, evaluated on arbitrary real gap sequences. Neither growth
nor arithmetic distribution assumptions are needed for this finite identity.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- Cyclic labels along a gap sequence, with specified label at index zero. -/
def phaseAt {k : ℕ} (hk : 0 < k) (r : Fin k) (n : ℕ) : Fin k :=
  (cyclicSucc hk)^[n] r

@[simp] theorem phaseAt_succ {k : ℕ} (hk : 0 < k) (r : Fin k) (n : ℕ) :
    phaseAt hk r (n + 1) = cyclicSucc hk (phaseAt hk r n) :=
  Function.iterate_succ_apply' _ _ _

/-- Evaluate a periodic local polynomial at the actual gap window at `n`. -/
def localValue {k : ℕ} (hk : 0 < k) (r : Fin k) (g : ℕ → ℝ)
    (F : PeriodicLocal k) (n : ℕ) : ℝ :=
  eval₂ (algebraMap ℚ ℝ) (fun j ↦ g (n + j)) (F (phaseAt hk r n))

@[simp] theorem localValue_add {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F H : PeriodicLocal k) (n : ℕ) :
    localValue hk r g (F + H) n = localValue hk r g F n + localValue hk r g H n := by
  simp [localValue]

@[simp] theorem localValue_sub {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F H : PeriodicLocal k) (n : ℕ) :
    localValue hk r g (F - H) n = localValue hk r g F n - localValue hk r g H n := by
  simp [localValue]

/-- The polynomial shift advances both the cyclic label and the gap window. -/
theorem localValue_shift {k : ℕ} (hk : 0 < k) (r : Fin k) (g : ℕ → ℝ)
    (H : PeriodicLocal k) (n : ℕ) :
    localValue hk r g (shift hk H) n = localValue hk r g H (n + 1) := by
  simp only [localValue, shift_apply, eval₂_rename, phaseAt_succ]
  congr 1
  funext j
  simp [Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The exact recurrence induced by a local telescope. -/
theorem localValue_telescope (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (H : PeriodicLocal k) (n : ℕ) :
    localValue hk r g (cyclicTelescope B hk H) n =
      (B : ℝ) * localValue hk r g H n - localValue hk r g H (n + 1) := by
  rw [telescope_eq, localValue_sub, localValue_shift]
  congr 1
  simp [localValue, smul_eq_C_mul]

/-- Finite weighted telescoping with the terminal remainder retained. -/
theorem finite_weighted_boundary {b : ℝ} (hb : b ≠ 0) (f : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (b * f i - f (i + 1)) / b ^ (i + 1)) =
      f 0 - f N / b ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp [hb]
    <;> ring

/-- Truncated local series starting at index `a`; the first denominator is `B`. -/
def finiteSeries (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) (g : ℕ → ℝ)
    (F : PeriodicLocal k) (a N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, localValue hk r g F (a + i) / (B : ℝ) ^ (i + 1)

theorem finiteSeries_add (B : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (g : ℕ → ℝ) (F H : PeriodicLocal k) (a N : ℕ) :
    finiteSeries B hk r g (F + H) a N =
      finiteSeries B hk r g F a N + finiteSeries B hk r g H a N := by
  simp [finiteSeries, add_div, Finset.sum_add_distrib]

/-- The paper's finite boundary identity, with arbitrary initial index. -/
theorem finiteSeries_telescope {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (H : PeriodicLocal k) (a N : ℕ) :
    finiteSeries B hk r g (cyclicTelescope B hk H) a N =
      localValue hk r g H a - localValue hk r g H (a + N) / (B : ℝ) ^ N := by
  have hb : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hB))
  simpa [finiteSeries, localValue_telescope, Nat.add_assoc] using
    finite_weighted_boundary hb (fun i ↦ localValue hk r g H (a + i)) N

/-- Any proved polynomial decomposition gives the finite series difference;
the decomposition hypothesis concerns only the displayed input tuples. -/
theorem finiteSeries_decomposition {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (F R H : PeriodicLocal k)
    (hF : F = R + cyclicTelescope B hk H) (a N : ℕ) :
    finiteSeries B hk r g F a N - finiteSeries B hk r g R a N =
      localValue hk r g H a - localValue hk r g H (a + N) / (B : ℝ) ^ N := by
  rw [hF, finiteSeries_add, add_sub_cancel_left, finiteSeries_telescope hB]

/-- A shifted chain and its weighted root have an explicit finite boundary. -/
theorem finiteSeries_shiftPower {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (F : PeriodicLocal k) (j a N : ℕ) :
    finiteSeries B hk r g (shiftPower hk j F) a N -
        finiteSeries B hk r g ((B : ℚ) ^ j • F) a N =
      localValue hk r g (-geometricPrimitive B hk j F) a -
        localValue hk r g (-geometricPrimitive B hk j F) (a + N) / (B : ℝ) ^ N :=
  finiteSeries_decomposition hB hk r g _ _ _ (shiftPower_decomposition B hk j F) a N

/-- The frozen paper's finite boundary for the actual canonical normal form.
Taking `a = 1` gives the displayed first and `(N+1)`st gap windows. -/
theorem finiteSeries_normalForm {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (g : ℕ → ℝ) (F : PeriodicLocal k) (a N : ℕ) :
    finiteSeries B hk r g F a N - finiteSeries B hk r g (normalForm hB hk F) a N =
      localValue hk r g (primitive hB hk F) a -
        localValue hk r g (primitive hB hk F) (a + N) / (B : ℝ) ^ N :=
  finiteSeries_decomposition hB hk r g F _ _ (decomposition hB hk F) a N

end

end PrimeGapNormality.Prime.CoreCyclic
