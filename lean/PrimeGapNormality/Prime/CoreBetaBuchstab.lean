import Mathlib.Data.List.Sublists
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-!
# Finite parity-stopped Buchstab weights

The available primes will be supplied as a decreasing list. The identities
here are finite polynomial identities, valid for any list and any real
weights. A selected sublist gets its actual sign (-1)^length if it passes
the alternating stem tests, and zero otherwise. First-failure records
retain the selected stem and the unexpanded smaller-prime suffix.

There is no assumed sieve inequality or remainder identity. Numerical
beta-level support and the fundamental-lemma estimate are later steps.
-/

namespace PrimeGapNormality.Prime.CoreBetaBuchstab

open scoped Classical
noncomputable section

set_option maxHeartbeats 600000

/-- Upper mode tests the next stem; lower mode takes one unchecked step.
The mode switches after each selected element, not after skipped elements. -/
def stops (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ) (p : ℕ) : Prop :=
  upper = true ∧ ¬ A (stem ++ [p])

def accepted (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ) : List ℕ → Prop
  | [] => True
  | p :: ps => ¬ stops upper A stem p ∧ accepted (!upper) A (stem ++ [p]) ps

def coefficient (upper : Bool) (A : List ℕ → Prop) (stem selected : List ℕ) : ℝ :=
  if accepted upper A stem selected then (-1 : ℝ) ^ selected.length else 0

@[simp] theorem coefficient_nil (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ) :
    coefficient upper A stem [] = 1 := by simp [coefficient, accepted]

theorem coefficient_abs_le_one (upper : Bool) (A : List ℕ → Prop)
    (stem selected : List ℕ) : |coefficient upper A stem selected| ≤ 1 := by
  unfold coefficient
  split_ifs <;> simp [abs_pow]

theorem coefficient_cons (upper : Bool) (A : List ℕ → Prop)
    (stem : List ℕ) (p : ℕ) (selected : List ℕ) :
    coefficient upper A stem (p :: selected) =
      if stops upper A stem p then 0 else
        -coefficient (!upper) A (stem ++ [p]) selected := by
  by_cases hs : stops upper A stem p <;>
    by_cases ha : accepted (!upper) A (stem ++ [p]) selected <;>
    simp [coefficient, accepted, hs, ha, pow_succ]

def product (g : ℕ → ℝ) (ps : List ℕ) : ℝ := (ps.map g).prod
def euler (g : ℕ → ℝ) (ps : List ℕ) : ℝ := (ps.map (fun p => 1 - g p)).prod

@[simp] theorem product_nil (g : ℕ → ℝ) : product g [] = 1 := rfl
@[simp] theorem product_cons (g : ℕ → ℝ) (p : ℕ) (ps : List ℕ) :
    product g (p :: ps) = g p * product g ps := rfl
@[simp] theorem euler_nil (g : ℕ → ℝ) : euler g [] = 1 := rfl
@[simp] theorem euler_cons (g : ℕ → ℝ) (p : ℕ) (ps : List ℕ) :
    euler g (p :: ps) = (1 - g p) * euler g ps := rfl

/-- Literal weighted sum of predicate-defined coefficients over sublists. -/
def main (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ) (g : ℕ → ℝ) : ℝ :=
  (ps.sublists'.map (fun selected => coefficient upper A stem selected * product g selected)).sum

/-- A record consists of the selected first-failure stem and the exact
suffix still unexpanded after its last selected element. -/
def firstFailures (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ) :
    List ℕ → List (List ℕ × List ℕ)
  | [] => []
  | p :: ps =>
      firstFailures upper A stem ps ++
        if stops upper A stem p then [([p], ps)]
        else (firstFailures (!upper) A (stem ++ [p]) ps).map
          (fun e => (p :: e.1, e.2))

/-- The remainder is an explicit finite sum, not an unspecified error. -/
def remainder (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ) (g : ℕ → ℝ) : ℝ :=
  ((firstFailures upper A stem ps).map (fun e => product g e.1 * euler g e.2)).sum

@[simp] theorem main_nil (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ) (g : ℕ → ℝ) :
    main upper A stem [] g = 1 := by simp [main]

@[simp] theorem remainder_nil (upper : Bool) (A : List ℕ → Prop)
    (stem : List ℕ) (g : ℕ → ℝ) : remainder upper A stem [] g = 0 := rfl

theorem main_cons (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ)
    (p : ℕ) (ps : List ℕ) (g : ℕ → ℝ) :
    main upper A stem (p :: ps) g = main upper A stem ps g -
      g p * (if stops upper A stem p then 0 else main (!upper) A (stem ++ [p]) ps g) := by
  unfold main
  rw [List.sublists'_cons, List.map_append, List.sum_append, List.map_map]
  change (ps.sublists'.map (fun selected =>
      coefficient upper A stem selected * product g selected)).sum +
    (ps.sublists'.map (fun selected =>
      coefficient upper A stem (p :: selected) * (g p * product g selected))).sum = _
  simp_rw [coefficient_cons]
  by_cases hs : stops upper A stem p
  · simp [hs]
  · simp only [hs, if_false]
    have heq : (fun selected : List ℕ =>
        -coefficient (!upper) A (stem ++ [p]) selected * (g p * product g selected)) =
        (fun selected => (-g p) *
          (coefficient (!upper) A (stem ++ [p]) selected * product g selected)) := by
      funext selected
      ring
    rw [heq, List.sum_map_mul_left]
    ring

theorem remainder_cons (upper : Bool) (A : List ℕ → Prop) (stem : List ℕ)
    (p : ℕ) (ps : List ℕ) (g : ℕ → ℝ) :
    remainder upper A stem (p :: ps) g = remainder upper A stem ps g +
      g p * (if stops upper A stem p then euler g ps else
        remainder (!upper) A (stem ++ [p]) ps g) := by
  unfold remainder
  rw [firstFailures, List.map_append, List.sum_append]
  by_cases hs : stops upper A stem p
  · simp [hs]
  · simp only [hs, if_false, List.map_map, Function.comp_apply, product_cons]
    change ((firstFailures upper A stem ps).map
        (fun e => product g e.1 * euler g e.2)).sum +
      ((firstFailures (!upper) A (stem ++ [p]) ps).map
        (fun e => (g p * product g e.1) * euler g e.2)).sum = _
    have heq : (fun e : List ℕ × List ℕ => (g p * product g e.1) * euler g e.2) =
        (fun e => g p * (product g e.1 * euler g e.2)) := by
      funext e
      ring
    rw [heq, List.sum_map_mul_left]

/-- Both exact signed identities, proved together by structural induction.
The stem parameter makes all recursive tests literal. -/
theorem main_eq_euler_add_signed_remainder
    (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ) (g : ℕ → ℝ) :
    main upper A stem ps g = euler g ps +
      (if upper then (1 : ℝ) else -1) * remainder upper A stem ps g := by
  induction ps generalizing upper stem with
  | nil => simp
  | cons p ps ih =>
    rw [main_cons, remainder_cons, euler_cons]
    cases upper with
    | false =>
      simp only [stops, Bool.false_eq_true, false_and, if_false, Bool.not_false]
      rw [ih false stem, ih true (stem ++ [p])]
      simp only [Bool.false_eq_true, if_false, if_true]
      ring
    | true =>
      simp only [Bool.not_true]
      rw [ih true stem, ih false (stem ++ [p])]
      by_cases hs : stops true A stem p <;>
        simp only [hs, Bool.false_eq_true, if_true, if_false] <;> ring

theorem upper_exact (A : List ℕ → Prop) (ps : List ℕ) (g : ℕ → ℝ) :
    main true A [] ps g = euler g ps + remainder true A [] ps g := by
  simpa using main_eq_euler_add_signed_remainder true A [] ps g

theorem lower_exact (A : List ℕ → Prop) (ps : List ℕ) (g : ℕ → ℝ) :
    main false A [] ps g = euler g ps - remainder false A [] ps g := by
  simpa only [Bool.false_eq_true, if_false, neg_one_mul, ← sub_eq_add_neg] using
    main_eq_euler_add_signed_remainder false A [] ps g

private theorem euler_nonneg (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ p ∈ ps, g p ≤ 1) : 0 ≤ euler g ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [euler_cons]
    exact mul_nonneg (sub_nonneg.mpr (hg p (by simp)))
      (ih (fun q hq => hg q (by simp [hq])))

theorem remainder_nonneg (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ)
    (g : ℕ → ℝ) (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1) :
    0 ≤ remainder upper A stem ps g := by
  induction ps generalizing upper stem with
  | nil => simp
  | cons p ps ih =>
    rw [remainder_cons]
    have htail : ∀ q ∈ ps, 0 ≤ g q ∧ g q ≤ 1 := fun q hq => hg q (by simp [hq])
    apply add_nonneg (ih upper stem htail)
    apply mul_nonneg (hg p (by simp)).1
    split_ifs
    · exact euler_nonneg g ps (fun q hq => (htail q hq).2)
    · exact ih (!upper) (stem ++ [p]) htail

/-- In particular this specializes to the literal avoidance indicator
when g takes the values zero and one. -/
theorem sieve_sandwich (A : List ℕ → Prop) (ps : List ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ ps, 0 ≤ g p ∧ g p ≤ 1) :
    main false A [] ps g ≤ euler g ps ∧ euler g ps ≤ main true A [] ps g := by
  rw [lower_exact, upper_exact]
  exact ⟨sub_le_self _ (remainder_nonneg false A [] ps g hg),
    le_add_of_nonneg_right (remainder_nonneg true A [] ps g hg)⟩

/-- The Boolean Euler product is precisely the actual avoidance event. -/
theorem euler_boolean (hit : ℕ → Prop) (ps : List ℕ) :
    euler (fun p => if hit p then 1 else 0) ps =
      if ∀ p ∈ ps, ¬ hit p then 1 else 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [euler_cons, ih]
    by_cases hp : hit p <;> simp [hp]

theorem boolean_sieve_sandwich (A : List ℕ → Prop) (ps : List ℕ) (hit : ℕ → Prop) :
    main false A [] ps (fun p => if hit p then 1 else 0) ≤
      (if ∀ p ∈ ps, ¬ hit p then 1 else 0) ∧
    (if ∀ p ∈ ps, ¬ hit p then 1 else 0) ≤
      main true A [] ps (fun p => if hit p then 1 else 0) := by
  have h := sieve_sandwich A ps (fun p => if hit p then 1 else 0)
    (by intro p hp; split_ifs <;> norm_num)
  simpa only [euler_boolean] using h

end
end PrimeGapNormality.Prime.CoreBetaBuchstab
