import PrimeGapNormality.Prime.CoreBetaBuchstab
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual beta admission implies level support

The beta parameter is natural, sufficient for the rough specialization
β=9k+1. No support or first-failure depth is assumed: both are consequences
of the literal alternating prefix admission predicate in CoreBetaBuchstab.
-/

namespace PrimeGapNormality.Prime.CoreBetaLevelSupport

open CoreBetaBuchstab
open scoped Classical
noncomputable section

set_option maxHeartbeats 600000

def natProduct (ps : List ℕ) : ℝ := product (fun p => (p : ℝ)) ps

/-- Recursive form of product(dropLast stem)*last(stem)^(β+1). -/
def cost (β : ℕ) : List ℕ → ℝ
  | [] => 1
  | [p] => (p : ℝ) ^ (β + 1)
  | p :: q :: ps => (p : ℝ) * cost β (q :: ps)

def test (β : ℕ) (R : ℝ) (stem : List ℕ) : Prop := cost β stem < R

theorem natProduct_nonneg (ps : List ℕ) : 0 ≤ natProduct ps := by
  induction ps with
  | nil => simp [natProduct]
  | cons p ps ih =>
    change 0 ≤ (p : ℝ) * natProduct ps
    exact mul_nonneg (Nat.cast_nonneg p) ih

theorem natProduct_append (ps qs : List ℕ) :
    natProduct (ps ++ qs) = natProduct ps * natProduct qs := by
  simp [natProduct, product]

theorem cost_cons_of_ne_nil (β p : ℕ) (ps : List ℕ) (hps : ps ≠ []) :
    cost β (p :: ps) = (p : ℝ) * cost β ps := by
  cases ps with
  | nil => contradiction
  | cons q qs => rfl

/-- Exact identification with the last-prime power test. -/
theorem cost_append_singleton (β : ℕ) (ps : List ℕ) (p : ℕ) :
    cost β (ps ++ [p]) = natProduct ps * (p : ℝ) ^ (β + 1) := by
  induction ps with
  | nil => simp [cost, natProduct]
  | cons q qs ih =>
    rw [List.cons_append, cost_cons_of_ne_nil β q (qs ++ [p]) (by simp), ih]
    change (q : ℝ) * (natProduct qs * (p : ℝ) ^ (β + 1)) =
      ((q : ℝ) * natProduct qs) * (p : ℝ) ^ (β + 1)
    ring

theorem cost_eq_dropLast_mul_last (β : ℕ) (ps : List ℕ) (hne : ps ≠ []) :
    cost β ps = natProduct ps.dropLast * (ps.getLast hne : ℝ) ^ (β + 1) := by
  calc
    cost β ps = cost β (ps.dropLast ++ [ps.getLast hne]) :=
      congrArg (cost β) (List.dropLast_append_getLast hne).symm
    _ = _ := cost_append_singleton β _ _

/-- One of the last two prefixes is genuinely tested, regardless of the
starting mode. This is derived from alternating admission itself. -/
theorem accepted_last_pair (upper : Bool) (A : List ℕ → Prop)
    (stem xs : List ℕ) (p q : ℕ)
    (h : accepted upper A stem (xs ++ [p, q])) :
    A (stem ++ xs ++ [p, q]) ∨ A (stem ++ xs ++ [p]) := by
  induction xs generalizing upper stem with
  | nil =>
    cases upper with
    | false =>
      left
      have ha : A ((stem ++ [p]) ++ [q]) := by simpa [stops] using h.2.1
      simpa [List.append_assoc] using ha
    | true =>
      right
      have ha : A (stem ++ [p]) := by simpa [stops] using h.1
      simpa using ha
  | cons x xs ih =>
    have hc := ih (!upper) (stem ++ [x]) h.2
    simpa [List.append_assoc] using hc

/-- Literal accepted decreasing lists have product strictly below R.
Only positivity and decreasing order are used; primality is not needed. -/
theorem accepted_product_lt
    {β : ℕ} (hβ : 1 ≤ β) {Z R : ℝ} (hZ : 1 ≤ Z) (hR : 1 < R)
    (hlevel : Z ^ β ≤ R) (upper : Bool) (ps : List ℕ)
    (hdec : ps.Pairwise (fun p q => q < p))
    (hpos : ∀ p ∈ ps, 1 ≤ p) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z)
    (ha : accepted upper (test β R) [] ps) : natProduct ps < R := by
  rcases List.eq_nil_or_concat' ps with rfl | ⟨xs, p, rfl⟩
  · simpa [natProduct] using hR
  rcases List.eq_nil_or_concat' xs with rfl | ⟨ys, q, rfl⟩
  · have hp := hbelow p (by simp)
    have hZR : Z ≤ R := (le_self_pow₀ hZ (by omega : β ≠ 0)).trans hlevel
    simpa [natProduct, product] using hp.trans_le hZR
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpos p (by simp)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hpos q (by simp)
  have hpq : (p : ℝ) ≤ q := by
    have h := (List.pairwise_append.mp hdec).2.2 q (by simp) p (by simp)
    exact_mod_cast Nat.le_of_lt h
  have htest := accepted_last_pair upper (test β R) [] ys q p
    (by simpa only [List.append_assoc, List.singleton_append] using ha)
  simp only [List.nil_append] at htest
  rcases htest with hfull | hprev
  · have hfull' : cost β ((ys ++ [q]) ++ [p]) < R := by
      simpa only [test, List.append_assoc, List.singleton_append] using hfull
    calc
      natProduct ((ys ++ [q]) ++ [p]) = natProduct (ys ++ [q]) * (p : ℝ) := by
        rw [natProduct_append]
        simp [natProduct, product]
      _ ≤ natProduct (ys ++ [q]) * (p : ℝ) ^ (β + 1) :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ hp1 (Nat.succ_ne_zero β))
          (natProduct_nonneg _)
      _ = cost β ((ys ++ [q]) ++ [p]) := (cost_append_singleton β _ p).symm
      _ < R := hfull'
  · have hprev' : cost β (ys ++ [q]) < R := hprev
    have hpPow : (p : ℝ) ≤ (q : ℝ) ^ β :=
      hpq.trans (le_self_pow₀ hq1 (by omega : β ≠ 0))
    calc
      natProduct ((ys ++ [q]) ++ [p]) = natProduct ys * ((q : ℝ) * (p : ℝ)) := by
        simp [natProduct, product, List.prod_append, mul_assoc]
      _ ≤ natProduct ys * ((q : ℝ) * (q : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg q)) (natProduct_nonneg ys)
      _ = cost β (ys ++ [q]) := by rw [cost_append_singleton, pow_succ]; ring
      _ < R := hprev'

/-- The actual nonzero coefficients therefore have strict level support. -/
theorem coefficient_ne_zero_product_lt
    {β : ℕ} (hβ : 1 ≤ β) {Z R : ℝ} (hZ : 1 ≤ Z) (hR : 1 < R)
    (hlevel : Z ^ β ≤ R) (upper : Bool) (ps : List ℕ)
    (hdec : ps.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z)
    (hc : coefficient upper (test β R) [] ps ≠ 0) : natProduct ps < R := by
  apply accepted_product_lt hβ hZ hR hlevel upper ps hdec
    (fun p hp => Nat.le_of_lt (hprime p hp).one_lt) hbelow
  by_contra hn
  exact hc (by simp [coefficient, hn])

/-- Every recorded stop fails its actual full-prefix predicate. -/
theorem firstFailure_not_test (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ)
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper A stem ps) :
    ¬ A (stem ++ e.1) := by
  induction ps generalizing upper stem e with
  | nil => simp [firstFailures] at he
  | cons p ps ih =>
    rw [firstFailures] at he
    rcases List.mem_append.mp he with he | he
    · exact ih upper stem e he
    · by_cases hs : stops upper A stem p
      · simp only [hs, if_true, List.mem_singleton] at he
        subst e
        exact hs.2
      · rw [if_neg hs] at he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        simpa only [List.append_assoc, List.singleton_append] using
          ih (!upper) (stem ++ [p]) e' he'

/-- Failure records contain a genuine nonempty selected sublist. -/
theorem firstFailure_sublist (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ)
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper A stem ps) :
    e.1 ≠ [] ∧ List.Sublist e.1 ps := by
  induction ps generalizing upper stem e with
  | nil => simp [firstFailures] at he
  | cons p ps ih =>
    rw [firstFailures] at he
    rcases List.mem_append.mp he with he | he
    · have h := ih upper stem e he
      exact ⟨h.1, List.Sublist.cons p h.2⟩
    · by_cases hs : stops upper A stem p
      · simp only [hs, if_true, List.mem_singleton] at he
        subst e
        exact ⟨by simp, List.Sublist.cons₂ p (List.nil_sublist ps)⟩
      · rw [if_neg hs] at he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact ⟨by simp, List.Sublist.cons₂ p (ih (!upper) (stem ++ [p]) e' he').2⟩

private theorem product_le_pow_length {Z : ℝ} (hZ : 0 ≤ Z) (ps : List ℕ)
    (hbelow : ∀ p ∈ ps, (p : ℝ) ≤ Z) : natProduct ps ≤ Z ^ ps.length := by
  induction ps with
  | nil => simp [natProduct]
  | cons p ps ih =>
    change (p : ℝ) * natProduct ps ≤ Z ^ (ps.length + 1)
    rw [pow_succ]
    calc
      (p : ℝ) * natProduct ps ≤ Z * Z ^ ps.length :=
        mul_le_mul (hbelow p (by simp)) (ih (fun q hq => hbelow q (by simp [hq])))
          (natProduct_nonneg ps) hZ
      _ = _ := mul_comm _ _

/-- A nonempty prefix has cost strictly below Z^(length+β), because its
last prime is strictly below Z. -/
theorem cost_lt_pow_length {Z : ℝ} (hZ : 0 < Z) (β : ℕ) (ps : List ℕ)
    (hne : ps ≠ []) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z) :
    cost β ps < Z ^ (ps.length + β) := by
  rcases List.eq_nil_or_concat' ps with rfl | ⟨xs, p, rfl⟩
  · contradiction
  have hp := hbelow p (by simp)
  have hxs := product_le_pow_length hZ.le xs (fun q hq => (hbelow q (by simp [hq])).le)
  rw [cost_append_singleton]
  calc
    natProduct xs * (p : ℝ) ^ (β + 1) ≤ Z ^ xs.length * (p : ℝ) ^ (β + 1) :=
      mul_le_mul_of_nonneg_right hxs (pow_nonneg (Nat.cast_nonneg p) _)
    _ < Z ^ xs.length * Z ^ (β + 1) :=
      mul_lt_mul_of_pos_left
        (pow_lt_pow_left₀ hp (Nat.cast_nonneg p) (Nat.succ_ne_zero β)) (pow_pos hZ _)
    _ = Z ^ ((xs ++ [p]).length + β) := by
      rw [← pow_add]
      congr 1
      simp only [List.length_append, List.length_singleton]
      omega

/-- Actual first-failure depth: r > log(R)/log(Z)-β. No assumed geometric
support statement occurs among the hypotheses. -/
theorem firstFailure_length_gt {Z R : ℝ} (hZ : 1 < Z) (hR : 0 < R)
    (β : ℕ) (upper : Bool) (ps : List ℕ)
    (hbelow : ∀ p ∈ ps, (p : ℝ) < Z) (e : List ℕ × List ℕ)
    (he : e ∈ firstFailures upper (test β R) [] ps) :
    Real.log R / Real.log Z - (β : ℝ) < (e.1.length : ℝ) := by
  have hsub := firstFailure_sublist upper (test β R) [] ps e he
  have hfail : R ≤ cost β e.1 := by
    have h := firstFailure_not_test upper (test β R) [] ps e he
    simpa only [List.nil_append, test, not_lt] using h
  have hcost := cost_lt_pow_length (zero_lt_one.trans hZ) β e.1 hsub.1
    (fun p hp => hbelow p (hsub.2.subset hp))
  have hlog := Real.log_lt_log hR (hfail.trans_lt hcost)
  rw [Real.log_pow] at hlog
  have hdiv : Real.log R / Real.log Z < ((e.1.length + β : ℕ) : ℝ) :=
    (div_lt_iff₀ (Real.log_pos hZ)).mpr hlog
  push_cast at hdiv
  linarith

end
end PrimeGapNormality.Prime.CoreBetaLevelSupport
