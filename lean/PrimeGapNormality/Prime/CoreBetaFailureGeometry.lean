import PrimeGapNormality.Prime.CoreBetaLevelSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Geometry of an actual first failed beta prefix

Earlier level inequalities are derived from the concrete admission and
first-failure records. A finite logarithmic budget induction turns them
into the geometric lower bound for the last, hence least, selected prime.
-/

namespace PrimeGapNormality.Prime.CoreBetaFailureGeometry

open CoreBetaBuchstab CoreBetaLevelSupport
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

def contraction (β : ℕ) : ℝ := ((β : ℝ) - 1) / β
def logProduct (ps : List ℕ) : ℝ := (ps.map (fun p : ℕ => Real.log (p : ℝ))).sum

theorem contraction_props {β : ℕ} (hβ : 2 ≤ β) :
    0 ≤ contraction β ∧ contraction β ≤ 1 ∧
      (β : ℝ) * contraction β = (β : ℝ) - 1 := by
  have hb : (0 : ℝ) < β := by exact_mod_cast (by omega : 0 < β)
  have hb1 : (1 : ℝ) ≤ β := by exact_mod_cast (by omega : 1 ≤ β)
  refine ⟨div_nonneg (sub_nonneg.mpr hb1) hb.le, ?_, ?_⟩
  · exact (div_le_one hb).mpr (by linarith)
  · unfold contraction
    field_simp [hb.ne']
    <;> ring

theorem accepted_append_left (upper : Bool) (A : List ℕ → Prop) (stem xs ys : List ℕ)
    (h : accepted upper A stem (xs ++ ys)) : accepted upper A stem xs := by
  induction xs generalizing upper stem with
  | nil => trivial
  | cons p xs ih => exact ⟨h.1, ih (!upper) (stem ++ [p]) h.2⟩

/-- Before a recorded first failure, the whole preceding selected stem
is actually admitted. -/
theorem firstFailure_dropLast_accepted (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (e : List ℕ × List ℕ)
    (he : e ∈ firstFailures upper A stem ps) :
    accepted upper A stem e.1.dropLast := by
  induction ps generalizing upper stem e with
  | nil => simp [firstFailures] at he
  | cons p ps ih =>
    rw [firstFailures] at he
    rcases List.mem_append.mp he with he | he
    · exact ih upper stem e he
    · by_cases hs : stops upper A stem p
      · simp only [hs, if_true, List.mem_singleton] at he
        subst e
        trivial
      · rw [if_neg hs] at he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        have hn := (firstFailure_sublist (!upper) A (stem ++ [p]) ps e' he').1
        rw [List.dropLast_cons_of_ne_nil hn]
        exact ⟨hs, ih (!upper) (stem ++ [p]) e' he'⟩

/-- Admission supplies the relaxed exponent β at every admitted last
prime, whether or not that last position itself was tested. -/
theorem accepted_relaxed_cost_lt {β : ℕ} (hβ : 2 ≤ β) {Z R : ℝ}
    (hZ : 1 ≤ Z) (hlevel : Z ^ β ≤ R) (upper : Bool) (ps : List ℕ)
    (hne : ps ≠ []) (hdec : ps.Pairwise (fun p q => q < p))
    (hpos : ∀ p ∈ ps, 1 ≤ p) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z)
    (ha : accepted upper (test β R) [] ps) : cost (β - 1) ps < R := by
  rcases List.eq_nil_or_concat' ps with rfl | ⟨xs, p, rfl⟩
  · contradiction
  rcases List.eq_nil_or_concat' xs with rfl | ⟨ys, q, rfl⟩
  · have hp := hbelow p (by simp)
    simpa only [List.nil_append, cost, Nat.sub_add_cancel (by omega : 1 ≤ β)] using
      (pow_lt_pow_left₀ hp (Nat.cast_nonneg p) (by omega : β ≠ 0)).trans_le hlevel
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpos p (by simp)
  have hpq : (p : ℝ) ≤ q := by
    have h := (List.pairwise_append.mp hdec).2.2 q (by simp) p (by simp)
    exact_mod_cast Nat.le_of_lt h
  have htest := accepted_last_pair upper (test β R) [] ys q p
    (by simpa only [List.append_assoc, List.singleton_append] using ha)
  simp only [List.nil_append] at htest
  rcases htest with hfull | hprev
  · have hfull' : cost β ((ys ++ [q]) ++ [p]) < R := by
      simpa only [test, List.append_assoc, List.singleton_append] using hfull
    apply lt_of_le_of_lt _ hfull'
    rw [cost_append_singleton, cost_append_singleton]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hp1 (by omega : β - 1 + 1 ≤ β + 1)) (natProduct_nonneg _)
  · have hprev' : cost β (ys ++ [q]) < R := hprev
    calc
      cost (β - 1) ((ys ++ [q]) ++ [p]) = natProduct ys * ((q : ℝ) * (p : ℝ) ^ β) := by
        rw [cost_append_singleton, Nat.sub_add_cancel (by omega : 1 ≤ β), natProduct_append]
        simp [natProduct, product, mul_assoc]
      _ ≤ natProduct ys * ((q : ℝ) * (q : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg p) hpq β)
            (Nat.cast_nonneg q)) (natProduct_nonneg ys)
      _ = cost β (ys ++ [q]) := by rw [cost_append_singleton, pow_succ]; ring
      _ < R := hprev'

theorem natProduct_pos (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p) : 0 < natProduct ps := by
  induction ps with
  | nil => simp [natProduct]
  | cons p ps ih =>
    change 0 < (p : ℝ) * natProduct ps
    exact mul_pos (Nat.cast_pos.mpr (hp p (by simp))) (ih (fun q hq => hp q (by simp [hq])))

theorem log_natProduct (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p) :
    Real.log (natProduct ps) = logProduct ps := by
  induction ps with
  | nil => simp [natProduct, logProduct]
  | cons p ps ih =>
    have ht : ∀ q ∈ ps, 0 < q := fun q hq => hp q (by simp [hq])
    change Real.log ((p : ℝ) * natProduct ps) = Real.log (p : ℝ) + logProduct ps
    rw [Real.log_mul (Nat.cast_ne_zero.mpr (hp p (by simp)).ne') (natProduct_pos ps ht).ne', ih ht]

/-- General finite budget lemma. Its explicit prefix premise is discharged
from admission below, and is not an assumption at the final endpoint. -/
theorem log_slack_ge {β : ℕ} (hβ : 2 ≤ β) (ps : List ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hpref : ∀ (u : List ℕ) (p : ℕ) (v : List ℕ), ps = u ++ p :: v →
      logProduct u + (β : ℝ) * Real.log (p : ℝ) ≤ L) :
    contraction β ^ ps.length * L ≤ L - logProduct ps := by
  obtain ⟨hq0, hq1, hqβ⟩ := contraction_props hβ
  have hb : (0 : ℝ) < β := by exact_mod_cast (by omega : 0 < β)
  induction ps generalizing L with
  | nil => simp [logProduct]
  | cons p ps ih =>
    have hhead := hpref [] p ps rfl
    simp only [logProduct, List.map_nil, List.sum_nil, zero_add] at hhead
    let L' := L - Real.log (p : ℝ)
    have hprod : (β : ℝ) * (contraction β * L) = ((β : ℝ) - 1) * L := by
      rw [← mul_assoc, hqβ]
    have hstep : contraction β * L ≤ L' := by dsimp only [L']; nlinarith
    have hL' : 0 ≤ L' := (mul_nonneg hq0 hL).trans hstep
    have htail : ∀ (u : List ℕ) (q : ℕ) (v : List ℕ), ps = u ++ q :: v →
        logProduct u + (β : ℝ) * Real.log (q : ℝ) ≤ L' := by
      intro u q v hv
      have h := hpref (p :: u) q v (by simp [hv])
      change (Real.log (p : ℝ) + logProduct u) + (β : ℝ) * Real.log (q : ℝ) ≤ L at h
      dsimp only [L']
      linarith
    have hi := ih L' hL' htail
    calc
      contraction β ^ (p :: ps).length * L = contraction β ^ ps.length * (contraction β * L) := by
        simp only [List.length_cons, pow_succ]
        ring
      _ ≤ contraction β ^ ps.length * L' := mul_le_mul_of_nonneg_left hstep (pow_nonneg hq0 _)
      _ ≤ L' - logProduct ps := hi
      _ = L - logProduct (p :: ps) := by simp [L', logProduct]; ring

/-- The entire prefix-budget premise is supplied by actual admission. -/
theorem admitted_log_prefix_bounds {β : ℕ} (hβ : 2 ≤ β) {Z R : ℝ}
    (hZ : 1 ≤ Z) (hlevel : Z ^ β ≤ R) (upper : Bool) (ps : List ℕ)
    (hdec : ps.Pairwise (fun p q => q < p))
    (hpos : ∀ p ∈ ps, 0 < p) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z)
    (ha : accepted upper (test β R) [] ps) :
    ∀ (u : List ℕ) (p : ℕ) (v : List ℕ), ps = u ++ p :: v →
      logProduct u + (β : ℝ) * Real.log (p : ℝ) ≤ Real.log R := by
  intro u p v hv
  have hshape : ps = (u ++ [p]) ++ v := by
    simpa only [List.append_assoc, List.singleton_append] using hv
  have hmem : ∀ q ∈ u ++ [p], q ∈ ps := by
    intro q hq
    rw [hshape]
    exact List.mem_append_left v hq
  have hupos : ∀ q ∈ u, 0 < q := fun q hq => hpos q (hmem q (by simp [hq]))
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (hpos p (hmem p (by simp)))
  have hdec' : (u ++ [p]).Pairwise (fun a b => b < a) :=
    (List.pairwise_append.mp (hshape ▸ hdec)).1
  have ha' := accepted_append_left upper (test β R) [] (u ++ [p]) v (hshape ▸ ha)
  have hcost := accepted_relaxed_cost_lt hβ hZ hlevel upper (u ++ [p]) (by simp)
    hdec' (fun q hq => Nat.succ_le_of_lt (hpos q (hmem q hq)))
    (fun q hq => hbelow q (hmem q hq)) ha'
  rw [cost_append_singleton, Nat.sub_add_cancel (by omega : 1 ≤ β)] at hcost
  have hlog := Real.log_lt_log
    (mul_pos (natProduct_pos u hupos) (pow_pos hp β)) hcost
  rw [Real.log_mul (natProduct_pos u hupos).ne' (pow_pos hp β).ne',
    Real.log_pow, log_natProduct u hupos] at hlog
  exact hlog.le

/-- Actual least-prime geometry, with the last selected prime written
explicitly. No earlier-prefix invariant is supplied by the caller. -/
theorem firstFailure_last_lower_of_append {β : ℕ} (hβ : 2 ≤ β)
    {Z R : ℝ} (hZ : 1 < Z) (hR : 1 < R) (hlevel : Z ^ β ≤ R)
    (upper : Bool) (ps : List ℕ) (hdec : ps.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z)
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper (test β R) [] ps)
    (xs : List ℕ) (p : ℕ) (hx : e.1 = xs ++ [p]) :
    Z ^ (contraction β ^ e.1.length) ≤ (p : ℝ) := by
  have hsub := firstFailure_sublist upper (test β R) [] ps e he
  have hedec := List.Pairwise.sublist hsub.2 hdec
  have hselpos : ∀ q ∈ e.1, 0 < q := fun q hq => (hprime q (hsub.2.subset hq)).pos
  have hselbelow : ∀ q ∈ e.1, (q : ℝ) < Z := fun q hq => hbelow q (hsub.2.subset hq)
  have hxspos : ∀ q ∈ xs, 0 < q := by
    intro q hq
    exact hselpos q (by rw [hx]; simp [hq])
  have hxsbelow : ∀ q ∈ xs, (q : ℝ) < Z := by
    intro q hq
    exact hselbelow q (by rw [hx]; simp [hq])
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (hselpos p (by rw [hx]; simp))
  have hxsdec : xs.Pairwise (fun p q => q < p) :=
    (List.pairwise_append.mp (hx ▸ hedec)).1
  have hadm : accepted upper (test β R) [] xs := by
    have h := firstFailure_dropLast_accepted upper (test β R) [] ps e he
    simpa only [hx, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] using h
  have hpref := admitted_log_prefix_bounds hβ hZ.le hlevel upper xs hxsdec hxspos hxsbelow hadm
  have hslack := log_slack_ge hβ xs (Real.log R) (Real.log_pos hR).le hpref
  have hfailure : R ≤ natProduct xs * (p : ℝ) ^ (β + 1) := by
    have h := firstFailure_not_test upper (test β R) [] ps e he
    simpa only [List.nil_append, hx, test, cost_append_singleton, not_lt] using h
  have hlast := Real.log_le_log (zero_lt_one.trans hR) hfailure
  rw [Real.log_mul (natProduct_pos xs hxspos).ne' (pow_pos hp _).ne',
    Real.log_pow, log_natProduct xs hxspos, Nat.cast_add, Nat.cast_one] at hlast
  have hlevelLog := Real.log_le_log (pow_pos (zero_lt_one.trans hZ) β) hlevel
  rw [Real.log_pow] at hlevelLog
  obtain ⟨hq0, hq1, hqβ⟩ := contraction_props hβ
  have hsmall : ((β : ℝ) + 1) * contraction β ≤ (β : ℝ) := by nlinarith
  have hlogZ : 0 ≤ Real.log Z := (Real.log_pos hZ).le
  have hscale : 0 ≤ contraction β ^ xs.length := pow_nonneg hq0 _
  have hchain : ((β : ℝ) + 1) * (contraction β ^ (xs.length + 1) * Real.log Z) ≤
      ((β : ℝ) + 1) * Real.log (p : ℝ) := by
    calc
      ((β : ℝ) + 1) * (contraction β ^ (xs.length + 1) * Real.log Z) =
          (contraction β ^ xs.length * Real.log Z) * (((β : ℝ) + 1) * contraction β) := by
        rw [pow_succ]
        ring
      _ ≤ (contraction β ^ xs.length * Real.log Z) * (β : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (mul_nonneg hscale hlogZ)
      _ = contraction β ^ xs.length * ((β : ℝ) * Real.log Z) := by ring
      _ ≤ contraction β ^ xs.length * Real.log R := mul_le_mul_of_nonneg_left hlevelLog hscale
      _ ≤ Real.log R - logProduct xs := hslack
      _ ≤ ((β : ℝ) + 1) * Real.log (p : ℝ) := by linarith
  have hb : (0 : ℝ) < (β : ℝ) + 1 := by positivity
  have hlogp := le_of_mul_le_mul_left hchain hb
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ), ← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  simpa only [hx, List.length_append, List.length_singleton, mul_comm] using hlogp

/-- The final first-failure bound in terms of the literal last element.
For the decreasing prime lists in the sieve this is the least prime. -/
theorem firstFailure_last_lower {β : ℕ} (hβ : 2 ≤ β)
    {Z R : ℝ} (hZ : 1 < Z) (hR : 1 < R) (hlevel : Z ^ β ≤ R)
    (upper : Bool) (ps : List ℕ) (hdec : ps.Pairwise (fun p q => q < p))
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hbelow : ∀ p ∈ ps, (p : ℝ) < Z)
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper (test β R) [] ps) :
    Z ^ (contraction β ^ e.1.length) ≤ (e.1.getLastD 1 : ℝ) := by
  have hn := (firstFailure_sublist upper (test β R) [] ps e he).1
  rcases List.eq_nil_or_concat' e.1 with hz | ⟨xs, p, hx⟩
  · exact (hn hz).elim
  · have h := firstFailure_last_lower_of_append hβ hZ hR hlevel upper ps hdec hprime hbelow e he xs p hx
    simpa only [hx, List.getLastD_concat] using h

end
end PrimeGapNormality.Prime.CoreBetaFailureGeometry
