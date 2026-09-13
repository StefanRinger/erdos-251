import PrimeGapNormality.Prime.CoreCyclicDegree

/-!
# Executable finite monomial reduction

`Term` and `Code` contain only finite lists, natural-number indices, finite
labels, and rational coefficients. `evaluateNormalForm` is executable and
does not call `normalForm`, `Classical.choose`, or polynomial operations.
Its interpretation in the actual polynomial space equals `normalForm`.
Every actual polynomial tuple has such a finite representation.
-/

namespace PrimeGapNormality.Prime.CoreCyclic.Executable

open MvPolynomial
open scoped BigOperators

structure Term (k : ℕ) where
  label : Fin k
  coefficient : ℚ
  vars : List ℕ
  deriving DecidableEq, Repr

abbrev Code (k : ℕ) := List (Term k)

/-- A computable version of the existing cyclic label successor. -/
def nextLabel {k : ℕ} (hk : 0 < k) (r : Fin k) : Fin k := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  exact r + 1

theorem nextLabel_eq {k : ℕ} (hk : 0 < k) (r : Fin k) :
    nextLabel hk r = cyclicSucc hk r := rfl

/-- A finite bound for all indices in a monomial. -/
def width : List ℕ → ℕ
  | [] => 0
  | i :: is => max (i + 1) (width is)

theorem lt_width_of_mem {is : List ℕ} {i : ℕ} (hi : i ∈ is) : i < width is := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact lt_of_lt_of_le (ih hi) (le_max_right _ _)

/-- Move the label once, multiply the coefficient by the base, lower indices. -/
def lowerTerm (B : ℕ) {k : ℕ} (hk : 0 < k) (t : Term k) : Term k :=
  ⟨nextLabel hk t.label, (B : ℚ) * t.coefficient, t.vars.map Nat.pred⟩

/-- Constants are discarded. Otherwise lower until the monomial contains `u₀`.
The fuel is supplied by the explicit finite width, not by classical choice. -/
def reduceTerm (B : ℕ) {k : ℕ} (hk : 0 < k) : ℕ → Term k → Code k
  | 0, _ => []
  | n + 1, t =>
      if t.vars = [] then []
      else if 0 ∈ t.vars then [t]
      else reduceTerm B hk n (lowerTerm B hk t)

/-- Finite linear extension of monomial reduction. -/
def evaluateNormalForm (B : ℕ) {k : ℕ} (hk : 0 < k) (xs : Code k) : Code k :=
  xs.flatMap fun t => reduceTerm B hk (width t.vars) t

noncomputable def variablesPoly : List ℕ → LocalPoly
  | [] => 1
  | i :: is => X i * variablesPoly is

noncomputable def interpretTerm {k : ℕ} (t : Term k) : PeriodicLocal k :=
  labelled t.label (C t.coefficient * variablesPoly t.vars)

noncomputable def interpret {k : ℕ} : Code k → PeriodicLocal k
  | [] => 0
  | t :: ts => interpretTerm t + interpret ts

@[simp] theorem interpret_nil {k : ℕ} : interpret ([] : Code k) = 0 := rfl

@[simp] theorem interpret_cons {k : ℕ} (t : Term k) (ts : Code k) :
    interpret (t :: ts) = interpretTerm t + interpret ts := rfl

@[simp] theorem interpret_append {k : ℕ} (xs ys : Code k) :
    interpret (xs ++ ys) = interpret xs + interpret ys := by
  induction xs with
  | nil => simp
  | cons t ts ih => simp [ih, add_assoc]

theorem strip_variablesPoly_eq_zero {is : List ℕ} (h : 0 ∈ is) :
    stripPoly 1 (variablesPoly is) = 0 := by
  induction is with
  | nil => simp at h
  | cons i is ih =>
      rcases List.mem_cons.mp h with hi | hi
      · subst i
        simp [variablesPoly]
      · simp [variablesPoly, ih hi]

theorem interpretTerm_rooted {k : ℕ} (hk : 0 < k) (t : Term k)
    (h : 0 ∈ t.vars) : drop hk (interpretTerm t) = 0 := by
  funext s
  by_cases hs : predecessor hk s = t.label
  · simp [drop_apply, interpretTerm, labelled, hs, strip_variablesPoly_eq_zero h]
  · simp [drop_apply, interpretTerm, labelled, hs]

theorem normalForm_interpretTerm_constant {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (t : Term k) (h : t.vars = []) : normalForm hB hk (interpretTerm t) = 0 := by
  have ht : interpretTerm t =
      constantTuple (fun s => if s = t.label then t.coefficient else 0) := by
    funext s
    by_cases hs : s = t.label <;>
      simp [interpretTerm, labelled, h, variablesPoly, constantTuple, hs]
  rw [ht, normalForm_constantTuple]

theorem rename_pred_variablesPoly {is : List ℕ} (h : 0 ∉ is) :
    rename Nat.succ (variablesPoly (is.map Nat.pred)) = variablesPoly is := by
  induction is with
  | nil => simp [variablesPoly]
  | cons i is ih =>
      have hi : i ≠ 0 := by intro hi; apply h; simp [hi]
      have ht : 0 ∉ is := by intro ht; apply h; simp [ht]
      simp [variablesPoly, ih ht, Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hi),
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]

theorem normalForm_lowerTerm {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (t : Term k) (h : 0 ∉ t.vars) :
    normalForm hB hk (interpretTerm (lowerTerm B hk t)) =
      normalForm hB hk (interpretTerm t) := by
  let p : LocalPoly := C t.coefficient * variablesPoly (t.vars.map Nat.pred)
  have hs : shift hk (labelled (cyclicSucc hk t.label) p) = interpretTerm t := by
    have hshift := shiftPower_labelled hk 1 t.label p
    simpa [p, interpretTerm, shiftPower_succ, rename_pred_variablesPoly h] using hshift
  have hl : interpretTerm (lowerTerm B hk t) =
      (B : ℚ) • labelled (cyclicSucc hk t.label) p := by
    funext s
    by_cases hs : s = cyclicSucc hk t.label
    · simp [interpretTerm, lowerTerm, nextLabel_eq, labelled, p, hs,
        smul_eq_C_mul, map_mul, mul_assoc]
    · simp [interpretTerm, lowerTerm, nextLabel_eq, labelled, hs]
  rw [hl, normalForm_smul, ← hs, normalForm_shift]

/-- Correctness of the bounded recursion, including constant monomials. -/
theorem reduceTerm_correct {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (n : ℕ) (t : Term k) (hn : ∀ i ∈ t.vars, i < n) :
    interpret (reduceTerm B hk n t) = normalForm hB hk (interpretTerm t) := by
  induction n generalizing t with
  | zero =>
      have ht : t.vars = [] := by
        cases hv : t.vars with
        | nil => rfl
        | cons i is => have := hn i (by simp [hv]); omega
      simp [reduceTerm, normalForm_interpretTerm_constant hB hk t ht]
  | succ n ih =>
      by_cases he : t.vars = []
      · simp [reduceTerm, he, normalForm_interpretTerm_constant hB hk t he]
      · by_cases hz : 0 ∈ t.vars
        · simp [reduceTerm, he, hz,
            normalForm_of_rooted hB hk _ (interpretTerm_rooted hk t hz)]
        · rw [reduceTerm, if_neg he, if_neg hz]
          have hb : ∀ i ∈ (lowerTerm B hk t).vars, i < n := by
            intro i hi
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
            have hpos : j ≠ 0 := by intro h; subst j; exact hz hj
            have := hn j hj
            simp only [Nat.pred_eq_sub_one]
            omega
          rw [ih _ hb, normalForm_lowerTerm hB hk t hz]

/-- The executable evaluator computes the existing actual normal form. -/
theorem evaluateNormalForm_correct {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (xs : Code k) :
    interpret (evaluateNormalForm B hk xs) = normalForm hB hk (interpret xs) := by
  induction xs with
  | nil => simp [evaluateNormalForm]
  | cons t ts ih =>
      change interpret (reduceTerm B hk (width t.vars) t ++
        evaluateNormalForm B hk ts) = normalForm hB hk (interpretTerm t + interpret ts)
      rw [interpret_append, reduceTerm_correct hB hk _ t (fun _ hi => lt_width_of_mem hi),
        ih, normalForm_add]

/-- Append one variable occurrence to every term; used to prove representation coverage. -/
def multiplyVariable {k : ℕ} (i : ℕ) (t : Term k) : Term k :=
  { t with vars := i :: t.vars }

theorem interpret_multiplyVariable {k : ℕ} (i : ℕ) (xs : Code k) :
    interpret (xs.map (multiplyVariable i)) = fun r => interpret xs r * X i := by
  induction xs with
  | nil => funext r; simp
  | cons t ts ih =>
      funext r
      simp only [List.map_cons, interpret_cons, Pi.add_apply, ih]
      have ht : interpretTerm (multiplyVariable i t) r = interpretTerm t r * X i := by
        by_cases hr : r = t.label
        · simp [interpretTerm, multiplyVariable, labelled, hr, variablesPoly]
          ring
        · simp [interpretTerm, multiplyVariable, labelled, hr]
      rw [ht]
      ring

/-- Every polynomial in one actual component has a finite list representation. -/
theorem exists_code_labelled {k : ℕ} (r : Fin k) (p : LocalPoly) :
    ∃ xs : Code k, interpret xs = labelled r p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨[⟨r, c, []⟩], ?_⟩
      simp [interpretTerm, variablesPoly]
  | add p q hp hq =>
      obtain ⟨xs, hxs⟩ := hp
      obtain ⟨ys, hys⟩ := hq
      refine ⟨xs ++ ys, ?_⟩
      rw [interpret_append, hxs, hys]
      funext s
      by_cases hs : s = r <;> simp [labelled, hs]
  | mul_X p i hp =>
      obtain ⟨xs, hxs⟩ := hp
      refine ⟨xs.map (multiplyVariable i), ?_⟩
      rw [interpret_multiplyVariable, hxs]
      funext s
      by_cases hs : s = r <;> simp [labelled, hs]

/-- Coverage of all actual rational polynomial tuples, with no representation premise. -/
theorem exists_code {k : ℕ} (F : PeriodicLocal k) :
    ∃ xs : Code k, interpret xs = F := by
  classical
  have hsum : ∀ S : Finset (Fin k),
      ∃ xs : Code k, interpret xs = ∑ r ∈ S, labelled r (F r) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨[], by simp⟩
    | @insert r S hr ih =>
        obtain ⟨xs, hxs⟩ := exists_code_labelled r (F r)
        obtain ⟨ys, hys⟩ := ih
        refine ⟨xs ++ ys, ?_⟩
        rw [interpret_append, hxs, hys, Finset.sum_insert hr]
  obtain ⟨xs, hxs⟩ := hsum Finset.univ
  refine ⟨xs, hxs.trans ?_⟩
  funext s
  simp [labelled]

/-- Every actual input admits a finite executable computation of its normal form. -/
theorem exists_code_and_evaluation {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    ∃ xs : Code k, interpret xs = F ∧
      interpret (evaluateNormalForm B hk xs) = normalForm hB hk F := by
  obtain ⟨xs, hxs⟩ := exists_code F
  exact ⟨xs, hxs, by rw [evaluateNormalForm_correct hB hk, hxs]⟩

/-- A finite computation: `3 e₀ u₂ u₄` reduces to `12 e₂ u₀ u₂` in base two. -/
theorem evaluateNormalForm_example_base_two : evaluateNormalForm 2 (by decide : 0 < 3)
    [⟨⟨0, by decide⟩, 3, [2, 4]⟩] = [⟨⟨2, by decide⟩, 12, [0, 2]⟩] := by
  norm_num [evaluateNormalForm, reduceTerm, width, lowerTerm, nextLabel] <;> decide

/-- Constants disappear; a period wrap is computed as well. -/
theorem evaluateNormalForm_example_base_three : evaluateNormalForm 3 (by decide : 0 < 2)
    [⟨⟨1, by decide⟩, 7, []⟩, ⟨⟨1, by decide⟩, -2, [1, 1]⟩] =
    [⟨⟨0, by decide⟩, -6, [0, 0]⟩] := by
  norm_num [evaluateNormalForm, reduceTerm, width, lowerTerm, nextLabel] <;> decide

end PrimeGapNormality.Prime.CoreCyclic.Executable
