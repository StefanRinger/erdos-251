import PrimeGapNormality.Prime.CoreLocalRelations

/-!
# The canonical labelled gap-power components

For a period `k` and a degree budget `D`, this file packages the literal
family

`e_s X₀^(d+1)`,  `(s,d) : Fin k × Fin D`.

These are genuine rooted canonical tuples.  Their independence is proved by
extracting the coefficient of the corresponding labelled monomial, rather
than being supplied as a premise.  The resulting applications of
`CoreLocalRelations` therefore concern the literal prime-gap component
series, all on the common clock `B^k`.
-/

namespace PrimeGapNormality.Prime.CoreGapPowerComponents

open Finset MvPolynomial CoreCyclic
open scoped BigOperators Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The exponent represented by the second coordinate.  Thus `Fin D`
indexes the positive powers `1, ..., D`. -/
def gapPowerExponent {D : ℕ} (d : Fin D) : ℕ := d.1 + 1

/-- The literal canonical tuple `e_s X₀^(d+1)`. -/
def gapPowerTuple {k D : ℕ} (i : Fin k × Fin D) : PeriodicLocal k :=
  labelled i.1 ((X 0 : LocalPoly) ^ gapPowerExponent i.2)

theorem gapPowerExponent_pos {D : ℕ} (d : Fin D) :
    0 < gapPowerExponent d := by
  unfold gapPowerExponent
  omega

theorem gapPowerExponent_le {D : ℕ} (d : Fin D) :
    gapPowerExponent d ≤ D := by
  unfold gapPowerExponent
  omega

/-- Every member contains the root variable `X₀`, hence is killed by the
actual canonical drop map. -/
theorem gapPowerTuple_rooted {k D : ℕ} (hk : 0 < k) (i : Fin k × Fin D) :
    drop hk (gapPowerTuple i) = 0 := by
  change drop hk (labelled i.1 ((X 0 : LocalPoly) ^ gapPowerExponent i.2)) = 0
  rw [X_pow_eq_monomial]
  apply labelled_monomial_rooted hk
  simpa only [Finsupp.single_eq_same] using (gapPowerExponent_pos i.2).ne'

/-- The actual canonical normal form fixes each gap-power tuple. -/
theorem normalForm_gapPowerTuple {B k D : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (i : Fin k × Fin D) :
    normalForm hB hk (gapPowerTuple i) = gapPowerTuple i :=
  normalForm_of_rooted hB hk _ (gapPowerTuple_rooted hk i)

/-- Componentwise total-degree control for the literal tuple. -/
theorem gapPowerTuple_totalDegree_le {k D : ℕ} (i : Fin k × Fin D)
    (s : Fin k) :
    (gapPowerTuple i s).totalDegree ≤ D := by
  by_cases hs : s = i.1
  · simp only [gapPowerTuple, labelled, hs, if_pos, totalDegree_X_pow]
    exact gapPowerExponent_le i.2
  · simp only [gapPowerTuple, labelled, hs, if_false, totalDegree_zero, zero_le]

theorem topDegree_gapPowerTuple_le {k D : ℕ} (i : Fin k × Fin D) :
    topDegree (gapPowerTuple i) ≤ D := by
  unfold topDegree
  apply Finset.sup_le
  intro s hs
  exact gapPowerTuple_totalDegree_le i s

theorem topDegree_normalForm_gapPowerTuple_le {B k D : ℕ}
    (hB : 2 ≤ B) (hk : 0 < k) (i : Fin k × Fin D) :
    topDegree (normalForm hB hk (gapPowerTuple i)) ≤ D := by
  rw [normalForm_gapPowerTuple hB hk]
  exact topDegree_gapPowerTuple_le i

/-- Coefficient extraction separates both the cyclic label and the positive
power.  This is the concrete Kronecker formula used below. -/
theorem coeff_gapPowerTuple {k D : ℕ} (i j : Fin k × Fin D) :
    coeff (Finsupp.single 0 (gapPowerExponent i.2)) (gapPowerTuple j i.1) =
      if j = i then 1 else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp [gapPowerTuple, labelled, coeff_X_pow]
  · rw [if_neg hji]
    by_cases hs : i.1 = j.1
    · simp only [gapPowerTuple, labelled, hs, if_pos, coeff_X_pow]
      rw [if_neg]
      intro hm
      have he := congrArg (fun m : ℕ →₀ ℕ => m 0) hm
      simp only [Finsupp.single_eq_same] at he
      have hd : j.2 = i.2 := Fin.ext (by
        unfold gapPowerExponent at he
        omega)
      exact hji (Prod.ext hs.symm hd)
    · simp only [gapPowerTuple, labelled, hs, if_false, coeff_zero]

/-- The `kD` canonical labelled gap powers are genuinely linearly
independent over `ℚ`. -/
theorem gapPowerTuple_linearIndependent {k D : ℕ} :
    LinearIndependent ℚ (gapPowerTuple : Fin k × Fin D → PeriodicLocal k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq i
  let m : ℕ →₀ ℕ := Finsupp.single 0 (gapPowerExponent i.2)
  let select : PeriodicLocal k →ₗ[ℚ] ℚ :=
    (MvPolynomial.lcoeff ℚ m).comp
      (LinearMap.proj i.1 : PeriodicLocal k →ₗ[ℚ] LocalPoly)
  have hc := congrArg select hq
  simp only [map_sum, map_smul, map_zero] at hc
  have hcoeff (j : Fin k × Fin D) :
      select (gapPowerTuple j) = if j = i then 1 else 0 := by
    change coeff m (gapPowerTuple j i.1) = if j = i then 1 else 0
    exact coeff_gapPowerTuple i j
  simp_rw [hcoeff] at hc
  simpa using hc

/-- The displayed summand of the `(s,d)` component series. -/
def gapPowerSeriesTerm {B k D : ℕ} (hk : 0 < k) (phase : Fin k)
    (i : Fin k × Fin D) (n : ℕ) : ℝ :=
  (if phaseAt hk phase n = i.1 then (1 : ℝ) else 0) *
      (primeGap n : ℝ) ^ gapPowerExponent i.2 /
    (B : ℝ) ^ (n + 1)

/-- The literal prime-gap component advertised in the paper. -/
def gapPowerSeries (B : ℕ) {k D : ℕ} (hk : 0 < k) (phase : Fin k)
    (i : Fin k × Fin D) : ℝ :=
  ∑' n : ℕ, gapPowerSeriesTerm (B := B) hk phase i n

theorem localValue_gapPowerTuple {k D : ℕ} (hk : 0 < k) (phase : Fin k)
    (i : Fin k × Fin D) (n : ℕ) :
    localValue hk phase (fun q => (primeGap q : ℝ)) (gapPowerTuple i) n =
      (if phaseAt hk phase n = i.1 then (1 : ℝ) else 0) *
        (primeGap n : ℝ) ^ gapPowerExponent i.2 := by
  by_cases hs : phaseAt hk phase n = i.1
  · simp [localValue, gapPowerTuple, labelled, hs]
  · simp [localValue, gapPowerTuple, labelled, hs]

theorem fullSeries_gapPowerTuple_eq {B k D : ℕ} (hk : 0 < k)
    (phase : Fin k) (i : Fin k × Fin D) :
    coreCyclicFullSeries B hk phase (fun n => (primeGap n : ℝ))
        (gapPowerTuple i) = gapPowerSeries B hk phase i := by
  unfold coreCyclicFullSeries gapPowerSeries gapPowerSeriesTerm
  apply tsum_congr
  intro n
  rw [localValue_gapPowerTuple]

/-- Each displayed literal component series is absolutely summable. -/
theorem gapPowerSeries_summable {B k D : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) (i : Fin k × Fin D) :
    Summable (gapPowerSeriesTerm (B := B) hk phase i) := by
  change Summable (fun n : ℕ =>
    ((if phaseAt hk phase n = i.1 then (1 : ℝ) else 0) *
      (primeGap n : ℝ) ^ gapPowerExponent i.2) / (B : ℝ) ^ (n + 1))
  simpa only [localValue_gapPowerTuple] using
    (CoreLocalRelations.primeSeries_summable hB hk phase (gapPowerTuple i))

/-- Under the actual `D` input, all labelled powers have the common
`B^k` joint Weyl property. -/
theorem gapPower_jointWeyl_of_D {B k D : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (phase : Fin k) {kappa d0 c : ℝ}
    (hkappa : (D : ℝ) / Real.log (B : ℝ) ≤ kappa)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD kappa d0 c) :
    JointWeyl (fun _ : Fin k × Fin D => B ^ k)
      (fun i => gapPowerSeries B hk phase i) := by
  have hW := CoreLocalRelations.jointWeyl_of_independent_normalForms_of_D
    hB hk phase (gapPowerTuple : Fin k × Fin D → PeriodicLocal k)
    (topDegree_normalForm_gapPowerTuple_le hB hk)
    (by
      simpa only [normalForm_gapPowerTuple hB hk] using
        (gapPowerTuple_linearIndependent (k := k) (D := D)))
    hkappa hd0 hc hD
  simpa only [fullSeries_gapPowerTuple_eq] using hW

/-- Consequently `1` and all the literal component series are linearly
independent over `ℚ`, with no caller-supplied normal-form independence. -/
theorem gapPower_one_series_linearIndependent_of_D
    {B k D : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    {kappa d0 c : ℝ}
    (hkappa : (D : ℝ) / Real.log (B : ℝ) ≤ kappa)
    (hd0 : 0 < d0) (hc : 1 ≤ c) (hD : CoreLinearD kappa d0 c) :
    LinearIndependent ℚ (fun i : Option (Fin k × Fin D) => match i with
      | none => (1 : ℝ)
      | some i => gapPowerSeries B hk phase i) := by
  have hclock : 2 ≤ B ^ k := by
    have hsplit : k = k - 1 + 1 :=
      (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm
    rw [hsplit, pow_succ]
    exact hB.trans (Nat.le_mul_of_pos_left B (pow_pos (by omega : 0 < B) _))
  convert linearIndependent_one_jointWeyl hclock
    (gapPower_jointWeyl_of_D hB hk phase hkappa hd0 hc hD) using 1
  funext i
  cases i <;> rfl

/-- Kuperberg supplies the actual `D` input at the exact fixed profile
`D / log B`; hence every fixed positive `k,D` gets the joint conclusion. -/
theorem gapPower_jointWeyl_of_kuperberg
    {B k D : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hDpos : 0 < D)
    (phase : Fin k) (hK : KuperbergConj13) :
    JointWeyl (fun _ : Fin k × Fin D => B ^ k)
      (fun i => gapPowerSeries B hk phase i) := by
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hkappa : 0 < (D : ℝ) / Real.log (B : ℝ) :=
    div_pos (Nat.cast_pos.mpr hDpos) hlog
  exact gapPower_jointWeyl_of_D hB hk phase le_rfl (by norm_num) (by norm_num)
    (coreLinearD_of_kuperberg hK hkappa)

theorem gapPower_one_series_linearIndependent_of_kuperberg
    {B k D : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hDpos : 0 < D)
    (phase : Fin k) (hK : KuperbergConj13) :
    LinearIndependent ℚ (fun i : Option (Fin k × Fin D) => match i with
      | none => (1 : ℝ)
      | some i => gapPowerSeries B hk phase i) := by
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hkappa : 0 < (D : ℝ) / Real.log (B : ℝ) :=
    div_pos (Nat.cast_pos.mpr hDpos) hlog
  exact gapPower_one_series_linearIndependent_of_D hB hk phase le_rfl
    (by norm_num) (by norm_num) (coreLinearD_of_kuperberg hK hkappa)

end
end PrimeGapNormality.Prime.CoreGapPowerComponents
