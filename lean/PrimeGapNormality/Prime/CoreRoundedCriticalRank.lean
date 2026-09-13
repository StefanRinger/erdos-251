import PrimeGapNormality.Prime.CoreCyclicLabels
import PrimeGapNormality.Prime.CoreRoundedPowerScaling

/-!
# Critical ranks for a fixed real leading exponent

For `0 < a ≤ 1`, apply the accepted integer-degree selector to the new
scale `G^a`, degree one, and profile coefficient `κ/a`.  The identity

`(κ/a) log(G^a) = κ log G`

shows that its square-root profile is *exactly* the original canonical
profile, including at `κ = 1/log B`.  This yields a residue-constrained
rank with `G^a/B^(j+1) ∈ [1,B^k)`.

The algebraic label is selected before the eventual rank.  When `a<1`, a
nonzero leading column entry is enough.  At `a=1`, cyclicity supplies an
entry with `B b_s-b_{s+1}≠0`.
-/

namespace PrimeGapNormality.Prime.CoreRoundedCriticalRank

open Finset Filter
open CoreCyclic CoreLocalCriticalRank
open scoped Topology Classical

noncomputable section

/-- The exact label condition used by the real-power insertion action. -/
def UsableLeadingLabel {k : ℕ} (B : ℕ) (hk : 0 < k)
    (a : ℝ) (b : Fin k → ℤ) (s : Fin k) : Prop :=
  if a = 1 then (B : ℤ) * b s - b (cyclicSucc hk s) ≠ 0
  else b s ≠ 0

/-- A nonzero cyclic column has a nonvanishing linear insertion slope. -/
theorem exists_cyclicLinear_ne_zero
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (b : Fin k → ℤ) (hb : b ≠ 0) :
    ∃ s : Fin k, (B : ℤ) * b s - b (cyclicSucc hk s) ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hstep : ∀ s : Fin k, b (cyclicSucc hk s) = (B : ℤ) * b s := by
    intro s
    linarith [hnone s]
  have hiter : ∀ n : ℕ, ∀ s : Fin k,
      b ((cyclicSucc hk)^[n] s) = ((B : ℤ) ^ n) * b s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro s
        rw [Function.iterate_succ_apply', hstep, ih, pow_succ]
        ring
  have hBk : (1 : ℤ) < (B : ℤ) ^ k := by
    exact_mod_cast (one_lt_pow₀ (by omega : 1 < B) (Nat.ne_of_gt hk))
  apply hb
  funext s
  have hs := hiter k s
  rw [cyclicSucc_period hk] at hs
  have hzero : (((B : ℤ) ^ k) - 1) * b s = 0 := by
    calc
      (((B : ℤ) ^ k) - 1) * b s = (B : ℤ) ^ k * b s - b s := by ring
      _ = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (ne_of_gt hBk))

/-- A fixed usable label exists for every nonzero maximal-exponent column. -/
theorem exists_usableLeadingLabel
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    {a : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (b : Fin k → ℤ) (hb : b ≠ 0) :
    ∃ s : Fin k, UsableLeadingLabel B hk a b s := by
  rcases haOne.lt_or_eq with halt | rfl
  · have haNe : a ≠ 1 := ne_of_lt halt
    have hs : ∃ s : Fin k, b s ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      exact hb (funext hnone)
    obtain ⟨s, hs⟩ := hs
    exact ⟨s, by simpa only [UsableLeadingLabel, if_neg haNe] using hs⟩
  · obtain ⟨s, hs⟩ := exists_cyclicLinear_ne_zero hB hk b hb
    exact ⟨s, by simpa [UsableLeadingLabel] using hs⟩

private theorem realProfile_exact
    {a κ G : ℝ} (ha : 0 < a) (hG : 0 < G) :
    CoreLinearInsertion.linearProfileL (κ / a) (G ^ a) =
      CoreLinearInsertion.linearProfileL κ G := by
  unfold CoreLinearInsertion.linearProfileL
  rw [Real.log_rpow hG]
  have hcancel : κ / a * (a * Real.log G) = κ * Real.log G := by
    field_simp [ha.ne']
  rw [hcancel]

/-- Residue-constrained critical rank on an arbitrary real scale `G`. -/
theorem eventually_realCriticalRank
    {B k r : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (hr : r ∈ Icc 1 k) {a κ : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ G : ℝ in atTop, ∃ j : ℕ,
      1 ≤ j ∧ j < CoreLinearInsertion.linearProfileL κ G ∧
      Nat.ModEq k j r ∧
      1 ≤ G ^ a / (B : ℝ) ^ (j + 1) ∧
      G ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (Nat.one_lt_cast.mpr (by omega))
  have hκpos : 0 < κ := (div_pos zero_lt_one hlogB).trans_le hκ
  have hbudget : 1 / Real.log (B : ℝ) ≤ κ / a := by
    apply (le_div_iff₀ ha).2
    calc
      (1 / Real.log (B : ℝ)) * a ≤
          (1 / Real.log (B : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left haOne (div_nonneg zero_le_one hlogB.le)
      _ = 1 / Real.log (B : ℝ) := mul_one _
      _ ≤ κ := hκ
  have hraw := CoreLocalCriticalRank.eventually_critical_rank
    (d := 1) (κ := κ / a) hB (by omega : 1 ≤ k) (by omega : 1 ≤ 1) hr 0
      (by simpa only [Nat.cast_one] using hbudget)
  have hscale : Tendsto (fun G : ℝ ↦ G ^ a) atTop atTop :=
    _root_.tendsto_rpow_atTop ha
  have hpull := hscale.eventually hraw
  filter_upwards [hpull, eventually_gt_atTop (0 : ℝ)] with G hG hGpos
  obtain ⟨j, hj, hjL, hmod, hlo, hhi⟩ := hG
  refine ⟨j, by simpa only [zero_add] using hj,
    ?_, hmod, ?_, ?_⟩
  · rw [realProfile_exact ha hGpos] at hjL
    simpa only [Nat.add_zero] using hjL
  · simpa only [pow_one] using hlo
  · simpa only [pow_one] using hhi

/-- Physical-profile specialization.  The square-root reserve and its
endpoint equality are unchanged. -/
theorem eventually_realCriticalRank_profile
    {B k r : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (hr : r ∈ Icc 1 k) {a κ : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ) :
    ∀ᶠ X : ℕ in atTop, ∃ j : ℕ,
      1 ≤ j ∧ j < profileL κ X ∧ Nat.ModEq k j r ∧
      1 ≤ windowG X ^ a / (B : ℝ) ^ (j + 1) ∧
      windowG X ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
  have hG : Tendsto windowG atTop atTop :=
    tendsto_atTop_mono (fun X ↦ le_max_left (Real.log (X : ℝ)) (1 : ℝ))
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hraw := hG.eventually
    (eventually_realCriticalRank hB hk hr ha haOne hκ)
  filter_upwards [hraw] with X hX
  obtain ⟨j, hj, hjL, hmod, hlo, hhi⟩ := hX
  refine ⟨j, hj, ?_, hmod, hlo, hhi⟩
  simpa only [profileL, CoreLinearInsertion.linearProfileL] using hjL

/-- Select the algebraic label once, then select ranks with that label on
every sufficiently large physical scale. -/
theorem exists_usableLabel_eventually_rank
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (phase : Fin k)
    {a κ : ℝ} (ha : 0 < a) (haOne : a ≤ 1)
    (hκ : 1 / Real.log (B : ℝ) ≤ κ)
    (b : Fin k → ℤ) (hb : b ≠ 0) :
    ∃ s : Fin k, UsableLeadingLabel B hk a b s ∧
      ∀ᶠ X : ℕ in atTop, ∃ j : ℕ,
        1 ≤ j ∧ j < profileL κ X ∧ phaseAt hk phase (j - 1) = s ∧
        1 ≤ windowG X ^ a / (B : ℝ) ^ (j + 1) ∧
        windowG X ^ a / (B : ℝ) ^ (j + 1) < (B : ℝ) ^ k := by
  obtain ⟨s, hs⟩ := exists_usableLeadingLabel hB hk ha haOne b hb
  obtain ⟨r, hr, hlabel⟩ := exists_insertion_residue hk phase s
  refine ⟨s, hs, ?_⟩
  filter_upwards [eventually_realCriticalRank_profile hB hk hr ha haOne hκ]
    with X hX
  obtain ⟨j, hj, hjL, hmod, hlo, hhi⟩ := hX
  exact ⟨j, hj, hjL, hlabel j hj hmod, hlo, hhi⟩

end
end PrimeGapNormality.Prime.CoreRoundedCriticalRank
