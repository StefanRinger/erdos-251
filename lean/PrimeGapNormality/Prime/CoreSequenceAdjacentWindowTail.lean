import PrimeGapNormality.Prime.CoreSequenceSTMeanTail
import PrimeGapNormality.Prime.CoreSequenceResiduePassage
import PrimeGapNormality.Prime.PosMassScale

/-!
# Gap tails from two adjacent physical windows

For the current index window `(X,2X]`, summing all shifted gap tails
telescopes into one position mass at the right endpoint.  Split that position
mass at a depth `H`.  If the next physical window `(2X,4X]` contains the
profile plus `H` further points, the finite head stays below `4X`; a global
quadratic position bound makes the remaining geometric tail explicit.

This is a deterministic sequence lemma.  The adjacent-window density and
the exponential-smallness rate are isolated in a transparent calibration
predicate; no rough-number theorem is assumed here.
-/

namespace PrimeGapNormality.Prime.CoreSequenceAdjacentWindowTail

open Finset Filter CoreCyclic
open CoreSequenceSTMeanTail
open scoped BigOperators Topology

noncomputable section

/-- Geometric summability from an actual global quadratic position bound. -/
theorem sequence_div_pow_summable_of_quadratic
    {a : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2)
    {rho : ℝ} (hrho : 1 < rho) :
    Summable (fun n : ℕ ↦ (a n : ℝ) / rho ^ n) := by
  have hbase : Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ 2 / rho ^ (n + 1))) := by
    simpa only [Nat.zero_add] using summable_succ_sq_div_pow hrho 0
  have hdom : Summable (fun n : ℕ ↦
      (C * rho) * (((n + 1 : ℕ) : ℝ) ^ 2 / rho ^ (n + 1))) :=
    hbase.mul_left (C * rho)
  apply Summable.of_nonneg_of_le
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_lt_one.trans hrho).le _)
  · intro n
    have hden : 0 ≤ rho ^ n := pow_nonneg (zero_lt_one.trans hrho).le _
    calc
      (a n : ℝ) / rho ^ n ≤
          (C * ((n + 1 : ℕ) : ℝ) ^ 2) / rho ^ n :=
        div_le_div_of_nonneg_right (hquad n) hden
      _ = (C * rho) *
          (((n + 1 : ℕ) : ℝ) ^ 2 / rho ^ (n + 1)) := by
        field_simp [(zero_lt_one.trans hrho).ne'] <;> ring
  · exact hdom

/-- A quadratic position majorant gives a uniform quadratic bound for the
position mass beginning at any index. -/
theorem posMass_le_of_quadratic
    {a : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2)
    {rho : ℝ} (hrho : 1 < rho) (n : ℕ) :
    posMass rho (fun j ↦ (a j : ℝ)) n ≤
      C * posMassGeomCoeff rho * (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hterm : ∀ j : ℕ,
      (a (n + j) : ℝ) / rho ^ (j + 1) ≤
        C * ((((n + j + 1 : ℕ) : ℝ) ^ 2) / rho ^ (j + 1)) := by
    intro j
    have hden : 0 ≤ rho ^ (j + 1) :=
      pow_nonneg (zero_lt_one.trans hrho).le _
    have h := div_le_div_of_nonneg_right (hquad (n + j)) hden
    simpa only [mul_div_assoc] using h
  have hbase := summable_succ_sq_div_pow hrho n
  have hdom : Summable (fun j : ℕ ↦
      C * ((((n + j + 1 : ℕ) : ℝ) ^ 2) / rho ^ (j + 1))) :=
    hbase.mul_left C
  have hleft : Summable (fun j : ℕ ↦
      (a (n + j) : ℝ) / rho ^ (j + 1)) :=
    Summable.of_nonneg_of_le
      (fun j ↦ div_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (zero_lt_one.trans hrho).le _)) hterm hdom
  have hsum := hleft.tsum_le_tsum hterm hdom
  rw [hbase.tsum_mul_left] at hsum
  unfold posMass
  have hscale := mul_le_mul_of_nonneg_left
    (tsum_succ_sq_div_pow_le hrho n) hC
  exact hsum.trans (hscale.trans_eq (by ring))

/-- Exact adjacent-window head/tail estimate before dividing by the current
window cardinality. -/
theorem sum_seqGapTail_le_adjacent_head_add_deep
    {a : ℕ → ℕ} (ha : StrictMono a)
    {rho : ℝ} (hrho : 1 < rho) {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2)
    {X L H : ℕ} (hN : 0 < (seqWindow a X).card)
    (hnext : L + H < (seqWindow a (2 * X)).card) :
    (∑ n ∈ seqWindow a X, seqGapTail rho a (n + L)) ≤
      4 * (X : ℝ) / (rho - 1) +
        rho⁻¹ ^ H *
          (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2)) := by
  let u := seqCount a X
  let b := seqCount a (2 * X)
  let c := seqCount a (4 * X)
  have hub : u < b := by
    have hc := hN
    rw [CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha,
      Nat.card_Ico] at hc
    simpa only [u, b] using (show u < b by omega)
  have hbc : b + L + H < c := by
    have hn := hnext
    rw [CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha,
      Nat.card_Ico] at hn
    rw [show 2 * (2 * X) = 4 * X by omega] at hn
    dsimp only [b, c]
    omega
  have hreachNat : a (b + L + H) ≤ 4 * X :=
    (seqCount_lt_iff ha).mp hbc
  have hreach : (a (b + L + H) : ℝ) ≤ 4 * (X : ℝ) := by
    exact_mod_cast hreachNat
  have hindexNat : b + L + H + 1 ≤ 4 * X + 1 := by
    have hself := strictMono_le_id ha (b + L + H)
    omega
  have hindex : (((b + L + H + 1 : ℕ) : ℝ) ^ 2) ≤
      (((4 * X + 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast Nat.pow_le_pow_left hindexNat 2
  have hsm := sequence_div_pow_summable_of_quadratic hC hquad hrho
  let t : Finset ℕ := (seqWindow a X).image (fun n ↦ n + L)
  have hinj : Set.InjOn (fun n : ℕ ↦ n + L) (seqWindow a X : Set ℕ) := by
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have ht : t ⊆ range (b + L) := by
    intro i hi
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hi
    have hnI : n ∈ Ico u b := by
      rwa [← CoreSequenceResiduePassage.seqWindow_eq_Ico_seqCount ha]
    have hnlt : n < b := (mem_Ico.mp hnI).2
    exact mem_range.mpr (by omega)
  have hgap : (fun k : ℕ ↦ (seqGap a k : ℝ)) =
      fun k ↦ (a (k + 1) : ℝ) - (a k : ℝ) := by
    funext k
    unfold seqGap
    rw [Nat.cast_sub (ha.monotone (Nat.le_succ k))]
  have htail := sum_gapTail_le_posMass (n := 0) hrho
    (fun k ↦ (a k : ℝ)) hsm
    (fun i j hij ↦ Nat.cast_le.mpr (ha.monotone hij))
    (fun _ ↦ Nat.cast_nonneg _) t ht
  rw [← hgap] at htail
  simp only [Nat.zero_add] at htail
  have himage :
      (∑ i ∈ t, gapTail rho (fun k ↦ (seqGap a k : ℝ)) i) =
        ∑ n ∈ seqWindow a X,
          gapTail rho (fun k ↦ (seqGap a k : ℝ)) (n + L) :=
    sum_image hinj
  have hblock :
      (∑ n ∈ seqWindow a X, seqGapTail rho a (n + L)) ≤
        posMass rho (fun k ↦ (a k : ℝ)) (b + L) := by
    have := himage.symm.trans_le htail
    simpa only [seqGapTail, gapTail, Nat.zero_add] using this
  have hsplit := posMass_eq_trunc_add hrho (fun k ↦ (a k : ℝ))
    hsm (b + L) H
  have hheadRaw := posMassTrunc_le_of_monotone hrho
    (fun k ↦ (a k : ℝ))
    (fun i j hij ↦ Nat.cast_le.mpr (ha.monotone hij)) (b + L) H
  have hinv0 : 0 ≤ rho⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hrho).le
  have hinv1 : rho⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hrho.le
  have hinvPow : 0 ≤ rho⁻¹ ^ H := pow_nonneg hinv0 _
  have hinvPowOne : rho⁻¹ ^ H ≤ 1 := pow_le_one₀ hinv0 hinv1
  have hfactor0 : 0 ≤ (1 - rho⁻¹ ^ H) / (rho - 1) :=
    div_nonneg (sub_nonneg.mpr hinvPowOne) (sub_nonneg.mpr hrho.le)
  have hfactorLe : (1 - rho⁻¹ ^ H) / (rho - 1) ≤ 1 / (rho - 1) :=
    div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hrho.le)
  have hhead : posMassTrunc rho (fun k ↦ (a k : ℝ)) (b + L) H ≤
      4 * (X : ℝ) / (rho - 1) := by
    calc
      posMassTrunc rho (fun k ↦ (a k : ℝ)) (b + L) H ≤
          (a (b + L + H) : ℝ) *
            ((1 - rho⁻¹ ^ H) / (rho - 1)) := by
        simpa only [Nat.add_assoc] using hheadRaw
      _ ≤ (4 * (X : ℝ)) * ((1 - rho⁻¹ ^ H) / (rho - 1)) :=
        mul_le_mul_of_nonneg_right hreach hfactor0
      _ ≤ (4 * (X : ℝ)) * (1 / (rho - 1)) :=
        mul_le_mul_of_nonneg_left hfactorLe (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      _ = 4 * (X : ℝ) / (rho - 1) := by ring
  have hposTail := posMass_le_of_quadratic hC hquad hrho (b + L + H)
  have htailBound :
      rho⁻¹ ^ H * posMass rho (fun k ↦ (a k : ℝ)) (b + L + H) ≤
        rho⁻¹ ^ H *
          (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hinvPow
    exact hposTail.trans
      (mul_le_mul_of_nonneg_left hindex
        (mul_nonneg hC (posMassGeomCoeff_nonneg hrho)))
  rw [hsplit] at hblock
  exact hblock.trans ((_root_.add_le_add hhead htailBound).trans_eq (by ring))

/-- Quantitative hypotheses which make the exact adjacent-window bound an
`O(G)` mean.  The last field is only an explicit polynomial times a
geometric factor, not a tail estimate. -/
def AdjacentWindowTailCalibration
    (a : ℕ → ℕ) (rho : ℝ) (G : ℕ → ℝ) (H : ℕ → ℕ)
    (C : ℝ) : Prop :=
  ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧
    ∀ᶠ X : ℕ in atTop,
      0 < (seqWindow a X).card ∧
      (X : ℝ) / ((seqWindow a X).card : ℝ) ≤ D * G X ∧
      stdProfileL rho (G X) + H X < (seqWindow a (2 * X)).card ∧
      rho⁻¹ ^ H X *
          (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2)) ≤
        E * G X

/-- The adjacent-window calibration gives the bare actual mean-tail input. -/
theorem meanGapTailT_of_adjacentWindow
    {a : ℕ → ℕ} (ha : StrictMono a)
    {rho : ℝ} (hrho : 1 < rho) {G : ℕ → ℝ}
    {H : ℕ → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ n : ℕ, (a n : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2)
    (hcal : AdjacentWindowTailCalibration a rho G H C) :
    MeanGapTailT a rho G := by
  obtain ⟨D, E, hD, hE, hcal⟩ := hcal
  let K : ℝ := 4 * D / (rho - 1) + E
  have hden : 0 ≤ rho - 1 := sub_nonneg.mpr hrho.le
  have hK : 0 ≤ K := add_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hD) hden) hE
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcal] with X hX
  rcases hX with ⟨hN, hcount, hnext, hdeep⟩
  refine ⟨hN, ?_⟩
  have hsum := sum_seqGapTail_le_adjacent_head_add_deep ha hrho hC hquad
    hN hnext
  have hcard : (0 : ℝ) < (seqWindow a X).card := Nat.cast_pos.mpr hN
  have hcardOne : (1 : ℝ) ≤ (seqWindow a X).card := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne')
  let deep : ℝ := rho⁻¹ ^ H X *
    (C * posMassGeomCoeff rho * (((4 * X + 1 : ℕ) : ℝ) ^ 2))
  have hdeep0 : 0 ≤ deep := by
    dsimp only [deep]
    exact mul_nonneg
      (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hrho).le) _)
      (mul_nonneg (mul_nonneg hC (posMassGeomCoeff_nonneg hrho))
        (sq_nonneg _))
  have hdeepDiv : deep / ((seqWindow a X).card : ℝ) ≤ deep := by
    apply (div_le_iff₀ hcard).2
    exact le_mul_of_one_le_right hdeep0 hcardOne
  unfold windowAvgReal
  calc
    (∑ n ∈ seqWindow a X,
        seqGapTail rho a (n + stdProfileL rho (G X))) /
        ((seqWindow a X).card : ℝ) ≤
      (4 * (X : ℝ) / (rho - 1) + deep) /
        ((seqWindow a X).card : ℝ) :=
      div_le_div_of_nonneg_right (by simpa only [deep] using hsum) hcard.le
    _ = (4 / (rho - 1)) *
          ((X : ℝ) / ((seqWindow a X).card : ℝ)) +
        deep / ((seqWindow a X).card : ℝ) := by ring
    _ ≤ (4 / (rho - 1)) * (D * G X) + deep :=
      _root_.add_le_add
        (mul_le_mul_of_nonneg_left hcount (div_nonneg (by norm_num) hden))
        hdeepDiv
    _ ≤ (4 / (rho - 1)) * (D * G X) + E * G X :=
      _root_.add_le_add le_rfl (by simpa only [deep] using hdeep)
    _ = K * G X := by
      dsimp only [K]
      ring

end
end PrimeGapNormality.Prime.CoreSequenceAdjacentWindowTail
