import PrimeGapNormality.Prime.CoreActualFrameRectangles
import PrimeGapNormality.Prime.CoreLinearMixtureScales
import PrimeGapNormality.Prime.FiniteRootMixSmallLowerException

/-! Actual fixed-dimensional rectangle bounds after good/high-count
aggregation, original missing-mass completion, and the prime-profile
Selberg/Euler-product limits. -/

namespace PrimeGapNormality.Prime.CoreActualFrameRectangleLimit

open Finset Filter MeasureTheory
open CoreActualFrameRectangles CoreCyclic.OnePoint.FiniteExterior
open scoped Classical BigOperators Topology ENNReal

noncomputable section

set_option maxHeartbeats 800000

private theorem sum_layers_filter (A : Finset ℕ) (μ : Finset ℕ → ℝ) (s : Finset ℕ) :
    (∑ n ∈ s, cardinalityLayer A μ n) =
      ∑ U ∈ A.powerset.filter (fun U => U.card ∈ s), μ U := by
  simp_rw [cardinalityLayer]
  rw [sum_sigma' (s := s) (t := fun n => A.powerset.filter (fun U => U.card = n))
    (f := fun _ U => μ U)]
  refine sum_bij' (fun p _ => p.2) (fun U _ => ⟨U.card, U⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hn := (mem_sigma.mp hp).1
    have hU := mem_filter.mp (mem_sigma.mp hp).2
    exact mem_filter.mpr ⟨hU.1, hU.2 ▸ hn⟩
  · intro U hU
    have hm := mem_filter.mp hU
    exact mem_sigma.mpr ⟨hm.2, mem_filter.mpr ⟨hm.1, rfl⟩⟩
  · intro p hp
    have hU := (mem_filter.mp (mem_sigma.mp hp).2).2
    simp [hU]
  · intro U _
    rfl
  · intro p _
    rfl

private theorem uniformMean_le_one (A : Finset ℕ) (m : ℕ) (hm : m ≤ A.card)
    (f : Finset ℕ → ℝ) (hf : ∀ U, f U ≤ 1) : auxFrame_uniformMean A m f ≤ 1 := by
  have hc : (0 : ℝ) < A.card.choose m := Nat.cast_pos.mpr (Nat.choose_pos hm)
  unfold auxFrame_uniformMean
  apply (div_le_one hc).2
  calc
    (∑ U ∈ A.powersetCard m, f U) ≤ ∑ _U ∈ A.powersetCard m, (1 : ℝ) :=
      sum_le_sum fun U _ => hf U
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one, card_powersetCard]

/-- Good layers use their proved bound; all other retained layers are
charged to the actual original high-count exception. -/
theorem fibre_le_good_add_high (S y L : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y)
    (f : Finset ℕ → ℝ) (hf : ∀ U, f U ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q)
    (hgood : ∀ n ∈ Icc L (presieveSurvivors S σ).card,
      (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y →
        auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f ≤ Q) :
    (∑ n ∈ Icc L (presieveSurvivors S σ).card,
      cardinalityLayer (presieveSurvivors S σ)
        (lateRootLaw S y (presieveSurvivors S σ)) n *
          auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f) ≤
      Q + coreFiniteRootMixUpperFibreMass S y σ := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let p := cardinalityLayer A μ
  let I := Icc L A.card
  let T : ℝ := 2 * (A.card : ℝ) * lateRetention S y
  have hμ := corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hp : ∀ n, 0 ≤ p n := fun n => sum_nonneg fun U hU => hμ.1 U (mem_filter.mp hU).1
  have hmass : (∑ n ∈ I, p n) ≤ 1 := by
    change (∑ n ∈ I, cardinalityLayer A μ n) ≤ 1
    rw [sum_layers_filter]
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun U hU _ => hμ.1 U hU)).trans_eq hμ.2.1
  have hhigh : (∑ n ∈ I, if T < (n : ℝ) then p n else 0) ≤
      coreFiniteRootMixUpperFibreMass S y σ := by
    change (∑ n ∈ I, if T < (n : ℝ) then cardinalityLayer A μ n else 0) ≤ _
    rw [← sum_filter, sum_layers_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro U hU
      have hm := mem_filter.mp hU
      refine mem_filter.mpr ⟨hm.1, ?_⟩
      simpa only [T, A, mul_assoc] using (mem_filter.mp hm.2).2
    · intro U hU _
      exact hμ.1 U (mem_filter.mp hU).1
  have hpoint : ∀ n ∈ I,
      p n * auxFrame_uniformMean A (n - 1) f ≤
        p n * Q + if T < (n : ℝ) then p n else 0 := by
    intro n hn
    by_cases h : T < (n : ℝ)
    · rw [if_pos h]
      have hle := mul_le_mul_of_nonneg_left
        (uniformMean_le_one A (n - 1) ((Nat.sub_le n 1).trans (Finset.mem_Icc.mp hn).2) f hf) (hp n)
      have hnn := mul_nonneg (hp n) hQ
      linarith
    · rw [if_neg h, add_zero]
      exact mul_le_mul_of_nonneg_left (hgood n hn (le_of_not_gt h)) (hp n)
  calc
    (∑ n ∈ I, p n * auxFrame_uniformMean A (n - 1) f) ≤
        ∑ n ∈ I, (p n * Q + if T < (n : ℝ) then p n else 0) := sum_le_sum hpoint
    _ = (∑ n ∈ I, p n) * Q + ∑ n ∈ I, if T < (n : ℝ) then p n else 0 := by
      rw [sum_add_distrib, sum_mul]
    _ ≤ 1 * Q + coreFiniteRootMixUpperFibreMass S y σ :=
      add_le_add (mul_le_mul_of_nonneg_right hmass hQ) hhigh
    _ = _ := by rw [one_mul]

theorem layer_le_good_add_high (S y L : ℕ) (hSy : S ≤ y)
    (f : Finset ℕ → ℝ) (hf : ∀ U, f U ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q)
    (hgood : ∀ σ : ResidueChoice S, ∀ n ∈ Icc L (presieveSurvivors S σ).card,
      (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) * lateRetention S y →
        auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f ≤ Q) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S y L F * f F) ≤
      Q + coreFiniteRootMixUpperRootMass S y := by
  rw [layer_expectation]
  have hc : (Fintype.card (ResidueChoice S) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ σ : ResidueChoice S, (Q + coreFiniteRootMixUpperFibreMass S y σ)) /
        (Fintype.card (ResidueChoice S) : ℝ) :=
      div_le_div_of_nonneg_right
        (sum_le_sum fun σ _ => fibre_le_good_add_high S y L σ hSy f hf hQ (hgood σ))
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_div]
      unfold coreFiniteRootMixUpperRootMass
      field_simp [hc]

theorem mixture_le_good_add_high (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) (hZ : 0 < mixZ X)
    (f : Finset ℕ → ℝ) (hf : ∀ U, f U ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q)
    (hgood : ∀ t ∈ mixScale X, ∀ σ : ResidueChoice S,
      ∀ n ∈ Icc L (presieveSurvivors S σ).card,
      (n : ℝ) ≤ 2 * ((presieveSurvivors S σ).card : ℝ) *
        lateRetention S (sieveCutoff (t : ℝ)) →
        auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f ≤ Q) :
    (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F * f F) ≤
      Q + (∑ t ∈ mixScale X, mixWeightV t *
        coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ))) / mixZ X := by
  unfold coreAuxiliaryFrameMass
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have heq : (∑ F ∈ (offsetWindow S).powerset,
      ∑ t ∈ mixScale X, mixWeightV t * coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F * f F) =
      ∑ t ∈ mixScale X, mixWeightV t *
        (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryLayerFrameMass S (sieveCutoff (t : ℝ)) L F * f F) := by
    rw [sum_comm]
    simp only [mul_sum, mul_assoc]
  simp_rw [Finset.sum_mul]
  rw [heq]
  calc
    _ ≤ (∑ t ∈ mixScale X, mixWeightV t *
        (Q + coreFiniteRootMixUpperRootMass S (sieveCutoff (t : ℝ)))) / mixZ X :=
      div_le_div_of_nonneg_right (sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
        (layer_le_good_add_high S _ L (hSy t ht) f hf hQ (hgood t ht))
        (mixWeightV_nonneg t)) hZ.le
    _ = _ := by
      simp_rw [mul_add]
      rw [sum_add_distrib, ← sum_mul, add_div]
      change mixZ X * Q / mixZ X + _ = _
      field_simp [hZ.ne']

/-! ### The missing atom is the already controlled original failure mass -/

theorem lowCountMass_eq_failure (S y L : ℕ) (hSy : S ≤ y) :
    coreAuxiliaryLayerLowCountMass S y L =
      Stopped.failureMass (offsetWindow S) (actualRootLaw y S) L := by
  rw [actualRootLaw_failureMass_eq_avg S y S L le_rfl hSy]
  unfold coreAuxiliaryLayerLowCountMass
  apply congrArg (fun x : ℝ => x / (Fintype.card (ResidueChoice S) : ℝ))
  apply sum_congr rfl
  intro σ _
  have hA : presieveSurvivors S σ ⊆ offsetWindow S := by
    simpa only [offsetWindow] using corePresieveSurvivors_subset_Icc S σ
  exact (lateRootLaw_failureMass_window_eq_fibre S y S hA L).symm

theorem missingMass_eq_failure (X S L : ℕ)
    (hSy : ∀ t ∈ mixScale X, S ≤ sieveCutoff (t : ℝ)) :
    coreAuxiliaryFrameMissingMass X S L =
      Stopped.failureMass (offsetWindow S) (finiteRootMix X S) L := by
  unfold coreAuxiliaryFrameMissingMass Stopped.failureMass finiteRootMix
  rw [← Finset.sum_div, sum_comm]
  apply congrArg (fun x : ℝ => x / mixZ X)
  apply sum_congr rfl
  intro t ht
  rw [← mul_sum]
  congr 1
  exact lowCountMass_eq_failure S _ L (hSy t ht)

theorem tendsto_missingMass {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun X => coreAuxiliaryFrameMissingMass X (ahlSmall_window κ X) (profileL κ X))
      atTop (𝓝 0) := by
  apply (tendsto_finiteRootMix_small_failureMass hκ).congr'
  filter_upwards [eventually_coreLinearScales_small_le_cutoff hκ] with X hcut
  simpa only [ahlSmall_omega, offsetWindow] using
    (missingMass_eq_failure X (ahlSmall_window κ X) (profileL κ X) hcut).symm

def rectangleError (κ : ℝ) (X : ℕ) : ℝ :=
  coreFiniteRootMixUpperException κ X +
    coreAuxiliaryFrameMissingMass X (ahlSmall_window κ X) (profileL κ X)

theorem tendsto_rectangleError {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (rectangleError κ) atTop (𝓝 0) := by
  change Tendsto (fun X => coreFiniteRootMixUpperException κ X +
    coreAuxiliaryFrameMissingMass X (ahlSmall_window κ X) (profileL κ X)) atTop (𝓝 0)
  simpa only [add_zero] using
    (tendsto_coreFiniteRootMixUpperException hκ).add (tendsto_missingMass hκ)

/-! ### Fixed-width padded Selberg caps -/

def rectangleRadius (δ G : ℝ) : ℕ :=
  selbergRadius (CoreSelberg.meshLength (min δ 1) G)

private theorem tendsto_log_div_self :
    Tendsto (fun G : ℝ => Real.log G / G) atTop (𝓝 0) := by
  simpa only [pow_one, one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)

/-- The integer padding and the ceiling in the candidate cap cost only a
fixed slack in the leading constant. The radius remains below `floor G`,
so the actual `S`-presieve supplies every required forbidden class. -/
theorem eventually_candidateCap_le {a b : ℝ} (hab : a < b) :
    ∀ᶠ G : ℝ in atTop,
      1 < G ∧ 1 ≤ rectangleRadius (b - a) G ∧
      rectangleRadius (b - a) G ≤ intervalLength (G * (b - a)) ∧
      rectangleRadius (b - a) G ≤ ⌊G⌋₊ ∧
      (candidateCap G a b (rectangleRadius (b - a) G) : ℝ) ≤
        8 * G / Real.log G * (b - a) := by
  let Δ := b - a
  let δ := min Δ 1
  have hΔ : 0 < Δ := sub_pos.2 hab
  have hδ : 0 < δ := lt_min hΔ zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδΔ : δ ≤ Δ := min_le_left _ _
  filter_upwards [CoreSelberg.eventually_mesh_density_le_three hδ hδ1,
    eventually_ge_atTop (2 / Δ), tendsto_log_div_self.eventually_le_const hΔ]
      with G hmesh hlarge hlogsmall
  obtain ⟨hG, hh, hR, hRh, hfloor, hmeshδ, hcap⟩ := hmesh
  let h := CoreSelberg.meshLength δ G
  let R := selbergRadius h
  let H := intervalLength (G * Δ)
  have hG0 : 0 < G := zero_lt_one.trans hG
  have hlog : 0 < Real.log G := Real.log_pos hG
  have hh0 : (0 : ℝ) < h :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hh)
  have hJ : selbergJR R ≠ 0 := (selbergJR_pos hR).ne'
  have hHh : h ≤ H := by
    have hreal : (h : ℝ) ≤ (H : ℝ) := by
      have hm : (h : ℝ) ≤ G * Δ := by
        have hmδ : (h : ℝ) ≤ δ * G := Nat.floor_le (mul_nonneg hδ.le hG0.le)
        nlinarith
      have hceil := Nat.le_ceil (G * Δ)
      dsimp only [H, intervalLength]
      push_cast
      linarith
    exact_mod_cast hreal
  have hHtwo : (H : ℝ) ≤ 2 * G * Δ := by
    have hGΔ : 2 ≤ G * Δ := (div_le_iff₀ hΔ).1 hlarge
    have hceil := (Nat.ceil_lt_add_one (mul_nonneg hG0.le hΔ.le)).le
    dsimp only [H, intervalLength]
    push_cast
    nlinarith
  have hscale : 1 ≤ (H : ℝ) / h := (le_div_iff₀ hh0).2
    (by simpa only [one_mul] using (Nat.cast_le.2 hHh : (h : ℝ) ≤ H))
  have hmeshcap : CoreSelberg.cellCap h R ≤
      (3 * G / Real.log G) * ((h : ℝ) / G) :=
    (div_le_iff₀ (div_pos hh0 hG0)).1 hcap
  have hpad : CoreSelberg.cellCap H R ≤ 3 * H / Real.log G := by
    calc
      CoreSelberg.cellCap H R = (H : ℝ) / selbergJR R + (R : ℝ) ^ 2 := rfl
      _ ≤ (H : ℝ) / selbergJR R + ((H : ℝ) / h) * (R : ℝ) ^ 2 :=
        add_le_add le_rfl (by nlinarith [sq_nonneg (R : ℝ)])
      _ = ((H : ℝ) / h) * CoreSelberg.cellCap h R := by
        unfold CoreSelberg.cellCap
        field_simp [hh0.ne', hJ]
        <;> ring
      _ ≤ ((H : ℝ) / h) * ((3 * G / Real.log G) * ((h : ℝ) / G)) :=
        mul_le_mul_of_nonneg_left hmeshcap (div_nonneg (Nat.cast_nonneg _) hh0.le)
      _ = 3 * H / Real.log G := by field_simp [hh0.ne', hG0.ne', hlog.ne'] <;> ring
  have hone : 1 ≤ G * Δ / Real.log G := by
    have hlg : Real.log G ≤ Δ * G := (div_le_iff₀ hG0).1 hlogsmall
    apply (le_div_iff₀ hlog).2
    nlinarith
  have hrounded : (candidateCap G a b R : ℝ) ≤ CoreSelberg.cellCap H R + 1 := by
    exact (Nat.ceil_lt_add_one (CoreSelberg.cellCap_nonneg H R hR)).le
  have hfinal : (candidateCap G a b R : ℝ) ≤ 8 * G / Real.log G * Δ := by
    have hmain : 3 * (H : ℝ) / Real.log G ≤ 6 * G * Δ / Real.log G :=
      div_le_div_of_nonneg_right (by nlinarith) hlog.le
    calc
      (candidateCap G a b R : ℝ) ≤ 3 * H / Real.log G + 1 :=
        hrounded.trans (add_le_add hpad le_rfl)
      _ ≤ 6 * G * Δ / Real.log G + G * Δ / Real.log G := add_le_add hmain hone
      _ ≤ 8 * G / Real.log G * Δ := by
        have hn : 0 ≤ G * Δ / Real.log G := div_nonneg (mul_nonneg hG0.le hΔ.le) hlog.le
        calc
          _ = 7 * (G * Δ / Real.log G) := by ring
          _ ≤ 8 * (G * Δ / Real.log G) := by nlinarith
          _ = _ := by ring
  exact ⟨hG, hR, hRh.trans hHh, hRh.trans hfloor, hfinal⟩

def rectangleConstant (w : ℕ) : ℝ :=
  ((96 : ℝ) / eulerProdLowerConst) ^ (2 * w + 1)

theorem rectangleConstant_pos (w : ℕ) : 0 < rectangleConstant w :=
  pow_pos (div_pos (by norm_num) eulerProdLowerConst_pos) _

/-- At the actual prime profile, every good presieve layer obeys one
fixed-dimensional rectangle estimate, uniformly in the varying interior
rank, original count, early root and final sieve cutoff. -/
theorem eventually_good_layer_rectangle {κ : ℝ} (hκ : 0 < κ)
    (w : ℕ) (a b : Fin (2 * w + 1) → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X : ℕ in atTop, ∀ t ∈ mixScale X, ∀ (j n : ℕ)
      (σ : ResidueChoice (ahlSmall_window κ X)),
      w + 1 ≤ j → j + w < profileL κ X → profileL κ X ≤ n →
      n ≤ (presieveSurvivors (ahlSmall_window κ X) σ).card →
      (n : ℝ) ≤ 2 * ((presieveSurvivors (ahlSmall_window κ X) σ).card : ℝ) *
        lateRetention (ahlSmall_window κ X) (sieveCutoff (t : ℝ)) →
      auxFrame_uniformMean (presieveSurvivors (ahlSmall_window κ X) σ) (n - 1)
        (fun F => if ∀ i, CoreActualFrameJoint.localFrame w j (windowG X) F i ∈
          Set.Ioo (a i) (b i) then 1 else 0) ≤
        rectangleConstant w * ∏ i, (b i - a i) := by
  have hcaps : ∀ᶠ G : ℝ in atTop, ∀ i : Fin (2 * w + 1),
      1 < G ∧ 1 ≤ rectangleRadius (b i - a i) G ∧
      rectangleRadius (b i - a i) G ≤ intervalLength (G * (b i - a i)) ∧
      rectangleRadius (b i - a i) G ≤ ⌊G⌋₊ ∧
      (candidateCap G (a i) (b i) (rectangleRadius (b i - a i) G) : ℝ) ≤
        8 * G / Real.log G * (b i - a i) :=
    Filter.eventually_all.2 fun i => eventually_candidateCap_le (hab i)
  filter_upwards [tendsto_windowG_atTop.eventually hcaps,
    eventually_coreLinearMixtureScales hκ,
    coreFRMUpper_eventually_lateRetention_le_quarter hκ] with X hcap hscale hquarter
  intro t ht j n σ hj hjL hLn hn hcount
  let S := ahlSmall_window κ X
  let y := sieveCutoff (t : ℝ)
  let G := windowG X
  let θ := lateRetention S y
  have hθ : 0 < θ := rootedEulerProdNat_pos (show 2 ≤ S from by have := hscale.2.2.1; omega)
  have hG0 : 0 < G := zero_lt_one.trans hscale.1
  let R : ℕ → ℕ := Function.extend (frameRank w j)
    (fun i : Fin (2 * w + 1) => rectangleRadius (b i - a i) G) (fun _ => 1)
  have hRi (i : Fin (2 * w + 1)) :
      R (frameRank w j i) = rectangleRadius (b i - a i) G :=
    (frameRank_injective w j hj).extend_apply _ _ i
  have hR : ∀ i : Fin (2 * w + 1), 1 ≤ R (frameRank w j i) ∧
      R (frameRank w j i) ≤ intervalLength (G * (b i - a i)) ∧ R (frameRank w j i) ≤ S := by
    intro i
    rw [hRi]
    exact ⟨(hcap i).2.1, (hcap i).2.2.1, (hcap i).2.2.2.1.trans hscale.2.2.2.1⟩
  have hfinite := actual_presieve_good_layer_rectangle_le S y (profileL κ X) n w j σ
    a b R hG0 hj hjL hLn hn hcount hθ (hquarter t ht) hR
  simp_rw [hRi] at hfinite
  have hcoord : ∀ i : Fin (2 * w + 1),
      (4 * θ) * (candidateCap G (a i) (b i) (rectangleRadius (b i - a i) G) : ℝ) ≤
        ((96 : ℝ) / eulerProdLowerConst) * (b i - a i) := by
    intro i
    have hret : θ * G / Real.log G ≤ (3 : ℝ) / eulerProdLowerConst :=
      (hscale.2.2.2.2 t ht).2.2.2.1
    calc
      _ ≤ (4 * θ) * (8 * G / Real.log G * (b i - a i)) :=
        mul_le_mul_of_nonneg_left (hcap i).2.2.2.2 (by positivity)
      _ = (32 * (θ * G / Real.log G)) * (b i - a i) := by ring
      _ ≤ (32 * ((3 : ℝ) / eulerProdLowerConst)) * (b i - a i) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hret (by norm_num))
          (sub_pos.2 (hab i)).le
      _ = _ := by ring
  have hprod := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin (2 * w + 1))))
    (fun i _ => mul_nonneg (by positivity : 0 ≤ 4 * θ) (Nat.cast_nonneg _))
    (fun i _ => hcoord i)
  have hprod' : (4 * θ) ^ (2 * w + 1) *
      (∏ i : Fin (2 * w + 1), (candidateCap G (a i) (b i) (rectangleRadius (b i - a i) G) : ℝ)) ≤
      rectangleConstant w * ∏ i, (b i - a i) := by
    simpa only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      rectangleConstant, mul_pow] using hprod
  exact hfinite.trans hprod'

/-! ### The actual completed joint law, in the exact Portmanteau interface -/

theorem frame_rectangle_mass_eq_integral {r : ℕ}
    (ν : ProbabilityMeasure (CoreJointFrameLimit.Joint r)) (a b : Fin r → ℝ) :
    (CoreJointFrameLimit.frameMarginal ν : Measure (Fin r → ℝ))
        (Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))) =
      ENNReal.ofReal (∫ z,
        if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i) then (1 : ℝ) else 0
        ∂(ν : Measure (CoreJointFrameLimit.Joint r))) := by
  let E : Set (Fin r → ℝ) := Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))
  have hE : MeasurableSet E :=
    (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).measurableSet
  have hpre : MeasurableSet (CoreJointFrameLimit.frame ⁻¹' E) :=
    hE.preimage CoreJointFrameLimit.continuous_frame.measurable
  have hint : (∫ z,
      if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i) then (1 : ℝ) else 0
      ∂(ν : Measure (CoreJointFrameLimit.Joint r))) =
      (ν : Measure (CoreJointFrameLimit.Joint r)).real (CoreJointFrameLimit.frame ⁻¹' E) := by
    simpa only [Set.indicator, Set.mem_preimage, E, Set.mem_pi, Set.mem_univ,
      forall_const, Pi.one_apply, Pi.ofNat_apply] using
      (integral_indicator_one (μ := (ν : Measure (CoreJointFrameLimit.Joint r))) hpre)
  have hmap : (CoreJointFrameLimit.frameMarginal ν : Measure (Fin r → ℝ)) E =
      (ν : Measure (CoreJointFrameLimit.Joint r)) (CoreJointFrameLimit.frame ⁻¹' E) :=
    ProbabilityMeasure.map_apply' ν CoreJointFrameLimit.continuous_frame.measurable.aemeasurable hE
  rw [hint, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact hmap

/-- The actual requested `hrect`: for each fixed open rectangle, uniformly
over every valid deterministic rank and every outer-phase map, the frame
marginal of the genuine completed joint PMF has the stated bound. The
only error is the explicit sum of existing original high/low exceptions.
No independence or spacing-distribution premise remains. -/
theorem eventually_jointLaw_rectangle_bound {κ : ℝ} (hκ : 0 < κ)
    (w : ℕ) (a b : Fin (2 * w + 1) → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᶠ X : ℕ in atTop, ∀ (j : ℕ) (θ : ℝ)
      (O : Finset ℕ → CoreActualFrameJoint.Circle)
      (hSy : ∀ t ∈ mixScale X, ahlSmall_window κ X ≤ sieveCutoff (t : ℝ))
      (hZ : 0 < mixZ X),
      w + 1 ≤ j → j + w < profileL κ X →
      (CoreJointFrameLimit.frameMarginal
        (CoreActualFrameJoint.jointLaw X (ahlSmall_window κ X) (profileL κ X) w j
          (windowG X) θ O hSy hZ) : Measure (Fin (2 * w + 1) → ℝ))
            (Set.pi Set.univ (fun i => Set.Ioo (a i) (b i))) ≤
        ENNReal.ofReal (rectangleConstant w * ∏ i, (b i - a i)) +
          ENNReal.ofReal (rectangleError κ X) := by
  filter_upwards [eventually_good_layer_rectangle hκ w a b hab] with X hgood
  intro j θ O hSy hZ hj hjL
  let S := ahlSmall_window κ X
  let L := profileL κ X
  let G := windowG X
  let f : Finset ℕ → ℝ := fun F =>
    if ∀ i, CoreActualFrameJoint.localFrame w j G F i ∈ Set.Ioo (a i) (b i) then 1 else 0
  let Q : ℝ := rectangleConstant w * ∏ i, (b i - a i)
  have hQ : 0 ≤ Q := mul_nonneg (rectangleConstant_pos w).le
    (Finset.prod_nonneg fun i _ => (sub_pos.2 (hab i)).le)
  have hf : ∀ F, f F ≤ 1 := by intro F; unfold f; split_ifs <;> norm_num
  have hm := mixture_le_good_add_high X S L hSy hZ f hf hQ
    (fun t ht σ n hn hc => hgood t ht j n σ hj hjL
      (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 hc)
  have hmissing : 0 ≤ coreAuxiliaryFrameMissingMass X S L :=
    coreAuxiliaryFrameMissingMass_nonneg X S L hSy hZ
  have hatom : coreAuxiliaryFrameMissingMass X S L *
      (if ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i) then 1 else 0) ≤
      coreAuxiliaryFrameMissingMass X S L := by
    split_ifs
    · simp only [mul_one]
      exact le_rfl
    · simpa only [mul_zero] using hmissing
  have hreal : (∫ z,
      if ∀ i, CoreJointFrameLimit.frame z i ∈ Set.Ioo (a i) (b i) then (1 : ℝ) else 0
      ∂(CoreActualFrameJoint.jointLaw X S L w j G θ O hSy hZ :
        Measure (CoreJointFrameLimit.Joint (2 * w + 1)))) ≤ Q + rectangleError κ X := by
    rw [joint_rectangle_integral]
    change (∑ F ∈ (offsetWindow S).powerset, coreAuxiliaryFrameMass X S L F * f F) +
      coreAuxiliaryFrameMissingMass X S L *
        (if ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i) then 1 else 0) ≤ _
    have hsum := add_le_add hm hatom
    exact hsum.trans_eq (by
      dsimp only [rectangleError, coreFiniteRootMixUpperException, S, L]
      ring)
  rw [frame_rectangle_mass_eq_integral]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le

end

end PrimeGapNormality.Prime.CoreActualFrameRectangleLimit
