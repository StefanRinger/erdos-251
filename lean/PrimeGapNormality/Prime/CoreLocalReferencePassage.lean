import PrimeGapNormality.Prime.CoreActualFrameLimit
import PrimeGapNormality.Prime.CoreCyclicTopCoefficientAE
import PrimeGapNormality.Prime.CoreShiftedPolynomialReference
import PrimeGapNormality.Prime.CoreWeakParameterIntegral
import PrimeGapNormality.Prime.CoreLocalModelPositive

/-!
# Fixed polynomial-image reference after actual joint extraction

The algebraic moving label is selected before any frame law or test.
The actual weak joint limit supplies its finite absolutely continuous
polynomial-image reference. Reciprocal scale is a deterministic Dirac
parameter; no independence or uniform integrability is introduced.
-/

namespace PrimeGapNormality.Prime.CoreLocalReferencePassage

open Filter MeasureTheory Set MvPolynomial
open CoreCyclic
open scoped Topology Polynomial ENNReal NNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev Circle := AddCircle (1 : ℝ)
abbrev Frame (w : ℕ) := Fin (2 * w + 1) → ℝ
abbrev Joint (w : ℕ) := CoreJointFrameLimit.Joint (2 * w + 1)

/-- Selection depends on the fixed tuple only, before the rank, law,
subsequence, test or cutoff is chosen. -/
def selectedLabel {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) : Fin k :=
  Classical.choose (exists_topDegree_movingDerivative_of_rooted hB hk w N hroot hN hw)

theorem selectedLabel_moving {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) :
    pderiv (-1) (homogeneousComponent (topDegree N)
      (OnePoint.action B hk w (selectedLabel hB hk w N hroot hN hw) N)) ≠ 0 :=
  Classical.choose_spec (exists_topDegree_movingDerivative_of_rooted hB hk w N hroot hN hw)

/-- Linear substitutions and shifts preserve the supplied tuple degree
bound; proved using actual homogeneous components. -/
theorem action_totalDegree_le (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ)
    (s : Fin k) (N : PeriodicLocal k) (d : ℕ)
    (hdeg : ∀ r, (N r).totalDegree ≤ d) :
    (OnePoint.action B hk w s N).totalDegree ≤ d := by
  let p := OnePoint.action B hk w s N
  by_contra hn
  have hlt : d < p.totalDegree := Nat.lt_of_not_ge hn
  have hp : p ≠ 0 := by
    intro hz
    have hzero : p.totalDegree = 0 := by rw [hz]; exact totalDegree_zero
    omega
  have hnonzero := OnePoint.homogeneousComponent_totalDegree_ne_zero p hp
  have hz : (fun r => homogeneousComponent p.totalDegree (N r)) = (0 : PeriodicLocal k) := by
    funext r
    exact homogeneousComponent_eq_zero p.totalDegree (N r) ((hdeg r).trans_lt hlt)
  apply hnonzero
  change homogeneousComponent p.totalDegree (OnePoint.action B hk w s N) = 0
  rw [OnePoint.homogeneousComponent_action, hz]
  simp [OnePoint.action, OnePoint.preAction, OnePoint.signedShift]

theorem action_totalDegree_le_topDegree (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (N : PeriodicLocal k) :
    (OnePoint.action B hk w s N).totalDegree ≤ topDegree N :=
  action_totalDegree_le B hk w s N _
    (fun r => Finset.le_sup (f := fun t : Fin k => (N t).totalDegree) (Finset.mem_univ r))

def zeroFamily (w d : ℕ) (p : OnePoint.SignedPoly) (Y : Frame w) : ℝ[X] :=
  CoreCyclicScaledSlot.normalizedActionFamily w d p (0, Y)

/-- A fixed nonzero formal top derivative, chosen before the law, is
nonconstant almost everywhere under any absolutely continuous frame law. -/
theorem zeroFamily_nonconstant_ae
    (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (hw : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ))
    (hp : pderiv (-1) (homogeneousComponent d p) ≠ 0)
    (ν : ProbabilityMeasure (Joint w))
    (hν : (CoreJointFrameLimit.frameMarginal ν : Measure (Frame w)) ≪ volume) :
    ∀ᵐ z ∂(ν : Measure (Joint w)), 0 < (zeroFamily w d p (CoreJointFrameLimit.frame z)).natDegree := by
  obtain ⟨n, hn⟩ := OnePoint.exists_exteriorDerivativeCoeff_ne_zero hp
  let q := OnePoint.exteriorDerivativeCoeff (homogeneousComponent d p) n
  have hq : ∀ i : OnePoint.ExteriorIndex, i ∈ q.vars →
      -(w : ℤ) - 1 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (w : ℤ) := by
    intro i hi
    exact hw i (OnePoint.vars_homogeneousComponent_subset d p
      (OnePoint.FiniteExterior.exteriorDerivativeCoeff_vars _ n hi))
  let P := OnePoint.FiniteExterior.realCoeff w q
  have hP : P ≠ 0 := OnePoint.FiniteExterior.realCoeff_ne_zero w q hq hn
  have hae := CoreMvPolynomialZeroSet.eval_ne_zero_ae_of_absolutelyContinuous
    P hP (CoreJointFrameLimit.frameMarginal ν : Measure (Frame w)) hν
  change ∀ᵐ Y ∂Measure.map CoreJointFrameLimit.frame (ν : Measure (Joint w)), eval Y P ≠ 0 at hae
  have hlift : ∀ᵐ z ∂(ν : Measure (Joint w)), eval (CoreJointFrameLimit.frame z) P ≠ 0 :=
    ae_of_ae_map CoreJointFrameLimit.continuous_frame.measurable.aemeasurable hae
  filter_upwards [hlift] with z hz
  have hvalue : eval (CoreJointFrameLimit.frame z) P =
      (zeroFamily w d p (CoreJointFrameLimit.frame z)).derivative.coeff n := by
    have heval := OnePoint.FiniteExterior.realCoeff_eval w q hq
      (CoreCyclicScaledSlot.finiteExteriorAssignment w (CoreJointFrameLimit.frame z))
    simp only [CoreCyclicScaledSlot.finiteExteriorAssignment_embedding] at heval
    have hcoeff := TopCoefficientAE.exteriorDerivativeCoeff_eval_eq_derivative_coeff
      (homogeneousComponent d p)
      (CoreCyclicScaledSlot.finiteExteriorAssignment w (CoreJointFrameLimit.frame z)) n
    rw [zeroFamily, CoreCyclicScaledSlot.normalizedActionFamily_zero w d p hd]
    exact heval.trans hcoeff
  have hder : (zeroFamily w d p (CoreJointFrameLimit.frame z)).derivative ≠ 0 := by
    intro hzero
    apply hz
    rw [hvalue, hzero, Polynomial.coeff_zero]
  exact Nat.pos_of_ne_zero (Polynomial.derivative_ne_zero.mp hder)

private theorem movingSpecialization_finite_eq (w : ℕ) (q : OnePoint.SignedPoly)
    (hw : ∀ i ∈ q.vars, -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ)) (Y : Frame w) :
    OnePoint.movingSpecialization q (CoreCyclicScaledSlot.finiteExteriorAssignment w Y) =
      OnePoint.movingSpecialization q (TopCoefficientAE.exteriorFrame w Y) := by
  apply Polynomial.funext
  intro v
  rw [OnePoint.movingSpecialization_eval, OnePoint.movingSpecialization_eval]
  apply eval₂_congr
  intro i m hi hm
  have hivar : i ∈ q.vars := (mem_vars_iff_mem_support i).2 ⟨m, mem_support_iff.2 hm, hi⟩
  by_cases him : i = -1
  · subst i
    simp only [OnePoint.movingAssignment_moving]
  · have hbox : (⟨i, him⟩ : OnePoint.ExteriorIndex) ∈
        Set.range (OnePoint.FiniteExterior.embedding w) :=
      (OnePoint.FiniteExterior.mem_range_embedding_iff w ⟨i, him⟩).2 (hw i hivar)
    obtain ⟨a, ha⟩ := hbox
    have hia : i = (OnePoint.FiniteExterior.embedding w a : ℤ) :=
      (congrArg Subtype.val ha).symm
    rw [hia]
    simp only [OnePoint.movingAssignment_exterior,
      CoreCyclicScaledSlot.finiteExteriorAssignment_embedding, TopCoefficientAE.exteriorFrame_embedding]

/-- Identification with the existing named top action; the two exterior
extensions agree on every variable that actually occurs. -/
theorem zeroFamily_action_eq_normalizedTopAction (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (N : PeriodicLocal k)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w) (Y : Frame w) :
    zeroFamily w (topDegree N) (OnePoint.action B hk w s N) Y =
      TopCoefficientAE.normalizedTopAction B hk w s N Y := by
  rw [zeroFamily, CoreCyclicScaledSlot.normalizedActionFamily_zero _ _ _
    (action_totalDegree_le_topDegree B hk w s N)]
  apply movingSpecialization_finite_eq
  intro i hi
  exact OnePoint.FiniteExterior.action_vars_bounds B hk w s N hw
    (OnePoint.vars_homogeneousComponent_subset _ _ hi)

theorem continuous_zeroFamily_eval (w d : ℕ) (p : OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) :
    Continuous (fun z : Joint w × ℝ => (zeroFamily w d p (CoreJointFrameLimit.frame z.1)).eval z.2) := by
  have harg : Continuous (fun z : Joint w × ℝ => (((0 : ℝ), CoreJointFrameLimit.frame z.1), z.2)) := by
    exact (continuous_const.prodMk
      (CoreJointFrameLimit.continuous_frame.comp continuous_fst)).prodMk continuous_snd
  exact (CoreCyclicScaledSlot.continuous_normalizedActionFamily_eval w d p hd).comp harg

def reference (w d : ℕ) (p : OnePoint.SignedPoly) (ν : ProbabilityMeasure (Joint w)) : Measure Circle :=
  CoreShiftedPolynomialReference.referenceMeasure (ν : Measure (Joint w))
    (CoreLocalModelPositive.jointWidth w) Prod.fst CoreJointFrameLimit.scale
    (fun z => zeroFamily w d p (CoreJointFrameLimit.frame z))

theorem reference_mass (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (ν : ProbabilityMeasure (Joint w)) :
    reference w d p ν Set.univ =
      ∫⁻ z, ENNReal.ofReal (CoreLocalModelPositive.jointWidth w z) ∂(ν : Measure (Joint w)) :=
  CoreShiftedPolynomialReference.referenceMeasure_mass _
    (CoreLocalModelPositive.continuous_jointWidth w).measurable _ _ _ measurable_fst
    CoreJointFrameLimit.continuous_scale.measurable (continuous_zeroFamily_eval w d p hd).measurable

theorem reference_isFinite (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (ν : ProbabilityMeasure (Joint w))
    (hfinite : (∫⁻ z, ENNReal.ofReal (CoreLocalModelPositive.jointWidth w z)
      ∂(ν : Measure (Joint w))) < ∞) : IsFiniteMeasure (reference w d p ν) :=
  ⟨by rw [reference_mass w d p hd ν]; exact hfinite⟩

theorem reference_absolutelyContinuous
    (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (hw : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ))
    (hp : pderiv (-1) (homogeneousComponent d p) ≠ 0)
    (ν : ProbabilityMeasure (Joint w))
    (hν : (CoreJointFrameLimit.frameMarginal ν : Measure (Frame w)) ≪ volume)
    (hscale : ∀ᵐ z ∂(ν : Measure (Joint w)), 1 ≤ CoreJointFrameLimit.scale z) :
    reference w d p ν ≪ volume := by
  apply CoreShiftedPolynomialReference.referenceMeasure_absolutelyContinuous _ _ _ _ _
    measurable_fst CoreJointFrameLimit.continuous_scale.measurable
    (continuous_zeroFamily_eval w d p hd).measurable
    (zeroFamily_nonconstant_ae w d p hd hw hp ν hν)
  exact hscale.mono fun z hz => (zero_lt_one.trans_le hz).ne'

theorem integral_reference (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (ν : ProbabilityMeasure (Joint w))
    (hW0 : ∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z)
    (hfinite : (∫⁻ z, ENNReal.ofReal (CoreLocalModelPositive.jointWidth w z)
      ∂(ν : Measure (Joint w))) < ∞) (f : Circle →ᵇ ℝ) :
    (∫ x, f x ∂reference w d p ν) =
      ∫ z, (∫ t in (0 : ℝ)..CoreLocalModelPositive.jointWidth w z,
        f (CoreLocalModelPositive.jointPhase w d p 0 z t)) ∂(ν : Measure (Joint w)) :=
  CoreShiftedPolynomialReference.integral_referenceMeasure _
    (CoreLocalModelPositive.continuous_jointWidth w).measurable hW0 hfinite
    _ _ _ measurable_fst CoreJointFrameLimit.continuous_scale.measurable
    (continuous_zeroFamily_eval w d p hd).measurable f

/-! ### Deterministic reciprocal scale in the compact test -/

theorem continuous_parameterPhase (w d : ℕ) (p : OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) :
    Continuous (fun q : (ℝ × Joint w) × ℝ =>
      CoreLocalModelPositive.jointPhase w d p q.1.1 q.1.2 q.2) := by
  have harg : Continuous (fun q : (ℝ × Joint w) × ℝ =>
      ((q.1.1, CoreJointFrameLimit.frame q.1.2), q.2)) := by
    exact (continuous_fst.fst.prodMk
      (CoreJointFrameLimit.continuous_frame.comp continuous_fst.snd)).prodMk continuous_snd
  have heval := (CoreCyclicScaledSlot.continuous_normalizedActionFamily_eval w d p hd).comp harg
  unfold CoreLocalModelPositive.jointPhase
  exact continuous_fst.snd.fst.add
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((CoreJointFrameLimit.continuous_scale.comp continuous_fst.snd).mul heval))

def parameterTest {R : ℝ} (hR : 0 ≤ R) (w d : ℕ) (p : OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) (f : Circle →ᵇ ℝ) : (ℝ × Joint w) →ᵇ ℝ :=
  CoreCompactFrameTest.boundedTest hR
    (fun q => CoreJointFrameLimit.frame q.2)
    (fun q => CoreLocalModelPositive.jointWidth w q.2)
    (fun q t => CoreLocalModelPositive.jointPhase w d p q.1 q.2 t)
    (CoreJointFrameLimit.continuous_frame.comp continuous_snd)
    ((CoreLocalModelPositive.continuous_jointWidth w).comp continuous_snd)
    (continuous_parameterPhase w d p hd) f

theorem parameterTest_apply {R : ℝ} (hR : 0 ≤ R) (w d : ℕ) (p : OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) (f : Circle →ᵇ ℝ) (γ : ℝ) (z : Joint w) :
    parameterTest hR w d p hd f (γ, z) =
      CoreLocalModelPositive.compactInsertionTest hR w d p hd γ f z := rfl

theorem compact_integrals_tendsto (w d : ℕ) (p : OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) (G : ℕ → ℝ) (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure (Joint w)) (ν : ProbabilityMeasure (Joint w))
    (hweak : Tendsto μ atTop (𝓝 ν)) {R : ℝ} (hR : 0 ≤ R) (f : Circle →ᵇ ℝ) :
    Tendsto (fun n => ∫ z,
      CoreLocalModelPositive.compactInsertionTest hR w d p hd (G n)⁻¹ f z
        ∂(μ n : Measure (Joint w))) atTop
      (𝓝 (∫ z, CoreLocalModelPositive.compactInsertionTest hR w d p hd 0 f z
        ∂(ν : Measure (Joint w)))) := by
  have hγ : Tendsto (fun n => (G n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hG
  simpa only [parameterTest_apply] using
    CoreWeakParameterIntegral.tendsto_integral_of_weak_and_parameter
      (fun n => (G n)⁻¹) 0 hγ μ ν hweak (parameterTest hR w d p hd f)

/-- Every nonnegative compact test is dominated by the same full reference
integral. The cutoff radius is not used in defining the reference. -/
theorem compact_integral_le_reference (w d : ℕ) (p : OnePoint.SignedPoly)
    (hd : p.totalDegree ≤ d) (ν : ProbabilityMeasure (Joint w))
    (hW0 : ∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z)
    (hWi : Integrable (CoreLocalModelPositive.jointWidth w) (ν : Measure (Joint w)))
    {R : ℝ} (hR : 0 ≤ R) (f : Circle →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∫ z, CoreLocalModelPositive.compactInsertionTest hR w d p hd 0 f z
      ∂(ν : Measure (Joint w))) ≤ ∫ x, f x ∂reference w d p ν := by
  let g : Joint w → ℝ := fun z =>
    ∫ t in (0 : ℝ)..CoreLocalModelPositive.jointWidth w z,
      f (CoreLocalModelPositive.jointPhase w d p 0 z t)
  have hgcont : Continuous g := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact f.continuous.comp (CoreLocalModelPositive.continuous_jointPhase_uncurry w d p hd 0)
    · exact CoreLocalModelPositive.continuous_jointWidth w
  have hg : Integrable g (ν : Measure (Joint w)) := by
    apply (hWi.norm.const_mul ‖f‖).mono' hgcont.measurable.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    simpa only [g, sub_zero, Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := CoreLocalModelPositive.jointWidth w z)
        (fun t _ => f.norm_coe_le_norm (CoreLocalModelPositive.jointPhase w d p 0 z t))
  have hpair : ∀ᵐ z ∂(ν : Measure (Joint w)),
      0 ≤ CoreLocalModelPositive.compactInsertionTest hR w d p hd 0 f z ∧
      CoreLocalModelPositive.compactInsertionTest hR w d p hd 0 f z ≤ g z := by
    filter_upwards [hW0] with z hz
    exact CoreCompactFrameTest.rawTest_nonneg_le_fullIntegral hR
      CoreJointFrameLimit.frame (CoreLocalModelPositive.jointWidth w)
      (CoreLocalModelPositive.jointPhase w d p 0)
      (CoreLocalModelPositive.continuous_jointPhase_uncurry w d p hd 0) f hf z hz
  have hfinite : (∫⁻ z, ENNReal.ofReal (CoreLocalModelPositive.jointWidth w z)
      ∂(ν : Measure (Joint w))) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hWi hW0]
    exact ENNReal.ofReal_lt_top
  rw [integral_reference w d p hd ν hW0 hfinite]
  exact integral_mono_of_nonneg (hpair.mono fun _ h => h.1) hg (hpair.mono fun _ h => h.2)

/-- Remove the original-law cutoff loss after the joint limit has been
fixed. The remaining premise is an explicit finite compact-test inequality,
not the desired reference domination or an assumed measure property. -/
theorem reference_domination_of_finite_compact_bounds
    (w d : ℕ) (p : OnePoint.SignedPoly) (hd : p.totalDegree ≤ d)
    (G : ℕ → ℝ) (hG : Tendsto G atTop atTop)
    (μ : ℕ → ProbabilityMeasure (Joint w)) (ν : ProbabilityMeasure (Joint w))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hW0 : ∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z)
    (hWi : Integrable (CoreLocalModelPositive.jointWidth w) (ν : Measure (Joint w)))
    (mean : ℕ → (Circle →ᵇ ℝ) → ℝ) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hfinite : ∀ (R : ℝ) (hR : 0 < R), ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0),
      LipschitzWith K f → (∀ x, 0 ≤ f x) → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, mean n f ≤
        A * (∫ z, CoreLocalModelPositive.compactInsertionTest hR.le w d p hd (G n)⁻¹ f z
          ∂(μ n : Measure (Joint w))) + D * ‖f‖ / R + η n * ‖f‖ + A * δ) :
    ∀ (f : Circle →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f → (∀ x, 0 ≤ f x) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        mean n f ≤ A * (∫ x, f x ∂reference w d p ν) + ε := by
  intro f K hK hf ε hε
  let R : ℝ := max 1 (4 * D * ‖f‖ / ε)
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  let δ : ℝ := ε / (4 * (A + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hAδ : A * δ ≤ ε / 4 := by
    have hA1 : A + 1 ≠ 0 := (show 0 < A + 1 from by linarith).ne'
    have heq : (4 * (A + 1)) * δ = ε := by dsimp only [δ]; field_simp [hA1]
    nlinarith
  have hcut : D * ‖f‖ / R ≤ ε / 4 := by
    apply (div_le_iff₀ hR).2
    have hle : 4 * D * ‖f‖ / ε ≤ R := le_max_right _ _
    have hmul := (div_le_iff₀ hε).1 hle
    nlinarith
  let I : ℝ := ∫ z, CoreLocalModelPositive.compactInsertionTest hR.le w d p hd 0 f z
    ∂(ν : Measure (Joint w))
  have hI : I ≤ ∫ x, f x ∂reference w d p ν :=
    compact_integral_le_reference w d p hd ν hW0 hWi hR.le f hf
  have hlim := compact_integrals_tendsto w d p hd G hG μ ν hweak hR.le f
  have herr : Tendsto (fun n => η n * ‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hη.mul_const ‖f‖
  filter_upwards [hfinite R hR f K hK hf δ hδ,
    hlim.eventually_le_const (by dsimp only [I]; linarith : I < I + δ),
    herr.eventually_le_const (by linarith : (0 : ℝ) < ε / 4)] with n hn htest herror
  have hscaled := mul_le_mul_of_nonneg_left
    (htest.trans (_root_.add_le_add hI le_rfl)) hA
  linarith

/-- The reference used above is supplied by a subsequence of the actual
auxiliary joint law. Its defining top-action label depends only on `N`.
The caller uses that fixed label in critical-rank selection before applying
the finite model bound; no label is selected from the limiting law. -/
theorem exists_actual_profile_reference
    {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (w : ℕ)
    (N : PeriodicLocal k) (hroot : drop hk N = 0) (hN : N ≠ 0)
    (hw : ∀ r i, i ∈ (N r).vars → i ≤ w)
    {κ : ℝ} (hκ : 0 < κ) (X : ℕ → ℕ) (hX : Tendsto X atTop atTop)
    (j : ℕ → ℕ) (θ : ℕ → ℝ) (O : ℕ → Finset ℕ → Circle)
    (hSy : ∀ n, ∀ t ∈ mixScale (X n), ahlSmall_window κ (X n) ≤ sieveCutoff (t : ℝ))
    (hZ : ∀ n, 0 < mixZ (X n)) (hG : ∀ n, 0 < windowG (X n))
    (hj : ∀ n, w + 1 ≤ j n) (hL : ∀ n, j n + w < profileL κ (X n))
    (hcal : ∀ n, ∀ t ∈ mixScale (X n),
      (eulerProdNat (sieveCutoff (t : ℝ)))⁻¹ / windowG (X n) ≤ 4)
    {C : ℝ} (hθ : ∀ n, θ n ∈ Set.Icc 1 C) :
    let p := OnePoint.action B hk w (selectedLabel hB hk w N hroot hN hw) N
    ∃ ν : ProbabilityMeasure (Joint w), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => CoreActualFrameJoint.jointLaw (X (φ n))
        (ahlSmall_window κ (X (φ n))) (profileL κ (X (φ n))) w (j (φ n))
        (windowG (X (φ n))) (θ (φ n)) (O (φ n)) (hSy (φ n)) (hZ (φ n)))
          atTop (𝓝 ν) ∧
      (∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z) ∧
      Integrable (CoreLocalModelPositive.jointWidth w) (ν : Measure (Joint w)) ∧
      IsFiniteMeasure (reference w (topDegree N) p ν) ∧
      reference w (topDegree N) p ν ≪ volume ∧
      reference w (topDegree N) p ν Set.univ ≤ ENNReal.ofReal 8 := by
  let s := selectedLabel hB hk w N hroot hN hw
  let p := OnePoint.action B hk w s N
  have hd : p.totalDegree ≤ topDegree N := action_totalDegree_le_topDegree B hk w s N
  have hp : pderiv (-1) (homogeneousComponent (topDegree N) p) ≠ 0 :=
    selectedLabel_moving hB hk w N hroot hN hw
  have hpw : ∀ i ∈ p.vars, -(w : ℤ) - 1 ≤ i ∧ i ≤ (w : ℤ) :=
    fun i hi => OnePoint.FiniteExterior.action_vars_bounds B hk w s N hw hi
  obtain ⟨ν, φ, hφ, hweak, hνac, hνnonneg, hνscale, hνint, hνbound⟩ :=
    CoreActualFrameJoint.exists_actual_profile_joint_limit hκ X hX w j θ O
      hSy hZ hG hj hL hcal hθ (CoreCyclicScaledSlot.centralIndex w)
  have hW0 : ∀ᵐ z ∂(ν : Measure (Joint w)), 0 ≤ CoreLocalModelPositive.jointWidth w z :=
    hνnonneg.mono fun z hz => hz (CoreCyclicScaledSlot.centralIndex w)
  have hWi : Integrable (CoreLocalModelPositive.jointWidth w) (ν : Measure (Joint w)) := hνint
  have hWbound : (∫ z, CoreLocalModelPositive.jointWidth w z ∂(ν : Measure (Joint w))) ≤ 8 := hνbound
  have hmass : (∫⁻ z, ENNReal.ofReal (CoreLocalModelPositive.jointWidth w z)
      ∂(ν : Measure (Joint w))) ≤ ENNReal.ofReal 8 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hWi hW0]
    exact ENNReal.ofReal_le_ofReal hWbound
  have hfinite := hmass.trans_lt ENNReal.ofReal_lt_top
  refine ⟨ν, φ, hφ, hweak, hW0, hWi,
    reference_isFinite w (topDegree N) p hd ν hfinite,
    reference_absolutelyContinuous w (topDegree N) p hd hpw hp ν hνac
      (hνscale.mono fun z hz => hz.1), ?_⟩
  rw [reference_mass w (topDegree N) p hd ν]
  exact hmass

end

end PrimeGapNormality.Prime.CoreLocalReferencePassage
