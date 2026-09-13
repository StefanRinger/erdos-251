import PrimeGapNormality.BFree.Definitions
import PrimeGapNormality.BFree.Enumeration
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Positivity

/-!
# Product Haar space, coordinatewise rotation, survival set

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (Ω, U, A, Haar);
`lean/BFREE_SOURCE_LEDGER.md` C2.
Contract: C2 (ambient product; Haar(`A`) = `rho`)
Audit: GREEN (measure of survival; measure-preserving rotation)
-/

open Classical
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology MeasureTheory
open Filter Finset

namespace PrimeGapNormality.BFree

/-- Exclusion moduli are nonzero, so each `ZMod (F.d i)` is a finite ring.

Source: `lean/BFREE_SOURCE_LEDGER.md` encoding freeze.
Contract: API
Audit: GREEN -/
instance d_neZero (F : AdmissibleFamily) (i : ℕ) : NeZero (F.d i) :=
  ⟨d_ne_zero F i⟩

/-- Ambient residue space `Ω = ∏_i ℤ/d i ℤ`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: API
Audit: GREEN -/
abbrev ResidueSpace (F : AdmissibleFamily) := ∀ i : ℕ, ZMod (F.d i)

/-- Coordinatewise rotation `U ω = ω + 1`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: API
Audit: GREEN -/
def shift (F : AdmissibleFamily) : ResidueSpace F → ResidueSpace F :=
  fun ω i => ω i + 1

theorem shift_apply (F : AdmissibleFamily) (ω : ResidueSpace F) (i : ℕ) :
    shift F ω i = ω i + 1 :=
  rfl

/-- Survival set `A = {ω | ∀ i, ω i ≠ 0}`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: API
Audit: GREEN -/
def survival (F : AdmissibleFamily) : Set (ResidueSpace F) :=
  {ω | ∀ i, ω i ≠ 0}

/-- Uniform probability on one finite coordinate.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`Mathlib.Probability.UniformOn`.
Contract: API
Audit: GREEN -/
noncomputable def coordMeasure (F : AdmissibleFamily) (i : ℕ) :
    Measure (ZMod (F.d i)) :=
  uniformOn (Set.univ : Set (ZMod (F.d i)))

instance coordMeasure_isProbabilityMeasure (F : AdmissibleFamily) (i : ℕ) :
    IsProbabilityMeasure (coordMeasure F i) := by
  have : Finite (ZMod (F.d i)) := inferInstance
  have : Nonempty (ZMod (F.d i)) := ⟨0⟩
  exact instIsProbabilityMeasure_uniformOn_univ

/-- Product Haar probability `μ = ⨂_i uniform(ℤ/d i ℤ)`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`Mathlib.Probability.ProductMeasure`.
Contract: API
Audit: GREEN -/
noncomputable def productMeasure (F : AdmissibleFamily) :
    Measure (ResidueSpace F) :=
  Measure.infinitePi (coordMeasure F)

instance productMeasure_isProbabilityMeasure (F : AdmissibleFamily) :
    IsProbabilityMeasure (productMeasure F) := by
  unfold productMeasure
  infer_instance

theorem coordMeasure_singleton_zero (F : AdmissibleFamily) (i : ℕ) :
    coordMeasure F i {0} = (F.d i : ℝ≥0∞)⁻¹ := by
  rw [coordMeasure, uniformOn_univ, Measure.count_singleton, ZMod.card]
  simp [one_div]

/-- One-coordinate survival mass `1 - 1/d i`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem coordMeasure_compl_zero (F : AdmissibleFamily) (i : ℕ) :
    coordMeasure F i ({0}ᶜ) = ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹) := by
  have := coordMeasure_isProbabilityMeasure F i
  have hpos : (0 : ℝ) < F.d i := Nat.cast_pos.mpr (d_pos F i)
  rw [prob_compl_eq_one_sub (measurableSet_singleton 0), coordMeasure_singleton_zero]
  have hinv_nonneg : 0 ≤ (F.d i : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [ENNReal.ofReal_sub 1 hinv_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_inv_of_pos hpos,
    ENNReal.ofReal_natCast]

theorem coordMeasure_compl_zero' (F : AdmissibleFamily) (i : ℕ) :
    coordMeasure F i ({0}ᶜ) = ENNReal.ofReal (1 - (1 : ℝ) / F.d i) := by
  simpa [one_div] using coordMeasure_compl_zero F i

/-- Translation of a finite cyclic group preserves Haar.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem coordMeasure_map_add (F : AdmissibleFamily) (i : ℕ) (a : ZMod (F.d i)) :
    Measure.map (fun x => x + a) (coordMeasure F i) = coordMeasure F i := by
  have hmeas : Measurable fun x : ZMod (F.d i) => x + a := Measurable.of_discrete
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, coordMeasure, uniformOn_univ, uniformOn_univ]
  have hcount :
      Measure.count ((fun x : ZMod (F.d i) => x + a) ⁻¹' s) = Measure.count s := by
    rw [Measure.count_apply (hs.preimage hmeas), Measure.count_apply hs,
      Set.encard_preimage_of_bijective (AddGroup.addRight_bijective a)]
  exact congrArg (fun x => x / (Fintype.card (ZMod (F.d i)) : ℝ≥0∞)) hcount

theorem coordMeasure_map_add_one (F : AdmissibleFamily) (i : ℕ) :
    Measure.map (fun x => x + 1) (coordMeasure F i) = coordMeasure F i :=
  coordMeasure_map_add F i 1

/-- Survival is the infinite product of the punctured coordinates.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem survival_eq_univ_pi (F : AdmissibleFamily) :
    survival F = Set.univ.pi fun i => ({0} : Set (ZMod (F.d i)))ᶜ := by
  ext ω
  simp [survival]

/-- Finite-coordinate survival cylinders. Countable intersection recovers `A`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem survival_eq_iInter (F : AdmissibleFamily) :
    survival F =
      ⋂ k : ℕ, Set.pi (range k : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ := by
  rw [survival_eq_univ_pi]
  ext ω
  simp only [Set.mem_iInter, Set.mem_pi, Set.mem_univ, Set.mem_compl_iff, Set.mem_singleton_iff,
    mem_coe, mem_range, forall_true_left]
  constructor
  · intro h k i hi
    exact h i
  · intro h i
    exact h (i + 1) i (Nat.lt_succ_self i)

theorem survivalCylinder_measurable (F : AdmissibleFamily) (s : Finset ℕ) :
    MeasurableSet
      (Set.pi (s : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ) :=
  MeasurableSet.pi (Finset.countable_toSet s) fun i _ =>
    (measurableSet_singleton (0 : ZMod (F.d i))).compl

/-- Finite-cylinder mass is the Euler factor product.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`Mathlib.Probability.ProductMeasure` (`infinitePi_pi`).
Contract: C2
Audit: GREEN -/
theorem measure_survival_pi (F : AdmissibleFamily) (s : Finset ℕ) :
    productMeasure F (Set.pi (s : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ) =
      ∏ i ∈ s, ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹) := by
  rw [productMeasure, Measure.infinitePi_pi]
  · refine prod_congr rfl fun i _ => coordMeasure_compl_zero F i
  · intro i _
    exact (measurableSet_singleton (0 : ZMod (F.d i))).compl

theorem finiteRho_eq_prod (F : AdmissibleFamily) (k : ℕ) :
    finiteRho F k = ∏ i ∈ range k, (1 - (F.d i : ℝ)⁻¹) := by
  simp [finiteRho, one_div]

theorem measure_survival_range (F : AdmissibleFamily) (k : ℕ) :
    productMeasure F
        (Set.pi (range k : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ) =
      ENNReal.ofReal (finiteRho F k) := by
  rw [measure_survival_pi, finiteRho_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (survivalFactor_pos F i).le

theorem finiteRho_tendsto_rho (F : AdmissibleFamily) :
    Tendsto (fun k => finiteRho F k) atTop (𝓝 (rho F)) := by
  simp only [rho]
  exact ((multipliable_rho F).tendsto_prod_tprod_nat).congr fun k =>
    (finiteRho_eq_prod F k).symm

theorem survivalCylinder_antitone (F : AdmissibleFamily) :
    Antitone fun k : ℕ =>
      Set.pi (range k : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ := by
  intro a b hab
  refine Set.pi_mono' (fun _ _ => Set.Subset.rfl) ?_
  exact Finset.coe_subset.mpr (range_subset_range.mpr hab)

theorem shift_measurable (F : AdmissibleFamily) : Measurable (shift F) :=
  measurable_pi_lambda _ fun i =>
    (Measurable.of_discrete (f := fun x : ZMod (F.d i) => x + 1)).comp
      (measurable_pi_apply i)

/-- `U` preserves product Haar.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem shift_measurePreserving (F : AdmissibleFamily) :
    MeasurePreserving (shift F) (productMeasure F) (productMeasure F) where
  measurable := shift_measurable F
  map_eq := by
    have hmap :=
      Measure.infinitePi_map_pi (μ := coordMeasure F)
        (f := fun i (x : ZMod (F.d i)) => x + 1) fun i => Measurable.of_discrete
    have hshift :
        (fun (ω : ResidueSpace F) i => ω i + 1) = shift F :=
      rfl
    rw [productMeasure, ← hshift, hmap]
    congr 1
    funext i
    exact coordMeasure_map_add_one F i

theorem survival_measurable (F : AdmissibleFamily) : MeasurableSet (survival F) := by
  rw [survival_eq_univ_pi]
  exact MeasurableSet.univ_pi fun i =>
    (measurableSet_singleton (0 : ZMod (F.d i))).compl

/-- Product Haar of survival equals the Euler density `rho`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`lean/BFREE_SOURCE_LEDGER.md` C2.
Contract: C2 (Haar(`A`) identified with `rho`, not a free parameter)
Audit: GREEN

The identification uses finite cylinders `∏_{i<k} (1-1/d i) = finiteRho`, then
`k → ∞` by `multipliable_rho`. Survival is the countable intersection of those
cylinders. -/
theorem measure_survival (F : AdmissibleFamily) :
    productMeasure F (survival F) = ENNReal.ofReal (rho F) := by
  have := productMeasure_isProbabilityMeasure F
  let cyl : ℕ → Set (ResidueSpace F) := fun k =>
    Set.pi (range k : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ
  have hcyl : ∀ k, NullMeasurableSet (cyl k) (productMeasure F) := fun k =>
    (survivalCylinder_measurable F (range k)).nullMeasurableSet
  have hanti : Antitone cyl := survivalCylinder_antitone F
  have hinter : survival F = ⋂ k, cyl k := survival_eq_iInter F
  have hlim :
      Tendsto (fun k => productMeasure F (cyl k)) atTop
        (𝓝 (productMeasure F (survival F))) := by
    rw [hinter]
    exact tendsto_measure_iInter_atTop hcyl hanti ⟨0, measure_ne_top _ _⟩
  have hfin :
      Tendsto (fun k => productMeasure F (cyl k)) atTop
        (𝓝 (ENNReal.ofReal (rho F))) := by
    have hrho := ENNReal.tendsto_ofReal (finiteRho_tendsto_rho F)
    refine hrho.congr fun k => ?_
    exact (measure_survival_range F k).symm
  exact tendsto_nhds_unique hlim hfin

/-- Coordinatewise inverse rotation `U⁻¹ ω = ω - 1`.

Source: `lean/BFREE_PRODUCT_GAPS.md` §5.1; `lean/BFREE_SIGNATURES.md` ProductRotation leftovers.
Contract: C2 / Carry Wave A
Audit: GREEN -/
def shift_inv (F : AdmissibleFamily) : ResidueSpace F → ResidueSpace F :=
  fun ω i => ω i - 1

theorem shift_inv_apply (F : AdmissibleFamily) (ω : ResidueSpace F) (i : ℕ) :
    shift_inv F ω i = ω i - 1 :=
  rfl

theorem shift_leftInverse (F : AdmissibleFamily) :
    Function.LeftInverse (shift_inv F) (shift F) := by
  intro ω
  funext i
  simp [shift_inv, shift]

theorem shift_rightInverse (F : AdmissibleFamily) :
    Function.RightInverse (shift_inv F) (shift F) := by
  intro ω
  funext i
  simp [shift_inv, shift]

theorem shift_bijective (F : AdmissibleFamily) : Function.Bijective (shift F) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shift_inv F, shift_leftInverse F, shift_rightInverse F⟩

theorem shift_inv_measurable (F : AdmissibleFamily) : Measurable (shift_inv F) :=
  measurable_pi_lambda _ fun i =>
    (Measurable.of_discrete (f := fun x : ZMod (F.d i) => x - 1)).comp
      (measurable_pi_apply i)

/-- Inverse rotation preserves product Haar, as the inverse of a bijective
measure-preserving map. -/
theorem shift_inv_measurePreserving (F : AdmissibleFamily) :
    MeasurePreserving (shift_inv F) (productMeasure F) (productMeasure F) where
  measurable := shift_inv_measurable F
  map_eq := by
    nth_rw 1 [← (shift_measurePreserving F).map_eq]
    rw [Measure.map_map (shift_inv_measurable F) (shift_measurable F)]
    have : shift_inv F ∘ shift F = id := funext (shift_leftInverse F)
    rw [this, Measure.map_id]

theorem shift_iterate_apply (F : AdmissibleFamily) (n : ℕ) (ω : ResidueSpace F)
    (i : ℕ) : (shift F)^[n] ω i = ω i + n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift_apply, ih, Nat.cast_succ, add_assoc]

theorem shift_inv_iterate_apply (F : AdmissibleFamily) (n : ℕ) (ω : ResidueSpace F)
    (i : ℕ) : (shift_inv F)^[n] ω i = ω i - n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift_inv_apply, ih, sub_sub, Nat.cast_succ]

/-- Thin wrapper: evaluation of one coordinate pushes product Haar to that
coordinate's uniform measure.

Source: `lean/BFREE_MATHLIB_TOWERS.md` (`infinitePi_map_eval`);
`lean/BFREE_PRODUCT_GAPS.md` §5.2.
Contract: C2 / Carry Wave A
Audit: GREEN -/
theorem productMeasure_map_eval (F : AdmissibleFamily) (i : ℕ) :
    Measure.map (fun ω : ResidueSpace F => ω i) (productMeasure F) =
      coordMeasure F i := by
  unfold productMeasure
  exact Measure.infinitePi_map_eval (coordMeasure F) i

/-- Split off coordinate `iq`: `Ω ≃ (∏_{i ≠ iq} ℤ/d i ℤ) × ℤ/d_{iq} ℤ`.

Source: `lean/BFREE_PRODUCT_GAPS.md` §5.2;
`MeasurableEquiv.piEquivPiSubtypeProd`.
Contract: C2 / Carry Wave A
Audit: GREEN -/
noncomputable def residueSplit (F : AdmissibleFamily) (iq : ℕ) :
    ResidueSpace F ≃ᵐ
      ((i : {j : ℕ // j ≠ iq}) → ZMod (F.d i)) × ZMod (F.d iq) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun j : ℕ => ZMod (F.d j))
      (fun j => j = iq)).trans
    (((MeasurableEquiv.piUnique fun i : {j : ℕ // j = iq} => ZMod (F.d i)).prodCongr
        (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodComm)

theorem residueSplit_apply (F : AdmissibleFamily) (iq : ℕ) (ω : ResidueSpace F) :
    residueSplit F iq ω =
      (fun i : {j : ℕ // j ≠ iq} => ω (i : ℕ), ω iq) := by
  dsimp [residueSplit]
  simp only [MeasurableEquiv.coe_trans, Function.comp_apply]
  rfl

theorem residueSplit_symm_eval_ne (F : AdmissibleFamily) (iq : ℕ)
    (p : ((i : {j : ℕ // j ≠ iq}) → ZMod (F.d i)) × ZMod (F.d iq))
    (i : {j : ℕ // j ≠ iq}) :
    (residueSplit F iq).symm p (i : ℕ) = p.1 i := by
  have h := residueSplit_apply F iq ((residueSplit F iq).symm p)
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact (congrFun (congrArg Prod.fst h) i).symm

theorem residueSplit_symm_eval_eq (F : AdmissibleFamily) (iq : ℕ)
    (p : ((i : {j : ℕ // j ≠ iq}) → ZMod (F.d i)) × ZMod (F.d iq)) :
    (residueSplit F iq).symm p iq = p.2 := by
  have h := residueSplit_apply F iq ((residueSplit F iq).symm p)
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact (congrArg Prod.snd h).symm

/-- Product Haar splits as Haar on the complementary coordinates times the
`iq`-fibre.

Source: `lean/BFREE_PRODUCT_GAPS.md` §5.2.
Contract: C2 / Carry Wave A
Audit: GREEN -/
theorem productMeasure_eq_prod (F : AdmissibleFamily) (iq : ℕ) :
    Measure.map (residueSplit F iq) (productMeasure F) =
      (Measure.infinitePi fun i : {j : ℕ // j ≠ iq} => coordMeasure F i).prod
        (coordMeasure F iq) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, productMeasure]
  refine (Measure.eq_infinitePi (coordMeasure F) fun s t ht => ?_).symm
  rw [MeasurableEquiv.map_apply]
  let sRest : Finset {j : ℕ // j ≠ iq} := s.subtype fun j => j ≠ iq
  have hpre :
      (residueSplit F iq).symm ⁻¹' Set.pi (s : Set ℕ) t =
        Set.pi (sRest : Set _) (fun i : {j : ℕ // j ≠ iq} => t (i : ℕ)) ×ˢ
          (if iq ∈ s then t iq else (Set.univ : Set (ZMod (F.d iq)))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe]
    constructor
    · intro hp
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [← residueSplit_symm_eval_ne F iq p i]
        exact hp (i : ℕ) (mem_subtype.mp hi)
      · split_ifs with hiq
        · rw [← residueSplit_symm_eval_eq F iq p]
          exact hp iq hiq
        · exact Set.mem_univ _
    · intro hp i hi
      by_cases hieq : i = iq
      · rw [hieq, residueSplit_symm_eval_eq]
        have hif : (if iq ∈ s then t iq else Set.univ) = t iq := if_pos (hieq ▸ hi)
        rw [hif] at hp
        exact hp.2
      · have hi' : (⟨i, hieq⟩ : {j : ℕ // j ≠ iq}) ∈ sRest :=
          mem_subtype.mpr hi
        have hrestmem := hp.1 ⟨i, hieq⟩ hi'
        rw [residueSplit_symm_eval_ne F iq p ⟨i, hieq⟩]
        exact hrestmem
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi]
  · have hrest :
        (∏ i ∈ sRest, coordMeasure F (i : ℕ) (t (i : ℕ))) =
          ∏ i ∈ s with i ≠ iq, coordMeasure F i (t i) := by
      simpa [sRest] using
        (prod_subtype_eq_prod_filter (fun i : ℕ => coordMeasure F i (t i))
          (s := s) (p := fun j => j ≠ iq))
    have hfibre :
        coordMeasure F iq (if iq ∈ s then t iq else Set.univ) =
          if iq ∈ s then coordMeasure F iq (t iq) else 1 := by
      split_ifs <;> simp [measure_univ]
    rw [hrest, hfibre]
    have hmul :
        (∏ i ∈ s with i ≠ iq, coordMeasure F i (t i)) *
            (if iq ∈ s then coordMeasure F iq (t iq) else 1) =
          ∏ i ∈ s, coordMeasure F i (t i) := by
      have hnot :
          (∏ i ∈ s with ¬ i ≠ iq, coordMeasure F i (t i)) =
            if iq ∈ s then coordMeasure F iq (t iq) else 1 := by
        split_ifs with hiq
        · have hfil : (s.filter fun i => ¬ i ≠ iq) = {iq} := by
            ext j
            simp only [mem_filter, mem_singleton]
            constructor
            · intro hj
              exact not_ne_iff.mp hj.2
            · intro hj
              subst hj
              exact ⟨hiq, fun h => h rfl⟩
          rw [hfil, prod_singleton]
        · have hfil : (s.filter fun i => ¬ i ≠ iq) = ∅ := by
            ext j
            simp only [mem_filter, notMem_empty, iff_false, not_and]
            intro hj hnn
            exact hiq (not_ne_iff.mp hnn ▸ hj)
          rw [hfil, prod_empty]
      rw [← hnot, prod_filter_mul_prod_filter_not]
    exact hmul
  · intro i _
    exact ht (i : ℕ)

/-! ### Wave D: finite CRT cycle and product ergodicity

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`lean/BFREE_ERGODIC.md`.
Contract: Carry Wave D / atomlessness (not Theorem 3.3)
Audit: GREEN (finite CRT cycle + `finiteShift_ergodic`; infinite-product Lévy lift `shift_ergodic`)
-/

lemma iterate_add_one {n : ℕ} [NeZero n] (k : ℕ) (x : ZMod n) :
    (fun y => y + 1)^[k] x = x + k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Nat.cast_succ, add_assoc]

theorem zmod_add_one_orbit_univ {n : ℕ} [NeZero n] (x : ZMod n) :
    Set.range (fun k : Fin n => x + (k : ZMod n)) = Set.univ := by
  ext y
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  refine ⟨⟨(y - x).val, ZMod.val_lt _⟩, ?_⟩
  simp

theorem uniformOn_add_one_measurePreserving (n : ℕ) [NeZero n] :
    MeasurePreserving (fun x : ZMod n => x + 1)
      (uniformOn Set.univ) (uniformOn Set.univ) where
  measurable := Measurable.of_discrete
  map_eq := by
    have hmeas : Measurable fun x : ZMod n => x + 1 := Measurable.of_discrete
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply hmeas hs, uniformOn_univ, uniformOn_univ]
    have hcount :
        Measure.count ((fun x : ZMod n => x + 1) ⁻¹' s) = Measure.count s := by
      rw [Measure.count_apply (hs.preimage hmeas), Measure.count_apply hs,
        Set.encard_preimage_of_bijective (AddGroup.addRight_bijective (1 : ZMod n))]
    exact congrArg (fun x => x / (Fintype.card (ZMod n) : ℝ≥0∞)) hcount

theorem uniformOn_add_one_preErgodic (n : ℕ) [NeZero n] :
    PreErgodic (fun x : ZMod n => x + 1) (uniformOn Set.univ) where
  aeconst_set s _ hs := by
    rw [eventuallyConst_set']
    by_cases hne : s.Nonempty
    · right
      have hsu : s = Set.univ := by
        ext y
        simp only [Set.mem_univ, iff_true]
        obtain ⟨x, hx⟩ := hne
        have hy : y ∈ Set.range (fun k : Fin n => x + (k : ZMod n)) := by
          rw [zmod_add_one_orbit_univ]
          exact Set.mem_univ _
        obtain ⟨k, hk⟩ := hy
        have hiter : (fun z : ZMod n => z + 1)^[k.val] x = y := by
          rw [iterate_add_one]
          exact hk
        have heq : (fun z : ZMod n => z + 1)^[k.val] ⁻¹' s = s :=
          Function.IsFixedPt.preimage_iterate hs k.val
        have hmem : (fun z : ZMod n => z + 1)^[k.val] x ∈ s := by
          rw [← Set.mem_preimage, heq]
          exact hx
        rwa [hiter] at hmem
      rw [hsu]
      exact Filter.EventuallyEq.rfl
    · left
      have hs0 : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hs0]
      exact Filter.EventuallyEq.rfl

theorem uniformOn_add_one_ergodic (n : ℕ) [NeZero n] :
    Ergodic (fun x : ZMod n => x + 1) (uniformOn Set.univ) :=
  ⟨uniformOn_add_one_measurePreserving n, uniformOn_add_one_preErgodic n⟩

theorem coordMeasure_add_one_measurePreserving (F : AdmissibleFamily) (i : ℕ) :
    MeasurePreserving (fun x : ZMod (F.d i) => x + 1)
      (coordMeasure F i) (coordMeasure F i) :=
  ⟨Measurable.of_discrete, coordMeasure_map_add_one F i⟩

theorem coordMeasure_add_one_ergodic (F : AdmissibleFamily) (i : ℕ) :
    Ergodic (fun x : ZMod (F.d i) => x + 1) (coordMeasure F i) := by
  simpa [coordMeasure] using uniformOn_add_one_ergodic (F.d i)

instance partialPeriod_neZero (F : AdmissibleFamily) (k : ℕ) :
    NeZero (partialPeriod F k) :=
  ⟨(partialPeriod_pos F k).ne'⟩

theorem partialPeriod_eq_prod_fin (F : AdmissibleFamily) (k : ℕ) :
    partialPeriod F k = ∏ i : Fin k, F.d i.val := by
  simpa [partialPeriod] using (Fin.prod_univ_eq_prod_range (fun i => F.d i) k).symm

noncomputable def partialPeriod_chineseRemainder (F : AdmissibleFamily) (k : ℕ) :
    ZMod (partialPeriod F (k + 1)) ≃+* ZMod (partialPeriod F k) × ZMod (F.d k) :=
  (ZMod.ringEquivCongr (partialPeriod_succ F k)).trans
    (ZMod.chineseRemainder (coprime_partialPeriod F k))

theorem pairwise_coprime_fin (F : AdmissibleFamily) (k : ℕ) :
    Pairwise (Function.onFun Nat.Coprime fun i : Fin k => F.d i.val) :=
  fun _i _j hij => F.pairwise_coprime (Fin.val_injective.ne hij)

noncomputable def partialPeriod_piEquiv (F : AdmissibleFamily) (k : ℕ) :
    ZMod (partialPeriod F k) ≃+* ∀ i : Fin k, ZMod (F.d i.val) :=
  (ZMod.ringEquivCongr (partialPeriod_eq_prod_fin F k)).trans
    (ZMod.prodEquivPi (fun i : Fin k => F.d i.val) (pairwise_coprime_fin F k))

theorem partialPeriod_piEquiv_apply (F : AdmissibleFamily) (k : ℕ)
    (x : ZMod (partialPeriod F k)) (i : Fin k) :
    partialPeriod_piEquiv F k x i =
      ZMod.castHom (dvd_prod_of_mem (fun j : Fin k => F.d j.val) (mem_univ i))
        (ZMod (F.d i.val))
        (ZMod.ringEquivCongr (partialPeriod_eq_prod_fin F k) x) := by
  simp [partialPeriod_piEquiv, ZMod.prodEquivPi_apply]

theorem partialPeriod_piEquiv_add_one (F : AdmissibleFamily) (k : ℕ)
    (x : ZMod (partialPeriod F k)) (i : Fin k) :
    partialPeriod_piEquiv F k (x + 1) i = partialPeriod_piEquiv F k x i + 1 := by
  simp [partialPeriod_piEquiv_apply, map_add, map_one]

noncomputable def partialPeriod_measurableEquiv (F : AdmissibleFamily) (k : ℕ) :
    ZMod (partialPeriod F k) ≃ᵐ ∀ i : Fin k, ZMod (F.d i.val) where
  toEquiv := (partialPeriod_piEquiv F k).toEquiv
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

def finiteShift (F : AdmissibleFamily) (k : ℕ) :
    (∀ i : Fin k, ZMod (F.d i.val)) → ∀ i : Fin k, ZMod (F.d i.val) :=
  fun ω i => ω i + 1

theorem finiteShift_iterate_apply (F : AdmissibleFamily) (k n : ℕ)
    (ω : ∀ i : Fin k, ZMod (F.d i.val)) (i : Fin k) :
    (finiteShift F k)^[n] ω i = ω i + n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', finiteShift, ih, Nat.cast_succ, add_assoc]

theorem finiteShift_iterate_eq (F : AdmissibleFamily) (k n : ℕ)
    (ω : ∀ i : Fin k, ZMod (F.d i.val)) :
    (finiteShift F k)^[n] ω = fun i => ω i + n := by
  ext i
  exact finiteShift_iterate_apply F k n ω i

theorem finiteShift_conjugate (F : AdmissibleFamily) (k : ℕ)
    (x : ZMod (partialPeriod F k)) :
    finiteShift F k (partialPeriod_piEquiv F k x) =
      partialPeriod_piEquiv F k (x + 1) := by
  ext i
  simp [finiteShift, partialPeriod_piEquiv_add_one]

theorem finiteShift_iterate_conjugate (F : AdmissibleFamily) (k : ℕ) (n : ℕ)
    (x : ZMod (partialPeriod F k)) :
    (finiteShift F k)^[n] (partialPeriod_piEquiv F k x) =
      partialPeriod_piEquiv F k (x + n) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, finiteShift_conjugate, Nat.cast_succ, add_assoc]

theorem finiteShift_orbit_univ (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : Fin k, ZMod (F.d i.val)) :
    Set.range (fun n : Fin (partialPeriod F k) => (finiteShift F k)^[n.val] ω) =
      Set.univ := by
  ext τ
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  let e := partialPeriod_piEquiv F k
  let x := e.symm ω
  let y := e.symm τ
  refine ⟨⟨(y - x).val, ZMod.val_lt _⟩, ?_⟩
  have hx : e x = ω := e.apply_symm_apply ω
  have hy : e y = τ := e.apply_symm_apply τ
  have hiter :
      (finiteShift F k)^[(y - x).val] ω = e (x + (y - x).val) := by
    rw [← hx, finiteShift_iterate_conjugate]
  rw [hiter, ZMod.natCast_zmod_val, add_sub_cancel, hy]

theorem finiteShift_measurePreserving (F : AdmissibleFamily) (k : ℕ) :
    MeasurePreserving (finiteShift F k)
      (Measure.pi fun i : Fin k => coordMeasure F i.val)
      (Measure.pi fun i : Fin k => coordMeasure F i.val) where
  measurable := Measurable.of_discrete
  map_eq := by
    have hfun :
        finiteShift F k =
          fun (ω : ∀ i : Fin k, ZMod (F.d i.val)) (i : Fin k) => ω i + 1 :=
      rfl
    rw [hfun]
    have hmap :=
      Measure.pi_map_pi (μ := fun i : Fin k => coordMeasure F i.val)
        (f := fun _ (x : ZMod _) => x + 1) fun _ => Measurable.of_discrete.aemeasurable
    rw [hmap]
    congr 1
    funext i
    exact coordMeasure_map_add_one F i.val

theorem finiteShift_preErgodic (F : AdmissibleFamily) (k : ℕ) :
    PreErgodic (finiteShift F k)
      (Measure.pi fun i : Fin k => coordMeasure F i.val) where
  aeconst_set s _ hs := by
    rw [eventuallyConst_set']
    by_cases hne : s.Nonempty
    · right
      have hsu : s = Set.univ := by
        ext τ
        simp only [Set.mem_univ, iff_true]
        obtain ⟨ω, hω⟩ := hne
        have hτ :
            τ ∈ Set.range (fun n : Fin (partialPeriod F k) =>
              (finiteShift F k)^[n.val] ω) := by
          rw [finiteShift_orbit_univ]
          exact Set.mem_univ _
        obtain ⟨n, hn⟩ := hτ
        have heq : (finiteShift F k)^[n.val] ⁻¹' s = s :=
          Function.IsFixedPt.preimage_iterate hs n.val
        have hmem : (finiteShift F k)^[n.val] ω ∈ s := by
          rw [← Set.mem_preimage, heq]
          exact hω
        rwa [show (finiteShift F k)^[n.val] ω = τ from hn] at hmem
      rw [hsu]
      exact Filter.EventuallyEq.rfl
    · left
      have hs0 : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hs0]
      exact Filter.EventuallyEq.rfl

theorem finiteShift_ergodic (F : AdmissibleFamily) (k : ℕ) :
    Ergodic (finiteShift F k)
      (Measure.pi fun i : Fin k => coordMeasure F i.val) :=
  ⟨finiteShift_measurePreserving F k, finiteShift_preErgodic F k⟩

/-! ### Wave D: cylinder filtration and Lévy lift to `shift_ergodic`

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`lean/BFREE_ERGODIC.md` §§5–7.
Contract: Carry Wave D / atomlessness (not Theorem 3.3)
Audit: GREEN
-/

def rangeEquiv (k : ℕ) : Fin k ≃ { i : ℕ // i ∈ range k } :=
  Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp [mem_range]))

def finitePi_reindex (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : Fin k, ZMod (F.d i.val)) :
    ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val) :=
  fun i => ω ⟨i.val, mem_range.mp i.property⟩

def finitePi_reindex_symm (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) :
    ∀ i : Fin k, ZMod (F.d i.val) :=
  fun i => ω ⟨i.val, mem_range.mpr i.isLt⟩

noncomputable def finitePiCongr (F : AdmissibleFamily) (k : ℕ) :
    (∀ i : Fin k, ZMod (F.d i.val)) ≃ᵐ
      (∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) where
  toFun := finitePi_reindex F k
  invFun := finitePi_reindex_symm F k
  left_inv ω := funext fun i => by
    simp [finitePi_reindex, finitePi_reindex_symm]
  right_inv ω := funext fun j => by
    simp [finitePi_reindex, finitePi_reindex_symm]
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

def finiteShift_range (F : AdmissibleFamily) (k : ℕ) :
    (∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) →
      ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val) :=
  fun ω i => ω i + 1

theorem finiteShift_range_apply (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val))
    (i : { j : ℕ // j ∈ range k }) :
    finiteShift_range F k ω i = ω i + 1 :=
  rfl

theorem finiteShift_range_measurable (F : AdmissibleFamily) (k : ℕ) :
    Measurable (finiteShift_range F k) :=
  measurable_pi_lambda _ fun i =>
    (Measurable.of_discrete (f := fun x : ZMod (F.d i.val) => x + 1)).comp
      (measurable_pi_apply i)

theorem finiteShift_range_semiconj (F : AdmissibleFamily) (k : ℕ) :
    Function.Semiconj (finitePiCongr F k) (finiteShift F k) (finiteShift_range F k) := by
  intro ω
  ext j
  simp [finitePiCongr, finitePi_reindex, finiteShift, finiteShift_range,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]

theorem coordMeasure_singleton (F : AdmissibleFamily) (i : ℕ) (a : ZMod (F.d i)) :
    coordMeasure F i {a} = (F.d i : ℝ≥0∞)⁻¹ := by
  rw [coordMeasure, uniformOn_univ, Measure.count_singleton, ZMod.card]
  simp [one_div]

theorem finitePiCongr_measurePreserving (F : AdmissibleFamily) (k : ℕ) :
    MeasurePreserving (finitePiCongr F k)
      (Measure.pi fun i : Fin k => coordMeasure F i.val)
      (Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val) where
  measurable := (finitePiCongr F k).measurable
  map_eq := by
    refine Measure.ext_iff_singleton.mpr fun τ => ?_
    have hpre :
        ⇑(finitePiCongr F k) ⁻¹' {τ} = {(finitePiCongr F k).symm τ} := by
      ext ω
      simp [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.eq_symm_apply]
    rw [MeasurableEquiv.map_apply, hpre]
    rw [Measure.pi_singleton, Measure.pi_singleton]
    simp only [coordMeasure_singleton]
    exact Fintype.prod_equiv (rangeEquiv k)
      (fun i => (F.d i.val : ℝ≥0∞)⁻¹)
      (fun i => (F.d i.val : ℝ≥0∞)⁻¹)
      (fun i => by simp [rangeEquiv])

theorem finiteShift_range_ergodic (F : AdmissibleFamily) (k : ℕ) :
    Ergodic (finiteShift_range F k)
      (Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val) :=
  (finitePiCongr_measurePreserving F k).ergodic_of_ergodic_semiconj
    (finiteShift_ergodic F k) (finiteShift_range_measurable F k)
    (finiteShift_range_semiconj F k)

theorem restrict_comp_shift (F : AdmissibleFamily) (k : ℕ) :
    (range k).restrict ∘ shift F = finiteShift_range F k ∘ (range k).restrict := by
  ext ω i
  simp [finiteShift_range, shift]

theorem restrict_comp_shift_inv (F : AdmissibleFamily) (k : ℕ) :
    (range k).restrict ∘ shift_inv F =
      (fun ω i => ω i - 1) ∘ (range k).restrict := by
  ext ω i
  simp [shift_inv]

theorem finitePi_singleton (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) :
    (Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val) {ω} =
      ∏ i : { j : ℕ // j ∈ range k }, (F.d i.val : ℝ≥0∞)⁻¹ := by
  rw [Measure.pi_singleton]
  exact Fintype.prod_congr _ _ fun i => coordMeasure_singleton F i.val (ω i)

theorem finitePi_singleton_pos (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) :
    0 < (Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val) {ω} := by
  rw [finitePi_singleton, pos_iff_ne_zero, ne_eq, Finset.prod_eq_zero_iff]
  push Not
  intro i _
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem finitePi_ae_eq {F : AdmissibleFamily} {k : ℕ}
    {f g : (∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) → ℝ}
    (h : f =ᵐ[Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val] g) :
    f = g := by
  funext ω
  by_contra hne
  have hnull :
      (Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val)
        {x | f x ≠ g x} = 0 :=
    ae_iff.mp h
  exact (finitePi_singleton_pos F k ω).ne'
    (measure_mono_null (Set.singleton_subset_iff.mpr hne) hnull)

noncomputable def coordFiltration (F : AdmissibleFamily) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ResidueSpace F)) where
  seq k := Filtration.piFinset (X := fun i : ℕ => ZMod (F.d i)) (range k)
  mono' _ _ hab :=
    (Filtration.piFinset (X := fun i : ℕ => ZMod (F.d i))).mono (range_subset_range.mpr hab)
  le' k := (Filtration.piFinset (X := fun i : ℕ => ZMod (F.d i))).le (range k)

theorem coordFiltration_eq_comap (F : AdmissibleFamily) (k : ℕ) :
    coordFiltration F k =
      MeasurableSpace.comap (range k).restrict
        (MeasurableSpace.pi : MeasurableSpace
          (∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val))) :=
  rfl

theorem coordFiltration_iSup (F : AdmissibleFamily) :
    ⨆ k, coordFiltration F k =
      (MeasurableSpace.pi : MeasurableSpace (ResidueSpace F)) := by
  refine le_antisymm (iSup_le fun k => (coordFiltration F).le k) ?_
  change
    (⨆ i, (inferInstance : MeasurableSpace (ZMod (F.d i))).comap
        fun ω : ResidueSpace F => ω i) ≤
      ⨆ k, coordFiltration F k
  refine iSup_le fun i => ?_
  have hi : i ∈ range (i + 1) := mem_range.mpr (Nat.lt_succ_self i)
  have hle :
      (inferInstance : MeasurableSpace (ZMod (F.d i))).comap
          (fun ω : ResidueSpace F => ω i) ≤
        coordFiltration F (i + 1) := by
    have hfun :
        (fun ω : ResidueSpace F => ω i) =
          (fun x : ∀ j : { a : ℕ // a ∈ range (i + 1) }, ZMod (F.d j.val) =>
              x ⟨i, hi⟩) ∘
            (range (i + 1)).restrict :=
      rfl
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.comap_le (measurable_pi_apply _))
  exact hle.trans (le_iSup (fun k => coordFiltration F k) (i + 1))

theorem shift_measurable_coordFiltration (F : AdmissibleFamily) (k : ℕ) :
    @Measurable (ResidueSpace F) (ResidueSpace F)
      (coordFiltration F k) (coordFiltration F k) (shift F) := by
  rw [measurable_iff_comap_le, coordFiltration_eq_comap, MeasurableSpace.comap_comp,
    restrict_comp_shift, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (Measurable.comap_le (finiteShift_range_measurable F k))

theorem shift_inv_measurable_coordFiltration (F : AdmissibleFamily) (k : ℕ) :
    @Measurable (ResidueSpace F) (ResidueSpace F)
      (coordFiltration F k) (coordFiltration F k) (shift_inv F) := by
  rw [measurable_iff_comap_le, coordFiltration_eq_comap, MeasurableSpace.comap_comp,
    restrict_comp_shift_inv, ← MeasurableSpace.comap_comp]
  have hmeas : Measurable fun ω : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val) =>
      fun i => ω i - 1 :=
    measurable_pi_lambda _ fun i =>
      (Measurable.of_discrete (f := fun x : ZMod (F.d i.val) => x - 1)).comp
        (measurable_pi_apply i)
  exact MeasurableSpace.comap_mono (Measurable.comap_le hmeas)

theorem shift_preimage_coordFiltration (F : AdmissibleFamily) (k : ℕ)
    {s : Set (ResidueSpace F)} (hs : MeasurableSet[coordFiltration F k] s) :
    MeasurableSet[coordFiltration F k] (shift F ⁻¹' s) :=
  (shift_measurable_coordFiltration F k) hs

theorem shift_inv_preimage_coordFiltration (F : AdmissibleFamily) (k : ℕ)
    {s : Set (ResidueSpace F)} (hs : MeasurableSet[coordFiltration F k] s) :
    MeasurableSet[coordFiltration F k] (shift_inv F ⁻¹' s) :=
  (shift_inv_measurable_coordFiltration F k) hs

theorem restrict_measurePreserving (F : AdmissibleFamily) (k : ℕ) :
    MeasurePreserving (range k).restrict (productMeasure F)
      (Measure.pi fun i : { j : ℕ // j ∈ range k } => coordMeasure F i.val) where
  measurable := Finset.measurable_restrict _
  map_eq := by
    simpa [productMeasure] using
      Measure.infinitePi_map_restrict (μ := coordMeasure F) (I := range k)

theorem setIntegral_comp_shift (F : AdmissibleFamily) {φ : ResidueSpace F → ℝ}
    {t : Set (ResidueSpace F)} (hφ : Integrable φ (productMeasure F))
    (ht : MeasurableSet t) :
    ∫ x in shift F ⁻¹' t, φ (shift F x) ∂productMeasure F =
      ∫ y in t, φ y ∂productMeasure F := by
  have hmp := shift_measurePreserving F
  have hφ' : AEStronglyMeasurable φ (Measure.map (shift F) (productMeasure F)) := by
    rw [hmp.map_eq]
    exact hφ.aestronglyMeasurable
  have h :=
    setIntegral_map (μ := productMeasure F) (g := shift F) ht hφ' hmp.aemeasurable
  rw [hmp.map_eq] at h
  exact h.symm

theorem condExp_comp_shift (F : AdmissibleFamily) (k : ℕ) {f : ResidueSpace F → ℝ}
    (hf : Integrable f (productMeasure F)) :
    (productMeasure F)[f ∘ shift F | coordFiltration F k] =ᵐ[productMeasure F]
      (productMeasure F)[f | coordFiltration F k] ∘ shift F := by
  have := productMeasure_isProbabilityMeasure F
  have hU := shift_measurePreserving F
  let g : ResidueSpace F → ℝ :=
    (productMeasure F)[f | coordFiltration F k] ∘ shift F
  have hg_int : Integrable g (productMeasure F) :=
    hU.integrable_comp_of_integrable integrable_condExp
  have hsm : StronglyMeasurable[coordFiltration F k]
      ((productMeasure F)[f | coordFiltration F k]) :=
    stronglyMeasurable_condExp
  have hgm :
      AEStronglyMeasurable[coordFiltration F k] g (productMeasure F) :=
    (hsm.comp_measurable (shift_measurable_coordFiltration F k)).aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((coordFiltration F).le k)
      (hU.integrable_comp_of_integrable hf)
      (fun s _ _ => hg_int.integrableOn)
      (fun s hs _ => ?_) hgm).symm
  let t := shift_inv F ⁻¹' s
  have ht : MeasurableSet[coordFiltration F k] t :=
    shift_inv_preimage_coordFiltration F k hs
  have hs_eq : shift F ⁻¹' t = s := by
    ext ω
    simp only [t, Set.mem_preimage]
    rw [shift_leftInverse F ω]
  have hs_amb : MeasurableSet t := (coordFiltration F).le k _ ht
  rw [← hs_eq]
  change
      ∫ x in shift F ⁻¹' t,
          ((productMeasure F)[f | coordFiltration F k] ∘ shift F) x ∂productMeasure F =
        ∫ x in shift F ⁻¹' t, (f ∘ shift F) x ∂productMeasure F
  refine (setIntegral_comp_shift F integrable_condExp hs_amb).trans ?_
  refine (setIntegral_condExp ((coordFiltration F).le k) hf ht).trans ?_
  exact (setIntegral_comp_shift F hf hs_amb).symm

theorem condExp_shift_of_invariant (F : AdmissibleFamily) (k : ℕ) {f : ResidueSpace F → ℝ}
    (hf : Integrable f (productMeasure F))
    (hinv : f ∘ shift F =ᵐ[productMeasure F] f) :
    ((productMeasure F)[f | coordFiltration F k]) ∘ shift F =ᵐ[productMeasure F]
      (productMeasure F)[f | coordFiltration F k] := by
  have hcomp := condExp_comp_shift F k hf
  have hcong := condExp_congr_ae (m := coordFiltration F k) hinv
  exact hcomp.symm.trans hcong

theorem finiteShift_range_orbit_univ (F : AdmissibleFamily) (k : ℕ)
    (ω : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) :
    Set.range (fun n : Fin (partialPeriod F k) => (finiteShift_range F k)^[n.val] ω) =
      Set.univ := by
  ext τ
  simp only [Set.mem_range, Set.mem_univ, iff_true]
  let e := finitePiCongr F k
  have hrange := finiteShift_orbit_univ F k (e.symm ω)
  have : e.symm τ ∈
      Set.range (fun n : Fin (partialPeriod F k) =>
        (finiteShift F k)^[n.val] (e.symm ω)) := by
    rw [hrange]
    exact Set.mem_univ _
  obtain ⟨n, hn⟩ := this
  refine ⟨n, ?_⟩
  have heq :=
    (Function.Semiconj.iterate_right (finiteShift_range_semiconj F k) n.val) (e.symm ω)
  have hn' : (finiteShift F k)^[n.val] (e.symm ω) = e.symm τ := hn
  rw [e.apply_symm_apply] at heq
  exact heq.symm.trans ((congrArg e hn').trans (e.apply_symm_apply τ))

theorem condExp_coord_ae_const (F : AdmissibleFamily) (k : ℕ) {f : ResidueSpace F → ℝ}
    (hf : Integrable f (productMeasure F))
    (hinv : f ∘ shift F =ᵐ[productMeasure F] f) :
    (productMeasure F)[f | coordFiltration F k] =ᵐ[productMeasure F]
      fun _ => ∫ x, f x ∂productMeasure F := by
  have := productMeasure_isProbabilityMeasure F
  have hg : StronglyMeasurable[coordFiltration F k]
      ((productMeasure F)[f | coordFiltration F k]) :=
    stronglyMeasurable_condExp
  have hg' :
      StronglyMeasurable[MeasurableSpace.comap (range k).restrict
          (MeasurableSpace.pi :
            MeasurableSpace (∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)))]
        ((productMeasure F)[f | coordFiltration F k]) := by
    rwa [← coordFiltration_eq_comap]
  obtain ⟨h, hmeas, hcomp⟩ := hg'.exists_eq_measurable_comp
  have hinvk := condExp_shift_of_invariant F k hf hinv
  have hrest :
      h ∘ finiteShift_range F k ∘ (range k).restrict =ᵐ[productMeasure F]
        h ∘ (range k).restrict := by
    have h1 :
        h ∘ finiteShift_range F k ∘ (range k).restrict =
          (h ∘ (range k).restrict) ∘ shift F := by
      rw [← restrict_comp_shift]
      rfl
    rw [h1, ← hcomp]
    exact hinvk
  have hEq :
      MeasurableSet
        { y : ∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val) |
          h (finiteShift_range F k y) = h y } :=
    (hmeas.comp_measurable (finiteShift_range_measurable F k)).measurableSet_eq_fun hmeas
  have hfin :
      h ∘ finiteShift_range F k =ᵐ[Measure.pi fun i : { j : ℕ // j ∈ range k } =>
          coordMeasure F i.val]
        h := by
    have hmp := restrict_measurePreserving F k
    rw [← hmp.map_eq]
    exact (ae_map_iff hmp.aemeasurable hEq).2 hrest
  have hpt : h ∘ finiteShift_range F k = h := finitePi_ae_eq hfin
  obtain ⟨ω₀⟩ : Nonempty (∀ i : { j : ℕ // j ∈ range k }, ZMod (F.d i.val)) := inferInstance
  have hiter : ∀ n : ℕ, h ((finiteShift_range F k)^[n] ω₀) = h ω₀ := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (h ∘ finiteShift_range F k) ((finiteShift_range F k)^[n] ω₀) = h ω₀
      rw [hpt, ih]
  have hconst : h = fun _ => h ω₀ := by
    funext τ
    have hmem :
        τ ∈ Set.range (fun n : Fin (partialPeriod F k) =>
          (finiteShift_range F k)^[n.val] ω₀) := by
      rw [finiteShift_range_orbit_univ]
      exact Set.mem_univ _
    obtain ⟨n, hn⟩ := hmem
    rw [← hn, hiter n.val]
  have hg_const :
      (productMeasure F)[f | coordFiltration F k] = fun _ => h ω₀ := by
    rw [hcomp, hconst]
    rfl
  have hinter :
      ∫ x, ((productMeasure F)[f | coordFiltration F k]) x ∂productMeasure F =
        ∫ x, f x ∂productMeasure F :=
    integral_condExp ((coordFiltration F).le k)
  have hval : h ω₀ = ∫ x, f x ∂productMeasure F := by
    rw [hg_const, integral_const] at hinter
    have huniv : (productMeasure F).real Set.univ = 1 := by
      rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [huniv, one_smul] at hinter
    exact hinter
  rw [hg_const, hval]

theorem shift_preErgodic (F : AdmissibleFamily) :
    PreErgodic (shift F) (productMeasure F) where
  aeconst_set s hs hinv := by
    have := productMeasure_isProbabilityMeasure F
    rw [eventuallyConst_set']
    let f : ResidueSpace F → ℝ := s.indicator fun _ => (1 : ℝ)
    have hf : Integrable f (productMeasure F) :=
      (integrable_const (1 : ℝ)).indicator hs
    have hf_shift : f ∘ shift F = f := by
      funext ω
      simp only [f, Function.comp_apply, Set.indicator_apply]
      rw [← Set.mem_preimage (f := shift F), hinv]
    have hinvf : f ∘ shift F =ᵐ[productMeasure F] f := EventuallyEq.of_eq hf_shift
    have hgmeas : StronglyMeasurable[⨆ n, coordFiltration F n] f := by
      rw [coordFiltration_iSup]
      exact stronglyMeasurable_const.indicator hs
    have hlevy := hf.tendsto_ae_condExp (ℱ := coordFiltration F) hgmeas
    have hconst :
        ∀ n, (productMeasure F)[f | coordFiltration F n] =ᵐ[productMeasure F]
          fun _ => ∫ x, f x ∂productMeasure F :=
      fun n => condExp_coord_ae_const F n hf hinvf
    have hall := (ae_all_iff (ι := ℕ)).2 hconst
    have hfconst :
        f =ᵐ[productMeasure F] fun _ => ∫ x, f x ∂productMeasure F := by
      filter_upwards [hlevy, hall] with x hxlevy hxall
      exact tendsto_nhds_unique (hxlevy.congr fun n => hxall n) tendsto_const_nhds
    have hinter :
        ∫ x, f x ∂productMeasure F = (productMeasure F).real s := by
      simp [f, integral_indicator hs, smul_eq_mul]
    rw [hinter] at hfconst
    obtain ⟨x, hx⟩ := hfconst.exists
    have h01 : f x = 0 ∨ f x = 1 := by
      by_cases hxmem : x ∈ s
      · simp [f, Set.indicator_of_mem hxmem]
      · simp [f, Set.indicator_of_notMem hxmem]
    have hc : (productMeasure F).real s = 0 ∨ (productMeasure F).real s = 1 := by
      rcases h01 with h0 | h1
      · left
        exact hx.symm.trans h0
      · right
        exact hx.symm.trans h1
    rcases hc with h0 | h1
    · left
      exact ae_eq_empty.2 ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0)
    · right
      exact (ae_eq_univ_iff_measure_eq hs.nullMeasurableSet).2 <| by
        rw [measure_univ, ← ENNReal.toReal_eq_one_iff]
        exact h1

theorem shift_ergodic (F : AdmissibleFamily) :
    Ergodic (shift F) (productMeasure F) where
  toMeasurePreserving := shift_measurePreserving F
  toPreErgodic := shift_preErgodic F

theorem shift_ae_invariant_prob_eq_zero_or_one
    (F : AdmissibleFamily) {E : Set (ResidueSpace F)}
    (hE : MeasurableSet E)
    (hinv : shift F ⁻¹' E =ᵐ[productMeasure F] E) :
    productMeasure F E = 0 ∨ productMeasure F E = 1 := by
  have := productMeasure_isProbabilityMeasure F
  have h :=
    (shift_ergodic F).quasiErgodic.ae_empty_or_univ₀ hE.nullMeasurableSet hinv
  rcases h with h0 | h1
  · left
    exact ae_eq_empty.mp h0
  · right
    rw [← measure_univ (μ := productMeasure F)]
    exact (ae_eq_univ_iff_measure_eq hE.nullMeasurableSet).mp h1

end PrimeGapNormality.BFree
