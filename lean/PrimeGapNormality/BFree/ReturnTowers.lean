import PrimeGapNormality.BFree.ProductRotation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.Linarith

/-!
# Forward hitting, return times, and Kakutani cells

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2
  (towers, Kac (4), `t` includes the present);
`lean/BFREE_SOURCE_LEDGER.md` C2; `lean/BFREE_RETURN_TOWERS.md`.
Contract: C2
Audit: GREEN (forward hitting / Poincaré / `μ_A` / `shiftZ` / last visit /
Kakutani disjointness / paper-Kac). Induced ergodicity postponed.

Public `t` includes the present (`firstHitTime = 0` on `A`). Public `g`
is at least one everywhere (dummy `1` on never-return). Dummy values are
harmless after Poincaré / sweep-out. No ambient integrability of `t`.
No `rho > 1/2`. Paper-Kac is `∫_A g dμ = 1`, not a hull identity.
-/

open Classical
open MeasureTheory ProbabilityTheory Function Filter
open Set hiding range mem_range
open Finset (range mem_range prod_congr dvd_prod_of_mem disjoint_left
  countable_toSet prod_coe_sort prod_range_mul_prod_Ico prod_le_one)
open scoped ENNReal Topology ProbabilityTheory

namespace PrimeGapNormality.BFree

variable (F : AdmissibleFamily)

local notation "Ω" => ResidueSpace F
local notation "μ" => productMeasure F
local notation "U" => shift F
local notation "A" => survival F

/-! ### Conservativity and Poincaré on `A` -/

theorem measure_survival_ne_zero : μ A ≠ 0 := by
  rw [measure_survival]
  exact (ENNReal.ofReal_pos.2 (rho_pos F)).ne'

/-- Finite-measure MP ⇒ conservative.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
mathlib `MeasurePreserving.conservative`.
Contract: C2
Audit: GREEN -/
theorem shift_conservative : Conservative U μ :=
  (shift_measurePreserving F).conservative

/-- Poincaré recurrence on survival: a.e. point of `A` returns i.o.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
mathlib `Conservative.ae_mem_imp_frequently_image_mem`.
Contract: C2
Audit: GREEN -/
theorem ae_mem_survival_frequently :
    ∀ᵐ a ∂μ, a ∈ A → ∃ᶠ n in atTop, U^[n] a ∈ A :=
  (shift_conservative F).ae_mem_imp_frequently_image_mem
    (survival_measurable F).nullMeasurableSet

theorem shift_iterate_mem_survival (n : ℕ) (ω : Ω) :
    U^[n] ω ∈ A ↔ ∀ i, ω i + n ≠ 0 := by
  constructor
  · intro h i
    simpa [shift_iterate_apply] using h i
  · intro h i
    simpa [shift_iterate_apply] using h i

/-! ### Finite-cylinder hitting (used for ambient sweep-out of `A`) -/

/-- Every orbit hits every finite survival cylinder.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem exists_add_ne_zero_lt (ω : Ω) :
    ∀ K : ℕ, ∃ n : ℕ, ∀ i : ℕ, i < K → ω i + n ≠ 0 := by
  intro K
  induction K with
  | zero =>
    exact ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ K ih =>
    obtain ⟨n, hn⟩ := ih
    let D : ℕ := ∏ i ∈ range K, F.d i
    have hcop : Nat.Coprime D (F.d K) :=
      Nat.coprime_prod_left_iff.mpr fun i hi =>
        F.pairwise_coprime (Nat.ne_of_lt (mem_range.mp hi))
    let u := ZMod.unitOfCoprime D hcop
    let mZ : ZMod (F.d K) := (1 - (ω K + n)) * (↑(u⁻¹) : ZMod (F.d K))
    refine ⟨n + mZ.val * D, ?_⟩
    intro i hi
    have hi' : i ≤ K := Nat.lt_succ_iff.mp hi
    rcases eq_or_lt_of_le hi' with hieq | hlt
    · have h1 : (1 : ZMod (F.d K)) ≠ 0 := by
        rw [ne_eq, ZMod.one_eq_zero_iff]
        exact d_not_one F K
      have hval : ω i + (n + mZ.val * D : ℕ) = (1 : ZMod (F.d i)) := by
        rw [hieq]
        have hDu : (u : ZMod (F.d K)) = D := ZMod.coe_unitOfCoprime D hcop
        have hinv : (↑(u⁻¹) : ZMod (F.d K)) * (u : ZMod (F.d K)) = 1 :=
          Units.inv_mul u
        calc
          ω K + ↑(n + mZ.val * D)
              = ω K + ↑n + ↑mZ.val * ↑D := by
                rw [Nat.cast_add, Nat.cast_mul, add_assoc]
          _ = ω K + n + mZ * (u : ZMod (F.d K)) := by
                rw [ZMod.natCast_val, ZMod.cast_id, hDu]
          _ = ω K + n + (1 - (ω K + n)) *
                ((↑(u⁻¹) : ZMod (F.d K)) * (u : ZMod (F.d K))) := by
                rw [mul_assoc]
          _ = ω K + n + (1 - (ω K + n)) := by
                rw [hinv, mul_one]
          _ = 1 := by
                rw [add_comm (ω K + n), sub_add_cancel]
      rw [hval]
      exact hieq ▸ h1
    · have hdiv : F.d i ∣ D := dvd_prod_of_mem F.d (mem_range.mpr hlt)
      have hD0 : (D : ZMod (F.d i)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
      have hsame : ω i + (n + mZ.val * D : ℕ) = ω i + n := by
        rw [Nat.cast_add, Nat.cast_mul, hD0, mul_zero, add_zero]
      rw [hsame]
      exact hn i hlt

theorem exists_add_ne_zero_restrict (K : ℕ)
    (x : ∀ i : range K, ZMod (F.d i)) :
    ∃ n : ℕ, ∀ i : range K, x i + n ≠ 0 := by
  let ω : Ω := fun i => if h : i ∈ range K then x ⟨i, h⟩ else 0
  obtain ⟨n, hn⟩ := exists_add_ne_zero_lt F ω K
  refine ⟨n, ?_⟩
  intro i
  have hω : ω i.1 = x i := dif_pos i.2
  exact hω ▸ hn i.1 (mem_range.mp i.2)

noncomputable def cylinderHit (K : ℕ) (ω : Ω) : ℕ :=
  Nat.find (exists_add_ne_zero_lt F ω K)

noncomputable def cylinderHitRestrict (K : ℕ)
    (x : ∀ i : range K, ZMod (F.d i)) : ℕ :=
  Nat.find (exists_add_ne_zero_restrict F K x)

theorem cylinderHit_eq_restrict (K : ℕ) (ω : Ω) :
    cylinderHit F K ω = cylinderHitRestrict F K (fun i => ω i.1) := by
  unfold cylinderHit cylinderHitRestrict
  refine Nat.find_congr' ?_
  intro n
  constructor
  · intro h i
    exact h i.1 (mem_range.mp i.2)
  · intro h i hi
    exact h ⟨i, mem_range.mpr hi⟩

theorem cylinderHit_spec (K : ℕ) (ω : Ω) :
    ∀ i : ℕ, i < K → ω i + cylinderHit F K ω ≠ 0 :=
  Nat.find_spec (exists_add_ne_zero_lt F ω K)

theorem measurableSet_coord_add_ne (i k : ℕ) :
    MeasurableSet {ω : Ω | ω i + k ≠ 0} :=
  ((measurableSet_singleton (0 : ZMod (F.d i))).compl).preimage
    ((measurable_pi_apply i).add measurable_const)

theorem measurable_cylinderHit (K : ℕ) : Measurable (cylinderHit F K) := by
  refine measurable_find (fun ω => exists_add_ne_zero_lt F ω K) fun k => ?_
  have : {ω : Ω | ∀ i : ℕ, i < K → ω i + k ≠ 0} =
      ⋂ i ∈ (range K : Set ℕ), {ω : Ω | ω i + k ≠ 0} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, Finset.mem_coe, mem_range]
  rw [this]
  exact MeasurableSet.biInter (countable_toSet _) fun i _ =>
    measurableSet_coord_add_ne F i k

/-! ### Sweep-out of `A` via independence of disjoint coordinate blocks -/

theorem indep_eval : iIndepFun (fun i (ω : Ω) => ω i) μ := by
  unfold productMeasure
  exact iIndepFun_infinitePi (P := coordMeasure F) (X := fun _ x => x)
    fun _ => measurable_id

theorem map_restrict_coord (s : Finset ℕ) :
    Measure.map (s.restrict (π := fun i => ZMod (F.d i))) μ =
      Measure.pi fun i : s => coordMeasure F i.1 := by
  unfold productMeasure
  exact Measure.infinitePi_map_restrict (coordMeasure F) (I := s)

theorem measure_pi_avoid_nat (T : Finset ℕ) (n : ℕ) :
    (Measure.pi fun i : T => coordMeasure F i.1)
        {y : (i : T) → ZMod (F.d i) | ∀ i : T, y i + n ≠ 0} =
      ∏ i ∈ T, ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹) := by
  have heq :
      {y : (i : T) → ZMod (F.d i) | ∀ i : T, y i + n ≠ 0} =
        Set.univ.pi fun i : T => {x : ZMod (F.d i.1) | x + n ≠ 0} := by
    ext y
    simp [Set.mem_pi]
  rw [heq, Measure.pi_pi]
  have hfac : ∀ i : T,
      coordMeasure F i.1 {x : ZMod (F.d i.1) | x + n ≠ 0} =
        ENNReal.ofReal (1 - (F.d i.1 : ℝ)⁻¹) := by
    intro i
    have hpre : {x : ZMod (F.d i.1) | x + n ≠ 0} =
        Set.preimage (fun x : ZMod (F.d i.1) => x + n)
          ({0}ᶜ : Set (ZMod (F.d i.1))) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
        mem_ofPred_eq, ne_eq]
    have hmeas : Measurable fun x : ZMod (F.d i.1) => x + n := Measurable.of_discrete
    have hs : MeasurableSet ({0}ᶜ : Set (ZMod (F.d i.1))) :=
      (measurableSet_singleton (0 : ZMod (F.d i.1))).compl
    rw [hpre, ← Measure.map_apply hmeas hs,
      coordMeasure_map_add F i.1 (n : ZMod (F.d i.1)), coordMeasure_compl_zero]
  simp_rw [hfac]
  exact prod_coe_sort T
    (fun i : ℕ => ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹))

theorem disjoint_range_Ico (K M : ℕ) :
    Disjoint (range K) (Finset.Ico K (K + M)) := by
  refine disjoint_left.mpr ?_
  intro i hiS hiT
  exact (mem_range.mp hiS).not_ge (Finset.mem_Ico.mp hiT).1

theorem prod_Ico_survivalFactor (K M : ℕ) :
    ∏ i ∈ Finset.Ico K (K + M), ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹) =
      ENNReal.ofReal (finiteRho F (K + M) / finiteRho F K) := by
  have hnonneg : ∀ i ∈ Finset.Ico K (K + M),
      0 ≤ (1 : ℝ) - (F.d i : ℝ)⁻¹ := fun i _ => (survivalFactor_pos F i).le
  have hmul :=
    prod_range_mul_prod_Ico (fun i => (1 : ℝ) - (F.d i : ℝ)⁻¹)
      (Nat.le_add_right K M)
  rw [← finiteRho_eq_prod F K, ← finiteRho_eq_prod F (K + M)] at hmul
  have hdiv :
      ∏ i ∈ Finset.Ico K (K + M), (1 - (F.d i : ℝ)⁻¹) =
        finiteRho F (K + M) / finiteRho F K := by
    rw [eq_div_iff (finiteRho_pos F K).ne']
    exact (mul_comm _ _).trans hmul
  rw [← ENNReal.ofReal_prod_of_nonneg hnonneg, hdiv]

/-- Finite-window tail after the canonical cylinder time.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem measure_cylinderHit_tail_window (K M : ℕ) :
    μ {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M → ω i + cylinderHit F K ω ≠ 0} =
      ENNReal.ofReal (finiteRho F (K + M) / finiteRho F K) := by
  let S : Finset ℕ := range K
  let T : Finset ℕ := Finset.Ico K (K + M)
  let e : Ω →
      ((∀ i : S, ZMod (F.d i)) × ∀ i : T, ZMod (F.d i)) :=
    fun ω => (S.restrict ω, T.restrict ω)
  have he : Measurable e :=
    (Finset.measurable_restrict S).prodMk (Finset.measurable_restrict T)
  let G : Set ((∀ i : S, ZMod (F.d i)) × ∀ i : T, ZMod (F.d i)) :=
    {p | ∀ i : T, p.2 i + cylinderHitRestrict F K p.1 ≠ 0}
  have hG : MeasurableSet G := MeasurableSet.of_discrete
  have hpre :
      {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M → ω i + cylinderHit F K ω ≠ 0} =
        e ⁻¹' G := by
    ext ω
    constructor
    · intro h i
      have hi := Finset.mem_Ico.mp i.2
      have hω := h i.1 hi.1 hi.2
      rw [cylinderHit_eq_restrict] at hω
      exact hω
    · intro h i hiK hiM
      have hiT : i ∈ T := Finset.mem_Ico.mpr ⟨hiK, hiM⟩
      have hω := h ⟨i, hiT⟩
      rw [cylinderHit_eq_restrict]
      exact hω
  have hInd :
      IndepFun (fun ω : Ω => S.restrict ω) (fun ω : Ω => T.restrict ω) μ :=
    (indep_eval F).indepFun_finset S T (disjoint_range_Ico K M)
      fun i => measurable_pi_apply i
  have hlaw :
      Measure.map e μ =
        (Measure.pi fun i : S => coordMeasure F i.1).prod
          (Measure.pi fun i : T => coordMeasure F i.1) := by
    have hX : AEMeasurable (fun ω : Ω => S.restrict ω) μ :=
      (Finset.measurable_restrict S).aemeasurable
    have hY : AEMeasurable (fun ω : Ω => T.restrict ω) μ :=
      (Finset.measurable_restrict T).aemeasurable
    have h := hInd.map_prod_eq_prod_map_map hX hY
    rw [map_restrict_coord F S, map_restrict_coord F T] at h
    exact h
  rw [hpre, ← Measure.map_apply he hG, hlaw, Measure.prod_apply hG]
  have hinner : ∀ x : ∀ i : S, ZMod (F.d i),
      (Measure.pi fun i : T => coordMeasure F i.1) (Prod.mk x ⁻¹' G) =
        ∏ i ∈ T, ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹) := by
    intro x
    have : Prod.mk x ⁻¹' G =
        {y : (i : T) → ZMod (F.d i) |
          ∀ i : T, y i + cylinderHitRestrict F K x ≠ 0} := rfl
    rw [this, measure_pi_avoid_nat]
  have hconst :
      (fun x => (Measure.pi fun i : T => coordMeasure F i.1) (Prod.mk x ⁻¹' G)) =
        fun _ => ∏ i ∈ T, ENNReal.ofReal (1 - (F.d i : ℝ)⁻¹) :=
    funext hinner
  rw [hconst, lintegral_const, measure_univ, mul_one, prod_Ico_survivalFactor]

theorem antitone_cylinderHit_tail (K : ℕ) :
    Antitone fun M : ℕ =>
      {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M → ω i + cylinderHit F K ω ≠ 0} := by
  intro a b hab ω hω i hiK hi
  exact hω i hiK (lt_of_lt_of_le hi (Nat.add_le_add_left hab K))

theorem cylinderHit_tail_iInter (K : ℕ) :
    (⋂ M : ℕ, {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M →
        ω i + cylinderHit F K ω ≠ 0}) =
      {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0} := by
  ext ω
  constructor
  · intro h i hiK
    have hM := mem_iInter.mp h (i + 1 - K)
    have hle : K ≤ i + 1 := hiK.trans (Nat.le_succ i)
    have hlt : i < K + (i + 1 - K) := by
      rw [Nat.add_sub_of_le hle]
      exact Nat.lt_succ_self i
    exact hM i hiK hlt
  · intro h
    refine mem_iInter.mpr ?_
    intro M i hiK hiM
    exact h i hiK

theorem measurableSet_cylinderHit_tail_window (K M : ℕ) :
    MeasurableSet {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M →
        ω i + cylinderHit F K ω ≠ 0} := by
  let T : Finset ℕ := Finset.Ico K (K + M)
  have heq :
      {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M → ω i + cylinderHit F K ω ≠ 0} =
        ⋂ i ∈ (T : Set ℕ), {ω : Ω | ω i + cylinderHit F K ω ≠ 0} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h i hi
      have hiT : i ∈ T := Finset.mem_coe.mp hi
      have hiIco := Finset.mem_Ico.mp hiT
      exact h i hiIco.1 hiIco.2
    · intro h i hiK hiM
      exact h i (Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨hiK, hiM⟩))
  rw [heq]
  refine MeasurableSet.biInter (countable_toSet T) fun i _ => ?_
  have hf : Measurable fun ω : Ω => ω i + (cylinderHit F K ω : ZMod (F.d i)) :=
    (measurable_pi_apply i).add
      ((Measurable.of_discrete
            (f := fun n : ℕ => (n : ZMod (F.d i)))).comp
        (measurable_cylinderHit F K))
  exact (measurableSet_singleton (0 : ZMod (F.d i))).compl.preimage hf

theorem measurableSet_cylinderHit_tail (K : ℕ) :
    MeasurableSet {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0} := by
  rw [← cylinderHit_tail_iInter]
  exact MeasurableSet.iInter fun M => measurableSet_cylinderHit_tail_window F K M

theorem measure_cylinderHit_tail (K : ℕ) :
    μ {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0} =
      ENNReal.ofReal (rho F / finiteRho F K) := by
  let s : ℕ → Set Ω := fun M =>
    {ω : Ω | ∀ i : ℕ, K ≤ i → i < K + M → ω i + cylinderHit F K ω ≠ 0}
  have hcyl : ∀ M, NullMeasurableSet (s M) μ := fun M =>
    (measurableSet_cylinderHit_tail_window F K M).nullMeasurableSet
  have hinter :
      {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0} = ⋂ M, s M :=
    (cylinderHit_tail_iInter F K).symm
  have hlim :
      Tendsto (fun M => μ (s M)) atTop
        (𝓝 (μ {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0})) := by
    rw [hinter]
    exact tendsto_measure_iInter_atTop hcyl (antitone_cylinderHit_tail F K)
      ⟨0, measure_ne_top _ _⟩
  have hfin :
      Tendsto (fun M => μ (s M)) atTop
        (𝓝 (ENNReal.ofReal (rho F / finiteRho F K))) := by
    have hrho :
        Tendsto (fun M => finiteRho F (K + M)) atTop (𝓝 (rho F)) := by
      have h := (finiteRho_tendsto_rho F).comp (tendsto_add_atTop_nat K)
      have heq :
          ((fun k => finiteRho F k) ∘ fun a => a + K) =
            fun M => finiteRho F (K + M) := by
        funext M
        simp [Function.comp_apply, add_comm]
      rwa [heq] at h
    have hdiv :
        Tendsto (fun M => finiteRho F (K + M) / finiteRho F K) atTop
          (𝓝 (rho F / finiteRho F K)) :=
      hrho.div tendsto_const_nhds (finiteRho_pos F K).ne'
    refine (ENNReal.tendsto_ofReal hdiv).congr fun M => ?_
    exact (measure_cylinderHit_tail_window F K M).symm
  exact tendsto_nhds_unique hlim hfin

theorem finiteRho_antitone : Antitone (finiteRho F) := by
  intro a b hab
  have hmul :=
    prod_range_mul_prod_Ico (fun i => (1 : ℝ) - (F.d i : ℝ)⁻¹) hab
  rw [← finiteRho_eq_prod F a, ← finiteRho_eq_prod F b] at hmul
  have hle :
      ∏ i ∈ Finset.Ico a b, (1 - (F.d i : ℝ)⁻¹) ≤ 1 :=
    prod_le_one (fun i _ => (survivalFactor_pos F i).le)
      (fun i _ => survivalFactor_le_one F i)
  calc
    finiteRho F b
        = finiteRho F a *
            ∏ i ∈ Finset.Ico a b, (1 - (F.d i : ℝ)⁻¹) := hmul.symm
    _ ≤ finiteRho F a * 1 :=
      mul_le_mul_of_nonneg_left hle (finiteRho_pos F a).le
    _ = finiteRho F a := mul_one _

theorem subset_hits_of_cylinderHit_tail (K : ℕ) :
    {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0} ⊆
      {ω : Ω | ∃ N, U^[N] ω ∈ A} := by
  intro ω hω
  refine ⟨cylinderHit F K ω, ?_⟩
  rw [shift_iterate_mem_survival]
  intro i
  by_cases hi : i < K
  · exact cylinderHit_spec F K ω i hi
  · exact hω i (Nat.le_of_not_lt hi)

/-- Almost every orbit hits `A` (including time `0`). Dummy collision for
`firstHitTime` is therefore null.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem measure_never_hits_survival :
    μ {ω : Ω | ∀ N, U^[N] ω ∉ A} = 0 := by
  have hle : ∀ K : ℕ,
      μ {ω : Ω | ∀ N, U^[N] ω ∉ A} ≤
        ENNReal.ofReal (1 - rho F / finiteRho F K) := by
    intro K
    have hge : rho F ≤ finiteRho F K :=
      le_of_tendsto (finiteRho_tendsto_rho F)
        ((eventually_ge_atTop K).mono fun n hn => finiteRho_antitone F hn)
    have hsubset :
        {ω : Ω | ∀ N, U^[N] ω ∉ A} ⊆
          {ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0}ᶜ := by
      intro ω hnever htail
      obtain ⟨N, hN⟩ := subset_hits_of_cylinderHit_tail F K htail
      exact hnever N hN
    have hmono :
        μ {ω : Ω | ∀ N, U^[N] ω ∉ A} ≤
          μ ({ω : Ω | ∀ i : ℕ, K ≤ i → ω i + cylinderHit F K ω ≠ 0}ᶜ) :=
      measure_mono hsubset
    have hfin :
        (productMeasure F)
          {ω : ResidueSpace F | ∀ i : ℕ, K ≤ i →
            ω i + cylinderHit F K ω ≠ 0} ≠ ∞ :=
      measure_ne_top (productMeasure F)
        {ω : ResidueSpace F | ∀ i : ℕ, K ≤ i →
          ω i + cylinderHit F K ω ≠ 0}
    have hcompl :=
      measure_compl (measurableSet_cylinderHit_tail F K) hfin
    rw [hcompl, measure_univ, measure_cylinderHit_tail F K] at hmono
    have hratio_le : rho F / finiteRho F K ≤ 1 :=
      div_le_one_of_le₀ hge (finiteRho_pos F K).le
    have hsub :
        (1 : ℝ≥0∞) - ENNReal.ofReal (rho F / finiteRho F K) =
          ENNReal.ofReal (1 - rho F / finiteRho F K) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
      · exact div_nonneg (rho_pos F).le (finiteRho_pos F K).le
    rwa [hsub] at hmono
  have htend :
      Tendsto (fun K : ℕ => ENNReal.ofReal (1 - rho F / finiteRho F K))
        atTop (𝓝 0) := by
    have hρ : Tendsto (finiteRho F) atTop (𝓝 (rho F)) := finiteRho_tendsto_rho F
    have hdiv : Tendsto (fun K => rho F / finiteRho F K) atTop (𝓝 (1 : ℝ)) := by
      have hc : Tendsto (fun _ : ℕ => rho F) atTop (𝓝 (rho F)) := tendsto_const_nhds
      have h := hc.div hρ (rho_pos F).ne'
      have h' :
          Tendsto ((fun _ : ℕ => rho F) / finiteRho F) atTop (𝓝 (1 : ℝ)) := by
        simpa [div_self (rho_pos F).ne'] using h
      exact h'
    have hsub :
        Tendsto (fun K => (1 : ℝ) - rho F / finiteRho F K) atTop (𝓝 0) := by
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa using h1.sub hdiv
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hsub
  refine le_antisymm ?_ bot_le
  exact ge_of_tendsto htend (Eventually.of_forall hle)

/-! ### First hit `t` (includes the present) -/

/-- First hitting time of `A`, including the present. Dummy `0` on never-visit
(`sInf ∅ = 0`), colliding with the genuine value on `A`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2; Contract C2.
Audit: GREEN -/
noncomputable def firstHitTime : Ω → ℕ :=
  fun ω => sInf {n : ℕ | U^[n] ω ∈ A}

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem firstHitTime_eq_zero_of_mem {ω : Ω} (h : ω ∈ A) :
    firstHitTime F ω = 0 := by
  unfold firstHitTime
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  simpa [iterate_zero_apply] using h

/-- Hitting set nonempty a.e. (dummy of `t` is null). Not `Integrable`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem firstHitTime_ae_finite :
    ∀ᵐ ω ∂μ, ∃ N, U^[N] ω ∈ A := by
  rw [ae_iff]
  simp only [not_exists]
  exact measure_never_hits_survival F

/-! ### Return time `g ≥ 1` -/

/-- First return time, strictly positive everywhere. Dummy `1` on never-return.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2; Contract C2.
Audit: GREEN -/
noncomputable def returnTime : Ω → ℕ :=
  fun ω =>
    if _h : {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty then
      sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}
    else
      1

/-- Totality: `g ≥ 1` everywhere, including the dummy.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem returnTime_pos (ω : Ω) : 0 < returnTime F ω := by
  unfold returnTime
  split_ifs with h
  · exact (Nat.sInf_mem h).1
  · exact Nat.succ_pos 0

/-- Height one: `ω ∈ A` and `U ω ∈ A` imply `g = 1`, everywhere.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §4.1 (transition);
ReturnTowers does not lift colours.
Contract: C2
Audit: GREEN -/
theorem returnTime_eq_one_of_mem {ω : Ω} (_hA : ω ∈ A) (hU : U ω ∈ A) :
    returnTime F ω = 1 := by
  unfold returnTime
  have hs : {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty :=
    ⟨1, Nat.succ_pos 0, by simpa [iterate_one] using hU⟩
  rw [dif_pos hs]
  have h1 : 1 ∈ {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} :=
    ⟨Nat.succ_pos 0, by simpa [iterate_one] using hU⟩
  have hle : sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} ≤ 1 := Nat.sInf_le h1
  have hpos : 0 < sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} := (Nat.sInf_mem hs).1
  omega

/-- On `A` this is Poincaré; off `A` it follows from sweep-out.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
mathlib `Conservative.ae_forall_image_mem_imp_frequently_image_mem`.
Contract: C2
Audit: GREEN -/
theorem returnTime_ae_finite :
    ∀ᵐ ω ∂μ, ∃ n, 0 < n ∧ U^[n] ω ∈ A := by
  filter_upwards [
    (shift_conservative F).ae_forall_image_mem_imp_frequently_image_mem
      (survival_measurable F).nullMeasurableSet,
    firstHitTime_ae_finite F] with ω hfreq hhit
  obtain ⟨k, hk⟩ := hhit
  obtain ⟨n, hn, hmem⟩ := (frequently_atTop.mp (hfreq k hk)) (k + 1)
  exact ⟨n, (Nat.succ_pos k).trans_le hn, hmem⟩

/-! ### Induced shift and root measure -/

/-- First-return map `S`, total on `Ω` because `returnTime` is total.
On `A` this is paper `S`; off `A` it is first forward hit (a.e.).

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
noncomputable def inducedShift : Ω → Ω :=
  fun ω => U^[returnTime F ω] ω

/-- Conditional Haar on the root: `μ[|A]`, a measure on `Ω` supported on `A`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
mathlib `ProbabilityTheory.cond`.
Contract: C2
Audit: GREEN -/
noncomputable def rootMeasure : Measure Ω :=
  μ[|A]

instance rootMeasure_isProbabilityMeasure : IsProbabilityMeasure (rootMeasure F) :=
  cond_isProbabilityMeasure (measure_survival_ne_zero F)

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem measure_root_survival : rootMeasure F A = 1 :=
  cond_apply_self (measure_survival_ne_zero F) (measure_ne_top μ A)

/-! ### Integer iterates (`shiftZ`) and invertibility (Wave 2) -/

/-- Two-sided rotation: `n ≥ 0` applies `U^n`, `n < 0` applies `(U⁻¹)^(-n)`.
Same encoding as Carry's `zpowersShift`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
`lean/BFREE_RETURN_TOWERS.md` Wave 2.
Contract: C2
Audit: GREEN -/
def shiftZ : ℤ → Ω → Ω
  | Int.ofNat k => U^[k]
  | Int.negSucc k => (shift_inv F)^[k + 1]

theorem shiftZ_zero : shiftZ F 0 = id :=
  rfl

theorem shiftZ_natCast (n : ℕ) (ω : Ω) : shiftZ F n ω = U^[n] ω :=
  rfl

theorem shiftZ_neg (n : ℕ) (ω : Ω) :
    shiftZ F (-n) ω = (shift_inv F)^[n] ω := by
  cases n with
  | zero =>
    simp [shiftZ]
  | succ n =>
    have hneg : -(n.succ : ℤ) = Int.negSucc n := by
      simp [Int.negSucc_eq]
    rw [hneg, shiftZ]

theorem shiftZ_apply (n : ℤ) (ω : Ω) (i : ℕ) : shiftZ F n ω i = ω i + n := by
  cases n with
  | ofNat k =>
    simpa [shiftZ] using shift_iterate_apply F k ω i
  | negSucc k =>
    have h := shift_inv_iterate_apply F (k + 1) ω i
    simpa [shiftZ, Int.cast_negSucc, sub_eq_add_neg] using h

theorem shiftZ_add (m n : ℤ) (ω : Ω) :
    shiftZ F (m + n) ω = shiftZ F m (shiftZ F n ω) := by
  funext i
  simp [shiftZ_apply, Int.cast_add, add_left_comm, add_comm]

theorem shiftZ_leftInverse (n : ℤ) :
    LeftInverse (shiftZ F (-n)) (shiftZ F n) := by
  intro ω
  rw [← shiftZ_add, neg_add_cancel, shiftZ_zero]
  rfl

theorem shift_iterate_injective (n : ℕ) : Injective (U^[n]) :=
  (shift_bijective F).injective.iterate n

theorem shift_inv_iterate_comp_shift (n : ℕ) (ω : Ω) :
    (shift_inv F)^[n] (U^[n] ω) = ω :=
  (shift_leftInverse F).iterate n ω

theorem shift_iterate_comp_shift_inv (n : ℕ) (ω : Ω) :
    U^[n] ((shift_inv F)^[n] ω) = ω :=
  (shift_rightInverse F).iterate n ω

theorem shift_inv_iterate_comp_shift_iterate {k j : ℕ} (hkj : k ≤ j) (ω : Ω) :
    (shift_inv F)^[k] (U^[j] ω) = U^[j - k] ω := by
  have hsplit : U^[j] ω = U^[k] (U^[j - k] ω) := by
    calc
      U^[j] ω = U^[k + (j - k)] ω := by rw [Nat.add_sub_of_le hkj]
      _ = U^[k] (U^[j - k] ω) := Function.iterate_add_apply (f := U) _ _ _
  rw [hsplit]
  exact shift_inv_iterate_comp_shift F k _

theorem shift_inv_iterate_mem_survival (n : ℕ) (ω : Ω) :
    (shift_inv F)^[n] ω ∈ A ↔ ∀ i, ω i - n ≠ 0 := by
  constructor
  · intro h i
    simpa [shift_inv_iterate_apply] using h i
  · intro h i
    simpa [shift_inv_iterate_apply] using h i

theorem shift_inv_conservative : Conservative (shift_inv F) μ :=
  (shift_inv_measurePreserving F).conservative

/-- Backward Poincaré on survival.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2;
mathlib `Conservative.ae_mem_imp_frequently_image_mem`.
Contract: C2
Audit: GREEN -/
theorem ae_mem_survival_frequently_backward :
    ∀ᵐ a ∂μ, a ∈ A → ∃ᶠ n in atTop, (shift_inv F)^[n] a ∈ A :=
  (shift_inv_conservative F).ae_mem_imp_frequently_image_mem
    (survival_measurable F).nullMeasurableSet

/-! ### Return-time gap and last visit -/

/-- First return is the least strictly positive hitting time, when one exists.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem returnTime_spec {ω : Ω}
    (hret : {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty) :
    U^[returnTime F ω] ω ∈ A ∧
      ∀ k, 0 < k → k < returnTime F ω → U^[k] ω ∉ A := by
  have hdef : returnTime F ω = sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} :=
    dif_pos hret
  rw [hdef]
  have hmem := Nat.sInf_mem hret
  refine ⟨hmem.2, ?_⟩
  intro k hk hklt hA
  have hkmem : k ∈ {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} := And.intro hk hA
  have : sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} ≤ k := Nat.sInf_le hkmem
  omega

/-- Interior of a tower of height `n` lies off `A`. Dummy `g = 1` cannot
have a strictly positive interior index.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3)).
Contract: C2
Audit: GREEN -/
theorem not_mem_survival_of_lt_returnTime {n k : ℕ} {a : Ω}
    (_haA : a ∈ A) (haN : returnTime F a = n) (hk : 0 < k) (hkn : k < n) :
    U^[k] a ∉ A := by
  by_cases hret : {m : ℕ | 0 < m ∧ U^[m] a ∈ A}.Nonempty
  · exact (returnTime_spec F hret).2 k hk (haN ▸ hkn)
  · have hn1 : n = 1 := by
      unfold returnTime at haN
      simp only [dif_neg hret] at haN
      exact haN.symm
    omega

/-- Last-visit age, including the present. Dummy `0` on never-in-the-past.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3));
`lean/BFREE_RETURN_TOWERS.md` Wave 2.
Contract: C2
Audit: GREEN -/
noncomputable def lastVisitAge : Ω → ℕ :=
  fun ω => sInf {k : ℕ | shiftZ F (-k) ω ∈ A}

theorem lastVisitAge_eq_zero_of_mem {ω : Ω} (h : ω ∈ A) :
    lastVisitAge F ω = 0 := by
  unfold lastVisitAge
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  simpa [shiftZ_zero] using h

theorem lastVisitAge_spec {ω : Ω}
    (hvis : {k : ℕ | shiftZ F (-k) ω ∈ A}.Nonempty) :
    shiftZ F (-lastVisitAge F ω) ω ∈ A ∧
      ∀ j < lastVisitAge F ω, shiftZ F (-j) ω ∉ A := by
  have hmem := Nat.sInf_mem hvis
  refine ⟨hmem, ?_⟩
  intro j hj hA
  exact (Nat.sInf_le hA).not_gt hj

/-- The most recent visit to `A` (including the present) is unique.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3)).
Contract: C2
Audit: GREEN -/
theorem lastVisitAge_unique {ω : Ω} {k : ℕ}
    (hmem : shiftZ F (-k) ω ∈ A)
    (hmin : ∀ j < k, shiftZ F (-j) ω ∉ A) :
    lastVisitAge F ω = k := by
  have hvis : {j : ℕ | shiftZ F (-j) ω ∈ A}.Nonempty := ⟨k, hmem⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_of_not_gt ?_
  intro hlt
  have hA : shiftZ F (-lastVisitAge F ω) ω ∈ A := by
    simpa [lastVisitAge] using Nat.sInf_mem hvis
  exact hmin _ hlt hA

theorem eq_of_isLastVisit {ω : Ω} {k k' : ℕ}
    (hk : shiftZ F (-k) ω ∈ A)
    (hkmin : ∀ j < k, shiftZ F (-j) ω ∉ A)
    (hk' : shiftZ F (-k') ω ∈ A)
    (hk'min : ∀ j < k', shiftZ F (-j) ω ∉ A) :
    k = k' := by
  rw [← lastVisitAge_unique F hk hkmin, lastVisitAge_unique F hk' hk'min]

/-! ### Kakutani cells -/

/-- Return-time level `A_n = A ∩ {g = n}`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3)).
Contract: C2
Audit: GREEN -/
noncomputable def returnLevel (n : ℕ) : Set Ω :=
  {ω | ω ∈ A ∧ returnTime F ω = n}

/-- Kakutani cell `U^j A_n`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3)).
Contract: C2
Audit: GREEN -/
noncomputable def towerCell (n j : ℕ) : Set Ω :=
  U^[j] '' returnLevel F n

theorem lastVisitAge_eq_of_mem_towerCell {n j : ℕ} {ω : Ω}
    (hj : j < n) (hω : ω ∈ towerCell F n j) :
    lastVisitAge F ω = j := by
  obtain ⟨a, ha, rfl⟩ := hω
  rcases ha with ⟨haA, haN⟩
  refine lastVisitAge_unique F ?_ ?_
  · rw [shiftZ_neg, shift_inv_iterate_comp_shift]
    exact haA
  · intro k hk
    rw [shiftZ_neg, shift_inv_iterate_comp_shift_iterate F (le_of_lt hk)]
    exact not_mem_survival_of_lt_returnTime F haA haN (Nat.sub_pos_of_lt hk)
      ((Nat.sub_le j k).trans_lt hj)

/-- Kakutani cells `U^j A_n` for `n ≥ 1`, `0 ≤ j < n` are pairwise disjoint.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3)).
Contract: C2
Audit: GREEN -/
theorem towerCell_disjoint {n n' j j' : ℕ}
    (_hn : 1 ≤ n) (hj : j < n) (_hn' : 1 ≤ n') (hj' : j' < n')
    (hne : n ≠ n' ∨ j ≠ j') :
    Disjoint (towerCell F n j) (towerCell F n' j') := by
  refine Set.disjoint_left.mpr ?_
  intro ω hω hω'
  obtain ⟨a, ha, rfl⟩ := hω
  obtain ⟨a', ha', hEq⟩ := hω'
  rcases ha with ⟨haA, haN⟩
  rcases ha' with ⟨ha'A, ha'N⟩
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have hle : j ≤ j' := le_of_lt hlt
    have hsplit : U^[j'] a' = U^[j] (U^[j' - j] a') := by
      calc
        U^[j'] a' = U^[j + (j' - j)] a' := by rw [Nat.add_sub_of_le hle]
        _ = U^[j] (U^[j' - j] a') := Function.iterate_add_apply (f := U) _ _ _
    have haeq : a = U^[j' - j] a' :=
      shift_iterate_injective F j (hEq.symm.trans hsplit)
    have hnot : U^[j' - j] a' ∉ A :=
      not_mem_survival_of_lt_returnTime F ha'A ha'N (Nat.sub_pos_of_lt hlt)
        ((Nat.sub_le j' j).trans_lt hj')
    rw [← haeq] at hnot
    exact hnot haA
  · have haeq : a = a' := by
      refine shift_iterate_injective F j ?_
      calc
        U^[j] a = U^[j'] a' := hEq.symm
        _ = U^[j] a' := by rw [heq]
    have hn_eq : n = n' := by
      rw [← haN, ← ha'N, haeq]
    exact hne.elim (fun hnn => hnn hn_eq) (fun hjj => hjj heq)
  · have hle : j' ≤ j := le_of_lt hgt
    have hsplit : U^[j] a = U^[j'] (U^[j - j'] a) := by
      calc
        U^[j] a = U^[j' + (j - j')] a := by rw [Nat.add_sub_of_le hle]
        _ = U^[j'] (U^[j - j'] a) := Function.iterate_add_apply (f := U) _ _ _
    have ha'eq : a' = U^[j - j'] a :=
      shift_iterate_injective F j' (hEq.trans hsplit)
    have hnot : U^[j - j'] a ∉ A :=
      not_mem_survival_of_lt_returnTime F haA haN (Nat.sub_pos_of_lt hgt)
        ((Nat.sub_le j j').trans_lt hj)
    rw [← ha'eq] at hnot
    exact hnot ha'A

theorem eq_of_mem_towerCell {n n' j j' : ℕ} {ω : Ω}
    (hn : 1 ≤ n) (hj : j < n) (hn' : 1 ≤ n') (hj' : j' < n')
    (hω : ω ∈ towerCell F n j) (hω' : ω ∈ towerCell F n' j') :
    n = n' ∧ j = j' := by
  by_contra hneq
  exact Set.disjoint_left.mp
    (towerCell_disjoint F hn hj hn' hj' (not_and_or.mp hneq)) hω hω'

/-! ### Measurability of return time and Kakutani cells -/

theorem measurableSet_iterate_mem_survival (n : ℕ) :
    MeasurableSet {ω : Ω | U^[n] ω ∈ A} :=
  (survival_measurable F).preimage ((shift_measurable F).iterate n)

theorem shift_iterate_image_eq_shift_inv_preimage (n : ℕ) (s : Set Ω) :
    U^[n] '' s = (shift_inv F)^[n] ⁻¹' s := by
  ext ω
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_preimage, shift_inv_iterate_comp_shift]
    exact ha
  · intro h
    exact ⟨(shift_inv F)^[n] ω, h, shift_iterate_comp_shift_inv F n ω⟩

theorem returnTime_eq_one_iff {ω : Ω} :
    returnTime F ω = 1 ↔
      U ω ∈ A ∨ ∀ n, 0 < n → U^[n] ω ∉ A := by
  constructor
  · intro h
    by_cases hs : {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty
    · left
      have hdef : returnTime F ω = sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} :=
        dif_pos hs
      have hmem := Nat.sInf_mem hs
      have h1 : sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} = 1 := by
        rw [← hdef, h]
      rw [h1] at hmem
      simpa [iterate_one] using hmem.2
    · right
      intro n hn hnA
      exact hs ⟨n, hn, hnA⟩
  · intro h
    rcases h with hU | hnever
    · unfold returnTime
      have hs : {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty :=
        ⟨1, Nat.succ_pos 0, by simpa [iterate_one] using hU⟩
      rw [dif_pos hs]
      have h1 : 1 ∈ {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} :=
        ⟨Nat.succ_pos 0, by simpa [iterate_one] using hU⟩
      have hle : sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} ≤ 1 := Nat.sInf_le h1
      have hpos : 0 < sInf {n : ℕ | 0 < n ∧ U^[n] ω ∈ A} := (Nat.sInf_mem hs).1
      omega
    · unfold returnTime
      have hs : ¬ {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty := by
        intro ⟨n, hn, hnA⟩
        exact hnever n hn hnA
      rw [dif_neg hs]

theorem returnTime_eq_iff {ω : Ω} {n : ℕ} (hn : 2 ≤ n) :
    returnTime F ω = n ↔
      U^[n] ω ∈ A ∧ ∀ k, 0 < k → k < n → U^[k] ω ∉ A := by
  constructor
  · intro hrt
    have hs : {m : ℕ | 0 < m ∧ U^[m] ω ∈ A}.Nonempty := by
      by_contra hempty
      have : returnTime F ω = 1 := by
        unfold returnTime
        rw [dif_neg hempty]
      omega
    have hspec := returnTime_spec F hs
    rw [hrt] at hspec
    exact hspec
  · intro ⟨hUn, hmin⟩
    have hs : {m : ℕ | 0 < m ∧ U^[m] ω ∈ A}.Nonempty :=
      ⟨n, lt_of_lt_of_le Nat.zero_lt_two hn, hUn⟩
    have hdef : returnTime F ω = sInf {m : ℕ | 0 < m ∧ U^[m] ω ∈ A} := dif_pos hs
    apply le_antisymm
    · rw [hdef]
      exact Nat.sInf_le ⟨lt_of_lt_of_le Nat.zero_lt_two hn, hUn⟩
    · by_contra hlt
      rw [not_le] at hlt
      exact hmin (returnTime F ω) (returnTime_pos F ω) hlt (returnTime_spec F hs).1

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem measurableSet_returnTime_eq (n : ℕ) :
    MeasurableSet {ω : Ω | returnTime F ω = n} := by
  match n with
  | 0 =>
    have : {ω : Ω | returnTime F ω = 0} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_empty_iff_false, iff_false, mem_ofPred_eq]
      exact (returnTime_pos F ω).ne'
    rw [this]
    exact MeasurableSet.empty
  | 1 =>
    have heq' : {ω : Ω | returnTime F ω = 1} =
        {ω | U ω ∈ A} ∪ {ω | ∀ n, 0 < n → U^[n] ω ∉ A} := by
      ext ω
      simpa [mem_union, mem_ofPred_eq] using (returnTime_eq_one_iff (F := F) (ω := ω))
    have hnever :
        {ω : Ω | ∀ n, 0 < n → U^[n] ω ∉ A} =
          ⋂ k : ℕ, {ω | U^[k + 1] ω ∉ A} := by
      ext ω
      simp only [mem_iInter, mem_ofPred_eq]
      constructor
      · intro h k
        exact h (k + 1) (Nat.succ_pos k)
      · intro h n hn
        simpa [Nat.sub_add_cancel hn] using h (n - 1)
    rw [heq', hnever]
    exact (measurableSet_iterate_mem_survival F 1).union
      (MeasurableSet.iInter fun k => (measurableSet_iterate_mem_survival F (k + 1)).compl)
  | n + 2 =>
    have heq : {ω : Ω | returnTime F ω = n + 2} =
        {ω | U^[n + 2] ω ∈ A} ∩
          ⋂ k ∈ (range (n + 1) : Set ℕ), {ω | U^[k + 1] ω ∉ A} := by
      ext ω
      simp only [mem_inter_iff, mem_iInter, Finset.mem_coe, mem_range, mem_ofPred_eq]
      constructor
      · intro hrt
        have h := (returnTime_eq_iff F (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))).mp hrt
        refine ⟨h.1, ?_⟩
        intro k hk
        exact h.2 (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ hk)
      · intro ⟨hUn, hmin⟩
        refine (returnTime_eq_iff F (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))).mpr
          ⟨hUn, ?_⟩
        intro k hk hkn
        have hk' : k - 1 < n + 1 := by
          have : k ≤ n + 1 := Nat.lt_succ_iff.mp hkn
          exact Nat.sub_lt_left_of_lt_add hk (by omega)
        have := hmin (k - 1) hk'
        simpa [Nat.sub_add_cancel hk] using this
    rw [heq]
    exact (measurableSet_iterate_mem_survival F (n + 2)).inter
      (MeasurableSet.biInter (countable_toSet _) fun k _ =>
        (measurableSet_iterate_mem_survival F (k + 1)).compl)

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem returnTime_measurable : Measurable (returnTime F) :=
  measurable_to_countable' fun n => measurableSet_returnTime_eq F n

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem measurableSet_returnLevel (n : ℕ) :
    MeasurableSet (returnLevel F n) :=
  (survival_measurable F).inter (measurableSet_returnTime_eq F n)

theorem measurableSet_towerCell (n j : ℕ) : MeasurableSet (towerCell F n j) := by
  rw [towerCell, shift_iterate_image_eq_shift_inv_preimage]
  exact (measurableSet_returnLevel F n).preimage ((shift_inv_measurable F).iterate j)

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (3)).
Contract: C2
Audit: GREEN -/
theorem towerCell_measure {n j : ℕ} (_hj : j < n) :
    μ (towerCell F n j) = μ (returnLevel F n) := by
  rw [towerCell, shift_iterate_image_eq_shift_inv_preimage]
  exact ((shift_inv_measurePreserving F).iterate j).measure_preimage
    (measurableSet_returnLevel F n).nullMeasurableSet

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem returnLevel_iUnion_eq : (⋃ n : ℕ, returnLevel F (n + 1)) = A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hω⟩ := mem_iUnion.mp h
    exact hω.1
  · intro hA
    refine mem_iUnion.mpr ⟨returnTime F ω - 1, ⟨hA, ?_⟩⟩
    exact (Nat.sub_add_cancel (returnTime_pos F ω)).symm

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem returnLevel_iUnion :
    ∀ᵐ a ∂μ, a ∈ A ↔ a ∈ ⋃ n : ℕ, returnLevel F (n + 1) := by
  refine Filter.Eventually.of_forall ?_
  intro a
  rw [returnLevel_iUnion_eq]

/-! ### Last-visit sweep-out and covering of `Ω` -/

/-- Almost every orbit hits `A` in the past, including the present.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2.
Contract: C2
Audit: GREEN -/
theorem lastVisitAge_ae_finite :
    ∀ᵐ ω ∂μ, {k : ℕ | shiftZ F (-k) ω ∈ A}.Nonempty := by
  let BadA : Set Ω :=
    {a | a ∈ A ∧ ¬ ∃ᶠ n in atTop, (shift_inv F)^[n] a ∈ A}
  have hBad : μ BadA = 0 := by
    have h := ae_iff.mp (ae_mem_survival_frequently_backward F)
    refine measure_mono_null ?_ h
    intro a ha
    exact fun hf => ha.2 (hf ha.1)
  have hW : μ (⋃ N : ℕ, U^[N] ⁻¹' BadA) = 0 := by
    refine measure_iUnion_null fun N => ?_
    have hmp := (shift_measurePreserving F).iterate N
    rw [hmp.measure_preimage (NullMeasurableSet.of_null hBad)]
    exact hBad
  have hWae : ∀ᵐ ω ∂μ, ∀ N, U^[N] ω ∉ BadA := by
    rw [ae_iff]
    have : {ω : Ω | ¬ ∀ N, U^[N] ω ∉ BadA} = ⋃ N : ℕ, U^[N] ⁻¹' BadA := by
      ext ω
      simp only [mem_iUnion, mem_preimage, mem_ofPred_eq, not_forall, not_not]
    rwa [this]
  filter_upwards [firstHitTime_ae_finite F, hWae] with ω hhit hnotBad
  obtain ⟨N, hN⟩ := hhit
  have hfreq : ∃ᶠ n in atTop, (shift_inv F)^[n] (U^[N] ω) ∈ A := by
    by_contra hnf
    exact hnotBad N ⟨hN, hnf⟩
  obtain ⟨k, hkN, hkA⟩ := (frequently_atTop.mp hfreq) N
  refine ⟨k - N, ?_⟩
  change shiftZ F (-(k - N : ℕ)) ω ∈ A
  rw [shiftZ_neg F (k - N) ω]
  have hcalc : (shift_inv F)^[k] (U^[N] ω) = (shift_inv F)^[k - N] ω := by
    calc
      (shift_inv F)^[k] (U^[N] ω)
          = (shift_inv F)^[(k - N) + N] (U^[N] ω) := by rw [Nat.sub_add_cancel hkN]
      _ = (shift_inv F)^[k - N] ((shift_inv F)^[N] (U^[N] ω)) :=
        iterate_add_apply _ _ _ _
      _ = (shift_inv F)^[k - N] ω := by rw [shift_inv_iterate_comp_shift]
  rwa [← hcalc]

theorem lastVisitAge_lt_returnTime {ω : Ω}
    (hvis : {k : ℕ | shiftZ F (-k) ω ∈ A}.Nonempty)
    (hret : {n : ℕ | 0 < n ∧ U^[n] (shiftZ F (-lastVisitAge F ω) ω) ∈ A}.Nonempty) :
    lastVisitAge F ω < returnTime F (shiftZ F (-lastVisitAge F ω) ω) := by
  let j := lastVisitAge F ω
  let a := shiftZ F (-j) ω
  have hnpos : 0 < returnTime F a := returnTime_pos F a
  have hspec := returnTime_spec F hret
  by_contra hge
  rw [not_lt] at hge
  have hjpos : 0 < j := lt_of_lt_of_le hnpos hge
  have hlt : j - returnTime F a < j := Nat.sub_lt hjpos hnpos
  have hω : U^[j] (shiftZ F (-j) ω) = ω := by
    rw [shiftZ_neg F j ω, shift_iterate_comp_shift_inv]
  have hmem : shiftZ F (-(j - returnTime F a : ℕ)) ω ∈ A := by
    rw [shiftZ_neg F (j - returnTime F a) ω, ← hω]
    have hinv :=
      shift_inv_iterate_comp_shift_iterate F (Nat.sub_le j (returnTime F a))
        (shiftZ F (-j) ω)
    have hjn : j - (j - returnTime F a) = returnTime F a :=
      tsub_tsub_cancel_of_le hge
    rw [hinv, hjn]
    exact hspec.1
  exact (lastVisitAge_spec F hvis).2 (j - returnTime F a) hlt hmem

theorem mem_kakutaniTowers_iff {ω : Ω} :
    ω ∈ ⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j ↔
      ∃ n j : ℕ, 1 ≤ n ∧ j < n ∧ ω ∈ towerCell F n j := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    exact ⟨n + 1, (j : ℕ), Nat.le_add_left 1 n, j.isLt, hj⟩
  · intro ⟨n, j, hn, hj, hω⟩
    refine mem_iUnion.mpr ⟨n - 1, mem_iUnion.mpr ⟨⟨j, ?_⟩, ?_⟩⟩
    · rw [Nat.sub_add_cancel hn]
      exact hj
    · convert hω
      exact Nat.sub_add_cancel hn

theorem mem_kakutaniTowers_of_lastVisit {ω : Ω}
    (hvis : {k : ℕ | shiftZ F (-k) ω ∈ A}.Nonempty)
    (hret : {n : ℕ | 0 < n ∧ U^[n] (shiftZ F (-lastVisitAge F ω) ω) ∈ A}.Nonempty) :
    ω ∈ ⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j := by
  set j := lastVisitAge F ω
  set a := shiftZ F (-j) ω
  have haA : a ∈ A := (lastVisitAge_spec F hvis).1
  have hjn := lastVisitAge_lt_returnTime F hvis hret
  have hn1 : 1 ≤ returnTime F a := Nat.succ_le_of_lt (returnTime_pos F a)
  have hcell : ω ∈ towerCell F (returnTime F a) j := by
    refine ⟨a, ⟨haA, rfl⟩, ?_⟩
    change U^[j] (shiftZ F (-j) ω) = ω
    rw [shiftZ_neg F j ω, shift_iterate_comp_shift_inv]
  exact (mem_kakutaniTowers_iff F).mpr ⟨returnTime F a, j, hn1, hjn, hcell⟩

theorem measure_never_returns :
    μ {ω : Ω | ¬ {n : ℕ | 0 < n ∧ U^[n] ω ∈ A}.Nonempty} = 0 := by
  simpa [Set.Nonempty] using (ae_iff.mp (returnTime_ae_finite F))

/-- Kakutani towers `⋃_{n≥1} ⋃_{0≤j<n} U^j A_n` are conull.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper after (3)).
Contract: C2
Audit: GREEN -/
theorem towers_cover_ae :
    μ (⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j)ᶜ = 0 := by
  let E : Set Ω := ⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j
  let NoPast : Set Ω := {ω | ¬ {k : ℕ | shiftZ F (-k) ω ∈ A}.Nonempty}
  let DummyRoot : Set Ω :=
    {a | a ∈ A ∧ ¬ {n : ℕ | 0 < n ∧ U^[n] a ∈ A}.Nonempty}
  let DummyOrbit : Set Ω := ⋃ j : ℕ, U^[j] '' DummyRoot
  have hNoPast : μ NoPast = 0 := by
    simpa [NoPast, Set.Nonempty] using (ae_iff.mp (lastVisitAge_ae_finite F))
  have hDummyRoot : μ DummyRoot = 0 :=
    measure_mono_null (fun _ ha => ha.2) (measure_never_returns F)
  have hDummyOrbit : μ DummyOrbit = 0 := by
    refine measure_iUnion_null fun j => ?_
    rw [shift_iterate_image_eq_shift_inv_preimage]
    have hmp := (shift_inv_measurePreserving F).iterate j
    rw [hmp.measure_preimage (NullMeasurableSet.of_null hDummyRoot)]
    exact hDummyRoot
  have hsubset : Eᶜ ⊆ NoPast ∪ DummyOrbit := by
    intro ω hE
    by_cases hvis : {k : ℕ | shiftZ F (-k) ω ∈ A}.Nonempty
    · right
      set j := lastVisitAge F ω
      set a := shiftZ F (-j) ω
      have haA : a ∈ A := (lastVisitAge_spec F hvis).1
      have hret_fail : ¬ {n : ℕ | 0 < n ∧ U^[n] a ∈ A}.Nonempty := by
        intro hret
        exact hE (mem_kakutaniTowers_of_lastVisit F hvis hret)
      refine mem_iUnion.mpr ⟨j, ⟨a, ⟨haA, hret_fail⟩, ?_⟩⟩
      change U^[j] (shiftZ F (-j) ω) = ω
      rw [shiftZ_neg F j ω, shift_iterate_comp_shift_inv]
    · exact Or.inl (by simpa [NoPast] using hvis)
  exact measure_mono_null hsubset (measure_union_null hNoPast hDummyOrbit)

/-! ### Kac (paper (4)) -/

theorem kakutaniTowers_eq_range_iUnion :
    (⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j) =
      ⋃ n : ℕ, ⋃ j ∈ range (n + 1), towerCell F (n + 1) j := by
  ext ω
  simp only [mem_iUnion, Finset.mem_range]
  constructor
  · intro ⟨n, j, hω⟩
    exact ⟨n, (j : ℕ), j.isLt, hω⟩
  · intro ⟨n, j, hj, hω⟩
    exact ⟨n, ⟨j, hj⟩, hω⟩

theorem measure_tower_slice (n : ℕ) :
    μ (⋃ j ∈ range (n + 1), towerCell F (n + 1) j) =
      (n + 1 : ℝ≥0∞) * μ (returnLevel F (n + 1)) := by
  have hd : PairwiseDisjoint (range (n + 1) : Set ℕ)
      (fun j => towerCell F (n + 1) j) := by
    intro a ha b hb hne
    have ha' : a < n + 1 := mem_range.mp (by simpa using ha)
    have hb' : b < n + 1 := mem_range.mp (by simpa using hb)
    exact towerCell_disjoint F (Nat.le_add_left 1 n) ha'
      (Nat.le_add_left 1 n) hb' (Or.inr hne)
  have hm : ∀ j ∈ range (n + 1), MeasurableSet (towerCell F (n + 1) j) :=
    fun j _ => measurableSet_towerCell F (n + 1) j
  rw [measure_biUnion_finset hd hm]
  have hconst : ∀ j ∈ range (n + 1),
      μ (towerCell F (n + 1) j) = μ (returnLevel F (n + 1)) :=
    fun j hj => towerCell_measure F (mem_range.mp hj)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp

theorem pairwise_disjoint_tower_slices :
    Pairwise (Disjoint on fun n : ℕ => ⋃ j ∈ range (n + 1), towerCell F (n + 1) j) := by
  intro n m hnm
  refine disjoint_left.mpr ?_
  intro ω hωn hωm
  have hn : ∃ j, j < n + 1 ∧ ω ∈ towerCell F (n + 1) j := by
    simpa [mem_iUnion, mem_range] using hωn
  have hm : ∃ j, j < m + 1 ∧ ω ∈ towerCell F (m + 1) j := by
    simpa [mem_iUnion, mem_range] using hωm
  obtain ⟨j, hj, hωj⟩ := hn
  obtain ⟨j', hj', hωj'⟩ := hm
  have h := eq_of_mem_towerCell F (Nat.le_add_left 1 n) hj
    (Nat.le_add_left 1 m) hj' hωj hωj'
  exact hnm (Nat.succ_injective h.1)

theorem measurableSet_tower_slice (n : ℕ) :
    MeasurableSet (⋃ j ∈ range (n + 1), towerCell F (n + 1) j) :=
  Finset.measurableSet_biUnion _ fun j _ => measurableSet_towerCell F (n + 1) j

theorem measure_kakutaniTowers :
    μ (⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j) = 1 := by
  let E : Set Ω := ⋃ n : ℕ, ⋃ j : Fin (n + 1), towerCell F (n + 1) j
  have h0 : μ Eᶜ = 0 := towers_cover_ae F
  have hle : μ E ≤ 1 := by
    have : μ E ≤ μ univ := measure_mono (subset_univ _)
    simpa [measure_univ] using this
  have hge : 1 ≤ μ E := by
    calc
      (1 : ℝ≥0∞) = μ (univ : Set Ω) := measure_univ.symm
      _ = μ (E ∪ Eᶜ) := by rw [union_compl_self]
      _ ≤ μ E + μ Eᶜ := measure_union_le _ _
      _ = μ E := by rw [h0, add_zero]
  exact le_antisymm hle hge

theorem lintegral_returnTime_eq_tsum :
    ∫⁻ ω in A, (returnTime F ω : ℝ≥0∞) ∂μ =
      ∑' n : ℕ, (n + 1 : ℝ≥0∞) * μ (returnLevel F (n + 1)) := by
  have heq : A = ⋃ n : ℕ, returnLevel F (n + 1) := (returnLevel_iUnion_eq F).symm
  rw [heq]
  have hd : Pairwise (Disjoint on fun n => returnLevel F (n + 1)) := by
    intro n m hnm
    refine disjoint_left.mpr ?_
    intro ω hω hω'
    exact hnm (Nat.succ_injective (hω.2.symm.trans hω'.2))
  rw [lintegral_iUnion (fun n => measurableSet_returnLevel F (n + 1)) hd]
  refine tsum_congr fun n => ?_
  have hfun : ∀ ω ∈ returnLevel F (n + 1),
      (returnTime F ω : ℝ≥0∞) = (n : ℝ≥0∞) + 1 := fun ω hω => by
    rw [hω.2, Nat.cast_succ]
  rw [setLIntegral_congr_fun (measurableSet_returnLevel F (n + 1)) hfun,
    setLIntegral_const]

/-- Kac's formula: `∫_A g dμ = 1`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (4)).
Contract: C2
Audit: GREEN -/
theorem kac_returnTime : ∫⁻ ω in A, returnTime F ω ∂μ = 1 := by
  rw [lintegral_returnTime_eq_tsum]
  have hslice : ∀ n : ℕ,
      ((n : ℝ≥0∞) + 1) * μ (returnLevel F (n + 1)) =
        μ (⋃ j ∈ range (n + 1), towerCell F (n + 1) j) :=
    fun n => (measure_tower_slice F n).symm
  simp_rw [hslice]
  have hd := pairwise_disjoint_tower_slices F
  have hm := measurableSet_tower_slice F
  rw [← measure_iUnion hd hm, ← kakutaniTowers_eq_range_iUnion]
  exact measure_kakutaniTowers F

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (4), Carry (2.2)).
Contract: C2
Audit: GREEN -/
theorem expected_returnTime :
    ∫⁻ ω, returnTime F ω ∂rootMeasure F = ENNReal.ofReal (rho F)⁻¹ := by
  unfold rootMeasure
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, kac_returnTime F,
    mul_one, measure_survival, ENNReal.ofReal_inv_of_pos (rho_pos F)]

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §2 (paper (4)).
Contract: C2
Audit: GREEN -/
theorem expected_returnTime_toReal :
    ∫ ω, (returnTime F ω : ℝ) ∂rootMeasure F = (rho F)⁻¹ := by
  have hnn : 0 ≤ᵐ[rootMeasure F] fun ω => (returnTime F ω : ℝ) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  have hfm : AEStronglyMeasurable (fun ω => (returnTime F ω : ℝ)) (rootMeasure F) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      (returnTime_measurable F) |>.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hfm]
  rw [lintegral_congr fun ω => ENNReal.ofReal_natCast (returnTime F ω),
    expected_returnTime F, ENNReal.toReal_ofReal]
  exact inv_nonneg.2 (rho_pos F).le

end PrimeGapNormality.BFree
