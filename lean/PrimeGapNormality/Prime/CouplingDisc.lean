import PrimeGapNormality.Prime.Coupling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Named finite shape discrepancy (TV / L¹)

Two discrete masses on a Finset: the named discrepancy is the L¹
distance, equivalently twice `tvHalf`. Bounded observations of those
masses (short-shape tests when the index is a configuration) differ by
at most that L¹. Product coupling and the categorical-versus-independent
bound are the Coupling lemmas that instantiate the named `Prop`.

`ShapeDiscrepancy` is a definition, not an `axiom`. No primes, no
Kuperberg.

Source: `lean/PRIME_SIGNATURES.md` Coupling;
`PrimeGapNormality.Prime.Coupling`; `Config.tvHalf`.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

/-! ### L¹ versus half-TV -/

/-- Full L¹ of two finite masses. Equals `2 * tvHalf`. -/
noncomputable def massL1 {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) : ℝ :=
  ∑ i ∈ s, |μ i - ν i|

theorem massL1_eq_two_tvHalf {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) :
    massL1 s μ ν = 2 * tvHalf s μ ν := by
  unfold massL1 tvHalf
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_div_cancel₀ (∑ i ∈ s, |μ i - ν i|) h2).symm

theorem massL1_nonneg {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) :
    0 ≤ massL1 s μ ν := by
  rw [massL1_eq_two_tvHalf]
  exact mul_nonneg (by norm_num) (tvHalf_nonneg s μ ν)

theorem massL1_comm {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) :
    massL1 s μ ν = massL1 s ν μ := by
  unfold massL1
  refine sum_congr rfl fun i _ => abs_sub_comm _ _

theorem massL1_self {ι : Type*} (s : Finset ι) (μ : ι → ℝ) :
    massL1 s μ μ = 0 := by
  unfold massL1
  refine sum_eq_zero fun _ _ => ?_
  simp [sub_self, abs_zero]

/-! ### Named discrepancy (not an axiom) -/

/-- Named finite discrepancy: L¹ of `μ` and `ν` on `s` is at most `ε`.
On a powerset this is the L¹ of short-shape (configuration) observations.
Not an `axiom`. -/
def ShapeDiscrepancy {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) (ε : ℝ) :
    Prop :=
  0 ≤ ε ∧ massL1 s μ ν ≤ ε

theorem shapeDiscrepancy_nonneg {ι : Type*} {s : Finset ι} {μ ν : ι → ℝ}
    {ε : ℝ} (h : ShapeDiscrepancy s μ ν ε) : 0 ≤ ε :=
  h.1

theorem shapeDiscrepancy_massL1_le {ι : Type*} {s : Finset ι}
    {μ ν : ι → ℝ} {ε : ℝ} (h : ShapeDiscrepancy s μ ν ε) :
    massL1 s μ ν ≤ ε :=
  h.2

theorem shapeDiscrepancy_two_tvHalf_le {ι : Type*} {s : Finset ι}
    {μ ν : ι → ℝ} {ε : ℝ} (h : ShapeDiscrepancy s μ ν ε) :
    2 * tvHalf s μ ν ≤ ε := by
  have hL := h.2
  rwa [massL1_eq_two_tvHalf] at hL

theorem shapeDiscrepancy_refl {ι : Type*} (s : Finset ι) (μ : ι → ℝ) :
    ShapeDiscrepancy s μ μ 0 :=
  ⟨le_rfl, le_of_eq (massL1_self s μ)⟩

theorem shapeDiscrepancy_symm {ι : Type*} {s : Finset ι} {μ ν : ι → ℝ}
    {ε : ℝ} (h : ShapeDiscrepancy s μ ν ε) :
    ShapeDiscrepancy s ν μ ε :=
  ⟨h.1, le_of_eq_of_le (massL1_comm s ν μ) h.2⟩

theorem shapeDiscrepancy_mono {ι : Type*} {s : Finset ι} {μ ν : ι → ℝ}
    {ε δ : ℝ} (h : ShapeDiscrepancy s μ ν ε) (hεδ : ε ≤ δ) :
    ShapeDiscrepancy s μ ν δ :=
  ⟨le_trans h.1 hεδ, h.2.trans hεδ⟩

/-- Coupling's `tvHalf` bound is an L¹ discrepancy of size `2δ`. -/
theorem shapeDiscrepancy_of_tvHalf_le {ι : Type*} {s : Finset ι}
    {μ ν : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (h : tvHalf s μ ν ≤ δ) :
    ShapeDiscrepancy s μ ν (2 * δ) := by
  refine ⟨mul_nonneg (by norm_num) hδ, ?_⟩
  rw [massL1_eq_two_tvHalf]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem shapeDiscrepancy_tvHalf {ι : Type*} (s : Finset ι) (μ ν : ι → ℝ) :
    ShapeDiscrepancy s μ ν (2 * tvHalf s μ ν) :=
  shapeDiscrepancy_of_tvHalf_le (tvHalf_nonneg s μ ν) le_rfl

/-! ### Bounded tests differ by at most the L¹ / TV -/

theorem abs_sum_mul_sub_le_mul_massL1 {ι : Type*} (s : Finset ι)
    (μ ν : ι → ℝ) (f : ι → ℝ) {M : ℝ}
    (_hM : 0 ≤ M) (hf : ∀ i ∈ s, |f i| ≤ M) :
    |∑ i ∈ s, μ i * f i - ∑ i ∈ s, ν i * f i| ≤ M * massL1 s μ ν := by
  have hrew :
      ∑ i ∈ s, μ i * f i - ∑ i ∈ s, ν i * f i =
        ∑ i ∈ s, (μ i - ν i) * f i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => (sub_mul _ _ _).symm
  rw [hrew]
  calc
    |∑ i ∈ s, (μ i - ν i) * f i|
        ≤ ∑ i ∈ s, |(μ i - ν i) * f i| :=
          abs_sum_le_sum_abs (fun i => (μ i - ν i) * f i) s
    _ = ∑ i ∈ s, |μ i - ν i| * |f i| := by
          refine sum_congr rfl fun _ _ => abs_mul _ _
    _ ≤ ∑ i ∈ s, |μ i - ν i| * M :=
          sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hf i hi) (abs_nonneg _)
    _ = M * massL1 s μ ν := by
          rw [← sum_mul, massL1, mul_comm]

/-- If `|f| ≤ 1`, the observation difference is at most the L¹ (twice
`tvHalf`). This is the TV bound for bounded short-shape tests. -/
theorem abs_sum_mul_sub_le_massL1 {ι : Type*} (s : Finset ι)
    (μ ν : ι → ℝ) (f : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1) :
    |∑ i ∈ s, μ i * f i - ∑ i ∈ s, ν i * f i| ≤ massL1 s μ ν := by
  have h := abs_sum_mul_sub_le_mul_massL1 s μ ν f (by norm_num : (0 : ℝ) ≤ 1) hf
  rwa [one_mul] at h

theorem abs_sum_mul_sub_le_two_tvHalf {ι : Type*} (s : Finset ι)
    (μ ν : ι → ℝ) (f : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1) :
    |∑ i ∈ s, μ i * f i - ∑ i ∈ s, ν i * f i| ≤ 2 * tvHalf s μ ν := by
  have h := abs_sum_mul_sub_le_massL1 s μ ν f hf
  rwa [massL1_eq_two_tvHalf] at h

/-- Under `ShapeDiscrepancy`, a 1-bounded test differs by at most `ε`. -/
theorem abs_sum_mul_sub_le_of_shapeDiscrepancy {ι : Type*} {s : Finset ι}
    {μ ν : ι → ℝ} {ε : ℝ} (f : ι → ℝ) (hf : ∀ i ∈ s, |f i| ≤ 1)
    (h : ShapeDiscrepancy s μ ν ε) :
    |∑ i ∈ s, μ i * f i - ∑ i ∈ s, ν i * f i| ≤ ε :=
  (abs_sum_mul_sub_le_massL1 s μ ν f hf).trans h.2

/-! ### Product coupling supplies a named discrepancy -/

/-- L¹ form of `tvHalf_mul_le`. -/
theorem massL1_mul_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ μ' : α → ℝ) (ν ν' : β → ℝ)
    (hν0 : ∀ b ∈ t, 0 ≤ ν b) (hμ'0 : ∀ a ∈ s, 0 ≤ μ' a)
    (hν1 : ∑ b ∈ t, ν b = 1) (hμ'1 : ∑ a ∈ s, μ' a = 1) :
    massL1 (s ×ˢ t) (fun p => μ p.1 * ν p.2) (fun p => μ' p.1 * ν' p.2)
      ≤ massL1 s μ μ' + massL1 t ν ν' := by
  have h := tvHalf_mul_le s t μ μ' ν ν' hν0 hμ'0 hν1 hμ'1
  rw [massL1_eq_two_tvHalf (s ×ˢ t) (fun p => μ p.1 * ν p.2)
      (fun p => μ' p.1 * ν' p.2),
    massL1_eq_two_tvHalf s μ μ', massL1_eq_two_tvHalf t ν ν', ← mul_add]
  exact mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)

theorem shapeDiscrepancy_mul {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} {μ μ' : α → ℝ} {ν ν' : β → ℝ}
    {ε δ : ℝ}
    (hν0 : ∀ b ∈ t, 0 ≤ ν b) (hμ'0 : ∀ a ∈ s, 0 ≤ μ' a)
    (hν1 : ∑ b ∈ t, ν b = 1) (hμ'1 : ∑ a ∈ s, μ' a = 1)
    (hε : ShapeDiscrepancy s μ μ' ε) (hδ : ShapeDiscrepancy t ν ν' δ) :
    ShapeDiscrepancy (s ×ˢ t)
      (fun p => μ p.1 * ν p.2) (fun p => μ' p.1 * ν' p.2) (ε + δ) := by
  refine ⟨add_nonneg hε.1 hδ.1, ?_⟩
  have hprod := massL1_mul_le s t μ μ' ν ν' hν0 hμ'0 hν1 hμ'1
  exact hprod.trans (add_le_add hε.2 hδ.2)

/-! ### Categorical versus independent deletion -/

/-- Cardinality-weighted categorical deletion mass. -/
noncomputable def categoricalCardMass (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  (m.choose k : ℝ) * categoricalDeleteMass m q k

/-- Cardinality-weighted independent Bernoulli deletion mass. -/
noncomputable def independentCardMass (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  (m.choose k : ℝ) * independentDeleteMass m q k

theorem independentCardMass_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (m k : ℕ) : 0 ≤ independentCardMass m q k :=
  mul_nonneg (Nat.cast_nonneg _) (independentDeleteMass_nonneg hq0 hq1 m k)

theorem independentCardMass_sum (m : ℕ) (q : ℝ) :
    ∑ k ∈ range (m + 1), independentCardMass m q k = 1 := by
  unfold independentCardMass
  exact independentDeleteMass_weighted_sum m q

theorem categoricalCardMass_nonneg {q : ℝ} (hq0 : 0 ≤ q) {m : ℕ}
    (hm : (m : ℝ) * q ≤ 1) (k : ℕ) : 0 ≤ categoricalCardMass m q k := by
  unfold categoricalCardMass
  by_cases h0 : k = 0
  · rw [h0, categoricalDeleteMass_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hm)
  · by_cases h1 : k = 1
    · rw [h1, categoricalDeleteMass_one]
      exact mul_nonneg (Nat.cast_nonneg _) hq0
    · have hk2 : 2 ≤ k := by omega
      rw [categoricalDeleteMass_of_two_le m q hk2, mul_zero]

theorem categoricalCardMass_sum (m : ℕ) (q : ℝ) :
    ∑ k ∈ range (m + 1), categoricalCardMass m q k = 1 := by
  unfold categoricalCardMass
  by_cases hm : m = 0
  · subst hm
    rw [range_one, sum_singleton, Nat.choose_zero_right,
      categoricalDeleteMass_zero]
    ring
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have h01 := pair_zero_one_subset_range hmpos
    have hrest :
        ∑ k ∈ range (m + 1) \ ({0, 1} : Finset ℕ),
            (m.choose k : ℝ) * categoricalDeleteMass m q k = 0 := by
      refine sum_eq_zero fun k hk => ?_
      have hk2 : 2 ≤ k := mem_two_of_mem_sdiff_zero_one hk
      rw [categoricalDeleteMass_of_two_le m q hk2, mul_zero]
    have hpair :
        ∑ k ∈ ({0, 1} : Finset ℕ),
            (m.choose k : ℝ) * categoricalDeleteMass m q k = 1 := by
      rw [sum_pair Nat.zero_ne_one, Nat.choose_zero_right,
        Nat.choose_one_right, categoricalDeleteMass_zero,
        categoricalDeleteMass_one]
      ring
    have hsplit :=
      (sum_sdiff h01 :
        ∑ k ∈ range (m + 1) \ ({0, 1} : Finset ℕ),
            (m.choose k : ℝ) * categoricalDeleteMass m q k +
          ∑ k ∈ ({0, 1} : Finset ℕ),
            (m.choose k : ℝ) * categoricalDeleteMass m q k =
          ∑ k ∈ range (m + 1),
            (m.choose k : ℝ) * categoricalDeleteMass m q k)
    rw [hrest, hpair, zero_add] at hsplit
    exact hsplit.symm

theorem tvHalf_cardMass (m : ℕ) (q : ℝ) :
    tvHalf (range (m + 1)) (categoricalCardMass m q) (independentCardMass m q)
      = categoricalVsIndependentTV m q := by
  unfold tvHalf categoricalVsIndependentTV categoricalCardMass
    independentCardMass
  have hpt : ∀ k ∈ range (m + 1),
      |(m.choose k : ℝ) * categoricalDeleteMass m q k -
          (m.choose k : ℝ) * independentDeleteMass m q k|
        = (m.choose k : ℝ) *
          |categoricalDeleteMass m q k - independentDeleteMass m q k| := by
    intro k _
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose k))]
  refine congrArg (fun z => z / (2 : ℝ)) ?_
  exact sum_congr rfl hpt

/-- Coupling's quadratic TV bound is a named `ShapeDiscrepancy`. -/
theorem shapeDiscrepancy_categorical {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (m : ℕ) :
    ShapeDiscrepancy (range (m + 1))
      (categoricalCardMass m q) (independentCardMass m q)
      (2 * ((m : ℝ) * (m - 1 : ℕ) * q ^ 2)) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hε : 0 ≤ (m : ℝ) * (m - 1 : ℕ) * q ^ 2 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg _))
      (sq_nonneg q)
  refine ⟨mul_nonneg h2 hε, ?_⟩
  rw [massL1_eq_two_tvHalf, tvHalf_cardMass, categoricalVsIndependentTV]
  exact mul_le_mul_of_nonneg_left (categorical_tv_le hq0 hq1 m) h2

theorem shapeDiscrepancy_categorical_mul {q ρ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (m n : ℕ)
    (hn : (n : ℝ) * ρ ≤ 1) :
    ShapeDiscrepancy (range (m + 1) ×ˢ range (n + 1))
      (fun p => categoricalCardMass m q p.1 * categoricalCardMass n ρ p.2)
      (fun p => independentCardMass m q p.1 * independentCardMass n ρ p.2)
      (2 * ((m : ℝ) * (m - 1 : ℕ) * q ^ 2) +
        2 * ((n : ℝ) * (n - 1 : ℕ) * ρ ^ 2)) :=
  shapeDiscrepancy_mul
    (fun k _ => categoricalCardMass_nonneg hρ0 hn k)
    (fun k _ => independentCardMass_nonneg hq0 hq1 m k)
    (categoricalCardMass_sum n ρ) (independentCardMass_sum m q)
    (shapeDiscrepancy_categorical hq0 hq1 m)
    (shapeDiscrepancy_categorical hρ0 hρ1 n)

/-- Bernoulli thinning is a probability mass, so Coupling's product
lemma applies to a second independent coordinate. -/
theorem massL1_mul_bernoulliThin (A B : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (μ μ' : Finset ℕ → ℝ)
    (hμ'0 : ∀ a ∈ A.powerset, 0 ≤ μ' a)
    (hμ'1 : ∑ a ∈ A.powerset, μ' a = 1) :
    massL1 (A.powerset ×ˢ B.powerset)
      (fun p => μ p.1 * bernoulliThin B ρ hρ0 hρ1 p.2)
      (fun p => μ' p.1 * bernoulliThin B ρ hρ0 hρ1 p.2)
      ≤ massL1 A.powerset μ μ' := by
  have hprod :=
    massL1_mul_le A.powerset B.powerset μ μ'
      (bernoulliThin B ρ hρ0 hρ1) (bernoulliThin B ρ hρ0 hρ1)
      (fun b _ => bernoulliThin_nonneg B hρ0 hρ1 b) hμ'0
      (bernoulliThin_sum B hρ0 hρ1) hμ'1
  have hself :
      massL1 B.powerset (bernoulliThin B ρ hρ0 hρ1)
          (bernoulliThin B ρ hρ0 hρ1) = 0 :=
    massL1_self _ _
  have hrew :
      massL1 A.powerset μ μ' +
          massL1 B.powerset (bernoulliThin B ρ hρ0 hρ1)
            (bernoulliThin B ρ hρ0 hρ1) =
        massL1 A.powerset μ μ' := by
    rw [hself, add_zero]
  exact hprod.trans (le_of_eq hrew)

end PrimeGapNormality.Prime
