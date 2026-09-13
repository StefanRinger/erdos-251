import PrimeGapNormality.Prime.Coupling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Abstract Palm factorial-moment envelope

Finite discrete masses on a `Finset`, not a new measure-theory stack.
Palm joint survival is the product `∏ (1 - j q_i)` with Root-Palm
`q = 1/(p-1)`, not `1/p`. This is not an arithmetic large sieve and
not a count of actual primes (`rootedTupleCount` lives in `EndAPI` and
is unused here).

Independent Bernoulli thinning (`bernoulliThin`) is an exact comparison
for a fixed candidate set. The inclusion probability is computed in the
original product; there is no TV-error × unbounded-moment product.

The exponential concentration event that supplies `ε`, `A`, and `M` in
the model application is **not** proved here.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §§2–4,
  especially (2.1) and the abstract envelope in §4;
`lean/PRIME_ARCHITECTURE.md` ModelMoments;
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Finset

set_option maxHeartbeats 400000

/-! ### Bernoulli factor used in (2.1) -/

/-- If `1 ≤ n` and `n q ≤ 1` with `q ≥ 0`, then `q ≤ 1`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem q_le_one_of_nat_mul {q : ℝ} {n : ℕ} (hn : 1 ≤ n) (hq0 : 0 ≤ q)
    (h : (n : ℝ) * q ≤ 1) : q ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) * q ≤ (n : ℝ) * q := mul_le_mul_of_nonneg_right hn1 hq0
  linarith

/-- Paper (2.1): `1 - j t ≤ (1-t)^j` whenever `0 ≤ t` and `0 ≤ j t ≤ 1`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem one_sub_mul_le_one_sub_pow {t : ℝ} (ht : 0 ≤ t) (j : ℕ)
    (hjt : (j : ℝ) * t ≤ 1) : 1 - (j : ℝ) * t ≤ (1 - t) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : (j : ℝ) * t ≤ 1 := by
      have hmono : (j : ℝ) * t ≤ (j.succ : ℝ) * t :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ j)) ht
      exact hmono.trans hjt
    have h1t : t ≤ 1 := by
      have hpos : (1 : ℝ) ≤ (j.succ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.succ_pos j)
      have : (1 : ℝ) * t ≤ (j.succ : ℝ) * t :=
        mul_le_mul_of_nonneg_right hpos ht
      linarith
    have hfac : 0 ≤ 1 - t := sub_nonneg.mpr h1t
    have hmul : (1 - t) * (1 - (j : ℝ) * t) ≤ (1 - t) * (1 - t) ^ j :=
      mul_le_mul_of_nonneg_left (ih hj) hfac
    have hpow : (1 - t) * (1 - t) ^ j = (1 - t) ^ j.succ := (pow_succ' (1 - t) j).symm
    have halg : 1 - (j.succ : ℝ) * t ≤ (1 - t) * (1 - (j : ℝ) * t) := by
      have hsq : 0 ≤ (j : ℝ) * t * t :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg j) ht) ht
      have hexp :
          (1 - t) * (1 - (j : ℝ) * t) - (1 - (j.succ : ℝ) * t) = (j : ℝ) * t * t := by
        simp [Nat.cast_succ]
        ring
      linarith
    exact halg.trans (hmul.trans (le_of_eq hpow))

/-! ### Finite Palm products (`q = 1/(p-1)`, not actual prime counts) -/

/-- One-point Palm survival `1 - q`. Paper's Euler factor at a later
modulus.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2.
Contract: API
Audit: GREEN -/
noncomputable def palmTheta {ι : Type*} (s : Finset ι) (q : ι → ℝ) : ℝ :=
  ∏ i ∈ s, (1 - q i)

/-- Joint Palm survival of a marked `j`-set: `∏ (1 - j q_i)`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2.
Contract: API
Audit: GREEN -/
noncomputable def palmJointSurvive {ι : Type*} (s : Finset ι) (q : ι → ℝ) (j : ℕ) : ℝ :=
  ∏ i ∈ s, (1 - (j : ℝ) * q i)

/-- Root-Palm hit probability `q = 1/(p-1)` at an integer `p ≥ 2`.
Defined for every `p : ℕ`; lemmas restrict to `2 ≤ p`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2;
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN -/
noncomputable def palmHitProb (p : ℕ) : ℝ :=
  1 / ((p : ℝ) - 1)

/-- Finite product `θ = ∏ (1 - 1/(p-1))` over a later-modulus set.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2.
Contract: API
Audit: GREEN -/
noncomputable def palmThetaPrimes (ps : Finset ℕ) : ℝ :=
  palmTheta ps palmHitProb

/-- Finite joint Palm survival `∏ (1 - j/(p-1))`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2.
Contract: API
Audit: GREEN -/
noncomputable def palmJointSurvivePrimes (ps : Finset ℕ) (j : ℕ) : ℝ :=
  palmJointSurvive ps palmHitProb j

theorem palmTheta_empty {ι : Type*} (q : ι → ℝ) : palmTheta (∅ : Finset ι) q = 1 :=
  prod_empty

theorem palmJointSurvive_empty {ι : Type*} (q : ι → ℝ) (j : ℕ) :
    palmJointSurvive (∅ : Finset ι) q j = 1 :=
  prod_empty

theorem palmJointSurvive_zero {ι : Type*} (s : Finset ι) (q : ι → ℝ) :
    palmJointSurvive s q 0 = 1 := by
  simp [palmJointSurvive]

theorem palmHitProb_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ palmHitProb p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact div_nonneg zero_le_one hden

theorem palmHitProb_le_one {p : ℕ} (hp : 2 ≤ p) : palmHitProb p ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hden : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact (div_le_one hpos).mpr hden

theorem palmHitProb_mul_le_one {p j : ℕ} (hp : 2 ≤ p) (hj : j ≤ p - 1) :
    (j : ℝ) * palmHitProb p ≤ 1 := by
  have hp1 : 1 ≤ p := Nat.le_of_succ_le hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
  have hjR : (j : ℝ) ≤ (p : ℝ) - 1 := by
    have : (j : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hj
    rwa [hcast] at this
  have hdiv : (j : ℝ) / ((p : ℝ) - 1) ≤ 1 := (div_le_one hden).mpr hjR
  have hrew : (j : ℝ) * palmHitProb p = (j : ℝ) / ((p : ℝ) - 1) := by
    simp [palmHitProb, div_eq_mul_inv]
  rwa [hrew]

/-- Joint Palm survival is at most `θ^j`. This is the product form of
(2.1); each factor uses `one_sub_mul_le_one_sub_pow`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem palmJointSurvive_le_theta_pow {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (q : ι → ℝ) (j : ℕ)
    (hq0 : ∀ i ∈ s, 0 ≤ q i) (hqj : ∀ i ∈ s, (j : ℝ) * q i ≤ 1) :
    palmJointSurvive s q j ≤ palmTheta s q ^ j := by
  cases j with
  | zero => simp [palmJointSurvive, palmTheta]
  | succ j =>
    have hq1 : ∀ i ∈ s, q i ≤ 1 := fun i hi =>
      q_le_one_of_nat_mul (Nat.succ_le_of_lt (Nat.succ_pos j)) (hq0 i hi) (hqj i hi)
    induction s using Finset.induction_on with
    | empty => simp [palmJointSurvive, palmTheta]
    | insert a s ha ih =>
      have hq0a : 0 ≤ q a := hq0 a (mem_insert_self a s)
      have hqja : (j.succ : ℝ) * q a ≤ 1 := hqj a (mem_insert_self a s)
      have hq0s : ∀ i ∈ s, 0 ≤ q i := fun i hi => hq0 i (mem_insert_of_mem hi)
      have hqjs : ∀ i ∈ s, (j.succ : ℝ) * q i ≤ 1 :=
        fun i hi => hqj i (mem_insert_of_mem hi)
      have hq1s : ∀ i ∈ s, q i ≤ 1 := fun i hi => hq1 i (mem_insert_of_mem hi)
      have ih' := ih hq0s hqjs hq1s
      have hpt := one_sub_mul_le_one_sub_pow hq0a j.succ hqja
      have hfac : 0 ≤ 1 - (j.succ : ℝ) * q a := sub_nonneg.mpr hqja
      have hprod0 : 0 ≤ palmJointSurvive s q j.succ :=
        prod_nonneg fun i hi => sub_nonneg.mpr (hqjs i hi)
      have hpow0 : 0 ≤ (1 - q a) ^ j.succ :=
        pow_nonneg (sub_nonneg.mpr (hq1 a (mem_insert_self a s))) _
      simp only [palmJointSurvive, palmTheta, prod_insert ha, mul_pow]
      exact mul_le_mul hpt ih' hprod0 hpow0

/-- Specialisation of `palmJointSurvive_le_theta_pow` to `q = 1/(p-1)`
on integers `p ≥ 2` with `j ≤ p-1` (so every factor is nonnegative).

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem palmJointSurvivePrimes_le_theta_pow (ps : Finset ℕ) (j : ℕ)
    (hps : ∀ p ∈ ps, 2 ≤ p) (hj : ∀ p ∈ ps, j ≤ p - 1) :
    palmJointSurvivePrimes ps j ≤ palmThetaPrimes ps ^ j :=
  palmJointSurvive_le_theta_pow ps palmHitProb j
    (fun p hp => palmHitProb_nonneg (hps p hp))
    (fun p hp => palmHitProb_mul_le_one (hps p hp) (hj p hp))

theorem palmJointSurvive_nonneg {ι : Type*} (s : Finset ι) (q : ι → ℝ) (j : ℕ)
    (hqj : ∀ i ∈ s, (j : ℝ) * q i ≤ 1) : 0 ≤ palmJointSurvive s q j :=
  prod_nonneg fun i hi => sub_nonneg.mpr (hqj i hi)

theorem palmTheta_nonneg {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq1 : ∀ i ∈ s, q i ≤ 1) : 0 ≤ palmTheta s q :=
  prod_nonneg fun i hi => sub_nonneg.mpr (hq1 i hi)

/-! ### Choose versus power / factorial -/

/-- `C(n,j) ≤ n^j / j!` over `ℝ`, from mathlib `Nat.choose_le_pow_div`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1);
`lean/PRIME_MATHLIB.md` binomials.
Contract: API
Audit: GREEN -/
theorem choose_le_pow_div_real (n j : ℕ) :
    (n.choose j : ℝ) ≤ (n : ℝ) ^ j / (j.factorial : ℝ) := by
  simpa [Nat.cast_pow] using (Nat.choose_le_pow_div (α := ℝ) j n)

/-! ### Finite-mass moments -/

/-- Power moment `∑ μ(i) N(i)^j`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §4.
Contract: API
Audit: GREEN -/
noncomputable def massPowerMoment {ι : Type*} (s : Finset ι) (μ N : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ s, μ i * N i ^ j

/-- Factorial counting moment `∑ μ(i) C(N(i), j)`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §4.
Contract: API
Audit: GREEN -/
noncomputable def massChooseMoment {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (N : ι → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ s, μ i * (N i).choose j

theorem massPowerMoment_mul_pow {ι : Type*} (s : Finset ι) (μ N : ι → ℝ)
    (θ : ℝ) (j : ℕ) :
    θ ^ j * massPowerMoment s μ N j = massPowerMoment s μ (fun i => θ * N i) j := by
  simp only [massPowerMoment, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem massChooseMoment_nonneg {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (N : ι → ℕ) (j : ℕ) (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    0 ≤ massChooseMoment s μ N j :=
  sum_nonneg fun i hi => mul_nonneg (hμ i hi) (Nat.cast_nonneg _)

/-- `E[C(N,j)] ≤ E[N^j] / j!` on a nonnegative finite mass.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem massChooseMoment_le_powerMoment {ι : Type*} (s : Finset ι)
    (μ : ι → ℝ) (N : ι → ℕ) (j : ℕ) (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    massChooseMoment s μ N j
      ≤ massPowerMoment s μ (fun i => (N i : ℝ)) j / (j.factorial : ℝ) := by
  have hpt : ∀ i ∈ s,
      μ i * (N i).choose j
        ≤ μ i * ((N i : ℝ) ^ j / (j.factorial : ℝ)) := fun i hi =>
    mul_le_mul_of_nonneg_left (choose_le_pow_div_real (N i) j) (hμ i hi)
  have hsum := sum_le_sum hpt
  have hdiv :
      ∑ i ∈ s, μ i * ((N i : ℝ) ^ j / (j.factorial : ℝ))
        = massPowerMoment s μ (fun i => (N i : ℝ)) j / (j.factorial : ℝ) := by
    have hrw : ∀ i ∈ s,
        μ i * ((N i : ℝ) ^ j / (j.factorial : ℝ))
          = (μ i * (N i : ℝ) ^ j) * (j.factorial : ℝ)⁻¹ := fun i _ => by
      ring
    rw [sum_congr rfl hrw, ← sum_mul]
    simp [massPowerMoment, div_eq_mul_inv, mul_comm]
  exact hsum.trans (le_of_eq hdiv)

/-! ### Independent Bernoulli comparison (no TV remainder) -/

/-- Pointwise: adjoining a fixed included `H` factors out `ρ^|H|`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2;
`lean/PRIME_SIGNATURES.md` Coupling `bernoulliThin`.
Contract: API
Audit: GREEN -/
theorem bernoulliThin_union_sdiff (A H C : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hHA : H ⊆ A) (hC : C ⊆ A \ H) :
    bernoulliThin A ρ hρ0 hρ1 (H ∪ C)
      = ρ ^ H.card * bernoulliThin (A \ H) ρ hρ0 hρ1 C := by
  have hdisj : Disjoint H C := Disjoint.mono_right hC (disjoint_sdiff (s := H) (t := A))
  have hUA : H ∪ C ⊆ A := by
    intro x hx
    rcases mem_union.mp hx with hxH | hxC
    · exact hHA hxH
    · exact (mem_sdiff.mp (hC hxC)).1
  have hcardUC : (H ∪ C).card = H.card + C.card := card_union_of_disjoint hdisj
  have hcardDiff : A.card - (H.card + C.card) = (A \ H).card - C.card := by
    rw [Nat.sub_add_eq, card_sdiff_of_subset hHA]
  rw [bernoulliThin_eq A hρ0 hρ1 hUA, bernoulliThin_eq (A \ H) hρ0 hρ1 hC, hcardUC,
    pow_add, hcardDiff, mul_assoc]

/-- Inclusion mass of a fixed `H ⊆ A` under independent thinning is
`ρ^|H|`. This is the independent comparison, not a Palm TV error.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §2.
Contract: API
Audit: GREEN -/
theorem bernoulliThin_superset_mass (A H : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hHA : H ⊆ A) :
    ∑ B ∈ A.powerset.filter (fun B => H ⊆ B), bernoulliThin A ρ hρ0 hρ1 B
      = ρ ^ H.card := by
  have hdisjC : ∀ C ∈ (A \ H).powerset,
      Disjoint H C := fun C hC =>
    Disjoint.mono_right (mem_powerset.mp hC) (disjoint_sdiff (s := H) (t := A))
  have hbij :
      ∑ B ∈ A.powerset.filter (fun B => H ⊆ B), bernoulliThin A ρ hρ0 hρ1 B
        = ∑ C ∈ (A \ H).powerset, bernoulliThin A ρ hρ0 hρ1 (H ∪ C) := by
    refine sum_bij'
      (fun B _ => B \ H)
      (fun C _ => H ∪ C)
      ?_ ?_ ?_ ?_ ?_
    · intro B hB
      have hBA : B ⊆ A := mem_powerset.mp (mem_filter.mp hB).1
      exact mem_powerset.mpr (sdiff_subset_sdiff hBA (subset_refl H))
    · intro C hC
      have hCAH : C ⊆ A \ H := mem_powerset.mp hC
      have hUA : H ∪ C ⊆ A := by
        intro x hx
        rcases mem_union.mp hx with hxH | hxC
        · exact hHA hxH
        · exact (mem_sdiff.mp (hCAH hxC)).1
      exact mem_filter.mpr ⟨mem_powerset.mpr hUA, subset_union_left⟩
    · intro B hB
      exact union_sdiff_of_subset (mem_filter.mp hB).2
    · intro C hC
      exact union_sdiff_cancel_left (hdisjC C hC)
    · intro B hB
      have hHB : H ⊆ B := (mem_filter.mp hB).2
      rw [union_sdiff_of_subset hHB]
  have hpt : ∀ C ∈ (A \ H).powerset,
      bernoulliThin A ρ hρ0 hρ1 (H ∪ C)
        = ρ ^ H.card * bernoulliThin (A \ H) ρ hρ0 hρ1 C := fun C hC =>
    bernoulliThin_union_sdiff A H C hρ0 hρ1 hHA (mem_powerset.mp hC)
  rw [hbij, sum_congr rfl hpt, ← mul_sum, bernoulliThin_sum (A \ H) hρ0 hρ1, mul_one]

/-- Exact independent factorial moment: `E[C(|B|,j)] = ρ^j C(|A|,j)`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1);
`lean/PRIME_SIGNATURES.md` Coupling.
Contract: API
Audit: GREEN -/
theorem bernoulliThin_choose_moment (A : Finset ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (j : ℕ) :
    ∑ B ∈ A.powerset, bernoulliThin A ρ hρ0 hρ1 B * (B.card.choose j : ℝ)
      = ρ ^ j * (A.card.choose j : ℝ) := by
  have hBchoose : ∀ B ∈ A.powerset,
      (B.card.choose j : ℝ)
        = ∑ H ∈ A.powersetCard j, if H ⊆ B then (1 : ℝ) else 0 := by
    intro B hB
    have hBA : B ⊆ A := mem_powerset.mp hB
    have hfilter :
        (A.powersetCard j).filter (fun H => H ⊆ B) = B.powersetCard j := by
      ext H
      simp only [mem_filter, mem_powersetCard]
      constructor
      · intro h
        exact ⟨h.2, h.1.2⟩
      · intro h
        exact ⟨⟨h.1.trans hBA, h.2⟩, h.1⟩
    calc
      (B.card.choose j : ℝ)
          = ∑ H ∈ B.powersetCard j, (1 : ℝ) := by
            simp [sum_const, nsmul_eq_mul, card_powersetCard]
      _ = ∑ H ∈ (A.powersetCard j).filter (fun H => H ⊆ B), (1 : ℝ) := by
            rw [hfilter]
      _ = ∑ H ∈ A.powersetCard j, if H ⊆ B then (1 : ℝ) else 0 := by
            rw [sum_filter]
  have h1 :
      ∑ B ∈ A.powerset, bernoulliThin A ρ hρ0 hρ1 B * (B.card.choose j : ℝ)
        = ∑ B ∈ A.powerset, ∑ H ∈ A.powersetCard j,
            bernoulliThin A ρ hρ0 hρ1 B * (if H ⊆ B then (1 : ℝ) else 0) := by
    refine sum_congr rfl fun B hB => ?_
    rw [hBchoose B hB, mul_sum]
  have hswap :
      ∑ B ∈ A.powerset, ∑ H ∈ A.powersetCard j,
          bernoulliThin A ρ hρ0 hρ1 B * (if H ⊆ B then (1 : ℝ) else 0)
        = ∑ H ∈ A.powersetCard j, ∑ B ∈ A.powerset.filter (fun B => H ⊆ B),
            bernoulliThin A ρ hρ0 hρ1 B := by
    rw [sum_comm]
    refine sum_congr rfl fun H _ => ?_
    have : ∑ B ∈ A.powerset,
        bernoulliThin A ρ hρ0 hρ1 B * (if H ⊆ B then (1 : ℝ) else 0)
        = ∑ B ∈ A.powerset,
            if H ⊆ B then bernoulliThin A ρ hρ0 hρ1 B else 0 := by
      refine sum_congr rfl fun B _ => ?_
      simp [mul_ite, mul_one, mul_zero]
    rw [this, ← sum_filter]
  rw [h1, hswap]
  have hH : ∀ H ∈ A.powersetCard j,
      ∑ B ∈ A.powerset.filter (fun B => H ⊆ B), bernoulliThin A ρ hρ0 hρ1 B
        = ρ ^ j := by
    intro H hH
    have hHA : H ⊆ A := (mem_powersetCard.mp hH).1
    have hcard : H.card = j := (mem_powersetCard.mp hH).2
    rw [bernoulliThin_superset_mass A H hρ0 hρ1 hHA, hcard]
  rw [sum_congr rfl hH, sum_const, nsmul_eq_mul, card_powersetCard, mul_comm]

/-! ### Good/bad power envelope (§4) -/

/-- Split `E[(θ N)^j]` across a good set of mass `≥ 1-ε` and a uniform
bound `θ N ≤ M` everywhere. No probability monad: finite masses.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §4.
Contract: API
Audit: GREEN -/
theorem massPowerMoment_scale_envelope {ι : Type*} [DecidableEq ι] (s g : Finset ι)
    (μ N : ι → ℝ) {θ ε A M : ℝ} (j : ℕ)
    (hθ : 0 ≤ θ) (_hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hN : ∀ i ∈ s, 0 ≤ N i)
    (hμ1 : ∑ i ∈ s, μ i ≤ 1) (hg : g ⊆ s)
    (hbad : ∑ i ∈ s \ g, μ i ≤ ε)
    (hgood : ∀ i ∈ g, θ * N i ≤ A)
    (hall : ∀ i ∈ s, θ * N i ≤ M) :
    massPowerMoment s μ (fun i => θ * N i) j ≤ A ^ j + ε * M ^ j := by
  have hAj : 0 ≤ A ^ j := pow_nonneg hA j
  have hMj : 0 ≤ M ^ j := pow_nonneg hM j
  have hsplit :
      massPowerMoment s μ (fun i => θ * N i) j
        = ∑ i ∈ g, μ i * (θ * N i) ^ j
          + ∑ i ∈ s \ g, μ i * (θ * N i) ^ j := by
    unfold massPowerMoment
    rw [← sum_sdiff hg, add_comm]
  have hgoodsum :
      ∑ i ∈ g, μ i * (θ * N i) ^ j ≤ A ^ j := by
    have hpt : ∀ i ∈ g, μ i * (θ * N i) ^ j ≤ μ i * A ^ j := by
      intro i hi
      have hiS : i ∈ s := hg hi
      have hbound : (θ * N i) ^ j ≤ A ^ j :=
        pow_le_pow_left₀ (mul_nonneg hθ (hN i hiS)) (hgood i hi) j
      exact mul_le_mul_of_nonneg_left hbound (hμ i hiS)
    have hμg : ∑ i ∈ g, μ i ≤ 1 :=
      (sum_le_sum_of_subset_of_nonneg hg fun i hi _ => hμ i hi).trans hμ1
    calc
      ∑ i ∈ g, μ i * (θ * N i) ^ j
          ≤ ∑ i ∈ g, μ i * A ^ j := sum_le_sum hpt
      _ = (∑ i ∈ g, μ i) * A ^ j := by simp [← sum_mul]
      _ ≤ 1 * A ^ j := mul_le_mul_of_nonneg_right hμg hAj
      _ = A ^ j := one_mul _
  have hbadsum :
      ∑ i ∈ s \ g, μ i * (θ * N i) ^ j ≤ ε * M ^ j := by
    have hpt : ∀ i ∈ s \ g, μ i * (θ * N i) ^ j ≤ μ i * M ^ j := by
      intro i hi
      have hiS : i ∈ s := (mem_sdiff.mp hi).1
      have hbound : (θ * N i) ^ j ≤ M ^ j :=
        pow_le_pow_left₀ (mul_nonneg hθ (hN i hiS)) (hall i hiS) j
      exact mul_le_mul_of_nonneg_left hbound (hμ i hiS)
    calc
      ∑ i ∈ s \ g, μ i * (θ * N i) ^ j
          ≤ ∑ i ∈ s \ g, μ i * M ^ j := sum_le_sum hpt
      _ = (∑ i ∈ s \ g, μ i) * M ^ j := by simp [← sum_mul]
      _ ≤ ε * M ^ j := mul_le_mul_of_nonneg_right hbad hMj
  rw [hsplit]
  exact add_le_add hgoodsum hbadsum

/-- Abstract §4 envelope: if `Q ≤ θ^j E[N0^j] / j!` and `θ N0 ≤ A` on a
good set of complementary mass `≤ ε` while `θ N0 ≤ M` everywhere, then
`Q ≤ (A^j + ε M^j) / j!`.

The good-event bound is written as `θ N0 ≤ A` (no division by `θ`), so
the `θ = 0` case is included. `g` is the good set; `s \ g` is bad.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §4.
Contract: API
Audit: GREEN -/
theorem factorialMoment_envelope {ι : Type*} [DecidableEq ι] (s g : Finset ι)
    (μ N : ι → ℝ) {θ ε A M Q : ℝ} (j : ℕ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hN : ∀ i ∈ s, 0 ≤ N i)
    (hμ1 : ∑ i ∈ s, μ i ≤ 1) (hg : g ⊆ s)
    (hbad : ∑ i ∈ s \ g, μ i ≤ ε)
    (hgood : ∀ i ∈ g, θ * N i ≤ A)
    (hall : ∀ i ∈ s, θ * N i ≤ M)
    (hQ : Q ≤ θ ^ j * massPowerMoment s μ N j / (j.factorial : ℝ)) :
    Q ≤ (A ^ j + ε * M ^ j) / (j.factorial : ℝ) := by
  have hscale := massPowerMoment_mul_pow s μ N θ j
  have henv := massPowerMoment_scale_envelope s g μ N j hθ hε hA hM hμ hN hμ1 hg
    hbad hgood hall
  have hdiv :
      θ ^ j * massPowerMoment s μ N j / (j.factorial : ℝ)
        ≤ (A ^ j + ε * M ^ j) / (j.factorial : ℝ) := by
    rw [hscale]
    exact div_le_div_of_nonneg_right henv (Nat.cast_nonneg _)
  exact hQ.trans hdiv

/-! ### Mixed Palm form of (2.1) -/

/-- Mixing: `E[C(N0,j)] ∏(1-j q) ≤ θ^j E[C(N0,j)]`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem palm_chooseMoment_le_theta_pow {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (μ : ι → ℝ) (N : ι → ℕ) (t : Finset κ) (q : κ → ℝ)
    (j : ℕ) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hq0 : ∀ i ∈ t, 0 ≤ q i) (hqj : ∀ i ∈ t, (j : ℝ) * q i ≤ 1) :
    palmJointSurvive t q j * massChooseMoment s μ N j
      ≤ palmTheta t q ^ j * massChooseMoment s μ N j :=
  mul_le_mul_of_nonneg_right
    (palmJointSurvive_le_theta_pow t q j hq0 hqj)
    (massChooseMoment_nonneg s μ N j hμ)

/-- (2.1) mixed: Palm joint survival times `E[C(N0,j)]` is at most
`θ^j E[N0^j] / j!`.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` (2.1).
Contract: API
Audit: GREEN -/
theorem palm_chooseMoment_le_pow_div {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (μ : ι → ℝ) (N : ι → ℕ) (t : Finset κ) (q : κ → ℝ)
    (j : ℕ) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hq0 : ∀ i ∈ t, 0 ≤ q i) (hqj : ∀ i ∈ t, (j : ℝ) * q i ≤ 1) :
    palmJointSurvive t q j * massChooseMoment s μ N j
      ≤ palmTheta t q ^ j
          * massPowerMoment s μ (fun i => (N i : ℝ)) j
          / (j.factorial : ℝ) := by
  have h1 := palm_chooseMoment_le_theta_pow s μ N t q j hμ hq0 hqj
  have h2 := massChooseMoment_le_powerMoment s μ N j hμ
  have hθj : 0 ≤ palmTheta t q ^ j := by
    cases j with
    | zero => simp
    | succ j =>
      have hq1 : ∀ i ∈ t, q i ≤ 1 := fun i hi =>
        q_le_one_of_nat_mul (Nat.succ_le_of_lt (Nat.succ_pos j)) (hq0 i hi) (hqj i hi)
      exact pow_nonneg (palmTheta_nonneg t q hq1) _
  have hmul := mul_le_mul_of_nonneg_left h2 hθj
  have hring :
      palmTheta t q ^ j
          * (massPowerMoment s μ (fun i => (N i : ℝ)) j / (j.factorial : ℝ))
        = palmTheta t q ^ j
            * massPowerMoment s μ (fun i => (N i : ℝ)) j
            / (j.factorial : ℝ) := by
    ring
  exact h1.trans (hmul.trans (le_of_eq hring))

/-- Packaged Palm envelope: the mixed (2.1) moment is bounded by
`(A^j + ε M^j) / j!` once `θ N0 ≤ A` on the good set and `θ N0 ≤ M`
everywhere, with `θ = ∏(1-q)`.

Does **not** prove the exponential concentration event that produces
`g`, `ε`, `A`, and `M` in the model application.

Source: `rounds/round104/08_model_moments_without_large_sieve.md` §§2–4.
Contract: API
Audit: GREEN -/
theorem palm_chooseMoment_envelope {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s g : Finset ι) (μ : ι → ℝ) (N : ι → ℕ) (t : Finset κ) (q : κ → ℝ)
    {ε A M : ℝ} (j : ℕ)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hμ1 : ∑ i ∈ s, μ i ≤ 1) (hg : g ⊆ s)
    (hbad : ∑ i ∈ s \ g, μ i ≤ ε)
    (hq0 : ∀ i ∈ t, 0 ≤ q i) (hq1 : ∀ i ∈ t, q i ≤ 1)
    (hqj : ∀ i ∈ t, (j : ℝ) * q i ≤ 1)
    (hgood : ∀ i ∈ g, palmTheta t q * (N i : ℝ) ≤ A)
    (hall : ∀ i ∈ s, palmTheta t q * (N i : ℝ) ≤ M) :
    palmJointSurvive t q j * massChooseMoment s μ N j
      ≤ (A ^ j + ε * M ^ j) / (j.factorial : ℝ) := by
  have hθ : 0 ≤ palmTheta t q := palmTheta_nonneg t q hq1
  have hN : ∀ i ∈ s, 0 ≤ (N i : ℝ) := fun i _ => Nat.cast_nonneg _
  have h21 := palm_chooseMoment_le_pow_div s μ N t q j hμ hq0 hqj
  exact h21.trans
    (factorialMoment_envelope s g μ (fun i => (N i : ℝ)) j hθ hε hA hM hμ hN
      hμ1 hg hbad hgood hall (le_of_eq rfl))

end PrimeGapNormality.Prime
