import PrimeGapNormality.BFree.Definitions
import PrimeGapNormality.BFree.Series
import PrimeGapNormality.BFree.CanonicalTransfer
import PrimeGapNormality.BFree.Irrationality
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Squarefree integers as an admissible family

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9;
`rounds/round89/03_gpt_core_audit_and_lean_architecture.md` §3.
Contract: Squarefree application
Audit: GREEN (density and identification of the set)
-/

namespace PrimeGapNormality.BFree

open Finset Function

/-- Exclusion moduli `p_i²`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9.
Contract: Squarefree
Audit: GREEN -/
noncomputable def squareModuli : ℕ → ℕ := fun i => Nat.nth Nat.Prime i ^ 2

theorem squareModuli_two_le (i : ℕ) : 2 ≤ squareModuli i := by
  have hp : 2 ≤ Nat.nth Nat.Prime i := (Nat.prime_nth_prime i).two_le
  have h4 : 4 ≤ Nat.nth Nat.Prime i * Nat.nth Nat.Prime i := Nat.mul_le_mul hp hp
  have h2 : 2 ≤ 4 := by decide
  simpa [squareModuli, pow_two] using h2.trans h4

theorem squareModuli_pairwise_coprime :
    Pairwise fun i j => Nat.Coprime (squareModuli i) (squareModuli j) := by
  intro i j hij
  have hi : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
  have hj : Nat.Prime (Nat.nth Nat.Prime j) := Nat.prime_nth_prime j
  have hne : Nat.nth Nat.Prime i ≠ Nat.nth Nat.Prime j := by
    intro h
    exact hij ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h)
  have hcop : Nat.Coprime (Nat.nth Nat.Prime i) (Nat.nth Nat.Prime j) :=
    (Nat.coprime_primes hi hj).2 hne
  simpa [squareModuli] using
    (Nat.coprime_pow_left_iff (by decide : 0 < 2) _ _).2
      ((Nat.coprime_pow_right_iff (by decide : 0 < 2) _ _).2 hcop)

/-- Inverse squares of odd integers `2k+1` are dominated by the telescoping term.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9.
Contract: Squarefree
Audit: GREEN -/
theorem inv_sq_odd_le_telescope {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) / (2 * k + 1) ^ 2 ≤ (1 / 4 : ℝ) * (1 / k - 1 / (k + 1)) := by
  have hlt : (4 : ℝ) * k * (k + 1) < (2 * k + 1 : ℝ) ^ 2 := by
    have : (2 * k + 1 : ℝ) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    linarith
  have hle : (1 : ℝ) / (2 * k + 1 : ℝ) ^ 2 ≤ 1 / (4 * k * (k + 1)) :=
    one_div_le_one_div_of_le (by positivity) hlt.le
  have hid : (1 : ℝ) / (4 * k * (k + 1)) = (1 / 4) * (1 / k - 1 / (k + 1)) := by
    field_simp
    ring
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = (2 * k + 1 : ℝ) := by simp
  simpa [hcast] using hle.trans_eq hid

/-- Telescoping harmonic differences from `2` to `N`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9.
Contract: Squarefree
Audit: GREEN -/
theorem sum_inv_sub_inv_Ico {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Ico 2 N, ((1 : ℝ) / k - 1 / (k + 1)) = (1 : ℝ) / 2 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn, ih]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_succ n
    simp [hcast]

theorem sum_inv_sub_inv_Ico_le (N : ℕ) :
    ∑ k ∈ Ico 2 N, ((1 : ℝ) / k - 1 / (k + 1)) ≤ (1 / 2 : ℝ) := by
  by_cases hN : 2 ≤ N
  · rw [sum_inv_sub_inv_Ico hN]
    have : 0 ≤ (1 : ℝ) / N := by positivity
    linarith
  · have : Ico 2 N = ∅ := Ico_eq_empty_iff.mpr (by omega)
    simp [this]

/-- Finite prime-square partial sums stay below `35/72`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9.
Contract: Squarefree
Audit: GREEN -/
theorem sum_primesBelow_inv_sq_le (N : ℕ) :
    ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p ^ 2 ≤ (35 / 72 : ℝ) := by
  classical
  let s23 : Finset ℕ := (Nat.primesBelow N).filter (fun p => p = 2 ∨ p = 3)
  let srest : Finset ℕ := (Nat.primesBelow N).filter (fun p => 5 ≤ p)
  have hdisj : Disjoint s23 srest := by
    rw [disjoint_left]
    intro p hp23 hprest
    simp only [s23, srest, mem_filter] at hp23 hprest
    omega
  have hunion : s23 ∪ srest = Nat.primesBelow N := by
    ext p
    simp only [mem_union, mem_filter, s23, srest]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hp
      have hP : Nat.Prime p := Nat.prime_of_mem_primesBelow hp
      have h2le : 2 ≤ p := hP.two_le
      by_cases h2 : p = 2
      · exact Or.inl ⟨hp, Or.inl h2⟩
      · by_cases h3 : p = 3
        · exact Or.inl ⟨hp, Or.inr h3⟩
        · have h4 : 4 ≤ p := by omega
          have hne4 : p ≠ 4 := by
            intro h
            subst h
            exact absurd hP (by decide : ¬ Nat.Prime 4)
          have h5 : 5 ≤ p := by omega
          exact Or.inr ⟨hp, h5⟩
  have hsum :
      ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p ^ 2 =
        ∑ p ∈ s23, (1 : ℝ) / p ^ 2 + ∑ p ∈ srest, (1 : ℝ) / p ^ 2 := by
    rw [← hunion, sum_union hdisj]
  have h23 : ∑ p ∈ s23, (1 : ℝ) / p ^ 2 ≤ (1 / 4 : ℝ) + 1 / 9 := by
    have hs : s23 ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      simp only [s23, mem_filter] at hp
      rcases hp.2 with h | h <;> simp [h]
    have hle : ∑ p ∈ s23, (1 : ℝ) / p ^ 2 ≤
        ∑ p ∈ ({2, 3} : Finset ℕ), (1 : ℝ) / p ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    refine hle.trans_eq ?_
    rw [sum_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)), sum_singleton]
    norm_num
  have hrest :
      ∑ p ∈ srest, (1 : ℝ) / p ^ 2 ≤ (1 / 8 : ℝ) := by
    let oddOf : ℕ → ℕ := fun k => 2 * k + 1
    have hsub : srest ⊆ (Ico 2 N).image oddOf := by
      intro p hp
      simp only [srest, mem_filter, Nat.mem_primesBelow] at hp
      obtain ⟨⟨hpN, hpP⟩, h5⟩ := hp
      have hne2 : p ≠ 2 := ne_of_gt (lt_of_lt_of_le (by decide : (2 : ℕ) < 5) h5)
      have hodd : p % 2 = 1 := hpP.eq_two_or_odd.resolve_left hne2
      have hdecomp : oddOf (p / 2) = p := by
        have hmod := Nat.div_add_mod p 2
        rw [hodd] at hmod
        exact hmod
      refine mem_image.mpr ⟨p / 2, ?_, hdecomp⟩
      rw [mem_Ico]
      refine ⟨?_, ?_⟩
      · have : 4 ≤ p := le_trans (by decide : 4 ≤ 5) h5
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 this
      · exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
          (hpN.trans_le (Nat.le_mul_of_pos_right N (by decide : 0 < 2)))
    have h1 :
        ∑ p ∈ srest, (1 : ℝ) / p ^ 2 ≤
          ∑ n ∈ (Ico 2 N).image oddOf, (1 : ℝ) / n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hinj : Set.InjOn oddOf (Ico 2 N) := by
      intro a _ b _ h
      dsimp [oddOf] at h
      omega
    have h2 : ∑ n ∈ (Ico 2 N).image oddOf, (1 : ℝ) / n ^ 2 =
        ∑ k ∈ Ico 2 N, (1 : ℝ) / (oddOf k) ^ 2 :=
      sum_image (g := oddOf) (f := fun n : ℕ => (1 : ℝ) / n ^ 2) hinj
    have h3 :
        ∑ k ∈ Ico 2 N, (1 : ℝ) / (oddOf k) ^ 2 ≤
          ∑ k ∈ Ico 2 N, (1 / 4 : ℝ) * ((1 : ℝ) / k - 1 / (k + 1)) := by
      refine sum_le_sum fun k hk => ?_
      have hk2 : 2 ≤ k := (mem_Ico.mp hk).1
      simpa [oddOf] using inv_sq_odd_le_telescope (le_trans (by decide : 1 ≤ 2) hk2)
    have h4 :
        ∑ k ∈ Ico 2 N, (1 / 4 : ℝ) * ((1 : ℝ) / k - 1 / (k + 1)) =
          (1 / 4 : ℝ) * ∑ k ∈ Ico 2 N, ((1 : ℝ) / k - (1 : ℝ) / (k + 1)) :=
      (mul_sum (Ico 2 N) (fun k => (1 : ℝ) / k - (1 : ℝ) / (k + 1)) (1 / 4 : ℝ)).symm
    have h5 := sum_inv_sub_inv_Ico_le N
    calc
      ∑ p ∈ srest, (1 : ℝ) / p ^ 2
        ≤ ∑ n ∈ (Ico 2 N).image oddOf, (1 : ℝ) / n ^ 2 := h1
      _ = ∑ k ∈ Ico 2 N, (1 : ℝ) / (oddOf k) ^ 2 := h2
      _ ≤ ∑ k ∈ Ico 2 N, (1 / 4 : ℝ) * ((1 : ℝ) / k - 1 / (k + 1)) := h3
      _ = (1 / 4 : ℝ) * ∑ k ∈ Ico 2 N, ((1 : ℝ) / k - (1 : ℝ) / (k + 1)) := h4
      _ ≤ (1 / 4 : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = 1 / 8 := by norm_num
  have h35 : (1 / 4 : ℝ) + 1 / 9 + 1 / 8 = 35 / 72 := by norm_num
  calc
    ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p ^ 2
      = ∑ p ∈ s23, (1 : ℝ) / p ^ 2 + ∑ p ∈ srest, (1 : ℝ) / p ^ 2 := hsum
    _ ≤ ((1 / 4 : ℝ) + 1 / 9) + 1 / 8 := add_le_add h23 hrest
    _ = 35 / 72 := h35

theorem primesBelow_nth_prime (n : ℕ) :
    Nat.primesBelow (Nat.nth Nat.Prime n) = (range n).image (Nat.nth Nat.Prime) := by
  ext p
  constructor
  · intro hp
    have hpP : Nat.Prime p := Nat.prime_of_mem_primesBelow hp
    have hplt : p < Nat.nth Nat.Prime n := Nat.lt_of_mem_primesBelow hp
    have hrange : p ∈ Set.range (Nat.nth Nat.Prime) := by
      rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
      exact hpP
    obtain ⟨k, rfl⟩ := Set.mem_range.mp hrange
    refine mem_image.mpr ⟨k, mem_range.mpr ?_, rfl⟩
    exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hplt
  · intro hp
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hp
    refine Nat.mem_primesBelow.mpr ⟨?_, Nat.prime_nth_prime k⟩
    exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr (mem_range.mp hk)

theorem sum_range_squareModuli (n : ℕ) :
    ∑ i ∈ range n, (1 : ℝ) / squareModuli i =
      ∑ p ∈ Nat.primesBelow (Nat.nth Nat.Prime n), (1 : ℝ) / p ^ 2 := by
  have hinj : Set.InjOn (Nat.nth Nat.Prime) (range n : Set ℕ) :=
    fun a _ b _ h => Nat.nth_injective Nat.infinite_setOfPred_prime h
  rw [primesBelow_nth_prime,
    sum_image (g := Nat.nth Nat.Prime) (f := fun p : ℕ => (1 : ℝ) / p ^ 2) hinj]
  simp [squareModuli]

/-- Elementary bound `∑_i p_i^{-2} ≤ 35/72`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9;
`03` §3.
Contract: Squarefree
Audit: GREEN -/
theorem tsum_prime_inv_sq_le : ∑' i, (1 : ℝ) / squareModuli i ≤ (35 / 72 : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun n => ?_
  rw [sum_range_squareModuli]
  exact sum_primesBelow_inv_sq_le _

theorem squareModuli_summable : Summable fun i => (1 : ℝ) / squareModuli i :=
  summable_of_sum_range_le (fun _ => by positivity) fun n =>
    (sum_range_squareModuli n).trans_le (sum_primesBelow_inv_sq_le _)

/-- The prime-square family is admissible.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: Squarefree
Audit: GREEN -/
noncomputable def squareModuliFamily : AdmissibleFamily :=
  ⟨squareModuli, squareModuli_two_le, squareModuli_pairwise_coprime, squareModuli_summable⟩

/-- Positive squarefree integers are exactly the `squareModuli` survivors.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §9.
Contract: Squarefree
Audit: GREEN -/
theorem bfree_squareModuli_iff (n : ℕ) :
    BFree squareModuliFamily n ↔ 0 < n ∧ Squarefree n := by
  constructor
  · intro ⟨hpos, hdiv⟩
    refine ⟨hpos, ?_⟩
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hsq
    obtain ⟨i, rfl⟩ : ∃ i, Nat.nth Nat.Prime i = p := by
      have : p ∈ Set.range (Nat.nth Nat.Prime) := by
        rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
        exact hp
      exact Set.mem_range.mp this
    exact hdiv i (by simpa [squareModuliFamily, squareModuli, pow_two] using hsq)
  · intro ⟨hpos, hsq⟩
    refine ⟨hpos, fun i hdiv => ?_⟩
    have hp : Nat.Prime (Nat.nth Nat.Prime i) := Nat.prime_nth_prime i
    have : Nat.nth Nat.Prime i * Nat.nth Nat.Prime i ∣ n := by
      simpa [squareModuliFamily, squareModuli, pow_two] using hdiv
    exact Nat.squarefree_iff_prime_squarefree.mp hsq _ hp this

theorem rho_squareModuli_ge : (37 / 72 : ℝ) ≤ rho squareModuliFamily := by
  have h := rho_ge_one_sub_tsum squareModuliFamily
  have hsum : ∑' i, (1 : ℝ) / squareModuliFamily.d i ≤ (35 / 72 : ℝ) := by
    simpa [squareModuliFamily] using tsum_prime_inv_sq_le
  linarith

theorem rho_squareModuli_gt_half : (1 / 2 : ℝ) < rho squareModuliFamily :=
  lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 37 / 72) rho_squareModuli_ge

theorem bfree_squareModuli_eq_squarefree :
    BFree squareModuliFamily = Squarefree := by
  funext n
  rw [eq_iff_iff, bfree_squareModuli_iff]
  constructor
  · exact And.right
  · intro h
    exact ⟨Nat.pos_of_ne_zero h.ne_zero, h⟩

theorem enum_squareModuli_eq_nth_squarefree (n : ℕ) :
    enum squareModuliFamily n = Nat.nth Squarefree n := by
  simp [enum, bfree_squareModuli_eq_squarefree]

/-- The ordered squarefree series is summable for every base `b ≥ 2`.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: Squarefree / C5
Audit: GREEN -/
theorem squarefree_posSeries_summable {b : ℕ} (hb : 2 ≤ b) :
    Summable fun n => (Nat.nth Squarefree n : ℝ) / (b : ℝ) ^ (n + 1) := by
  simpa [enum_squareModuli_eq_nth_squarefree] using
    posSeries_summable squareModuliFamily hb (enum_linear_bound squareModuliFamily)

/-- Squarefree position series is irrational for every base `b ≥ 2`.
No leftover `rho > 1/2` hypothesis.

Source: `lean/BFREE_SIGNATURES.md`; `lean/BFREE_IRRATIONALITY.md` §4.5.
Contract: Squarefree / C5
Audit: GREEN -/
theorem squarefree_posSeries_irrational {b : ℕ} (hb : 2 ≤ b) :
    Irrational (∑' n, (Nat.nth Squarefree n : ℝ) / (b : ℝ) ^ (n + 1)) := by
  simpa [posSeries, enum_squareModuli_eq_nth_squarefree] using
    posSeries_irrational squareModuliFamily hb

end PrimeGapNormality.BFree
