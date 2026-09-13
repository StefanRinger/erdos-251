import PrimeGapNormality.BFree.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Partial periods, infinitude, and the ordered enumeration

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (11), (18).
Contract: API / C4
Audit: GREEN

Infinitude uses that a summable exclusion family cannot contain all but
finitely many primes, so infinitely many primes survive. This is not a
window count and does not add `+1` per modulus.
-/

namespace PrimeGapNormality.BFree

open Finset Function Filter
open scoped Topology

/-- Product of the first `k` exclusion moduli. Empty product is `1`. -/
def partialPeriod (F : AdmissibleFamily) (k : ℕ) : ℕ :=
  ∏ i ∈ range k, F.d i

theorem partialPeriod_pos (F : AdmissibleFamily) (k : ℕ) : 0 < partialPeriod F k :=
  prod_pos fun i _ => d_pos F i

theorem partialPeriod_zero (F : AdmissibleFamily) : partialPeriod F 0 = 1 := by
  simp [partialPeriod]

theorem partialPeriod_succ (F : AdmissibleFamily) (k : ℕ) :
    partialPeriod F (k + 1) = partialPeriod F k * F.d k := by
  simp [partialPeriod, prod_range_succ]

theorem d_dvd_partialPeriod (F : AdmissibleFamily) {k i : ℕ} (hi : i < k) :
    F.d i ∣ partialPeriod F k :=
  dvd_prod_of_mem _ (mem_range.mpr hi)

theorem coprime_partialPeriod (F : AdmissibleFamily) (k : ℕ) :
    Nat.Coprime (partialPeriod F k) (F.d k) := by
  rw [partialPeriod, Nat.coprime_prod_left_iff]
  intro i hi
  exact F.pairwise_coprime (ne_of_lt (mem_range.mp hi) : i ≠ k)

/-- An injective sequence of moduli `d i ≥ 2` is unbounded.

Source: `lean/BFREE_SOURCE_LEDGER.md`.
Contract: API
Audit: GREEN -/
theorem d_unbounded (F : AdmissibleFamily) (N : ℕ) : ∃ i, N < F.d i := by
  by_contra h
  have hle : ∀ i, F.d i ≤ N := fun i => le_of_not_gt fun hi => h ⟨i, hi⟩
  exact (Set.infinite_of_injective_forall_mem (d_injective F) hle) (Set.finite_le_nat N)

/-- Unused exclusion modulus `q ≥ 8W` for the adaptive window.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (3.5);
`rounds/round92/05_grok_positive_carry_update.md` §3.B.
Contract: C1
Audit: GREEN -/
theorem exists_unused_modulus (F : AdmissibleFamily) (W : ℕ) (hW : 0 < W) :
    ∃ i, 8 * W ≤ F.d i := by
  obtain ⟨i, hi⟩ := d_unbounded F (8 * W - 1)
  have hpos : 0 < 8 * W := Nat.mul_pos (by decide : (0 : ℕ) < 8) hW
  exact ⟨i, by omega⟩

/-- Unused index `i ∉ s` with exclusion modulus `q ≥ 8W`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (3.5);
`lean/BFREE_UNUSED_INDEX.md`.
Contract: C1
Audit: GREEN -/
theorem exists_unused_index (F : AdmissibleFamily) (s : Finset ℕ)
    (W : ℕ) (hW : 0 < W) :
    ∃ i, i ∉ s ∧ 8 * W ≤ F.d i := by
  obtain ⟨i, hi⟩ := d_unbounded F (max (8 * W - 1) (s.sup F.d))
  have hpos : 0 < 8 * W := Nat.mul_pos (by decide : (0 : ℕ) < 8) hW
  refine ⟨i, ?_, by omega⟩
  intro himem
  have hle : F.d i ≤ s.sup F.d := le_sup himem
  have : F.d i ≤ max (8 * W - 1) (s.sup F.d) :=
    le_trans hle (le_max_right _ _)
  exact Nat.not_le_of_gt hi this

/-- Finite-sieve density factor `∏_{i<k} (1-1/d i)`. -/
noncomputable def finiteRho (F : AdmissibleFamily) (k : ℕ) : ℝ :=
  ∏ i ∈ range k, (1 - (1 : ℝ) / F.d i)

theorem finiteRho_pos (F : AdmissibleFamily) (k : ℕ) : 0 < finiteRho F k :=
  prod_pos fun i _ => by
    have : 0 < 1 - (F.d i : ℝ)⁻¹ := survivalFactor_pos F i
    simpa [one_div] using this

theorem finiteRho_zero (F : AdmissibleFamily) : finiteRho F 0 = 1 := by
  simp [finiteRho]

/-- A prime that fails to survive is itself an exclusion modulus.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN -/
theorem not_bfree_prime_mem_range (F : AdmissibleFamily) {p : ℕ}
    (hp : Nat.Prime p) (h : ¬ BFree F p) : p ∈ Set.range F.d := by
  have : ∃ i, F.d i ∣ p := by
    by_contra hnone
    exact h ⟨hp.pos, fun i hi => hnone ⟨i, hi⟩⟩
  obtain ⟨i, hi⟩ := this
  rcases (Nat.dvd_prime hp).mp hi with h1 | heq
  · exact (d_not_one F i h1).elim
  · exact ⟨i, heq⟩

/-- Reciprocal sums over primes strictly below `N` diverge.

Source: `Mathlib.NumberTheory.SumPrimeReciprocals`.
Contract: API
Audit: GREEN -/
theorem tendsto_sum_primesBelow_inv :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p) atTop atTop := by
  have hnn : ∀ n, 0 ≤ ({p | Nat.Prime p}.indicator (fun n : ℕ => (1 : ℝ) / n)) n :=
    fun n => Set.indicator_nonneg (fun _ _ => by positivity) n
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp
    not_summable_one_div_on_primes
  refine hdiv.congr fun N => ?_
  simp only [Nat.primesBelow_eq_filter_range]
  rw [sum_filter]
  refine sum_congr rfl fun n _ => ?_
  simp [Set.indicator]

/-- Survivors are infinite: a summable family cannot swallow all but finitely
many primes.

Source: `lean/BFREE_SIGNATURES.md`.
Contract: API
Audit: GREEN -/
theorem bfree_infinite (F : AdmissibleFamily) : (Set.ofPred (BFree F)).Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  let FB : Finset ℕ := hfin.toFinset
  have hle : ∀ N : ℕ,
      ∑ p ∈ (Nat.primesBelow N).filter (fun p => p ∉ FB), (1 : ℝ) / p ≤
        ∑' i, (1 : ℝ) / F.d i := by
    intro N
    let s := (Nat.primesBelow N).filter (fun p => p ∉ FB)
    have hrange : ∀ p ∈ s, p ∈ Set.range F.d := by
      intro p hp
      have hp' := mem_filter.mp hp
      have hpP : Nat.Prime p := Nat.prime_of_mem_primesBelow hp'.1
      have hnot : ¬ BFree F p := by
        intro hB
        exact hp'.2 (hfin.mem_toFinset.mpr hB)
      exact not_bfree_prime_mem_range F hpP hnot
    have hinv : ∀ p ∈ s, F.d (invFun F.d p) = p := fun p hp =>
      invFun_eq (hrange p hp)
    have hinj : Set.InjOn (invFun F.d) (s : Set ℕ) := by
      intro a ha b hb heq
      have := congrArg F.d heq
      rw [hinv a ha, hinv b hb] at this
      exact this
    have hrew : ∑ p ∈ s, (1 : ℝ) / p =
        ∑ p ∈ s, (1 : ℝ) / F.d (invFun F.d p) :=
      sum_congr rfl fun p hp => by rw [hinv p hp]
    have himage :
        ∑ p ∈ s, (1 : ℝ) / F.d (invFun F.d p) =
          ∑ i ∈ s.image (invFun F.d), (1 : ℝ) / F.d i := by
      exact
        (sum_image (g := invFun F.d) (f := fun i : ℕ => (1 : ℝ) / F.d i) hinj).symm
    have hts := F.summable.sum_le_tsum (s.image (invFun F.d))
      (fun i _ => one_div_d_nonneg F i)
    exact (hrew.trans himage).trans_le hts
  have hC : ∀ N : ℕ,
      ∑ p ∈ (Nat.primesBelow N).filter (fun p => p ∈ FB), (1 : ℝ) / p ≤
        ∑ p ∈ FB, (1 : ℝ) / p := by
    intro N
    have hs : (Nat.primesBelow N).filter (fun p => p ∈ FB) ⊆ FB := fun p hp =>
      (mem_filter.mp hp).2
    exact sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
  have hsplit : ∀ N : ℕ,
      ∑ p ∈ (Nat.primesBelow N).filter (fun p => p ∉ FB), (1 : ℝ) / p =
        ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p -
          ∑ p ∈ (Nat.primesBelow N).filter (fun p => p ∈ FB), (1 : ℝ) / p := by
    intro N
    have hdisj :=
      disjoint_filter_filter_not (Nat.primesBelow N) (Nat.primesBelow N) (fun p => p ∈ FB)
    have hunion :=
      filter_union_filter_not_eq (p := fun p => p ∈ FB) (Nat.primesBelow N)
    have hsu :=
      sum_union (s₁ := (Nat.primesBelow N).filter (fun p => p ∈ FB))
        (s₂ := (Nat.primesBelow N).filter (fun p => p ∉ FB))
        (f := fun p : ℕ => (1 : ℝ) / p) hdisj
    linarith [hunion ▸ hsu]
  have hge : ∀ N : ℕ,
      ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p - ∑ p ∈ FB, (1 : ℝ) / p ≤
        ∑ p ∈ (Nat.primesBelow N).filter (fun p => p ∉ FB), (1 : ℝ) / p := by
    intro N
    rw [hsplit]
    linarith [hC N]
  have hto : Tendsto (fun N : ℕ =>
      ∑ p ∈ (Nat.primesBelow N).filter (fun p => p ∉ FB), (1 : ℝ) / p) atTop atTop :=
    tendsto_atTop_mono hge
      (tendsto_atTop_add_const_right atTop (-∑ p ∈ FB, (1 : ℝ) / p)
        tendsto_sum_primesBelow_inv)
  rcases exists_lt_of_tendsto_atTop hto 0 (∑' i, (1 : ℝ) / F.d i) with ⟨N, -, hlt⟩
  exact (hlt.trans_le (hle N)).false

theorem enum_mem (F : AdmissibleFamily) (n : ℕ) : BFree F (enum F n) :=
  Nat.nth_mem_of_infinite (bfree_infinite F) n

theorem enum_strictMono (F : AdmissibleFamily) : StrictMono (enum F) :=
  Nat.nth_strictMono (bfree_infinite F)

theorem enum_zero (F : AdmissibleFamily) : enum F 0 = 1 := by
  rw [enum, Nat.nth_zero]
  have hne : (Set.ofPred (BFree F)).Nonempty :=
    ⟨1, Set.mem_ofPred.mpr (bfree_one F)⟩
  refine le_antisymm (Nat.sInf_le (Set.mem_ofPred.mpr (bfree_one F))) ?_
  have hmem := Nat.sInf_mem hne
  exact Nat.succ_le_of_lt (Set.mem_ofPred.mp hmem).1

theorem range_enum (F : AdmissibleFamily) :
    Set.range (enum F) = Set.ofPred (BFree F) :=
  Nat.range_nth_of_infinite (bfree_infinite F)

end PrimeGapNormality.BFree
