import PrimeGapNormality.Prime.CoreRootedGapMean
import Mathlib.Data.Nat.Nth
import Mathlib.Order.WellFounded

/-!
# The actual Nat.nth enumeration of periodic survivors

Sort the survivors in one physical period, and repeat that sorted block.
Strict monotonicity and the exact range identify this explicit enumeration
with `Nat.nth`, the definition used by `StatisticalCriterion.sievePoint`.
-/

open Finset

namespace PrimeGapNormality.Prime

noncomputable def corePeriodicPoint (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (r : ℕ) : ℕ :=
  P * (r / (n + 1)) + A.orderEmbOfFin hcard ⟨r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem corePeriodicPoint_strictMono (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) :
    StrictMono (corePeriodicPoint P A hcard) := by
  intro r t hrt
  have hq : r / (n + 1) ≤ t / (n + 1) := Nat.div_le_div_right hrt.le
  rcases hq.eq_or_lt with hq | hq
  · have hrem : r % (n + 1) < t % (n + 1) := by
      have hr := Nat.mod_add_div r (n + 1)
      have ht := Nat.mod_add_div t (n + 1)
      rw [hq] at hr
      omega
    have hcoord := (A.orderEmbOfFin hcard).strictMono
      (show (⟨r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1)) <
          ⟨t % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ from hrem)
    simpa only [corePeriodicPoint, hq] using
      Nat.add_lt_add_left hcoord (P * (t / (n + 1)))
  · have hcoord : A.orderEmbOfFin hcard
        ⟨r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ < P :=
      mem_range.mp (hA (A.orderEmbOfFin_mem hcard _))
    have hprod := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hq)
    dsimp only [corePeriodicPoint]
    nlinarith

theorem corePeriodicPoint_mod (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (r : ℕ) :
    corePeriodicPoint P A hcard r % P =
      A.orderEmbOfFin hcard ⟨r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
  have hcoord : A.orderEmbOfFin hcard
      ⟨r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ < P :=
    mem_range.mp (hA (A.orderEmbOfFin_mem hcard _))
  simp [corePeriodicPoint, Nat.add_mod, Nat.mod_eq_of_lt hcoord]

theorem corePeriodicPoint_range (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) :
    Set.range (corePeriodicPoint P A hcard) = {m : ℕ | m % P ∈ A} := by
  ext m
  constructor
  · rintro ⟨r, rfl⟩
    change corePeriodicPoint P A hcard r % P ∈ A
    rw [corePeriodicPoint_mod P A hcard hA]
    exact A.orderEmbOfFin_mem hcard _
  · intro hm
    let i : Fin (n + 1) := (A.orderIsoOfFin hcard).symm ⟨m % P, hm⟩
    have hi : A.orderEmbOfFin hcard i = m % P := by
      exact congrArg Subtype.val ((A.orderIsoOfFin hcard).apply_symm_apply ⟨m % P, hm⟩)
    let r := i.val + (n + 1) * (m / P)
    have hrdiv : r / (n + 1) = m / P := by
      dsimp [r]
      rw [Nat.add_mul_div_left _ _ (Nat.succ_pos _), Nat.div_eq_of_lt i.isLt, zero_add]
    have hrmod : r % (n + 1) = i.val := by
      dsimp [r]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
    refine ⟨r, ?_⟩
    dsimp only [corePeriodicPoint]
    rw [hrdiv]
    have hidx : (⟨r % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (n + 1)) = i :=
      Fin.ext hrmod
    rw [hidx, hi]
    exact Nat.div_add_mod m P

/-- No extra enumeration axiom: the explicit periodic list is literally
the existing `Nat.nth` enumerator. -/
theorem corePeriodicPoint_eq_nth (P : ℕ) (A : Finset ℕ) {n : ℕ}
    (hcard : A.card = n + 1) (hA : A ⊆ range P) (r : ℕ) :
    corePeriodicPoint P A hcard r = Nat.nth (fun m => m % P ∈ A) r := by
  have hmono := corePeriodicPoint_strictMono P A hcard hA
  have hrange := corePeriodicPoint_range P A hcard hA
  have hinf : Set.Infinite {m : ℕ | m % P ∈ A} := by
    rw [← hrange]
    exact Set.infinite_range_of_injective hmono.injective
  have heq : corePeriodicPoint P A hcard = Nat.nth (fun m => m % P ∈ A) := by
    apply (hmono.range_inj (Nat.nth_strictMono hinf)).mp
    rw [hrange, Nat.range_nth_of_infinite hinf]
  exact congrFun heq r

end PrimeGapNormality.Prime
