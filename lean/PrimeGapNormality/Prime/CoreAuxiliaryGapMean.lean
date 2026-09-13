import PrimeGapNormality.Prime.AuxFrameDelete
import PrimeGapNormality.Prime.UniformAuxFrame
import PrimeGapNormality.Prime.CoreRootedGapExpectation
import PrimeGapNormality.Prime.CorePresieveLaw
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The physical first moment of the auxiliary deletion law

The auxiliary frame law is realized honestly: first sample the actual rooted
sieve configuration, restrict to configurations with enough points, and then
delete a uniformly random point.  Conditional on an exposed presieve and the
final cardinality, `lateRootLaw` is cardinality-symmetric, so the exact finite
deletion identity below identifies this construction with a uniform
`(n - 1)`-subset of the presieve carrier.

For an arbitrary deleted point, not merely the point at the tested rank, the
new rank-`j` gap is at most the sum of the old rank-`j` and rank-`j+1` gaps.
The already proved physical rooted-gap identity then gives the auxiliary span
mean at most `2 / V(y)`, without an assumed model moment.
-/

open Finset
open scoped BigOperators Classical

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### Minimal finite-window enumeration facts

These are kept under unique names here rather than importing the legacy
transfer leaves, which expose mutually conflicting global helper names. -/

private theorem coreAux_residueOfChoice_ne_zero (y : ℕ) (σ : ResidueChoice y)
    {p : ℕ} (hp : p ∈ Nat.primesLE y) : residueOfChoice y σ p ≠ 0 := by
  simp [residueOfChoice, hp]

private theorem coreAux_sieveSurvives_zero (y : ℕ) (σ : ResidueChoice y) :
    sieveSurvives y (residueOfChoice y σ) 0 := by
  intro p hp
  rw [Nat.zero_mod]
  exact (coreAux_residueOfChoice_ne_zero y σ hp).symm

private theorem coreAux_sievePoint_zero (y : ℕ) (σ : ResidueChoice y) :
    sievePoint y (residueOfChoice y σ) 0 = 0 :=
  Nat.nth_zero_of_zero (coreAux_sieveSurvives_zero y σ)

private theorem coreAux_sieveModulus_pos (y : ℕ) :
    0 < ∏ p ∈ Nat.primesLE y, p :=
  prod_pos fun p hp => (Nat.prime_of_mem_primesLE hp).pos

private theorem coreAux_sieveSurvives_infinite (y : ℕ) (σ : ResidueChoice y) :
    (Set.ofPred (sieveSurvives y (residueOfChoice y σ))).Infinite := by
  set M := ∏ p ∈ Nat.primesLE y, p
  have hM : 0 < M := coreAux_sieveModulus_pos y
  refine Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => (k + 1) * M) ?_ ?_
  · intro a b h
    exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right hM h)
  · intro k
    intro p hp
    have hdiv : p ∣ M := dvd_prod_of_mem (fun q => q) hp
    have hdiv' : p ∣ (k + 1) * M := hdiv.mul_left (k + 1)
    rw [Nat.mod_eq_zero_of_dvd hdiv']
    exact (coreAux_residueOfChoice_ne_zero y σ hp).symm

private theorem coreAux_sievePoint_strictMono (y : ℕ) (σ : ResidueChoice y) :
    StrictMono (sievePoint y (residueOfChoice y σ)) :=
  Nat.nth_strictMono (coreAux_sieveSurvives_infinite y σ)

private theorem coreAux_sievePoint_survives (y : ℕ) (σ : ResidueChoice y)
    (k : ℕ) :
    sieveSurvives y (residueOfChoice y σ)
      (sievePoint y (residueOfChoice y σ) k) :=
  Nat.nth_mem_of_infinite (coreAux_sieveSurvives_infinite y σ) k

private theorem coreAux_sievePoint_pos {y k : ℕ} (σ : ResidueChoice y)
    (hk : 1 ≤ k) : 1 ≤ sievePoint y (residueOfChoice y σ) k :=
  le_trans hk (Nat.le_nth fun hf => (coreAux_sieveSurvives_infinite y σ hf).elim)

private theorem coreAux_exists_rank_of_mem_sieveSurvivorsFin {y S n : ℕ}
    {σ : ResidueChoice y} (hn : n ∈ sieveSurvivorsFin y σ S) :
    ∃ k : ℕ, 1 ≤ k ∧ sievePoint y (residueOfChoice y σ) k = n := by
  have hnI := mem_Icc.mp (mem_filter.mp hn).1
  have hsurv : sieveSurvives y (residueOfChoice y σ) n :=
    (mem_filter.mp hn).2
  obtain ⟨k, _, hkn⟩ := Nat.exists_lt_card_nth_eq hsurv
  refine ⟨k, ?_, hkn⟩
  by_contra hk
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
  subst hk0
  change sievePoint y (residueOfChoice y σ) 0 = n at hkn
  rw [coreAux_sievePoint_zero] at hkn
  omega

private theorem coreAux_sievePoint_le_of_le_card {y S k : ℕ}
    {σ : ResidueChoice y} (hk : 1 ≤ k)
    (hcard : k ≤ (sieveSurvivorsFin y σ S).card) :
    sievePoint y (residueOfChoice y σ) k ≤ S := by
  by_contra hgt
  have hSlt : S < sievePoint y (residueOfChoice y σ) k := Nat.not_le.mp hgt
  let U := sieveSurvivorsFin y σ S
  have hsub : U ⊆
      (Icc 1 (k - 1)).image (sievePoint y (residueOfChoice y σ)) := by
    intro n hn
    obtain ⟨r, hr1, hrn⟩ := coreAux_exists_rank_of_mem_sieveSurvivorsFin hn
    have hnS : n ≤ S := (mem_Icc.mp (mem_filter.mp hn).1).2
    have hrk : r < k :=
      (coreAux_sievePoint_strictMono y σ).lt_iff_lt.mp (by
        rw [hrn]
        exact Nat.lt_of_le_of_lt hnS hSlt)
    exact mem_image.mpr ⟨r, mem_Icc.mpr ⟨hr1, Nat.le_sub_one_of_lt hrk⟩, hrn⟩
  have hle : U.card ≤ k - 1 := by
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    rw [Nat.card_Icc]
    omega
  have : k ≤ k - 1 := hcard.trans hle
  omega

private theorem coreAux_sievePoint_mem_survivors {y S k : ℕ}
    {σ : ResidueChoice y} (hk : 1 ≤ k)
    (hcard : k ≤ (sieveSurvivorsFin y σ S).card) :
    sievePoint y (residueOfChoice y σ) k ∈ sieveSurvivorsFin y σ S :=
  mem_filter.mpr ⟨mem_Icc.mpr ⟨coreAux_sievePoint_pos σ hk,
    coreAux_sievePoint_le_of_le_card hk hcard⟩,
    coreAux_sievePoint_survives y σ k⟩

private theorem coreAux_sievePoint_eq_orderEmb {y S : ℕ}
    {σ : ResidueChoice y} (hU : 0 < (sieveSurvivorsFin y σ S).card) :
    (fun i : Fin (sieveSurvivorsFin y σ S).card =>
        sievePoint y (residueOfChoice y σ) (i.val + 1)) =
      orderEmbOfFin (sieveSurvivorsFin y σ S) rfl := by
  let U := sieveSurvivorsFin y σ S
  let f : Fin U.card → ℕ := fun i =>
    sievePoint y (residueOfChoice y σ) (i.val + 1)
  have hmem : ∀ i : Fin U.card, f i ∈ U := by
    intro i
    exact coreAux_sievePoint_mem_survivors (Nat.succ_pos i.val)
      (Nat.succ_le_of_lt i.isLt)
  have hmono : StrictMono f := by
    intro i k hik
    exact coreAux_sievePoint_strictMono y σ (Nat.succ_lt_succ hik)
  exact orderEmbOfFin_unique rfl hmem hmono

/-! ### An arbitrary deletion only merges neighbouring rank gaps -/

private theorem coreAux_getElem_eraseIdx_between {l : List ℕ} {i j : ℕ}
    (hsorted : l.SortedLT) (hi : i < l.length) (hj : j + 1 < l.length) :
    l[j]'(by omega) ≤ (l.eraseIdx i)[j]'(by
      rw [List.length_eraseIdx_of_lt hi]
      omega) ∧
      (l.eraseIdx i)[j]'(by
        rw [List.length_eraseIdx_of_lt hi]
        omega) ≤ l[j + 1]'hj := by
  have hj0 : j < l.length := Nat.lt_trans (Nat.lt_succ_self j) hj
  have hjErase : j < (l.eraseIdx i).length := by
    rw [List.length_eraseIdx_of_lt hi]
    omega
  have hstep : l[j]'hj0 < l[j + 1]'hj :=
    hsorted.getElem_lt_getElem_of_lt (hi := hj0) (hj := hj) (Nat.lt_succ_self j)
  by_cases hji : j < i
  · rw [List.getElem_eraseIdx_of_lt hjErase hji]
    exact ⟨le_rfl, Nat.le_of_lt hstep⟩
  · have hij : i ≤ j := Nat.le_of_not_gt hji
    rw [List.getElem_eraseIdx_of_ge hjErase hij]
    exact ⟨Nat.le_of_lt hstep, le_rfl⟩

/-- Deleting any point of a finite set can enlarge a fixed interior rank gap
by at most the next original gap.  This is independent of the deleted rank. -/
theorem coreAux_subsetGap_erase_le_neighbor_sum {E : Finset ℕ} {x j : ℕ}
    (hx : x ∈ E) (hj : j + 1 < E.card) :
    subsetGap (E.erase x) j ≤ subsetGap E j + subsetGap E (j + 1) := by
  let l := E.sort (· ≤ ·)
  have hlen : l.length = E.card := length_sort _
  have hxl : x ∈ l := by
    simpa [l] using hx
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxl
  have hiE : i < E.card := by simpa [hlen] using hi
  have hxstat : orderStat E (i + 1) = x := by
    rw [orderStat_succ_eq_sort hiE]
    simpa [l] using hix
  have hsort : (E.erase x).sort (· ≤ ·) = l.eraseIdx i := by
    simpa [l, hxstat] using auxDel_sort_erase (E := E) (i := i) hiE
  have hcard : (E.erase x).card = E.card - 1 := card_erase_of_mem hx
  have hjE : j < E.card := Nat.lt_trans (Nat.lt_succ_self j) hj
  have hjF : j < (E.erase x).card := by
    rw [hcard]
    omega
  have hjList : j + 1 < l.length := by simpa [hlen] using hj
  have hbetween := coreAux_getElem_eraseIdx_between
    (hsorted := sortedLT_sort E) hi hjList
  have hright : orderStat (E.erase x) (j + 1) ≤ orderStat E (j + 2) := by
    have hjFsort : j < ((E.erase x).sort (· ≤ ·)).length := by
      simpa [length_sort] using hjF
    calc
      orderStat (E.erase x) (j + 1) =
          ((E.erase x).sort (· ≤ ·))[j]'hjFsort := orderStat_succ_eq_sort hjF
      _ = (l.eraseIdx i)[j]'(hsort ▸ hjFsort) :=
        List.getElem_of_eq hsort hjFsort
      _ ≤ l[j + 1]'hjList := hbetween.2
      _ = orderStat E (j + 2) := by
        rw [orderStat_succ_eq_sort hj]
  have hleft : orderStat E j ≤ orderStat (E.erase x) j := by
    by_cases hj0 : j = 0
    · subst hj0
      simpa only [orderStat_zero] using (le_rfl : (0 : ℕ) ≤ 0)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hjPred : j - 1 + 1 < l.length := by
        rw [Nat.sub_add_cancel hjpos, hlen]
        exact hjE
      have hbetweenPred := coreAux_getElem_eraseIdx_between
        (hsorted := sortedLT_sort E) hi hjPred
      have hjFsort : j - 1 < ((E.erase x).sort (· ≤ ·)).length := by
        rw [length_sort]
        omega
      calc
        orderStat E j = l[j - 1]'(by rw [hlen]; omega) := by
          rw [orderStat_pos_eq_sort hjpos (Nat.le_of_lt hjE)]
        _ ≤ (l.eraseIdx i)[j - 1]'(hsort ▸ hjFsort) := hbetweenPred.1
        _ = ((E.erase x).sort (· ≤ ·))[j - 1]'hjFsort :=
          (List.getElem_of_eq hsort hjFsort).symm
        _ = orderStat (E.erase x) j :=
          (orderStat_pos_eq_sort hjpos (Nat.le_of_lt hjF)).symm
  have hwide :
      orderStat (E.erase x) (j + 1) - orderStat (E.erase x) j ≤
        orderStat E (j + 2) - orderStat E j :=
    tsub_le_tsub hright hleft
  have hle₁ : orderStat E j ≤ orderStat E (j + 1) :=
    auxDel_orderStat_le_succ hjE
  have hle₂ : orderStat E (j + 1) ≤ orderStat E (j + 2) :=
    auxDel_orderStat_le_succ hj
  unfold subsetGap
  calc
    orderStat (E.erase x) (j + 1) - orderStat (E.erase x) j ≤
        orderStat E (j + 2) - orderStat E j := hwide
    _ = (orderStat E (j + 1) - orderStat E j) +
        (orderStat E (j + 2) - orderStat E (j + 1)) :=
      auxDel_tsub_add hle₁ hle₂

/-! ### Exact uniform deletion law -/

/-- Insert/delete gives a weight-preserving bijection between
`(U, x ∈ U)`, for `|U| = n`, and `(F, x ∈ A \ F)`, for `|F| = n-1`. -/
theorem coreAux_uniform_delete_pairs (A : Finset ℕ) (n : ℕ)
    (f : Finset ℕ → ℝ) (hn : 1 ≤ n) :
    ∑ U ∈ A.powersetCard n, ∑ x ∈ U, f (U.erase x) =
      ∑ F ∈ A.powersetCard (n - 1), ∑ x ∈ A \ F, f F := by
  rw [sum_sigma' (s := A.powersetCard n) (t := fun U => U)
      (f := fun U x => f (U.erase x)),
    sum_sigma' (s := A.powersetCard (n - 1)) (t := fun F => A \ F)
      (f := fun F _x => f F)]
  refine sum_bij'
      (fun p _ => ⟨p.1.erase p.2, p.2⟩)
      (fun p _ => ⟨insert p.2 p.1, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).1
    have hxU := (mem_sigma.mp hp).2
    refine mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨(erase_subset _ _).trans hU.1, ?_⟩,
      mem_sdiff.mpr ⟨hU.1 hxU, by simp⟩⟩
    rw [card_erase_of_mem hxU, hU.2]
  · intro p hp
    have hF := mem_powersetCard.mp (mem_sigma.mp hp).1
    have hx := mem_sdiff.mp (mem_sigma.mp hp).2
    have hcard : (insert p.2 p.1).card = n := by
      rw [card_insert_of_notMem hx.2, hF.2, Nat.sub_add_cancel hn]
    exact mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨insert_subset hx.1 hF.1, hcard⟩,
      mem_insert_self _ _⟩
  · intro p hp
    have hxU := (mem_sigma.mp hp).2
    simp [insert_erase hxU]
  · intro p hp
    have hx := mem_sdiff.mp (mem_sigma.mp hp).2
    simp [erase_insert hx.2]
  · intro p _hp
    rfl

/-- Unnormalized deletion sum.  Every remaining `(n-1)`-set has exactly
`|A|-n+1` one-point extensions. -/
theorem coreAux_uniform_delete_sum (A : Finset ℕ) (n : ℕ)
    (f : Finset ℕ → ℝ) (hn : 1 ≤ n) (hnA : n ≤ A.card) :
    ∑ U ∈ A.powersetCard n, ∑ x ∈ U, f (U.erase x) =
      ((A.card : ℝ) - n + 1) * ∑ F ∈ A.powersetCard (n - 1), f F := by
  rw [coreAux_uniform_delete_pairs A n f hn]
  calc
    (∑ F ∈ A.powersetCard (n - 1), ∑ x ∈ A \ F, f F) =
        ∑ F ∈ A.powersetCard (n - 1), ((A \ F).card : ℝ) * f F := by
      refine sum_congr rfl fun F _hF => ?_
      rw [sum_const, nsmul_eq_mul]
    _ = ∑ F ∈ A.powersetCard (n - 1),
        ((A.card : ℝ) - n + 1) * f F := by
      refine sum_congr rfl fun F hF => ?_
      have hFm := mem_powersetCard.mp hF
      rw [auxDel_extension_card rfl hFm.1 hFm.2 hn hnA,
        auxFrame_cast_sub hnA]
    _ = ((A.card : ℝ) - n + 1) *
        ∑ F ∈ A.powersetCard (n - 1), f F := by
      rw [Finset.mul_sum]

/-- Exact normalized law: a uniform `n`-subset followed by a uniformly
random deletion is a uniform `(n-1)`-subset. -/
theorem coreAux_uniform_delete_law (A : Finset ℕ) (n : ℕ)
    (f : Finset ℕ → ℝ) (hn : 1 ≤ n) (hnA : n ≤ A.card) :
    (∑ U ∈ A.powersetCard n, ∑ x ∈ U, f (U.erase x)) /
        ((n : ℝ) * (A.card.choose n : ℝ)) =
      auxFrame_uniformMean A (n - 1) f := by
  unfold auxFrame_uniformMean
  rw [coreAux_uniform_delete_sum A n f hn hnA,
    auxFrame_choose_mul_real hn hnA]
  field_simp [auxFrame_sub_ne_zero hnA, auxFrame_choose_pred_ne_zero hnA]

/-- On an actual late sieve fibre the preceding uniform deletion law is the
paper's auxiliary law, because equal-cardinality survivor sets have equal
`lateRootLaw` mass. -/
theorem coreAux_lateRootLaw_delete_layer_eq_auxiliary
    (S y : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y) (n : ℕ)
    (f : Finset ℕ → ℝ) (hn : 1 ≤ n)
    (hnA : n ≤ (presieveSurvivors S σ).card) :
    (∑ U ∈ (presieveSurvivors S σ).powersetCard n,
        lateRootLaw S y (presieveSurvivors S σ) U *
          ((∑ x ∈ U, f (U.erase x)) / (n : ℝ))) =
      cardinalityLayer (presieveSurvivors S σ)
          (lateRootLaw S y (presieveSurvivors S σ)) n *
        auxFrame_uniformMean (presieveSurvivors S σ) (n - 1) f := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  let w := uniformLayerWeight A μ n
  have hμ : CardinalitySymmetricMass A μ := by
    simpa [A, μ] using corePresieveLaw_cardinalitySymmetric S y σ hSy
  have hterm : ∀ U ∈ A.powersetCard n, μ U = w := by
    intro U hU
    have hUm := mem_powersetCard.mp hU
    simpa [w, hUm.2] using mu_eq_uniformLayerWeight hμ hUm.1
  have hw : w = cardinalityLayer A μ n / (A.card.choose n : ℝ) := by
    unfold w uniformLayerWeight
    rw [dif_pos ⟨hnA, Nat.choose_pos hnA⟩]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hchoose : (A.card.choose n : ℝ) ≠ 0 := auxFrame_choose_ne_zero hnA
  have hlaw := coreAux_uniform_delete_law A n f hn hnA
  change (∑ U ∈ A.powersetCard n,
      μ U * ((∑ x ∈ U, f (U.erase x)) / (n : ℝ))) = _
  calc
    (∑ U ∈ A.powersetCard n,
        μ U * ((∑ x ∈ U, f (U.erase x)) / (n : ℝ))) =
        ∑ U ∈ A.powersetCard n,
          w * ((∑ x ∈ U, f (U.erase x)) / (n : ℝ)) := by
      refine sum_congr rfl fun U hU => ?_
      rw [hterm U hU]
    _ = w * (∑ U ∈ A.powersetCard n,
        (∑ x ∈ U, f (U.erase x)) / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ = w * ((∑ U ∈ A.powersetCard n, ∑ x ∈ U, f (U.erase x)) /
        (n : ℝ)) := by
      rw [Finset.sum_div]
    _ = cardinalityLayer A μ n *
        ((∑ U ∈ A.powersetCard n, ∑ x ∈ U, f (U.erase x)) /
          ((n : ℝ) * (A.card.choose n : ℝ))) := by
      rw [hw]
      field_simp [hn0, hchoose]
      <;> ring
    _ = cardinalityLayer A μ n * auxFrame_uniformMean A (n - 1) f := by
      rw [hlaw]

/-! ### The concrete actual auxiliary physical span -/

/-- Mean rank-`j` physical gap after a uniformly random point of `E` is
deleted.  It is zero for the empty set. -/
noncomputable def coreAux_uniformDeletedGap (E : Finset ℕ) (j : ℕ) : ℝ :=
  (∑ x ∈ E, (subsetGap (E.erase x) j : ℝ)) / (E.card : ℝ)

theorem coreAux_uniformDeletedGap_nonneg (E : Finset ℕ) (j : ℕ) :
    0 ≤ coreAux_uniformDeletedGap E j :=
  div_nonneg (sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem coreAux_uniformDeletedGap_le (E : Finset ℕ) (j : ℕ)
    (hj : j + 1 < E.card) :
    coreAux_uniformDeletedGap E j ≤
      (subsetGap E j : ℝ) + (subsetGap E (j + 1) : ℝ) := by
  have hcard : (0 : ℝ) < (E.card : ℝ) := by
    exact_mod_cast (lt_trans (Nat.zero_lt_succ j) hj)
  have hsum :
      (∑ x ∈ E, (subsetGap (E.erase x) j : ℝ)) ≤
        ∑ x ∈ E, ((subsetGap E j : ℝ) + (subsetGap E (j + 1) : ℝ)) := by
    refine sum_le_sum fun x hx => ?_
    exact_mod_cast coreAux_subsetGap_erase_le_neighbor_sum hx hj
  unfold coreAux_uniformDeletedGap
  calc
    (∑ x ∈ E, (subsetGap (E.erase x) j : ℝ)) / (E.card : ℝ) ≤
        (∑ x ∈ E, ((subsetGap E j : ℝ) +
          (subsetGap E (j + 1) : ℝ))) / (E.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcard.le
    _ = (subsetGap E j : ℝ) + (subsetGap E (j + 1) : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
      field_simp

/-- The actual auxiliary span law on a finite physical window.  The mass on
`N < L` is discarded rather than renormalized, exactly as in the paper. -/
noncomputable def coreAuxiliaryPhysicalGapMean (y S L j : ℕ) : ℝ :=
  ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U *
    if L ≤ U.card then coreAux_uniformDeletedGap U j else 0

/-- The paper presentation of the same auxiliary law: retain the exposed
presieve and final-cardinality marginals, discard `n < L`, and conditionally
choose a uniform `(n-1)`-subset of the presieve carrier. -/
noncomputable def coreAuxiliaryLayerPhysicalGapMean (S y L j : ℕ) : ℝ :=
  (∑ σ : ResidueChoice S,
      ∑ n ∈ Icc L (presieveSurvivors S σ).card,
        cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
          auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
            (fun F => (subsetGap F j : ℝ))) /
    (Fintype.card (ResidueChoice S) : ℝ)

private theorem coreAux_lateRootLaw_eq_zero_of_not_subset
    {S y : ℕ} {A U : Finset ℕ} (hU : ¬ U ⊆ A) :
    lateRootLaw S y A U = 0 := by
  have hempty :
      ((univ : Finset (LateResidueChoice S y)).filter
          fun τ => lateSurvivors S y A τ = U) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro τ hτ
    apply hU
    have heq : lateSurvivors S y A τ = U := (mem_filter.mp hτ).2
    rw [← heq]
    exact filter_subset _ _
  simp [lateRootLaw, lateProductMass, hempty]

/-- Partition a lower cardinality tail of the powerset into exact layers. -/
private theorem coreAux_sum_powerset_card_layers (A : Finset ℕ) (L : ℕ)
    (g : Finset ℕ → ℝ) :
    (∑ n ∈ Icc L A.card, ∑ U ∈ A.powersetCard n, g U) =
      ∑ U ∈ A.powerset.filter (fun U => L ≤ U.card), g U := by
  rw [sum_sigma' (s := Icc L A.card) (t := fun n => A.powersetCard n)
    (f := fun _n U => g U)]
  refine sum_bij'
      (fun p _ => p.2)
      (fun U _ => ⟨U.card, U⟩)
      ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hn := (mem_sigma.mp hp).1
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).2
    exact mem_filter.mpr ⟨mem_powerset.mpr hU.1,
      hU.2 ▸ (mem_Icc.mp hn).1⟩
  · intro U hU
    have hUm := mem_filter.mp hU
    have hsub := mem_powerset.mp hUm.1
    exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hUm.2, card_le_card hsub⟩,
      mem_powersetCard.mpr ⟨hsub, rfl⟩⟩
  · intro p hp
    have hU := mem_powersetCard.mp (mem_sigma.mp hp).2
    simp [hU.2]
  · intro U _hU
    rfl
  · intro p _hp
    rfl

/-- On one exposed presieve fibre, aggregation of the exact conditional
uniform deletion law over all `n ≥ L` equals the random-deletion
realization on the full physical window. -/
private theorem coreAux_lateRootLaw_auxiliary_gap_eq_window
    (S y L j : ℕ) (σ : ResidueChoice S) (hSy : S ≤ y) (hL : 1 ≤ L) :
    (∑ n ∈ Icc L (presieveSurvivors S σ).card,
        cardinalityLayer (presieveSurvivors S σ)
            (lateRootLaw S y (presieveSurvivors S σ)) n *
          auxFrame_uniformMean (presieveSurvivors S σ) (n - 1)
            (fun F => (subsetGap F j : ℝ))) =
      ∑ U ∈ (offsetWindow S).powerset,
        lateRootLaw S y (presieveSurvivors S σ) U *
          if L ≤ U.card then coreAux_uniformDeletedGap U j else 0 := by
  let A := presieveSurvivors S σ
  let μ := lateRootLaw S y A
  have hlayers :
      (∑ n ∈ Icc L A.card,
          cardinalityLayer A μ n *
            auxFrame_uniformMean A (n - 1)
              (fun F => (subsetGap F j : ℝ))) =
        ∑ n ∈ Icc L A.card,
          ∑ U ∈ A.powersetCard n, μ U * coreAux_uniformDeletedGap U j := by
    refine sum_congr rfl fun n hn => ?_
    have hnm := mem_Icc.mp hn
    have hn : 1 ≤ n := hL.trans hnm.1
    calc
      cardinalityLayer A μ n *
          auxFrame_uniformMean A (n - 1) (fun F => (subsetGap F j : ℝ)) =
        ∑ U ∈ A.powersetCard n, μ U *
          ((∑ x ∈ U, ((subsetGap (U.erase x) j : ℕ) : ℝ)) / (n : ℝ)) := by
        simpa [A, μ] using
          (coreAux_lateRootLaw_delete_layer_eq_auxiliary S y σ hSy n
            (fun F => (subsetGap F j : ℝ)) hn hnm.2).symm
      _ = ∑ U ∈ A.powersetCard n, μ U * coreAux_uniformDeletedGap U j := by
        refine sum_congr rfl fun U hU => ?_
        have hcard := (mem_powersetCard.mp hU).2
        unfold coreAux_uniformDeletedGap
        rw [hcard]
  have hpartition := coreAux_sum_powerset_card_layers A L
    (fun U => μ U * coreAux_uniformDeletedGap U j)
  have hfilter :
      (∑ U ∈ A.powerset, μ U *
          if L ≤ U.card then coreAux_uniformDeletedGap U j else 0) =
        ∑ U ∈ A.powerset.filter (fun U => L ≤ U.card),
          μ U * coreAux_uniformDeletedGap U j := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
  have hA : A ⊆ offsetWindow S := by
    simpa [A, offsetWindow] using corePresieveSurvivors_subset_Icc S σ
  have hsub : A.powerset ⊆ (offsetWindow S).powerset := powerset_mono.mpr hA
  have hext :
      (∑ U ∈ A.powerset, μ U *
          if L ≤ U.card then coreAux_uniformDeletedGap U j else 0) =
        ∑ U ∈ (offsetWindow S).powerset, μ U *
          if L ≤ U.card then coreAux_uniformDeletedGap U j else 0 := by
    exact sum_subset hsub fun U _hU hnot => by
      have hnotA : ¬ U ⊆ A := fun hUA => hnot (mem_powerset.mpr hUA)
      dsimp only [μ]
      rw [coreAux_lateRootLaw_eq_zero_of_not_subset hnotA, zero_mul]
  change (∑ n ∈ Icc L A.card,
      cardinalityLayer A μ n *
        auxFrame_uniformMean A (n - 1) (fun F => (subsetGap F j : ℝ))) = _
  rw [hlayers, hpartition, ← hfilter, hext]

/-- Weighted expectations under `actualRootLaw` are the uniform early-root
average of the corresponding late-fibre expectations. -/
private theorem coreAux_actualRootLaw_expectation_eq_avg_presieve
    (S y : ℕ) (hSy : S ≤ y) (g : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U) =
      (∑ σ : ResidueChoice S,
          ∑ U ∈ (offsetWindow S).powerset,
            lateRootLaw S y (presieveSurvivors S σ) U * g U) /
        (Fintype.card (ResidueChoice S) : ℝ) := by
  have hU : ∀ U,
      actualRootLaw y S U =
        (∑ σ : ResidueChoice S,
          lateRootLaw S y (presieveSurvivors S σ) U) /
          (Fintype.card (ResidueChoice S) : ℝ) :=
    fun U => coreActualRootLaw_eq_avg_presieve S y hSy U
  calc
    (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U) =
        ∑ U ∈ (offsetWindow S).powerset,
          ((∑ σ : ResidueChoice S,
            lateRootLaw S y (presieveSurvivors S σ) U) /
              (Fintype.card (ResidueChoice S) : ℝ)) * g U := by
      refine sum_congr rfl fun U _ => ?_
      rw [hU U]
    _ = ∑ U ∈ (offsetWindow S).powerset,
          ((∑ σ : ResidueChoice S,
            lateRootLaw S y (presieveSurvivors S σ) U) * g U) /
              (Fintype.card (ResidueChoice S) : ℝ) := by
      refine sum_congr rfl fun U _ => ?_
      ring
    _ = (∑ U ∈ (offsetWindow S).powerset,
          (∑ σ : ResidueChoice S,
            lateRootLaw S y (presieveSurvivors S σ) U) * g U) /
              (Fintype.card (ResidueChoice S) : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ σ : ResidueChoice S,
          ∑ U ∈ (offsetWindow S).powerset,
            lateRootLaw S y (presieveSurvivors S σ) U * g U) /
              (Fintype.card (ResidueChoice S) : ℝ) := by
      congr 1
      simp_rw [sum_mul]
      rw [sum_comm]

/-- The fully aggregated paper auxiliary law is exactly the concrete actual
random-deletion law, rather than a separately assumed model moment. -/
theorem coreAuxiliaryLayerPhysicalGapMean_eq_actual
    (S y L j : ℕ) (hSy : S ≤ y) (hL : 1 ≤ L) :
    coreAuxiliaryLayerPhysicalGapMean S y L j =
      coreAuxiliaryPhysicalGapMean y S L j := by
  let g : Finset ℕ → ℝ := fun U =>
    if L ≤ U.card then coreAux_uniformDeletedGap U j else 0
  have hmix := coreAux_actualRootLaw_expectation_eq_avg_presieve S y hSy g
  unfold coreAuxiliaryLayerPhysicalGapMean coreAuxiliaryPhysicalGapMean
  change _ = ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U
  rw [hmix]
  congr 1
  refine sum_congr rfl fun σ _ => ?_
  exact coreAux_lateRootLaw_auxiliary_gap_eq_window S y L j σ hSy hL

/-- Generic pushforward identity for the actual finite root law. -/
theorem coreAux_actualRootLaw_expectation (y S : ℕ) (g : Finset ℕ → ℝ) :
    (∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U) =
      (∑ σ : ResidueChoice y, g (sieveSurvivorsFin y σ S)) /
        (Fintype.card (ResidueChoice y) : ℝ) := by
  have hmaps : ∀ σ ∈ (univ : Finset (ResidueChoice y)),
      sieveSurvivorsFin y σ S ∈ (offsetWindow S).powerset :=
    fun _σ _ => mem_powerset.mpr (filter_subset _ _)
  have hfib := sum_fiberwise_of_maps_to' (s := univ)
    (t := (offsetWindow S).powerset)
    (g := fun σ => sieveSurvivorsFin y σ S) hmaps g
  have hinner :
      ∑ U ∈ (offsetWindow S).powerset,
          ∑ σ ∈ univ.filter (fun σ => sieveSurvivorsFin y σ S = U), g U =
        ∑ U ∈ (offsetWindow S).powerset,
          ((univ.filter (fun σ => sieveSurvivorsFin y σ S = U)).card : ℝ) * g U := by
    refine sum_congr rfl fun U _ => ?_
    rw [sum_const, nsmul_eq_mul]
  symm
  calc
    (∑ σ : ResidueChoice y, g (sieveSurvivorsFin y σ S)) /
        (Fintype.card (ResidueChoice y) : ℝ) =
      (∑ σ ∈ (univ : Finset (ResidueChoice y)),
          g (sieveSurvivorsFin y σ S)) /
        (Fintype.card (ResidueChoice y) : ℝ) := by simp
    _ = (∑ U ∈ (offsetWindow S).powerset,
          ∑ σ ∈ univ.filter (fun σ => sieveSurvivorsFin y σ S = U), g U) /
        (Fintype.card (ResidueChoice y) : ℝ) := by rw [hfib]
    _ = (∑ U ∈ (offsetWindow S).powerset,
          ((univ.filter (fun σ => sieveSurvivorsFin y σ S = U)).card : ℝ) * g U) /
        (Fintype.card (ResidueChoice y) : ℝ) := by rw [hinner]
    _ = ∑ U ∈ (offsetWindow S).powerset, actualRootLaw y S U * g U := by
      rw [Finset.sum_div]
      refine sum_congr rfl fun U _ => ?_
      unfold actualRootLaw
      ring

theorem coreAux_orderStat_sieveSurvivorsFin (y S : ℕ) (σ : ResidueChoice y)
    (k : ℕ) (hk : k ≤ (sieveSurvivorsFin y σ S).card) :
    orderStat (sieveSurvivorsFin y σ S) k =
      sievePoint y (residueOfChoice y σ) k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [orderStat_zero, coreAux_sievePoint_zero]
  · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hpos : 0 < (sieveSurvivorsFin y σ S).card := lt_of_lt_of_le hkpos hk
    have hfin : k - 1 < (sieveSurvivorsFin y σ S).card := by omega
    have hfun :
        sievePoint y (residueOfChoice y σ) k =
          orderEmbOfFin (sieveSurvivorsFin y σ S) rfl ⟨k - 1, hfin⟩ := by
      have h := congrFun (coreAux_sievePoint_eq_orderEmb hpos) ⟨k - 1, hfin⟩
      simpa [Nat.sub_add_cancel hkpos] using h
    have hget :
        ((sieveSurvivorsFin y σ S).sort (· ≤ ·))[k - 1]'(by
          rw [length_sort]
          exact hfin) =
          orderEmbOfFin (sieveSurvivorsFin y σ S) rfl ⟨k - 1, hfin⟩ := by
      rw [orderEmbOfFin_apply]
      simp [Fin.getElem_fin]
    rw [orderStat_pos_eq_sort hkpos hk]
    exact hget.trans hfun.symm

theorem coreAux_subsetGap_sieveSurvivorsFin (y S : ℕ) (σ : ResidueChoice y)
    (j : ℕ) (hj : j + 1 ≤ (sieveSurvivorsFin y σ S).card) :
    (subsetGap (sieveSurvivorsFin y σ S) j : ℝ) =
      (sievePoint y (residueOfChoice y σ) (j + 1) : ℝ) -
        (sievePoint y (residueOfChoice y σ) j : ℝ) := by
  have hmono : sievePoint y (residueOfChoice y σ) j ≤
      sievePoint y (residueOfChoice y σ) (j + 1) :=
    (coreAux_sievePoint_strictMono y σ (Nat.lt_succ_self j)).le
  unfold subsetGap
  rw [coreAux_orderStat_sieveSurvivorsFin y S σ (j + 1) hj,
    coreAux_orderStat_sieveSurvivorsFin y S σ j
      (le_trans (Nat.le_add_right j 1) hj),
    Nat.cast_sub hmono]

/-- Exact finite physical first-moment bound for the actual auxiliary law.
The two on the right is the arbitrary-deletion merge cost; both original
rooted gaps have the proved mean `1 / V(y)`. -/
theorem coreAuxiliaryPhysicalGapMean_le (y S L j : ℕ)
    (hj : j + 1 < L) :
    coreAuxiliaryPhysicalGapMean y S L j ≤
      (2 : ℝ) * (eulerProdNat y)⁻¹ := by
  rw [coreAuxiliaryPhysicalGapMean, coreAux_actualRootLaw_expectation]
  have hpoint : ∀ σ : ResidueChoice y,
      (if L ≤ (sieveSurvivorsFin y σ S).card then
          coreAux_uniformDeletedGap (sieveSurvivorsFin y σ S) j else 0) ≤
        ((sievePoint y (residueOfChoice y σ) (j + 1) : ℝ) -
          (sievePoint y (residueOfChoice y σ) j : ℝ)) +
        ((sievePoint y (residueOfChoice y σ) (j + 2) : ℝ) -
          (sievePoint y (residueOfChoice y σ) (j + 1) : ℝ)) := by
    intro σ
    by_cases hN : L ≤ (sieveSurvivorsFin y σ S).card
    · rw [if_pos hN]
      have hjN : j + 1 < (sieveSurvivorsFin y σ S).card :=
        lt_of_lt_of_le hj hN
      have hjcard : j + 1 ≤ (sieveSurvivorsFin y σ S).card := hjN.le
      have hjsuccCard : j + 2 ≤ (sieveSurvivorsFin y σ S).card := by omega
      calc
        coreAux_uniformDeletedGap (sieveSurvivorsFin y σ S) j ≤
            (subsetGap (sieveSurvivorsFin y σ S) j : ℝ) +
              (subsetGap (sieveSurvivorsFin y σ S) (j + 1) : ℝ) :=
          coreAux_uniformDeletedGap_le _ _ hjN
        _ = _ := by
          rw [coreAux_subsetGap_sieveSurvivorsFin y S σ j hjcard,
            coreAux_subsetGap_sieveSurvivorsFin y S σ (j + 1) hjsuccCard]
    · rw [if_neg hN]
      have hmono₁ : sievePoint y (residueOfChoice y σ) j ≤
          sievePoint y (residueOfChoice y σ) (j + 1) :=
        (coreAux_sievePoint_strictMono y σ (Nat.lt_succ_self j)).le
      have hmono₂ : sievePoint y (residueOfChoice y σ) (j + 1) ≤
          sievePoint y (residueOfChoice y σ) (j + 2) :=
        (coreAux_sievePoint_strictMono y σ (Nat.lt_succ_self (j + 1))).le
      exact add_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono₁))
        (sub_nonneg.mpr (by exact_mod_cast hmono₂))
  have hsum :
      (∑ σ : ResidueChoice y,
        if L ≤ (sieveSurvivorsFin y σ S).card then
          coreAux_uniformDeletedGap (sieveSurvivorsFin y σ S) j else 0) ≤
      ∑ σ : ResidueChoice y,
        (((sievePoint y (residueOfChoice y σ) (j + 1) : ℝ) -
          (sievePoint y (residueOfChoice y σ) j : ℝ)) +
        ((sievePoint y (residueOfChoice y σ) (j + 2) : ℝ) -
          (sievePoint y (residueOfChoice y σ) (j + 1) : ℝ))) := by
    exact sum_le_sum fun σ _ => hpoint σ
  have hden : 0 ≤ (Fintype.card (ResidueChoice y) : ℝ) := Nat.cast_nonneg _
  calc
    (∑ σ : ResidueChoice y,
        if L ≤ (sieveSurvivorsFin y σ S).card then
          coreAux_uniformDeletedGap (sieveSurvivorsFin y σ S) j else 0) /
        (Fintype.card (ResidueChoice y) : ℝ) ≤
      (∑ σ : ResidueChoice y,
        (((sievePoint y (residueOfChoice y σ) (j + 1) : ℝ) -
          (sievePoint y (residueOfChoice y σ) j : ℝ)) +
        ((sievePoint y (residueOfChoice y σ) (j + 2) : ℝ) -
          (sievePoint y (residueOfChoice y σ) (j + 1) : ℝ)))) /
        (Fintype.card (ResidueChoice y) : ℝ) :=
      div_le_div_of_nonneg_right hsum hden
    _ = ((∑ σ : ResidueChoice y,
          ((sievePoint y (residueOfChoice y σ) (j + 1) : ℝ) -
            (sievePoint y (residueOfChoice y σ) j : ℝ))) /
          (Fintype.card (ResidueChoice y) : ℝ)) +
        ((∑ σ : ResidueChoice y,
          ((sievePoint y (residueOfChoice y σ) (j + 2) : ℝ) -
            (sievePoint y (residueOfChoice y σ) (j + 1) : ℝ))) /
          (Fintype.card (ResidueChoice y) : ℝ)) := by
      rw [sum_add_distrib, add_div]
    _ = (eulerProdNat y)⁻¹ + (eulerProdNat y)⁻¹ := by
      rw [core_rooted_sieve_gap_mean y j,
        core_rooted_sieve_gap_mean y (j + 1)]
    _ = (2 : ℝ) * (eulerProdNat y)⁻¹ := by ring

end

end PrimeGapNormality.Prime
