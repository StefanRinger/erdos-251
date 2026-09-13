import PrimeGapNormality.Prime.FiniteRootMixInclusionProduct
import PrimeGapNormality.Prime.ResidueMcDiarmid
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Quantitative completion of the finite singular-series product

Above the diameter, all tuple residues are distinct.  At primes
`p ≥ 2 |E|`, the local factor lies in `[0,1]` and its defect is at most
`|E|²/p²`.  Summability of these defects gives genuine multipliability
of the tail.  Finite product bounds pass to this infinite product.
-/

open Filter Finset
open scoped Topology Classical

namespace PrimeGapNormality.Prime

noncomputable section

private theorem bernoulli_second_order (v : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (1 - u) ^ v - (1 - (v : ℝ) * u) ∧
      (1 - u) ^ v - (1 - (v : ℝ) * u) ≤ (v.choose 2 : ℝ) * u ^ 2 := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hc : ((v + 1).choose 2 : ℝ) = (v.choose 2 : ℝ) + v := by
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right, Nat.cast_add]
      ring
    have hid : (1 - u) ^ (v + 1) - (1 - ((v + 1 : ℕ) : ℝ) * u) =
        (1 - u) * ((1 - u) ^ v - (1 - (v : ℝ) * u)) + (v : ℝ) * u ^ 2 := by
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hid, hc]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) ih.1)
        (mul_nonneg (Nat.cast_nonneg v) (sq_nonneg u))
    · have hmul := mul_le_mul_of_nonneg_left ih.2 (sub_nonneg.mpr hu1)
      have hrem : (1 - u) * ((v.choose 2 : ℝ) * u ^ 2) ≤ (v.choose 2 : ℝ) * u ^ 2 :=
        mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg u)) (by linarith)
      nlinarith

private theorem twice_choose_two_le_sq (v : ℕ) :
    2 * (v.choose 2 : ℝ) ≤ (v : ℝ) ^ 2 := by
  have h : 2 * v.choose 2 ≤ v ^ 2 := by
    calc
      2 * v.choose 2 = (v * (v - 1) / 2) * 2 := by rw [Nat.choose_two_right]; omega
      _ ≤ v * (v - 1) := Nat.div_mul_le_self _ _
      _ ≤ v * v := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = v ^ 2 := (pow_two _).symm
  exact_mod_cast h

/-- Above the tuple diameter, reduction modulo a prime is injective. -/
theorem residueCount_eq_card_of_lt {E : Finset ℕ} {p : ℕ}
    (hp : Nat.Prime p) (hE : ∀ n ∈ E, n < p) : residueCount E p = E.card := by
  unfold residueCount
  apply card_image_of_injOn
  intro a ha b hb heq
  have hmod := (ZMod.natCast_eq_natCast_iff' a b p).mp heq
  rwa [Nat.mod_eq_of_lt (hE a ha), Nat.mod_eq_of_lt (hE b hb)] at hmod

/-- The local singular-series factor has a summable quadratic defect
once the modulus is beyond the diameter and twice the tuple size. -/
theorem localHLFactor_tail_bounds {E : Finset ℕ} {p : ℕ}
    (hp : Nat.Prime p) (hE : ∀ n ∈ E, n < p) (hvp : 2 * E.card ≤ p) :
    0 ≤ localHLFactor E p ∧ localHLFactor E p ≤ 1 ∧
      1 - localHLFactor E p ≤ (E.card : ℝ) ^ 2 * ((p : ℝ)⁻¹) ^ 2 := by
  let v := E.card
  let u : ℝ := (p : ℝ)⁻¹
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr hp.one_le
  have hu0 : 0 ≤ u := inv_nonneg.mpr hp0.le
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hvhalf : (v : ℝ) * u ≤ 1 / 2 := by
    have hcast : 2 * (v : ℝ) ≤ (p : ℝ) := by exact_mod_cast hvp
    change (v : ℝ) * (p : ℝ)⁻¹ ≤ 1 / 2
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hp0).mpr
    linarith
  have hnum : 0 ≤ 1 - (v : ℝ) * u := by linarith
  have hbon := bernoulli_second_order v hu0 hu1
  have hden : (1 / 2 : ℝ) ≤ (1 - u) ^ v := by linarith [hbon.1]
  have hdenpos : 0 < (1 - u) ^ v := lt_of_lt_of_le (by norm_num) hden
  have heq : localHLFactor E p = (1 - (v : ℝ) * u) / (1 - u) ^ v := by
    rw [localHLFactor, if_neg (not_le.mpr hp.one_lt), residueCount_eq_card_of_lt hp hE]
    simp only [v, u, div_eq_mul_inv, one_mul]
  rw [heq]
  refine ⟨div_nonneg hnum hdenpos.le, ?_, ?_⟩
  · apply (div_le_one hdenpos).mpr
    linarith [hbon.1]
  · have hdiff : 1 - (1 - (v : ℝ) * u) / (1 - u) ^ v =
        ((1 - u) ^ v - (1 - (v : ℝ) * u)) / (1 - u) ^ v := by
      field_simp [hdenpos.ne']
    rw [hdiff]
    calc
      ((1 - u) ^ v - (1 - (v : ℝ) * u)) / (1 - u) ^ v ≤
          ((1 - u) ^ v - (1 - (v : ℝ) * u)) / (1 / 2) :=
        div_le_div_of_nonneg_left hbon.1 (by norm_num) hden
      _ ≤ 2 * (v.choose 2 : ℝ) * u ^ 2 := by nlinarith [hbon.2]
      _ ≤ (v : ℝ) ^ 2 * u ^ 2 :=
        mul_le_mul_of_nonneg_right (twice_choose_two_le_sq v) (sq_nonneg u)

/-- Tail factors are one away from the primes above the cutoff. -/
def singularSeriesTailFactor (E : Finset ℕ) (y n : ℕ) : ℝ :=
  if y < n ∧ Nat.Prime n then localHLFactor E n else 1

theorem singularSeriesTailFactor_bounds {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hvy : 2 * E.card ≤ y) (n : ℕ) :
    0 ≤ singularSeriesTailFactor E y n ∧ singularSeriesTailFactor E y n ≤ 1 ∧
      1 - singularSeriesTailFactor E y n ≤ (E.card : ℝ) ^ 2 * ((n : ℝ)⁻¹) ^ 2 := by
  unfold singularSeriesTailFactor
  split_ifs with hn
  · exact localHLFactor_tail_bounds hn.2
      (fun a ha => (hE a ha).trans_lt (hSy.trans hn.1)) (hvy.trans hn.1.le)
  · exact ⟨by norm_num, le_rfl, by
      simpa only [sub_self] using mul_nonneg (sq_nonneg (E.card : ℝ)) (sq_nonneg ((n : ℝ)⁻¹))⟩

theorem multipliable_singularSeriesTailFactor {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hvy : 2 * E.card ≤ y) :
    Multipliable (singularSeriesTailFactor E y) := by
  have hpseries : Summable (fun n : ℕ => (E.card : ℝ) ^ 2 * ((n : ℝ)⁻¹) ^ 2) := by
    simpa only [one_div, inv_pow] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left ((E.card : ℝ) ^ 2)
  have hsum : Summable (fun n : ℕ => singularSeriesTailFactor E y n - 1) := by
    apply hpseries.of_norm_bounded
    intro n
    have h := singularSeriesTailFactor_bounds hE hSy hvy n
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h.2.1)]
    linarith [h.2.2]
  simpa only [add_sub_cancel] using Real.multipliable_one_add_of_summable hsum

private theorem one_sub_prod_le_sum_defects {s : Finset ℕ} {f : ℕ → ℝ}
    (hf0 : ∀ n ∈ s, 0 ≤ f n) (hf1 : ∀ n ∈ s, f n ≤ 1) :
    1 - ∏ n ∈ s, f n ≤ ∑ n ∈ s, (1 - f n) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih =>
    rw [prod_insert hn, sum_insert hn]
    have hs0 : ∀ m ∈ s, 0 ≤ f m := fun m hm => hf0 m (mem_insert_of_mem hm)
    have hs1 : ∀ m ∈ s, f m ≤ 1 := fun m hm => hf1 m (mem_insert_of_mem hm)
    have hprev := ih hs0 hs1
    have hprod : ∏ m ∈ s, f m ≤ 1 := prod_le_one hs0 hs1
    have hn1 := hf1 n (mem_insert_self _ _)
    have hmul := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hn1)
    nlinarith

private theorem singularSeriesTail_sum_defects_le {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hvy : 2 * E.card ≤ y)
    (hy : 1 ≤ y) (s : Finset ℕ) :
    ∑ n ∈ s, (1 - singularSeriesTailFactor E y n) ≤ (E.card : ℝ) ^ 2 / y := by
  have hfilter : ∑ n ∈ s, (1 - singularSeriesTailFactor E y n) =
      ∑ n ∈ s.filter (y < ·), (1 - singularSeriesTailFactor E y n) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnot
    have hny : ¬ y < n := by simpa only [mem_filter, hn, true_and] using hnot
    simp [singularSeriesTailFactor, hny]
  have hsub : s.filter (y < ·) ⊆ Icc (y + 1) (s.sup id) := by
    intro n hn
    have hmem := mem_filter.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt hmem.2, Finset.le_sup (f := id) hmem.1⟩
  have hinv : ∑ n ∈ s.filter (y < ·), ((n : ℝ)⁻¹) ^ 2 ≤ (y : ℝ)⁻¹ :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg ((n : ℝ)⁻¹))).trans
      (sum_inv_sq_Icc_succ_le hy)
  rw [hfilter]
  calc
    _ ≤ ∑ n ∈ s.filter (y < ·), (E.card : ℝ) ^ 2 * ((n : ℝ)⁻¹) ^ 2 :=
      sum_le_sum fun n _ => (singularSeriesTailFactor_bounds hE hSy hvy n).2.2
    _ = (E.card : ℝ) ^ 2 * ∑ n ∈ s.filter (y < ·), ((n : ℝ)⁻¹) ^ 2 :=
      (mul_sum _ _ _).symm
    _ ≤ (E.card : ℝ) ^ 2 * (y : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = (E.card : ℝ) ^ 2 / y := (div_eq_mul_inv _ _).symm

/-- The actual infinite tail lies between `1 - |E|²/y` and one. -/
theorem singularSeriesTail_tprod_bounds {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hvy : 2 * E.card ≤ y) (hy : 1 ≤ y) :
    1 - (E.card : ℝ) ^ 2 / y ≤ ∏' n : ℕ, singularSeriesTailFactor E y n ∧
      (∏' n : ℕ, singularSeriesTailFactor E y n) ≤ 1 := by
  have hmul := multipliable_singularSeriesTailFactor hE hSy hvy
  have hf0 : ∀ n, 0 ≤ singularSeriesTailFactor E y n :=
    fun n => (singularSeriesTailFactor_bounds hE hSy hvy n).1
  have hf1 : ∀ n, singularSeriesTailFactor E y n ≤ 1 :=
    fun n => (singularSeriesTailFactor_bounds hE hSy hvy n).2.1
  constructor
  · apply le_hasProd_of_le_prod hmul.hasProd
    intro s
    have h := one_sub_prod_le_sum_defects (s := s) (fun n _ => hf0 n) (fun n _ => hf1 n)
    have hsum := singularSeriesTail_sum_defects_le hE hSy hvy hy s
    linarith
  · exact hasProd_le_of_prod_le hmul.hasProd fun s =>
      prod_le_one (fun n _ => hf0 n) (fun n _ => hf1 n)

/-- Head/tail decomposition for the literal infinite product in
`EndAPI.singularSeries`.  Finite zero factors are allowed. -/
theorem singularSeries_eq_prefix_mul_tail {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hvy : 2 * E.card ≤ y) :
    singularSeries E = (∏ p ∈ Nat.primesLE y, localHLFactor E p) *
      ∏' n : ℕ, singularSeriesTailFactor E y n := by
  let head : ℕ → ℝ := fun n => if n ∈ Nat.primesLE y then localHLFactor E n else 1
  have hhead : Multipliable head :=
    multipliable_of_ne_finset_one (s := Nat.primesLE y) fun n hn => if_neg hn
  have hheadprod : (∏' n : ℕ, head n) = ∏ p ∈ Nat.primesLE y, localHLFactor E p := by
    rw [tprod_eq_prod (s := Nat.primesLE y) (fun n hn => show head n = 1 from if_neg hn)]
    exact prod_congr rfl fun n hn => if_pos hn
  have hpoint : (fun n : ℕ => if Nat.Prime n then localHLFactor E n else 1) =
      fun n => head n * singularSeriesTailFactor E y n := by
    funext n
    by_cases hp : Nat.Prime n
    · by_cases hny : n ≤ y
      · have hmem : n ∈ Nat.primesLE y := Nat.mem_primesLE.mpr ⟨hny, hp⟩
        simp [head, singularSeriesTailFactor, hp, hmem, not_lt_of_ge hny]
      · have hlt : y < n := Nat.lt_of_not_ge hny
        have hnot : n ∉ Nat.primesLE y := fun h => hny (Nat.le_of_mem_primesLE h)
        simp [head, singularSeriesTailFactor, hp, hlt, hnot]
    · have hnot : n ∉ Nat.primesLE y := fun h => hp (Nat.prime_of_mem_primesLE h)
      simp [head, singularSeriesTailFactor, hp, hnot]
  unfold singularSeries
  rw [hpoint, hhead.tprod_mul (multipliable_singularSeriesTailFactor hE hSy hvy), hheadprod]

theorem finiteTupleSieveProduct_nonneg (E : Finset ℕ) (y : ℕ) :
    0 ≤ finiteTupleSieveProduct E y := by
  unfold finiteTupleSieveProduct
  apply prod_nonneg
  intro p hp
  have hpprime := Nat.prime_of_mem_primesLE hp
  letI : NeZero p := ⟨hpprime.ne_zero⟩
  have hres : residueCount E p ≤ p := by
    unfold residueCount
    simpa only [ZMod.card] using card_le_univ (E.image fun n : ℕ => (n : ZMod p))
  have hfrac : (residueCount E p : ℝ) / p ≤ 1 :=
    (div_le_one (Nat.cast_pos.mpr hpprime.pos : (0 : ℝ) < p)).mpr (Nat.cast_le.mpr hres)
  linarith

/-- The finite tuple product is the finite singular prefix times the
corresponding power of the Euler density. -/
theorem finiteTupleSieveProduct_eq_prefix_mul_euler (E : Finset ℕ) (y : ℕ) :
    finiteTupleSieveProduct E y =
      (∏ p ∈ Nat.primesLE y, localHLFactor E p) * eulerProdNat y ^ E.card := by
  unfold finiteTupleSieveProduct eulerProdNat
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hpprime := Nat.prime_of_mem_primesLE hp
  have hden : (1 - (p : ℝ)⁻¹) ^ E.card ≠ 0 :=
    pow_ne_zero _ (one_sub_inv_pos hpprime).ne'
  rw [localHLFactor, if_neg (not_le.mpr hpprime.one_lt)]
  simpa only [one_div] using
    (div_mul_cancel₀ (1 - (residueCount E p : ℝ) / p) hden).symm

/-- The genuine infinite singular series and the finite tuple product
differ only by the controlled tail. -/
theorem singularSeries_mul_euler_eq_finite_mul_tail {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hvy : 2 * E.card ≤ y) :
    singularSeries E * eulerProdNat y ^ E.card = finiteTupleSieveProduct E y *
      ∏' n : ℕ, singularSeriesTailFactor E y n := by
  rw [singularSeries_eq_prefix_mul_tail hE hSy hvy,
    finiteTupleSieveProduct_eq_prefix_mul_euler]
  ring

/-- Uniform relative finite-product completion.  The mild bound
`y ≥ 2 |E|²` makes the tail at least one half; no division by the
singular series or an admissibility assumption occurs. -/
theorem finiteTupleSieveProduct_relative_error_le {E : Finset ℕ} {S y : ℕ}
    (hE : ∀ n ∈ E, n ≤ S) (hSy : S < y) (hy : 2 ≤ y) (hvy2 : 2 * E.card ^ 2 ≤ y) :
    |finiteTupleSieveProduct E y - singularSeries E * eulerProdNat y ^ E.card| ≤
      (2 * (E.card : ℝ) ^ 2 / y) * (singularSeries E * eulerProdNat y ^ E.card) := by
  have hvquad : E.card ≤ E.card ^ 2 := by
    by_cases hv : E.card = 0
    · simp [hv]
    · have hv1 : 1 ≤ E.card := Nat.one_le_iff_ne_zero.mpr hv
      simpa only [pow_two, mul_one] using Nat.mul_le_mul_left E.card hv1
  have hvy : 2 * E.card ≤ y := (Nat.mul_le_mul_left 2 hvquad).trans hvy2
  have hypos : (0 : ℝ) < y := Nat.cast_pos.mpr (by omega)
  have ha : (E.card : ℝ) ^ 2 / y ≤ 1 / 2 := by
    have hcast : 2 * (E.card : ℝ) ^ 2 ≤ (y : ℝ) := by exact_mod_cast hvy2
    apply (div_le_iff₀ hypos).mpr
    linarith
  have ha0 : 0 ≤ (E.card : ℝ) ^ 2 / y := div_nonneg (sq_nonneg _) hypos.le
  have hQ := singularSeriesTail_tprod_bounds hE hSy hvy (by omega)
  have hQhalf : (1 / 2 : ℝ) ≤ ∏' n : ℕ, singularSeriesTailFactor E y n := by linarith [hQ.1]
  have hF := finiteTupleSieveProduct_nonneg E y
  have hid := singularSeries_mul_euler_eq_finite_mul_tail hE hSy hvy
  have hupper := mul_le_mul_of_nonneg_left hQ.2 hF
  have hlower := mul_le_mul_of_nonneg_left hQhalf hF
  have hdefect := mul_le_mul_of_nonneg_left hQ.1 hF
  have hmainnonneg : 0 ≤ singularSeries E * eulerProdNat y ^ E.card := by
    rw [hid]
    exact mul_nonneg hF (le_trans (by norm_num) hQhalf)
  have hdiffnonneg : 0 ≤ finiteTupleSieveProduct E y - singularSeries E * eulerProdNat y ^ E.card := by
    rw [hid]
    nlinarith
  rw [abs_of_nonneg hdiffnonneg]
  have hdouble : finiteTupleSieveProduct E y ≤ 2 * (singularSeries E * eulerProdNat y ^ E.card) := by
    rw [hid]
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hdouble ha0
  rw [← hid] at hdefect
  calc
    finiteTupleSieveProduct E y - singularSeries E * eulerProdNat y ^ E.card ≤
        ((E.card : ℝ) ^ 2 / y) * finiteTupleSieveProduct E y := by
      nlinarith only [hdefect]
    _ ≤ ((E.card : ℝ) ^ 2 / y) *
        (2 * (singularSeries E * eulerProdNat y ^ E.card)) := hscaled
    _ = (2 * (E.card : ℝ) ^ 2 / y) *
        (singularSeries E * eulerProdNat y ^ E.card) := by ring

end

end PrimeGapNormality.Prime
