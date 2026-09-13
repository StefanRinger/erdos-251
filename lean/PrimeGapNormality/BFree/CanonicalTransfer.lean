import PrimeGapNormality.BFree.Definitions
import PrimeGapNormality.BFree.Enumeration
import PrimeGapNormality.BFree.Series
import PrimeGapNormality.BFree.ProductRotation
import PrimeGapNormality.BFree.ReturnTowers
import PrimeGapNormality.Digital.GapAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical transfer: no `+1` per discarded modulus

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §6 (18)–(20);
`rounds/round92/01_gpt_positive_integer_carry.md` §4;
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN (counting lemmas; period product; `O(n)`; paper (20)/(23) Cesaro)
-/

namespace PrimeGapNormality.BFree

open PrimeGapNormality Finset Function Filter
open scoped Topology
open Classical

/-- Multiples of `d` in `{1,…,N}`: exactly `N / d`, no `+1`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (18).
Contract: C4
Audit: GREEN -/
theorem card_multiples_Icc_one {d N : ℕ} (hd : 0 < d) :
    #{n ∈ Icc 1 N | d ∣ n} = N / d := by
  let s : Finset ℕ := Icc 1 (N / d)
  have hinj : Set.InjOn (fun k : ℕ => d * k) (s : Set ℕ) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  have himg : s.image (fun k : ℕ => d * k) = (Icc 1 N).filter (fun n => d ∣ n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
      obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
      have hd1 : 1 ≤ d := Nat.succ_le_of_lt hd
      have hkN : d * k ≤ N := by
        simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hk2
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_le_mul hd1 hk1, hkN⟩, dvd_mul_right d k⟩
    · intro hn
      obtain ⟨hnI, hdvd⟩ := mem_filter.mp hn
      obtain ⟨h1, hN⟩ := mem_Icc.mp hnI
      obtain ⟨k, rfl⟩ := hdvd
      have hk0 : k ≠ 0 := by
        intro hk
        subst hk
        exact (not_le_of_gt (by decide : (0 : ℕ) < 1)) h1
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
      have hk2 : k ≤ N / d :=
        (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hN)
      exact mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk1, hk2⟩, rfl⟩
  rw [← himg, card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel]

theorem card_dvd_shift_le {d X j H : ℕ} (hd : 0 < d) (hj : j ≤ H) :
    #{n ∈ Icc 1 X | d ∣ n + j} ≤ (X + H) / d := by
  have hsub :
      ((Icc 1 X).filter (fun n => d ∣ n + j)).image (fun n => n + j) ⊆
        (Icc 1 (X + H)).filter (fun m => d ∣ m) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨hnI, hdvd⟩ := mem_filter.mp hn
    obtain ⟨h1, hX⟩ := mem_Icc.mp hnI
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨le_trans h1 (Nat.le_add_right n j), add_le_add hX hj⟩, hdvd⟩
  have hinj :
      Set.InjOn (fun n : ℕ => n + j)
        (((Icc 1 X).filter (fun n => d ∣ n + j)) : Set ℕ) :=
    fun a _ b _ h => Nat.add_right_cancel h
  have hle := card_le_card hsub
  have hcard :
      #(((Icc 1 X).filter (fun n => d ∣ n + j)).image (fun n => n + j)) =
        #{n ∈ Icc 1 X | d ∣ n + j} :=
    card_image_of_injOn hinj
  have hmul := card_multiples_Icc_one (d := d) (N := X + H) hd
  have : #{n ∈ Icc 1 X | d ∣ n + j} ≤ #{m ∈ Icc 1 (X + H) | d ∣ m} := by
    rw [← hcard]
    exact hle
  simpa [hmul] using this

/-- Exactly one residue class modulo `q` is killed by a coprime progression.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §6.
Contract: C4
Audit: GREEN -/
theorem card_dvd_coprime_progression {P' q a : ℕ} (hq : 0 < q)
    (hcop : Nat.Coprime P' q) :
    #{t ∈ range q | q ∣ a + t * P'} = 1 := by
  let : NeZero q := ⟨ne_of_gt hq⟩
  have hu : IsUnit (P' : ZMod q) := (ZMod.isUnit_iff_coprime P' q).mpr hcop
  obtain ⟨u, huP⟩ := hu
  let t0 : ℕ := ((-((a : ZMod q)) * (↑u⁻¹ : ZMod q)).val)
  have ht0 : t0 < q := ZMod.val_lt _
  have hzmod_t0 : (t0 : ZMod q) = -((a : ZMod q)) * (↑u⁻¹ : ZMod q) :=
    ZMod.natCast_zmod_val _
  have hcast (t : ℕ) : ((a + t * P' : ℕ) : ZMod q) =
      (a : ZMod q) + (t : ZMod q) * (P' : ZMod q) := by
    simp [Nat.cast_add, Nat.cast_mul]
  have hP1 : (↑u⁻¹ : ZMod q) * (P' : ZMod q) = 1 := by
    rw [← huP]
    exact Units.inv_mul u
  have hsolZ : (a : ZMod q) + (t0 : ZMod q) * (P' : ZMod q) = 0 := by
    rw [hzmod_t0]
    calc
      (a : ZMod q) + (-(a : ZMod q) * (↑u⁻¹ : ZMod q)) * (P' : ZMod q)
          = (a : ZMod q) + (-(a : ZMod q)) * ((↑u⁻¹ : ZMod q) * (P' : ZMod q)) := by
            ring
      _ = (a : ZMod q) + (-(a : ZMod q)) * 1 := by rw [hP1]
      _ = 0 := by ring
  have hsol : q ∣ a + t0 * P' :=
    (ZMod.natCast_eq_zero_iff (a + t0 * P') q).mp (by simpa [hcast] using hsolZ)
  have huniq : ∀ t ∈ range q, q ∣ a + t * P' → t = t0 := by
    intro t ht hdiv
    have htq : t < q := mem_range.mp ht
    have htZ : (a : ZMod q) + (t : ZMod q) * (P' : ZMod q) = 0 :=
      (by simpa [hcast] using (ZMod.natCast_eq_zero_iff (a + t * P') q).mpr hdiv)
    have hmul : (t : ZMod q) * (P' : ZMod q) = (t0 : ZMod q) * (P' : ZMod q) := by
      have := htZ.trans hsolZ.symm
      apply_fun (fun z => z - (a : ZMod q)) at this
      simpa using this
    have hteq : (t : ZMod q) = (t0 : ZMod q) := by
      have h0 : ((t : ZMod q) - t0) * (P' : ZMod q) = 0 := by
        simp [sub_mul, hmul]
      have hP1' : (P' : ZMod q) * (↑u⁻¹ : ZMod q) = 1 := by
        rw [mul_comm, hP1]
      have hsub : (t : ZMod q) - t0 = 0 := by
        calc
          (t : ZMod q) - t0
            = ((t : ZMod q) - t0) * 1 := (mul_one _).symm
          _ = ((t : ZMod q) - t0) * ((P' : ZMod q) * (↑u⁻¹ : ZMod q)) := by
            rw [hP1']
          _ = (((t : ZMod q) - t0) * (P' : ZMod q)) * (↑u⁻¹ : ZMod q) := by
            rw [mul_assoc]
          _ = 0 := by rw [h0, zero_mul]
      exact sub_eq_zero.mp hsub
    exact
      ((ZMod.val_cast_of_lt htq).symm.trans (congrArg ZMod.val hteq)).trans
        (ZMod.val_cast_of_lt ht0)
  refine card_eq_one.mpr ⟨t0, ?_⟩
  ext t
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · intro ⟨htq, hdiv⟩
    exact huniq t (mem_range.mpr htq) hdiv
  · intro h
    subst h
    exact ⟨ht0, hsol⟩

def residueSieve (F : AdmissibleFamily) (k n : ℕ) : Prop :=
  ∀ i < k, ¬ F.d i ∣ n

theorem residueSieve_zero (F : AdmissibleFamily) (n : ℕ) : residueSieve F 0 n :=
  fun i hi => (Nat.not_lt_zero i hi).elim

theorem residueSieve_succ_iff (F : AdmissibleFamily) (k n : ℕ) :
    residueSieve F (k + 1) n ↔ residueSieve F k n ∧ ¬ F.d k ∣ n := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self _)⟩
  · intro ⟨hk, hq⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact hk i hlt
    · exact hq

theorem residueSieve_add_period (F : AdmissibleFamily) {k a t : ℕ} :
    residueSieve F k (a + t * partialPeriod F k) ↔ residueSieve F k a := by
  constructor
  · intro h i hi hdiv
    have hdvdP := d_dvd_partialPeriod F hi
    have : F.d i ∣ a + t * partialPeriod F k :=
      dvd_add hdiv (dvd_mul_of_dvd_right hdvdP t)
    exact h i hi this
  · intro h i hi hdiv
    have hdvdP := d_dvd_partialPeriod F hi
    have htp : F.d i ∣ t * partialPeriod F k := dvd_mul_of_dvd_right hdvdP t
    exact h i hi ((Nat.dvd_add_iff_left htp).mpr hdiv)

theorem residueSieve_of_bfree (F : AdmissibleFamily) {k n : ℕ} (h : BFree F n) :
    residueSieve F k n :=
  fun i _ => h.2 i

theorem add_mul_lt_mul {a P' t q : ℕ} (ha : a < P') (ht : t < q) :
    a + t * P' < P' * q := by
  have hstep : a + t * P' < P' + t * P' := Nat.add_lt_add_right ha (t * P')
  have hrewrite : P' + t * P' = (t + 1) * P' := by
    rw [add_comm, Nat.succ_mul]
  have hle : (t + 1) * P' ≤ q * P' :=
    Nat.mul_le_mul_right P' (Nat.succ_le_of_lt ht)
  exact hstep.trans_le (hrewrite.trans_le (hle.trans_eq (Nat.mul_comm q P')))

theorem mem_range_prod {P' q : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ ((range P' ×ˢ range q) : Set (ℕ × ℕ))) :
    p.1 < P' ∧ p.2 < q := by
  have hp' : p.1 ∈ range P' ∧ p.2 ∈ range q := by
    simpa [Set.mem_prod] using hp
  exact ⟨mem_range.mp hp'.1, mem_range.mp hp'.2⟩

theorem injOn_add_mul_range (P' q : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2 * P')
      ((range P' ×ˢ range q) : Set (ℕ × ℕ)) := by
  intro p hp p' hp' h
  have hpP := (mem_range_prod hp).1
  have hpP' := (mem_range_prod hp').1
  have hpos : 0 < P' := Nat.zero_lt_of_lt hpP
  have hmod := congrArg (fun n => n % P') h
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hpP, Nat.mod_eq_of_lt hpP'] at hmod
  have hmul : p.2 * P' = p'.2 * P' := by
    have heq : p.1 + p.2 * P' = p'.1 + p'.2 * P' := h
    rw [hmod] at heq
    exact Nat.add_left_cancel heq
  exact Prod.ext hmod (Nat.eq_of_mul_eq_mul_right hpos hmul)

theorem image_add_mul_range (P' q : ℕ) :
    (range P' ×ˢ range q).image (fun p : ℕ × ℕ => p.1 + p.2 * P') =
      range (P' * q) := by
  ext n
  constructor
  · intro hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    exact mem_range.mpr
      (add_mul_lt_mul (mem_range.mp (mem_product.mp hp).1)
        (mem_range.mp (mem_product.mp hp).2))
  · intro hn
    have hnlt : n < P' * q := mem_range.mp hn
    by_cases hP : P' = 0
    · subst hP
      rw [zero_mul] at hnlt
      exact (Nat.not_lt_zero n hnlt).elim
    · have hpos : 0 < P' := Nat.pos_of_ne_zero hP
      refine mem_image.mpr ⟨(n % P', n / P'), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mem_range.mpr (Nat.mod_lt n hpos)
      · exact mem_range.mpr
          ((Nat.div_lt_iff_lt_mul hpos).mpr (by rwa [mul_comm] at hnlt))
      · rw [add_comm, Nat.div_add_mod']

theorem card_not_dvd_coprime_progression {P' q a : ℕ} (hq : 0 < q)
    (hcop : Nat.Coprime P' q) :
    #{t ∈ range q | ¬ q ∣ a + t * P'} = q - 1 := by
  have h1 := card_dvd_coprime_progression (P' := P') (q := q) (a := a) hq hcop
  have hsplit :=
    card_filter_add_card_filter_not (s := range q) (fun t => q ∣ a + t * P')
  have hx : 1 + #{t ∈ range q | ¬ q ∣ a + t * P'} = q := by
    simpa [h1, card_range] using hsplit
  have hq1 : 1 ≤ q := Nat.succ_le_of_lt hq
  have hqw : q = 1 + (q - 1) := by
    rw [add_comm, Nat.sub_add_cancel hq1]
  exact Nat.add_left_cancel (hx.trans hqw)

theorem card_residueSieve_range_mul (F : AdmissibleFamily) (k m : ℕ) :
    #{n ∈ range (m * partialPeriod F k) | residueSieve F k n} =
      m * #{a ∈ range (partialPeriod F k) | residueSieve F k a} := by
  let P' := partialPeriod F k
  let f : ℕ × ℕ → ℕ := fun p => p.1 + p.2 * P'
  have himg : (range P' ×ˢ range m).image f = range (P' * m) :=
    image_add_mul_range P' m
  have hinj := injOn_add_mul_range P' m
  have hpred : ∀ p : ℕ × ℕ, residueSieve F k (f p) ↔ residueSieve F k p.1 :=
    fun p => residueSieve_add_period (F := F) (k := k) (a := p.1) (t := p.2)
  rw [mul_comm m P', ← himg, filter_image]
  have hinj' :
      Set.InjOn f
        (((range P' ×ˢ range m).filter (fun p => residueSieve F k (f p))) :
          Set (ℕ × ℕ)) := by
    intro p hp p' hp' h
    have hpS : p ∈ ((range P' ×ˢ range m) : Set (ℕ × ℕ)) := by
      simpa using (mem_filter.mp hp).1
    have hpS' : p' ∈ ((range P' ×ˢ range m) : Set (ℕ × ℕ)) := by
      simpa using (mem_filter.mp hp').1
    exact hinj hpS hpS' h
  rw [card_image_of_injOn hinj']
  have hfilter :
      (range P' ×ˢ range m).filter (fun p => residueSieve F k (f p)) =
        (range P').filter (fun a => residueSieve F k a) ×ˢ range m := by
    have hpred' :
        (range P' ×ˢ range m).filter (fun p => residueSieve F k (f p)) =
          (range P' ×ˢ range m).filter (fun p => residueSieve F k p.1) := by
      ext p
      simp only [mem_filter, hpred]
    rw [hpred', filter_product_left (p := fun a => residueSieve F k a)]
  rw [hfilter, card_product, card_range, mul_comm]

/-- Period card is `∏ (d i - 1)`, not Euler `φ`. For `d = 4` the count is `3`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §6.
Contract: C4
Audit: GREEN -/
theorem card_residueSieve_period (F : AdmissibleFamily) (k : ℕ) :
    #{n ∈ range (partialPeriod F k) | residueSieve F k n} =
      ∏ i ∈ range k, (F.d i - 1) := by
  induction k with
  | zero =>
    simp [partialPeriod_zero, residueSieve_zero]
  | succ k ih =>
    let P' := partialPeriod F k
    let q := F.d k
    have hq : 0 < q := d_pos F k
    have hcop := coprime_partialPeriod F k
    rw [partialPeriod_succ, prod_range_succ]
    let f : ℕ × ℕ → ℕ := fun p => p.1 + p.2 * P'
    have himg : (range P' ×ˢ range q).image f = range (P' * q) :=
      image_add_mul_range P' q
    have hinj := injOn_add_mul_range P' q
    have hpred : ∀ p : ℕ × ℕ,
        residueSieve F (k + 1) (f p) ↔
          residueSieve F k p.1 ∧ ¬ q ∣ f p := by
      intro p
      rw [residueSieve_succ_iff, residueSieve_add_period]
    rw [← himg, filter_image]
    have hinj' :
        Set.InjOn f
          (((range P' ×ˢ range q).filter
              (fun p => residueSieve F (k + 1) (f p))) : Set (ℕ × ℕ)) := by
      intro p hp p' hp' h
      have hpS : p ∈ ((range P' ×ˢ range q) : Set (ℕ × ℕ)) := by
        simpa using (mem_filter.mp hp).1
      have hpS' : p' ∈ ((range P' ×ˢ range q) : Set (ℕ × ℕ)) := by
        simpa using (mem_filter.mp hp').1
      exact hinj hpS hpS' h
    rw [card_image_of_injOn hinj']
    have hfilter :
        (range P' ×ˢ range q).filter (fun p => residueSieve F (k + 1) (f p)) =
          ((range P').filter (fun a => residueSieve F k a) ×ˢ range q).filter
            (fun p => ¬ q ∣ f p) := by
      ext p
      simp only [mem_filter, mem_product, hpred]
      constructor
      · intro ⟨⟨hP, ht⟩, ⟨hs, hd⟩⟩
        exact ⟨⟨⟨hP, hs⟩, ht⟩, hd⟩
      · intro ⟨⟨⟨hP, hs⟩, ht⟩, hd⟩
        exact ⟨⟨hP, ht⟩, ⟨hs, hd⟩⟩
    rw [hfilter]
    set survivors := (range P').filter (fun a => residueSieve F k a)
    set pairs :=
      (survivors ×ˢ range q).filter (fun p => ¬ q ∣ p.1 + p.2 * P')
    have hpairs : pairs =
        (survivors ×ˢ range q).filter (fun p => ¬ q ∣ f p) := rfl
    have hmaps : (pairs : Set (ℕ × ℕ)).MapsTo (fun p => p.1) survivors := by
      intro p hp
      exact (mem_product.mp (mem_filter.mp hp).1).1
    have hfib :=
      card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1) (s := pairs)
        (t := survivors) hmaps
    have hfa : ∀ a ∈ survivors, #{p ∈ pairs | p.1 = a} = q - 1 := by
      intro a ha
      have himga :
          ((range q).filter (fun t => ¬ q ∣ a + t * P')).image
              (fun t => (a, t)) =
            pairs.filter (fun p => p.1 = a) := by
        ext p
        constructor
        · intro hp
          obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
          obtain ⟨htq, hdvd⟩ := mem_filter.mp ht
          refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨ha, htq⟩, hdvd⟩, rfl⟩
        · intro hp
          obtain ⟨hpairs, hfst⟩ := mem_filter.mp hp
          obtain ⟨hprod, hdvd⟩ := mem_filter.mp hpairs
          obtain ⟨_, ht⟩ := mem_product.mp hprod
          refine mem_image.mpr
            ⟨p.2, mem_filter.mpr ⟨ht, by rw [← hfst]; exact hdvd⟩, ?_⟩
          exact (Prod.ext hfst.symm rfl)
      have hinjt :
          Set.InjOn (fun t : ℕ => (a, t))
            ((range q).filter (fun t => ¬ q ∣ a + t * P') : Set ℕ) :=
        fun t _ t' _ h => (Prod.mk_right_injective a) h
      rw [← himga, card_image_of_injOn hinjt]
      exact card_not_dvd_coprime_progression hq hcop
    rw [hfib, sum_const_nat hfa, ih]

theorem card_residueSieve_Icc_eq_range (F : AdmissibleFamily) (k m : ℕ) :
    #{n ∈ Icc 1 (m * partialPeriod F k) | residueSieve F k n} =
      #{n ∈ range (m * partialPeriod F k) | residueSieve F k n} := by
  let P := partialPeriod F k
  let N := m * P
  by_cases hN : N = 0
  · have hm : m = 0 := by
      rcases Nat.mul_eq_zero.mp hN with hm | hP
      · exact hm
      · exact (ne_of_gt (partialPeriod_pos F k) hP).elim
    have : m * partialPeriod F k = 0 := hN
    simp [this]
  · have hpos : 0 < N := Nat.pos_of_ne_zero hN
    let g : ℕ → ℕ := fun n => if n = 0 then N else n
    have hg0 : g 0 = N := if_pos rfl
    have hgne : ∀ n, n ≠ 0 → g n = n := fun n hn => if_neg hn
    have hinj :
        Set.InjOn g ((range N).filter (residueSieve F k) : Set ℕ) := by
      intro a ha b hb heq
      have haR : a ∈ range N := (mem_filter.mp ha).1
      have hbR : b ∈ range N := (mem_filter.mp hb).1
      by_cases ha0 : a = 0
      · subst ha0
        by_cases hb0 : b = 0
        · exact hb0.symm
        · rw [hg0, hgne _ hb0] at heq
          exact (ne_of_lt (mem_range.mp hbR) heq.symm).elim
      · by_cases hb0 : b = 0
        · subst hb0
          rw [hgne _ ha0, hg0] at heq
          exact (ne_of_lt (mem_range.mp haR) heq).elim
        · rw [hgne _ ha0, hgne _ hb0] at heq
          exact heq
    have himg : ((range N).filter (residueSieve F k)).image g =
        (Icc 1 N).filter (residueSieve F k) := by
      ext n
      constructor
      · intro hn
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
        obtain ⟨haR, hres⟩ := mem_filter.mp ha
        by_cases ha0 : a = 0
        · subst ha0
          rw [hg0]
          have hresN : residueSieve F k N := by
            have hiff :=
              residueSieve_add_period (F := F) (k := k) (a := 0) (t := m)
            have hNP : 0 + m * P = N := by simp [N, P]
            exact hNP ▸ hiff.mpr hres
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_le_of_lt hpos, le_rfl⟩, hresN⟩
        · rw [hgne _ ha0]
          exact mem_filter.mpr
            ⟨mem_Icc.mpr
              ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha0),
                Nat.le_of_lt (mem_range.mp haR)⟩,
              hres⟩
      · intro hn
        obtain ⟨hnI, hres⟩ := mem_filter.mp hn
        obtain ⟨h1, hle⟩ := mem_Icc.mp hnI
        by_cases hnN : n = N
        · subst hnN
          refine mem_image.mpr ⟨0, ?_, hg0⟩
          have hres0 : residueSieve F k 0 := by
            have hiff :=
              residueSieve_add_period (F := F) (k := k) (a := 0) (t := m)
            have hNP : 0 + m * P = N := by simp [N, P]
            exact hiff.mp (hNP ▸ hres)
          exact mem_filter.mpr ⟨mem_range.mpr hpos, hres0⟩
        · have hnlt : n < N := lt_of_le_of_ne hle hnN
          have hn0 : n ≠ 0 := ne_of_gt (Nat.succ_le_iff.mp h1)
          exact mem_image.mpr ⟨n, mem_filter.mpr ⟨mem_range.mpr hnlt, hres⟩, hgne n hn0⟩
    rw [← himg, card_image_of_injOn hinj]

theorem card_residueSieve_Icc_mul (F : AdmissibleFamily) (k m : ℕ) :
    #{n ∈ Icc 1 (m * partialPeriod F k) | residueSieve F k n} =
      m * ∏ i ∈ range k, (F.d i - 1) := by
  rw [card_residueSieve_Icc_eq_range, card_residueSieve_range_mul,
    card_residueSieve_period]

theorem card_residueSieve_Icc_one_ge (F : AdmissibleFamily) (k X : ℕ) :
    (X / partialPeriod F k) * ∏ i ∈ range k, (F.d i - 1) ≤
      #{n ∈ Icc 1 X | residueSieve F k n} := by
  let P := partialPeriod F k
  let m := X / P
  have hle : m * P ≤ X := Nat.div_mul_le_self X P
  have hsub : Icc 1 (m * P) ⊆ Icc 1 X := Icc_subset_Icc_right hle
  have hcard := card_le_card (filter_subset_filter (residueSieve F k) hsub)
  have heq := card_residueSieve_Icc_mul F k m
  exact heq.symm.trans_le hcard

theorem finiteRho_eq_prod_div (F : AdmissibleFamily) (k : ℕ) :
    finiteRho F k =
      ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) / (partialPeriod F k : ℝ) := by
  have hfun : ∀ i, (1 : ℝ) - 1 / F.d i = ((F.d i - 1 : ℕ) : ℝ) / F.d i := by
    intro i
    have hcast : (F.d i : ℝ) - 1 = ((F.d i - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one, Nat.cast_sub (Nat.succ_le_of_lt (d_pos F i))]
    rw [one_sub_div (d_cast_ne_zero F i), hcast]
  simp only [finiteRho, partialPeriod]
  rw [prod_congr rfl fun i _ => hfun i, prod_div_distrib]
  rw [Nat.cast_prod (R := ℝ), Nat.cast_prod (R := ℝ)]

theorem finiteRho_ge_rho (F : AdmissibleFamily) (k : ℕ) :
    rho F ≤ finiteRho F k := by
  have ht : Tendsto (finiteRho F) atTop (𝓝 (rho F)) := by
    have hprod := (multipliable_rho F).tendsto_prod_tprod_nat
    have hfun : finiteRho F = fun n => ∏ i ∈ range n, (1 - (F.d i : ℝ)⁻¹) := by
      funext n
      simp [finiteRho, one_div]
    simpa [hfun, rho] using hprod
  have hle : ∀ n, k ≤ n → finiteRho F n ≤ finiteRho F k := by
    intro n hkn
    have hs : range k ⊆ range n := range_subset_range.mpr hkn
    have hsplit :
        finiteRho F n =
          finiteRho F k *
            ∏ i ∈ range n \ range k, (1 - (1 : ℝ) / F.d i) := by
      simp only [finiteRho]
      rw [← prod_sdiff hs, mul_comm]
    have hrest1 :
        ∏ i ∈ range n \ range k, (1 - (1 : ℝ) / F.d i) ≤ 1 :=
      prod_le_one
        (fun i _ => by rw [one_div]; exact (survivalFactor_pos F i).le)
        (fun i _ => by rw [one_div]; exact survivalFactor_le_one F i)
    rw [hsplit]
    exact mul_le_of_le_one_right (finiteRho_pos F k).le hrest1
  have hle' : ∀ n, finiteRho F (n + k) ≤ finiteRho F k :=
    fun n => hle (n + k) (Nat.le_add_left k n)
  have ht' : Tendsto (fun n => finiteRho F (n + k)) atTop (𝓝 (rho F)) :=
    ht.comp (tendsto_add_atTop_nat k)
  have hconst : Tendsto (fun _ : ℕ => finiteRho F k) atTop (𝓝 (finiteRho F k)) :=
    tendsto_const_nhds
  exact le_of_tendsto_of_tendsto ht' hconst (Eventually.of_forall hle')

theorem exists_sieve_cutoff (F : AdmissibleFamily) :
    ∃ k, ∑' i, (1 : ℝ) / F.d (i + k) < finiteRho F k / 2 := by
  have htail := tendsto_sum_nat_add (fun i => (1 : ℝ) / F.d i)
  have hmem : (0 : ℝ) ∈ Set.Iio (rho F / 2) := half_pos (rho_pos F)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (htail.eventually (isOpen_Iio.mem_nhds hmem))
  refine ⟨K, ?_⟩
  have hlt : ∑' i, (1 : ℝ) / F.d (i + K) < rho F / 2 := hK K le_rfl
  have hge : rho F / 2 ≤ finiteRho F K / 2 := by
    have := finiteRho_ge_rho F K
    linarith
  exact hlt.trans_le hge

theorem count_bfree_succ (F : AdmissibleFamily) (X : ℕ) :
    Nat.count (BFree F) (X + 1) = #{n ∈ Icc 1 X | BFree F n} := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [mem_filter, mem_range, mem_Icc]
  constructor
  · intro ⟨hn, hB⟩
    exact ⟨⟨Nat.succ_le_of_lt hB.1, Nat.lt_succ_iff.mp hn⟩, hB⟩
  · intro ⟨⟨_, hX⟩, hB⟩
    exact ⟨Nat.lt_succ_iff.mpr hX, hB⟩

theorem enum_le_of_card_bfree (F : AdmissibleFamily) {n X : ℕ}
    (h : n + 1 ≤ #{m ∈ Icc 1 X | BFree F m}) : enum F n ≤ X := by
  have hcnt : n + 1 ≤ Nat.count (BFree F) (X + 1) := by
    rwa [count_bfree_succ]
  have hlt : n < Nat.count (BFree F) (X + 1) := Nat.succ_le_iff.mp hcnt
  have henum : enum F n < X + 1 :=
    (Nat.lt_nth_iff_count_lt (bfree_infinite F)).mp hlt
  exact Nat.lt_succ_iff.mp henum

theorem card_exists_dvd_tail_le (F : AdmissibleFamily) (k X : ℕ) :
    (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n} : ℝ) ≤
      X * ∑' i, (1 : ℝ) / F.d (i + k) := by
  have hfin : {i : ℕ | F.d i ≤ X}.Finite :=
    (Set.finite_le_nat X).preimage fun a _ b _ hab => d_injective F hab
  let s := hfin.toFinset.filter (fun i => k ≤ i)
  have hsub :
      (Icc 1 X).filter (fun n => ∃ i, k ≤ i ∧ F.d i ∣ n) ⊆
        (Icc 1 X).filter (fun n => ∃ i ∈ s, F.d i ∣ n) := by
    intro n hn
    obtain ⟨hnI, ⟨i, hi, hdiv⟩⟩ := mem_filter.mp hn
    obtain ⟨h1, hX⟩ := mem_Icc.mp hnI
    have hdi : F.d i ≤ X :=
      le_trans (Nat.le_of_dvd (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1) hdiv) hX
    have himem : i ∈ hfin.toFinset := hfin.mem_toFinset.mpr hdi
    exact mem_filter.mpr ⟨hnI, ⟨i, mem_filter.mpr ⟨himem, hi⟩, hdiv⟩⟩
  have heq :
      (Icc 1 X).filter (fun n => ∃ i ∈ s, F.d i ∣ n) =
        s.biUnion (fun i => (Icc 1 X).filter (fun n => F.d i ∣ n)) := by
    ext n
    simp only [mem_filter, mem_biUnion]
    constructor
    · intro ⟨hI, ⟨i, his, hd⟩⟩
      exact ⟨i, his, ⟨hI, hd⟩⟩
    · intro ⟨i, his, ⟨hI, hd⟩⟩
      exact ⟨hI, ⟨i, his, hd⟩⟩
  have hle_card := card_le_card hsub
  have hbi :=
    (card_biUnion_le (s := s)
      (t := fun i => (Icc 1 X).filter (fun n => F.d i ∣ n)))
  have hsum :
      ∑ i ∈ s, #{n ∈ Icc 1 X | F.d i ∣ n} = ∑ i ∈ s, X / F.d i :=
    sum_congr rfl fun i _ => card_multiples_Icc_one (d_pos F i)
  have hcast :
      ((∑ i ∈ s, X / F.d i : ℕ) : ℝ) ≤ ∑ i ∈ s, (X : ℝ) / F.d i := by
    rw [Nat.cast_sum]
    exact sum_le_sum fun i _ => Nat.cast_div_le
  have hmul :
      ∑ i ∈ s, (X : ℝ) / F.d i = (X : ℝ) * ∑ i ∈ s, (1 : ℝ) / F.d i := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [div_eq_mul_one_div]
  have hsk : ∀ i ∈ s, k ≤ i := fun i hi => (mem_filter.mp hi).2
  have hinj : Set.InjOn (fun i : ℕ => i - k) (s : Set ℕ) := by
    intro a ha b hb heq
    have := congrArg (fun n => n + k) heq
    simpa [Nat.sub_add_cancel (hsk a ha), Nat.sub_add_cancel (hsk b hb)] using this
  have hre :
      ∑ i ∈ s, (1 : ℝ) / F.d i =
        ∑ j ∈ s.image (fun i => i - k), (1 : ℝ) / F.d (j + k) := by
    have himg :=
      sum_image (g := fun i : ℕ => i - k)
        (f := fun j : ℕ => (1 : ℝ) / F.d (j + k)) hinj
    refine (sum_congr rfl fun i hi => ?_).trans himg.symm
    rw [Nat.sub_add_cancel (hsk i hi)]
  have hshift : Summable fun i : ℕ => (1 : ℝ) / F.d (i + k) :=
    (summable_nat_add_iff (f := fun i => (1 : ℝ) / F.d i) k).2 F.summable
  have hts :=
    hshift.sum_le_tsum (s.image (fun i => i - k))
      (fun i _ => one_div_d_nonneg F (i + k))
  have hnat :
      (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n} : ℝ) ≤
        ((∑ i ∈ s, X / F.d i : ℕ) : ℝ) := by
    have : #{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n} ≤ ∑ i ∈ s, X / F.d i := by
      rw [← hsum]
      exact hle_card.trans (heq ▸ hbi)
    exact Nat.cast_le.mpr this
  calc
    (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n} : ℝ) ≤
        ((∑ i ∈ s, X / F.d i : ℕ) : ℝ) :=
      hnat
    _ ≤ ∑ i ∈ s, (X : ℝ) / F.d i := hcast
    _ = (X : ℝ) * ∑ i ∈ s, (1 : ℝ) / F.d i := hmul
    _ = (X : ℝ) * ∑ j ∈ s.image (fun i => i - k), (1 : ℝ) / F.d (j + k) := by
        rw [hre]
    _ ≤ (X : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) :=
      mul_le_mul_of_nonneg_left hts (Nat.cast_nonneg _)

theorem card_bfree_Icc_one_ge (F : AdmissibleFamily) (k X : ℕ) :
    (#{n ∈ Icc 1 X | BFree F n} : ℝ) ≥
      finiteRho F k * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) -
        X * ∑' i, (1 : ℝ) / F.d (i + k) := by
  let P := partialPeriod F k
  have hPpos : 0 < P := partialPeriod_pos F k
  have hP0 : (P : ℝ) ≠ 0 := (Nat.cast_pos.mpr hPpos).ne'
  let S := #{n ∈ Icc 1 X | residueSieve F k n}
  let Q := #{n ∈ Icc 1 X | BFree F n}
  have hfilter :
      (Icc 1 X).filter (BFree F) =
        ((Icc 1 X).filter (residueSieve F k)).filter (BFree F) := by
    ext n
    simp only [mem_filter]
    constructor
    · intro ⟨hI, hB⟩
      exact ⟨⟨hI, residueSieve_of_bfree F hB⟩, hB⟩
    · intro ⟨⟨hI, _⟩, hB⟩
      exact ⟨hI, hB⟩
  have hsplit :=
    card_filter_add_card_filter_not
      (s := (Icc 1 X).filter (residueSieve F k)) (BFree F)
  have hQ : Q + #{n ∈ (Icc 1 X).filter (residueSieve F k) | ¬ BFree F n} = S := by
    simpa [hfilter, Q, S] using hsplit
  have hextra :
      #{n ∈ (Icc 1 X).filter (residueSieve F k) | ¬ BFree F n} ≤
        #{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n} := by
    apply card_le_card
    intro n hn
    obtain ⟨hsieve, hnot⟩ := mem_filter.mp hn
    obtain ⟨hI, hres⟩ := mem_filter.mp hsieve
    obtain ⟨h1, _⟩ := mem_Icc.mp hI
    have : ∃ i, F.d i ∣ n := by
      by_contra hnone
      exact hnot ⟨lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1, fun i hdiv =>
        hnone ⟨i, hdiv⟩⟩
    obtain ⟨i, hdiv⟩ := this
    have hik : k ≤ i := by
      by_contra hki
      exact hres i (Nat.not_le.mp hki) hdiv
    exact mem_filter.mpr ⟨hI, ⟨i, hik, hdiv⟩⟩
  have hQreal : (Q : ℝ) = (S : ℝ) -
      #{n ∈ (Icc 1 X).filter (residueSieve F k) | ¬ BFree F n} := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hQ
    simp [Nat.cast_add] at this
    linarith
  have hSge : (X / P) * ∏ i ∈ range k, (F.d i - 1) ≤ S :=
    card_residueSieve_Icc_one_ge F k X
  have hSreal : ((X / P * ∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) ≤ (S : ℝ) :=
    Nat.cast_le.mpr hSge
  have hρeq := finiteRho_eq_prod_div F k
  have hprodP :
      ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) = finiteRho F k * P := by
    rw [hρeq, div_mul_cancel₀ _ hP0]
  have hdivmod : ((X / P : ℕ) * P : ℝ) = (X : ℝ) - ((X % P : ℕ) : ℝ) := by
    have hnat : (X / P) * P + X % P = X := Nat.div_add_mod' X P
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
    simp [Nat.cast_add, Nat.cast_mul] at hcast
    linarith
  have hmodle : ((X % P : ℕ) : ℝ) ≤ P :=
    (Nat.cast_lt.mpr (Nat.mod_lt X hPpos)).le
  have hperiod :
      ((X / P : ℕ) * P : ℝ) ≥ (X : ℝ) - P := by
    rw [hdivmod]
    linarith
  have hSρ : finiteRho F k * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) ≤ (S : ℝ) := by
    have : ((X / P : ℕ) : ℝ) * ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) ≤ (S : ℝ) := by
      simpa [Nat.cast_mul] using hSreal
    have hrew :
        ((X / P : ℕ) : ℝ) * ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) =
          ((X / P : ℕ) * P : ℝ) * finiteRho F k := by
      rw [hprodP]
      ring
    have : ((X / P : ℕ) * P : ℝ) * finiteRho F k ≥
        ((X : ℝ) - P) * finiteRho F k :=
      mul_le_mul_of_nonneg_right hperiod (finiteRho_pos F k).le
    have hfinP : finiteRho F k * P = ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) :=
      hprodP.symm
    have : ((X : ℝ) - P) * finiteRho F k =
        finiteRho F k * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) := by
      rw [sub_mul, mul_comm (P : ℝ) (finiteRho F k), hfinP]
      ring
    linarith
  have htail := card_exists_dvd_tail_le F k X
  have hextraR :
      (#{n ∈ (Icc 1 X).filter (residueSieve F k) | ¬ BFree F n} : ℝ) ≤
        X * ∑' i, (1 : ℝ) / F.d (i + k) :=
    (Nat.cast_le.mpr hextra).trans htail
  linarith [hQreal, hSρ, hextraR]

/-- Survival counting `Q(X)` is at least linear in `X`, after a finite sieve cutoff.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (20).
Contract: C4
Audit: GREEN -/
theorem card_bfree_Icc_one_ge_half (F : AdmissibleFamily) {k : ℕ}
    (htail : ∑' i, (1 : ℝ) / F.d (i + k) < finiteRho F k / 2) (X : ℕ) :
    finiteRho F k / 2 * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) ≤
      #{n ∈ Icc 1 X | BFree F n} := by
  have hQ := card_bfree_Icc_one_ge F k X
  have hρ : 0 ≤ finiteRho F k := (finiteRho_pos F k).le
  have hX : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
  have htail_le : ∑' i, (1 : ℝ) / F.d (i + k) ≤ finiteRho F k / 2 := htail.le
  have :
      finiteRho F k * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) -
          X * ∑' i, (1 : ℝ) / F.d (i + k) ≥
        finiteRho F k / 2 * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) := by
    have hmul : X * ∑' i, (1 : ℝ) / F.d (i + k) ≤ X * (finiteRho F k / 2) :=
      mul_le_mul_of_nonneg_left htail_le hX
    linarith
  exact this.trans hQ

/-- `enum F n = O(n)`. The constant may depend on `F`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (20).
Contract: C4
Audit: GREEN -/
theorem enum_linear_bound (F : AdmissibleFamily) :
    ∃ C : ℝ, ∀ n, (enum F n : ℝ) ≤ C * (n + 1) := by
  obtain ⟨k, htail⟩ := exists_sieve_cutoff F
  let δ : ℝ := finiteRho F k / 2
  let C0 : ℝ := ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ)
  have hδ : 0 < δ := half_pos (finiteRho_pos F k)
  have hC0 : 0 ≤ C0 := by
    change 0 ≤ ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ)
    exact Nat.cast_nonneg _
  refine ⟨(1 + C0) / δ + 1, fun n => ?_⟩
  let y : ℝ := ((n + 1 : ℝ) + C0) / δ
  have hy0 : 0 ≤ y :=
    div_nonneg
      (add_nonneg (add_nonneg (Nat.cast_nonneg n) (zero_le_one : (0 : ℝ) ≤ 1)) hC0)
      hδ.le
  let X : ℕ := Nat.ceil y
  have hXy : y ≤ X := Nat.le_ceil y
  have hδX : (n + 1 : ℝ) + C0 ≤ δ * X := (div_le_iff₀' hδ).mp hXy
  have hQreal :
      finiteRho F k / 2 * X - C0 ≤ #{m ∈ Icc 1 X | BFree F m} :=
    card_bfree_Icc_one_ge_half F htail X
  have hnQ : (n + 1 : ℝ) ≤ #{m ∈ Icc 1 X | BFree F m} := by
    have : (n + 1 : ℝ) ≤ δ * X - C0 := by linarith
    exact this.trans hQreal
  have hnat : n + 1 ≤ #{m ∈ Icc 1 X | BFree F m} := by exact_mod_cast hnQ
  have henum : enum F n ≤ X := enum_le_of_card_bfree F hnat
  have hXle : (X : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hy1 : y + 1 ≤ ((1 + C0) / δ + 1) * (n + 1) := by
    have h1 : (1 : ℝ) ≤ n + 1 := by
      exact_mod_cast (Nat.le_add_left (1 : ℕ) n)
    have hC : C0 ≤ C0 * (n + 1) := le_mul_of_one_le_right hC0 h1
    have hnum : (n + 1 : ℝ) + C0 ≤ (1 + C0) * (n + 1) := by linarith
    have hdiv : y ≤ ((1 + C0) / δ) * (n + 1) := by
      change ((n + 1 : ℝ) + C0) / δ ≤ ((1 + C0) / δ) * (n + 1)
      rw [div_le_iff₀' hδ, ← mul_assoc, mul_div_cancel₀ _ hδ.ne']
      exact hnum
    have hone : (1 : ℝ) ≤ 1 * (n + 1) := by
      rw [one_mul]
      exact h1
    linarith
  have : (enum F n : ℝ) ≤ X := Nat.cast_le.mpr henum
  have : (enum F n : ℝ) < y + 1 := this.trans_lt hXle
  exact this.le.trans hy1

theorem tendsto_finiteRho (F : AdmissibleFamily) :
    Tendsto (finiteRho F) atTop (𝓝 (rho F)) := by
  have hprod := (multipliable_rho F).tendsto_prod_tprod_nat
  have hfun : finiteRho F = fun n => ∏ i ∈ range n, (1 - (F.d i : ℝ)⁻¹) := by
    funext n
    simp [finiteRho, one_div]
  simpa [hfun, rho] using hprod

theorem tendsto_tail_one_div_d (F : AdmissibleFamily) :
    Tendsto (fun k : ℕ => ∑' i, (1 : ℝ) / F.d (i + k)) atTop (𝓝 0) :=
  tendsto_sum_nat_add fun i => (1 : ℝ) / F.d i

theorem card_residueSieve_Icc_one_le (F : AdmissibleFamily) (k X : ℕ) :
    #{n ∈ Icc 1 X | residueSieve F k n} ≤
      (X / partialPeriod F k + 1) * ∏ i ∈ range k, (F.d i - 1) := by
  let P := partialPeriod F k
  let m := X / P + 1
  have hP : 0 < P := partialPeriod_pos F k
  have hlt : X < m * P := by
    have hmod := Nat.mod_lt X hP
    have hdeq : (X / P) * P + X % P = X := Nat.div_add_mod' X P
    have hm : m * P = (X / P) * P + P := by
      simp [m, add_mul, one_mul]
    rw [← hdeq, hm]
    exact Nat.add_lt_add_left hmod _
  have hsub : Icc 1 X ⊆ Icc 1 (m * P) := Icc_subset_Icc_right (Nat.le_of_lt hlt)
  have hcard := card_le_card (filter_subset_filter (residueSieve F k) hsub)
  have heq := card_residueSieve_Icc_mul F k m
  exact hcard.trans_eq heq

theorem card_bfree_le_residueSieve (F : AdmissibleFamily) (k X : ℕ) :
    #{n ∈ Icc 1 X | BFree F n} ≤ #{n ∈ Icc 1 X | residueSieve F k n} := by
  refine card_le_card ?_
  intro n hn
  obtain ⟨hI, hB⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hI, residueSieve_of_bfree F hB⟩

theorem card_bfree_Icc_one_le (F : AdmissibleFamily) (k X : ℕ) :
    (#{n ∈ Icc 1 X | BFree F n} : ℝ) ≤
      finiteRho F k * X + ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) := by
  let P := partialPeriod F k
  have hPpos : 0 < P := partialPeriod_pos F k
  have hP0 : (P : ℝ) ≠ 0 := (Nat.cast_pos.mpr hPpos).ne'
  let C0 : ℝ := ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ)
  let m : ℕ := X / P + 1
  have hQleS := card_bfree_le_residueSieve F k X
  have hSle := card_residueSieve_Icc_one_le F k X
  have hnat : #{n ∈ Icc 1 X | BFree F n} ≤ m * ∏ i ∈ range k, (F.d i - 1) :=
    hQleS.trans hSle
  have hreal : (#{n ∈ Icc 1 X | BFree F n} : ℝ) ≤ (m : ℝ) * C0 := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [Nat.cast_mul (α := ℝ)] at hcast
    exact hcast
  have hm : (m : ℝ) = ((X / P : ℕ) : ℝ) + 1 := Nat.cast_succ (R := ℝ) (X / P)
  have hsplit : (m : ℝ) * C0 = ((X / P : ℕ) : ℝ) * C0 + C0 := by
    rw [hm, add_mul, one_mul]
  have hρeq := finiteRho_eq_prod_div F k
  have hprodP : C0 = finiteRho F k * (P : ℝ) := by
    rw [hρeq, div_mul_cancel₀ _ hP0]
  have hdiv : ((X / P : ℕ) : ℝ) * (P : ℝ) ≤ (X : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr (Nat.div_mul_le_self X P)
    rwa [Nat.cast_mul (α := ℝ)] at this
  have hmain : ((X / P : ℕ) : ℝ) * C0 ≤ finiteRho F k * X := by
    rw [hprodP, mul_comm (finiteRho F k) (P : ℝ), ← mul_assoc]
    have : ((X / P : ℕ) : ℝ) * (P : ℝ) * finiteRho F k ≤ (X : ℝ) * finiteRho F k :=
      mul_le_mul_of_nonneg_right hdiv (finiteRho_pos F k).le
    simpa [mul_comm (finiteRho F k) (X : ℝ)] using this
  linarith

theorem card_bfree_div_le (F : AdmissibleFamily) (k X : ℕ) (hX : 1 ≤ X) :
    (#{n ∈ Icc 1 X | BFree F n} : ℝ) / X ≤
      finiteRho F k + ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) / X := by
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hX)
  have hQ := card_bfree_Icc_one_le F k X
  have hdiv := div_le_div_of_nonneg_right hQ hXpos.le
  have hrew :
      (finiteRho F k * X + ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ)) / X =
        finiteRho F k + ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) / X := by
    rw [add_div, mul_div_cancel_right₀ _ hXpos.ne']
  exact hdiv.trans_eq hrew

theorem card_bfree_div_ge (F : AdmissibleFamily) (k X : ℕ) (hX : 1 ≤ X) :
    finiteRho F k - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) / X -
        ∑' i, (1 : ℝ) / F.d (i + k) ≤
      (#{n ∈ Icc 1 X | BFree F n} : ℝ) / X := by
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hX)
  have hQ := card_bfree_Icc_one_ge F k X
  have hdiv := div_le_div_of_nonneg_right hQ.le hXpos.le
  have hrew :
      (finiteRho F k * X - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) -
          X * ∑' i, (1 : ℝ) / F.d (i + k)) / X =
        finiteRho F k - ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) / X -
          ∑' i, (1 : ℝ) / F.d (i + k) := by
    rw [sub_div, sub_div, mul_div_cancel_right₀ _ hXpos.ne',
      mul_comm (X : ℝ), mul_div_cancel_right₀ _ hXpos.ne']
  exact hrew.symm.trans_le hdiv

theorem card_bfree_div_near_rho (F : AdmissibleFamily) (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hρ : |finiteRho F k - rho F| < ε / 3)
    (hτ : ∑' i, (1 : ℝ) / F.d (i + k) < ε / 3) :
    ∀ᶠ X : ℕ in atTop,
      |(#{n ∈ Icc 1 X | BFree F n} : ℝ) / X - rho F| < ε := by
  let C0 : ℝ := ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ)
  have hC0 : 0 ≤ C0 := Nat.cast_nonneg _
  have hε3 : 0 < ε / 3 := by positivity
  have hC0X : Tendsto (fun X : ℕ => C0 / (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C0
  have hge : ∀ᶠ X : ℕ in atTop, 1 ≤ X := eventually_ge_atTop 1
  have hsmall : ∀ᶠ X : ℕ in atTop, dist (C0 / (X : ℝ)) 0 < ε / 3 :=
    hC0X.eventually (Metric.ball_mem_nhds (0 : ℝ) hε3)
  filter_upwards [hge, hsmall] with X hX hC0ε
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hX)
  have hC0div : C0 / X < ε / 3 := by
    have hdist : dist (C0 / X) (0 : ℝ) = |C0 / X| := by
      rw [Real.dist_eq, sub_zero]
    have habs : |C0 / X| < ε / 3 := by
      rwa [hdist] at hC0ε
    rwa [abs_of_nonneg (div_nonneg hC0 hXpos.le)] at habs
  have hupper := card_bfree_div_le F k X hX
  have hlower := card_bfree_div_ge F k X hX
  have hρle : rho F ≤ finiteRho F k := finiteRho_ge_rho F k
  have hρdiff : finiteRho F k - rho F < ε / 3 := by
    have : |finiteRho F k - rho F| = finiteRho F k - rho F :=
      abs_of_nonneg (sub_nonneg.mpr hρle)
    rwa [this] at hρ
  have hC0eq : C0 = ((∏ i ∈ range k, (F.d i - 1) : ℕ) : ℝ) := rfl
  rw [abs_sub_lt_iff]
  constructor
  · have h1 : (#{n ∈ Icc 1 X | BFree F n} : ℝ) / X - rho F ≤
        finiteRho F k - rho F + C0 / X := by
      linarith [hupper, hC0eq]
    linarith
  · have h1 : rho F - (#{n ∈ Icc 1 X | BFree F n} : ℝ) / X ≤
        C0 / X + ∑' i, (1 : ℝ) / F.d (i + k) := by
      linarith [hlower, hρle, hC0eq]
    linarith

/-- Counting density `Q(X)/X → ρ`. Paper (20), first half.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (20);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem tendsto_card_bfree_div (F : AdmissibleFamily) :
    Tendsto (fun X : ℕ => (#{n ∈ Icc 1 X | BFree F n} : ℝ) / X) atTop (𝓝 (rho F)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε3 : 0 < ε / 3 := by positivity
  have hρev :=
    (tendsto_finiteRho F).eventually (Metric.ball_mem_nhds (rho F) hε3)
  have hτev :=
    (tendsto_tail_one_div_d F).eventually (Metric.ball_mem_nhds (0 : ℝ) hε3)
  obtain ⟨k, hk⟩ := (hρev.and hτev).exists
  have hρ : |finiteRho F k - rho F| < ε / 3 := by
    simpa [Real.dist_eq] using hk.1
  have hτabs : |∑' i, (1 : ℝ) / F.d (i + k)| < ε / 3 := by
    simpa [Real.dist_eq] using hk.2
  have hτnonneg : 0 ≤ ∑' i, (1 : ℝ) / F.d (i + k) :=
    tsum_nonneg fun i => one_div_d_nonneg F (i + k)
  have hτ : ∑' i, (1 : ℝ) / F.d (i + k) < ε / 3 := by
    rwa [abs_of_nonneg hτnonneg] at hτabs
  exact card_bfree_div_near_rho F k hε hρ hτ

theorem card_bfree_enum (F : AdmissibleFamily) (N : ℕ) :
    #{n ∈ Icc 1 (enum F N) | BFree F n} = N + 1 := by
  rw [← count_bfree_succ]
  exact Nat.count_nth_succ_of_infinite (bfree_infinite F) N

/-- `a_N / N → 1/ρ`. Paper (20), inverted at `X = a_N`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (20);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem tendsto_enum_div_n (F : AdmissibleFamily) :
    Tendsto (fun N : ℕ => (enum F N : ℝ) / (N + 1)) atTop (𝓝 (rho F)⁻¹) := by
  have hcomp := (tendsto_card_bfree_div F).comp (enum_strictMono F).tendsto_atTop
  have hratio : Tendsto (fun N : ℕ => (N + 1 : ℝ) / (enum F N : ℝ)) atTop (𝓝 (rho F)) := by
    refine (tendsto_congr fun N => ?_).mp hcomp
    rw [Function.comp_apply, card_bfree_enum, Nat.cast_succ]
  have hinv := hratio.inv₀ (rho_pos F).ne'
  refine (tendsto_congr fun N => ?_).mp hinv
  exact inv_div (N + 1 : ℝ) (enum F N : ℝ)

theorem sum_gap_enum (F : AdmissibleFamily) (j N : ℕ) :
    ∑ n ∈ range N, (gap (enum F) (n + j) : ℝ) =
      (enum F (N + j) : ℝ) - enum F j := by
  have h :=
    congrArg (fun z : ℤ => (z : ℝ)) (sum_gap_int (enum_strictMono F) j N)
  simp only [Int.cast_sum, Int.cast_sub, Int.cast_natCast] at h
  have hidx :
      ∑ n ∈ range N, (gap (enum F) (n + j) : ℝ) =
        ∑ n ∈ range N, (gap (enum F) (j + n) : ℝ) :=
    sum_congr rfl fun n _ => by rw [add_comm]
  rw [hidx, h, add_comm j N]

theorem tendsto_succ_add_div_self (j : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) + (j : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
  have h :=
    tendsto_add_mul_div_add_mul_atTop_nhds ((j : ℝ) + 1) (0 : ℝ) (1 : ℝ)
      (one_ne_zero : (1 : ℝ) ≠ 0)
  have hfun :
      (fun N : ℕ => ((N : ℝ) + (j : ℝ) + 1) / (N : ℝ)) =
        fun N : ℕ => (((j : ℝ) + 1) + (1 : ℝ) * (N : ℝ)) /
          ((0 : ℝ) + (1 : ℝ) * (N : ℝ)) := by
    funext N
    ring
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + (j : ℝ) + 1) / (N : ℝ)) atTop
      (𝓝 ((1 : ℝ) / 1)) := by
    rwa [hfun]
  rw [div_one (1 : ℝ)] at h1
  exact h1

theorem tendsto_enum_add_div_nat (F : AdmissibleFamily) (j : ℕ) :
    Tendsto (fun N : ℕ => (enum F (N + j) : ℝ) / N) atTop (𝓝 (rho F)⁻¹) := by
  have h1 := (tendsto_enum_div_n F).comp (tendsto_add_atTop_nat j)
  have h2 := tendsto_succ_add_div_self j
  have hmul := h1.mul h2
  have hlim : (rho F)⁻¹ * 1 = (rho F)⁻¹ := mul_one _
  refine (tendsto_congr fun N => ?_).mp (hlim ▸ hmul)
  have hden_eq : ((N + j : ℕ) : ℝ) + 1 = (N : ℝ) + (j : ℝ) + 1 := by
    rw [Nat.cast_add (R := ℝ) N j]
  change
    ((enum F (N + j) : ℝ) / (((N + j : ℕ) : ℝ) + 1)) *
        (((N : ℝ) + (j : ℝ) + 1) / (N : ℝ)) =
      (enum F (N + j) : ℝ) / (N : ℝ)
  by_cases hN : N = 0
  · subst hN
    simp
  · have hden : (N : ℝ) + (j : ℝ) + 1 ≠ 0 := by
      have : (0 : ℝ) < (N : ℝ) + (j : ℝ) + 1 := by
        have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
        linarith
      exact this.ne'
    rw [hden_eq]
    rw [div_mul_div_comm, mul_comm (enum F (N + j) : ℝ), mul_div_mul_left _ _ hden]

/-- Cesaro of shifted gaps: `(a_{N+j+1} - a_{j+1}) / N → 1/ρ`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (20)–(23);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem tendsto_cesaro_gap (F : AdmissibleFamily) (j : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (gap (enum F) (n + j) : ℝ)) / N)
      atTop (𝓝 (rho F)⁻¹) := by
  have hsum := tendsto_enum_add_div_nat F j
  have hj : Tendsto (fun N : ℕ => (enum F j : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (enum F j : ℝ)
  have hsub := hsum.sub hj
  have hlim : (rho F)⁻¹ - 0 = (rho F)⁻¹ := sub_zero _
  refine (tendsto_congr fun N => ?_).mp (hlim ▸ hsub)
  rw [← sub_div, sum_gap_enum]

theorem exists_enum_linear_bound_nonneg (F : AdmissibleFamily) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, (enum F n : ℝ) ≤ C * (n + 1) := by
  obtain ⟨C0, hC0⟩ := enum_linear_bound F
  refine ⟨max C0 0, le_max_right _ _, fun n => ?_⟩
  exact (hC0 n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem gap_le_linear_bound (F : AdmissibleFamily) {C : ℝ}
    (hC : ∀ n, (enum F n : ℝ) ≤ C * (n + 1)) (n : ℕ) :
    (gap (enum F) n : ℝ) ≤ C * (n + 2 : ℝ) := by
  have h := (gap_le_enum_succ F n).trans (by simpa using hC (n + 1))
  have h2 : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by
    rw [add_assoc, one_add_one_eq_two]
  rwa [h2] at h

theorem cesaro_gap_le_of_linear (F : AdmissibleFamily) {C : ℝ}
    (hC : ∀ n, (enum F n : ℝ) ≤ C * (n + 1)) (hC0 : 0 ≤ C) (j N : ℕ) :
    (∑ n ∈ range N, (gap (enum F) (n + j) : ℝ)) / N ≤ C * ((j : ℝ) + 2) := by
  by_cases hN : N = 0
  · subst hN
    simp
    exact mul_nonneg hC0 (by positivity)
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
    rw [sum_gap_enum]
    have hnum : (enum F (N + j) : ℝ) - enum F j ≤ enum F (N + j) := by
      have : (0 : ℝ) ≤ enum F j := Nat.cast_nonneg _
      linarith
    have hfrac : ((N : ℝ) + (j : ℝ) + 1) / N ≤ (j : ℝ) + 2 := by
      have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
      have hrew : ((N : ℝ) + (j : ℝ) + 1) / N = 1 + ((j : ℝ) + 1) / N := by
        field_simp [hN0]
        ring
      have hle : ((j : ℝ) + 1) / N ≤ (j : ℝ) + 1 :=
        div_le_self (by positivity) hN1
      rw [hrew]
      linarith
    have hcast : ((N + j : ℕ) : ℝ) + 1 = (N : ℝ) + (j : ℝ) + 1 := by
      rw [Nat.cast_add (R := ℝ) N j]
    calc
      ((enum F (N + j) : ℝ) - enum F j) / N
          ≤ (enum F (N + j) : ℝ) / N :=
        div_le_div_of_nonneg_right hnum hNpos.le
      _ ≤ C * (((N + j : ℕ) : ℝ) + 1) / N :=
        div_le_div_of_nonneg_right (hC (N + j)) hNpos.le
      _ = C * ((((N + j : ℕ) : ℝ) + 1) / N) := by
        rw [mul_div_assoc]
      _ = C * (((N : ℝ) + (j : ℝ) + 1) / N) := by
        rw [hcast]
      _ ≤ C * ((j : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hfrac hC0

theorem summable_linear_geom {b : ℕ} (hb : 2 ≤ b) (m : ℝ) :
    Summable fun j : ℕ => (m + j + 2 : ℝ) * (b : ℝ)⁻¹ ^ j := by
  have hlin := summable_add_two_mul_geometric hb
  have hgeo := summable_geometric_of_norm_lt_one (K := ℝ) (inv_b_norm_lt_one hb)
  have hm := hgeo.mul_left m
  have hs := hm.add hlin
  have hfun :
      (fun j : ℕ => (m + j + 2 : ℝ) * (b : ℝ)⁻¹ ^ j) =
        fun j : ℕ => m * (b : ℝ)⁻¹ ^ j + (j + 2 : ℝ) * (b : ℝ)⁻¹ ^ j := by
    funext j
    ring
  rw [hfun]
  exact hs

theorem summable_gap_pow (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    Summable fun j : ℕ =>
      (gap (enum F) (m + j) : ℝ) / (b : ℝ) ^ (j + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_enum_linear_bound_nonneg F
  have hnn : ∀ j, 0 ≤ (gap (enum F) (m + j) : ℝ) / (b : ℝ) ^ (j + 1) :=
    fun j => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hdom : Summable fun j : ℕ => C * (m + j + 2 : ℝ) / (b : ℝ) ^ (j + 1) := by
    have hsum := summable_linear_geom hb (m : ℝ)
    have hmul := hsum.mul_left (C / b)
    have hfun : (fun j : ℕ => C * (m + j + 2 : ℝ) / (b : ℝ) ^ (j + 1)) =
        fun j : ℕ => C / b * ((m + j + 2 : ℝ) * (b : ℝ)⁻¹ ^ j) :=
      funext fun j => scaled_geom C hb j (m + j + 2)
    rw [hfun]
    exact hmul
  refine Summable.of_nonneg_of_le hnn (fun j => ?_) hdom
  have hgap := gap_le_linear_bound F hC (m + j)
  have hcast : ((m + j : ℕ) : ℝ) + 2 = (m : ℝ) + j + 2 := by
    rw [Nat.cast_add (R := ℝ) m j]
  have hgap' : (gap (enum F) (m + j) : ℝ) ≤ C * ((m : ℝ) + j + 2) := by
    rw [hcast] at hgap
    exact hgap
  exact div_le_div_of_nonneg_right hgap' (pow_nonneg (Nat.cast_nonneg _) _)

noncomputable def canonicalGapTail (F : AdmissibleFamily) (b n : ℕ) : ℝ :=
  ∑' j, (gap (enum F) (n + j) : ℝ) / (b : ℝ) ^ (j + 1)

noncomputable def canonicalGapTailTrunc (F : AdmissibleFamily) (b J n : ℕ) : ℝ :=
  ∑ j ∈ range J, (gap (enum F) (n + j) : ℝ) / (b : ℝ) ^ (j + 1)

theorem summable_gap_pow_tail (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (n J : ℕ) :
    Summable fun j : ℕ =>
      (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) := by
  have h := (summable_gap_pow F hb (n + J)).div_const ((b : ℝ) ^ J)
  have hfun :
      (fun j : ℕ =>
          (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1)) =
        fun j : ℕ =>
          (gap (enum F) (n + J + j) : ℝ) / (b : ℝ) ^ (j + 1) / (b : ℝ) ^ J := by
    funext j
    have hadd : n + (j + J) = n + J + j := by
      rw [add_comm j J, add_assoc]
    have hpow : (b : ℝ) ^ (j + J + 1) = (b : ℝ) ^ (j + 1) * (b : ℝ) ^ J := by
      have : j + J + 1 = j + 1 + J := by ring
      rw [this, pow_add]
    rw [hadd, hpow, div_div]
  rw [hfun]
  exact h

theorem canonicalGapTail_sub_trunc (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (J n : ℕ) :
    canonicalGapTail F b n - canonicalGapTailTrunc F b J n =
      ∑' j, (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) := by
  have hs := summable_gap_pow F hb n
  have hsplit := hs.sum_add_tsum_nat_add J
  have : canonicalGapTailTrunc F b J n +
        ∑' j, (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) =
      canonicalGapTail F b n := by
    simpa [canonicalGapTail, canonicalGapTailTrunc] using hsplit
  linarith

theorem tsum_inv_pow_add_succ {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    ∑' j : ℕ, (1 : ℝ) / (b : ℝ) ^ (j + J + 1) =
      (b : ℝ) ^ (-(J : ℤ)) / ((b : ℝ) - 1) := by
  have hb1 := one_lt_cast_of_two_le hb
  have hr0 : 0 ≤ (b : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hr1 : (b : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb1
  have hgeo : ∑' n : ℕ, ((b : ℝ)⁻¹) ^ n = (1 - (b : ℝ)⁻¹)⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hpow : ∀ j, (1 : ℝ) / (b : ℝ) ^ (j + J + 1) = ((b : ℝ)⁻¹) ^ (j + J + 1) :=
    fun j => by rw [one_div, inv_pow]
  rw [tsum_congr hpow]
  have hshift : ∀ j, ((b : ℝ)⁻¹) ^ (j + J + 1) =
      ((b : ℝ)⁻¹) ^ (J + 1) * ((b : ℝ)⁻¹) ^ j := by
    intro j
    have hidx : j + J + 1 = (J + 1) + j := by ring
    rw [hidx, pow_add]
  simp_rw [hshift]
  rw [tsum_mul_left, hgeo]
  have hb0 := b_cast_ne_zero hb
  have hne : (b : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hb1.ne'
  have hinv : (1 - (b : ℝ)⁻¹)⁻¹ = (b : ℝ) / ((b : ℝ) - 1) := by
    rw [inv_eq_one_div (b : ℝ), one_sub_div hb0, inv_div]
  rw [hinv]
  have hz : (b : ℝ) ^ (-(J : ℤ)) = (b : ℝ)⁻¹ ^ J := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hz, pow_succ]
  field_simp [hb0, hne]

theorem summable_cesaro_gap_bound {b : ℕ} (hb : 2 ≤ b) {C : ℝ} (J : ℕ) :
    Summable fun j : ℕ => C * (((j + J : ℕ) : ℝ) + 2) / (b : ℝ) ^ (j + J + 1) := by
  have hlin := summable_linear_geom hb (J : ℝ)
  have hscale := hlin.mul_left (C * (b : ℝ)⁻¹ ^ (J + 1))
  have hfun : (fun j : ℕ => C * (((j + J : ℕ) : ℝ) + 2) / (b : ℝ) ^ (j + J + 1)) =
      fun j : ℕ =>
        (C * (b : ℝ)⁻¹ ^ (J + 1)) * (((J : ℝ) + j + 2) * (b : ℝ)⁻¹ ^ j) := by
    funext j
    have hcast : ((j + J : ℕ) : ℝ) + 2 = (J : ℝ) + j + 2 := by
      rw [Nat.cast_add (R := ℝ) j J]
      ring
    have hpow : (b : ℝ) ^ (j + J + 1) = (b : ℝ) ^ j * (b : ℝ) ^ (J + 1) := by
      have : j + J + 1 = j + (J + 1) := by ring
      rw [this, pow_add]
    rw [hcast, hpow, div_eq_mul_inv, mul_inv, inv_pow, inv_pow]
    ring
  rw [hfun]
  exact hscale

theorem tendsto_cesaro_gap_div_pow (F : AdmissibleFamily) {b : ℕ} (_hb : 2 ≤ b)
    (J j : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) / N /
        (b : ℝ) ^ (j + J + 1))
      atTop (𝓝 ((rho F)⁻¹ / (b : ℝ) ^ (j + J + 1))) :=
  (tendsto_cesaro_gap F (j + J)).div_const _

theorem cesaro_remainder_eq_tsum (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (J N : ℕ) :
    (∑ n ∈ range N,
        (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N =
      ∑' j, (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) / N /
        (b : ℝ) ^ (j + J + 1) := by
  have hf : ∀ n ∈ range N, Summable fun j : ℕ =>
      (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) :=
    fun n _ => summable_gap_pow_tail F hb n J
  have hinter := Summable.tsum_finsetSum hf
  have hrem : ∀ n,
      canonicalGapTail F b n - canonicalGapTailTrunc F b J n =
        ∑' j, (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) :=
    fun n => canonicalGapTail_sub_trunc F hb J n
  have hsum :
      ∑ n ∈ range N,
          (canonicalGapTail F b n - canonicalGapTailTrunc F b J n) =
        ∑' j, ∑ n ∈ range N,
          (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) := by
    simp_rw [hrem]
    exact hinter.symm
  rw [hsum]
  have hswap :
      (∑' j, ∑ n ∈ range N,
          (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1)) / N =
        ∑' j, (∑ n ∈ range N,
          (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1)) / N :=
    (tsum_div_const
        (f := fun j : ℕ =>
          ∑ n ∈ range N,
            (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1))
        (a := (N : ℝ)) (L := SummationFilter.unconditional ℕ)).symm
  rw [hswap]
  refine tsum_congr fun j => ?_
  have hs :
      ∑ n ∈ range N,
          (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) =
        (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) /
          (b : ℝ) ^ (j + J + 1) :=
    (sum_div (range N) (fun n => (gap (enum F) (n + (j + J)) : ℝ))
      ((b : ℝ) ^ (j + J + 1))).symm
  rw [hs]
  exact div_right_comm
    (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ))
    ((b : ℝ) ^ (j + J + 1)) (N : ℝ)

/-- Canonical Cesaro of the remaining geometric gap tail. Paper (23).

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (23);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem canonical_mean_tail (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b) (J : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
          (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N)
      atTop (𝓝 ((b : ℝ) ^ (-(J : ℤ)) / (rho F * ((b : ℝ) - 1)))) := by
  obtain ⟨C, hC0, hC⟩ := exists_enum_linear_bound_nonneg F
  have hterm : ∀ j : ℕ, Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) / N /
        (b : ℝ) ^ (j + J + 1))
      atTop (𝓝 ((rho F)⁻¹ / (b : ℝ) ^ (j + J + 1))) :=
    fun j => tendsto_cesaro_gap_div_pow F hb J j
  have hbound : Summable fun j : ℕ =>
      C * (((j + J : ℕ) : ℝ) + 2) / (b : ℝ) ^ (j + J + 1) :=
    summable_cesaro_gap_bound hb J
  have hdom : ∀ N j,
      ‖(∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) / N /
          (b : ℝ) ^ (j + J + 1)‖ ≤
        C * (((j + J : ℕ) : ℝ) + 2) / (b : ℝ) ^ (j + J + 1) := by
    intro N j
    have hidx := cesaro_gap_le_of_linear F hC hC0 (j + J) N
    have hnn : 0 ≤ (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) / N := by
      refine div_nonneg ?_ (Nat.cast_nonneg _)
      exact sum_nonneg fun n _ => Nat.cast_nonneg _
    have hpow0 : 0 ≤ (b : ℝ) ^ (j + J + 1) := pow_nonneg (Nat.cast_nonneg _) _
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
      abs_of_nonneg hpow0]
    exact div_le_div_of_nonneg_right hidx hpow0
  have ht :=
    tendsto_tsum_of_dominated_convergence hbound hterm
      (Eventually.of_forall hdom)
  have hlim :
      ∑' j, (rho F)⁻¹ / (b : ℝ) ^ (j + J + 1) =
        (b : ℝ) ^ (-(J : ℤ)) / (rho F * ((b : ℝ) - 1)) := by
    have hρ0 : rho F ≠ 0 := (rho_pos F).ne'
    have hb1 := one_lt_cast_of_two_le hb
    have hne : (b : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hb1.ne'
    calc
      ∑' j, (rho F)⁻¹ / (b : ℝ) ^ (j + J + 1)
          = ∑' j, (rho F)⁻¹ * ((1 : ℝ) / (b : ℝ) ^ (j + J + 1)) :=
        tsum_congr fun j => div_eq_mul_one_div _ _
      _ = (rho F)⁻¹ * ∑' j, (1 : ℝ) / (b : ℝ) ^ (j + J + 1) :=
        tsum_mul_left (L := SummationFilter.unconditional ℕ)
      _ = (rho F)⁻¹ * ((b : ℝ) ^ (-(J : ℤ)) / ((b : ℝ) - 1)) := by
        rw [tsum_inv_pow_add_succ hb J]
      _ = (b : ℝ) ^ (-(J : ℤ)) / (rho F * ((b : ℝ) - 1)) := by
        field_simp [hρ0, hne]
  have hfun :
      (fun N : ℕ =>
          (∑ n ∈ range N,
              (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N) =
        fun N : ℕ =>
          ∑' j, (∑ n ∈ range N, (gap (enum F) (n + (j + J)) : ℝ)) / N /
            (b : ℝ) ^ (j + J + 1) :=
    funext fun N => cesaro_remainder_eq_tsum F hb J N
  have ht' : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N,
          (canonicalGapTail F b n - canonicalGapTailTrunc F b J n)) / N)
      atTop (𝓝 (∑' j, (rho F)⁻¹ / (b : ℝ) ^ (j + J + 1))) := by
    rw [hfun]
    exact ht
  rw [← hlim]
  exact ht'

/-! ### Paper (4.2): canonical recurrence, no coprimeness -/

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.2);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem canonicalGapTail_zero (F : AdmissibleFamily) {b : ℕ} (_hb : 2 ≤ b) :
    canonicalGapTail F b 0 = gapSeries F b := by
  unfold canonicalGapTail gapSeries
  refine tsum_congr fun j => ?_
  rw [zero_add]

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.2);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem canonicalGapTail_recurrence (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    (n : ℕ) :
    canonicalGapTail F b (n + 1) =
      (b : ℝ) * canonicalGapTail F b n - (gap (enum F) n : ℝ) := by
  have hb0 := b_cast_ne_zero hb
  have hs := summable_gap_pow F hb n
  have hs' : Summable fun j : ℕ =>
      (gap (enum F) (n + j) : ℝ) / (b : ℝ) ^ j := by
    have hmul := hs.mul_left (b : ℝ)
    refine hmul.congr fun j => ?_
    have hpow : (b : ℝ) ^ (j + 1) = (b : ℝ) * (b : ℝ) ^ j := pow_succ' _ _
    rw [hpow, ← mul_div_assoc, mul_div_mul_left _ _ hb0]
  have hT : (b : ℝ) * canonicalGapTail F b n =
      ∑' j, (gap (enum F) (n + j) : ℝ) / (b : ℝ) ^ j := by
    unfold canonicalGapTail
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    have hpow : (b : ℝ) ^ (j + 1) = (b : ℝ) * (b : ℝ) ^ j := pow_succ' _ _
    rw [hpow, ← mul_div_assoc, mul_div_mul_left _ _ hb0]
  have hsplit := hs'.sum_add_tsum_nat_add 1
  have htail :
      ∑' j, (gap (enum F) (n + (j + 1)) : ℝ) / (b : ℝ) ^ (j + 1) =
        canonicalGapTail F b (n + 1) := by
    unfold canonicalGapTail
    refine tsum_congr fun j => ?_
    have hadd : n + (j + 1) = n + 1 + j := by
      simp [add_comm, add_left_comm, add_assoc]
    rw [hadd]
  have h0 : (gap (enum F) (n + 0) : ℝ) / (b : ℝ) ^ 0 = (gap (enum F) n : ℝ) := by
    simp
  have : (b : ℝ) * canonicalGapTail F b n =
      (gap (enum F) n : ℝ) + canonicalGapTail F b (n + 1) := by
    rw [hT, ← hsplit, htail]
    simp [sum_range_one, h0]
  linarith

/-- Source: `rounds/round92/01_gpt_positive_integer_carry.md` (4.2);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN

Index: no `Nat.Coprime Q b`. -/
theorem mul_canonicalGapTail_int (F : AdmissibleFamily) {b : ℕ} (hb : 2 ≤ b)
    {Q : ℕ} (hβ : ∃ z : ℤ, (Q : ℝ) * gapSeries F b = z) (n : ℕ) :
    ∃ z : ℤ, (Q : ℝ) * canonicalGapTail F b n = z := by
  obtain ⟨z0, hz0⟩ := hβ
  induction n with
  | zero =>
    refine ⟨z0, ?_⟩
    rwa [canonicalGapTail_zero F hb]
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨(b : ℤ) * z - (Q : ℤ) * (gap (enum F) n : ℤ), ?_⟩
    rw [canonicalGapTail_recurrence F hb n, mul_sub, mul_left_comm (Q : ℝ) (b : ℝ)]
    simp [hz]

theorem canonicalGapTailTrunc_le_canonicalGapTail (F : AdmissibleFamily)
    {b : ℕ} (hb : 2 ≤ b) (J n : ℕ) :
    canonicalGapTailTrunc F b J n ≤ canonicalGapTail F b n := by
  have h := canonicalGapTail_sub_trunc F hb J n
  have hnn : 0 ≤
      ∑' j, (gap (enum F) (n + (j + J)) : ℝ) / (b : ℝ) ^ (j + J + 1) :=
    tsum_nonneg fun _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  linarith

/-! ### Residue embedding of physical integers (paper after (21)) -/

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §6;
`rounds/round92/01_gpt_positive_integer_carry.md` §4.
Contract: C4
Audit: GREEN -/
def residuePoint (F : AdmissibleFamily) (n : ℕ) : ResidueSpace F :=
  fun i => n

theorem enum_ge_add_one (F : AdmissibleFamily) (n : ℕ) : n + 1 ≤ enum F n := by
  induction n with
  | zero =>
    simp [enum_zero]
  | succ n ih =>
    have hlt : enum F n < enum F (n + 1) :=
      enum_strictMono F (Nat.lt_succ_self n)
    exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hlt)

theorem exists_bfree_gt (F : AdmissibleFamily) (n : ℕ) :
    ∃ m, n < m ∧ BFree F m :=
  ⟨enum F n, Nat.lt_of_succ_le (enum_ge_add_one F n), enum_mem F n⟩

noncomputable def nextBFree (F : AdmissibleFamily) (n : ℕ) : ℕ :=
  Nat.find (exists_bfree_gt F n)

theorem nextBFree_gt (F : AdmissibleFamily) (n : ℕ) : n < nextBFree F n :=
  (Nat.find_spec (exists_bfree_gt F n)).1

theorem nextBFree_mem (F : AdmissibleFamily) (n : ℕ) : BFree F (nextBFree F n) :=
  (Nat.find_spec (exists_bfree_gt F n)).2

theorem nextBFree_min (F : AdmissibleFamily) {n m : ℕ} (hnm : n < m)
    (hm : BFree F m) : nextBFree F n ≤ m :=
  Nat.find_min' (exists_bfree_gt F n) ⟨hnm, hm⟩

theorem nextBFree_enum (F : AdmissibleFamily) (k : ℕ) :
    nextBFree F (enum F k) = enum F (k + 1) := by
  apply le_antisymm
  · exact nextBFree_min F (enum_strictMono F (Nat.lt_succ_self k)) (enum_mem F (k + 1))
  · have ⟨j, hj⟩ : ∃ j, enum F j = nextBFree F (enum F k) := by
      have hmem : nextBFree F (enum F k) ∈ Set.range (enum F) := by
        rw [range_enum]
        exact Set.mem_ofPred.mpr (nextBFree_mem F (enum F k))
      exact hmem
    have hlt : enum F k < enum F j := by
      rw [hj]
      exact nextBFree_gt F (enum F k)
    have hkj : k < j := (enum_strictMono F).lt_iff_lt.mp hlt
    have hle : k + 1 ≤ j := Nat.succ_le_of_lt hkj
    have : enum F (k + 1) ≤ enum F j := (enum_strictMono F).monotone hle
    rwa [hj] at this

theorem nextBFree_iterate_enum (F : AdmissibleFamily) (j k : ℕ) :
    (nextBFree F)^[j] (enum F k) = enum F (k + j) := by
  induction j with
  | zero =>
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, nextBFree_enum]
    simp [Nat.succ_eq_add_one, add_assoc]

theorem shift_residuePoint (F : AdmissibleFamily) (n t : ℕ) :
    (shift F)^[t] (residuePoint F n) = residuePoint F (n + t) := by
  induction t with
  | zero =>
    simp [residuePoint]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    funext i
    simp [shift, residuePoint, Nat.cast_add, Nat.cast_succ, add_assoc]

theorem mem_survival_residuePoint (F : AdmissibleFamily) {n : ℕ} :
    residuePoint F n ∈ survival F ↔ BFree F n := by
  constructor
  · intro h
    have hn0 : n ≠ 0 := by
      intro hn
      subst hn
      exact (h 0) (by simp [residuePoint])
    refine ⟨Nat.pos_of_ne_zero hn0, fun i hdiv => ?_⟩
    exact h i ((ZMod.natCast_eq_zero_iff n (F.d i)).mpr hdiv)
  · intro hn i hi
    exact hn.2 i ((ZMod.natCast_eq_zero_iff n (F.d i)).mp hi)

theorem exists_return_residuePoint (F : AdmissibleFamily) (n : ℕ) :
    {t : ℕ | 0 < t ∧ (shift F)^[t] (residuePoint F n) ∈ survival F}.Nonempty := by
  obtain ⟨m, hnm, hm⟩ := exists_bfree_gt F n
  refine ⟨m - n, Nat.sub_pos_of_lt hnm, ?_⟩
  have hm' : n + (m - n) = m := Nat.add_sub_of_le (Nat.le_of_lt hnm)
  rw [shift_residuePoint, hm', mem_survival_residuePoint]
  exact hm

theorem returnTime_residuePoint (F : AdmissibleFamily) (n : ℕ) :
    returnTime F (residuePoint F n) = nextBFree F n - n := by
  have hne := exists_return_residuePoint F n
  have hspec := returnTime_spec (F := F) hne
  apply le_antisymm
  · have ht : 0 < nextBFree F n - n := Nat.sub_pos_of_lt (nextBFree_gt F n)
    have hmem : (shift F)^[nextBFree F n - n] (residuePoint F n) ∈ survival F := by
      have hadd : n + (nextBFree F n - n) = nextBFree F n :=
        Nat.add_sub_of_le (Nat.le_of_lt (nextBFree_gt F n))
      rw [shift_residuePoint, hadd, mem_survival_residuePoint]
      exact nextBFree_mem F n
    have hdef : returnTime F (residuePoint F n) =
        sInf {t : ℕ | 0 < t ∧ (shift F)^[t] (residuePoint F n) ∈ survival F} :=
      dif_pos hne
    rw [hdef]
    exact Nat.sInf_le ⟨ht, hmem⟩
  · have hB : BFree F (n + returnTime F (residuePoint F n)) := by
      have : n + returnTime F (residuePoint F n) =
          n + returnTime F (residuePoint F n) := rfl
      have hsh := hspec.1
      rw [shift_residuePoint, mem_survival_residuePoint] at hsh
      exact hsh
    have hlt : n < n + returnTime F (residuePoint F n) :=
      Nat.lt_add_of_pos_right (returnTime_pos F (residuePoint F n))
    have hle := nextBFree_min F hlt hB
    exact Nat.sub_le_iff_le_add.mpr (hle.trans_eq (add_comm _ _))

theorem inducedShift_residuePoint (F : AdmissibleFamily) (n : ℕ) :
    inducedShift F (residuePoint F n) = residuePoint F (nextBFree F n) := by
  unfold inducedShift
  have hadd : n + (nextBFree F n - n) = nextBFree F n :=
    Nat.add_sub_of_le (Nat.le_of_lt (nextBFree_gt F n))
  rw [returnTime_residuePoint, shift_residuePoint, hadd]

theorem inducedShift_iterate_residuePoint (F : AdmissibleFamily) (j n : ℕ) :
    (inducedShift F)^[j] (residuePoint F n) =
      residuePoint F ((nextBFree F)^[j] n) := by
  induction j with
  | zero =>
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (inducedShift F), ih,
      inducedShift_residuePoint]
    rw [← Function.iterate_succ_apply' (nextBFree F)]

/-- Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` after (21);
`lean/BFREE_IRRATIONALITY.md` §4.4.
Contract: C4
Audit: GREEN -/
theorem canonicalGapTailTrunc_eq_returnTime (F : AdmissibleFamily)
    {b : ℕ} (_hb : 2 ≤ b) (J k : ℕ) :
    canonicalGapTailTrunc F b J k =
      ∑ j ∈ range J,
        (returnTime F
            ((inducedShift F)^[j] (residuePoint F (enum F k))) : ℝ) /
          (b : ℝ) ^ (j + 1) := by
  refine sum_congr rfl fun j hj => ?_
  have hret :
      returnTime F ((inducedShift F)^[j] (residuePoint F (enum F k))) =
        gap (enum F) (k + j) := by
    rw [inducedShift_iterate_residuePoint, returnTime_residuePoint,
      nextBFree_iterate_enum, nextBFree_enum]
    simp [gap]
  rw [hret]

/-! ### J-gap Palm: bounded Lipschitz tests of truncated tails. -/

section PalmTransfer

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private theorem measurable_inducedShift_palm (F : AdmissibleFamily) :
    Measurable (inducedShift F) := by
  intro s hs
  have hpre : inducedShift F ⁻¹' s =
      ⋃ n : ℕ, {ω | returnTime F ω = n} ∩ (shift F)^[n] ⁻¹' s := by
    ext ω
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨returnTime F ω, ⟨rfl, h⟩⟩
    · intro h
      obtain ⟨n, ⟨hn, hmem⟩⟩ := Set.mem_iUnion.mp h
      change (shift F)^[returnTime F ω] ω ∈ s
      rw [hn]
      exact hmem
  rw [hpre]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_returnTime_eq (F := F) n).inter
      (((shift_measurePreserving F).iterate n).measurable hs)

noncomputable def modelTrunc (F : AdmissibleFamily) (b J : ℕ)
    (ω : ResidueSpace F) : ℝ :=
  ∑ j ∈ range J,
    (returnTime F ((inducedShift F)^[j] ω) : ℝ) / (b : ℝ) ^ (j + 1)

noncomputable def modelSpan (F : AdmissibleFamily) (J : ℕ)
    (ω : ResidueSpace F) : ℕ :=
  ∑ j ∈ range J, returnTime F ((inducedShift F)^[j] ω)

theorem measurable_modelTrunc (F : AdmissibleFamily) (b J : ℕ) :
    Measurable (modelTrunc F b J) := by
  refine Finset.measurable_sum (range J) fun j _ => ?_
  have hret :
      Measurable fun ω : ResidueSpace F =>
        (returnTime F ((inducedShift F)^[j] ω) : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      ((returnTime_measurable (F := F)).comp
        ((measurable_inducedShift_palm F).iterate j))
  exact hret.div_const _

theorem measurable_modelSpan (F : AdmissibleFamily) (J : ℕ) :
    Measurable (modelSpan F J) :=
  Finset.measurable_sum (range J) fun j _ =>
    (returnTime_measurable (F := F)).comp
      ((measurable_inducedShift_palm F).iterate j)

theorem canonicalGapTailTrunc_eq_modelTrunc (F : AdmissibleFamily)
    {b : ℕ} (hb : 2 ≤ b) (J k : ℕ) :
    canonicalGapTailTrunc F b J k =
      modelTrunc F b J (residuePoint F (enum F k)) :=
  canonicalGapTailTrunc_eq_returnTime F hb J k

noncomputable def truncTestWindow (F : AdmissibleFamily) (b J H : ℕ)
    (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if BFree F n then
    if (nextBFree F)^[J] n ≤ n + H then
      f (∑ j ∈ range J,
          (((nextBFree F)^[j + 1] n - (nextBFree F)^[j] n : ℝ) /
            (b : ℝ) ^ (j + 1)))
    else 0
  else 0

noncomputable def truncTestWindowModel (F : AdmissibleFamily) (b J H : ℕ)
    (f : ℝ → ℝ) (ω : ResidueSpace F) : ℝ :=
  if ω ∈ survival F then
    if modelSpan F J ω ≤ H then f (modelTrunc F b J ω) else 0
  else 0

theorem nextBFree_diff_returnTime (F : AdmissibleFamily) (j n : ℕ) :
    (nextBFree F)^[j + 1] n - (nextBFree F)^[j] n =
      returnTime F ((inducedShift F)^[j] (residuePoint F n)) := by
  have h1 : (nextBFree F)^[j + 1] n = nextBFree F ((nextBFree F)^[j] n) :=
    Function.iterate_succ_apply' (nextBFree F) j n
  rw [h1, inducedShift_iterate_residuePoint, returnTime_residuePoint]

theorem nextBFree_iterate_ge (F : AdmissibleFamily) (J n : ℕ) :
    n ≤ (nextBFree F)^[J] n := by
  induction J with
  | zero => simp
  | succ J ih =>
    exact ih.trans (Nat.le_of_lt (by
      simpa [Function.iterate_succ_apply'] using
        nextBFree_gt F ((nextBFree F)^[J] n)))

theorem nextBFree_iterate_sub (F : AdmissibleFamily) (J n : ℕ) :
    (nextBFree F)^[J] n - n = modelSpan F J (residuePoint F n) := by
  induction J with
  | zero =>
    simp [modelSpan]
  | succ J ih =>
    have hpos : n ≤ (nextBFree F)^[J] n := nextBFree_iterate_ge F J n
    have hpos' : (nextBFree F)^[J] n ≤ (nextBFree F)^[J + 1] n :=
      Nat.le_of_lt (by
        simpa [Function.iterate_succ_apply'] using
          nextBFree_gt F ((nextBFree F)^[J] n))
    have htel :
        (nextBFree F)^[J + 1] n - n =
          ((nextBFree F)^[J + 1] n - (nextBFree F)^[J] n) +
            ((nextBFree F)^[J] n - n) := by
      omega
    rw [htel, nextBFree_diff_returnTime, ih]
    simp [modelSpan, sum_range_succ, add_comm]

theorem truncTestWindow_eq_model (F : AdmissibleFamily) (b J H : ℕ)
    (f : ℝ → ℝ) (n : ℕ) :
    truncTestWindow F b J H f n =
      truncTestWindowModel F b J H f (residuePoint F n) := by
  unfold truncTestWindow truncTestWindowModel
  rw [mem_survival_residuePoint]
  by_cases hB : BFree F n
  · simp only [hB, ite_true]
    have hiff :
        (nextBFree F)^[J] n ≤ n + H ↔
          modelSpan F J (residuePoint F n) ≤ H := by
      rw [← nextBFree_iterate_sub F J n]
      exact (Nat.sub_le_iff_le_add').symm
    simp only [hiff]
    by_cases hsp : modelSpan F J (residuePoint F n) ≤ H
    · simp only [hsp, ite_true]
      congr 1
      unfold modelTrunc
      refine sum_congr rfl fun j _ => ?_
      have hle : (nextBFree F)^[j] n ≤ (nextBFree F)^[j + 1] n :=
        Nat.le_of_lt (by
          simpa [Function.iterate_succ_apply'] using
            nextBFree_gt F ((nextBFree F)^[j] n))
      rw [← Nat.cast_sub hle, nextBFree_diff_returnTime]
    · simp only [hsp, ite_false]
  · simp only [hB, ite_false]

theorem truncTestWindow_enum (F : AdmissibleFamily) (b J H : ℕ)
    (f : ℝ → ℝ) (k : ℕ) :
    truncTestWindow F b J H f (enum F k) =
      (if enum F (k + J) ≤ enum F k + H then
        f (canonicalGapTailTrunc F b J k) else 0) := by
  unfold truncTestWindow
  simp only [enum_mem, ite_true]
  rw [nextBFree_iterate_enum]
  have hsum :
      ∑ j ∈ range J,
          (((nextBFree F)^[j + 1] (enum F k) -
            (nextBFree F)^[j] (enum F k) : ℝ) / (b : ℝ) ^ (j + 1)) =
        canonicalGapTailTrunc F b J k := by
    unfold canonicalGapTailTrunc
    refine sum_congr rfl fun j _ => ?_
    have hj : (nextBFree F)^[j] (enum F k) = enum F (k + j) :=
      nextBFree_iterate_enum F j k
    have hj1 : (nextBFree F)^[j + 1] (enum F k) = enum F (k + j + 1) := by
      simpa [add_assoc] using nextBFree_iterate_enum F (j + 1) k
    have hle : enum F (k + j) ≤ enum F (k + j + 1) :=
      (enum_strictMono F).monotone (Nat.le_succ _)
    rw [hj, hj1, ← Nat.cast_sub hle]
    simp [gap]
  have hfun :
      ∑ j ∈ range J,
          (((nextBFree F)^[j] (nextBFree F (enum F k)) -
            (nextBFree F)^[j] (enum F k) : ℝ) / (b : ℝ) ^ (j + 1)) =
        canonicalGapTailTrunc F b J k := by
    refine Eq.trans ?_ hsum
    refine sum_congr rfl fun j _ => ?_
    have hiter : (nextBFree F)^[j] (nextBFree F (enum F k)) =
        (nextBFree F)^[j + 1] (enum F k) :=
      (Function.iterate_succ_apply (nextBFree F) j (enum F k)).symm
    rw [hiter]
  simp [hfun]

theorem abs_truncTestWindow_le {M : ℝ} (F : AdmissibleFamily) (b J H : ℕ)
    {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) (n : ℕ) :
    |truncTestWindow F b J H f n| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  unfold truncTestWindow
  split_ifs
  · exact hbdd _
  · rwa [abs_zero]
  · rwa [abs_zero]

theorem abs_truncTestWindowModel_le {M : ℝ} (F : AdmissibleFamily) (b J H : ℕ)
    {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) (ω : ResidueSpace F) :
    |truncTestWindowModel F b J H f ω| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  unfold truncTestWindowModel
  split_ifs
  · exact hbdd _
  · rwa [abs_zero]
  · rwa [abs_zero]

theorem measurable_truncTestWindowModel (F : AdmissibleFamily) (b J H : ℕ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (truncTestWindowModel F b J H f) := by
  have hA := survival_measurable F
  have hspan : MeasurableSet {ω : ResidueSpace F | modelSpan F J ω ≤ H} :=
    (measurable_modelSpan F J)
      (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic H))
  have hfun : Measurable fun ω => f (modelTrunc F b J ω) :=
    hf.measurable.comp (measurable_modelTrunc F b J)
  exact Measurable.ite hA (Measurable.ite hspan hfun measurable_const) measurable_const

theorem integrable_truncTestWindowModel {M : ℝ} (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Integrable (truncTestWindowModel F b J H f) (productMeasure F) := by
  refine (integrable_const M).mono' ?_ ?_
  · exact (measurable_truncTestWindowModel F b J H hf).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    exact abs_truncTestWindowModel_le F b J H hbdd ω

/-- Physical mismatch on a window of length `H+1`. Paper (18).

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (18).
Contract: C4
Audit: GREEN -/
theorem mismatch_window_card (F : AdmissibleFamily) (k X H : ℕ) :
    (#{n ∈ Icc 1 X |
        ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)} : ℝ) ≤
      (H + 1 : ℝ) * (X + H : ℝ) *
        ∑' i, (1 : ℝ) / F.d (i + k) := by
  have hsub :
      (Icc 1 X).filter
          (fun n => ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)) ⊆
        (Icc 1 X).filter
          (fun n => ∃ j ≤ H, ∃ i, k ≤ i ∧ F.d i ∣ n + j) := by
    intro n hn
    obtain ⟨hI, ⟨j, hj, hres, hnot⟩⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hI, ⟨j, hj, ?_⟩⟩
    obtain ⟨h1, _⟩ := mem_Icc.mp hI
    have hn1 : 1 ≤ n + j := le_trans h1 (Nat.le_add_right n j)
    have : ∃ i, F.d i ∣ n + j := by
      by_contra hnone
      exact hnot ⟨lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn1,
        fun i hdiv => hnone ⟨i, hdiv⟩⟩
    obtain ⟨i, hdiv⟩ := this
    have hik : k ≤ i := by
      by_contra hki
      exact hres i (Nat.not_le.mp hki) hdiv
    exact ⟨i, hik, hdiv⟩
  have hle_card := card_le_card hsub
  let s := Icc 0 H
  have hsj : ∀ n, (∃ j ≤ H, ∃ i, k ≤ i ∧ F.d i ∣ n + j) →
      ∃ j ∈ s, ∃ i, k ≤ i ∧ F.d i ∣ n + j := by
    intro n ⟨j, hj, hi⟩
    exact ⟨j, mem_Icc.mpr ⟨Nat.zero_le j, hj⟩, hi⟩
  have hbi :
      #{n ∈ Icc 1 X | ∃ j ≤ H, ∃ i, k ≤ i ∧ F.d i ∣ n + j} ≤
        ∑ j ∈ s, #{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} := by
    have hcov :
        (Icc 1 X).filter (fun n => ∃ j ≤ H, ∃ i, k ≤ i ∧ F.d i ∣ n + j) ⊆
          s.biUnion (fun j => (Icc 1 X).filter
            (fun n => ∃ i, k ≤ i ∧ F.d i ∣ n + j)) := by
      intro n hn
      obtain ⟨hI, ⟨j, hj, hi⟩⟩ := mem_filter.mp hn
      exact mem_biUnion.mpr ⟨j, mem_Icc.mpr ⟨Nat.zero_le j, hj⟩,
        mem_filter.mpr ⟨hI, hi⟩⟩
    exact (card_le_card hcov).trans card_biUnion_le
  have hterm : ∀ j ∈ s,
      (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} : ℝ) ≤
        (X + H : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
    intro j hj
    have hjH : j ≤ H := (mem_Icc.mp hj).2
    have hinj : Set.InjOn (fun n : ℕ => n + j)
        ((Icc 1 X).filter (fun n => ∃ i, k ≤ i ∧ F.d i ∣ n + j) : Set ℕ) :=
      fun a _ b _ h => Nat.add_right_cancel h
    have himg :
        ((Icc 1 X).filter (fun n => ∃ i, k ≤ i ∧ F.d i ∣ n + j)).image
            (fun n => n + j) ⊆
          (Icc 1 (X + H)).filter (fun m => ∃ i, k ≤ i ∧ F.d i ∣ m) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      obtain ⟨hI, hi⟩ := mem_filter.mp hn
      obtain ⟨h1, hX⟩ := mem_Icc.mp hI
      exact mem_filter.mpr
        ⟨mem_Icc.mpr ⟨le_trans h1 (Nat.le_add_right n j), add_le_add hX hjH⟩, hi⟩
    have hcard_img := card_le_card himg
    have hcard_eq :
        #(((Icc 1 X).filter (fun n => ∃ i, k ≤ i ∧ F.d i ∣ n + j)).image
            (fun n => n + j)) =
          #{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} :=
      card_image_of_injOn hinj
    have htail := card_exists_dvd_tail_le F k (X + H)
    have : (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} : ℝ) ≤
        (#{m ∈ Icc 1 (X + H) | ∃ i, k ≤ i ∧ F.d i ∣ m} : ℝ) := by
      exact Nat.cast_le.mpr (by rwa [← hcard_eq])
    exact this.trans (by simpa [Nat.cast_add] using htail)
  have hsum : ∑ j ∈ s, (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} : ℝ) ≤
      ∑ j ∈ s, (X + H : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) :=
    sum_le_sum hterm
  have hsC : (s.card : ℝ) = (H + 1 : ℝ) := by
    simp [s, Nat.card_Icc]
  have hconst :
      ∑ j ∈ s, (X + H : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) =
        (H + 1 : ℝ) * (X + H : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
    rw [sum_const, nsmul_eq_mul, hsC]
    ring
  have hnat :
      (#{n ∈ Icc 1 X |
          ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)} : ℝ) ≤
        ∑ j ∈ s, (#{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} : ℝ) := by
    have h : (#{n ∈ Icc 1 X |
          ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)} : ℝ) ≤
        (∑ j ∈ s, #{n ∈ Icc 1 X | ∃ i, k ≤ i ∧ F.d i ∣ n + j} : ℝ) := by
      rw [← Nat.cast_sum]
      exact Nat.cast_le.mpr (hle_card.trans hbi)
    exact h
  exact hnat.trans (hsum.trans_eq hconst)

theorem sum_Icc_periodic_blocks (g : ℕ → ℝ) {P : ℕ} (hP : 0 < P)
    (hg : ∀ n, g (n + P) = g n) (q : ℕ) :
    ∑ n ∈ Icc 1 (q * P), g n = (q : ℝ) * ∑ n ∈ Icc 1 P, g n := by
  have hgq : ∀ t n, g (n + t * P) = g n := by
    intro t
    induction t with
    | zero => intro n; simp
    | succ t ih =>
      intro n
      rw [Nat.succ_mul, ← add_assoc, hg, ih]
  induction q with
  | zero => simp
  | succ q ih =>
    have hun : Icc 1 ((q + 1) * P) =
        Icc 1 (q * P) ∪ Icc (q * P + 1) ((q + 1) * P) := by
      ext n
      simp only [mem_union, mem_Icc]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hq : n ≤ q * P
        · exact Or.inl ⟨h1, hq⟩
        · exact Or.inr ⟨Nat.succ_le_of_lt (Nat.not_le.mp hq), h2⟩
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2.trans (Nat.mul_le_mul_right P (Nat.le_succ q))⟩
        · exact ⟨le_trans (Nat.succ_le_succ (Nat.zero_le _)) h1, h2⟩
    have hdisj :
        Disjoint (Icc 1 (q * P)) (Icc (q * P + 1) ((q + 1) * P)) :=
      disjoint_left.mpr fun n hn hn' => by
        simp only [mem_Icc] at hn hn'
        exact Nat.not_succ_le_self (q * P) (hn'.1.trans hn.2)
    rw [hun, sum_union hdisj, ih]
    have himg :
        (Icc 1 P).image (fun n => n + q * P) =
          Icc (q * P + 1) ((q + 1) * P) := by
      ext m
      constructor
      · intro hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        obtain ⟨hn1, hnP⟩ := mem_Icc.mp hn
        refine mem_Icc.mpr ⟨?_, ?_⟩
        · simpa [add_comm] using Nat.add_le_add_right hn1 (q * P)
        · have : n + q * P ≤ P + q * P := Nat.add_le_add_right hnP (q * P)
          simpa [Nat.succ_mul, add_comm, add_left_comm] using this
      · intro hm
        obtain ⟨hle, hge⟩ := mem_Icc.mp hm
        have hqm : q * P ≤ m := Nat.le_of_succ_le hle
        refine mem_image.mpr ⟨m - q * P, mem_Icc.mpr ⟨?_, ?_⟩,
          Nat.sub_add_cancel hqm⟩
        · exact (Nat.le_sub_iff_add_le hqm).mpr (by simpa [add_comm] using hle)
        · have hge' : m ≤ q * P + P := by
            have hmul : (q + 1) * P = q * P + P := Nat.succ_mul q P
            rwa [hmul] at hge
          exact Nat.sub_le_iff_le_add'.mpr hge'
    have hsum :
        ∑ n ∈ Icc (q * P + 1) ((q + 1) * P), g n =
          ∑ n ∈ Icc 1 P, g n := by
      rw [← himg, sum_image]
      · refine Finset.sum_congr rfl fun n hn => ?_
        simp [hgq]
      · intro a ha b hb h
        exact Nat.add_right_cancel h
    rw [hsum, Nat.cast_succ, add_mul, one_mul]

theorem tendsto_cesaro_periodic {P : ℕ} (hP : 0 < P) (g : ℕ → ℝ)
    (hg : ∀ n, g (n + P) = g n) :
    Tendsto (fun X : ℕ => (∑ n ∈ Icc 1 X, g n) / (X : ℝ)) atTop
      (𝓝 ((∑ n ∈ Icc 1 P, g n) / (P : ℝ))) := by
  set S := ∑ n ∈ Icc 1 P, g n
  have hPpos : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hgq : ∀ t n, g (n + t * P) = g n := by
    intro t
    induction t with
    | zero => intro n; simp
    | succ t ih =>
      intro n
      rw [Nat.succ_mul, ← add_assoc, hg, ih]
  have hsumX : ∀ X, ∑ n ∈ Icc 1 X, g n =
      ((X / P : ℕ) : ℝ) * S + ∑ n ∈ Icc 1 (X % P), g n := by
    intro X
    have hdecomp : X = (X / P) * P + X % P := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod X P).symm
    have hun : Icc 1 X =
        Icc 1 ((X / P) * P) ∪ Icc ((X / P) * P + 1) X := by
      ext n
      simp only [mem_union, mem_Icc]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hq : n ≤ (X / P) * P
        · exact Or.inl ⟨h1, hq⟩
        · exact Or.inr ⟨Nat.succ_le_of_lt (Nat.not_le.mp hq), h2⟩
      · intro h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2.trans (by omega)⟩
        · refine ⟨le_trans (Nat.succ_le_succ (Nat.zero_le _)) h1, h2⟩
    have hdisj :
        Disjoint (Icc 1 ((X / P) * P))
          (Icc ((X / P) * P + 1) X) :=
      disjoint_left.mpr fun n hn hn' => by
        simp only [mem_Icc] at hn hn'
        exact Nat.not_succ_le_self ((X / P) * P) (hn'.1.trans hn.2)
    rw [hun, sum_union hdisj, sum_Icc_periodic_blocks g hP hg]
    have hrest :
        ∑ n ∈ Icc ((X / P) * P + 1) X, g n =
          ∑ n ∈ Icc 1 (X % P), g n := by
      by_cases hr : X % P = 0
      · have hX : (X / P) * P = X := by
          have := Nat.div_add_mod X P
          rw [hr, add_zero] at this
          simpa [Nat.mul_comm] using this
        simp [hX, hr]
      · have himg :
            (Icc 1 (X % P)).image (fun n => n + (X / P) * P) =
              Icc ((X / P) * P + 1) X := by
          ext m
          constructor
          · intro hm
            obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
            obtain ⟨hn1, hnP⟩ := mem_Icc.mp hn
            refine mem_Icc.mpr ⟨?_, ?_⟩
            · simpa [add_comm] using
                Nat.add_le_add_right hn1 ((X / P) * P)
            · have hle' : n + (X / P) * P ≤ X % P + (X / P) * P :=
                Nat.add_le_add_right hnP ((X / P) * P)
              rw [add_comm (X % P), ← hdecomp] at hle'
              exact hle'
          · intro hm
            obtain ⟨hle, hge⟩ := mem_Icc.mp hm
            have hqm : (X / P) * P ≤ m := Nat.le_of_succ_le hle
            refine mem_image.mpr ⟨m - (X / P) * P, mem_Icc.mpr ⟨?_, ?_⟩,
              Nat.sub_add_cancel hqm⟩
            · exact (Nat.le_sub_iff_add_le hqm).mpr
                (by simpa [add_comm] using hle)
            · omega
        rw [← himg, sum_image]
        · refine Finset.sum_congr rfl fun n hn => ?_
          simp [hgq]
        · intro a ha b hb h
          exact Nat.add_right_cancel h
    rw [hrest]
  have hbound : ∀ r, r < P → |∑ n ∈ Icc 1 r, g n| ≤ ∑ n ∈ Icc 1 P, |g n| := by
    intro r hr
    have hsub : Icc 1 r ⊆ Icc 1 P := by
      intro n hn
      simp only [mem_Icc] at hn ⊢
      exact ⟨hn.1, hn.2.trans hr.le⟩
    exact (abs_sum_le_sum_abs _ _).trans
      (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCpos : 0 ≤ ∑ n ∈ Icc 1 P, |g n| := sum_nonneg fun _ _ => abs_nonneg _
  set C := ∑ n ∈ Icc 1 P, |g n|
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + |S| + 1) / ε)
  refine ⟨max N 1, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < X :=
    Nat.cast_pos.mpr (le_trans (le_max_right N 1) hX)
  have hXge : N ≤ X := le_trans (le_max_left N 1) hX
  have hXgt : (C + |S| + 1) / ε < X := hN.trans_le (Nat.cast_le.mpr hXge)
  have hsmall : (C + |S|) / (X : ℝ) < ε := by
    have hnum : C + |S| + 1 < ε * X := by
      have := (div_lt_iff₀ hε).mp hXgt
      linarith
    have hfrac : (C + |S| + 1) / (X : ℝ) < ε := (div_lt_iff₀ hXpos).mpr hnum
    exact (div_le_div_of_nonneg_right (by linarith) hXpos.le).trans_lt hfrac
  have hdiff :
      |((∑ n ∈ Icc 1 X, g n) / (X : ℝ)) - S / P| ≤
        (C + |S|) / (X : ℝ) := by
    rw [hsumX]
    set q := X / P
    set r := X % P
    have hrP : r < P := Nat.mod_lt X hP
    have hXeq : (X : ℝ) = (q : ℝ) * P + r := by
      have := congrArg (fun n : ℕ => (n : ℝ))
        (show X = q * P + r by
          rw [Nat.mul_comm]
          exact (Nat.div_add_mod X P).symm)
      simpa using this
    have hnum :
        |((q : ℝ) * S + ∑ n ∈ Icc 1 r, g n) * P - S * X| ≤
          (C + |S|) * P := by
      have : ((q : ℝ) * S + ∑ n ∈ Icc 1 r, g n) * P - S * X =
          (∑ n ∈ Icc 1 r, g n) * P - S * (r : ℝ) := by
        rw [hXeq]
        ring
      rw [this]
      have h1 : |(∑ n ∈ Icc 1 r, g n) * P| ≤ C * P := by
        rw [abs_mul, abs_of_pos hPpos]
        exact mul_le_mul_of_nonneg_right (hbound r hrP) hPpos.le
      have h2 : |S * (r : ℝ)| ≤ |S| * (P : ℝ) := by
        rw [abs_mul]
        have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
        rw [abs_of_nonneg hr0]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have : r ≤ P := hrP.le
        exact_mod_cast this
      have htri :
          |(∑ n ∈ Icc 1 r, g n) * P - S * (r : ℝ)| ≤
            |(∑ n ∈ Icc 1 r, g n) * P| + |S * (r : ℝ)| := by
        have hnorm :=
          norm_add_le ((∑ n ∈ Icc 1 r, g n) * P) (-(S * (r : ℝ)))
        simpa [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using hnorm
      exact htri.trans (add_le_add h1 h2) |>.trans_eq (by ring)
    have hden0 : 0 < (X : ℝ) * P := mul_pos hXpos hPpos
    have : |((q : ℝ) * S + ∑ n ∈ Icc 1 r, g n) / X - S / P| ≤
        ((C + |S|) * P) / (X * P) := by
      have hdenX : (X : ℝ) ≠ 0 := hXpos.ne'
      have hP0 : (P : ℝ) ≠ 0 := hPpos.ne'
      have heq :
          |((q : ℝ) * S + ∑ n ∈ Icc 1 r, g n) / X - S / P| =
            |P * ((q : ℝ) * S + ∑ n ∈ Icc 1 r, g n) - S * X| / (X * P) := by
        rw [div_sub_div _ _ hdenX hP0, abs_div]
        congr 1
        · ring_nf
        · rw [abs_mul, abs_of_pos hXpos, abs_of_pos hPpos]
      rw [heq]
      have : |P * ((q : ℝ) * S + ∑ n ∈ Icc 1 r, g n) - S * X| ≤
          (C + |S|) * P := by
        convert hnum using 2
        ring
      exact div_le_div_of_nonneg_right this hden0.le
    have hsimp : ((C + |S|) * P) / (X * P) = (C + |S|) / X := by
      field_simp [hXpos.ne', hPpos.ne']
    rwa [hsimp] at this
  have hdist : dist ((∑ n ∈ Icc 1 X, g n) / (X : ℝ)) (S / P) < ε := by
    simpa [Real.dist_eq] using hdiff.trans_lt hsmall
  exact hdist

/-- Tail of the reciprocal series. Paper (18) `τ_k → 0`. -/
theorem tendsto_tsum_tail_one_div_d (F : AdmissibleFamily) :
    Tendsto (fun k : ℕ => ∑' i, (1 : ℝ) / F.d (i + k)) atTop (𝓝 0) := by
  have hs := F.summable
  have hpart :
      Tendsto (fun k : ℕ => ∑ i ∈ range k, (1 : ℝ) / F.d i) atTop
        (𝓝 (∑' i, (1 : ℝ) / F.d i)) :=
    hs.hasSum.tendsto_sum_nat
  have htail :
      Tendsto (fun k : ℕ =>
          (∑' i, (1 : ℝ) / F.d i) - ∑ i ∈ range k, (1 : ℝ) / F.d i)
        atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub hpart
    ring
  refine htail.congr fun k => ?_
  have hsplit := hs.sum_add_tsum_nat_add k
  linarith

theorem exists_sieve_gt (F : AdmissibleFamily) (k n : ℕ) :
    ∃ m, n < m ∧ residueSieve F k m := by
  by_cases hk : k = 0
  · subst hk
    exact ⟨n + 1, Nat.lt_succ_self n, residueSieve_zero F _⟩
  · have hcard :
        0 < #{a ∈ range (partialPeriod F k) | residueSieve F k a} := by
      rw [card_residueSieve_period]
      exact prod_pos fun i _ => Nat.sub_pos_of_lt (F.two_le i)
    obtain ⟨a, ha⟩ := card_pos.mp hcard
    obtain ⟨haR, haS⟩ := mem_filter.mp ha
    refine ⟨a + (n + 1) * partialPeriod F k, ?_, ?_⟩
    · have hmul : n < (n + 1) * partialPeriod F k :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
          (Nat.le_mul_of_pos_right (n + 1) (partialPeriod_pos F k))
      exact hmul.trans_le (Nat.le_add_left _ a)
    · rwa [residueSieve_add_period]

noncomputable def nextSieve (F : AdmissibleFamily) (k n : ℕ) : ℕ :=
  Nat.find (exists_sieve_gt F k n)

theorem nextSieve_gt (F : AdmissibleFamily) (k n : ℕ) :
    n < nextSieve F k n :=
  (Nat.find_spec (exists_sieve_gt F k n)).1

theorem nextSieve_mem (F : AdmissibleFamily) (k n : ℕ) :
    residueSieve F k (nextSieve F k n) :=
  (Nat.find_spec (exists_sieve_gt F k n)).2

theorem nextSieve_min (F : AdmissibleFamily) (k : ℕ) {n m : ℕ}
    (hnm : n < m) (hm : residueSieve F k m) : nextSieve F k n ≤ m :=
  Nat.find_min' (exists_sieve_gt F k n) ⟨hnm, hm⟩

theorem nextSieve_add_period (F : AdmissibleFamily) (k n : ℕ) :
    nextSieve F k (n + partialPeriod F k) =
      nextSieve F k n + partialPeriod F k := by
  set P := partialPeriod F k
  have hP := partialPeriod_pos F k
  apply le_antisymm
  · have hm : residueSieve F k (nextSieve F k n + P) := by
      have hiff := residueSieve_add_period (F := F) (k := k)
        (a := nextSieve F k n) (t := 1)
      simpa [one_mul] using hiff.mpr (nextSieve_mem F k n)
    exact nextSieve_min F k (Nat.add_lt_add_right (nextSieve_gt F k n) P) hm
  · have hgt := nextSieve_gt F k (n + P)
    have hmem := nextSieve_mem F k (n + P)
    have hP_le : P ≤ nextSieve F k (n + P) :=
      (Nat.le_add_left P n).trans (Nat.le_of_lt hgt)
    have hshift : residueSieve F k (nextSieve F k (n + P) - P) := by
      have heq : nextSieve F k (n + P) =
          (nextSieve F k (n + P) - P) + P :=
        (Nat.sub_add_cancel hP_le).symm
      have hiff := residueSieve_add_period (F := F) (k := k)
        (a := nextSieve F k (n + P) - P) (t := 1)
      have hmem' : residueSieve F k
          ((nextSieve F k (n + P) - P) + 1 * P) := by
        rw [one_mul, ← heq]
        exact hmem
      exact hiff.mp hmem'
    have hlt' : n < nextSieve F k (n + P) - P := by omega
    have hle := nextSieve_min F k hlt' hshift
    exact (Nat.le_sub_iff_add_le hP_le).mp hle

theorem nextSieve_iterate_add_period (F : AdmissibleFamily) (k J n : ℕ) :
    (nextSieve F k)^[J] (n + partialPeriod F k) =
      (nextSieve F k)^[J] n + partialPeriod F k := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Function.iterate_succ_apply', ih, nextSieve_add_period,
      Function.iterate_succ_apply']

theorem nextSieve_iterate_ge (F : AdmissibleFamily) (k J n : ℕ) :
    n ≤ (nextSieve F k)^[J] n := by
  induction J with
  | zero => simp
  | succ J ih =>
    exact ih.trans (Nat.le_of_lt (by
      simpa [Function.iterate_succ_apply'] using
        nextSieve_gt F k ((nextSieve F k)^[J] n)))

def survivalFin (F : AdmissibleFamily) (k : ℕ) : Set (ResidueSpace F) :=
  Set.pi (range k : Set ℕ) fun i => ({0} : Set (ZMod (F.d i)))ᶜ

theorem mem_survivalFin (F : AdmissibleFamily) (k : ℕ) (ω : ResidueSpace F) :
    ω ∈ survivalFin F k ↔ ∀ i < k, ω i ≠ 0 := by
  simp [survivalFin, Set.mem_pi, mem_range]

theorem mem_survivalFin_residuePoint (F : AdmissibleFamily) (k n : ℕ) :
    residuePoint F n ∈ survivalFin F k ↔ residueSieve F k n := by
  simp [mem_survivalFin, residuePoint, residueSieve, ZMod.natCast_eq_zero_iff]

theorem exists_pos_cylinderHit (F : AdmissibleFamily) (k : ℕ)
    (ω : ResidueSpace F) :
    ∃ t : ℕ, 0 < t ∧ ∀ i < k, ω i + t ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_add_ne_zero_lt F (shift F ω) k
  refine ⟨n + 1, Nat.succ_pos n, fun i hi => ?_⟩
  have h := hn i hi
  simpa [shift_apply, Nat.cast_succ, add_comm, add_left_comm, add_assoc] using h

noncomputable def sieveReturnTime (F : AdmissibleFamily) (k : ℕ)
    (ω : ResidueSpace F) : ℕ :=
  Nat.find (exists_pos_cylinderHit F k ω)

theorem sieveReturnTime_pos (F : AdmissibleFamily) (k : ℕ)
    (ω : ResidueSpace F) : 0 < sieveReturnTime F k ω :=
  (Nat.find_spec (exists_pos_cylinderHit F k ω)).1

theorem sieveReturnTime_spec (F : AdmissibleFamily) (k : ℕ)
    (ω : ResidueSpace F) :
    (∀ i < k, ω i + sieveReturnTime F k ω ≠ 0) ∧
      ∀ t, 0 < t → t < sieveReturnTime F k ω → ¬ ∀ i < k, ω i + t ≠ 0 := by
  refine ⟨(Nat.find_spec (exists_pos_cylinderHit F k ω)).2, ?_⟩
  intro t ht hlt hall
  exact Nat.find_min (exists_pos_cylinderHit F k ω) hlt ⟨ht, hall⟩

noncomputable def inducedSieveShift (F : AdmissibleFamily) (k : ℕ) :
    ResidueSpace F → ResidueSpace F :=
  fun ω => (shift F)^[sieveReturnTime F k ω] ω

theorem sieveReturnTime_residuePoint (F : AdmissibleFamily) (k n : ℕ) :
    sieveReturnTime F k (residuePoint F n) = nextSieve F k n - n := by
  apply le_antisymm
  · have ht : 0 < nextSieve F k n - n := Nat.sub_pos_of_lt (nextSieve_gt F k n)
    have hmem : ∀ i < k,
        residuePoint F n i + (nextSieve F k n - n : ℕ) ≠ 0 := by
      intro i hi
      have hadd : n + (nextSieve F k n - n) = nextSieve F k n :=
        Nat.add_sub_of_le (Nat.le_of_lt (nextSieve_gt F k n))
      have hres : residuePoint F (nextSieve F k n) ∈ survivalFin F k :=
        (mem_survivalFin_residuePoint F k _).mpr (nextSieve_mem F k n)
      have hsh : (shift F)^[nextSieve F k n - n] (residuePoint F n) =
          residuePoint F (nextSieve F k n) := by
        rw [shift_residuePoint, hadd]
      have := (mem_survivalFin F k _).mp (hsh ▸ hres)
      simpa [shift_iterate_apply, residuePoint, hadd] using this i hi
    exact Nat.find_min' (exists_pos_cylinderHit F k (residuePoint F n))
      ⟨ht, hmem⟩
  · have hspec := Nat.find_spec (exists_pos_cylinderHit F k (residuePoint F n))
    have ht := hspec.1
    have hmem := hspec.2
    have hB : residueSieve F k (n + sieveReturnTime F k (residuePoint F n)) := by
      refine (mem_survivalFin_residuePoint F k _).mp ?_
      rw [← shift_residuePoint, mem_survivalFin]
      intro i hi
      simpa [shift_iterate_apply, residuePoint, sieveReturnTime] using hmem i hi
    have hlt : n < n + sieveReturnTime F k (residuePoint F n) :=
      Nat.lt_add_of_pos_right ht
    have hle := nextSieve_min F k hlt hB
    exact Nat.sub_le_iff_le_add.mpr (hle.trans_eq (add_comm _ _))

theorem inducedSieveShift_residuePoint (F : AdmissibleFamily) (k n : ℕ) :
    inducedSieveShift F k (residuePoint F n) =
      residuePoint F (nextSieve F k n) := by
  unfold inducedSieveShift
  have hadd : n + (nextSieve F k n - n) = nextSieve F k n :=
    Nat.add_sub_of_le (Nat.le_of_lt (nextSieve_gt F k n))
  rw [sieveReturnTime_residuePoint, shift_residuePoint, hadd]

theorem inducedSieveShift_iterate_residuePoint (F : AdmissibleFamily)
    (k j n : ℕ) :
    (inducedSieveShift F k)^[j] (residuePoint F n) =
      residuePoint F ((nextSieve F k)^[j] n) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (inducedSieveShift F k), ih,
      inducedSieveShift_residuePoint]
    rw [← Function.iterate_succ_apply' (nextSieve F k)]

noncomputable def sieveTrunc (F : AdmissibleFamily) (k b J : ℕ)
    (ω : ResidueSpace F) : ℝ :=
  ∑ j ∈ range J,
    (sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) : ℝ) /
      (b : ℝ) ^ (j + 1)

noncomputable def sieveSpan (F : AdmissibleFamily) (k J : ℕ)
    (ω : ResidueSpace F) : ℕ :=
  ∑ j ∈ range J, sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)

noncomputable def truncTestWindowSieve (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if residueSieve F k n then
    if (nextSieve F k)^[J] n ≤ n + H then
      f (∑ j ∈ range J,
          (((nextSieve F k)^[j + 1] n - (nextSieve F k)^[j] n : ℝ) /
            (b : ℝ) ^ (j + 1)))
    else 0
  else 0

noncomputable def truncTestWindowSieveModel (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) (ω : ResidueSpace F) : ℝ :=
  if ω ∈ survivalFin F k then
    if sieveSpan F k J ω ≤ H then f (sieveTrunc F k b J ω) else 0
  else 0

theorem nextSieve_diff_sieveReturn (F : AdmissibleFamily) (k j n : ℕ) :
    (nextSieve F k)^[j + 1] n - (nextSieve F k)^[j] n =
      sieveReturnTime F k
        ((inducedSieveShift F k)^[j] (residuePoint F n)) := by
  have h1 : (nextSieve F k)^[j + 1] n =
      nextSieve F k ((nextSieve F k)^[j] n) :=
    Function.iterate_succ_apply' (nextSieve F k) j n
  rw [h1, inducedSieveShift_iterate_residuePoint, sieveReturnTime_residuePoint]

theorem nextSieve_iterate_sub (F : AdmissibleFamily) (k J n : ℕ) :
    (nextSieve F k)^[J] n - n = sieveSpan F k J (residuePoint F n) := by
  induction J with
  | zero => simp [sieveSpan]
  | succ J ih =>
    have hpos : n ≤ (nextSieve F k)^[J] n := nextSieve_iterate_ge F k J n
    have hpos' : (nextSieve F k)^[J] n ≤ (nextSieve F k)^[J + 1] n :=
      Nat.le_of_lt (by
        simpa [Function.iterate_succ_apply'] using
          nextSieve_gt F k ((nextSieve F k)^[J] n))
    have htel :
        (nextSieve F k)^[J + 1] n - n =
          ((nextSieve F k)^[J + 1] n - (nextSieve F k)^[J] n) +
            ((nextSieve F k)^[J] n - n) := by
      omega
    rw [htel, nextSieve_diff_sieveReturn, ih]
    simp [sieveSpan, sum_range_succ, add_comm]

theorem truncTestWindowSieve_eq_model (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) (n : ℕ) :
    truncTestWindowSieve F k b J H f n =
      truncTestWindowSieveModel F k b J H f (residuePoint F n) := by
  unfold truncTestWindowSieve truncTestWindowSieveModel
  rw [mem_survivalFin_residuePoint]
  by_cases hB : residueSieve F k n
  · simp only [hB, ite_true]
    have hiff :
        (nextSieve F k)^[J] n ≤ n + H ↔
          sieveSpan F k J (residuePoint F n) ≤ H := by
      rw [← nextSieve_iterate_sub F k J n]
      exact (Nat.sub_le_iff_le_add').symm
    simp only [hiff]
    by_cases hsp : sieveSpan F k J (residuePoint F n) ≤ H
    · simp only [hsp, ite_true]
      congr 1
      unfold sieveTrunc
      refine sum_congr rfl fun j _ => ?_
      have hle : (nextSieve F k)^[j] n ≤ (nextSieve F k)^[j + 1] n :=
        Nat.le_of_lt (by
          simpa [Function.iterate_succ_apply'] using
            nextSieve_gt F k ((nextSieve F k)^[j] n))
      rw [← Nat.cast_sub hle, nextSieve_diff_sieveReturn]
    · simp only [hsp, ite_false]
  · simp only [hB, ite_false]

theorem truncTestWindowSieve_periodic (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) (n : ℕ) :
    truncTestWindowSieve F k b J H f (n + partialPeriod F k) =
      truncTestWindowSieve F k b J H f n := by
  unfold truncTestWindowSieve
  have hper : residueSieve F k (n + partialPeriod F k) ↔ residueSieve F k n := by
    simpa [one_mul] using
      residueSieve_add_period (F := F) (k := k) (a := n) (t := 1)
  simp only [hper]
  by_cases hB : residueSieve F k n
  · simp only [hB, ite_true]
    rw [nextSieve_iterate_add_period]
    have hiff :
        (nextSieve F k)^[J] n + partialPeriod F k ≤
            n + partialPeriod F k + H ↔
          (nextSieve F k)^[J] n ≤ n + H := by
      have hadd :
          n + partialPeriod F k + H = n + H + partialPeriod F k := by
        simp [add_comm, add_left_comm, add_assoc]
      rw [hadd]
      exact Nat.add_le_add_iff_right
    simp only [hiff]
    by_cases hsp : (nextSieve F k)^[J] n ≤ n + H
    · simp only [hsp, ite_true]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      have h1 := nextSieve_iterate_add_period F k (j + 1) n
      have h0 := nextSieve_iterate_add_period F k j n
      have hj1 :
          (nextSieve F k)^[j + 1] (n + partialPeriod F k) =
            (nextSieve F k)^[j + 1] n + partialPeriod F k := h1
      have hj0 :
          (nextSieve F k)^[j] (n + partialPeriod F k) =
            (nextSieve F k)^[j] n + partialPeriod F k := h0
      have hle :
          (nextSieve F k)^[j] n ≤ (nextSieve F k)^[j + 1] n :=
        Nat.le_of_lt (by
          simpa [Function.iterate_succ_apply'] using
            nextSieve_gt F k ((nextSieve F k)^[j] n))
      have hle' :
          (nextSieve F k)^[j] n + partialPeriod F k ≤
            (nextSieve F k)^[j + 1] n + partialPeriod F k :=
        Nat.add_le_add_right hle _
      rw [hj1, hj0]
      simp [Nat.cast_add]
    · simp only [hsp, ite_false]
  · simp only [hB, ite_false]

theorem abs_truncTestWindowSieve_le {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) (n : ℕ) :
    |truncTestWindowSieve F k b J H f n| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  unfold truncTestWindowSieve
  split_ifs
  · exact hbdd _
  · rwa [abs_zero]
  · rwa [abs_zero]

theorem abs_truncTestWindowSieveModel_le {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M)
    (ω : ResidueSpace F) :
    |truncTestWindowSieveModel F k b J H f ω| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  unfold truncTestWindowSieveModel
  split_ifs
  · exact hbdd _
  · rwa [abs_zero]
  · rwa [abs_zero]

abbrev FiniteCoords (F : AdmissibleFamily) (k : ℕ) :=
  ∀ i : Fin k, ZMod (F.d i.val)

def restrictFin (F : AdmissibleFamily) (k : ℕ) (ω : ResidueSpace F) :
    FiniteCoords F k :=
  fun i => ω i.val

def extendZero (F : AdmissibleFamily) (k : ℕ) (x : FiniteCoords F k) :
    ResidueSpace F :=
  fun i => if hi : i < k then x ⟨i, hi⟩ else 0

def DependsOnFin (F : AdmissibleFamily) (k : ℕ)
    (g : ResidueSpace F → ℝ) : Prop :=
  ∀ ω ω', restrictFin F k ω = restrictFin F k ω' → g ω = g ω'

def coordFiber (F : AdmissibleFamily) (k : ℕ) (x : FiniteCoords F k) :
    Set (ResidueSpace F) :=
  {ω | restrictFin F k ω = x}

theorem dependsOnFin_extend {F : AdmissibleFamily} {k : ℕ}
    {g : ResidueSpace F → ℝ} (h : DependsOnFin F k g)
    (ω : ResidueSpace F) :
    g ω = g (extendZero F k (restrictFin F k ω)) := by
  refine h ω _ ?_
  ext i
  simp [restrictFin, extendZero, i.isLt]

theorem partialPeriod_piEquiv_natCast (F : AdmissibleFamily) (k n : ℕ)
    (i : Fin k) :
    partialPeriod_piEquiv F k n i = n := by
  have h := map_natCast (partialPeriod_piEquiv F k).toRingHom n
  exact congrFun h i

noncomputable def coordsOfNat (F : AdmissibleFamily) (k n : ℕ) :
    FiniteCoords F k :=
  partialPeriod_piEquiv F k n

noncomputable def natOfCoords (F : AdmissibleFamily) (k : ℕ)
    (x : FiniteCoords F k) : ℕ :=
  ((partialPeriod_piEquiv F k).symm x).val

theorem coordsOfNat_restrict (F : AdmissibleFamily) (k n : ℕ) :
    coordsOfNat F k n = restrictFin F k (residuePoint F n) := by
  ext i
  simp [coordsOfNat, restrictFin, residuePoint, partialPeriod_piEquiv_natCast]

theorem natOfCoords_lt (F : AdmissibleFamily) (k : ℕ)
    (x : FiniteCoords F k) :
    natOfCoords F k x < partialPeriod F k :=
  ZMod.val_lt _

theorem coordsOfNat_natOfCoords (F : AdmissibleFamily) (k : ℕ)
    (x : FiniteCoords F k) :
    coordsOfNat F k (natOfCoords F k x) = x := by
  simp [coordsOfNat, natOfCoords, ZMod.natCast_val, RingEquiv.apply_symm_apply]

theorem natOfCoords_coordsOfNat (F : AdmissibleFamily) (k n : ℕ)
    (hn : n < partialPeriod F k) :
    natOfCoords F k (coordsOfNat F k n) = n := by
  unfold natOfCoords coordsOfNat
  rw [RingEquiv.symm_apply_apply]
  exact ZMod.val_natCast_of_lt hn

theorem prod_inv_d_eq_inv_period (F : AdmissibleFamily) (k : ℕ) :
    (∏ i ∈ range k, (F.d i : ℝ≥0∞)⁻¹) = (partialPeriod F k : ℝ≥0∞)⁻¹ := by
  induction k with
  | zero => simp [partialPeriod_zero]
  | succ k ih =>
    rw [prod_range_succ, partialPeriod_succ, ih, Nat.cast_mul]
    have hP0 : (partialPeriod F k : ℝ≥0∞) ≠ 0 := by
      intro h
      apply (partialPeriod_pos F k).ne'
      exact_mod_cast h
    have hd0 : (F.d k : ℝ≥0∞) ≠ 0 := by
      intro h
      apply d_ne_zero F k
      exact_mod_cast h
    exact (ENNReal.mul_inv (Or.inl hP0) (Or.inr hd0)).symm

theorem coordFiber_eq_pi (F : AdmissibleFamily) (k : ℕ)
    (x : FiniteCoords F k) :
    coordFiber F k x =
      Set.pi (range k : Set ℕ) fun i =>
        if hi : i < k then ({x ⟨i, hi⟩} : Set (ZMod (F.d i))) else Set.univ := by
  ext ω
  constructor
  · intro hω i hi
    have hik : i < k := mem_range.mp (by simpa using hi)
    simp [hik]
    simpa [restrictFin] using congrFun hω ⟨i, hik⟩
  · intro h
    refine funext fun i => ?_
    have hik : i.val < k := i.isLt
    have hi' : i.val ∈ (range k : Set ℕ) := by simp [mem_range, hik]
    have hmem := h i.val hi'
    simpa [hik, restrictFin] using hmem

theorem measure_coordFiber (F : AdmissibleFamily) (k : ℕ)
    (x : FiniteCoords F k) :
    productMeasure F (coordFiber F k x) =
      (partialPeriod F k : ℝ≥0∞)⁻¹ := by
  rw [coordFiber_eq_pi, productMeasure, Measure.infinitePi_pi]
  · refine Eq.trans ?_ (prod_inv_d_eq_inv_period F k)
    refine prod_congr rfl fun i hi => ?_
    have hik : i < k := mem_range.mp hi
    simp only [hik, ↓reduceDIte, coordMeasure_singleton]
  · intro i hi
    have hik : i < k := mem_range.mp hi
    simp only [hik, ↓reduceDIte]
    exact measurableSet_singleton _

theorem measurableSet_coordFiber (F : AdmissibleFamily) (k : ℕ)
    (x : FiniteCoords F k) : MeasurableSet (coordFiber F k x) := by
  rw [coordFiber_eq_pi]
  refine MeasurableSet.pi (Finset.countable_toSet _) fun i hi => ?_
  have hik : i < k := mem_range.mp (by simpa using hi)
  simp only [hik, ↓reduceDIte]
  exact measurableSet_singleton _

theorem integral_dependsOnFin (F : AdmissibleFamily) (k : ℕ)
    {g : ResidueSpace F → ℝ} (hdep : DependsOnFin F k g)
    (hg : Integrable g (productMeasure F)) :
    ∫ ω, g ω ∂productMeasure F =
      (∑ n ∈ range (partialPeriod F k), g (residuePoint F n)) /
        (partialPeriod F k : ℝ) := by
  let P := partialPeriod F k
  have hPpos : (0 : ℝ) < P := Nat.cast_pos.mpr (partialPeriod_pos F k)
  have hg_eq : g = fun ω =>
      ∑ x : FiniteCoords F k,
        (coordFiber F k x).indicator (fun _ => g (extendZero F k x)) ω := by
    funext ω
    let x := restrictFin F k ω
    rw [Fintype.sum_eq_single x]
    · have hx : ω ∈ coordFiber F k x := rfl
      simp [Set.indicator_of_mem hx]
      exact dependsOnFin_extend hdep ω
    · intro y hy
      have : ω ∉ coordFiber F k y := fun hmem => hy hmem.symm
      simp [Set.indicator_of_notMem this]
  have hint : ∀ x : FiniteCoords F k,
      Integrable
        ((coordFiber F k x).indicator (fun _ => g (extendZero F k x)))
        (productMeasure F) := fun x =>
    (integrable_const (g (extendZero F k x))).indicator
      (measurableSet_coordFiber F k x)
  conv_lhs => rw [hg_eq]
  rw [integral_finsetSum Finset.univ (fun x _ => hint x)]
  have hxμ : ∀ x : FiniteCoords F k,
      (productMeasure F).real (coordFiber F k x) = (P : ℝ)⁻¹ := by
    intro x
    rw [Measure.real, measure_coordFiber, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hint' :
      ∀ x : FiniteCoords F k,
        ∫ ω, (coordFiber F k x).indicator (fun _ => g (extendZero F k x)) ω
            ∂productMeasure F =
          g (extendZero F k x) * (P : ℝ)⁻¹ := by
    intro x
    rw [integral_indicator_const _ (measurableSet_coordFiber F k x), smul_eq_mul,
      hxμ, mul_comm]
  simp_rw [hint']
  have hsumμ :
      ∑ x : FiniteCoords F k, g (extendZero F k x) * (P : ℝ)⁻¹ =
        (∑ x : FiniteCoords F k, g (extendZero F k x)) * (P : ℝ)⁻¹ := by
    rw [← Finset.sum_mul]
  rw [hsumμ, div_eq_mul_inv]
  have hsums :
      ∑ x : FiniteCoords F k, g (extendZero F k x) =
        ∑ n ∈ range P, g (residuePoint F n) := by
    have himg :
        (range P).image (coordsOfNat F k) =
          (Finset.univ : Finset (FiniteCoords F k)) := by
      ext x
      constructor
      · intro
        exact mem_univ _
      · intro
        exact mem_image.mpr ⟨natOfCoords F k x, mem_range.mpr (natOfCoords_lt F k x),
          coordsOfNat_natOfCoords F k x⟩
    have hinj : ∀ a ∈ range P, ∀ b ∈ range P,
        coordsOfNat F k a = coordsOfNat F k b → a = b := by
      intro a ha b hb h
      have ha' := natOfCoords_coordsOfNat F k a (mem_range.mp ha)
      have hb' := natOfCoords_coordsOfNat F k b (mem_range.mp hb)
      rw [← ha', ← hb']
      exact congrArg (natOfCoords F k) h
    rw [← himg, sum_image hinj]
    refine sum_congr rfl fun n hn => ?_
    rw [coordsOfNat_restrict]
    exact (dependsOnFin_extend hdep (residuePoint F n)).symm
  rw [hsums]

theorem sieveReturnTime_congr (F : AdmissibleFamily) (k : ℕ)
    {ω ω' : ResidueSpace F}
    (h : restrictFin F k ω = restrictFin F k ω') :
    sieveReturnTime F k ω = sieveReturnTime F k ω' := by
  unfold sieveReturnTime
  refine Nat.find_congr' ?_
  intro t
  constructor
  · intro ⟨ht, hall⟩
    refine ⟨ht, fun i hi => ?_⟩
    have hi' : ω i = ω' i := by
      have := congrFun h ⟨i, hi⟩
      simpa [restrictFin] using this
    simpa [hi'] using hall i hi
  · intro ⟨ht, hall⟩
    refine ⟨ht, fun i hi => ?_⟩
    have hi' : ω i = ω' i := by
      have := congrFun h ⟨i, hi⟩
      simpa [restrictFin] using this
    simpa [hi'] using hall i hi

theorem inducedSieveShift_congr (F : AdmissibleFamily) (k : ℕ)
    {ω ω' : ResidueSpace F}
    (h : restrictFin F k ω = restrictFin F k ω') :
    restrictFin F k (inducedSieveShift F k ω) =
      restrictFin F k (inducedSieveShift F k ω') := by
  have ht := sieveReturnTime_congr F k h
  ext i
  simp [restrictFin, inducedSieveShift, shift_iterate_apply, ht]
  have hi := congrFun h i
  simpa [restrictFin] using hi

theorem inducedSieveShift_iterate_congr (F : AdmissibleFamily) (k j : ℕ)
    {ω ω' : ResidueSpace F}
    (h : restrictFin F k ω = restrictFin F k ω') :
    restrictFin F k ((inducedSieveShift F k)^[j] ω) =
      restrictFin F k ((inducedSieveShift F k)^[j] ω') := by
  induction j with
  | zero => simpa
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact inducedSieveShift_congr F k ih

theorem dependsOnFin_sieveModel (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) :
    DependsOnFin F k (truncTestWindowSieveModel F k b J H f) := by
  intro ω ω' h
  unfold truncTestWindowSieveModel
  have hA : ω ∈ survivalFin F k ↔ ω' ∈ survivalFin F k := by
    simp [mem_survivalFin]
    constructor
    · intro hω i hi
      have heq : ω i = ω' i := by
        simpa [restrictFin] using congrFun h ⟨i, hi⟩
      rw [← heq]
      exact hω i hi
    · intro hω i hi
      have heq : ω i = ω' i := by
        simpa [restrictFin] using congrFun h ⟨i, hi⟩
      rw [heq]
      exact hω i hi
  have hspan : sieveSpan F k J ω = sieveSpan F k J ω' := by
    unfold sieveSpan
    refine sum_congr rfl fun j _ => ?_
    rw [sieveReturnTime_congr F k (inducedSieveShift_iterate_congr F k j h)]
  have htrunc : sieveTrunc F k b J ω = sieveTrunc F k b J ω' := by
    unfold sieveTrunc
    refine sum_congr rfl fun j _ => ?_
    rw [sieveReturnTime_congr F k (inducedSieveShift_iterate_congr F k j h)]
  simp [hA, hspan, htrunc]

theorem measurableSet_survivalFin (F : AdmissibleFamily) (k : ℕ) :
    MeasurableSet (survivalFin F k) :=
  survivalCylinder_measurable F (range k)

theorem measurable_sieveReturnTime (F : AdmissibleFamily) (k : ℕ) :
    Measurable (sieveReturnTime F k) := by
  refine measurable_find (fun ω => exists_pos_cylinderHit F k ω) fun t => ?_
  by_cases ht : 0 < t
  · have hset :
        {ω : ResidueSpace F | 0 < t ∧ ∀ i < k, ω i + t ≠ 0} =
          ⋂ i ∈ (range k : Set ℕ), {ω : ResidueSpace F | ω i + t ≠ 0} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_coe, mem_range]
      constructor
      · intro h i hi
        exact h.2 i hi
      · intro h
        exact ⟨ht, h⟩
    rw [hset]
    exact MeasurableSet.biInter (countable_toSet _) fun i _ =>
      measurableSet_coord_add_ne F i t
  · have hset :
        {ω : ResidueSpace F | 0 < t ∧ ∀ i < k, ω i + t ≠ 0} = ∅ := by
      ext ω
      simp [ht]
    simpa [hset] using MeasurableSet.empty

theorem measurable_inducedSieveShift (F : AdmissibleFamily) (k : ℕ) :
    Measurable (inducedSieveShift F k) := by
  intro s hs
  have hpre : inducedSieveShift F k ⁻¹' s =
      ⋃ n : ℕ, {ω | sieveReturnTime F k ω = n} ∩ (shift F)^[n] ⁻¹' s := by
    ext ω
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨sieveReturnTime F k ω, ⟨rfl, h⟩⟩
    · intro h
      obtain ⟨n, ⟨hn, hmem⟩⟩ := Set.mem_iUnion.mp h
      change (shift F)^[sieveReturnTime F k ω] ω ∈ s
      rw [hn]
      exact hmem
  rw [hpre]
  exact MeasurableSet.iUnion fun n =>
    ((measurable_sieveReturnTime F k) (measurableSet_singleton n)).inter
      (((shift_measurePreserving F).iterate n).measurable hs)

theorem measurable_sieveSpan (F : AdmissibleFamily) (k J : ℕ) :
    Measurable (sieveSpan F k J) :=
  Finset.measurable_sum (range J) fun j _ =>
    (measurable_sieveReturnTime F k).comp
      ((measurable_inducedSieveShift F k).iterate j)

theorem measurable_sieveTrunc (F : AdmissibleFamily) (k b J : ℕ) :
    Measurable (sieveTrunc F k b J) := by
  refine Finset.measurable_sum (range J) fun j _ => ?_
  have hret :
      Measurable fun ω =>
        (sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) : ℝ) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_sieveReturnTime F k).comp
        ((measurable_inducedSieveShift F k).iterate j))
  exact hret.div_const _

theorem measurable_truncTestWindowSieveModel (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (truncTestWindowSieveModel F k b J H f) := by
  have hA := measurableSet_survivalFin F k
  have hspan : MeasurableSet {ω | sieveSpan F k J ω ≤ H} :=
    (measurable_sieveSpan F k J)
      (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic H))
  have hfun : Measurable fun ω => f (sieveTrunc F k b J ω) :=
    hf.measurable.comp (measurable_sieveTrunc F k b J)
  exact Measurable.ite hA (Measurable.ite hspan hfun measurable_const) measurable_const

theorem period_average_sieveModel (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F =
      (∑ n ∈ range (partialPeriod F k),
          truncTestWindowSieve F k b J H f n) /
        (partialPeriod F k : ℝ) := by
  have hdep := dependsOnFin_sieveModel F k b J H f
  have hmeas := measurable_truncTestWindowSieveModel F k b J H hf
  have hg : Integrable (truncTestWindowSieveModel F k b J H f)
      (productMeasure F) :=
    (integrable_const M).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_truncTestWindowSieveModel_le F k b J H hbdd ω)
  have hinter := integral_dependsOnFin F k hdep hg
  refine hinter.trans ?_
  congr 1
  refine sum_congr rfl fun n _ => ?_
  exact (truncTestWindowSieve_eq_model F k b J H f n).symm

theorem sum_sieve_range_eq_Icc (F : AdmissibleFamily) (k b J H : ℕ)
    (f : ℝ → ℝ) :
    ∑ n ∈ range (partialPeriod F k), truncTestWindowSieve F k b J H f n =
      ∑ n ∈ Icc 1 (partialPeriod F k), truncTestWindowSieve F k b J H f n := by
  set P := partialPeriod F k
  have hP := partialPeriod_pos F k
  have h0P : truncTestWindowSieve F k b J H f P =
      truncTestWindowSieve F k b J H f 0 := by
    simpa using truncTestWindowSieve_periodic F k b J H f 0
  have hr : range P = insert 0 (Icc 1 (P - 1)) := by
    ext n
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have hI : Icc 1 P = insert P (Icc 1 (P - 1)) := by
    ext n
    simp only [mem_insert, mem_Icc]
    omega
  rw [hr, hI]
  rw [sum_insert, sum_insert]
  · rw [h0P]
  · intro h
    have := mem_Icc.mp h
    omega
  · intro h
    have := mem_Icc.mp h
    omega

/-! Paper after (21): physical mismatch, periodic sieve Cesaro, Haar
identification, then Palm along `enum`. No Birkhoff genericity of a
model point. -/

theorem nextBFree_eq_nextSieve_of_agree (F : AdmissibleFamily)
    (k n X : ℕ)
    (h : ∀ m, n < m → m ≤ X → (BFree F m ↔ residueSieve F k m)) :
    (nextBFree F n ≤ X ↔ nextSieve F k n ≤ X) ∧
      (nextBFree F n ≤ X → nextBFree F n = nextSieve F k n) := by
  constructor
  · constructor
    · intro hB
      have hmem : residueSieve F k (nextBFree F n) :=
        (h _ (nextBFree_gt F n) hB).mp (nextBFree_mem F n)
      exact (nextSieve_min F k (nextBFree_gt F n) hmem).trans hB
    · intro hS
      have hmem : BFree F (nextSieve F k n) :=
        (h _ (nextSieve_gt F k n) hS).mpr (nextSieve_mem F k n)
      exact (nextBFree_min F (nextSieve_gt F k n) hmem).trans hS
  · intro hB
    apply le_antisymm
    · have hS : nextSieve F k n ≤ X := by
        have hmem : residueSieve F k (nextBFree F n) :=
          (h _ (nextBFree_gt F n) hB).mp (nextBFree_mem F n)
        exact (nextSieve_min F k (nextBFree_gt F n) hmem).trans hB
      have hmem : BFree F (nextSieve F k n) :=
        (h _ (nextSieve_gt F k n) hS).mpr (nextSieve_mem F k n)
      exact nextBFree_min F (nextSieve_gt F k n) hmem
    · have hmem : residueSieve F k (nextBFree F n) :=
        (h _ (nextBFree_gt F n) hB).mp (nextBFree_mem F n)
      exact nextSieve_min F k (nextBFree_gt F n) hmem

theorem nextBFree_iterate_eq_sieve_of_agree (F : AdmissibleFamily)
    (k n H j : ℕ)
    (h : ∀ m, n < m → m ≤ n + H → (BFree F m ↔ residueSieve F k m))
    (hle : (nextBFree F)^[j] n ≤ n + H) :
    (nextBFree F)^[j] n = (nextSieve F k)^[j] n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (nextBFree F),
      Function.iterate_succ_apply' (nextSieve F k)]
    have hprev : (nextBFree F)^[j] n ≤ n + H := by
      refine (Nat.le_of_lt (nextBFree_gt F ((nextBFree F)^[j] n))).trans ?_
      rwa [Function.iterate_succ_apply' (nextBFree F)] at hle
    have heq := ih hprev
    have h' : ∀ m, (nextBFree F)^[j] n < m → m ≤ n + H →
        (BFree F m ↔ residueSieve F k m) :=
      fun m hm hmH =>
        h m (lt_of_le_of_lt (nextBFree_iterate_ge F j n) hm) hmH
    have hB : nextBFree F ((nextBFree F)^[j] n) ≤ n + H := by
      rwa [Function.iterate_succ_apply' (nextBFree F)] at hle
    have hns :=
      (nextBFree_eq_nextSieve_of_agree F k ((nextBFree F)^[j] n) (n + H) h').2 hB
    rw [hns, heq]

theorem nextSieve_iterate_eq_bfree_of_agree (F : AdmissibleFamily)
    (k n H j : ℕ)
    (h : ∀ m, n < m → m ≤ n + H → (BFree F m ↔ residueSieve F k m))
    (hle : (nextSieve F k)^[j] n ≤ n + H) :
    (nextBFree F)^[j] n = (nextSieve F k)^[j] n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (nextBFree F),
      Function.iterate_succ_apply' (nextSieve F k)]
    have hprev : (nextSieve F k)^[j] n ≤ n + H := by
      refine (Nat.le_of_lt (nextSieve_gt F k ((nextSieve F k)^[j] n))).trans ?_
      rwa [Function.iterate_succ_apply' (nextSieve F k)] at hle
    have heq := ih hprev
    have h' : ∀ m, (nextSieve F k)^[j] n < m → m ≤ n + H →
        (BFree F m ↔ residueSieve F k m) :=
      fun m hm hmH =>
        h m (lt_of_le_of_lt (nextSieve_iterate_ge F k j n) hm) hmH
    have hS : nextSieve F k ((nextSieve F k)^[j] n) ≤ n + H := by
      rwa [Function.iterate_succ_apply' (nextSieve F k)] at hle
    have hBnd :=
      (nextBFree_eq_nextSieve_of_agree F k ((nextSieve F k)^[j] n) (n + H) h').1.mpr hS
    have hns :=
      (nextBFree_eq_nextSieve_of_agree F k ((nextSieve F k)^[j] n) (n + H) h').2 hBnd
    rw [heq, hns]

theorem nextBFree_iterate_mono (F : AdmissibleFamily) {j J n : ℕ}
    (h : j ≤ J) :
    (nextBFree F)^[j] n ≤ (nextBFree F)^[J] n := by
  have hdecomp : (nextBFree F)^[J] n =
      (nextBFree F)^[(J - j) + j] n := by
    rw [Nat.sub_add_cancel h]
  rw [hdecomp, Function.iterate_add_apply]
  exact nextBFree_iterate_ge F (J - j) _

theorem nextSieve_iterate_mono (F : AdmissibleFamily) (k : ℕ) {j J n : ℕ}
    (h : j ≤ J) :
    (nextSieve F k)^[j] n ≤ (nextSieve F k)^[J] n := by
  have hdecomp : (nextSieve F k)^[J] n =
      (nextSieve F k)^[(J - j) + j] n := by
    rw [Nat.sub_add_cancel h]
  rw [hdecomp, Function.iterate_add_apply]
  exact nextSieve_iterate_ge F k (J - j) _

theorem truncTestWindow_eq_sieve_of_agree (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) (n : ℕ)
    (h : ∀ m, n < m → m ≤ n + H → (BFree F m ↔ residueSieve F k m))
    (h0 : BFree F n ↔ residueSieve F k n) :
    truncTestWindow F b J H f n = truncTestWindowSieve F k b J H f n := by
  unfold truncTestWindow truncTestWindowSieve
  simp only [h0]
  by_cases hB : BFree F n
  · have hB' : residueSieve F k n := h0.mp hB
    simp only [hB, hB', ite_true]
    have hiff :
        (nextBFree F)^[J] n ≤ n + H ↔ (nextSieve F k)^[J] n ≤ n + H := by
      constructor
      · intro hle
        simpa [nextBFree_iterate_eq_sieve_of_agree F k n H J h hle] using hle
      · intro hle
        simpa [nextSieve_iterate_eq_bfree_of_agree F k n H J h hle] using hle
    simp only [hiff]
    by_cases hsp : (nextSieve F k)^[J] n ≤ n + H
    · simp only [hsp, ite_true]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      have hjJ : j + 1 ≤ J := Nat.succ_le_of_lt (mem_range.mp hj)
      have hBspan : (nextBFree F)^[J] n ≤ n + H := hiff.mpr hsp
      have hlej : (nextBFree F)^[j] n ≤ n + H :=
        (nextBFree_iterate_mono F (mem_range.mp hj).le).trans hBspan
      have hlej1 : (nextBFree F)^[j + 1] n ≤ n + H :=
        (nextBFree_iterate_mono F hjJ).trans hBspan
      have heqj := nextBFree_iterate_eq_sieve_of_agree F k n H j h hlej
      have heqj1 := nextBFree_iterate_eq_sieve_of_agree F k n H (j + 1) h hlej1
      rw [heqj, heqj1]
    · simp only [hsp, ite_false]
  · have : ¬ residueSieve F k n := fun hS => hB (h0.mpr hS)
    simp [hB, this]

theorem residueSieve_of_BFree (F : AdmissibleFamily) (k n : ℕ)
    (h : BFree F n) : residueSieve F k n :=
  fun i _ => h.2 i

theorem mismatch_of_window_disagree (F : AdmissibleFamily)
    (k n H : ℕ)
    (hdis : ¬ ((BFree F n ↔ residueSieve F k n) ∧
      ∀ m, n < m → m ≤ n + H → (BFree F m ↔ residueSieve F k m))) :
    ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j) := by
  by_contra hnone
  apply hdis
  constructor
  · constructor
    · intro hB
      exact residueSieve_of_BFree F k n hB
    · intro hS
      by_contra hB
      exact hnone ⟨0, Nat.zero_le _, hS, hB⟩
  · intro m hm hmH
    constructor
    · intro hB
      exact residueSieve_of_BFree F k m hB
    · intro hS
      by_contra hB
      refine hnone ⟨m - n, ?_, ?_, ?_⟩
      · exact (Nat.sub_le_iff_le_add').mpr hmH
      · simpa [Nat.add_sub_of_le (Nat.le_of_lt hm)] using hS
      · simpa [Nat.add_sub_of_le (Nat.le_of_lt hm)] using hB

theorem abs_window_sub_sieve_le {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) (n : ℕ) :
    |truncTestWindow F b J H f n - truncTestWindowSieve F k b J H f n| ≤
      if ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j) then 2 * M else 0 := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  by_cases hmis : ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)
  · simp only [hmis, ite_true]
    have h1 := abs_truncTestWindow_le F b J H hbdd n
    have h2 := abs_truncTestWindowSieve_le F k b J H hbdd n
    have htri :
        |truncTestWindow F b J H f n - truncTestWindowSieve F k b J H f n| ≤
          |truncTestWindow F b J H f n| +
            |truncTestWindowSieve F k b J H f n| := by
      have hnorm :=
        norm_add_le (truncTestWindow F b J H f n)
          (-truncTestWindowSieve F k b J H f n)
      simpa [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using hnorm
    exact htri.trans (by linarith)
  · have hagree :
        (BFree F n ↔ residueSieve F k n) ∧
          ∀ m, n < m → m ≤ n + H → (BFree F m ↔ residueSieve F k m) := by
      by_contra hdis
      exact hmis (mismatch_of_window_disagree F k n H hdis)
    have heq :=
      truncTestWindow_eq_sieve_of_agree F k b J H f n hagree.2 hagree.1
    simp [hmis, heq]

theorem sum_abs_window_sub_sieve {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) (X : ℕ) :
    ∑ n ∈ Icc 1 X,
        |truncTestWindow F b J H f n -
          truncTestWindowSieve F k b J H f n| ≤
      2 * M *
        (#{n ∈ Icc 1 X |
            ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)} : ℝ) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hpt : ∀ n ∈ Icc 1 X,
      |truncTestWindow F b J H f n - truncTestWindowSieve F k b J H f n| ≤
        2 * M *
          (if ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j) then
            (1 : ℝ) else 0) := by
    intro n hn
    have h := abs_window_sub_sieve_le F k b J H hbdd n
    by_cases hmis : ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)
    · simpa [hmis, mul_one] using h
    · simpa [hmis] using h
  have hsum := sum_le_sum hpt
  have hif :
      ∑ n ∈ Icc 1 X,
          (if ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j) then
            (1 : ℝ) else 0) =
        (#{n ∈ Icc 1 X |
            ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j)} : ℝ) := by
    simp [sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  have hmul :
      ∑ n ∈ Icc 1 X,
          2 * M *
            (if ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j) then
              (1 : ℝ) else 0) =
        2 * M *
          ∑ n ∈ Icc 1 X,
            (if ∃ j ≤ H, residueSieve F k (n + j) ∧ ¬ BFree F (n + j) then
              (1 : ℝ) else 0) :=
    (mul_sum _ _ _).symm
  exact hsum.trans (by rw [hmul, hif])

theorem tendsto_cesaro_truncTestWindowSieve (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Tendsto (fun X : ℕ =>
        (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ))
      atTop
      (𝓝 (∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F)) := by
  have hper : ∀ n, truncTestWindowSieve F k b J H f (n + partialPeriod F k) =
      truncTestWindowSieve F k b J H f n :=
    truncTestWindowSieve_periodic F k b J H f
  have hces :=
    tendsto_cesaro_periodic (partialPeriod_pos F k)
      (truncTestWindowSieve F k b J H f) hper
  have havg := period_average_sieveModel F k b J H hf hbdd
  have hIcc := sum_sieve_range_eq_Icc F k b J H f
  have hlim :
      ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F =
        (∑ n ∈ Icc 1 (partialPeriod F k),
            truncTestWindowSieve F k b J H f n) /
          (partialPeriod F k : ℝ) :=
    havg.trans (by rw [hIcc])
  rwa [hlim]

theorem integrable_truncTestWindowSieveModel {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Integrable (truncTestWindowSieveModel F k b J H f) (productMeasure F) :=
  (integrable_const M).mono'
    (measurable_truncTestWindowSieveModel F k b J H hf).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_truncTestWindowSieveModel_le F k b J H hbdd ω)

theorem survival_subset_survivalFin (F : AdmissibleFamily) (k : ℕ) :
    survival F ⊆ survivalFin F k := by
  intro ω hω
  rw [mem_survivalFin]
  intro i _
  exact hω i

theorem shift_iterate_mem_survivalFin (F : AdmissibleFamily) (k t : ℕ)
    (ω : ResidueSpace F) :
    (shift F)^[t] ω ∈ survivalFin F k ↔ ∀ i < k, ω i + t ≠ 0 := by
  rw [mem_survivalFin]
  constructor
  · intro h i hi
    simpa [shift_iterate_apply] using h i hi
  · intro h i hi
    simpa [shift_iterate_apply] using h i hi

theorem measurableSet_coord_eq_zero (F : AdmissibleFamily) (i : ℕ) :
    MeasurableSet {ω : ResidueSpace F | ω i = 0} :=
  (measurable_pi_apply i) (measurableSet_singleton 0)

theorem measure_coord_eq_zero (F : AdmissibleFamily) (i : ℕ) :
    productMeasure F {ω : ResidueSpace F | ω i = 0} =
      (F.d i : ℝ≥0∞)⁻¹ := by
  have hmeas : Measurable fun ω : ResidueSpace F => ω i := measurable_pi_apply i
  have hpre :
      {ω : ResidueSpace F | ω i = 0} =
        (fun ω : ResidueSpace F => ω i) ⁻¹' ({0} : Set (ZMod (F.d i))) := by
    ext ω
    simp
  rw [hpre, ← Measure.map_apply hmeas (measurableSet_singleton 0),
    productMeasure_map_eval, coordMeasure_singleton_zero]

theorem survivalFin_sdiff_subset_tail_zeros (F : AdmissibleFamily) (k : ℕ) :
    survivalFin F k \ survival F ⊆
      ⋃ i : ℕ, {ω : ResidueSpace F | ω (i + k) = 0} := by
  intro ω hω
  have hFin : ω ∈ survivalFin F k := hω.1
  have hnot : ω ∉ survival F := hω.2
  have hex : ∃ i, ω i = 0 := by
    simpa [survival] using hnot
  obtain ⟨i, hi0⟩ := hex
  have hik : k ≤ i := by
    by_contra hki
    exact (mem_survivalFin F k ω).mp hFin i (Nat.not_le.mp hki) hi0
  refine Set.mem_iUnion.mpr ⟨i - k, ?_⟩
  change ω (i - k + k) = 0
  rwa [Nat.sub_add_cancel hik]

theorem tsum_inv_d_ennreal (F : AdmissibleFamily) (k : ℕ) :
    ∑' i, (F.d (i + k) : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (∑' i, (1 : ℝ) / F.d (i + k)) := by
  have hterm : ∀ i : ℕ,
      (F.d (i + k) : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / F.d (i + k)) := by
    intro i
    have hpos : (0 : ℝ) < F.d (i + k) := Nat.cast_pos.mpr (d_pos F (i + k))
    rw [one_div, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hpos]
  simp_rw [hterm]
  have hshift : Summable fun i : ℕ => (1 : ℝ) / F.d (i + k) :=
    (summable_nat_add_iff (f := fun i => (1 : ℝ) / F.d i) k).2 F.summable
  refine (ENNReal.ofReal_tsum_of_nonneg
      (fun i => one_div_d_nonneg F (i + k)) hshift).symm

theorem measure_survivalFin_sdiff_le (F : AdmissibleFamily) (k : ℕ) :
    productMeasure F (survivalFin F k \ survival F) ≤
      ENNReal.ofReal (∑' i, (1 : ℝ) / F.d (i + k)) := by
  have hsub := survivalFin_sdiff_subset_tail_zeros F k
  have hle := measure_mono (μ := productMeasure F) hsub
  have hU :
      productMeasure F (⋃ i : ℕ, {ω : ResidueSpace F | ω (i + k) = 0}) ≤
        ∑' i, productMeasure F {ω : ResidueSpace F | ω (i + k) = 0} :=
    measure_iUnion_le _
  have hterm : ∀ i,
      productMeasure F {ω : ResidueSpace F | ω (i + k) = 0} =
        (F.d (i + k) : ℝ≥0∞)⁻¹ :=
    fun i => measure_coord_eq_zero F (i + k)
  have htsum :
      ∑' i, productMeasure F {ω : ResidueSpace F | ω (i + k) = 0} =
        ∑' i, (F.d (i + k) : ℝ≥0∞)⁻¹ :=
    tsum_congr hterm
  rw [htsum, tsum_inv_d_ennreal] at hU
  exact hle.trans hU

def haarMismatch (F : AdmissibleFamily) (k H : ℕ) : Set (ResidueSpace F) :=
  {ω | ∃ j ≤ H, (shift F)^[j] ω ∈ survivalFin F k \ survival F}

theorem haarMismatch_eq_biUnion (F : AdmissibleFamily) (k H : ℕ) :
    haarMismatch F k H =
      ⋃ j ∈ Icc 0 H,
        (shift F)^[j] ⁻¹' (survivalFin F k \ survival F) := by
  ext ω
  simp only [haarMismatch, Set.mem_iUnion, Set.mem_preimage, mem_Icc]
  constructor
  · intro ⟨j, hj, hmem⟩
    exact ⟨j, ⟨Nat.zero_le j, hj⟩, hmem⟩
  · intro ⟨j, ⟨_, hj⟩, hmem⟩
    exact ⟨j, hj, hmem⟩

theorem measurableSet_haarMismatch (F : AdmissibleFamily) (k H : ℕ) :
    MeasurableSet (haarMismatch F k H) := by
  rw [haarMismatch_eq_biUnion]
  refine Finset.measurableSet_biUnion _ fun j _ =>
    ((shift_measurePreserving F).iterate j).measurable
      ((measurableSet_survivalFin F k).diff (survival_measurable F))

theorem measure_haarMismatch_le (F : AdmissibleFamily) (k H : ℕ) :
    (productMeasure F).real (haarMismatch F k H) ≤
      (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
  have hτ : 0 ≤ ∑' i, (1 : ℝ) / F.d (i + k) :=
    tsum_nonneg fun i => one_div_d_nonneg F (i + k)
  have hU :
      productMeasure F (haarMismatch F k H) ≤
        ∑ j ∈ Icc 0 H,
          productMeasure F
            ((shift F)^[j] ⁻¹' (survivalFin F k \ survival F)) := by
    rw [haarMismatch_eq_biUnion]
    exact measure_biUnion_finset_le _ _
  have hsdiff :
      MeasurableSet (survivalFin F k \ survival F) :=
    (measurableSet_survivalFin F k).diff (survival_measurable F)
  have hterm : ∀ j ∈ Icc 0 H,
      productMeasure F ((shift F)^[j] ⁻¹' (survivalFin F k \ survival F)) =
        productMeasure F (survivalFin F k \ survival F) := fun j _ => by
    have hmp := (shift_measurePreserving F).iterate j
    rw [← Measure.map_apply hmp.measurable hsdiff, hmp.map_eq]
  have hsum :
      ∑ j ∈ Icc 0 H,
          productMeasure F
            ((shift F)^[j] ⁻¹' (survivalFin F k \ survival F)) =
        (H + 1 : ℝ≥0∞) * productMeasure F (survivalFin F k \ survival F) := by
    rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
    have hcard : ((Icc 0 H).card : ℝ≥0∞) = (H + 1 : ℝ≥0∞) := by
      simp [Nat.card_Icc]
    rw [hcard]
  have hmul :
      productMeasure F (haarMismatch F k H) ≤
        (H + 1 : ℝ≥0∞) *
          ENNReal.ofReal (∑' i, (1 : ℝ) / F.d (i + k)) :=
    hU.trans (hsum.trans_le
      (mul_le_mul' le_rfl (measure_survivalFin_sdiff_le F k)))
  have hcast : (H + 1 : ℝ≥0∞) = ENNReal.ofReal (H + 1 : ℝ) := by
    calc
      (H + 1 : ℝ≥0∞) = ((H + 1 : ℕ) : ℝ≥0∞) := (Nat.cast_succ H).symm
      _ = ENNReal.ofReal ((H + 1 : ℕ) : ℝ) := (ENNReal.ofReal_natCast (H + 1)).symm
      _ = ENNReal.ofReal (H + 1 : ℝ) := by rw [Nat.cast_succ]
  have hprod :
      (H + 1 : ℝ≥0∞) * ENNReal.ofReal (∑' i, (1 : ℝ) / F.d (i + k)) =
        ENNReal.ofReal ((H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k)) := by
    have hH : 0 ≤ (H + 1 : ℝ) := by positivity
    rw [hcast, ENNReal.ofReal_mul hH]
  have hle' :
      productMeasure F (haarMismatch F k H) ≤
        ENNReal.ofReal ((H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k)) := by
    rwa [hprod] at hmul
  have hfin :
      ENNReal.ofReal ((H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hleR := ENNReal.toReal_mono hfin hle'
  have hto :
      (ENNReal.ofReal ((H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k))).toReal =
        (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) :=
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) hτ)
  rw [hto] at hleR
  exact hleR

theorem modelSpan_mono (F : AdmissibleFamily) {j J : ℕ} (h : j ≤ J)
    (ω : ResidueSpace F) : modelSpan F j ω ≤ modelSpan F J ω := by
  unfold modelSpan
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h)
    fun _ _ _ => Nat.zero_le _

theorem sieveSpan_mono (F : AdmissibleFamily) (k : ℕ) {j J : ℕ} (h : j ≤ J)
    (ω : ResidueSpace F) : sieveSpan F k j ω ≤ sieveSpan F k J ω := by
  unfold sieveSpan
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h)
    fun _ _ _ => Nat.zero_le _

theorem modelSpan_succ (F : AdmissibleFamily) (j : ℕ) (ω : ResidueSpace F) :
    modelSpan F (j + 1) ω =
      modelSpan F j ω + returnTime F ((inducedShift F)^[j] ω) := by
  simp [modelSpan, sum_range_succ]

theorem sieveSpan_succ (F : AdmissibleFamily) (k j : ℕ) (ω : ResidueSpace F) :
    sieveSpan F k (j + 1) ω =
      sieveSpan F k j ω +
        sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) := by
  simp [sieveSpan, sum_range_succ]

theorem inducedShift_iterate_eq_shift_span (F : AdmissibleFamily) (j : ℕ)
    (ω : ResidueSpace F) :
    (inducedShift F)^[j] ω = (shift F)^[modelSpan F j ω] ω := by
  induction j with
  | zero => simp [modelSpan]
  | succ j ih =>
    calc
      (inducedShift F)^[j + 1] ω
          = inducedShift F ((inducedShift F)^[j] ω) :=
            Function.iterate_succ_apply' (inducedShift F) j ω
      _ = (shift F)^[returnTime F ((inducedShift F)^[j] ω)]
            ((inducedShift F)^[j] ω) := rfl
      _ = (shift F)^[returnTime F ((inducedShift F)^[j] ω)]
            ((shift F)^[modelSpan F j ω] ω) := by rw [ih]
      _ = (shift F)^[returnTime F ((inducedShift F)^[j] ω) +
            modelSpan F j ω] ω :=
          (Function.iterate_add_apply (shift F)
            (returnTime F ((inducedShift F)^[j] ω))
            (modelSpan F j ω) ω).symm
      _ = (shift F)^[modelSpan F j ω +
            returnTime F ((inducedShift F)^[j] ω)] ω := by
          rw [add_comm]
      _ = (shift F)^[modelSpan F (j + 1) ω] ω := by
          rw [modelSpan_succ]

theorem inducedSieveShift_iterate_eq_shift_span (F : AdmissibleFamily)
    (k j : ℕ) (ω : ResidueSpace F) :
    (inducedSieveShift F k)^[j] ω =
      (shift F)^[sieveSpan F k j ω] ω := by
  induction j with
  | zero => simp [sieveSpan]
  | succ j ih =>
    calc
      (inducedSieveShift F k)^[j + 1] ω
          = inducedSieveShift F k ((inducedSieveShift F k)^[j] ω) :=
            Function.iterate_succ_apply' (inducedSieveShift F k) j ω
      _ = (shift F)^[sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)]
            ((inducedSieveShift F k)^[j] ω) := rfl
      _ = (shift F)^[sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)]
            ((shift F)^[sieveSpan F k j ω] ω) := by rw [ih]
      _ = (shift F)^[sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) +
            sieveSpan F k j ω] ω :=
          (Function.iterate_add_apply (shift F)
            (sieveReturnTime F k ((inducedSieveShift F k)^[j] ω))
            (sieveSpan F k j ω) ω).symm
      _ = (shift F)^[sieveSpan F k j ω +
            sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)] ω := by
          rw [add_comm]
      _ = (shift F)^[sieveSpan F k (j + 1) ω] ω := by
          rw [sieveSpan_succ]

theorem ae_frequently_mem_survival (F : AdmissibleFamily) :
    ∀ᵐ ω ∂productMeasure F,
      ∃ᶠ n in atTop, (shift F)^[n] ω ∈ survival F := by
  filter_upwards [
    (shift_conservative F).ae_forall_image_mem_imp_frequently_image_mem
      (survival_measurable F).nullMeasurableSet,
    firstHitTime_ae_finite F] with ω hfreq hhit
  obtain ⟨k, hk⟩ := hhit
  exact hfreq k hk

theorem returnTime_eq_sieve_of_agree (F : AdmissibleFamily) (k : ℕ)
    (ω : ResidueSpace F) (X : ℕ)
    (h : ∀ t, 0 < t → t ≤ X →
      ((shift F)^[t] ω ∈ survival F ↔
        (shift F)^[t] ω ∈ survivalFin F k))
    (hhit : {t : ℕ | 0 < t ∧ (shift F)^[t] ω ∈ survival F}.Nonempty) :
    (returnTime F ω ≤ X ↔ sieveReturnTime F k ω ≤ X) ∧
      (returnTime F ω ≤ X → returnTime F ω = sieveReturnTime F k ω) := by
  have hret := returnTime_spec (F := F) hhit
  have hgpos := returnTime_pos F ω
  have hσpos := sieveReturnTime_pos F k ω
  have hsle : sieveReturnTime F k ω ≤ returnTime F ω := by
    have hFin : (shift F)^[returnTime F ω] ω ∈ survivalFin F k :=
      survival_subset_survivalFin F k hret.1
    exact Nat.find_min' (exists_pos_cylinderHit F k ω)
      ⟨hgpos, (shift_iterate_mem_survivalFin F k (returnTime F ω) ω).mp hFin⟩
  have hhitS : sieveReturnTime F k ω ∈
      {t : ℕ | 0 < t ∧ (shift F)^[t] ω ∈ survival F} →
        returnTime F ω ≤ sieveReturnTime F k ω := by
    intro hmem
    have hdef : returnTime F ω =
        sInf {t : ℕ | 0 < t ∧ (shift F)^[t] ω ∈ survival F} :=
      dif_pos hhit
    rw [hdef]
    exact Nat.sInf_le hmem
  constructor
  · constructor
    · intro hB
      exact hsle.trans hB
    · intro hS
      have hFin : (shift F)^[sieveReturnTime F k ω] ω ∈ survivalFin F k :=
        (shift_iterate_mem_survivalFin F k (sieveReturnTime F k ω) ω).mpr
          (sieveReturnTime_spec F k ω).1
      have hA : (shift F)^[sieveReturnTime F k ω] ω ∈ survival F :=
        (h (sieveReturnTime F k ω) hσpos hS).mpr hFin
      exact (hhitS ⟨hσpos, hA⟩).trans hS
  · intro hB
    apply le_antisymm
    · have hS : sieveReturnTime F k ω ≤ X := hsle.trans hB
      have hFin : (shift F)^[sieveReturnTime F k ω] ω ∈ survivalFin F k :=
        (shift_iterate_mem_survivalFin F k (sieveReturnTime F k ω) ω).mpr
          (sieveReturnTime_spec F k ω).1
      have hA : (shift F)^[sieveReturnTime F k ω] ω ∈ survival F :=
        (h (sieveReturnTime F k ω) hσpos hS).mpr hFin
      exact hhitS ⟨hσpos, hA⟩
    · exact hsle

theorem not_mem_haarMismatch_iff (F : AdmissibleFamily) (k H : ℕ)
    (ω : ResidueSpace F) :
    ω ∉ haarMismatch F k H ↔
      ∀ t ≤ H,
        ((shift F)^[t] ω ∈ survival F ↔
          (shift F)^[t] ω ∈ survivalFin F k) := by
  constructor
  · intro hmis t ht
    constructor
    · intro hA
      exact survival_subset_survivalFin F k hA
    · intro hFin
      by_contra hnot
      exact hmis ⟨t, ht, ⟨hFin, hnot⟩⟩
  · intro h ⟨t, ht, hmem⟩
    exact hmem.2 ((h t ht).mpr hmem.1)

theorem frequently_hit_after (F : AdmissibleFamily) {ω : ResidueSpace F}
    (hfreq : ∃ᶠ n in atTop, (shift F)^[n] ω ∈ survival F) (T : ℕ) :
    {t : ℕ | 0 < t ∧ (shift F)^[t] ((shift F)^[T] ω) ∈ survival F}.Nonempty := by
  obtain ⟨n, hn, hmem⟩ := (frequently_atTop.mp hfreq) (T + 1)
  refine ⟨n - T, Nat.sub_pos_of_lt (Nat.lt_of_succ_le hn), ?_⟩
  have hadd : n - T + T = n := Nat.sub_add_cancel (Nat.le_of_succ_le hn)
  rw [← Function.iterate_add_apply, hadd]
  exact hmem

theorem inducedShift_iterate_eq_sieve_of_agree (F : AdmissibleFamily)
    (k : ℕ) (ω : ResidueSpace F) (H j : ℕ)
    (h : ∀ t, 0 < t → t ≤ H →
      ((shift F)^[t] ω ∈ survival F ↔
        (shift F)^[t] ω ∈ survivalFin F k))
    (hfreq : ∃ᶠ n in atTop, (shift F)^[n] ω ∈ survival F)
    (hle : modelSpan F j ω ≤ H) :
    (inducedShift F)^[j] ω = (inducedSieveShift F k)^[j] ω ∧
      modelSpan F j ω = sieveSpan F k j ω := by
  induction j with
  | zero => simp [modelSpan, sieveSpan]
  | succ j ih =>
    have hprev : modelSpan F j ω ≤ H :=
      (modelSpan_mono F (Nat.le_succ j) ω).trans hle
    obtain ⟨heq, hspan⟩ := ih hprev
    set T := modelSpan F j ω
    have hT : T ≤ H := hprev
    have hhit' := frequently_hit_after F hfreq T
    rw [← inducedShift_iterate_eq_shift_span] at hhit'
    have h' : ∀ t, 0 < t → t ≤ H - T →
        ((shift F)^[t] ((inducedShift F)^[j] ω) ∈ survival F ↔
          (shift F)^[t] ((inducedShift F)^[j] ω) ∈ survivalFin F k) := by
      intro t ht htX
      have htuH : T + t ≤ H := by
        rw [add_comm]
        exact (Nat.le_sub_iff_add_le hT).mp htX
      have htpos : 0 < T + t := Nat.add_pos_right T ht
      have horig := h (T + t) htpos htuH
      have hadd : (shift F)^[t] ((inducedShift F)^[j] ω) =
          (shift F)^[t + T] ω := by
        rw [inducedShift_iterate_eq_shift_span, ← Function.iterate_add_apply]
      simpa [hadd, add_comm t T] using horig
    have hsum := modelSpan_succ F j ω
    have hRTle : returnTime F ((inducedShift F)^[j] ω) ≤ H - T := by
      have : T + returnTime F ((inducedShift F)^[j] ω) ≤ H := by
        rwa [← hsum]
      exact (Nat.le_sub_iff_add_le hT).mpr (by simpa [add_comm] using this)
    have hRT :=
      returnTime_eq_sieve_of_agree F k ((inducedShift F)^[j] ω) (H - T) h' hhit'
    have hRTeq := hRT.2 hRTle
    constructor
    · calc
        (inducedShift F)^[j + 1] ω
            = inducedShift F ((inducedShift F)^[j] ω) :=
              Function.iterate_succ_apply' (inducedShift F) j ω
        _ = (shift F)^[returnTime F ((inducedShift F)^[j] ω)]
              ((inducedShift F)^[j] ω) := rfl
        _ = (shift F)^[sieveReturnTime F k ((inducedShift F)^[j] ω)]
              ((inducedShift F)^[j] ω) := by rw [hRTeq]
        _ = (shift F)^[sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)]
              ((inducedSieveShift F k)^[j] ω) := by rw [heq]
        _ = inducedSieveShift F k ((inducedSieveShift F k)^[j] ω) := rfl
        _ = (inducedSieveShift F k)^[j + 1] ω :=
            (Function.iterate_succ_apply' (inducedSieveShift F k) j ω).symm
    · calc
        modelSpan F (j + 1) ω
            = modelSpan F j ω +
                returnTime F ((inducedShift F)^[j] ω) :=
              modelSpan_succ F j ω
        _ = sieveSpan F k j ω +
              sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) := by
            rw [hRTeq, heq]
            exact congrArg (fun n =>
                n + sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)) hspan
        _ = sieveSpan F k (j + 1) ω :=
            (sieveSpan_succ F k j ω).symm

theorem inducedSieveShift_iterate_eq_of_agree (F : AdmissibleFamily)
    (k : ℕ) (ω : ResidueSpace F) (H j : ℕ)
    (h : ∀ t, 0 < t → t ≤ H →
      ((shift F)^[t] ω ∈ survival F ↔
        (shift F)^[t] ω ∈ survivalFin F k))
    (hfreq : ∃ᶠ n in atTop, (shift F)^[n] ω ∈ survival F)
    (hle : sieveSpan F k j ω ≤ H) :
    (inducedShift F)^[j] ω = (inducedSieveShift F k)^[j] ω ∧
      modelSpan F j ω = sieveSpan F k j ω := by
  induction j with
  | zero => simp [modelSpan, sieveSpan]
  | succ j ih =>
    have hprev : sieveSpan F k j ω ≤ H :=
      (sieveSpan_mono F k (Nat.le_succ j) ω).trans hle
    obtain ⟨heq, hspan⟩ := ih hprev
    set T := sieveSpan F k j ω
    have hT : T ≤ H := hprev
    have hhit' := frequently_hit_after F hfreq T
    rw [← inducedSieveShift_iterate_eq_shift_span, ← heq] at hhit'
    have h' : ∀ t, 0 < t → t ≤ H - T →
        ((shift F)^[t] ((inducedShift F)^[j] ω) ∈ survival F ↔
          (shift F)^[t] ((inducedShift F)^[j] ω) ∈ survivalFin F k) := by
      intro t ht htX
      have htuH : T + t ≤ H := by
        rw [add_comm]
        exact (Nat.le_sub_iff_add_le hT).mp htX
      have htpos : 0 < T + t := Nat.add_pos_right T ht
      have horig := h (T + t) htpos htuH
      have hadd : (shift F)^[t] ((inducedShift F)^[j] ω) =
          (shift F)^[t + T] ω := by
        rw [heq, inducedSieveShift_iterate_eq_shift_span,
          ← Function.iterate_add_apply]
      simpa [hadd, add_comm t T] using horig
    have hsum := sieveSpan_succ F k j ω
    have hSle : sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) ≤ H - T := by
      have : T + sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) ≤ H := by
        rwa [← hsum]
      exact (Nat.le_sub_iff_add_le hT).mpr (by simpa [add_comm] using this)
    rw [← heq] at hSle
    have hRT :=
      returnTime_eq_sieve_of_agree F k ((inducedShift F)^[j] ω) (H - T) h' hhit'
    have hRTle : returnTime F ((inducedShift F)^[j] ω) ≤ H - T :=
      hRT.1.mpr hSle
    have hRTeq := hRT.2 hRTle
    constructor
    · calc
        (inducedShift F)^[j + 1] ω
            = inducedShift F ((inducedShift F)^[j] ω) :=
              Function.iterate_succ_apply' (inducedShift F) j ω
        _ = (shift F)^[returnTime F ((inducedShift F)^[j] ω)]
              ((inducedShift F)^[j] ω) := rfl
        _ = (shift F)^[sieveReturnTime F k ((inducedShift F)^[j] ω)]
              ((inducedShift F)^[j] ω) := by rw [hRTeq]
        _ = (shift F)^[sieveReturnTime F k ((inducedSieveShift F k)^[j] ω)]
              ((inducedSieveShift F k)^[j] ω) := by rw [heq]
        _ = inducedSieveShift F k ((inducedSieveShift F k)^[j] ω) := rfl
        _ = (inducedSieveShift F k)^[j + 1] ω :=
            (Function.iterate_succ_apply' (inducedSieveShift F k) j ω).symm
    · calc
        modelSpan F (j + 1) ω
            = modelSpan F j ω +
                returnTime F ((inducedShift F)^[j] ω) :=
              modelSpan_succ F j ω
        _ = sieveSpan F k j ω +
              sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) := by
            rw [hRTeq, heq, hspan]
        _ = sieveSpan F k (j + 1) ω :=
            (sieveSpan_succ F k j ω).symm

theorem truncTestWindowModel_eq_sieve_of_agree (F : AdmissibleFamily)
    (k b J H : ℕ) (f : ℝ → ℝ) (ω : ResidueSpace F)
    (h : ∀ t ≤ H,
      ((shift F)^[t] ω ∈ survival F ↔
        (shift F)^[t] ω ∈ survivalFin F k))
    (hfreq : ∃ᶠ n in atTop, (shift F)^[n] ω ∈ survival F) :
    truncTestWindowModel F b J H f ω =
      truncTestWindowSieveModel F k b J H f ω := by
  unfold truncTestWindowModel truncTestWindowSieveModel
  have h0 := h 0 (Nat.zero_le H)
  simp only [Function.iterate_zero_apply] at h0
  rw [h0]
  have hpos : ∀ t, 0 < t → t ≤ H →
      ((shift F)^[t] ω ∈ survival F ↔
        (shift F)^[t] ω ∈ survivalFin F k) :=
    fun t _ htH => h t htH
  by_cases hA : ω ∈ survival F
  · have hA' : ω ∈ survivalFin F k := h0.mp hA
    simp only [hA, hA', ite_true]
    have hiff : modelSpan F J ω ≤ H ↔ sieveSpan F k J ω ≤ H := by
      constructor
      · intro hle
        have hagr :=
          inducedShift_iterate_eq_sieve_of_agree F k ω H J hpos hfreq hle
        simpa [hagr.2] using hle
      · intro hle
        have hagr :=
          inducedSieveShift_iterate_eq_of_agree F k ω H J hpos hfreq hle
        simpa [hagr.2] using hle
    simp only [hiff]
    by_cases hsp : sieveSpan F k J ω ≤ H
    · simp only [hsp, ite_true]
      congr 1
      unfold modelTrunc sieveTrunc
      refine sum_congr rfl fun j hj => ?_
      have hjJ : j + 1 ≤ J := Nat.succ_le_of_lt (mem_range.mp hj)
      have hBspan : modelSpan F J ω ≤ H := hiff.mpr hsp
      have hlej : modelSpan F j ω ≤ H :=
        (modelSpan_mono F (mem_range.mp hj).le ω).trans hBspan
      have hlej1 : modelSpan F (j + 1) ω ≤ H :=
        (modelSpan_mono F hjJ ω).trans hBspan
      have heqj :=
        inducedShift_iterate_eq_sieve_of_agree F k ω H j hpos hfreq hlej
      have heqj1 :=
        inducedShift_iterate_eq_sieve_of_agree F k ω H (j + 1) hpos hfreq hlej1
      have hms := modelSpan_succ F j ω
      have hss := sieveSpan_succ F k j ω
      have hret :
          returnTime F ((inducedShift F)^[j] ω) =
            sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) := by
        apply Nat.add_left_cancel (n := modelSpan F j ω)
        calc
          modelSpan F j ω + returnTime F ((inducedShift F)^[j] ω) =
              modelSpan F (j + 1) ω := hms.symm
          _ = sieveSpan F k (j + 1) ω := heqj1.2
          _ = sieveSpan F k j ω +
                sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) := hss
          _ = modelSpan F j ω +
                sieveReturnTime F k ((inducedSieveShift F k)^[j] ω) := by
            rw [heqj.2]
      rw [hret]
    · simp only [hsp, ite_false]
  · have hnot : ω ∉ survivalFin F k := fun hS => hA (h0.mpr hS)
    simp only [hA, hnot, ite_false]

theorem abs_windowModel_sub_sieveModel_le {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M)
    (ω : ResidueSpace F) :
    |truncTestWindowModel F b J H f ω -
        truncTestWindowSieveModel F k b J H f ω| ≤ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have h1 := abs_truncTestWindowModel_le F b J H hbdd ω
  have h2 := abs_truncTestWindowSieveModel_le F k b J H hbdd ω
  have htri :
      |truncTestWindowModel F b J H f ω -
          truncTestWindowSieveModel F k b J H f ω| ≤
        |truncTestWindowModel F b J H f ω| +
          |truncTestWindowSieveModel F k b J H f ω| := by
    have hnorm :=
      norm_add_le (truncTestWindowModel F b J H f ω)
        (-truncTestWindowSieveModel F k b J H f ω)
    simpa [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using hnorm
  exact htri.trans (by linarith)

theorem abs_integral_window_sub_sieve {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    |∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F -
        ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| ≤
      2 * M * (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hw := integrable_truncTestWindowModel F b J H hf hbdd
  have hs := integrable_truncTestWindowSieveModel F k b J H hf hbdd
  have hsub := hw.sub hs
  have habs : Integrable
      (fun ω =>
        |truncTestWindowModel F b J H f ω -
          truncTestWindowSieveModel F k b J H f ω|)
      (productMeasure F) := by
    simpa [Real.norm_eq_abs] using hsub.norm
  have hInd :
      Integrable
        (fun ω => (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω)
        (productMeasure F) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_haarMismatch F k H)
  have hbound : Integrable
      (fun ω =>
        2 * M * (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω)
      (productMeasure F) :=
    hInd.const_mul (2 * M)
  have hpt :
      (fun ω =>
          |truncTestWindowModel F b J H f ω -
            truncTestWindowSieveModel F k b J H f ω|)
        ≤ᵐ[productMeasure F]
      fun ω =>
        2 * M *
          (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_frequently_mem_survival F] with ω hfreq
    by_cases hmis : ω ∈ haarMismatch F k H
    · have htri := abs_windowModel_sub_sieveModel_le F k b J H hbdd ω
      have hind : (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω = 1 :=
        Set.indicator_of_mem hmis (fun _ => (1 : ℝ))
      simpa [hind] using htri
    · have heq :=
        truncTestWindowModel_eq_sieve_of_agree F k b J H f ω
          ((not_mem_haarMismatch_iff F k H ω).mp hmis) hfreq
      have hind : (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω = 0 :=
        Set.indicator_of_notMem hmis (fun _ => (1 : ℝ))
      simpa [heq, hind]
  have hinter := integral_mono_ae habs hbound hpt
  have hmul :
      ∫ ω,
          2 * M * (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω
          ∂productMeasure F =
        2 * M * (productMeasure F).real (haarMismatch F k H) := by
    rw [integral_const_mul (2 * M)]
    have hind1 :
        (fun ω => (haarMismatch F k H).indicator (fun _ => (1 : ℝ)) ω) =
          (haarMismatch F k H).indicator (1 : ResidueSpace F → ℝ) :=
      rfl
    rw [hind1, integral_indicator_one (measurableSet_haarMismatch F k H)]
  have hdiff :
      |∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F -
          ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| =
        |∫ ω,
            truncTestWindowModel F b J H f ω -
              truncTestWindowSieveModel F k b J H f ω
            ∂productMeasure F| := by
    rw [integral_sub hw hs]
  have hnorm :
      |∫ ω,
          truncTestWindowModel F b J H f ω -
            truncTestWindowSieveModel F k b J H f ω
          ∂productMeasure F| ≤
        ∫ ω,
          |truncTestWindowModel F b J H f ω -
            truncTestWindowSieveModel F k b J H f ω|
          ∂productMeasure F := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun ω =>
          truncTestWindowModel F b J H f ω -
            truncTestWindowSieveModel F k b J H f ω)
  have hmis := measure_haarMismatch_le F k H
  calc
    |∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F -
        ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F|
        = |∫ ω,
            truncTestWindowModel F b J H f ω -
              truncTestWindowSieveModel F k b J H f ω
            ∂productMeasure F| := hdiff
    _ ≤ ∫ ω,
          |truncTestWindowModel F b J H f ω -
            truncTestWindowSieveModel F k b J H f ω|
          ∂productMeasure F := hnorm
    _ ≤ 2 * M * (productMeasure F).real (haarMismatch F k H) := by
        rwa [← hmul]
    _ ≤ 2 * M * ((H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k)) :=
        mul_le_mul_of_nonneg_left hmis (mul_nonneg (by norm_num) hM)
    _ = 2 * M * (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
        ring

theorem cesaro_window_sub_sieve_le {M : ℝ} (F : AdmissibleFamily)
    (k b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) {X : ℕ}
    (hX : 1 ≤ X) :
    |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
        (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| ≤
      2 * M * (H + 1 : ℝ) * ((X : ℝ) + H) / X *
        ∑' i, (1 : ℝ) / F.d (i + k) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  set τ : ℝ := ∑' i, (1 : ℝ) / F.d (i + k)
  have hsum :
      |∑ n ∈ Icc 1 X,
            (truncTestWindow F b J H f n -
              truncTestWindowSieve F k b J H f n)| ≤
        ∑ n ∈ Icc 1 X,
          |truncTestWindow F b J H f n -
            truncTestWindowSieve F k b J H f n| :=
    abs_sum_le_sum_abs _ _
  have hle := sum_abs_window_sub_sieve F k b J H hbdd X
  have hcard := mismatch_window_card F k X H
  set τ : ℝ := ∑' i, (1 : ℝ) / F.d (i + k)
  have hτ : 0 ≤ τ := tsum_nonneg fun i => one_div_d_nonneg F (i + k)
  have hnum :
      |∑ n ∈ Icc 1 X,
            (truncTestWindow F b J H f n -
              truncTestWindowSieve F k b J H f n)| ≤
        2 * M * (H + 1 : ℝ) * (X + H : ℝ) * τ :=
    hsum.trans (hle.trans (by
      have h2M : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
      have := mul_le_mul_of_nonneg_left hcard h2M
      convert this using 1
      ring))
  have hdiv :
      |∑ n ∈ Icc 1 X,
            (truncTestWindow F b J H f n -
              truncTestWindowSieve F k b J H f n)| / (X : ℝ) ≤
        2 * M * (H + 1 : ℝ) * (X + H : ℝ) / X * τ := by
    have := div_le_div_of_nonneg_right hnum hXpos.le
    have hassoc :
        (2 * M * (H + 1 : ℝ) * (X + H : ℝ) * τ) / (X : ℝ) =
          2 * M * (H + 1 : ℝ) * (X + H : ℝ) / X * τ := by
      ring
    rwa [hassoc] at this
  have hform :
      |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
          (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| =
        |∑ n ∈ Icc 1 X,
            (truncTestWindow F b J H f n -
              truncTestWindowSieve F k b J H f n)| / (X : ℝ) := by
    rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hXpos]
  rw [hform]
  exact hdiv

/-- Physical Cesàro of the BFree window tends to Haar of `truncTestWindowModel`.
Paper (19): `X → ∞`, then `k → ∞` with `τ_k → 0`. -/
theorem tendsto_cesaro_truncTestWindow (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Tendsto (fun X : ℕ =>
        (∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ))
      atTop
      (𝓝 (∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F)) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C : ℝ := 6 * M * (H + 1 : ℝ)
  have hC0 : 0 ≤ C :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (by positivity)
  have hτ := tendsto_tsum_tail_one_div_d F
  rw [Metric.tendsto_atTop] at hτ
  obtain ⟨k0, hk0⟩ := hτ ((ε / 2) / (C + 1)) (by positivity)
  let k := k0
  have hτk : 0 ≤ ∑' i, (1 : ℝ) / F.d (i + k) :=
    tsum_nonneg fun i => one_div_d_nonneg F (i + k)
  have hτabs : ∑' i, (1 : ℝ) / F.d (i + k) < (ε / 2) / (C + 1) := by
    have hdist := hk0 k (le_rfl)
    have habs : |∑' i, (1 : ℝ) / F.d (i + k)| < (ε / 2) / (C + 1) := by
      simpa [Real.dist_eq] using hdist
    rwa [abs_of_nonneg hτk] at habs
  have hCτ : C * ∑' i, (1 : ℝ) / F.d (i + k) ≤ ε / 2 := by
    have hden : 0 < C + 1 := by linarith
    have hle : ∑' i, (1 : ℝ) / F.d (i + k) ≤ (ε / 2) / (C + 1) := hτabs.le
    have hmul : C * ∑' i, (1 : ℝ) / F.d (i + k) ≤
        C * ((ε / 2) / (C + 1)) :=
      mul_le_mul_of_nonneg_left hle hC0
    have hfrac : C * ((ε / 2) / (C + 1)) = (C / (C + 1)) * (ε / 2) := by
      field_simp [hden.ne']
    have hC1 : C / (C + 1) ≤ 1 :=
      (div_le_one hden).2 (by linarith)
    have hposε : 0 ≤ ε / 2 := by linarith
    have hle' : (C / (C + 1)) * (ε / 2) ≤ 1 * (ε / 2) :=
      mul_le_mul_of_nonneg_right hC1 hposε
    linarith
  have hsieve := tendsto_cesaro_truncTestWindowSieve F k b J H hf hbdd
  have hhaar := abs_integral_window_sub_sieve F k b J H hf hbdd
  rw [Metric.tendsto_atTop] at hsieve
  obtain ⟨N0, hN0⟩ := hsieve (ε / 2) (by linarith)
  refine ⟨max N0 (max H 1), fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right H 1) (le_trans (le_max_right N0 _) hX)
  have hXH : H ≤ X := le_trans (le_max_left H 1) (le_trans (le_max_right N0 _) hX)
  have hXN : N0 ≤ X := le_trans (le_max_left N0 _) hX
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX1
  have hsieveX := hN0 X hXN
  have hphys := cesaro_window_sub_sieve_le F k b J H hbdd hX1
  have hHX : ((X : ℝ) + H) / X ≤ 2 := by
    have : (H : ℝ) / X ≤ 1 :=
      div_le_one_of_le₀ (Nat.cast_le.mpr hXH) hXpos.le
    have hrew : ((X : ℝ) + H) / X = 1 + (H : ℝ) / X := by
      field_simp [hXpos.ne']
    linarith
  have hphys' :
      |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
          (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| ≤
        4 * M * (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
    have h2M : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
    have hH1 : 0 ≤ (H + 1 : ℝ) := by positivity
    set τ : ℝ := ∑' i, (1 : ℝ) / F.d (i + k)
    have hcoeff : 0 ≤ 2 * M * (H + 1 : ℝ) * τ :=
      mul_nonneg (mul_nonneg h2M hH1) hτk
    have hstep :
        2 * M * (H + 1 : ℝ) * ((X : ℝ) + H) / X * τ ≤
          (2 * M * (H + 1 : ℝ) * τ) * 2 := by
      have hassoc :
          2 * M * (H + 1 : ℝ) * ((X : ℝ) + H) / X * τ =
            (2 * M * (H + 1 : ℝ) * τ) * (((X : ℝ) + H) / X) := by
        ring
      rw [hassoc]
      exact mul_le_mul_of_nonneg_left hHX hcoeff
    have h4 : (2 * M * (H + 1 : ℝ) * τ) * 2 =
        4 * M * (H + 1 : ℝ) * τ := by
      ring
    rw [← h4]
    exact hphys.trans hstep
  have hhaar' :
      |∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
          ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F| ≤
        2 * M * (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) := by
    simpa [abs_sub_comm] using hhaar
  have hmis :
      4 * M * (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) +
          2 * M * (H + 1 : ℝ) * ∑' i, (1 : ℝ) / F.d (i + k) ≤
        C * ∑' i, (1 : ℝ) / F.d (i + k) := by
    unfold C
    linarith
  have htri :
      |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
          ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F| ≤
        |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
            (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| +
          |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
              ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| +
          |∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
              ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F| := by
    have hrew :
        ((∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
            ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F) =
          ((∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
              (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)) +
            ((∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
              ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F) := by
      ring
    have hrew2 :
        ((∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
            ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F) =
          ((∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
              ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F) +
            (∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
              ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F) := by
      ring
    calc
      |((∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
          ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F)|
          = |((∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
                (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)) +
              ((∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
                ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F)| := by
            rw [hrew]
      _ ≤ |((∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
              (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ))| +
            |((∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
                ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F)| :=
          abs_add_le _ _
      _ ≤ |((∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
              (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ))| +
            (|(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
                ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| +
              |∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
                  ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F|) :=
          add_le_add le_rfl (by rw [hrew2]; exact abs_add_le _ _)
      _ = _ := by ring
  rw [Real.dist_eq]
  have hsieveless :
      |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
          ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| <
        ε / 2 := by
    simpa [Real.dist_eq] using hsieveX
  have hsumerr :
      |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
          (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| +
        |∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
            ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F| ≤
        C * ∑' i, (1 : ℝ) / F.d (i + k) :=
    (add_le_add hphys' hhaar').trans hmis
  have hsplit :
      |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
          ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F| ≤
        C * ∑' i, (1 : ℝ) / F.d (i + k) +
          |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
              ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| := by
    have hrew :
        |(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
            (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| +
          |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
              ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| +
          |∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
              ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F| =
          (|(∑ n ∈ Icc 1 X, truncTestWindow F b J H f n) / (X : ℝ) -
              (∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ)| +
            |∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F -
                ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F|) +
            |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
                ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| := by
      ring
    exact htri.trans (hrew.trans_le (add_le_add hsumerr le_rfl))
  have hlt :
      C * ∑' i, (1 : ℝ) / F.d (i + k) +
          |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
              ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| <
        ε := by
    have : C * ∑' i, (1 : ℝ) / F.d (i + k) +
        |(∑ n ∈ Icc 1 X, truncTestWindowSieve F k b J H f n) / (X : ℝ) -
            ∫ ω, truncTestWindowSieveModel F k b J H f ω ∂productMeasure F| <
        ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hCτ hsieveless
    linarith
  exact hsplit.trans_lt hlt

theorem truncTestWindow_eq_zero_of_not_bfree (F : AdmissibleFamily)
    (b J H : ℕ) (f : ℝ → ℝ) {n : ℕ} (hn : ¬ BFree F n) :
    truncTestWindow F b J H f n = 0 := by
  unfold truncTestWindow
  simp [hn]

theorem filter_Icc_bfree_eq_image_enum (F : AdmissibleFamily) (N : ℕ) :
    (Icc 1 (enum F N)).filter (BFree F) = (range (N + 1)).image (enum F) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hI, hB⟩ := mem_filter.mp hn
    obtain ⟨h1, hN⟩ := mem_Icc.mp hI
    have hr : n ∈ Set.range (enum F) := by
      rw [range_enum]
      exact Set.mem_ofPred.mpr hB
    obtain ⟨k, rfl⟩ := Set.mem_range.mp hr
    refine mem_image.mpr ⟨k, ?_, rfl⟩
    exact mem_range.mpr (Nat.lt_succ_iff.mpr ((enum_strictMono F).le_iff_le.mp hN))
  · intro hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, enum_mem F k⟩
    · have : enum F 0 ≤ enum F k := (enum_strictMono F).monotone (Nat.zero_le k)
      simpa [enum_zero] using this
    · exact (enum_strictMono F).monotone hkN

theorem sum_truncTestWindow_Icc_enum (F : AdmissibleFamily)
    (b J H : ℕ) (f : ℝ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 (enum F N), truncTestWindow F b J H f n =
      ∑ k ∈ range (N + 1), truncTestWindow F b J H f (enum F k) := by
  have hsub := filter_subset (BFree F) (Icc 1 (enum F N))
  have hzero : ∑ n ∈ Icc 1 (enum F N), truncTestWindow F b J H f n =
      ∑ n ∈ (Icc 1 (enum F N)).filter (BFree F),
        truncTestWindow F b J H f n := by
    refine (sum_subset hsub fun n hn hnf => ?_).symm
    have hnot : ¬ BFree F n := fun hB => hnf (mem_filter.mpr ⟨hn, hB⟩)
    exact truncTestWindow_eq_zero_of_not_bfree F b J H f hnot
  rw [hzero, filter_Icc_bfree_eq_image_enum]
  exact sum_image fun a _ b _ h => (enum_strictMono F).injective h

theorem integrable_truncTestWindowModel_root {M : ℝ} (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Integrable (truncTestWindowModel F b J H f) (rootMeasure F) :=
  (integrable_const M).mono'
    (measurable_truncTestWindowModel F b J H hf).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_truncTestWindowModel_le F b J H hbdd ω)

theorem truncTestWindowModel_eq_indicator (F : AdmissibleFamily)
    (b J H : ℕ) (f : ℝ → ℝ) :
    truncTestWindowModel F b J H f =
      (survival F).indicator (truncTestWindowModel F b J H f) := by
  funext ω
  by_cases h : ω ∈ survival F
  · rw [Set.indicator_of_mem h]
  · have hz : truncTestWindowModel F b J H f ω = 0 := by
      unfold truncTestWindowModel
      simp [h]
    rw [Set.indicator_of_notMem h, hz]

theorem integral_truncTestWindowModel_mul_rho (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F =
      rho F * ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F := by
  have hA := survival_measurable F
  have hind := truncTestWindowModel_eq_indicator F b J H f
  have hμ :
      ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F =
        ∫ ω in survival F, truncTestWindowModel F b J H f ω
          ∂productMeasure F := by
    conv_lhs => rw [hind]
    exact integral_indicator hA
  have hroot :
      ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F =
        ((productMeasure F) (survival F))⁻¹.toReal *
          ∫ ω in survival F, truncTestWindowModel F b J H f ω
            ∂productMeasure F := by
    unfold rootMeasure ProbabilityTheory.cond
    rw [integral_smul_measure]
    rfl
  have hinv : ((productMeasure F) (survival F))⁻¹.toReal = (rho F)⁻¹ := by
    rw [measure_survival, ENNReal.toReal_inv, ENNReal.toReal_ofReal (rho_pos F).le]
  have hρ : rho F ≠ 0 := (rho_pos F).ne'
  rw [hμ, hroot, hinv, ← mul_assoc, mul_inv_cancel₀ hρ, one_mul]

theorem enum_pos (F : AdmissibleFamily) (n : ℕ) : 0 < enum F n :=
  lt_of_lt_of_le (Nat.succ_pos n) (enum_ge_add_one F n)

/-- Palm (21) along `enum`: Cesàro of the physical window on BFree points
equals Haar on `rootMeasure`. No Birkhoff genericity of a model point. -/
theorem tendsto_cesaro_truncTestWindow_enum (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N)
      atTop
      (𝓝 (∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F)) := by
  have hphys :=
    (tendsto_cesaro_truncTestWindow F b J H hf hbdd).comp
      (enum_strictMono F).tendsto_atTop
  have hratio := tendsto_enum_div_n F
  have hmul := hratio.mul hphys
  have hident :
      (rho F)⁻¹ *
          ∫ ω, truncTestWindowModel F b J H f ω ∂productMeasure F =
        ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F := by
    have h := integral_truncTestWindowModel_mul_rho F b J H hf hbdd
    rw [h, ← mul_assoc, inv_mul_cancel₀ (rho_pos F).ne', one_mul]
  have hfun :
      (fun N : ℕ =>
        (∑ k ∈ range (N + 1), truncTestWindow F b J H f (enum F k)) /
          (N + 1 : ℝ)) =
        fun N =>
          ((enum F N : ℝ) / (N + 1)) *
            ((∑ n ∈ Icc 1 (enum F N), truncTestWindow F b J H f n) /
              (enum F N : ℝ)) := by
    funext N
    have hpos : (enum F N : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (enum_pos F N)).ne'
    rw [sum_truncTestWindow_Icc_enum]
    field_simp [hpos]
  have ht :
      Tendsto (fun N : ℕ =>
        (∑ k ∈ range (N + 1), truncTestWindow F b J H f (enum F k)) /
          ((N + 1 : ℕ) : ℝ))
        atTop
        (𝓝 (∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F)) := by
    have hfun' :
        (fun N : ℕ =>
          (∑ k ∈ range (N + 1), truncTestWindow F b J H f (enum F k)) /
            ((N + 1 : ℕ) : ℝ)) =
          fun N =>
            (∑ k ∈ range (N + 1), truncTestWindow F b J H f (enum F k)) /
              (N + 1 : ℝ) := by
      funext N
      rw [Nat.cast_succ]
    rw [hfun', hfun, ← hident]
    exact hmul
  exact (tendsto_add_atTop_iff_nat 1).mp ht

theorem sum_enum_span (F : AdmissibleFamily) (J N : ℕ) :
    ∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k) =
      ∑ j ∈ range J, ((enum F (N + j) : ℝ) - enum F j) := by
  have htel : ∀ k,
      ((enum F (k + J) : ℝ) - enum F k) =
        ∑ j ∈ range J, (gap (enum F) (k + j) : ℝ) := by
    intro k
    have h := sum_gap_enum F k J
    have hidx :
        ∑ n ∈ range J, (gap (enum F) (n + k) : ℝ) =
          ∑ n ∈ range J, (gap (enum F) (k + n) : ℝ) :=
      sum_congr rfl fun n _ => by rw [add_comm]
    rw [← hidx, h, add_comm J k]
  simp_rw [htel]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simpa [add_comm j] using sum_gap_enum F j N

theorem tendsto_cesaro_span_enum (F : AdmissibleFamily) (J : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k)) / N)
      atTop (𝓝 ((J : ℝ) * (rho F)⁻¹)) := by
  have hfun :
      (fun N : ℕ =>
        (∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k)) / N) =
        fun N =>
          ∑ j ∈ range J, ((enum F (N + j) : ℝ) - enum F j) / N := by
    funext N
    rw [sum_enum_span, div_eq_inv_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [div_eq_inv_mul]
  have hterm : ∀ j,
      Tendsto (fun N : ℕ => ((enum F (N + j) : ℝ) - enum F j) / N)
        atTop (𝓝 (rho F)⁻¹) := fun j => by
    have h :=
      (tendsto_enum_add_div_nat F j).sub
        (tendsto_const_div_atTop_nhds_zero_nat (enum F j : ℝ))
    rw [sub_zero] at h
    exact h.congr fun N => (sub_div _ _ _).symm
  have ht : ∀ J' : ℕ,
      Tendsto (fun N : ℕ =>
          ∑ j ∈ range J', ((enum F (N + j) : ℝ) - enum F j) / N)
        atTop (𝓝 ((J' : ℝ) * (rho F)⁻¹)) := by
    intro J'
    induction J' with
    | zero =>
      simpa using tendsto_const_nhds (x := (0 : ℝ))
    | succ J' ih =>
      simp only [sum_range_succ]
      have hsum := ih.add (hterm J')
      have hlim : (J' : ℝ) * (rho F)⁻¹ + (rho F)⁻¹ =
          ((J' + 1 : ℕ) : ℝ) * (rho F)⁻¹ := by
        rw [Nat.cast_succ]
        ring
      rwa [hlim] at hsum
  rw [hfun]
  exact ht J

theorem card_enum_span_gt_le (F : AdmissibleFamily) (J H N : ℕ) :
    (H + 1 : ℝ) *
        (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) ≤
      ∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k) := by
  have hpt : ∀ k ∈ range N,
      (H + 1 : ℝ) *
          (if H < enum F (k + J) - enum F k then (1 : ℝ) else 0) ≤
        (enum F (k + J) : ℝ) - enum F k := by
    intro k hk
    have hle : enum F k ≤ enum F (k + J) :=
      (enum_strictMono F).monotone (Nat.le_add_right _ _)
    by_cases hgt : H < enum F (k + J) - enum F k
    · simp only [hgt, ite_true, mul_one]
      have : (H + 1 : ℕ) ≤ enum F (k + J) - enum F k :=
        Nat.succ_le_iff.mpr hgt
      rw [← Nat.cast_sub hle, ← Nat.cast_succ]
      exact (Nat.cast_le (α := ℝ)).mpr this
    · simp only [hgt, ite_false, mul_zero]
      have : (0 : ℝ) ≤ (enum F (k + J) : ℝ) - enum F k := by
        rw [← Nat.cast_sub hle]
        exact Nat.cast_nonneg _
      exact this
  have hsum := sum_le_sum hpt
  have hmul :
      ∑ k ∈ range N,
          (H + 1 : ℝ) *
            (if H < enum F (k + J) - enum F k then (1 : ℝ) else 0) =
        (H + 1 : ℝ) *
          ∑ k ∈ range N,
            (if H < enum F (k + J) - enum F k then (1 : ℝ) else 0) :=
    (mul_sum _ _ _).symm
  have hcard :
      ∑ k ∈ range N,
          (if H < enum F (k + J) - enum F k then (1 : ℝ) else 0) =
        (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) := by
    let p : ℕ → Prop := fun k => H < enum F (k + J) - enum F k
    change ∑ k ∈ range N, (if p k then (1 : ℝ) else 0) =
      (#{k ∈ range N | p k} : ℝ)
    rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
      mul_one, mul_zero, add_zero]
  rw [hmul, hcard] at hsum
  exact hsum

theorem abs_cesaro_trunc_sub_window_enum {M : ℝ} (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} (hbdd : ∀ x, |f x| ≤ M) (N : ℕ) :
    |(∑ k ∈ range N, f (canonicalGapTailTrunc F b J k)) / N -
        (∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N| ≤
      M * (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hpt : ∀ k ∈ range N,
      |f (canonicalGapTailTrunc F b J k) -
          truncTestWindow F b J H f (enum F k)| ≤
        M * (if H < enum F (k + J) - enum F k then (1 : ℝ) else 0) := by
    intro k hk
    have hw := truncTestWindow_enum F b J H f k
    have hle : enum F k ≤ enum F (k + J) :=
      (enum_strictMono F).monotone (Nat.le_add_right _ _)
    have hiff :
        enum F (k + J) ≤ enum F k + H ↔
          enum F (k + J) - enum F k ≤ H :=
      (Nat.sub_le_iff_le_add').symm
    by_cases hsp : enum F (k + J) ≤ enum F k + H
    · have hnot : ¬ H < enum F (k + J) - enum F k :=
        not_lt.mpr (hiff.mp hsp)
      rw [hw, if_pos hsp, sub_self, abs_zero]
      simp [hnot]
    · have hgt : H < enum F (k + J) - enum F k :=
        Nat.not_le.mp fun hle' => hsp (hiff.mpr hle')
      rw [hw, if_neg hsp, sub_zero]
      simpa [hgt] using hbdd _
  have hsum :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
  have hmul :
      ∑ k ∈ range N,
          M * (if H < enum F (k + J) - enum F k then (1 : ℝ) else 0) =
        M *
          (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) := by
    rw [← mul_sum]
    simp [sum_ite, sum_const, nsmul_eq_mul]
  have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg N)
  have hnum := hsum.trans (by rw [hmul])
  have hdiv := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg N)
  calc
    |(∑ k ∈ range N, f (canonicalGapTailTrunc F b J k)) / N -
          (∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N|
        = |∑ k ∈ range N,
              (f (canonicalGapTailTrunc F b J k) -
                truncTestWindow F b J H f (enum F k))| / N := by
          rw [← sub_div, ← sum_sub_distrib, abs_div, hNabs]
    _ ≤ M * (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N :=
        hdiv

theorem ae_mem_survival_rootMeasure (F : AdmissibleFamily) :
    ∀ᵐ ω ∂rootMeasure F, ω ∈ survival F := by
  rw [MeasureTheory.ae_iff]
  have hA : rootMeasure F (survival F) = 1 := measure_root_survival F
  have hcompl : rootMeasure F (survival F)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (survival_measurable F), hA, tsub_self]
  change rootMeasure F {ω | ω ∉ survival F} = 0
  convert hcompl
  ext ω
  simp

theorem integrable_test_modelTrunc {M : ℝ} (F : AdmissibleFamily)
    (b J : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Integrable (fun ω => f (modelTrunc F b J ω)) (rootMeasure F) :=
  (integrable_const M).mono'
    (hf.measurable.comp (measurable_modelTrunc F b J)).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hbdd _)

theorem measurableSet_modelSpan_gt (F : AdmissibleFamily) (J H : ℕ) :
    MeasurableSet {ω : ResidueSpace F | H < modelSpan F J ω} := by
  have hle : MeasurableSet {ω : ResidueSpace F | modelSpan F J ω ≤ H} :=
    (measurable_modelSpan F J)
      (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic H))
  have hset : {ω : ResidueSpace F | H < modelSpan F J ω} =
      {ω : ResidueSpace F | modelSpan F J ω ≤ H}ᶜ := by
    ext ω
    simp [not_le]
  rw [hset]
  exact hle.compl

theorem tendsto_measureReal_modelSpan_gt (F : AdmissibleFamily) (J : ℕ) :
    Tendsto (fun H : ℕ =>
      (rootMeasure F).real {ω | H < modelSpan F J ω}) atTop (𝓝 0) := by
  let s : ℕ → Set (ResidueSpace F) :=
    fun H => {ω | H < modelSpan F J ω}
  have hs : ∀ H, NullMeasurableSet (s H) (rootMeasure F) := fun H =>
    (measurableSet_modelSpan_gt F J H).nullMeasurableSet
  have hanti : Antitone s := by
    intro a b hab ω h
    exact lt_of_le_of_lt hab h
  have hinter : (⋂ H, s H) = ∅ := by
    ext ω
    simp only [s, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    intro h
    exact (lt_irrefl (modelSpan F J ω)) (h (modelSpan F J ω))
  have hlim :
      Tendsto (fun H : ℕ => rootMeasure F (s H)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hs hanti
      ⟨0, measure_ne_top _ _⟩
    have hinter0 : rootMeasure F (⋂ H, s H) = 0 := by
      rw [hinter, measure_empty]
    simpa [hinter0, Function.comp_def] using h
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hnhds : {x : ℝ≥0∞ | x < ENNReal.ofReal ε} ∈ 𝓝 (0 : ℝ≥0∞) :=
    Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨H0, hH0⟩ := eventually_atTop.mp (hlim.eventually hnhds)
  refine ⟨H0, fun H hH => ?_⟩
  have hlt : rootMeasure F (s H) < ENNReal.ofReal ε := hH0 H hH
  have habs :
      |(rootMeasure F).real (s H)| = (rootMeasure F).real (s H) :=
    abs_of_nonneg ENNReal.toReal_nonneg
  simpa [Real.dist_eq, Measure.real, habs] using
    ENNReal.toReal_lt_of_lt_ofReal hlt

theorem abs_integral_windowModel_sub_test {M : ℝ} (F : AdmissibleFamily)
    (b J H : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
        ∫ ω, f (modelTrunc F b J ω) ∂rootMeasure F| ≤
      M * (rootMeasure F).real {ω | H < modelSpan F J ω} := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hw := integrable_truncTestWindowModel_root F b J H hf hbdd
  have hfI := integrable_test_modelTrunc F b J hf hbdd
  have hsub := hw.sub hfI
  have habs : Integrable
      (fun ω =>
        |truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)|)
      (rootMeasure F) := by
    simpa [Real.norm_eq_abs] using hsub.norm
  have hInd : Integrable
      (fun ω =>
        ({ω | H < modelSpan F J ω} : Set (ResidueSpace F)).indicator
          (fun _ => (1 : ℝ)) ω)
      (rootMeasure F) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_modelSpan_gt F J H)
  have hbound : Integrable
      (fun ω =>
        M *
          ({ω | H < modelSpan F J ω} : Set (ResidueSpace F)).indicator
            (fun _ => (1 : ℝ)) ω)
      (rootMeasure F) :=
    hInd.const_mul M
  have hpt :
      (fun ω =>
          |truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)|)
        ≤ᵐ[rootMeasure F]
      fun ω =>
        M *
          ({ω | H < modelSpan F J ω} : Set (ResidueSpace F)).indicator
            (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_mem_survival_rootMeasure F] with ω hA
    unfold truncTestWindowModel
    simp only [hA, ite_true]
    by_cases hsp : modelSpan F J ω ≤ H
    · have hnot : ¬ H < modelSpan F J ω := not_lt.mpr hsp
      have hnotS : ω ∉ ({ω : ResidueSpace F | H < modelSpan F J ω}) := hnot
      simp only [hsp, ite_true, sub_self, abs_zero]
      rw [Set.indicator_of_notMem hnotS, mul_zero]
    · have hgt : H < modelSpan F J ω := Nat.not_le.mp hsp
      have hgtS : ω ∈ ({ω : ResidueSpace F | H < modelSpan F J ω}) := hgt
      simp only [hsp, ite_false]
      rw [Set.indicator_of_mem hgtS, mul_one]
      simpa [abs_sub_comm, sub_zero] using hbdd (modelTrunc F b J ω)
  have hinter := integral_mono_ae habs hbound hpt
  have hmul :
      ∫ ω,
          M *
            ({ω | H < modelSpan F J ω} : Set (ResidueSpace F)).indicator
              (fun _ => (1 : ℝ)) ω
          ∂rootMeasure F =
        M * (rootMeasure F).real {ω | H < modelSpan F J ω} := by
    rw [integral_const_mul M]
    have hind1 :
        (fun ω =>
          ({ω | H < modelSpan F J ω} : Set (ResidueSpace F)).indicator
            (fun _ => (1 : ℝ)) ω) =
          ({ω | H < modelSpan F J ω} : Set (ResidueSpace F)).indicator
            (1 : ResidueSpace F → ℝ) :=
      rfl
    rw [hind1, integral_indicator_one (measurableSet_modelSpan_gt F J H)]
  have hdiff :
      |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
          ∫ ω, f (modelTrunc F b J ω) ∂rootMeasure F| =
        |∫ ω,
            truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)
            ∂rootMeasure F| := by
    rw [integral_sub hw hfI]
  have hnorm :
      |∫ ω,
          truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)
          ∂rootMeasure F| ≤
        ∫ ω,
          |truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)|
          ∂rootMeasure F := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun ω =>
          truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω))
  calc
    |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
        ∫ ω, f (modelTrunc F b J ω) ∂rootMeasure F|
        = |∫ ω,
            truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)
            ∂rootMeasure F| := hdiff
    _ ≤ ∫ ω,
          |truncTestWindowModel F b J H f ω - f (modelTrunc F b J ω)|
          ∂rootMeasure F := hnorm
    _ ≤ M * (rootMeasure F).real {ω | H < modelSpan F J ω} := by
        rwa [← hmul]

theorem tendsto_integral_windowModel_H (F : AdmissibleFamily)
    (b J : ℕ) {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f)
    (hbdd : ∀ x, |f x| ≤ M) :
    Tendsto (fun H : ℕ =>
      ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F)
      atTop
      (𝓝 (∫ ω, f (modelTrunc F b J ω) ∂rootMeasure F)) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hμ := tendsto_measureReal_modelSpan_gt F J
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_cases hM0 : M = 0
  · refine ⟨0, fun H _ => ?_⟩
    have hbound := abs_integral_windowModel_sub_test F b J H hf hbdd
    have hle0 : |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
        ∫ ω, f (modelTrunc F b J ω) ∂rootMeasure F| ≤ 0 := by
      simpa [hM0] using hbound
    rw [Real.dist_eq]
    exact hle0.trans_lt hε
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    obtain ⟨H0, hH0⟩ := (Metric.tendsto_atTop.mp hμ) (ε / M) (by positivity)
    refine ⟨H0, fun H hH => ?_⟩
    have hμH : (rootMeasure F).real {ω | H < modelSpan F J ω} < ε / M := by
      have hdist := hH0 H hH
      rw [dist_zero_right, Real.norm_eq_abs] at hdist
      exact lt_of_le_of_lt (le_abs_self _) hdist
    have hbound := abs_integral_windowModel_sub_test F b J H hf hbdd
    have hlt : M * (rootMeasure F).real {ω | H < modelSpan F J ω} < ε := by
      have := mul_lt_mul_of_pos_left hμH hMpos
      rwa [mul_div_cancel₀ _ hM0] at this
    rw [Real.dist_eq]
    exact hbound.trans_lt hlt

/-- J-gap Palm transfer of a bounded Lipschitz test of the truncated tail.
CanonicalTransfer cannot import Carry, so the Haar side is `modelTrunc`
(equal to `gapTailTrunc` on `survival`, hence `rootMeasure`-a.e.). -/
theorem cesaro_trunc_test_eq_root
    (F : AdmissibleFamily) {b : ℕ} (_hb : 2 ≤ b) (J : ℕ)
    {f : ℝ → ℝ} {K : ℝ≥0} {M : ℝ}
    (hLip : LipschitzWith K f) (hbdd : ∀ x, |f x| ≤ M) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, f (canonicalGapTailTrunc F b J n)) / N)
      atTop
      (𝓝 (∫ a, f (modelTrunc F b J a) ∂rootMeasure F)) := by
  have hf : Continuous f := hLip.continuous
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbdd 0)
  have hI := tendsto_integral_windowModel_H F b J hf hbdd
  have hspan := tendsto_cesaro_span_enum F J
  rw [Metric.tendsto_atTop]
  intro ε hε
  let Cspan : ℝ := (J : ℝ) * (rho F)⁻¹ + 1
  have hCspan0 : 0 ≤ Cspan := by
    unfold Cspan
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (rho_pos F).le))
      zero_le_one
  have hmarkovH :
      Tendsto (fun H : ℕ => M * Cspan / (H + 1 : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun H : ℕ => (1 : ℝ) / (H + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hfun :
        (fun H : ℕ => M * Cspan / ((H : ℝ) + 1)) =
          fun H : ℕ => (M * Cspan) * ((1 : ℝ) / ((H : ℝ) + 1)) :=
      funext fun H => by ring
    rw [hfun]
    simpa [mul_zero] using hinv.const_mul (M * Cspan)
  obtain ⟨H1, hH1⟩ := (Metric.tendsto_atTop.mp hI) (ε / 3) (by linarith)
  obtain ⟨H2, hH2⟩ := (Metric.tendsto_atTop.mp hmarkovH) (ε / 3) (by linarith)
  let H := max H1 H2
  have hIH : dist (∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F)
      (∫ a, f (modelTrunc F b J a) ∂rootMeasure F) < ε / 3 :=
    hH1 H (le_max_left _ _)
  have hMH : M * Cspan / (H + 1 : ℝ) < ε / 3 := by
    have hdist := hH2 H (le_max_right H1 H2)
    rw [dist_zero_right, Real.norm_eq_abs] at hdist
    exact lt_of_le_of_lt (le_abs_self _) hdist
  have hw := tendsto_cesaro_truncTestWindow_enum F b J H hf hbdd
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hw) (ε / 3) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hspan) (1 : ℝ) (by norm_num)
  refine ⟨max N1 (max N2 1), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_max_left N1 _) hN
  have hN2' : N2 ≤ N :=
    le_trans (le_max_left N2 1) (le_trans (le_max_right N1 _) hN)
  have hNpos : 1 ≤ N :=
    le_trans (le_max_right N2 1) (le_trans (le_max_right N1 _) hN)
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hwN :
      dist ((∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N)
        (∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F) < ε / 3 :=
    hN1 N hN1'
  have hSN : |((∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k)) / N) -
      (J : ℝ) * (rho F)⁻¹| < 1 := by
    simpa [Real.dist_eq] using hN2 N hN2'
  have hSle : (∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k)) / N ≤ Cspan := by
    have hnn : 0 ≤ (∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k)) / N := by
      refine div_nonneg (sum_nonneg fun k _ => ?_) (Nat.cast_nonneg _)
      have hle : enum F k ≤ enum F (k + J) :=
        (enum_strictMono F).monotone (Nat.le_add_right _ _)
      rw [← Nat.cast_sub hle]
      exact Nat.cast_nonneg _
    have : (∑ k ∈ range N, ((enum F (k + J) : ℝ) - enum F k)) / N < Cspan := by
      unfold Cspan
      linarith [abs_lt.mp hSN]
    exact this.le
  have hcard :
      (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N ≤
        Cspan / (H + 1 : ℝ) := by
    have hHpos : (0 : ℝ) < (H + 1 : ℝ) := by positivity
    have hnum := card_enum_span_gt_le F J H N
    have hdiv := div_le_div_of_nonneg_right hnum hN0.le
    have hrew :
        ((H + 1 : ℝ) *
            (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ)) / N =
          (H + 1 : ℝ) *
            ((#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N) := by
      ring
    rw [hrew] at hdiv
    have hmul :
        (H + 1 : ℝ) *
            ((#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N) ≤
          Cspan :=
      hdiv.trans hSle
    have hmul' :
        ((#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N) *
            (H + 1 : ℝ) ≤
          Cspan := by
      convert hmul using 1
      ring
    exact (le_div_iff₀ hHpos).mpr hmul'
  have hdiff :
      |(∑ n ∈ range N, f (canonicalGapTailTrunc F b J n)) / N -
          (∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N| ≤
        M * Cspan / (H + 1 : ℝ) := by
    have h := abs_cesaro_trunc_sub_window_enum F b J H hbdd N
    have hle :
        M * (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N ≤
          M * Cspan / (H + 1 : ℝ) := by
      have h1 :
          M * (#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N =
            M * ((#{k ∈ range N | H < enum F (k + J) - enum F k} : ℝ) / N) := by
        ring
      have h2 : M * Cspan / (H + 1 : ℝ) = M * (Cspan / (H + 1 : ℝ)) := by
        ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hcard hM
    exact h.trans hle
  rw [Real.dist_eq]
  have htri :
      |(∑ n ∈ range N, f (canonicalGapTailTrunc F b J n)) / N -
          ∫ a, f (modelTrunc F b J a) ∂rootMeasure F| ≤
        |(∑ n ∈ range N, f (canonicalGapTailTrunc F b J n)) / N -
            (∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N| +
          |(∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N -
              ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F| +
          |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
              ∫ a, f (modelTrunc F b J a) ∂rootMeasure F| := by
    have hrew :
        (∑ n ∈ range N, f (canonicalGapTailTrunc F b J n)) / N -
            ∫ a, f (modelTrunc F b J a) ∂rootMeasure F =
          ((∑ n ∈ range N, f (canonicalGapTailTrunc F b J n)) / N -
              (∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N) +
            ((∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N -
                ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F) +
            (∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
                ∫ a, f (modelTrunc F b J a) ∂rootMeasure F) := by
      ring
    rw [hrew]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hwabs :
      |(∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N -
          ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F| < ε / 3 := by
    simpa [Real.dist_eq] using hwN
  have hIabs :
      |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
          ∫ a, f (modelTrunc F b J a) ∂rootMeasure F| < ε / 3 := by
    simpa [Real.dist_eq, abs_sub_comm] using hIH
  have hsumlt :
      M * Cspan / (H + 1 : ℝ) +
          |(∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N -
              ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F| +
          |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
              ∫ a, f (modelTrunc F b J a) ∂rootMeasure F| <
        ε := by
    have : M * Cspan / (H + 1 : ℝ) +
        |(∑ k ∈ range N, truncTestWindow F b J H f (enum F k)) / N -
            ∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F| +
        |∫ ω, truncTestWindowModel F b J H f ω ∂rootMeasure F -
            ∫ a, f (modelTrunc F b J a) ∂rootMeasure F| <
        ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add_of_le_of_lt hMH.le hwabs) hIabs
    linarith
  exact (htri.trans (add_le_add (add_le_add hdiff le_rfl) le_rfl)).trans_lt hsumlt

end PalmTransfer

end PrimeGapNormality.BFree
