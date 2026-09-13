import PrimeGapNormality.Prime.CoreBetaFailureGeometry
import PrimeGapNormality.Prime.CoreBetaBoundaryMass
import PrimeGapNormality.Prime.CoreBetaRankinTail

/-!
# Actual beta-sieve boundary records and their weighted mass

The suffix in a Buchstab record is identified with the original pool below
the last selected prime. Thus the Euler factors in the exact remainder are
the factors to which the finite dimension hypothesis applies. No boundary
multiplicity or suffix identity is assumed.
-/

namespace PrimeGapNormality.Prime.CoreBetaRemainderBound

open CoreBetaBuchstab CoreBetaLevelSupport CoreBetaFailureGeometry CoreBetaBoundaryMass
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 1000000

/-- Each actual record ends at a selected member of the original pool,
and its second component is exactly the suffix following that member. -/
theorem firstFailure_suffix_exists (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (e : List ℕ × List ℕ)
    (he : e ∈ firstFailures upper A stem ps) :
    ∃ (xs ys : List ℕ) (p : ℕ), e.1 = xs ++ [p] ∧ ps = ys ++ p :: e.2 := by
  induction ps generalizing upper stem e with
  | nil => simp [firstFailures] at he
  | cons p ps ih =>
    rw [firstFailures, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨xs, ys, q, hx, hy⟩ := ih upper stem e he
      exact ⟨xs, p :: ys, q, hx, by simp [hy]⟩
    · by_cases hs : stops upper A stem p
      · simp only [hs, if_true, List.mem_singleton] at he
        subst e
        exact ⟨[], [], p, rfl, rfl⟩
      · simp only [hs, if_false, List.mem_map] at he
        obtain ⟨e', he', rfl⟩ := he
        obtain ⟨xs, ys, q, hx, hy⟩ := ih (!upper) (stem ++ [p]) e' he'
        exact ⟨p :: xs, p :: ys, q, by simp [hx], by simp [hy]⟩

/-- Exact Euler-factor indexing: no smaller pool or independent list is
substituted for the actual suffix. -/
theorem firstFailure_suffix_eq_filter (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper A stem ps) :
    e.2 = ps.filter (fun q : ℕ => decide (q < e.1.getLastD 1)) := by
  obtain ⟨xs, ys, p, hx, hy⟩ := firstFailure_suffix_exists upper A stem ps e he
  have hd := List.pairwise_append.mp (hy ▸ hdec)
  have hbefore : ys.filter (fun q : ℕ => decide (q < p)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    have hpq : p < q := hd.2.2 q hq p (by simp)
    simp [Nat.not_lt.mpr hpq.le]
  have hafter : e.2.filter (fun q : ℕ => decide (q < p)) = e.2 := by
    apply List.filter_eq_self.mpr
    intro q hq
    exact decide_eq_true ((List.pairwise_cons.mp hd.2.1).1 q hq)
  rw [hx, List.getLastD_concat, hy, List.filter_append, hbefore]
  simp [hafter]

theorem firstFailure_euler_suffix (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper A stem ps) (g : ℕ → ℝ) :
    euler g e.2 = euler g (ps.filter (fun q : ℕ => decide (q < e.1.getLastD 1))) := by
  rw [firstFailure_suffix_eq_filter upper A stem ps hdec e he]

/-- Every selected prime is at least the last selected prime. -/
theorem firstFailure_last_le_member (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper A stem ps)
    (p : ℕ) (hp : p ∈ e.1) : e.1.getLastD 1 ≤ p := by
  obtain ⟨xs, ys, q, hx, hy⟩ := firstFailure_suffix_exists upper A stem ps e he
  have hs := (firstFailure_sublist upper A stem ps e he).2
  have hd := List.pairwise_append.mp (hx ▸ List.Pairwise.sublist hs hdec)
  rw [hx, List.getLastD_concat]
  rw [hx, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact (hd.2.2 p hp q (by simp)).le
  · exact le_rfl

/-- The actual first-failure geometry puts every selected prime in the
same r-dependent band; it does not only bound the final selected prime. -/
theorem firstFailure_member_lower {β : ℕ} (hβ : 2 ≤ β) {Z R : ℝ}
    (hZ : 1 < Z) (hR : 1 < R) (hlevel : Z ^ β ≤ R)
    (upper : Bool) (ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (hprime : ∀ (p : ℕ), p ∈ ps → Nat.Prime p) (hbelow : ∀ (p : ℕ), p ∈ ps → (p : ℝ) < Z)
    (e : List ℕ × List ℕ) (he : e ∈ firstFailures upper (test β R) [] ps)
    (p : ℕ) (hp : p ∈ e.1) :
    max 2 (Z ^ (contraction β ^ e.1.length)) ≤ (p : ℝ) := by
  apply max_le
  · exact_mod_cast (hprime p ((firstFailure_sublist upper (test β R) [] ps e he).2.subset hp)).two_le
  · exact (firstFailure_last_lower hβ hZ hR hlevel upper ps hdec hprime hbelow e he).trans
      (Nat.cast_le.mpr (firstFailure_last_le_member upper (test β R) [] ps hdec e he p hp))

/-- Incorporating an Euler-factor bound in a length-r record sum uses
the proved factorial estimate for the actual distinct selected words. -/
theorem weighted_boundary_le (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (hn : ps.Nodup) (r : ℕ) (band : List ℕ)
    (g : ℕ → ℝ) (hg : ∀ (p : ℕ), p ∈ ps → 0 ≤ g p)
    (hgb : ∀ (p : ℕ), p ∈ band → 0 ≤ g p) (E : ℝ) (hE : 0 ≤ E)
    (hband : ∀ e ∈ firstFailures upper A stem ps, e.1.length = r → List.Sublist e.1 band)
    (heuler : ∀ e ∈ firstFailures upper A stem ps, e.1.length = r → euler g e.2 ≤ E) :
    ((((firstFailures upper A stem ps).filter (fun e => decide (e.1.length = r))).map
      (fun e => product g e.1 * euler g e.2)).sum) ≤
      E * (mass g band ^ r / (r.factorial : ℝ)) := by
  let records := (firstFailures upper A stem ps).filter (fun e => decide (e.1.length = r))
  have hterm : ∀ e ∈ records, product g e.1 * euler g e.2 ≤ E * product g e.1 := by
    intro e he
    obtain ⟨he, hr⟩ := List.mem_filter.mp he
    have hp : 0 ≤ product g e.1 := by
      unfold product
      apply List.prod_nonneg
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hg p ((firstFailure_sublist upper A stem ps e he).2.subset hp)
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (heuler e he (of_decide_eq_true hr)) hp
  calc
    _ ≤ (records.map (fun e => E * product g e.1)).sum := List.sum_le_sum hterm
    _ = E * ((boundaryWords upper A stem ps r).map (product g)).sum := by
      rw [List.sum_map_mul_left, boundary_mass_eq_record_sum]
    _ ≤ E * (mass g band ^ r / (r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (firstFailure_mass_le_pow_div_factorial upper A stem ps hn r band g hgb hband) hE

theorem euler_pos (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ (p : ℕ), p ∈ ps → g p < 1) : 0 < euler g ps := by
  unfold euler
  apply List.prod_pos
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact sub_pos.mpr (hg p hp)

/-- The band logarithm uses the finite Euler ratio once, not once per
recursion depth. This follows directly from x ≤ -log(1-x). -/
theorem band_mass_le_log_euler_ratio (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ (p : ℕ), p ∈ ps → g p < 1) (u : ℝ) :
    mass g (ps.filter (fun p : ℕ => decide (u ≤ (p : ℝ)))) ≤
      Real.log (euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) / euler g ps) := by
  have hmain : mass g (ps.filter (fun p : ℕ => decide (u ≤ (p : ℝ)))) ≤
      Real.log (euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u)))) - Real.log (euler g ps) := by
    induction ps with
    | nil => simp [mass, euler]
    | cons p ps ih =>
      have hp : 0 < 1 - g p := sub_pos.mpr (hg p (by simp))
      have ht : ∀ (q : ℕ), q ∈ ps → g q < 1 := fun (q : ℕ) hq => hg q (by simp [hq])
      have htf : ∀ (q : ℕ), q ∈ ps.filter (fun q : ℕ => decide ((q : ℝ) < u)) → g q < 1 :=
        fun (q : ℕ) hq => ht q (List.mem_filter.mp hq).1
      have hi := ih ht
      have hlog := Real.log_le_sub_one_of_pos hp
      by_cases hpu : (p : ℝ) < u
      · simp only [List.filter_cons, hpu, decide_true, Bool.coe_true, if_true,
          not_le.mpr hpu, decide_false, Bool.false_eq_true, if_false, euler_cons]
        rw [Real.log_mul hp.ne' (euler_pos g _ htf).ne',
          Real.log_mul hp.ne' (euler_pos g ps ht).ne']
        linarith
      · have hup : u ≤ (p : ℝ) := le_of_not_gt hpu
        simp only [List.filter_cons, hpu, decide_false, Bool.false_eq_true, if_false,
          hup, decide_true, Bool.coe_true, if_true, euler_cons]
        change g p + mass g (ps.filter (fun q : ℕ => decide (u ≤ (q : ℝ)))) ≤ _
        rw [Real.log_mul hp.ne' (euler_pos g ps ht).ne']
        linarith
  rw [Real.log_div (euler_pos g _ (fun (p : ℕ) hp => hg p (List.mem_filter.mp hp).1)).ne'
    (euler_pos g ps hg).ne']
  exact hmain

theorem euler_filter_antitone (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ (p : ℕ), p ∈ ps → 0 ≤ g p ∧ g p < 1) {u v : ℝ} (huv : u ≤ v) :
    euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < v))) ≤
      euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih =>
    have hp := hg p (by simp)
    have ht : ∀ (q : ℕ), q ∈ ps → 0 ≤ g q ∧ g q < 1 := fun (q : ℕ) hq => hg q (by simp [hq])
    have hi := ih ht
    by_cases hpu : (p : ℝ) < u
    · have hpv := hpu.trans_le huv
      simpa only [List.filter_cons, hpu, hpv, decide_true, Bool.coe_true,
        if_true, euler_cons] using mul_le_mul_of_nonneg_left hi (sub_pos.mpr hp.2).le
    · by_cases hpv : (p : ℝ) < v
      · simp only [List.filter_cons, hpu, hpv, decide_true, decide_false,
          Bool.coe_true, Bool.false_eq_true, if_true, if_false, euler_cons]
        have he : 0 ≤ euler g (ps.filter (fun q : ℕ => decide ((q : ℝ) < v))) :=
          (euler_pos g _ (fun (q : ℕ) hq => (ht q (List.mem_filter.mp hq).1).2)).le
        exact (mul_le_of_le_one_left he (by linarith : 1 - g p ≤ 1)).trans hi
      · simpa only [List.filter_cons, hpu, hpv, decide_false, Bool.false_eq_true,
          if_false] using hi

/-- The geometric cutoff stays inside the legitimate dimension range,
including when its untruncated value lies below the first prime. -/
theorem geometric_cutoff_mem {Z q : ℝ} (hZ : 2 < Z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (r : ℕ) : 2 ≤ max 2 (Z ^ (q ^ r)) ∧ max 2 (Z ^ (q ^ r)) ≤ Z := by
  refine ⟨le_max_left _ _, max_le hZ.le ?_⟩
  exact Real.rpow_le_self_of_one_le (by linarith)
    (pow_le_one₀ hq0 hq1)

theorem geometric_log_ratio_pow_le {Z q : ℝ} (hZ : 2 < Z)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (k r : ℕ) :
    (Real.log Z / Real.log (max 2 (Z ^ (q ^ r)))) ^ k ≤
      Real.exp ((k : ℝ) * Real.log q⁻¹ * (r : ℝ)) := by
  let u := max 2 (Z ^ (q ^ r))
  have hZ0 : 0 < Z := by linarith
  have hu : 1 < u := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hlZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlog : q ^ r * Real.log Z ≤ Real.log u := by
    simpa only [Real.log_rpow hZ0] using
      Real.log_le_log (Real.rpow_pos_of_pos hZ0 _) (le_max_right 2 (Z ^ (q ^ r)))
  have hqp : 0 < q ^ r := pow_pos hq0 r
  have hratio : Real.log Z / Real.log u ≤ (q ^ r)⁻¹ := by
    apply (div_le_iff₀ hlu).mpr
    apply (le_inv_mul_iff₀ hqp).mpr
    simpa only [mul_comm] using hlog
  calc
    _ ≤ ((q ^ r)⁻¹) ^ k :=
      pow_le_pow_left₀ (div_nonneg hlZ.le hlu.le) hratio k
    _ = Real.exp ((k : ℝ) * Real.log q⁻¹ * (r : ℝ)) := by
      rw [← Real.exp_log (pow_pos (inv_pos.mpr hqp) k)]
      congr 1
      rw [Real.log_pow, Real.log_inv, Real.log_pow, Real.log_inv]
      ring

/-- Both uses of the dimension input at a fixed geometric band. -/
theorem geometric_band_bounds {Z q K : ℝ} (hZ : 2 < Z)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hK : 1 ≤ K) (k r : ℕ)
    (ps : List ℕ) (g : ℕ → ℝ) (hg : ∀ (p : ℕ), p ∈ ps → g p < 1)
    (hdim : ∀ u : ℝ, 2 ≤ u → u ≤ Z →
      euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) / euler g ps ≤
        K * (Real.log Z / Real.log u) ^ k) :
    let u := max 2 (Z ^ (q ^ r))
    euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) / euler g ps ≤
        K * Real.exp ((k : ℝ) * Real.log q⁻¹ * (r : ℝ)) ∧
      mass g (ps.filter (fun p : ℕ => decide (u ≤ (p : ℝ)))) ≤
        Real.log K + (k : ℝ) * Real.log q⁻¹ * (r : ℝ) := by
  dsimp only
  have hu := geometric_cutoff_mem hZ hq0.le hq1 r
  have hratio := (hdim _ hu.1 hu.2).trans
    (mul_le_mul_of_nonneg_left (geometric_log_ratio_pow_le hZ hq0 hq1 k r)
      (zero_le_one.trans hK))
  refine ⟨hratio, (band_mass_le_log_euler_ratio g ps hg _).trans ?_⟩
  have hrpos : 0 < euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < max 2 (Z ^ (q ^ r))))) /
      euler g ps := div_pos (euler_pos g _ (fun (p : ℕ) hp => hg p (List.mem_filter.mp hp).1))
        (euler_pos g ps hg)
  have hh := Real.log_le_log hrpos hratio
  simpa only [Real.log_mul (zero_lt_one.trans_le hK).ne' (Real.exp_pos _).ne',
    Real.log_exp] using hh

/-- Finite disintegration by the actual length, valid for any finite set
containing the lengths of the records. -/
theorem sum_records_by_length (es : List (List ℕ × List ℕ)) (f : (List ℕ × List ℕ) → ℝ)
    (S : Finset ℕ) (hS : ∀ e ∈ es, e.1.length ∈ S) :
    (es.map f).sum = ∑ r ∈ S, ((es.filter (fun e => decide (e.1.length = r))).map f).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := hS e (by simp)
    have ht : ∀ a ∈ es, a.1.length ∈ S := fun a ha => hS a (by simp [ha])
    have hcons (r : ℕ) :
        (((e :: es).filter (fun a => decide (a.1.length = r))).map f).sum =
          (if e.1.length = r then f e else 0) +
            ((es.filter (fun a => decide (a.1.length = r))).map f).sum := by
      by_cases hr : e.1.length = r <;> simp [hr]
    simp only [List.map_cons, List.sum_cons, hcons, Finset.sum_add_distrib, ← ih ht]
    rw [Finset.sum_eq_single e.1.length]
    · simp
    · intro b hb hbe
      simp [Ne.symm hbe]
    · exact fun h => (h he).elim

theorem beta_contraction_log_bounds {k : ℕ} (hk : 1 ≤ k) :
    let q := contraction (9 * k + 1)
    0 < q ∧ q ≤ 1 ∧ 0 ≤ (k : ℝ) * Real.log q⁻¹ ∧
      (k : ℝ) * Real.log q⁻¹ ≤ 1 / 9 := by
  dsimp only
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hq : contraction (9 * k + 1) = (9 * (k : ℝ)) / (9 * (k : ℝ) + 1) := by
    unfold contraction
    push_cast
    ring
  have hq0 : 0 < contraction (9 * k + 1) := by rw [hq]; positivity
  have hq1 : contraction (9 * k + 1) ≤ 1 := by
    rw [hq, div_le_one (by positivity)]
    linarith
  have hi : (contraction (9 * k + 1))⁻¹ - 1 = 1 / (9 * (k : ℝ)) := by
    rw [hq]
    field_simp [hk0.ne']
    <;> ring
  have hlog0 : 0 ≤ Real.log (contraction (9 * k + 1))⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hq0.le hq1)
  refine ⟨hq0, hq1, mul_nonneg hk0.le hlog0, ?_⟩
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (inv_pos.mpr hq0)) hk0.le
  rw [hi] at hlog
  calc
    _ ≤ (k : ℝ) * (1 / (9 * (k : ℝ))) := hlog
    _ = 1 / 9 := by field_simp [hk0.ne'] <;> ring

theorem weighted_geometric_boundary_le {β : ℕ} (hβ : 2 ≤ β) {Z R K : ℝ}
    (hZ : 2 < Z) (hR : 1 < R) (hlevel : Z ^ β ≤ R)
    (hK : 1 ≤ K) (k r : ℕ)
    (hq0 : 0 < contraction β) (hq1 : contraction β ≤ 1)
    (upper : Bool) (ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (hprime : ∀ (p : ℕ), p ∈ ps → Nat.Prime p) (hbelow : ∀ (p : ℕ), p ∈ ps → (p : ℝ) < Z)
    (g : ℕ → ℝ) (hg : ∀ (p : ℕ), p ∈ ps → 0 ≤ g p ∧ g p < 1)
    (hdim : ∀ u : ℝ, 2 ≤ u → u ≤ Z →
      euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) / euler g ps ≤
        K * (Real.log Z / Real.log u) ^ k) :
    ((((firstFailures upper (test β R) [] ps).filter (fun e => decide (e.1.length = r))).map
      (fun e => product g e.1 * euler g e.2)).sum) ≤
      euler g ps * (K * Real.exp ((k : ℝ) * Real.log (contraction β)⁻¹ * (r : ℝ)) *
        (Real.log K + (k : ℝ) * Real.log (contraction β)⁻¹ * (r : ℝ)) ^ r /
          (r.factorial : ℝ)) := by
  let u := max 2 (Z ^ (contraction β ^ r))
  let band : List ℕ := ps.filter (fun p : ℕ => decide (u ≤ (p : ℝ)))
  let E := euler g ps * (K * Real.exp ((k : ℝ) * Real.log (contraction β)⁻¹ * (r : ℝ)))
  have hV := euler_pos g ps (fun (p : ℕ) hp => (hg p hp).2)
  have hgb : ∀ (p : ℕ), p ∈ band → 0 ≤ g p := fun (p : ℕ) hp => (hg p (List.mem_filter.mp hp).1).1
  have hh := geometric_band_bounds hZ hq0 hq1 hK k r ps g (fun (p : ℕ) hp => (hg p hp).2) hdim
  have hE : 0 ≤ E := mul_nonneg hV.le
    (mul_nonneg (zero_le_one.trans hK) (Real.exp_pos _).le)
  have hband : ∀ e ∈ firstFailures upper (test β R) [] ps, e.1.length = r →
      List.Sublist e.1 band := by
    intro e he hr
    apply sublist_filter_of_forall (firstFailure_sublist upper (test β R) [] ps e he).2
    intro p hp
    apply decide_eq_true
    simpa only [u, hr] using
      firstFailure_member_lower hβ (by linarith) hR hlevel upper ps hdec hprime hbelow e he p hp
  have heuler : ∀ e ∈ firstFailures upper (test β R) [] ps, e.1.length = r → euler g e.2 ≤ E := by
    intro e he hr
    have hlast : u ≤ (e.1.getLastD 1 : ℝ) := by
      obtain ⟨xs, ys, p, hx, hy⟩ := firstFailure_suffix_exists upper (test β R) [] ps e he
      have hp : p ∈ e.1 := by simp [hx]
      rw [hx, List.getLastD_concat]
      simpa only [u, hr] using
        firstFailure_member_lower hβ (by linarith) hR hlevel upper ps hdec hprime hbelow e he p hp
    have hm := euler_filter_antitone g ps hg hlast
    have hratio : euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) ≤ E := by
      simpa only [E, mul_comm] using (div_le_iff₀ hV).mp hh.1
    rw [firstFailure_euler_suffix upper (test β R) [] ps hdec e he g]
    have hid : ps.filter (fun q : ℕ => decide (q < e.1.getLastD 1)) =
        ps.filter (fun q : ℕ => decide ((q : ℝ) < (e.1.getLastD 1 : ℝ))) := by simp
    rw [hid]
    exact hm.trans hratio
  have hn : ps.Nodup := hdec.imp (fun h => Ne.symm h.ne)
  have hw := weighted_boundary_le upper (test β R) [] ps hn r band g
    (fun (p : ℕ) hp => (hg p hp).1) hgb E hE hband heuler
  have hpow := pow_le_pow_left₀ (mass_nonneg g band hgb) hh.2 r
  have hd := div_le_div_of_nonneg_right hpow (Nat.cast_nonneg r.factorial)
  have hmul := mul_le_mul_of_nonneg_left hd hE
  exact hw.trans (hmul.trans_eq (by dsimp only [E]; ring))

/-- Uniform finite fundamental-lemma remainder for the actual parity
stopped weights. The sole distribution input is the finite Euler-product
dimension inequality, quantified over genuine cutoffs 2 ≤ u ≤ Z. -/
theorem remainder_le {k : ℕ} (hk : 1 ≤ k) {Z R K : ℝ}
    (hZ : 2 < Z) (hlevel : Z ^ (9 * k + 1) ≤ R) (hK : 1 ≤ K)
    (upper : Bool) (ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (hprime : ∀ (p : ℕ), p ∈ ps → Nat.Prime p) (hbelow : ∀ (p : ℕ), p ∈ ps → (p : ℝ) < Z)
    (g : ℕ → ℝ) (hg : ∀ (p : ℕ), p ∈ ps → 0 ≤ g p ∧ g p < 1)
    (hdim : ∀ u : ℝ, 2 ≤ u → u ≤ Z →
      euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) / euler g ps ≤
        K * (Real.log Z / Real.log u) ^ k) :
    remainder upper (test (9 * k + 1) R) [] ps g ≤
      2 * K ^ 9 * Real.exp (((9 * k + 1 : ℕ) : ℝ) - Real.log R / Real.log Z) * euler g ps := by
  let β := 9 * k + 1
  let s := Real.log R / Real.log Z
  let α := (k : ℝ) * Real.log (contraction β)⁻¹
  let S := (Finset.range (ps.length + 1)).filter (fun r : ℕ => s - (β : ℝ) < (r : ℝ))
  have hβ : 2 ≤ β := by dsimp [β]; omega
  have hZ1 : 1 < Z := by linarith
  have hR : 1 < R := hZ1.trans_le
    ((le_self_pow₀ hZ1.le (by omega : β ≠ 0)).trans hlevel)
  have hβs : (β : ℝ) ≤ s := by
    apply (le_div_iff₀ (Real.log_pos hZ1)).mpr
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by linarith : 0 < Z) β) hlevel
  obtain ⟨hq0, hq1, hα0, hα⟩ := beta_contraction_log_bounds hk
  have hV := euler_pos g ps (fun (p : ℕ) hp => (hg p hp).2)
  have hS : ∀ e ∈ firstFailures upper (test β R) [] ps, e.1.length ∈ S := by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hl := (firstFailure_sublist upper (test β R) [] ps e he).2.length_le
      omega
    · exact firstFailure_length_gt hZ1 (zero_lt_one.trans hR) β upper ps hbelow e he
  change (((firstFailures upper (test β R) [] ps).map
    (fun e => product g e.1 * euler g e.2)).sum) ≤ _
  rw [sum_records_by_length _ _ S hS]
  calc
    _ ≤ ∑ r ∈ S, euler g ps *
        (K * Real.exp (α * (r : ℝ)) * (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact weighted_geometric_boundary_le hβ hZ hR hlevel hK k r hq0 hq1
        upper ps hdec hprime hbelow g hg hdim
    _ = euler g ps * ∑ r ∈ S,
        K * Real.exp (α * (r : ℝ)) * (Real.log K + α * (r : ℝ)) ^ r / (r.factorial : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ euler g ps * (2 * K ^ 9 * Real.exp ((β : ℝ) - s)) :=
      mul_le_mul_of_nonneg_left (CoreBetaRankinTail.beta_rankin_tail_le hK hα0 hα hβs) hV.le
    _ = _ := by dsimp only [β, s]; ring

/-- Both upper and lower means satisfy the same explicit relative error.
The sign and the nonnegative error come from the exact finite Buchstab
identity, not from an assumed upper/lower approximation. -/
theorem main_abs_sub_euler_le {k : ℕ} (hk : 1 ≤ k) {Z R K : ℝ}
    (hZ : 2 < Z) (hlevel : Z ^ (9 * k + 1) ≤ R) (hK : 1 ≤ K)
    (upper : Bool) (ps : List ℕ) (hdec : ps.Pairwise (fun (p q : ℕ) => q < p))
    (hprime : ∀ (p : ℕ), p ∈ ps → Nat.Prime p) (hbelow : ∀ (p : ℕ), p ∈ ps → (p : ℝ) < Z)
    (g : ℕ → ℝ) (hg : ∀ (p : ℕ), p ∈ ps → 0 ≤ g p ∧ g p < 1)
    (hdim : ∀ u : ℝ, 2 ≤ u → u ≤ Z →
      euler g (ps.filter (fun p : ℕ => decide ((p : ℝ) < u))) / euler g ps ≤
        K * (Real.log Z / Real.log u) ^ k) :
    |main upper (test (9 * k + 1) R) [] ps g - euler g ps| ≤
      2 * K ^ 9 * Real.exp (((9 * k + 1 : ℕ) : ℝ) - Real.log R / Real.log Z) * euler g ps := by
  have hn := remainder_nonneg upper (test (9 * k + 1) R) [] ps g
    (fun (p : ℕ) hp => ⟨(hg p hp).1, (hg p hp).2.le⟩)
  have hb := remainder_le hk hZ hlevel hK upper ps hdec hprime hbelow g hg hdim
  rw [main_eq_euler_add_signed_remainder]
  cases upper <;> simpa [abs_of_nonneg hn] using hb

end
end PrimeGapNormality.Prime.CoreBetaRemainderBound
