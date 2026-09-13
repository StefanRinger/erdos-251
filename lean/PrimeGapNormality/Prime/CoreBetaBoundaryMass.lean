import PrimeGapNormality.Prime.CoreBetaBuchstab
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# No multiplicity loss in first-failure boundary mass

Selected first-failure words form a sublist of the actual sublist
enumeration. For a nodup pool they are therefore nodup. Elementary
symmetric sums are bounded by mass^r/r! using a proved one-step recurrence,
and the bound is applied to the actual selected boundary words.
-/

namespace PrimeGapNormality.Prime.CoreBetaBoundaryMass

open CoreBetaBuchstab
open scoped Classical
noncomputable section

set_option maxHeartbeats 800000

/-- Stronger than a cardinality assertion: the selected failure words
occur in their actual order in the sublist enumeration. -/
theorem firstFailures_selected_sublist (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) :
    List.Sublist ((firstFailures upper A stem ps).map Prod.fst) ps.sublists' := by
  induction ps generalizing upper stem with
  | nil => simp [firstFailures]
  | cons p ps ih =>
    rw [firstFailures, List.map_append, List.sublists'_cons]
    apply List.Sublist.append (ih upper stem)
    by_cases hs : stops upper A stem p
    · simp only [hs, if_true, List.map_cons, List.map_nil]
      have hnil : List.Sublist ([[]] : List (List ℕ)) ps.sublists' :=
        List.singleton_sublist.mpr (List.mem_sublists'.mpr (List.nil_sublist ps))
      simpa only [List.map_cons, List.map_nil] using hnil.map (List.cons p)
    · simp only [hs, if_false]
      simpa only [List.map_map, Function.comp_def] using
        (ih (!upper) (stem ++ [p])).map (List.cons p)

/-- No selected word is charged twice, proved from the finite construction. -/
theorem firstFailures_selected_nodup (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (hn : ps.Nodup) :
    ((firstFailures upper A stem ps).map Prod.fst).Nodup :=
  List.Pairwise.sublist (firstFailures_selected_sublist upper A stem ps)
    (List.nodup_sublists'.mpr hn)

def mass (g : ℕ → ℝ) (ps : List ℕ) : ℝ := (ps.map g).sum

def elementary (g : ℕ → ℝ) (ps : List ℕ) (r : ℕ) : ℝ :=
  ((ps.sublistsLen r).map (product g)).sum

private theorem product_nonneg (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ p ∈ ps, 0 ≤ g p) : 0 ≤ product g ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [product_cons]
    exact mul_nonneg (hg p (by simp)) (ih (fun q hq => hg q (by simp [hq])))

theorem mass_nonneg (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ p ∈ ps, 0 ≤ g p) : 0 ≤ mass g ps := by
  unfold mass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact hg p hp

theorem elementary_nonneg (g : ℕ → ℝ) (ps : List ℕ) (r : ℕ)
    (hg : ∀ p ∈ ps, 0 ≤ g p) : 0 ≤ elementary g ps r := by
  unfold elementary
  apply List.sum_nonneg
  intro x hx
  obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
  exact product_nonneg g xs (fun p hp => hg p ((List.mem_sublistsLen.mp hxs).1.subset hp))

@[simp] theorem elementary_zero (g : ℕ → ℝ) (ps : List ℕ) : elementary g ps 0 = 1 := by
  simp [elementary]

@[simp] theorem elementary_nil_succ (g : ℕ → ℝ) (r : ℕ) : elementary g [] (r + 1) = 0 := rfl

theorem elementary_one (g : ℕ → ℝ) (ps : List ℕ) : elementary g ps 1 = mass g ps := by
  simp [elementary, List.sublistsLen_one, List.map_map, Function.comp_def, product, mass]

theorem elementary_cons (g : ℕ → ℝ) (p : ℕ) (ps : List ℕ) (r : ℕ) :
    elementary g (p :: ps) (r + 1) = elementary g ps (r + 1) + g p * elementary g ps r := by
  unfold elementary
  rw [List.sublistsLen_succ_cons, List.map_append, List.sum_append, List.map_map]
  change ((ps.sublistsLen (r + 1)).map (product g)).sum +
    ((ps.sublistsLen r).map (fun xs => g p * product g xs)).sum = _
  rw [List.sum_map_mul_left]

/-- The multiplicity r+1 is proved by the sublist recurrence, without
assuming an ordering/permutation count. -/
theorem elementary_step_le (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ p ∈ ps, 0 ≤ g p) (r : ℕ) :
    (r + 1 : ℝ) * elementary g ps (r + 1) ≤ mass g ps * elementary g ps r := by
  induction ps generalizing r with
  | nil => simp [elementary_nil_succ, mass]
  | cons p ps ih =>
    have hp : 0 ≤ g p := hg p (by simp)
    have htail : ∀ q ∈ ps, 0 ≤ g q := fun q hq => hg q (by simp [hq])
    cases r with
    | zero => simp [elementary_one]
    | succ r =>
      rw [elementary_cons g p ps (r + 1), elementary_cons g p ps r]
      change ((r + 1 : ℕ) + 1 : ℝ) *
          (elementary g ps (r + 1 + 1) + g p * elementary g ps (r + 1)) ≤
        (g p + mass g ps) * (elementary g ps (r + 1) + g p * elementary g ps r)
      have hi1 := ih htail (r + 1)
      have hi0 := mul_le_mul_of_nonneg_left (ih htail r) hp
      have hdiag : 0 ≤ g p * g p * elementary g ps r :=
        mul_nonneg (mul_nonneg hp hp) (elementary_nonneg g ps r htail)
      push_cast at hi1 hi0 ⊢
      nlinarith

theorem factorial_mul_elementary_le_pow (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ p ∈ ps, 0 ≤ g p) (r : ℕ) :
    (r.factorial : ℝ) * elementary g ps r ≤ mass g ps ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hs := elementary_step_le g ps hg r
    calc
      ((r + 1).factorial : ℝ) * elementary g ps (r + 1) =
          (r.factorial : ℝ) * ((r + 1 : ℝ) * elementary g ps (r + 1)) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (r.factorial : ℝ) * (mass g ps * elementary g ps r) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ = mass g ps * ((r.factorial : ℝ) * elementary g ps r) := by ring
      _ ≤ mass g ps * mass g ps ^ r := mul_le_mul_of_nonneg_left ih (mass_nonneg g ps hg)
      _ = mass g ps ^ (r + 1) := by rw [pow_succ]; ring

theorem elementary_le_pow_div_factorial (g : ℕ → ℝ) (ps : List ℕ)
    (hg : ∀ p ∈ ps, 0 ≤ g p) (r : ℕ) :
    elementary g ps r ≤ mass g ps ^ r / (r.factorial : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos r))).mpr
  simpa only [mul_comm] using factorial_mul_elementary_le_pow g ps hg r

/-- A genuine collection of distinct subwords in the band is dominated by
its elementary symmetric sum. This generic helper's nodup premise will be
discharged from the actual first-failure enumeration below. -/
theorem words_mass_le_elementary (g : ℕ → ℝ) (band : List ℕ) (r : ℕ)
    (words : List (List ℕ)) (hn : words.Nodup)
    (hwords : ∀ xs ∈ words, List.Sublist xs band ∧ xs.length = r)
    (hg : ∀ p ∈ band, 0 ≤ g p) :
    (words.map (product g)).sum ≤ elementary g band r := by
  have hsubset : words ⊆ band.sublistsLen r :=
    fun xs hxs => List.mem_sublistsLen.mpr (hwords xs hxs)
  obtain ⟨l, hl, hsub⟩ := List.subperm_iff.mp (hn.subperm hsubset)
  calc
    (words.map (product g)).sum ≤ (l.map (product g)).sum := by
      apply (hsub.map (product g)).sum_le_sum
      intro x hx
      obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
      have hm := (List.mem_sublistsLen.mp (hl.mem_iff.mp hxs)).1
      exact product_nonneg g xs (fun p hp => hg p (hm.subset hp))
    _ = elementary g band r := (hl.map (product g)).sum_eq

def boundaryWords (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ) (r : ℕ) :
    List (List ℕ) :=
  ((firstFailures upper A stem ps).map Prod.fst).filter (fun xs => decide (xs.length = r))

theorem boundaryWords_nodup (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ)
    (r : ℕ) (hn : ps.Nodup) : (boundaryWords upper A stem ps r).Nodup :=
  (firstFailures_selected_nodup upper A stem ps hn).filter _

theorem boundary_mass_eq_record_sum (upper : Bool) (A : List ℕ → Prop)
    (stem ps : List ℕ) (r : ℕ) (g : ℕ → ℝ) :
    ((boundaryWords upper A stem ps r).map (product g)).sum =
      (((firstFailures upper A stem ps).filter (fun e => decide (e.1.length = r))).map
        (fun e => product g e.1)).sum := by
  have hmap (l : List (List ℕ × List ℕ)) :
      (l.map Prod.fst).filter (fun xs => decide (xs.length = r)) =
        (l.filter (fun e => decide (e.1.length = r))).map Prod.fst := by
    induction l with
    | nil => rfl
    | cons e es ih => by_cases he : e.1.length = r <;> simp [he, ih]
  unfold boundaryWords
  rw [hmap]
  simp only [List.map_map, Function.comp_def]

/-- Actual length-r first-failure mass in an ordered band. The only band
premise is literal containment as a sublist; multiplicity is proved here. -/
theorem firstFailure_mass_le_pow_div_factorial
    (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ) (hn : ps.Nodup)
    (r : ℕ) (band : List ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ band, 0 ≤ g p)
    (hband : ∀ e ∈ firstFailures upper A stem ps, e.1.length = r → List.Sublist e.1 band) :
    ((boundaryWords upper A stem ps r).map (product g)).sum ≤
      mass g band ^ r / (r.factorial : ℝ) := by
  apply le_trans (words_mass_le_elementary g band r _ (boundaryWords_nodup upper A stem ps r hn) _ hg)
    (elementary_le_pow_div_factorial g band hg r)
  intro xs hxs
  obtain ⟨hm, hlen⟩ := List.mem_filter.mp hxs
  have hlen' : xs.length = r := of_decide_eq_true hlen
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  exact ⟨hband e he hlen', hlen'⟩

theorem sublist_filter_of_forall {xs ps : List ℕ} (hsub : List.Sublist xs ps)
    (Q : ℕ → Bool) (hall : ∀ p ∈ xs, Q p = true) : List.Sublist xs (ps.filter Q) := by
  have h := hsub.filter Q
  rwa [List.filter_eq_self.mpr hall] at h

/-- Direct filtered-band form for the geometric cutoff supplier. -/
theorem firstFailure_mass_le_filtered_band
    (upper : Bool) (A : List ℕ → Prop) (stem ps : List ℕ) (hn : ps.Nodup)
    (r : ℕ) (Q : ℕ → Bool) (g : ℕ → ℝ)
    (hg : ∀ p ∈ ps.filter Q, 0 ≤ g p)
    (hband : ∀ e ∈ firstFailures upper A stem ps, e.1.length = r →
      ∀ p ∈ e.1, Q p = true) :
    ((boundaryWords upper A stem ps r).map (product g)).sum ≤
      mass g (ps.filter Q) ^ r / (r.factorial : ℝ) := by
  apply firstFailure_mass_le_pow_div_factorial upper A stem ps hn r (ps.filter Q) g hg
  intro e he hr
  have hs : List.Sublist e.1 ps := List.mem_sublists'.mp
    ((firstFailures_selected_sublist upper A stem ps).subset (List.mem_map.mpr ⟨e, he, rfl⟩))
  exact sublist_filter_of_forall hs Q (hband e he hr)

end
end PrimeGapNormality.Prime.CoreBetaBoundaryMass
