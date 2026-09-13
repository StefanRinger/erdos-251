import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Clean finite residue-counting lemmas for the digital window adapter.  This
file deliberately has no dependency on the legacy sieve probability stack.
-/

open Finset

namespace PrimeGapNormality.Prime

/-- At most `h / p + 1` offsets in a length-`h` range occupy one residue
class modulo a positive `p`. -/
theorem core_card_range_add_mod_le (a h p r : ℕ) (hp : 0 < p) :
    ((range h).filter fun j ↦ (a + j) % p = r % p).card ≤ h / p + 1 := by
  let s := (range h).filter fun j ↦ (a + j) % p = r % p
  let f : ℕ → ℕ := fun j ↦ j / p
  have hinj : Set.InjOn f s := by
    intro j hj j' hj' hf
    have hs := (mem_filter.mp hj).2
    have hs' := (mem_filter.mp hj').2
    have hcong : a % p + j % p ≡ a % p + j' % p [MOD p] := by
      change (a % p + j % p) % p = (a % p + j' % p) % p
      rw [← Nat.add_mod, ← Nat.add_mod, hs, hs']
    have hmod : j % p = j' % p := by
      simpa only [Nat.ModEq, Nat.mod_mod] using
        (Nat.ModEq.add_left_cancel' (a % p) hcong)
    have hjdec := (Nat.div_add_mod j p).symm
    have hj'dec := (Nat.div_add_mod j' p).symm
    rw [hjdec, hj'dec, show j / p = j' / p from hf, hmod]
  have himg : s.image f ⊆ range (h / p + 1) := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    have hjlt : j < h := mem_range.mp (mem_filter.mp hj).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hjlt)))
  have hcard : (s.image f).card = s.card := card_image_of_injOn hinj
  have hle : (s.image f).card ≤ (range (h / p + 1)).card := card_le_card himg
  have : s.card ≤ h / p + 1 := by
    simpa only [hcard, card_range] using hle
  simpa only [s] using this

/-- At least the complete `h / p` blocks contribute one point to each
residue class. -/
theorem core_card_range_add_mod_ge (a h p r : ℕ) (hp : 0 < p) :
    h / p ≤ ((range h).filter fun j ↦ (a + j) % p = r % p).card := by
  have hinj : Set.InjOn (fun j ↦ (a + j) % p) (range p : Set ℕ) := by
    intro j hj j' hj' heq
    have hjlt := mem_range.mp hj
    have hj'lt := mem_range.mp hj'
    have hcong : a + j ≡ a + j' [MOD p] := heq
    have hjj : j ≡ j' [MOD p] := Nat.ModEq.add_left_cancel' a hcong
    have hjmod : j % p = j := Nat.mod_eq_of_lt hjlt
    have hj'mod : j' % p = j' := Nat.mod_eq_of_lt hj'lt
    simpa only [Nat.ModEq, hjmod, hj'mod] using hjj
  have himg : (range p).image (fun j ↦ (a + j) % p) ⊆ range p := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    exact mem_range.mpr (Nat.mod_lt _ hp)
  have hcard : ((range p).image (fun j ↦ (a + j) % p)).card = p := by
    rw [card_image_of_injOn hinj, card_range]
  have heqImage : (range p).image (fun j ↦ (a + j) % p) = range p :=
    eq_of_subset_of_card_le himg (by rw [hcard, card_range])
  have hr : r % p ∈ range p := mem_range.mpr (Nat.mod_lt r hp)
  have hr' : r % p ∈ (range p).image (fun j ↦ (a + j) % p) := by
    rwa [heqImage]
  obtain ⟨j₀, hj₀, hj₀eq⟩ := mem_image.mp hr'
  let f : ℕ → ℕ := fun q ↦ q * p + j₀
  have hinjf : Set.InjOn f (range (h / p) : Set ℕ) := by
    intro q hq q' hq' heq
    have hmul : q * p = q' * p := by
      exact Nat.add_right_cancel (by simpa only [f] using heq)
    exact Nat.eq_of_mul_eq_mul_right hp hmul
  have himgf : (range (h / p)).image f ⊆
      (range h).filter (fun j ↦ (a + j) % p = r % p) := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hj
    have hqlt := mem_range.mp hq
    have hj₀lt := mem_range.mp hj₀
    have hjlt : q * p + j₀ < h := by
      have hblocks : (q + 1) * p ≤ (h / p) * p :=
        Nat.mul_le_mul_right p (Nat.succ_le_of_lt hqlt)
      have hfloor : (h / p) * p ≤ h := by
        simpa only [Nat.mul_comm] using Nat.mul_div_le h p
      have hinside : q * p + j₀ + 1 ≤ (q + 1) * p := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left (Nat.succ_le_of_lt hj₀lt) _
      omega
    have hmod : (a + (q * p + j₀)) % p = r % p := by
      have hreorder : a + (q * p + j₀) = (a + j₀) + q * p := by ring
      rw [hreorder, Nat.add_mul_mod_self_right, hj₀eq]
    exact mem_filter.mpr ⟨mem_range.mpr hjlt, hmod⟩
  have hcardf : ((range (h / p)).image f).card = h / p := by
    rw [card_image_of_injOn hinjf, card_range]
  have hle := card_le_card himgf
  simpa only [hcardf] using hle

/-- Translating offsets by `a` identifies the range count with the literal
half-open interval count. -/
theorem core_card_Ico_mod_eq_card_range (a h p r : ℕ) :
    ((Ico a (a + h)).filter fun n ↦ n % p = r % p).card =
      ((range h).filter fun j ↦ (a + j) % p = r % p).card := by
  let e : ℕ ↪ ℕ := ⟨fun j ↦ a + j, add_right_injective a⟩
  have himage :
      ((range h).filter (fun j ↦ (a + j) % p = r % p)).map e =
        (Ico a (a + h)).filter (fun n ↦ n % p = r % p) := by
    ext n
    simp only [mem_map, mem_filter, mem_range, mem_Ico, e,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨j, ⟨hj, heq⟩, rfl⟩
      exact ⟨⟨Nat.le_add_right a j, Nat.add_lt_add_left hj a⟩, heq⟩
    · rintro ⟨⟨hle, hlt⟩, heq⟩
      refine ⟨n - a, ⟨?_, ?_⟩, ?_⟩
      · omega
      · rwa [Nat.add_sub_cancel' hle]
      · exact Nat.add_sub_cancel' hle
  rw [← himage, card_map]

theorem core_card_Ico_mod_le (a h p r : ℕ) (hp : 0 < p) :
    ((Ico a (a + h)).filter fun n ↦ n % p = r % p).card ≤ h / p + 1 := by
  rw [core_card_Ico_mod_eq_card_range]
  exact core_card_range_add_mod_le a h p r hp

theorem core_card_Ico_mod_ge (a h p r : ℕ) (hp : 0 < p) :
    h / p ≤ ((Ico a (a + h)).filter fun n ↦ n % p = r % p).card := by
  rw [core_card_Ico_mod_eq_card_range]
  exact core_card_range_add_mod_ge a h p r hp

/-- A residue class in an interval differs from its rational density by at
most one point. -/
theorem core_abs_card_Ico_mod_sub_div (a h p r : ℕ) (hp : 0 < p) :
    |(((Ico a (a + h)).filter fun n ↦ n % p = r % p).card : ℝ) -
        (h : ℝ) / p| ≤ 1 := by
  have hle := core_card_Ico_mod_le a h p r hp
  have hge := core_card_Ico_mod_ge a h p r hp
  let C : ℝ := (((Ico a (a + h)).filter fun n ↦ n % p = r % p).card : ℝ)
  let Q : ℝ := (h / p : ℕ)
  have hCge : Q ≤ C := Nat.cast_le.mpr hge
  have hCle : C ≤ Q + 1 := by
    have hcast : C ≤ ((h / p + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
    simpa only [Q, Nat.cast_add, Nat.cast_one] using hcast
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hdiv : Q ≤ (h : ℝ) / p := by
    have hmulNat : p * (h / p) ≤ h := by
      simpa only [Nat.mul_comm] using Nat.mul_div_le h p
    have hmul : (p : ℝ) * (h / p : ℕ) ≤ h := by exact_mod_cast hmulNat
    exact (le_div_iff₀ hp0).mpr (by simpa only [Q, mul_comm] using hmul)
  have hfrac : (h : ℝ) / p < Q + 1 := by
    have hdecompNat : h = p * (h / p) + h % p := by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod h p).symm
    have hdecomp : (h : ℝ) = (p : ℝ) * (h / p : ℕ) + (h % p : ℕ) := by
      exact_mod_cast hdecompNat
    have hmod : ((h % p : ℕ) : ℝ) < p := Nat.cast_lt.mpr (Nat.mod_lt h hp)
    have hpne : (p : ℝ) ≠ 0 := hp0.ne'
    have heq : (h : ℝ) / p = Q + (h % p : ℕ) / p := by
      rw [hdecomp]
      dsimp only [Q]
      field_simp [hpne]
    rw [heq]
    have hratio : ((h % p : ℕ) : ℝ) / p < 1 := (div_lt_one hp0).mpr hmod
    linarith
  apply abs_le.mpr
  constructor <;> dsimp only [C, Q] at * <;> linarith

end PrimeGapNormality.Prime
