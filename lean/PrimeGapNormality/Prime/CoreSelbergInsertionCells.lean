import PrimeGapNormality.Prime.FiniteSelbergAsymptoticCap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Positivity

/-!
Finite cells for positive insertion majorization from the actual Selberg sieve cap.
The forbidden residue classes and the location of the integer interval are
arbitrary. Cell counting is proved from the sieve, not supplied as a grid law.
-/

namespace PrimeGapNormality.Prime.CoreSelberg

open Finset Filter
open MeasureTheory (volume)
open scoped Topology NNReal

noncomputable section

def AvoidsResidues (E : Finset ℕ) (R : ℕ) : Prop :=
  ∀ p ∈ Nat.primesLE R, ∃ c : ℕ, ∀ n ∈ E, n % p ≠ c % p

theorem AvoidsResidues.mono {E F : Finset ℕ} {R : ℕ}
    (hE : AvoidsResidues E R) (hF : F ⊆ E) : AvoidsResidues F R := by
  intro p hp
  obtain ⟨c, hc⟩ := hE p hp
  exact ⟨c, fun n hn ↦ hc n (hF hn)⟩

/-- Translating the candidate set translates its forbidden classes as well. -/
theorem avoidsResidues_translate {E : Finset ℕ} {R a : ℕ}
    (hE : AvoidsResidues E R) (ha : ∀ n ∈ E, a ≤ n) :
    AvoidsResidues (E.image (fun n ↦ n - a)) R := by
  intro p hp
  obtain ⟨c, hc⟩ := hE p hp
  have hp0 : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) (Nat.two_le_of_mem_primesLE hp)
  let c' : ℕ := p - a % p + c
  have hshift : (a + c') % p = c % p := by
    calc
      (a + c') % p = (a % p + c') % p := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = (p + c) % p := by
        congr 1
        have hamod := Nat.mod_lt a hp0
        dsimp [c']
        omega
      _ = c % p := by simp
  refine ⟨c', ?_⟩
  intro m hm
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
  intro hbad
  apply hc n hn
  have hnid : n = a + (n - a) := by have := ha n hn; omega
  calc
    n % p = (a + (n - a)) % p := by rw [← hnid]
    _ = (a + c') % p := Nat.ModEq.add_left a hbad
    _ = c % p := hshift

/-- The finite Selberg cap on an arbitrary translated integer interval. -/
theorem translated_card_le {E : Finset ℕ} {a H R : ℕ}
    (hR : 1 ≤ R) (hRH : R ≤ H) (hE : E ⊆ Ioc a (a + H))
    (havoid : AvoidsResidues E R) :
    (E.card : ℝ) ≤ (H : ℝ) / selbergJR R + (R : ℝ) ^ 2 := by
  let F := E.image (fun n ↦ n - a)
  have hleft : ∀ n ∈ E, a ≤ n := fun n hn ↦ (Finset.mem_Ioc.mp (hE hn)).1.le
  have hF : F ⊆ Icc 1 H := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hi := Finset.mem_Ioc.mp (hE hn)
    exact Finset.mem_Icc.mpr (by omega)
  have hcard : F.card = E.card := by
    apply Finset.card_image_of_injOn
    intro n hn m hm hnm
    change n - a = m - a at hnm
    have hna := hleft n hn
    have hma := hleft m hm
    omega
  have hcap := finiteSelberg_card_le hR hRH hF (avoidsResidues_translate havoid hleft)
  rwa [hcard] at hcap

/-- Integrating the Lipschitz inequality on a cell controls every sample by
the cell average. This is the finite Riemann majorization step. -/
theorem lipschitz_cell_majorant {ι : Type*} (E : Finset ι) (z : ι → ℝ)
    (f : ℝ → ℝ) {K : ℝ≥0} (hLip : LipschitzWith K f) (l δ cap : ℝ)
    (hδ : 0 < δ) (hz : ∀ n ∈ E, z n ∈ Set.Icc l (l + δ))
    (hf : ∀ t ∈ Set.Icc l (l + δ), 0 ≤ f t) (hcard : (E.card : ℝ) ≤ cap) :
    δ * (∑ n ∈ E, f (z n)) ≤
      cap * ((∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2) := by
  have hl : l ≤ l + δ := by linarith
  have hint : IntervalIntegrable f volume l (l + δ) :=
    hLip.continuous.intervalIntegrable l (l + δ)
  have hpoint : ∀ n ∈ E, δ * f (z n) ≤
      (∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2 := by
    intro n hn
    have hncell := hz n hn
    have hle : ∀ t ∈ Set.Icc l (l + δ), f (z n) ≤ f t + (K : ℝ) * δ := by
      intro t ht
      have hdist : dist (z n) t ≤ δ := by
        rw [Real.dist_eq]
        apply abs_le.mpr
        constructor <;> linarith [ht.1, ht.2, hncell.1, hncell.2]
      exact (hLip.le_add_mul (z n) t).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
    have hmono := intervalIntegral.integral_mono_on hl
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ f (z n)) volume l (l + δ))
      (hint.add intervalIntegrable_const) hle
    calc
      δ * f (z n) = ∫ t in l..(l + δ), f (z n) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ t in l..(l + δ), f t + (K : ℝ) * δ := hmono
      _ = (∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2 := by
        rw [intervalIntegral.integral_add hint intervalIntegrable_const,
          intervalIntegral.integral_const]
        simp only [add_sub_cancel_left, smul_eq_mul]
        ring
  have hnon : 0 ≤ (∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2 :=
    add_nonneg (intervalIntegral.integral_nonneg hl hf) (mul_nonneg K.coe_nonneg (sq_nonneg δ))
  calc
    δ * (∑ n ∈ E, f (z n)) = ∑ n ∈ E, δ * f (z n) := Finset.mul_sum ..
    _ ≤ ∑ _n ∈ E, ((∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2) :=
      Finset.sum_le_sum hpoint
    _ = (E.card : ℝ) * ((∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2) := by simp <;> ring
    _ ≤ cap * ((∫ t in l..(l + δ), f t) + (K : ℝ) * δ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hnon

/-- Index of the right-closed length-`H` cell above the integer anchor `a`. -/
def cellIndex (a H n : ℕ) : ℕ := (n - a - 1) / H

def cell (E : Finset ℕ) (a H j : ℕ) : Finset ℕ :=
  E.filter fun n ↦ cellIndex a H n = j

theorem cell_subset_interval {E : Finset ℕ} {a H j : ℕ} (hH : 0 < H)
    (ha : ∀ n ∈ E, a < n) : cell E a H j ⊆ Ioc (a + j * H) (a + j * H + H) := by
  intro n hn
  obtain ⟨hnE, hnidx⟩ := Finset.mem_filter.mp hn
  have hna := ha n hnE
  have hdiv := Nat.div_add_mod (n - a - 1) H
  have hmod := Nat.mod_lt (n - a - 1) hH
  change (n - a - 1) / H = j at hnidx
  rw [hnidx, Nat.mul_comm H j] at hdiv
  exact Finset.mem_Ioc.mpr (by omega)

theorem cellIndex_lt {E : Finset ℕ} {a H M : ℕ} (hH : 0 < H)
    (hE : E ⊆ Ioc a (a + M * H)) {n : ℕ} (hn : n ∈ E) :
    cellIndex a H n < M := by
  have hi := Finset.mem_Ioc.mp (hE hn)
  apply (Nat.div_lt_iff_lt_mul hH).2
  omega

/-- Every cell count in this mesh is supplied by the actual Selberg cap. -/
theorem cell_card_le {E : Finset ℕ} {a H R j : ℕ}
    (hR : 1 ≤ R) (hRH : R ≤ H) (ha : ∀ n ∈ E, a < n)
    (havoid : AvoidsResidues E R) :
    ((cell E a H j).card : ℝ) ≤ (H : ℝ) / selbergJR R + (R : ℝ) ^ 2 := by
  have hH : 0 < H := lt_of_lt_of_le (by omega : 0 < R) hRH
  exact translated_card_le hR hRH (cell_subset_interval hH ha)
    (havoid.mono (Finset.filter_subset _ _))

end

end PrimeGapNormality.Prime.CoreSelberg
