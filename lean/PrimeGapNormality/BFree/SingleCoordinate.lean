import PrimeGapNormality.BFree.Definitions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One unused exclusion coordinate: finite character algebra and period choice

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §§3–4.1 (5)–(11);
`rounds/round89/03_gpt_core_audit_and_lean_architecture.md` §1.
Contract: C1
Audit: GREEN
-/

namespace PrimeGapNormality.BFree

/-- Exact squared identity behind (6).

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (6).
Contract: C1
Audit: GREEN -/
theorem bernoulli_char_norm_sq {v : ℝ} {lam : ℂ} (hlam : ‖lam‖ = 1) :
    ‖((1 : ℂ) - ↑v + ↑v * lam)‖ ^ 2 =
      1 - v * (1 - v) * ‖(1 : ℂ) - lam‖ ^ 2 := by
  have hlamsq : lam.re ^ 2 + lam.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq lam
    rw [Complex.normSq_apply] at this
    simp [← sq, hlam] at this
    exact this
  have hz : ‖((1 : ℂ) - ↑v + ↑v * lam)‖ ^ 2 =
      ((1 - v + v * lam.re) ^ 2 + (v * lam.im) ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have h1 : ‖(1 : ℂ) - lam‖ ^ 2 = 2 - 2 * lam.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    linarith [hlamsq]
  have hexp : (1 - v + v * lam.re) ^ 2 + (v * lam.im) ^ 2 =
      (1 - v) ^ 2 + 2 * (1 - v) * v * lam.re + v ^ 2 := by
    have h : (1 - v + v * lam.re) ^ 2 + (v * lam.im) ^ 2 =
        (1 - v) ^ 2 + 2 * (1 - v) * v * lam.re +
          v ^ 2 * (lam.re ^ 2 + lam.im ^ 2) := by ring
    simpa [hlamsq] using h
  rw [hz, h1, hexp]
  ring

/-- Linear bound from the squared identity; requires `v ≤ 1/2`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (6);
`03` squared comparison.
Contract: C1
Audit: GREEN -/
theorem bernoulli_char_norm_le {v : ℝ} {lam : ℂ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2)
    (hlam : ‖lam‖ = 1) :
    ‖((1 : ℂ) - ↑v + ↑v * lam)‖ ≤ 1 - v * ‖(1 : ℂ) - lam‖ ^ 2 / 4 := by
  set s := ‖(1 : ℂ) - lam‖ ^ 2
  have hs0 : 0 ≤ s := sq_nonneg _
  have hs4 : s ≤ 4 := by
    have hnm : ‖(1 : ℂ) - lam‖ ≤ 2 := by
      have := norm_sub_le (1 : ℂ) lam
      simp [hlam] at this
      linarith
    have hsq : ‖(1 : ℂ) - lam‖ ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr hnm
    have : (2 : ℝ) ^ 2 = 4 := by norm_num
    exact this ▸ hsq
  have hL := bernoulli_char_norm_sq (v := v) (lam := lam) hlam
  have hR0 : 0 ≤ 1 - v * s / 4 := by
    have : v * s / 4 ≤ (1 / 2 : ℝ) * 4 / 4 := by
      have : v * s ≤ (1 / 2) * 4 := mul_le_mul hv hs4 hs0 (by norm_num)
      linarith
    linarith
  have hL0 : 0 ≤ ‖((1 : ℂ) - ↑v + ↑v * lam)‖ := norm_nonneg _
  have hdiff :
      (1 - v * s / 4) ^ 2 - ‖((1 : ℂ) - ↑v + ↑v * lam)‖ ^ 2 =
        v * s * (1 / 2 - v) + v ^ 2 * s ^ 2 / 16 := by
    rw [hL]
    ring
  have hsq : ‖((1 : ℂ) - ↑v + ↑v * lam)‖ ^ 2 ≤ (1 - v * s / 4) ^ 2 := by
    have : 0 ≤ v * s * (1 / 2 - v) + v ^ 2 * s ^ 2 / 16 := by
      have : 0 ≤ 1 / 2 - v := by linarith [hv]
      positivity
    linarith [hdiff]
  exact (sq_le_sq₀ hL0 hR0).mp hsq

/-- Adaptive window `H = W ⌊q / (4W)⌋`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (11).
Contract: C1
Audit: GREEN -/
def adaptedWindow (W q : ℕ) : ℕ :=
  W * (q / (4 * W))

theorem adaptedWindow_spec {W q : ℕ} (hW : 0 < W) (hq : 8 * W ≤ q) :
    W ∣ adaptedWindow W q ∧
      q / 8 ≤ adaptedWindow W q ∧
      adaptedWindow W q ≤ q / 4 ∧
      adaptedWindow W q < q ∧
      q ≤ 8 * adaptedWindow W q ∧
      4 * adaptedWindow W q ≤ q := by
  have h4W : 0 < 4 * W := Nat.mul_pos (by decide) hW
  have hqpos : 0 < q :=
    lt_of_lt_of_le (Nat.mul_pos (by decide : 0 < 8) hW) hq
  have h4Wle : 4 * W ≤ q :=
    le_trans (Nat.mul_le_mul_right W (by decide : 4 ≤ 8)) hq
  have hk : 1 ≤ q / (4 * W) := Nat.div_pos h4Wle h4W
  have h8 : q ≤ 8 * adaptedWindow W q := by
    have hqeq : 4 * W * (q / (4 * W)) + q % (4 * W) = q := Nat.div_add_mod q (4 * W)
    have hrem : q % (4 * W) ≤ 4 * W * (q / (4 * W)) :=
      (Nat.mod_lt q h4W).le.trans (Nat.le_mul_of_pos_right (4 * W) hk)
    calc
      q = 4 * W * (q / (4 * W)) + q % (4 * W) := hqeq.symm
      _ ≤ 4 * W * (q / (4 * W)) + 4 * W * (q / (4 * W)) := Nat.add_le_add_left hrem _
      _ = 8 * (W * (q / (4 * W))) := by ring
      _ = 8 * adaptedWindow W q := by rw [adaptedWindow]
  have h4 : 4 * adaptedWindow W q ≤ q := by
    simpa [adaptedWindow, mul_assoc] using Nat.mul_div_le q (4 * W)
  have hle : adaptedWindow W q ≤ q / 4 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < (4 : ℕ))]
    simpa [mul_comm] using h4
  refine ⟨Nat.dvd_mul_right W (q / (4 * W)), Nat.div_le_of_le_mul h8, hle,
    lt_of_le_of_lt hle (Nat.div_lt_self hqpos (by decide : 1 < 4)), h8, h4⟩

/-- Real comparison for the same window. Nat division `q / 8 ≤ H` does not
by itself give the real bound used in `E v ≥ ρ / 8`.

Source: `rounds/round92/01_gpt_positive_integer_carry.md` (3.5), (3.10);
`rounds/round92/05_grok_positive_carry_update.md` §3.B.
Contract: C1
Audit: GREEN -/
theorem adaptedWindow_real {W q : ℕ} (hW : 0 < W) (hq : 8 * W ≤ q) :
    (q : ℝ) / 8 ≤ adaptedWindow W q ∧
      (adaptedWindow W q : ℝ) ≤ (q : ℝ) / 4 := by
  have hspec := adaptedWindow_spec hW hq
  have h8 : (q : ℝ) ≤ 8 * (adaptedWindow W q : ℝ) := by
    exact_mod_cast hspec.2.2.2.2.1
  have h4 : 4 * (adaptedWindow W q : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hspec.2.2.2.2.2
  constructor
  · have h8pos : (0 : ℝ) < 8 := by norm_num
    exact (div_le_iff₀ h8pos).mpr (by linarith)
  · have h4pos : (0 : ℝ) < 4 := by norm_num
    exact (le_div_iff₀ h4pos).mpr (by linarith [mul_comm (adaptedWindow W q : ℝ) (4 : ℝ)])

/-- Distinct candidate times in a window of length `H < q` have distinct residues mod `q`.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` §3.
Contract: C1
Audit: GREEN -/
theorem candidate_residues_injective {q H : ℕ} (hH : H < q) {j k : ℕ}
    (hj : j < H) (hk : k < H) (heq : j % q = k % q) : j = k := by
  rw [Nat.mod_eq_of_lt (hj.trans hH), Nat.mod_eq_of_lt (hk.trans hH)] at heq
  exact heq

/-- Empty product period is one.

Source: `rounds/round89/01_gpt_bfree_single_coordinate.md` (11).
Contract: C1
Audit: GREEN -/
theorem adaptedWindow_empty_period {q : ℕ} (_hq : 8 ≤ q) :
    adaptedWindow 1 q = q / 4 := by
  simp [adaptedWindow]

end PrimeGapNormality.BFree
