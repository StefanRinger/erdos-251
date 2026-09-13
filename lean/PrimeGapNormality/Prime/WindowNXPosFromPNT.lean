import PrimeGapNormality.Prime.GapTailLogKuperberg

/-!
# Eventual `0 < windowNX` from qualitative PNT density

Progress: drop the calibration binder `∀ᶠ X, 0 < windowNX X`.

Lake-green `GapTailLogKuperberg.tendsto_windowNX_div_of_primeCountingAsymp`
gives `|I_X| / (X / log X) → 1`. Combined with `X / log X → ∞`, the
window count itself tends to `∞`, hence is eventually positive.

Does **not** import MixZeta, ExactRootWindowClose,
RootedCutoffTypicalOsc, TypicalOscSlotWidth, TypicalOscFibreAvg,
FibreSlotFromProfile, Weyl leaves, or CrtMixtureTransfer.

Does **not** claim HL calibration, off-band, Bonferroni, typical
osc, or `hcut`. `G(X) = X` is not the remainder scale (`windowG`,
not linear Chebyshev). Bertrand pointwise positivity
(`windowNX_pos_of_pos`) is a different lemma; this leaf uses the
PNT density. No MixZeta.

**Compiled.**
1. `Tendsto (fun X => (windowNX X : ℝ)) atTop atTop` from
   `PrimeCountingAsymp` (ratio → 1 and `X / log X → ∞`).
2. `∀ᶠ X, 0 < windowNX X` from that, and from `KuperbergConj13`
   via `primeCountingAsymp_of_kuperberg`.

**Not compiled.** HL calibration. Off-band. Bonferroni. Typical
osc. `hcut`. Kernel close.

**Theorem versus remaining hypothesis**

| Item | Status |
|---|---|
| `|I_X| / (X / log X) → 1` | theorem (`tendsto_windowNX_div_of_primeCountingAsymp`) |
| `X / log X → ∞` | theorem (this leaf) |
| `windowNX → ∞` from `PrimeCountingAsymp` | theorem |
| `∀ᶠ X, 0 < windowNX` from `PrimeCountingAsymp` | theorem |
| same two from `KuperbergConj13` | theorem (`primeCountingAsymp_of_kuperberg`) |
| `PrimeCountingAsymp` / `KuperbergConj13` | remains (analytic input) |
| HL calibration `q_H = M_X/N_X` | not claimed |
| off-band / Bonferroni / typical osc / `hcut` | not claimed |
| Chebyshev / `G(X) = X` remainder scale | not used |

Does not claim the kernel is closed.

Source: `GapTailLogKuperberg.tendsto_windowNX_div_of_primeCountingAsymp`;
`SingletonLi.primeCountingAsymp_of_kuperberg`.
Contract: API
-/

open Filter
open scoped Topology

namespace PrimeGapNormality.Prime

noncomputable section

/-! ### `X / log X → ∞` -/

private theorem tendsto_log_div_self :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
  exact h0.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_nat_div_log :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop, Real.log n / (n : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1 : ℝ) < n :=
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) (Nat.cast_le.mpr hn)
    have hn0 : (0 : ℝ) < n :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (Nat.cast_le.mpr hn)
    exact div_pos (Real.log_pos hn1) hn0
  have hwithin :
      Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_log_div_self, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hwithin
  refine hinv.congr fun n => ?_
  simp only [Function.comp_apply]
  exact inv_div (Real.log (n : ℝ)) (n : ℝ)

/-! ### `windowNX → ∞` and eventual positivity from PNT -/

/-- Dyadic window count `N_X → ∞` from `|I_X| ∼ X / log X`.
Not the linear Chebyshev scale `G(X) = X`. -/
theorem tendsto_windowNX_atTop_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    Tendsto (fun X : ℕ => (windowNX X : ℝ)) atTop atTop := by
  have hratio := tendsto_windowNX_div_of_primeCountingAsymp hπ
  have hden := tendsto_nat_div_log
  exact (hratio.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hden).congr'
    (EventuallyEq.div_mul_cancel_atTop hden)

/-- Calibration binder `∀ᶠ X, 0 < windowNX X` from qualitative PNT.
Does not use Bertrand. -/
theorem eventually_windowNX_pos_of_primeCountingAsymp
    (hπ : PrimeCountingAsymp) :
    ∀ᶠ X : ℕ in atTop, 0 < windowNX X := by
  filter_upwards [
    (tendsto_windowNX_atTop_of_primeCountingAsymp hπ).eventually_gt_atTop
      (0 : ℝ)] with X hx
  exact Nat.cast_pos.mp hx

/-! ### Same two from Kuperberg 1.3 -/

theorem tendsto_windowNX_atTop_of_kuperberg (hK : KuperbergConj13) :
    Tendsto (fun X : ℕ => (windowNX X : ℝ)) atTop atTop :=
  tendsto_windowNX_atTop_of_primeCountingAsymp
    (primeCountingAsymp_of_kuperberg hK)

theorem eventually_windowNX_pos_of_kuperberg (hK : KuperbergConj13) :
    ∀ᶠ X : ℕ in atTop, 0 < windowNX X :=
  eventually_windowNX_pos_of_primeCountingAsymp
    (primeCountingAsymp_of_kuperberg hK)

end

end PrimeGapNormality.Prime
