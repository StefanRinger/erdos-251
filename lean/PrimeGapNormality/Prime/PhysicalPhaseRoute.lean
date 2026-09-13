import PrimeGapNormality.Prime.StatisticalCriterion

/-!
# G0d — infinite phase on the physical window, then index means

`UniformOrbitTail` at a **fixed** profile with `∀ ε>0, ∀ n, tail ≤ ε`
forces the series remainder to vanish identically. That contract is
unusable for `P = X` and genuine prime gaps (`OrbitIndexProfile`).

Replacement order (paper end-consumer, R105/01):

1. relative-rank truncated phase on the physical window `I_X`;
2. remove the span cut by its own local short indicator;
3. restore the infinite phase on **that same window** via a bounded
   character remainder (not a pointwise raw tail);
4. pass to Cesàro means of one fixed sequence (`IndexPassageD`);
5. period-step recurrence and `positiveProgression_sequenceWeyl`.

This route does **not** use `hU` or `hmatch`, and does not compare
`L_X` with `L_(p_n)`. Do not allocate further work to those adapters.

R105 G0d.

Source: `rounds/round105/00_grok_repair_priorities.md` G0d;
`rounds/round105/01_gpt_endchain_audit.md` Checkpoint 1 and §4.
Contract: API
Audit: GREEN
-/

open Finset Filter Polynomial
open scoped Topology

namespace PrimeGapNormality.Prime

/-- Bounded character remainder on the physical window, one `L_X`. -/
def PhysicalPhaseRemainderVanishing (a : ℕ → ℕ) (P : ℕ → ℝ[X]) (B : ℕ)
    (L : ℕ → ℕ) : Prop :=
  Tendsto (fun X : ℕ =>
      windowAvgReal (seqWindow a X) fun n =>
        ‖e (seqGapPolyTail a P B n) -
            e (seqGapPolyTailTrunc a P B (L X) n)‖)
    atTop (𝓝 0)

/-- Profile form: `L_X = stdProfileL ρ (G X)`, independent of `n`. -/
def PhysicalPhaseRemainderVanishingProfile (a : ℕ → ℕ) (P : ℕ → ℝ[X])
    (B : ℕ) (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  PhysicalPhaseRemainderVanishing a P B fun X => stdProfileL ρ (G X)

/-- Physical-window means of a bounded sequence vanish. -/
def PhysicalWindowMeanVanishing (a : ℕ → ℕ) (f : ℕ → ℂ) : Prop :=
  Tendsto (fun X : ℕ => windowAvg (seqWindow a X) f) atTop (𝓝 0)

/-- Cesàro means of the same sequence. No profile parameter. -/
def CesaroMeanVanishing (f : ℕ → ℂ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ range N, f n) / N) atTop (𝓝 0)

/-- G0d step 4: physical window → index Cesàro, from `StrictMono` and `D`.
Named contract; proved in the C leaf, not here. -/
def PhysicalWindowToCesaro (a : ℕ → ℕ) : Prop :=
  StrictMono a →
    IndexPassageD a →
      ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
        PhysicalWindowMeanVanishing a f → CesaroMeanVanishing f

/-- Marker: the old uniform pointwise tail is not an input of this route. -/
def AvoidUniformOrbitTail : Prop := True

end PrimeGapNormality.Prime
