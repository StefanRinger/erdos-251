import PrimeGapNormality.Prime.ModelMoments
import PrimeGapNormality.Prime.EulerProd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic

/-!
# Model good event and factorial-moment band (v0.3 Lemma B.2)

Finite-space Hoeffding / bounded differences on an independent Bernoulli
product, Bonferroni's first union bound, the `S̄` rounding, and the
abstract combination with `factorialMoment_envelope`.

On the middle good event `θ N₀ ≤ 6 L` of complementary mass
`ε_G ≤ C L exp(-c (log G)^{3/2})`, with the crude bound
`θ N₀ ≤ C₁ L log S̄` everywhere, one has
`Q_j ≤ (12 L)^j / j!` for every previously fixed `a > 0` and
`1 ≤ j ≤ a L + 1` eventually. The envelope `12` is chosen first;
`d₀ > 24e` is not proved here.

Not proved: CRT / neighbouring-Bonferroni cell counts that produce
`N₀ ≤ (1+o(1)) S̄ V(S̄)`, and sieve-cutoff calibration `V(y)⁻¹/G → 1`.
The later Chebyshev exception to `G^4` is not used.

Two mean-value steps give `φ(u) ≤ u²/4`, hence one-sided tails
`exp(-u² / ∑ c_i²)`. The paper's integral remainder `φ(u) ≤ u²/8`
only improves `c_κ`; both yield `(log G)^{3/2}`.

Source: `rounds/round104/13_gpt_paper_v0_3.tex` `lem:moments`,
  Appendix C middle stage and (eq:bd);
`rounds/round104/08_model_moments_without_large_sieve.md` §§3–4.
Contract: API
Audit: GREEN
-/

namespace PrimeGapNormality.Prime

open Filter Finset
open scoped Topology

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-! ### Paper `S̄` rounding -/

/-- Cell width `h = ⌊G⌋`. -/
noncomputable def modelCellWidth (G : ℝ) : ℕ := ⌊G⌋₊

/-- Paper `S = ⌊4 L G⌋`. -/
noncomputable def modelSpan (L : ℕ) (G : ℝ) : ℕ := ⌊(4 : ℝ) * L * G⌋₊

/-- Paper `\overline S = h ⌈4 L G / h⌉` with `h = ⌊G⌋`. -/
noncomputable def modelSpanBar (L : ℕ) (G : ℝ) : ℕ :=
  let h := modelCellWidth G
  if h = 0 then 0 else h * ⌈((4 : ℝ) * L * G / h)⌉₊

theorem modelCellWidth_pos {G : ℝ} (hG : 1 ≤ G) : 1 ≤ modelCellWidth G :=
  (Nat.one_le_floor_iff G).mpr hG

theorem nat_mul_ceil_div_ge {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (_hx : 0 ≤ x) :
    x ≤ (n : ℝ) * ⌈x / n⌉₊ := by
  have hn0 : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 1) hn)
  have hceil : x / n ≤ ⌈x / n⌉₊ := Nat.le_ceil _
  have := mul_le_mul_of_nonneg_left hceil hn0.le
  rwa [mul_div_cancel₀ x hn0.ne'] at this

theorem nat_mul_ceil_div_lt_add {n : ℕ} {x : ℝ} (hn : 1 ≤ n) (hx : 0 ≤ x) :
    (n : ℝ) * ⌈x / n⌉₊ < x + n := by
  have hn0 : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 1) hn)
  have hceil : (⌈x / n⌉₊ : ℝ) < x / n + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hx hn0.le)
  have := mul_lt_mul_of_pos_left hceil hn0
  have hrew : (n : ℝ) * (x / n + 1) = x + n := by
    field_simp [hn0.ne']
  linarith [this, hrew]

theorem modelSpanBar_eq {L : ℕ} {G : ℝ} (hG : 1 ≤ G) :
    (modelSpanBar L G : ℝ) =
      (modelCellWidth G : ℝ) * ⌈((4 : ℝ) * L * G / modelCellWidth G)⌉₊ := by
  have hpos : 1 ≤ modelCellWidth G := modelCellWidth_pos hG
  have hne : modelCellWidth G ≠ 0 := Nat.ne_zero_of_lt (Nat.succ_le_iff.mp hpos)
  simp [modelSpanBar, hne, Nat.cast_mul]

theorem modelSpan_le_four_mul {L : ℕ} {G : ℝ} (hG : 0 ≤ G) :
    (modelSpan L G : ℝ) ≤ (4 : ℝ) * L * G :=
  Nat.floor_le (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg L)) hG)

theorem modelSpan_le_modelSpanBar {L : ℕ} {G : ℝ} (hG : 1 ≤ G) :
    modelSpan L G ≤ modelSpanBar L G := by
  have h4 : (0 : ℝ) ≤ (4 : ℝ) * L * G :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hG)
  have hcell : 1 ≤ modelCellWidth G := modelCellWidth_pos hG
  have hge := nat_mul_ceil_div_ge (x := (4 : ℝ) * L * G) hcell h4
  have hS := modelSpan_le_four_mul (L := L)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hG)
  have hbar := modelSpanBar_eq (L := L) hG
  have : (modelSpan L G : ℝ) ≤ (modelSpanBar L G : ℝ) :=
    hS.trans (hge.trans (le_of_eq hbar.symm))
  exact_mod_cast this

theorem modelSpanBar_lt_four_add {L : ℕ} {G : ℝ} (hG : 1 ≤ G) :
    (modelSpanBar L G : ℝ) < (4 : ℝ) * L * G + G := by
  have h4 : (0 : ℝ) ≤ (4 : ℝ) * L * G :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hG)
  have hcell : 1 ≤ modelCellWidth G := modelCellWidth_pos hG
  have hlt := nat_mul_ceil_div_lt_add (x := (4 : ℝ) * L * G) hcell h4
  have hbar := modelSpanBar_eq (L := L) hG
  have hh : (modelCellWidth G : ℝ) ≤ G :=
    Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 1) hG)
  have : (modelSpanBar L G : ℝ) < (4 : ℝ) * L * G + modelCellWidth G := by
    rwa [hbar]
  exact this.trans_le (by linarith [hh])

/-- `\overline S ≤ 5 L G` once `1 ≤ L` and `1 ≤ G`. -/
theorem modelSpanBar_le_five_mul {L : ℕ} {G : ℝ} (hL : 1 ≤ L) (hG : 1 ≤ G) :
    (modelSpanBar L G : ℝ) ≤ (5 : ℝ) * L * G := by
  have hlt := modelSpanBar_lt_four_add (L := L) hG
  have hLG : G ≤ (L : ℝ) * G := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hG0 : 0 ≤ G := le_trans (by norm_num : (0 : ℝ) ≤ 1) hG
    simpa using mul_le_mul_of_nonneg_right hL1 hG0
  have hle : (4 : ℝ) * L * G + G ≤ (5 : ℝ) * L * G := by
    have : (4 : ℝ) * L * G + G ≤ (4 : ℝ) * L * G + L * G := by
      linarith [hLG]
    have hring : (4 : ℝ) * L * G + L * G = (5 : ℝ) * L * G := by ring
    rwa [hring] at this
  exact hlt.le.trans hle

/-! ### Exception rate `C L exp(-c (log G)^{3/2})` -/

/-- `(log G)^{3/2} = log G · √(log G)` for `log G ≥ 0`. -/
noncomputable def logThreeHalves (G : ℝ) : ℝ :=
  Real.log G * Real.sqrt (Real.log G)

/-- Middle-stage exception mass, paper `ε_G`. -/
noncomputable def modelExceptionRate (C c L G : ℝ) : ℝ :=
  C * L * Real.exp (-c * logThreeHalves G)

/-- Paper `η = (log G)^{-1/4}`. -/
noncomputable def modelEta (G : ℝ) : ℝ :=
  (Real.sqrt (Real.sqrt (Real.log G)))⁻¹

/-! ### Hoeffding `φ` -/

noncomputable def hoeffdingDen (p u : ℝ) : ℝ :=
  1 - p + p * Real.exp u

noncomputable def hoeffdingPhi (p u : ℝ) : ℝ :=
  -p * u + Real.log (hoeffdingDen p u)

noncomputable def hoeffdingPhiDeriv (p u : ℝ) : ℝ :=
  -p + p * Real.exp u / hoeffdingDen p u

noncomputable def hoeffdingPhiDerivTwo (p u : ℝ) : ℝ :=
  p * (1 - p) * Real.exp u / hoeffdingDen p u ^ 2

theorem hoeffdingDen_pos {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < hoeffdingDen p u := by
  rcases eq_or_lt_of_le hp1 with hp | hp
  · subst hp
    simpa [hoeffdingDen] using Real.exp_pos u
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr hp)
      (mul_nonneg hp0 (Real.exp_pos u).le)

theorem hoeffdingDen_ne_zero {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hoeffdingDen p u ≠ 0 :=
  (hoeffdingDen_pos hp0 hp1).ne'

private theorem hoeffding_sq_identity (p u : ℝ) :
    hoeffdingDen p u ^ 2 - 4 * p * (1 - p) * Real.exp u =
      (1 - p - p * Real.exp u) ^ 2 := by
  simp only [hoeffdingDen]
  ring

theorem hoeffdingPhiDerivTwo_le_one_div_four {p u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hoeffdingPhiDerivTwo p u ≤ 1 / 4 := by
  have hden := hoeffdingDen_pos hp0 hp1 (u := u)
  have hden2 : 0 < hoeffdingDen p u ^ 2 := pow_pos hden 2
  have h4 : 0 < (4 : ℝ) := by norm_num
  have hle : 4 * (p * (1 - p) * Real.exp u) ≤ hoeffdingDen p u ^ 2 := by
    have hs := hoeffding_sq_identity p u
    have hsq : 0 ≤ (1 - p - p * Real.exp u) ^ 2 := sq_nonneg _
    linarith
  have hnum : p * (1 - p) * Real.exp u ≤ hoeffdingDen p u ^ 2 / 4 :=
    (le_div_iff₀' h4).mpr hle
  have : p * (1 - p) * Real.exp u / hoeffdingDen p u ^ 2
      ≤ (hoeffdingDen p u ^ 2 / 4) / hoeffdingDen p u ^ 2 :=
    div_le_div_of_nonneg_right hnum hden2.le
  have hsimp : (hoeffdingDen p u ^ 2 / 4) / hoeffdingDen p u ^ 2 = 1 / 4 := by
    field_simp [hden2.ne']
  simpa [hoeffdingPhiDerivTwo, hsimp] using this

theorem hoeffdingPhi_hasDerivAt {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (hoeffdingPhi p) (hoeffdingPhiDeriv p u) u := by
  have hlin : HasDerivAt (fun x : ℝ => -p * x) (-p) u := by
    simpa using (hasDerivAt_id' u).const_mul (-p)
  have hexp : HasDerivAt (fun x : ℝ => p * Real.exp x) (p * Real.exp u) u :=
    (Real.hasDerivAt_exp u).const_mul p
  have hden : HasDerivAt (fun x : ℝ => (1 - p) + p * Real.exp x) (p * Real.exp u) u :=
    hexp.const_add (1 - p)
  have hden' : HasDerivAt (hoeffdingDen p) (p * Real.exp u) u :=
    hden.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [hoeffdingDen])
  have hlog : HasDerivAt (fun x : ℝ => Real.log (hoeffdingDen p x))
      (p * Real.exp u / hoeffdingDen p u) u :=
    hden'.log (hoeffdingDen_ne_zero hp0 hp1)
  have hsum := hlin.add hlog
  have hfun : (fun x : ℝ => -p * x + Real.log (hoeffdingDen p x)) = hoeffdingPhi p := by
    ext x
    simp [hoeffdingPhi]
  have hder : -p + p * Real.exp u / hoeffdingDen p u = hoeffdingPhiDeriv p u := by
    simp [hoeffdingPhiDeriv]
  exact ((hsum.congr_of_eventuallyEq
      (Eventually.of_forall fun x => (congrFun hfun x).symm)).congr_deriv hder)

theorem hoeffdingPhiDeriv_hasDerivAt {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt (hoeffdingPhiDeriv p) (hoeffdingPhiDerivTwo p u) u := by
  have hexp : HasDerivAt (fun x : ℝ => p * Real.exp x) (p * Real.exp u) u :=
    (Real.hasDerivAt_exp u).const_mul p
  have hden : HasDerivAt (fun x : ℝ => (1 - p) + p * Real.exp x) (p * Real.exp u) u :=
    hexp.const_add (1 - p)
  have hden' : HasDerivAt (hoeffdingDen p) (p * Real.exp u) u :=
    hden.congr_of_eventuallyEq (Eventually.of_forall fun x => by simp [hoeffdingDen])
  have hdiv := hexp.fun_div hden' (hoeffdingDen_ne_zero hp0 hp1)
  have hconst : HasDerivAt (fun _ : ℝ => -p) (0 : ℝ) u := hasDerivAt_const u (-p)
  have hadd := hconst.add hdiv
  have hne := hoeffdingDen_ne_zero hp0 hp1 (u := u)
  have hderiv :
      0 + (p * Real.exp u * hoeffdingDen p u -
          p * Real.exp u * (p * Real.exp u)) / hoeffdingDen p u ^ 2 =
        hoeffdingPhiDerivTwo p u := by
    simp only [hoeffdingPhiDerivTwo, hoeffdingDen]
    field_simp [hne]
    ring
  have hfun :
      (fun x : ℝ => -p + p * Real.exp x / hoeffdingDen p x) = hoeffdingPhiDeriv p := by
    ext x
    simp [hoeffdingPhiDeriv]
  exact (hadd.congr_of_eventuallyEq
      (Eventually.of_forall fun x => (congrFun hfun x).symm)).congr_deriv hderiv

theorem hoeffdingPhi_zero {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    hoeffdingPhi p 0 = 0 := by
  simp [hoeffdingPhi, hoeffdingDen]

theorem hoeffdingPhiDeriv_zero {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    hoeffdingPhiDeriv p 0 = 0 := by
  simp [hoeffdingPhiDeriv, hoeffdingDen]

theorem hoeffdingPhi_continuous {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Continuous (hoeffdingPhi p) :=
  continuous_iff_continuousAt.mpr fun u =>
    (hoeffdingPhi_hasDerivAt hp0 hp1 (u := u)).continuousAt

theorem hoeffdingPhiDeriv_continuous {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Continuous (hoeffdingPhiDeriv p) :=
  continuous_iff_continuousAt.mpr fun u =>
    (hoeffdingPhiDeriv_hasDerivAt hp0 hp1 (u := u)).continuousAt

private theorem eq_div_mul {y x d : ℝ} (h : y = x / d) (hd : d ≠ 0) :
    x = y * d := by
  rw [h, div_mul_cancel₀ x hd]

private theorem hoeffdingPhi_le_sq_div_four_pos {p u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu : 0 < u) :
    hoeffdingPhi p u ≤ u ^ 2 / 4 := by
  have hcont : ContinuousOn (hoeffdingPhi p) (Set.Icc 0 u) :=
    (hoeffdingPhi_continuous hp0 hp1).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo 0 u,
      HasDerivAt (hoeffdingPhi p) (hoeffdingPhiDeriv p x) x :=
    fun x _ => hoeffdingPhi_hasDerivAt hp0 hp1
  obtain ⟨ξ, hξ, hξeq⟩ :=
    exists_hasDerivAt_eq_slope (hoeffdingPhi p) (hoeffdingPhiDeriv p) hu hcont hderiv
  have hξgt : 0 < ξ := hξ.1
  have hξlt : ξ < u := hξ.2
  have hcont' : ContinuousOn (hoeffdingPhiDeriv p) (Set.Icc 0 ξ) :=
    (hoeffdingPhiDeriv_continuous hp0 hp1).continuousOn
  have hderiv' : ∀ x ∈ Set.Ioo 0 ξ,
      HasDerivAt (hoeffdingPhiDeriv p) (hoeffdingPhiDerivTwo p x) x :=
    fun x _ => hoeffdingPhiDeriv_hasDerivAt hp0 hp1
  obtain ⟨η, _, hηeq⟩ :=
    exists_hasDerivAt_eq_slope (hoeffdingPhiDeriv p) (hoeffdingPhiDerivTwo p)
      hξgt hcont' hderiv'
  have hφ0 := hoeffdingPhi_zero hp0 hp1
  have hd0 := hoeffdingPhiDeriv_zero hp0 hp1
  have hune : u ≠ 0 := ne_of_gt hu
  have hξne : ξ ≠ 0 := ne_of_gt hξgt
  have hφu : hoeffdingPhi p u = u * hoeffdingPhiDeriv p ξ := by
    have : hoeffdingPhiDeriv p ξ =
        (hoeffdingPhi p u - hoeffdingPhi p 0) / (u - 0) := hξeq
    have hdiv : hoeffdingPhiDeriv p ξ = hoeffdingPhi p u / u := by
      simpa [hφ0] using this
    have := eq_div_mul hdiv hune
    linarith
  have hξmul : hoeffdingPhiDeriv p ξ = ξ * hoeffdingPhiDerivTwo p η := by
    have : hoeffdingPhiDerivTwo p η =
        (hoeffdingPhiDeriv p ξ - hoeffdingPhiDeriv p 0) / (ξ - 0) := hηeq
    have hdiv : hoeffdingPhiDerivTwo p η = hoeffdingPhiDeriv p ξ / ξ := by
      simpa [hd0] using this
    have := eq_div_mul hdiv hξne
    linarith
  have hφu' : hoeffdingPhi p u = u * ξ * hoeffdingPhiDerivTwo p η := by
    rw [hφu, hξmul, mul_assoc]
  have hφ'' := hoeffdingPhiDerivTwo_le_one_div_four (p := p) (u := η) hp0 hp1
  have hξ0 : 0 ≤ ξ := le_of_lt hξgt
  have hu0 : 0 ≤ u := le_of_lt hu
  have hξu : ξ ≤ u := le_of_lt hξlt
  rw [hφu']
  by_cases hpos : 0 ≤ hoeffdingPhiDerivTwo p η
  · have hmul := mul_le_mul_of_nonneg_left hφ'' (mul_nonneg hu0 hξ0)
    have hξstep : u * ξ * (1 / 4) ≤ u * u * (1 / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξu hu0) (by norm_num)
    have hring : u * u * (1 / 4) = u ^ 2 / 4 := by ring
    exact hmul.trans (hξstep.trans (le_of_eq hring))
  · have hprod : u * ξ * hoeffdingPhiDerivTwo p η ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu0 hξ0) (le_of_not_ge hpos)
    exact hprod.trans (div_nonneg (sq_nonneg u) (by norm_num))

private theorem hoeffdingPhi_le_sq_div_four_neg {p u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hu : u < 0) :
    hoeffdingPhi p u ≤ u ^ 2 / 4 := by
  have hcont : ContinuousOn (hoeffdingPhi p) (Set.Icc u 0) :=
    (hoeffdingPhi_continuous hp0 hp1).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo u 0,
      HasDerivAt (hoeffdingPhi p) (hoeffdingPhiDeriv p x) x :=
    fun x _ => hoeffdingPhi_hasDerivAt hp0 hp1
  obtain ⟨ξ, hξ, hξeq⟩ :=
    exists_hasDerivAt_eq_slope (hoeffdingPhi p) (hoeffdingPhiDeriv p) hu hcont hderiv
  have hξgt : u < ξ := hξ.1
  have hξlt : ξ < 0 := hξ.2
  have hcont' : ContinuousOn (hoeffdingPhiDeriv p) (Set.Icc ξ 0) :=
    (hoeffdingPhiDeriv_continuous hp0 hp1).continuousOn
  have hderiv' : ∀ x ∈ Set.Ioo ξ 0,
      HasDerivAt (hoeffdingPhiDeriv p) (hoeffdingPhiDerivTwo p x) x :=
    fun x _ => hoeffdingPhiDeriv_hasDerivAt hp0 hp1
  obtain ⟨η, _, hηeq⟩ :=
    exists_hasDerivAt_eq_slope (hoeffdingPhiDeriv p) (hoeffdingPhiDerivTwo p)
      hξlt hcont' hderiv'
  have hφ0 := hoeffdingPhi_zero hp0 hp1
  have hd0 := hoeffdingPhiDeriv_zero hp0 hp1
  have hune : u ≠ 0 := ne_of_lt hu
  have hξne : ξ ≠ 0 := ne_of_lt hξlt
  have hφu : hoeffdingPhi p u = u * hoeffdingPhiDeriv p ξ := by
    have : hoeffdingPhiDeriv p ξ =
        (hoeffdingPhi p 0 - hoeffdingPhi p u) / (0 - u) := hξeq
    have hdiv : hoeffdingPhiDeriv p ξ = hoeffdingPhi p u / u := by
      simpa [hφ0, zero_sub, sub_zero, neg_div, div_neg] using this
    have := eq_div_mul hdiv hune
    linarith
  have hξmul : hoeffdingPhiDeriv p ξ = ξ * hoeffdingPhiDerivTwo p η := by
    have : hoeffdingPhiDerivTwo p η =
        (hoeffdingPhiDeriv p 0 - hoeffdingPhiDeriv p ξ) / (0 - ξ) := hηeq
    have hdiv : hoeffdingPhiDerivTwo p η = hoeffdingPhiDeriv p ξ / ξ := by
      simpa [hd0, zero_sub, neg_div, div_neg] using this
    have := eq_div_mul hdiv hξne
    linarith
  have hφu' : hoeffdingPhi p u = u * ξ * hoeffdingPhiDerivTwo p η := by
    rw [hφu, hξmul, mul_assoc]
  have hφ'' := hoeffdingPhiDerivTwo_le_one_div_four (p := p) (u := η) hp0 hp1
  have hu0 : u ≤ 0 := le_of_lt hu
  have hξ0 : ξ ≤ 0 := le_of_lt hξlt
  have huc0 : 0 ≤ u * ξ := mul_nonneg_of_nonpos_of_nonpos hu0 hξ0
  have hξu : |ξ| ≤ |u| := by
    rw [abs_of_nonpos hξ0, abs_of_nonpos hu0]
    exact neg_le_neg_iff.mpr (le_of_lt hξgt)
  rw [hφu']
  by_cases hpos : 0 ≤ hoeffdingPhiDerivTwo p η
  · have hmul := mul_le_mul_of_nonneg_left hφ'' huc0
    have huc : u * ξ = |u| * |ξ| := by
      rw [abs_of_nonpos hu0, abs_of_nonpos hξ0]
      ring
    have hstep : u * ξ * (1 / 4) ≤ |u| * |u| * (1 / 4) := by
      have : |u| * |ξ| ≤ |u| * |u| :=
        mul_le_mul_of_nonneg_left hξu (abs_nonneg _)
      have hrew : u * ξ * (1 / 4) = |u| * |ξ| * (1 / 4) := by rw [huc]
      have hrew' : |u| * |u| * (1 / 4) = |u| * |u| * (1 / 4) := rfl
      rw [hrew]
      exact mul_le_mul_of_nonneg_right this (by norm_num)
    have hring : |u| * |u| * (1 / 4) = u ^ 2 / 4 := by
      have : |u| * |u| = u ^ 2 := by simp [abs_mul_abs_self, sq]
      rw [this]
      ring
    exact hmul.trans (hstep.trans (le_of_eq hring))
  · have hprod : u * ξ * hoeffdingPhiDerivTwo p η ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos huc0 (le_of_not_ge hpos)
    exact hprod.trans (div_nonneg (sq_nonneg u) (by norm_num))

/-- Two MVTs: paper uses `u²/8`; this `u²/4` keeps the `(log G)^{3/2}` rate. -/
theorem hoeffdingPhi_le_sq_div_four {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hoeffdingPhi p u ≤ u ^ 2 / 4 := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · exact hoeffdingPhi_le_sq_div_four_neg hp0 hp1 hu
  · subst hu
    simp [hoeffdingPhi_zero hp0 hp1]
  · exact hoeffdingPhi_le_sq_div_four_pos hp0 hp1 hu

theorem hoeffdingPhi_exp_le {p u : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (-p * u) + p * Real.exp ((1 - p) * u)
      ≤ Real.exp (u ^ 2 / 4) := by
  have hden := hoeffdingDen_pos hp0 hp1 (u := u)
  have hexp : Real.exp (hoeffdingPhi p u) =
      (1 - p) * Real.exp (-p * u) + p * Real.exp ((1 - p) * u) := by
    rw [hoeffdingPhi, Real.exp_add, Real.exp_log hden, hoeffdingDen, mul_add]
    have h1 : Real.exp (-p * u) * (1 - p) = (1 - p) * Real.exp (-p * u) :=
      mul_comm _ _
    have h2 : Real.exp (-p * u) * (p * Real.exp u) = p * Real.exp ((1 - p) * u) := by
      calc
        Real.exp (-p * u) * (p * Real.exp u)
            = p * (Real.exp (-p * u) * Real.exp u) := by ring
        _ = p * Real.exp (-p * u + u) := by rw [Real.exp_add]
        _ = p * Real.exp ((1 - p) * u) := by
            congr 1
            ring
    rw [h1, h2]
  have hle : Real.exp (hoeffdingPhi p u) ≤ Real.exp (u ^ 2 / 4) :=
    Real.exp_le_exp.mpr (hoeffdingPhi_le_sq_div_four hp0 hp1)
  rwa [hexp] at hle

/-- Two-point Hoeffding lemma on a finite Bernoulli coordinate. -/
theorem two_point_mgf_le {q x0 x1 t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q) * Real.exp (t * x0) + q * Real.exp (t * x1)
      ≤ Real.exp (t * ((1 - q) * x0 + q * x1) + t ^ 2 * (x1 - x0) ^ 2 / 4) := by
  set m := (1 - q) * x0 + q * x1
  set δ := x1 - x0
  have hx0 : x0 = m + -q * δ := by
    simp [m, δ]
    ring
  have hx1 : x1 = m + (1 - q) * δ := by
    simp [m, δ]
    ring
  have h0 : t * x0 = t * m + -q * (t * δ) := by
    rw [hx0]
    ring
  have h1 : t * x1 = t * m + (1 - q) * (t * δ) := by
    rw [hx1]
    ring
  have hfactor :
      (1 - q) * Real.exp (t * x0) + q * Real.exp (t * x1) =
        Real.exp (t * m) *
          ((1 - q) * Real.exp (-q * (t * δ)) +
            q * Real.exp ((1 - q) * (t * δ))) := by
    rw [h0, h1, Real.exp_add, Real.exp_add]
    ring
  have hφ := hoeffdingPhi_exp_le (p := q) (u := t * δ) hq0 hq1
  have hmul := mul_le_mul_of_nonneg_left hφ (Real.exp_nonneg (t * m))
  have hrew : Real.exp (t * m) * Real.exp ((t * δ) ^ 2 / 4) =
      Real.exp (t * m + t ^ 2 * (x1 - x0) ^ 2 / 4) := by
    rw [← Real.exp_add]
    congr 1
    simp [δ]
    ring
  calc
    (1 - q) * Real.exp (t * x0) + q * Real.exp (t * x1)
        = Real.exp (t * m) *
            ((1 - q) * Real.exp (-q * (t * δ)) +
              q * Real.exp ((1 - q) * (t * δ))) := hfactor
    _ ≤ Real.exp (t * m) * Real.exp ((t * δ) ^ 2 / 4) := hmul
    _ = Real.exp (t * m + t ^ 2 * (x1 - x0) ^ 2 / 4) := hrew

/-! ### Independent Bernoulli product masses -/

/-- Heterogeneous independent Bernoulli mass of a coordinate set `s`. -/
noncomputable def indepBernoulliMass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q : ι → ℝ) (s : Finset ι) : ℝ :=
  if s ⊆ I then (∏ i ∈ s, q i) * (∏ i ∈ I \ s, (1 - q i)) else 0

theorem indepBernoulliMass_nonneg {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {q : ι → ℝ} (s : Finset ι)
    (hq0 : ∀ i ∈ I, 0 ≤ q i) (hq1 : ∀ i ∈ I, q i ≤ 1) :
    0 ≤ indepBernoulliMass I q s := by
  unfold indepBernoulliMass
  split_ifs with hs
  · exact mul_nonneg (prod_nonneg fun i hi => hq0 i (hs hi))
      (prod_nonneg fun i hi => sub_nonneg.mpr (hq1 i (sdiff_subset hi)))
  · exact le_rfl

theorem indepBernoulliMass_empty {ι : Type*} [DecidableEq ι] (q : ι → ℝ) :
    indepBernoulliMass (∅ : Finset ι) q ∅ = 1 := by
  simp [indepBernoulliMass]

theorem indepBernoulliMass_insert_self {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {a : ι} (ha : a ∉ I) (q : ι → ℝ) {s : Finset ι}
    (hs : s ⊆ I) :
    indepBernoulliMass (insert a I) q (insert a s) =
      q a * indepBernoulliMass I q s := by
  have hsI : insert a s ⊆ insert a I := Finset.insert_subset_insert a hs
  have has : a ∉ s := fun h => ha (hs h)
  have hdiff : insert a I \ insert a s = I \ s := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · intro hx
      rcases hx.1 with rfl | hxI
      · exact (hx.2 (Or.inl rfl)).elim
      · exact ⟨hxI, fun hxs => hx.2 (Or.inr hxs)⟩
    · intro hx
      refine ⟨Or.inr hx.1, ?_⟩
      intro h
      rcases h with rfl | hxs
      · exact ha hx.1
      · exact hx.2 hxs
  have hsif : s ⊆ I := hs
  simp only [indepBernoulliMass, hsI, hsif, ↓reduceIte, prod_insert has, hdiff]
  ring

theorem indepBernoulliMass_insert_of_notMem {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {a : ι} (ha : a ∉ I) (q : ι → ℝ) {s : Finset ι}
    (hs : s ⊆ I) :
    indepBernoulliMass (insert a I) q s =
      (1 - q a) * indepBernoulliMass I q s := by
  have hsI : s ⊆ insert a I := hs.trans (subset_insert a I)
  have has : a ∉ s := fun h => ha (hs h)
  have hdiff : insert a I \ s = insert a (I \ s) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · intro hx
      rcases hx.1 with rfl | hxI
      · exact Or.inl rfl
      · exact Or.inr ⟨hxI, hx.2⟩
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨Or.inl rfl, has⟩
      · exact ⟨Or.inr hx.1, hx.2⟩
  have haI : a ∉ I \ s := fun h => ha (mem_sdiff.mp h).1
  simp only [indepBernoulliMass, hsI, hs, ↓reduceIte, hdiff, prod_insert haI]
  ring

private theorem powerset_insert_disjoint {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {a : ι} (ha : a ∉ I) :
    Disjoint I.powerset (I.powerset.image (insert a)) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht2
  exact ha ((mem_powerset.mp ht1) (mem_insert_self a u))

private theorem insert_injOn_powerset {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {a : ι} (ha : a ∉ I) :
    Set.InjOn (insert a) (I.powerset : Set (Finset ι)) := by
  intro s hs t ht h
  have hsI : s ⊆ I := mem_powerset.mp hs
  have htI : t ⊆ I := mem_powerset.mp ht
  ext x
  constructor
  · intro hx
    have : x ∈ insert a t := by
      rw [← h]
      exact mem_insert_of_mem hx
    rcases mem_insert.mp this with rfl | hxt
    · exact (ha (hsI hx)).elim
    · exact hxt
  · intro hx
    have : x ∈ insert a s := by
      rw [h]
      exact mem_insert_of_mem hx
    rcases mem_insert.mp this with rfl | hxs
    · exact (ha (htI hx)).elim
    · exact hxs

theorem indepBernoulliMass_sum {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {q : ι → ℝ}
    (hq0 : ∀ i ∈ I, 0 ≤ q i) (hq1 : ∀ i ∈ I, q i ≤ 1) :
    ∑ s ∈ I.powerset, indepBernoulliMass I q s = 1 := by
  induction I using Finset.induction_on with
  | empty =>
    simp [indepBernoulliMass_empty]
  | insert a I ha ih =>
    have hq0I : ∀ i ∈ I, 0 ≤ q i := fun i hi => hq0 i (mem_insert_of_mem hi)
    have hq1I : ∀ i ∈ I, q i ≤ 1 := fun i hi => hq1 i (mem_insert_of_mem hi)
    have ih' := ih hq0I hq1I
    have hdisj := powerset_insert_disjoint ha
    rw [Finset.powerset_insert I a, sum_union hdisj, sum_image (insert_injOn_powerset ha)]
    have h0 : ∀ s ∈ I.powerset,
        indepBernoulliMass (insert a I) q s =
          (1 - q a) * indepBernoulliMass I q s := fun s hs =>
      indepBernoulliMass_insert_of_notMem ha q (mem_powerset.mp hs)
    have h1 : ∀ s ∈ I.powerset,
        indepBernoulliMass (insert a I) q (insert a s) =
          q a * indepBernoulliMass I q s := fun s hs =>
      indepBernoulliMass_insert_self ha q (mem_powerset.mp hs)
    rw [sum_congr rfl h0, sum_congr rfl h1, ← mul_sum, ← mul_sum, ih']
    ring

/-- Expectation of `F` under the independent Bernoulli product. -/
noncomputable def indepBernoulliExpect {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q : ι → ℝ) (F : Finset ι → ℝ) : ℝ :=
  ∑ s ∈ I.powerset, indepBernoulliMass I q s * F s

private theorem indepBernoulliExpect_insert {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {a : ι} (ha : a ∉ I) (q : ι → ℝ) (F : Finset ι → ℝ) :
    indepBernoulliExpect (insert a I) q F =
      indepBernoulliExpect I q (fun s => (1 - q a) * F s + q a * F (insert a s)) := by
  have hdisj := powerset_insert_disjoint ha
  unfold indepBernoulliExpect
  rw [Finset.powerset_insert I a, sum_union hdisj, sum_image (insert_injOn_powerset ha)]
  have h0 : ∀ s ∈ I.powerset,
      indepBernoulliMass (insert a I) q s * F s =
        indepBernoulliMass I q s * ((1 - q a) * F s) := fun s hs => by
    rw [indepBernoulliMass_insert_of_notMem ha q (mem_powerset.mp hs)]
    ring
  have h1 : ∀ s ∈ I.powerset,
      indepBernoulliMass (insert a I) q (insert a s) * F (insert a s) =
        indepBernoulliMass I q s * (q a * F (insert a s)) := fun s hs => by
    rw [indepBernoulliMass_insert_self ha q (mem_powerset.mp hs)]
    ring
  rw [sum_congr rfl h0, sum_congr rfl h1, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  ring

private theorem bernoulli_bounded_diff_mgf_aux {ι : Type*} [DecidableEq ι]
    (I : Finset ι) : ∀ (q : ι → ℝ) (F : Finset ι → ℝ) (c : ι → ℝ) (t : ℝ),
      (∀ i ∈ I, 0 ≤ q i) → (∀ i ∈ I, q i ≤ 1) → (∀ i ∈ I, 0 ≤ c i) →
      (∀ s : Finset ι, ∀ i ∈ I, i ∉ s → |F (insert i s) - F s| ≤ c i) →
      ∑ s ∈ I.powerset,
          indepBernoulliMass I q s *
            Real.exp (t * (F s - indepBernoulliExpect I q F))
        ≤ Real.exp (t ^ 2 * (∑ i ∈ I, c i ^ 2) / 4) := by
  induction I using Finset.induction_on with
  | empty =>
    intro q F c t _ _ _ _
    simp [indepBernoulliExpect, indepBernoulliMass_empty]
  | insert a I ha ih =>
    intro q F c t hq0 hq1 hc hdiff
    have hq0I : ∀ i ∈ I, 0 ≤ q i := fun i hi => hq0 i (mem_insert_of_mem hi)
    have hq1I : ∀ i ∈ I, q i ≤ 1 := fun i hi => hq1 i (mem_insert_of_mem hi)
    have hcI : ∀ i ∈ I, 0 ≤ c i := fun i hi => hc i (mem_insert_of_mem hi)
    have hqa0 : 0 ≤ q a := hq0 a (mem_insert_self a I)
    have hqa1 : q a ≤ 1 := hq1 a (mem_insert_self a I)
    set m : Finset ι → ℝ := fun s => (1 - q a) * F s + q a * F (insert a s)
    have hdiffI : ∀ s : Finset ι, ∀ i ∈ I, i ∉ s → |m (insert i s) - m s| ≤ c i := by
      intro s i hi his
      have hiI : i ∈ insert a I := mem_insert_of_mem hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have hnot : i ∉ insert a s := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hia, his⟩
      have hF0 := hdiff s i hiI his
      have hF1 := hdiff (insert a s) i hiI hnot
      have hqa0' : 0 ≤ 1 - q a := sub_nonneg.mpr hqa1
      have hcomm : insert a (insert i s) = insert i (insert a s) :=
        insert_comm a i s
      have hsub :
          m (insert i s) - m s =
            (1 - q a) * (F (insert i s) - F s) +
              q a * (F (insert a (insert i s)) - F (insert a s)) := by
        simp [m]
        ring
      have habs :
          |m (insert i s) - m s|
            ≤ (1 - q a) * |F (insert i s) - F s| +
              q a * |F (insert a (insert i s)) - F (insert a s)| := by
        rw [hsub]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hqa0', abs_of_nonneg hqa0]
      have hF1' : |F (insert a (insert i s)) - F (insert a s)| ≤ c i := by
        rw [hcomm]
        exact hF1
      have : (1 - q a) * |F (insert i s) - F s| +
          q a * |F (insert a (insert i s)) - F (insert a s)|
            ≤ (1 - q a) * c i + q a * c i :=
        add_le_add (mul_le_mul_of_nonneg_left hF0 hqa0')
          (mul_le_mul_of_nonneg_left hF1' hqa0)
      have hring : (1 - q a) * c i + q a * c i = c i := by ring
      exact habs.trans (this.trans (le_of_eq hring))
    have ih' := ih q m c t hq0I hq1I hcI hdiffI
    have hEF : indepBernoulliExpect (insert a I) q F = indepBernoulliExpect I q m :=
      indepBernoulliExpect_insert ha q F
    have hdisj := powerset_insert_disjoint ha
    have hsplit :
        ∑ s ∈ (insert a I).powerset,
            indepBernoulliMass (insert a I) q s *
              Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F))
          = ∑ s ∈ I.powerset, indepBernoulliMass I q s *
              ((1 - q a) *
                  Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F)) +
                q a * Real.exp (t * (F (insert a s) -
                  indepBernoulliExpect (insert a I) q F))) := by
      rw [Finset.powerset_insert I a, sum_union hdisj, sum_image (insert_injOn_powerset ha)]
      have h0 : ∀ s ∈ I.powerset,
          indepBernoulliMass (insert a I) q s *
              Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F)) =
            indepBernoulliMass I q s * ((1 - q a) *
              Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F))) :=
        fun s hs => by
          rw [indepBernoulliMass_insert_of_notMem ha q (mem_powerset.mp hs)]
          ring
      have h1 : ∀ s ∈ I.powerset,
          indepBernoulliMass (insert a I) q (insert a s) *
              Real.exp (t * (F (insert a s) - indepBernoulliExpect (insert a I) q F)) =
            indepBernoulliMass I q s * (q a *
              Real.exp (t * (F (insert a s) - indepBernoulliExpect (insert a I) q F))) :=
        fun s hs => by
          rw [indepBernoulliMass_insert_self ha q (mem_powerset.mp hs)]
          ring
      rw [sum_congr rfl h0, sum_congr rfl h1, ← sum_add_distrib]
      refine sum_congr rfl fun s _ => ?_
      ring
    have hca : 0 ≤ c a := hc a (mem_insert_self a I)
    have ht2 : 0 ≤ t ^ 2 / 4 := div_nonneg (sq_nonneg t) (by norm_num)
    have hpt : ∀ s ∈ I.powerset,
        (1 - q a) * Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F)) +
            q a * Real.exp (t * (F (insert a s) - indepBernoulliExpect (insert a I) q F))
          ≤ Real.exp (t * (m s - indepBernoulliExpect (insert a I) q F) +
              t ^ 2 * c a ^ 2 / 4) := fun s hs => by
      have htp := two_point_mgf_le (q := q a)
          (x0 := F s - indepBernoulliExpect (insert a I) q F)
          (x1 := F (insert a s) - indepBernoulliExpect (insert a I) q F)
          (t := t) hqa0 hqa1
      have hm : (1 - q a) * (F s - indepBernoulliExpect (insert a I) q F) +
          q a * (F (insert a s) - indepBernoulliExpect (insert a I) q F) =
            m s - indepBernoulliExpect (insert a I) q F := by
        simp [m]
        ring
      have hδ : |F (insert a s) - F s| ≤ c a :=
        hdiff s a (mem_insert_self a I) (fun h => ha ((mem_powerset.mp hs) h))
      have hδ' : |(F (insert a s) - indepBernoulliExpect (insert a I) q F) -
          (F s - indepBernoulliExpect (insert a I) q F)| ≤ c a := by
        simpa [sub_sub_sub_cancel_right] using hδ
      have hδsq : ((F (insert a s) - indepBernoulliExpect (insert a I) q F) -
          (F s - indepBernoulliExpect (insert a I) q F)) ^ 2 ≤ c a ^ 2 := by
        have : |F (insert a s) - F s| ^ 2 ≤ c a ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hδ 2
        have hrew : (F (insert a s) - indepBernoulliExpect (insert a I) q F) -
            (F s - indepBernoulliExpect (insert a I) q F) = F (insert a s) - F s := by
          ring
        rw [hrew, ← sq_abs]
        exact this
      have hmono : t ^ 2 *
            ((F (insert a s) - indepBernoulliExpect (insert a I) q F) -
              (F s - indepBernoulliExpect (insert a I) q F)) ^ 2 / 4
          ≤ t ^ 2 * c a ^ 2 / 4 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδsq (sq_nonneg t)) (by norm_num)
      have htp' := htp.trans (Real.exp_le_exp.mpr (add_le_add_right hmono _))
      simpa [hm] using htp'
    have hsum :
        ∑ s ∈ I.powerset, indepBernoulliMass I q s *
            ((1 - q a) *
                Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F)) +
              q a * Real.exp (t * (F (insert a s) -
                indepBernoulliExpect (insert a I) q F)))
          ≤ ∑ s ∈ I.powerset, indepBernoulliMass I q s *
              Real.exp (t * (m s - indepBernoulliExpect (insert a I) q F) +
                t ^ 2 * c a ^ 2 / 4) :=
      sum_le_sum fun s hs =>
        mul_le_mul_of_nonneg_left (hpt s hs) (indepBernoulliMass_nonneg I s hq0I hq1I)
    have hfact :
        ∑ s ∈ I.powerset, indepBernoulliMass I q s *
            Real.exp (t * (m s - indepBernoulliExpect (insert a I) q F) +
              t ^ 2 * c a ^ 2 / 4)
          = Real.exp (t ^ 2 * c a ^ 2 / 4) *
            ∑ s ∈ I.powerset, indepBernoulliMass I q s *
              Real.exp (t * (m s - indepBernoulliExpect I q m)) := by
      rw [hEF]
      simp only [Real.exp_add]
      have hpt : ∀ s ∈ I.powerset,
          indepBernoulliMass I q s *
              (Real.exp (t * (m s - indepBernoulliExpect I q m)) *
                Real.exp (t ^ 2 * c a ^ 2 / 4)) =
            Real.exp (t ^ 2 * c a ^ 2 / 4) *
              (indepBernoulliMass I q s *
                Real.exp (t * (m s - indepBernoulliExpect I q m))) :=
        fun s _ => by ring
      rw [sum_congr rfl hpt, ← mul_sum]
    have hσ :
        t ^ 2 * c a ^ 2 / 4 + t ^ 2 * (∑ i ∈ I, c i ^ 2) / 4 =
          t ^ 2 * (∑ i ∈ insert a I, c i ^ 2) / 4 := by
      rw [sum_insert ha]
      ring
    calc
      ∑ s ∈ (insert a I).powerset,
          indepBernoulliMass (insert a I) q s *
            Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F))
          = ∑ s ∈ I.powerset, indepBernoulliMass I q s *
              ((1 - q a) *
                  Real.exp (t * (F s - indepBernoulliExpect (insert a I) q F)) +
                q a * Real.exp (t * (F (insert a s) -
                  indepBernoulliExpect (insert a I) q F))) := hsplit
      _ ≤ ∑ s ∈ I.powerset, indepBernoulliMass I q s *
            Real.exp (t * (m s - indepBernoulliExpect (insert a I) q F) +
              t ^ 2 * c a ^ 2 / 4) := hsum
      _ = Real.exp (t ^ 2 * c a ^ 2 / 4) *
            ∑ s ∈ I.powerset, indepBernoulliMass I q s *
              Real.exp (t * (m s - indepBernoulliExpect I q m)) := hfact
      _ ≤ Real.exp (t ^ 2 * c a ^ 2 / 4) *
            Real.exp (t ^ 2 * (∑ i ∈ I, c i ^ 2) / 4) :=
        mul_le_mul_of_nonneg_left ih' (Real.exp_nonneg _)
      _ = Real.exp (t ^ 2 * (∑ i ∈ insert a I, c i ^ 2) / 4) := by
          rw [← Real.exp_add, hσ]

/-- Bounded-differences MGF on a finite independent Bernoulli product. -/
theorem bernoulli_bounded_diff_mgf {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q : ι → ℝ) (F : Finset ι → ℝ) (c : ι → ℝ) (t : ℝ)
    (hq0 : ∀ i ∈ I, 0 ≤ q i) (hq1 : ∀ i ∈ I, q i ≤ 1)
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hdiff : ∀ s : Finset ι, ∀ i ∈ I, i ∉ s → |F (insert i s) - F s| ≤ c i) :
    ∑ s ∈ I.powerset,
        indepBernoulliMass I q s *
          Real.exp (t * (F s - indepBernoulliExpect I q F))
      ≤ Real.exp (t ^ 2 * (∑ i ∈ I, c i ^ 2) / 4) :=
  bernoulli_bounded_diff_mgf_aux I q F c t hq0 hq1 hc hdiff

/-! ### Exponential Markov and one-sided tails -/

theorem exp_markov_finset {ι : Type*} (Ω : Finset ι) (μ Z : ι → ℝ) {t u : ℝ}
    (ht : 0 ≤ t) (hμ : ∀ i ∈ Ω, 0 ≤ μ i) :
    ∑ i ∈ Ω.filter (fun i => u ≤ Z i), μ i
      ≤ Real.exp (-t * u) * ∑ i ∈ Ω, μ i * Real.exp (t * Z i) := by
  have hpt : ∀ i ∈ Ω,
      (if u ≤ Z i then μ i else 0)
        ≤ Real.exp (-t * u) * (μ i * Real.exp (t * Z i)) := fun i hi => by
    by_cases hZ : u ≤ Z i
    · have hexp : (1 : ℝ) ≤ Real.exp (t * (Z i - u)) := by
        have : 0 ≤ t * (Z i - u) := mul_nonneg ht (sub_nonneg.mpr hZ)
        simpa using (Real.one_le_exp this)
      have : μ i ≤ μ i * Real.exp (t * (Z i - u)) := by
        have hμi := hμ i hi
        have : μ i * 1 ≤ μ i * Real.exp (t * (Z i - u)) :=
          mul_le_mul_of_nonneg_left hexp hμi
        simpa using this
      have hrew : Real.exp (t * (Z i - u)) =
          Real.exp (-t * u) * Real.exp (t * Z i) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [hZ, ↓reduceIte]
      calc
        μ i ≤ μ i * Real.exp (t * (Z i - u)) := this
        _ = Real.exp (-t * u) * (μ i * Real.exp (t * Z i)) := by
            rw [hrew]
            ring
    · simp only [hZ, ↓reduceIte]
      exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hμ i hi) (Real.exp_nonneg _))
  have hsum := sum_le_sum hpt
  have hleft : ∑ i ∈ Ω.filter (fun i => u ≤ Z i), μ i =
      ∑ i ∈ Ω, if u ≤ Z i then μ i else 0 := by
    rw [sum_filter]
  have hright :
      ∑ i ∈ Ω, Real.exp (-t * u) * (μ i * Real.exp (t * Z i)) =
        Real.exp (-t * u) * ∑ i ∈ Ω, μ i * Real.exp (t * Z i) := by
    rw [← mul_sum]
  rw [hleft]
  exact hsum.trans (le_of_eq hright)

private theorem bounded_diff_eq_empty {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : Finset ι → ℝ) (c : ι → ℝ)
    (hc0 : ∀ i ∈ I, c i = 0)
    (hdiff : ∀ s : Finset ι, ∀ i ∈ I, i ∉ s → |F (insert i s) - F s| ≤ c i)
    {s : Finset ι} : s ⊆ I → F s = F ∅ := by
  induction s using Finset.induction_on with
  | empty => intro _; rfl
  | insert b s hb ih =>
    intro hs
    have hbI : b ∈ I := hs (mem_insert_self b s)
    have hsI : s ⊆ I := fun x hx => hs (mem_insert_of_mem hx)
    have ih' := ih hsI
    have hle := hdiff s b hbI hb
    have : |F (insert b s) - F s| ≤ 0 := by
      simpa [hc0 b hbI] using hle
    have heq : F (insert b s) = F s :=
      sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
    rw [heq, ih']

/-- One-sided bounded-differences tail. Paper (eq:bd) has the sharper
`exp(-2 u² / ∑ c²)` from `φ ≤ u²/8`; this `u²/4` form is `exp(-u² / ∑ c²)`. -/
theorem bernoulli_bounded_diff_one_sided {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q : ι → ℝ) (F : Finset ι → ℝ) (c : ι → ℝ) {u : ℝ}
    (hq0 : ∀ i ∈ I, 0 ≤ q i) (hq1 : ∀ i ∈ I, q i ≤ 1)
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hdiff : ∀ s : Finset ι, ∀ i ∈ I, i ∉ s → |F (insert i s) - F s| ≤ c i)
    (hu : 0 < u) :
    ∑ s ∈ I.powerset.filter
        (fun s => u ≤ F s - indepBernoulliExpect I q F),
      indepBernoulliMass I q s
      ≤ if ∑ i ∈ I, c i ^ 2 = 0 then 0
        else Real.exp (-u ^ 2 / ∑ i ∈ I, c i ^ 2) := by
  by_cases hσ : ∑ i ∈ I, c i ^ 2 = 0
  · have hc0 : ∀ i ∈ I, c i = 0 := by
      intro i hi
      have hsum :=
        (sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hσ i hi
      exact (sq_eq_zero_iff.mp hsum)
    have hconst : ∀ s ∈ I.powerset, F s = F ∅ := fun s hs =>
      bounded_diff_eq_empty I F c hc0 hdiff (mem_powerset.mp hs)
    have hE : indepBernoulliExpect I q F = F ∅ := by
      unfold indepBernoulliExpect
      have hpt : ∀ s ∈ I.powerset,
          indepBernoulliMass I q s * F s = indepBernoulliMass I q s * F ∅ :=
        fun s hs => by rw [hconst s hs]
      rw [sum_congr rfl hpt, ← sum_mul, indepBernoulliMass_sum I hq0 hq1, one_mul]
    have hempty :
        I.powerset.filter (fun s => u ≤ F s - indepBernoulliExpect I q F) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have hmem := mem_filter.mp hs
      have : u ≤ 0 := by
        simpa [hconst s hmem.1, hE] using hmem.2
      exact (not_le_of_gt hu) this
    simp [hσ, hempty]
  · have hσnn : 0 ≤ ∑ i ∈ I, c i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hσpos : 0 < ∑ i ∈ I, c i ^ 2 := hσnn.lt_of_ne (Ne.symm hσ)
    set σ := ∑ i ∈ I, c i ^ 2
    set t := (2 : ℝ) * u / σ
    have ht : 0 ≤ t :=
      div_nonneg (mul_nonneg (by norm_num) hu.le) hσpos.le
    have hmarkov :=
      exp_markov_finset (I.powerset) (indepBernoulliMass I q)
        (fun s => F s - indepBernoulliExpect I q F) (u := u) ht
        (fun s _ => indepBernoulliMass_nonneg I s hq0 hq1)
    have hmgf := bernoulli_bounded_diff_mgf I q F c t hq0 hq1 hc hdiff
    have hexp : Real.exp (-t * u) * Real.exp (t ^ 2 * σ / 4) =
        Real.exp (-u ^ 2 / σ) := by
      rw [← Real.exp_add]
      congr 1
      have hσ0 : σ ≠ 0 := ne_of_gt hσpos
      have : -t * u + t ^ 2 * σ / 4 = -u ^ 2 / σ := by
        simp only [t]
        field_simp [hσ0]
        ring
      exact this
    have hstep :=
      (mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (-t * u))).trans (le_of_eq hexp)
    have : ∑ s ∈ I.powerset.filter
          (fun s => u ≤ F s - indepBernoulliExpect I q F),
        indepBernoulliMass I q s
        ≤ Real.exp (-u ^ 2 / σ) := hmarkov.trans hstep
    simpa [hσ, σ] using this

/-! ### Bonferroni union bound -/

/-- First Bonferroni inequality on a finite mass: the union is at most
the sum. Paper Appendix C uses this over `O(log G)` cells. -/
theorem bonferroni_union_mass {ι κ : Type*} [DecidableEq ι]
    (Ω : Finset ι) (μ : ι → ℝ) (K : Finset κ) (E : κ → Finset ι)
    (hμ : ∀ i ∈ Ω, 0 ≤ μ i) :
    ∑ i ∈ Ω.filter (fun ω => ∃ k ∈ K, ω ∈ E k), μ i
      ≤ ∑ k ∈ K, ∑ i ∈ Ω ∩ E k, μ i := by
  have hpt : ∀ i ∈ Ω,
      (if ∃ k ∈ K, i ∈ E k then μ i else 0)
        ≤ ∑ k ∈ K, if i ∈ E k then μ i else 0 := fun i hi => by
    by_cases hex : ∃ k ∈ K, i ∈ E k
    · obtain ⟨k0, hk0, hiE⟩ := hex
      have hnn : ∀ k ∈ K, 0 ≤ (if i ∈ E k then μ i else 0) := fun k _ =>
        if hEk : i ∈ E k then by
          rw [if_pos hEk]
          exact hμ i hi
        else by
          rw [if_neg hEk]
      have hsingle := single_le_sum hnn hk0
      rw [if_pos hiE] at hsingle
      rw [if_pos ⟨k0, hk0, hiE⟩]
      exact hsingle
    · simp only [hex, ↓reduceIte]
      exact sum_nonneg fun k _ =>
        if hEk : i ∈ E k then by
          rw [if_pos hEk]
          exact hμ i hi
        else by
          rw [if_neg hEk]
  have hsum := sum_le_sum hpt
  have hleft :
      ∑ i ∈ Ω.filter (fun ω => ∃ k ∈ K, ω ∈ E k), μ i =
        ∑ i ∈ Ω, if ∃ k ∈ K, i ∈ E k then μ i else 0 := by
    rw [sum_filter]
  calc
    ∑ i ∈ Ω.filter (fun ω => ∃ k ∈ K, ω ∈ E k), μ i
        = ∑ i ∈ Ω, if ∃ k ∈ K, i ∈ E k then μ i else 0 := hleft
    _ ≤ ∑ i ∈ Ω, ∑ k ∈ K, if i ∈ E k then μ i else 0 := hsum
    _ = ∑ k ∈ K, ∑ i ∈ Ω, if i ∈ E k then μ i else 0 := sum_comm
    _ = ∑ k ∈ K, ∑ i ∈ Ω ∩ E k, μ i := by
        refine sum_congr rfl fun k _ => ?_
        rw [← sum_filter, filter_mem_eq_inter]

/-! ### Algebraic `6 L` and `(12 L)^j` envelope -/

theorem two_mul_six_pow_le_twelve_pow {j : ℕ} (hj : 1 ≤ j) :
    2 * (6 : ℝ) ^ j ≤ (12 : ℝ) ^ j := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
    simpa using this
  calc
    (2 : ℝ) * 6 ^ j ≤ 2 ^ j * 6 ^ j :=
      mul_le_mul_of_nonneg_right h2 (pow_nonneg (by norm_num) _)
    _ = (2 * 6) ^ j := (mul_pow (2 : ℝ) 6 j).symm
    _ = 12 ^ j := by norm_num

/-- Paper: `(1+η) θ S̄ V ≤ 6 L` once `η ≤ 1` and calibration `θ S̄ V ≤ 3 L`. -/
theorem theta_N0_le_six {θ N0 Sbar V L η : ℝ}
    (hθ : 0 ≤ θ) (_hN0 : 0 ≤ N0) (hS : 0 ≤ Sbar) (hV : 0 ≤ V) (_hL : 0 ≤ L)
    (hgood : N0 ≤ (1 + η) * Sbar * V) (_hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hcal : θ * Sbar * V ≤ 3 * L) :
    θ * N0 ≤ 6 * L := by
  have h1 : θ * N0 ≤ θ * ((1 + η) * Sbar * V) :=
    mul_le_mul_of_nonneg_left hgood hθ
  have h2 : θ * ((1 + η) * Sbar * V) = (1 + η) * (θ * Sbar * V) := by ring
  have hη2 : 1 + η ≤ 2 := by linarith
  have hnn : 0 ≤ θ * Sbar * V := mul_nonneg (mul_nonneg hθ hS) hV
  have h3 : (1 + η) * (θ * Sbar * V) ≤ 2 * (3 * L) :=
    mul_le_mul hη2 hcal hnn (by norm_num)
  have h4 : 2 * (3 * L) = 6 * L := by ring
  calc
    θ * N0 ≤ θ * ((1 + η) * Sbar * V) := h1
    _ = (1 + η) * (θ * Sbar * V) := h2
    _ ≤ 2 * (3 * L) := h3
    _ = 6 * L := h4

theorem exception_add_le_twelve_pow {L ε C1 logS : ℝ} {j : ℕ}
    (hL : 0 ≤ L) (_hε : 0 ≤ ε) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hj : 1 ≤ j) (hsmall : ε * (C1 * logS / 6) ^ j ≤ 1) :
    (6 * L) ^ j + ε * (C1 * L * logS) ^ j ≤ (12 * L) ^ j := by
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  have hrew : C1 * L * logS = (6 * L) * (C1 * logS / 6) := by
    field_simp [h6]
  have hpow : (C1 * L * logS) ^ j = (6 * L) ^ j * (C1 * logS / 6) ^ j := by
    rw [hrew, mul_pow]
  have hnn6 : 0 ≤ (6 * L) ^ j := pow_nonneg (mul_nonneg (by norm_num) hL) j
  have hratio : 0 ≤ (C1 * logS / 6) ^ j :=
    pow_nonneg (div_nonneg (mul_nonneg hC1 hlog) (by norm_num)) j
  have hLHS :
      (6 * L) ^ j + ε * (C1 * L * logS) ^ j =
        (6 * L) ^ j * (1 + ε * (C1 * logS / 6) ^ j) := by
    rw [hpow]
    ring
  have hone : 1 + ε * (C1 * logS / 6) ^ j ≤ 2 := by linarith
  have htwo : (6 * L) ^ j * (1 + ε * (C1 * logS / 6) ^ j) ≤ 2 * (6 * L) ^ j :=
    (mul_le_mul_of_nonneg_left hone hnn6).trans_eq (by ring)
  have h12 : 2 * (6 * L) ^ j ≤ (12 * L) ^ j := by
    have : 2 * (6 * L) ^ j = 2 * 6 ^ j * L ^ j := by
      rw [mul_pow]
      ring
    have : (12 * L) ^ j = 12 ^ j * L ^ j := mul_pow _ _ _
    have hLpow : 0 ≤ L ^ j := pow_nonneg hL j
    have hsix := two_mul_six_pow_le_twelve_pow hj
    calc
      2 * (6 * L) ^ j = (2 * 6 ^ j) * L ^ j := by
        rw [mul_pow]
        ring
      _ ≤ (12 ^ j) * L ^ j := mul_le_mul_of_nonneg_right hsix hLpow
      _ = (12 * L) ^ j := (mul_pow (12 : ℝ) L j).symm
  rw [hLHS]
  exact htwo.trans h12

/-- Abstract Lemma B.2 combination: good event `θ N ≤ 6 L` of mass
complement `≤ ε`, everywhere `θ N ≤ C₁ L log S̄`, and the ModelMoments
envelope, yield `Q ≤ (12 L)^j / j!`. -/
theorem factorialMoment_le_twelve {ι : Type*} [DecidableEq ι]
    (s g : Finset ι) (μ N : ι → ℝ) {θ ε L C1 logS Q : ℝ} (j : ℕ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hL : 0 ≤ L) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hN : ∀ i ∈ s, 0 ≤ N i)
    (hμ1 : ∑ i ∈ s, μ i ≤ 1) (hg : g ⊆ s)
    (hbad : ∑ i ∈ s \ g, μ i ≤ ε)
    (hgood : ∀ i ∈ g, θ * N i ≤ 6 * L)
    (hall : ∀ i ∈ s, θ * N i ≤ C1 * L * logS)
    (hQ : Q ≤ θ ^ j * massPowerMoment s μ N j / (j.factorial : ℝ))
    (hj : 1 ≤ j) (hsmall : ε * (C1 * logS / 6) ^ j ≤ 1) :
    Q ≤ (12 * L) ^ j / (j.factorial : ℝ) := by
  have hA : 0 ≤ 6 * L := mul_nonneg (by norm_num) hL
  have hM : 0 ≤ C1 * L * logS := mul_nonneg (mul_nonneg hC1 hL) hlog
  have henv :=
    factorialMoment_envelope s g μ N j hθ hε hA hM hμ hN hμ1 hg hbad hgood hall hQ
  have halg := exception_add_le_twelve_pow hL hε hC1 hlog hj hsmall
  have : ((6 * L) ^ j + ε * (C1 * L * logS) ^ j) / (j.factorial : ℝ)
      ≤ (12 * L) ^ j / (j.factorial : ℝ) :=
    div_le_div_of_nonneg_right halg (Nat.cast_nonneg _)
  exact henv.trans this

/-- Mixed Palm form of the moment band. -/
theorem palm_chooseMoment_le_twelve {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s g : Finset ι) (μ : ι → ℝ) (N : ι → ℕ) (t : Finset κ) (q : κ → ℝ)
    {ε L C1 logS : ℝ} (j : ℕ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hμ1 : ∑ i ∈ s, μ i ≤ 1) (hg : g ⊆ s)
    (hbad : ∑ i ∈ s \ g, μ i ≤ ε)
    (hq0 : ∀ i ∈ t, 0 ≤ q i) (hq1 : ∀ i ∈ t, q i ≤ 1)
    (hqj : ∀ i ∈ t, (j : ℝ) * q i ≤ 1)
    (hgood : ∀ i ∈ g, palmTheta t q * (N i : ℝ) ≤ 6 * L)
    (hall : ∀ i ∈ s, palmTheta t q * (N i : ℝ) ≤ C1 * L * logS)
    (hj : 1 ≤ j) (hsmall : ε * (C1 * logS / 6) ^ j ≤ 1) :
    palmJointSurvive t q j * massChooseMoment s μ N j
      ≤ (12 * L) ^ j / (j.factorial : ℝ) := by
  have hA : 0 ≤ 6 * L := mul_nonneg (by norm_num) hL
  have hM : 0 ≤ C1 * L * logS := mul_nonneg (mul_nonneg hC1 hL) hlog
  have henv :=
    palm_chooseMoment_envelope s g μ N t q j hε hA hM hμ hμ1 hg hbad hq0 hq1 hqj
      hgood hall
  have halg := exception_add_le_twelve_pow hL hε hC1 hlog hj hsmall
  have : ((6 * L) ^ j + ε * (C1 * L * logS) ^ j) / (j.factorial : ℝ)
      ≤ (12 * L) ^ j / (j.factorial : ℝ) :=
    div_le_div_of_nonneg_right halg (Nat.cast_nonneg _)
  exact henv.trans this

theorem massChooseMoment_zero_le_one {ι : Type*} (s : Finset ι) (μ : ι → ℝ)
    (N : ι → ℕ) (_hμ : ∀ i ∈ s, 0 ≤ μ i) (hμ1 : ∑ i ∈ s, μ i ≤ 1) :
    massChooseMoment s μ N 0 ≤ 1 := by
  have : massChooseMoment s μ N 0 = ∑ i ∈ s, μ i := by
    simp [massChooseMoment]
  rwa [this]

/-! ### Exception `ε_G (C₁ log S̄ / 6)^j → 0` on the band `j ≤ a L + 1` -/

theorem tendsto_log_div_sqrt_atTop :
    Tendsto (fun t : ℝ => Real.log t / Real.sqrt t) atTop (nhds 0) := by
  have h :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.sqrt_eq_rpow]

private theorem eventually_log_le_half_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, Real.log t ≤ (c / 2) * t * Real.sqrt t := by
  have h0 := tendsto_log_div_sqrt_atTop
  have hc2 : 0 < c / 2 := div_pos hc (by norm_num)
  filter_upwards [h0.eventually (Metric.ball_mem_nhds (0 : ℝ) hc2),
    eventually_ge_atTop (1 : ℝ)] with t htball ht1
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have habs : |Real.log t / Real.sqrt t| < c / 2 := by
    have : dist (Real.log t / Real.sqrt t) 0 < c / 2 := Metric.mem_ball.mp htball
    rw [Real.dist_eq, sub_zero] at this
    exact this
  have hlog : Real.log t ≤ (c / 2) * Real.sqrt t := by
    have hle : Real.log t / Real.sqrt t ≤ |Real.log t / Real.sqrt t| :=
      le_abs_self _
    have hlt : Real.log t / Real.sqrt t < c / 2 := hle.trans_lt habs
    exact (div_lt_iff₀ hsqrt).mp hlt |>.le
  have hmul : Real.sqrt t ≤ t * Real.sqrt t := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right ht1 hsqrt.le
  calc
    Real.log t ≤ (c / 2) * Real.sqrt t := hlog
    _ ≤ (c / 2) * (t * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hmul (div_nonneg hc.le (by norm_num))
    _ = (c / 2) * t * Real.sqrt t := by ring

private theorem tendsto_id_mul_sqrt_atTop :
    Tendsto (fun t : ℝ => t * Real.sqrt t) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have h1 : (1 : ℝ) ≤ Real.sqrt t :=
    (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) ht0).mpr (by simpa using ht)
  exact le_mul_of_one_le_right ht0 h1

private theorem tendsto_t_mul_exp_neg_three_halves {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => t * Real.exp (-k * t * Real.sqrt t)) atTop (nhds 0) := by
  have hle := eventually_log_le_half_sqrt hk
  have hbotBound : Tendsto (fun t : ℝ => -(k / 2) * t * Real.sqrt t) atTop atBot := by
    have hc2 : 0 < k / 2 := div_pos hk (by norm_num)
    have hpos := tendsto_id_mul_sqrt_atTop.const_mul_atTop hc2
    refine (tendsto_neg_atTop_atBot.comp hpos).congr' ?_
    filter_upwards with t
    simp [Function.comp]
    ring
  have hle' : ∀ᶠ t : ℝ in atTop,
      Real.log t - k * t * Real.sqrt t ≤ -(k / 2) * t * Real.sqrt t := by
    filter_upwards [hle, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    linarith
  have hbot : Tendsto (fun t : ℝ => Real.log t - k * t * Real.sqrt t) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    have hb := (tendsto_atBot.mp hbotBound) b
    filter_upwards [hle', hb] with t ht htbound
    exact ht.trans htbound
  have hexp : Tendsto (fun t : ℝ => Real.exp (Real.log t - k * t * Real.sqrt t))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hbot
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hlog : Real.exp (Real.log t) = t := Real.exp_log ht
  have hneg : -(k * t * Real.sqrt t) = -k * t * Real.sqrt t := by ring
  have : (Real.exp (k * t * Real.sqrt t))⁻¹ = Real.exp (-(k * t * Real.sqrt t)) :=
    (Real.exp_neg _).symm
  rw [Real.exp_sub, hlog, div_eq_mul_inv, this, hneg]

private theorem eventually_add_log_le_id (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, C + Real.log t ≤ t := by
  have hC : Tendsto (fun t : ℝ => C / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    refine (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_one]
  have hsum : Tendsto (fun t : ℝ => (C + Real.log t) / t) atTop (nhds 0) := by
    have hadd : Tendsto (fun t : ℝ => C / t + Real.log t / t) atTop (nhds (0 : ℝ)) := by
      simpa [add_zero] using hC.add hlog
    refine hadd.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  filter_upwards [hsum.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with t hball ht0
  have habs : |(C + Real.log t) / t| < 1 := by
    have : dist ((C + Real.log t) / t) 0 < 1 := Metric.mem_ball.mp hball
    rw [Real.dist_eq, sub_zero] at this
    exact this
  have : |C + Real.log t| < t := by
    rwa [abs_div, abs_of_pos ht0, div_lt_one ht0] at habs
  exact (le_abs_self (C + Real.log t)).trans this.le

theorem modelExceptionRate_nonneg {C c L G : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) :
    0 ≤ modelExceptionRate C c L G :=
  mul_nonneg (mul_nonneg hC hL) (Real.exp_nonneg _)

private theorem tendsto_sqrt_inv_atTop :
    Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop

/-- Uniform vanishing of the bad factorial-moment term on `1 ≤ j ≤ a L + 1`. -/
theorem eventually_exception_ratio_le_one
    (a C c C1 κ : ℝ)
    (ha : 0 < a) (hC : 0 < C) (hc : 0 < c) (hC1 : 0 < C1) (hκ : 0 < κ) :
    ∀ᶠ G : ℝ in atTop,
      ∀ (L Sbar : ℝ) (j : ℕ),
        1 ≤ L →
        L ≤ 2 * κ * Real.log G →
        Real.exp 1 ≤ Sbar →
        Sbar ≤ 5 * L * G →
        1 ≤ j →
        (j : ℝ) ≤ a * L + 1 →
        modelExceptionRate C c L G * (C1 * Real.log Sbar / 6) ^ j ≤ 1 := by
  have hc2 : 0 < c / 2 := div_pos hc (by norm_num)
  have hc4 : 0 < c / 4 := div_pos hc (by norm_num)
  have hB : 0 < 2 * a * κ + 1 :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg (mul_nonneg (by norm_num) ha.le) hκ.le) (by norm_num)
  have hδ : 0 < (c / 2) / (2 * a * κ + 1) := div_pos hc2 hB
  have htexp := tendsto_t_mul_exp_neg_three_halves hc2
  have hεmass :
      Tendsto (fun t : ℝ => (C * (2 * κ)) *
          (t * Real.exp (-(c / 2) * t * Real.sqrt t))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul htexp
  have hratio :
      Tendsto (fun t : ℝ => (Real.log (C1 / 3) + Real.log t) / Real.sqrt t)
        atTop (nhds 0) := by
    have hadd :
        Tendsto (fun t : ℝ =>
            Real.log (C1 / 3) * (Real.sqrt t)⁻¹ + Real.log t / Real.sqrt t)
          atTop (nhds (0 : ℝ)) := by
      simpa [mul_zero, add_zero] using
        (tendsto_const_nhds.mul tendsto_sqrt_inv_atTop).add tendsto_log_div_sqrt_atTop
    refine hadd.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp [hsqrt]
  have h10κ : 0 < 10 * κ := mul_pos (by norm_num) hκ
  filter_upwards [
    eventually_gt_atTop (Real.exp (Real.exp 1)),
    eventually_gt_atTop (1 : ℝ),
    (hεmass.comp Real.tendsto_log_atTop).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)),
    (hratio.comp Real.tendsto_log_atTop).eventually (Metric.ball_mem_nhds (0 : ℝ) hδ),
    Real.tendsto_log_atTop.eventually (eventually_log_le_half_sqrt hc2),
    Real.tendsto_log_atTop.eventually (eventually_add_log_le_id (Real.log (10 * κ))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 / (2 * κ))),
    (tendsto_id_mul_sqrt_atTop.const_mul_atTop hc4 |>.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (Real.log (C * (2 * κ))))] with
    G hGexp hG1 hεball hrb hloghalf hlogSbound h2κt hconstle
  intro L Sbar j hL hLlog hS1 hSle hj hjband
  have hGpos : 0 < G := lt_trans (by norm_num) hG1
  have ht : Real.exp 1 < Real.log G := (Real.lt_log_iff_exp_lt hGpos).mpr hGexp
  have htpos : 0 < Real.log G := lt_trans (Real.exp_pos 1) ht
  have ht1 : 1 ≤ Real.log G :=
    le_trans (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) ht.le
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hεnn : 0 ≤ modelExceptionRate C c L G :=
    modelExceptionRate_nonneg hC.le hLpos.le
  have hSpos : 0 < Sbar := lt_of_lt_of_le (Real.exp_pos 1) hS1
  have hlogSnn : 0 ≤ Real.log Sbar :=
    Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) hS1)
  have hr0 : 0 ≤ C1 * Real.log Sbar / 6 :=
    div_nonneg (mul_nonneg hC1.le hlogSnn) (by norm_num)
  have hsqrtG : 0 < Real.sqrt (Real.log G) := Real.sqrt_pos.mpr htpos
  have hmass :
      (C * (2 * κ)) *
          (Real.log G * Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G))) < 1 := by
    have : |((C * (2 * κ)) *
        (Real.log G * Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G))))| < 1 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Function.comp_apply] using hεball
    exact (le_abs_self _).trans_lt this
  have hεle : modelExceptionRate C c L G ≤
      (C * (2 * κ)) *
        (Real.log G * Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G))) := by
    have hLbound : L ≤ 2 * κ * Real.log G := hLlog
    have hexp_le :
        Real.exp (-c * Real.log G * Real.sqrt (Real.log G)) ≤
          Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G)) :=
      Real.exp_le_exp.mpr (by
        have hnn : 0 ≤ Real.log G * Real.sqrt (Real.log G) :=
          mul_nonneg htpos.le hsqrtG.le
        have hmul :=
          mul_le_mul_of_nonneg_right (by linarith : -c ≤ -(c / 2)) hnn
        simpa [mul_assoc] using hmul)
    have h1 : C * L * Real.exp (-c * logThreeHalves G) ≤
        C * (2 * κ * Real.log G) *
          Real.exp (-c * logThreeHalves G) := by
      calc
        C * L * Real.exp (-c * logThreeHalves G)
            = C * (L * Real.exp (-c * logThreeHalves G)) := by ring
        _ ≤ C * (2 * κ * Real.log G * Real.exp (-c * logThreeHalves G)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hLbound (Real.exp_nonneg _)) hC.le
        _ = C * (2 * κ * Real.log G) * Real.exp (-c * logThreeHalves G) := by ring
    have h2 : C * (2 * κ * Real.log G) * Real.exp (-c * logThreeHalves G) ≤
        C * (2 * κ * Real.log G) *
          Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G)) := by
      unfold logThreeHalves
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hC.le (mul_nonneg (mul_nonneg (by norm_num) hκ.le) htpos.le))
      simpa [mul_assoc] using hexp_le
    unfold modelExceptionRate
    have hring : C * (2 * κ * Real.log G) *
          Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G)) =
        (C * (2 * κ)) *
          (Real.log G * Real.exp (-(c / 2) * Real.log G * Real.sqrt (Real.log G))) := by
      ring
    exact (h1.trans h2).trans (le_of_eq hring)
  have hε1 : modelExceptionRate C c L G ≤ 1 := hεle.trans hmass.le
  set r := C1 * Real.log Sbar / 6
  by_cases hr1 : r ≤ 1
  · have hpow : r ^ j ≤ 1 := pow_le_one₀ hr0 hr1
    calc
      modelExceptionRate C c L G * r ^ j ≤ modelExceptionRate C c L G * 1 :=
        mul_le_mul_of_nonneg_left hpow hεnn
      _ = modelExceptionRate C c L G := mul_one _
      _ ≤ 1 := hε1
  · have hrgt : 1 < r := lt_of_not_ge hr1
    have h5LG : 0 < 5 * L * G :=
      mul_pos (mul_pos (by norm_num) hLpos) hGpos
    have hlogSle : Real.log Sbar ≤ Real.log (5 * L * G) :=
      (Real.log_le_log_iff hSpos h5LG).mpr hSle
    have h2κt' : 1 ≤ 2 * κ * Real.log G := by
      have : 1 / (2 * κ) ≤ Real.log G := h2κt
      have h2κpos : 0 < 2 * κ := mul_pos (by norm_num) hκ
      have hmul := mul_le_mul_of_nonneg_left this h2κpos.le
      have hcancel : (2 * κ) * (1 / (2 * κ)) = 1 := by
        field_simp [h2κpos.ne']
      rwa [hcancel] at hmul
    have hlogL : Real.log L ≤ Real.log (2 * κ * Real.log G) :=
      (Real.log_le_log_iff hLpos (mul_pos (mul_pos (by norm_num) hκ) htpos)).mpr hLlog
    have hlog5LG : Real.log (5 * L * G) =
        Real.log 5 + Real.log L + Real.log G := by
      have h5 : (5 : ℝ) ≠ 0 := by norm_num
      have hLne : L ≠ 0 := hLpos.ne'
      rw [mul_assoc, Real.log_mul h5 (mul_ne_zero hLne hGpos.ne'),
        Real.log_mul hLne hGpos.ne', ← add_assoc]
    have hlog5LG_le : Real.log (5 * L * G) ≤ 2 * Real.log G := by
      have hlog2κ : Real.log (2 * κ * Real.log G) =
          Real.log (2 * κ) + Real.log (Real.log G) :=
        Real.log_mul (mul_pos (by norm_num) hκ).ne' htpos.ne'
      have hsum : Real.log 5 + Real.log (2 * κ) + Real.log (Real.log G) + Real.log G ≤
          2 * Real.log G := by
        have : Real.log 5 + Real.log (2 * κ) = Real.log (10 * κ) := by
          have h10 : (10 : ℝ) = 5 * 2 := by norm_num
          rw [h10, mul_assoc, Real.log_mul (by norm_num : (5 : ℝ) ≠ 0)
            (mul_pos (by norm_num) hκ).ne']
        rw [this]
        have := hlogSbound
        linarith
      have : Real.log 5 + Real.log L + Real.log G ≤
          Real.log 5 + Real.log (2 * κ * Real.log G) + Real.log G := by
        linarith [hlogL]
      rw [hlog5LG]
      exact this.trans (by
        rw [hlog2κ]
        linarith [hsum])
    have hlogS2 : Real.log Sbar ≤ 2 * Real.log G := hlogSle.trans hlog5LG_le
    have hrle : r ≤ (C1 / 3) * Real.log G := by
      have : C1 * Real.log Sbar / 6 ≤ C1 * (2 * Real.log G) / 6 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogS2 hC1.le) (by norm_num)
      have hring : C1 * (2 * Real.log G) / 6 = (C1 / 3) * Real.log G := by
        rw [div_eq_mul_inv]
        ring
      exact this.trans (le_of_eq hring)
    have hrtpos : 0 < (C1 / 3) * Real.log G :=
      mul_pos (div_pos hC1 (by norm_num)) htpos
    have hlogr : Real.log r ≤ Real.log ((C1 / 3) * Real.log G) :=
      (Real.log_le_log_iff (lt_trans (by norm_num) hrgt) hrtpos).mpr hrle
    have hlogrt : Real.log ((C1 / 3) * Real.log G) =
        Real.log (C1 / 3) + Real.log (Real.log G) :=
      Real.log_mul (div_pos hC1 (by norm_num)).ne' htpos.ne'
    have hjB : (j : ℝ) ≤ (2 * a * κ + 1) * Real.log G := by
      have : a * L + 1 ≤ a * (2 * κ * Real.log G) + 1 := by
        have hmul : a * L ≤ a * (2 * κ * Real.log G) :=
          mul_le_mul_of_nonneg_left hLlog ha.le
        linarith [hmul]
      have hring : a * (2 * κ * Real.log G) + 1 ≤ (2 * a * κ + 1) * Real.log G := by
        have : 1 ≤ Real.log G := ht1
        linarith
      exact hjband.trans (this.trans hring)
    have hjr : (j : ℝ) * Real.log r ≤
        (2 * a * κ + 1) * Real.log G * Real.log ((C1 / 3) * Real.log G) := by
      have hlogrnn : 0 ≤ Real.log r := Real.log_nonneg hrgt.le
      exact mul_le_mul hjB hlogr hlogrnn
        (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.le) hκ.le)
          (by norm_num)) htpos.le)
    have hhalf : (2 * a * κ + 1) * Real.log G *
          Real.log ((C1 / 3) * Real.log G) ≤
        (c / 2) * Real.log G * Real.sqrt (Real.log G) := by
      have habs :
          |(Real.log (C1 / 3) + Real.log (Real.log G)) / Real.sqrt (Real.log G)| <
            (c / 2) / (2 * a * κ + 1) := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Function.comp_apply] using hrb
      have hlt :
          (Real.log (C1 / 3) + Real.log (Real.log G)) / Real.sqrt (Real.log G) <
            (c / 2) / (2 * a * κ + 1) :=
        (le_abs_self _).trans_lt habs
      have hmul := (div_lt_iff₀ hsqrtG).mp hlt
      have : Real.log (C1 / 3) + Real.log (Real.log G) <
          ((c / 2) / (2 * a * κ + 1)) * Real.sqrt (Real.log G) := hmul
      have hBnn : 0 ≤ 2 * a * κ + 1 := hB.le
      have hbound := mul_le_mul_of_nonneg_left this.le hBnn
      have hsimp : (2 * a * κ + 1) * (((c / 2) / (2 * a * κ + 1)) *
            Real.sqrt (Real.log G)) =
          (c / 2) * Real.sqrt (Real.log G) := by
        field_simp [hB.ne']
      rw [hsimp] at hbound
      have hbound' := mul_le_mul_of_nonneg_left hbound htpos.le
      rw [hlogrt]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbound'
    have hεrlog : Real.log (modelExceptionRate C c L G * r ^ j) ≤ 0 := by
      have hεpos : 0 < modelExceptionRate C c L G := by
        unfold modelExceptionRate
        exact mul_pos (mul_pos hC hLpos) (Real.exp_pos _)
      have hrpos : 0 < r := lt_trans (by norm_num) hrgt
      have hprodpos : 0 < modelExceptionRate C c L G * r ^ j :=
        mul_pos hεpos (pow_pos hrpos j)
      have hlogε : Real.log (modelExceptionRate C c L G) =
          Real.log C + Real.log L + (-c * logThreeHalves G) := by
        unfold modelExceptionRate
        have hCLne : C * L ≠ 0 := mul_ne_zero hC.ne' hLpos.ne'
        rw [Real.log_mul hCLne (Real.exp_ne_zero _),
          Real.log_mul hC.ne' hLpos.ne', Real.log_exp]
      have hlogprod : Real.log (modelExceptionRate C c L G * r ^ j) =
          Real.log (modelExceptionRate C c L G) + (j : ℝ) * Real.log r := by
        rw [Real.log_mul hεpos.ne' (pow_ne_zero j hrpos.ne'), Real.log_pow]
      rw [hlogprod, hlogε]
      have hlogLε : Real.log L ≤ Real.log (2 * κ * Real.log G) := hlogL
      have hsum : Real.log C + Real.log L - c * logThreeHalves G +
            (j : ℝ) * Real.log r ≤
          Real.log C + Real.log (2 * κ * Real.log G) - c * logThreeHalves G +
            (c / 2) * Real.log G * Real.sqrt (Real.log G) := by
        have hCLlog : Real.log C + Real.log L ≤
            Real.log C + Real.log (2 * κ * Real.log G) := by
          linarith [hlogLε]
        unfold logThreeHalves
        linarith [hCLlog, hjr, hhalf]
      have hlog2κG : Real.log (2 * κ * Real.log G) =
          Real.log (2 * κ) + Real.log (Real.log G) :=
        Real.log_mul (mul_pos (by norm_num) hκ).ne' htpos.ne'
      have hC2 : Real.log C + Real.log (2 * κ) = Real.log (C * (2 * κ)) :=
        (Real.log_mul hC.ne' (mul_pos (by norm_num) hκ).ne').symm
      have : Real.log C + Real.log (2 * κ * Real.log G) - c * logThreeHalves G +
            (c / 2) * Real.log G * Real.sqrt (Real.log G) ≤
          Real.log (C * (2 * κ)) + Real.log (Real.log G) -
            (c / 2) * Real.log G * Real.sqrt (Real.log G) := by
        rw [hlog2κG]
        unfold logThreeHalves
        linarith [hC2]
      have hfin : Real.log (C * (2 * κ)) + Real.log (Real.log G) -
            (c / 2) * Real.log G * Real.sqrt (Real.log G) ≤ 0 := by
        have hloghalf' : Real.log (Real.log G) ≤
            (c / 4) * Real.log G * Real.sqrt (Real.log G) := by
          have hcq : (c / 2) / 2 = (c / 4) := by ring
          have := hloghalf
          rw [hcq] at this
          simpa [mul_assoc] using this
        have hconst : Real.log (C * (2 * κ)) ≤
            (c / 4) * Real.log G * Real.sqrt (Real.log G) := by
          have := hconstle
          dsimp [Function.comp] at this
          simpa [mul_assoc] using this
        linarith [hloghalf', hconst]
      linarith [hsum, this, hfin]
    have hεpos' : 0 < modelExceptionRate C c L G :=
      mul_pos (mul_pos hC hLpos) (Real.exp_pos _)
    have hprodpos : 0 < modelExceptionRate C c L G * r ^ j :=
      mul_pos hεpos' (pow_pos (lt_trans (by norm_num) hrgt) j)
    have : Real.log (modelExceptionRate C c L G * r ^ j) ≤ Real.log 1 := by
      simpa [Real.log_one] using hεrlog
    exact (Real.log_le_log_iff hprodpos (by norm_num : (0 : ℝ) < 1)).mp this

/-! ### Rooted `θ` versus paper `V`, and the middle `u²/σ` ratio -/

theorem palmThetaPrimes_sdiff (z y : ℕ) :
    palmThetaPrimes (Nat.primesLE y \ Nat.primesLE z) = rootedEulerProdNat z y := by
  simp [palmThetaPrimes, palmTheta, palmHitProb, rootedEulerProdNat, one_div]

/-- Everywhere bound: `θ z ≤ V(y) z log z / e^{-30}` for `z ≥ 16`. -/
theorem rootedEulerProdNat_mul_le_log {z y : ℕ} (hz : 16 ≤ z) (hzy : z ≤ y) :
    rootedEulerProdNat z y * z ≤
      eulerProdNat y / eulerProdLowerConst * z * Real.log z := by
  have hz2 : 2 ≤ z := le_trans (by norm_num : (2 : ℕ) ≤ 16) hz
  have hdiv := rootedEulerProdNat_le_div hzy hz2
  have hV := eulerProdNat_ge_mul_inv_log hz
  have hzR : (16 : ℝ) ≤ z := Nat.cast_le.mpr hz
  have hlog : 0 < Real.log z :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 16) hzR)
  have hVpos : 0 < eulerProdNat z := eulerProdNat_pos z
  have hlowpos : 0 < eulerProdLowerConst / Real.log z :=
    div_pos eulerProdLowerConst_pos hlog
  have hinv : (eulerProdNat z)⁻¹ ≤ Real.log z / eulerProdLowerConst := by
    have := inv_anti₀ hlowpos hV
    rwa [inv_div] at this
  have hθ : rootedEulerProdNat z y * z ≤
      eulerProdNat y / eulerProdNat z * z :=
    mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg _)
  have hrew : eulerProdNat y / eulerProdNat z * z =
      eulerProdNat y * (eulerProdNat z)⁻¹ * z := by
    rw [div_eq_mul_inv]
  have hstep : eulerProdNat y * (eulerProdNat z)⁻¹ * z ≤
      eulerProdNat y * (Real.log z / eulerProdLowerConst) * z :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinv (eulerProdNat_pos y).le)
      (Nat.cast_nonneg _)
  have hring : eulerProdNat y * (Real.log z / eulerProdLowerConst) * z =
      eulerProdNat y / eulerProdLowerConst * z * Real.log z := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  exact hθ.trans (hrew.trans_le (hstep.trans (le_of_eq hring)))

/-- Paper `θ S̄ ≤ C₁ L log S̄` with `C₁ = 10 / e^{-30}`, once `V(y) G ≤ 2`
and `S̄ ≤ 5 L G`. -/
theorem rooted_Sbar_everywhere {z y : ℕ} {L G : ℝ}
    (hz : 16 ≤ z) (hzy : z ≤ y) (hL : 0 ≤ L) (_hG : 0 < G)
    (hS : (z : ℝ) ≤ 5 * L * G) (hcal : eulerProdNat y * G ≤ 2) :
    rootedEulerProdNat z y * z ≤
      (10 / eulerProdLowerConst) * L * Real.log z := by
  have hmain := rootedEulerProdNat_mul_le_log hz hzy
  have hzR : (16 : ℝ) ≤ z := Nat.cast_le.mpr hz
  have hlog : 0 ≤ Real.log z :=
    Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ 16) hzR)
  have hstep : eulerProdNat y / eulerProdLowerConst * z * Real.log z ≤
      eulerProdNat y / eulerProdLowerConst * (5 * L * G) * Real.log z :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hS
        (div_nonneg (eulerProdNat_pos y).le eulerProdLowerConst_pos.le))
      hlog
  have hcal' : eulerProdNat y * G ≤ 2 := hcal
  have hring : eulerProdNat y / eulerProdLowerConst * (5 * L * G) * Real.log z =
      (5 * (eulerProdNat y * G) / eulerProdLowerConst) * L * Real.log z := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have h5 : (5 * (eulerProdNat y * G) / eulerProdLowerConst) * L * Real.log z ≤
      (5 * 2 / eulerProdLowerConst) * L * Real.log z :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcal' (by norm_num))
          eulerProdLowerConst_pos.le)
        hL)
      hlog
  have h10 : (5 * 2 / eulerProdLowerConst) = 10 / eulerProdLowerConst := by
    ring
  calc
    rootedEulerProdNat z y * z
        ≤ eulerProdNat y / eulerProdLowerConst * z * Real.log z := hmain
    _ ≤ eulerProdNat y / eulerProdLowerConst * (5 * L * G) * Real.log z := hstep
    _ = (5 * (eulerProdNat y * G) / eulerProdLowerConst) * L * Real.log z := hring
    _ ≤ (5 * 2 / eulerProdLowerConst) * L * Real.log z := h5
    _ = (10 / eulerProdLowerConst) * L * Real.log z := by rw [h10]

/-- Middle-stage McDiarmid exponent: with `η = (log G)^{-1/4}`,
`u = η h V`, `σ ≤ K h² / t⁴` and `V ≥ c / t`, one has
`u² / σ ≥ (c² / K) (log G)^{3/2}`. -/
theorem middle_deviation_sq_ratio {η h V σ K t c : ℝ}
    (ht : 0 < t) (hh : 0 < h) (hK : 0 < K) (hσ : 0 < σ) (hc : 0 < c)
    (hηeq : η = (Real.sqrt (Real.sqrt t))⁻¹)
    (hσle : σ ≤ K * h ^ 2 / t ^ 4) (hV : c / t ≤ V) :
    η ^ 2 * h ^ 2 * V ^ 2 / σ ≥ (c ^ 2 / K) * t * Real.sqrt t := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hηsq : η ^ 2 = (Real.sqrt t)⁻¹ := by
    rw [hηeq, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg t)]
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hinvσ : t ^ 4 / (K * h ^ 2) ≤ σ⁻¹ := by
    have := inv_anti₀ hσ hσle
    rwa [inv_div] at this
  have hnumnn : 0 ≤ η ^ 2 * h ^ 2 * V ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hstep : η ^ 2 * h ^ 2 * V ^ 2 / σ =
      η ^ 2 * h ^ 2 * V ^ 2 * σ⁻¹ := by
    rw [div_eq_mul_inv]
  have hge : η ^ 2 * h ^ 2 * V ^ 2 * (t ^ 4 / (K * h ^ 2)) ≤
      η ^ 2 * h ^ 2 * V ^ 2 * σ⁻¹ :=
    mul_le_mul_of_nonneg_left hinvσ hnumnn
  have hsimp : η ^ 2 * h ^ 2 * V ^ 2 * (t ^ 4 / (K * h ^ 2)) =
      η ^ 2 * V ^ 2 * t ^ 4 / K := by
    have hcancel : h ^ 2 / (K * h ^ 2) = (1 : ℝ) / K := by
      field_simp [hh2.ne', hK.ne']
    calc
      η ^ 2 * h ^ 2 * V ^ 2 * (t ^ 4 / (K * h ^ 2))
          = η ^ 2 * V ^ 2 * t ^ 4 * (h ^ 2 / (K * h ^ 2)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ = η ^ 2 * V ^ 2 * t ^ 4 * ((1 : ℝ) / K) := by rw [hcancel]
      _ = η ^ 2 * V ^ 2 * t ^ 4 / K := by
        rw [mul_one_div]
  have hV2 : c ^ 2 / t ^ 2 ≤ V ^ 2 := by
    have hct : 0 ≤ c / t := div_nonneg hc.le ht.le
    have := pow_le_pow_left₀ hct hV 2
    rwa [div_pow] at this
  have hge2 : η ^ 2 * (c ^ 2 / t ^ 2) * t ^ 4 / K ≤ η ^ 2 * V ^ 2 * t ^ 4 / K :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hV2 (sq_nonneg _)) (pow_nonneg ht.le 4))
      hK.le
  have hsimp2 : η ^ 2 * (c ^ 2 / t ^ 2) * t ^ 4 / K = η ^ 2 * c ^ 2 * t ^ 2 / K := by
    have ht42 : t ^ 4 / t ^ 2 = t ^ 2 := by
      field_simp [ht.ne']
    calc
      η ^ 2 * (c ^ 2 / t ^ 2) * t ^ 4 / K
          = η ^ 2 * c ^ 2 * (t ^ 4 / t ^ 2) / K := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ = η ^ 2 * c ^ 2 * t ^ 2 / K := by rw [ht42]
  have hsimp3 : η ^ 2 * c ^ 2 * t ^ 2 / K = (c ^ 2 / K) * t * Real.sqrt t := by
    rw [hηsq]
    have hts : t / Real.sqrt t = Real.sqrt t := by
      calc
        t / Real.sqrt t
            = (Real.sqrt t * Real.sqrt t) / Real.sqrt t := by
          rw [Real.mul_self_sqrt ht.le]
        _ = Real.sqrt t := by
          exact mul_div_cancel_left₀ _ hsqrt.ne'
    have ht2 : t ^ 2 / Real.sqrt t = t * Real.sqrt t := by
      calc
        t ^ 2 / Real.sqrt t = t * t / Real.sqrt t := by ring
        _ = t * (t / Real.sqrt t) := by ring
        _ = t * Real.sqrt t := by rw [hts]
    calc
      (Real.sqrt t)⁻¹ * c ^ 2 * t ^ 2 / K
          = c ^ 2 / K * (t ^ 2 / Real.sqrt t) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ = c ^ 2 / K * (t * Real.sqrt t) := by rw [ht2]
      _ = (c ^ 2 / K) * t * Real.sqrt t := by ring
  have : (c ^ 2 / K) * t * Real.sqrt t ≤ η ^ 2 * h ^ 2 * V ^ 2 / σ := by
    calc
      (c ^ 2 / K) * t * Real.sqrt t
          = η ^ 2 * c ^ 2 * t ^ 2 / K := hsimp3.symm
      _ = η ^ 2 * (c ^ 2 / t ^ 2) * t ^ 4 / K := hsimp2.symm
      _ ≤ η ^ 2 * V ^ 2 * t ^ 4 / K := hge2
      _ = η ^ 2 * h ^ 2 * V ^ 2 * (t ^ 4 / (K * h ^ 2)) := hsimp.symm
      _ ≤ η ^ 2 * h ^ 2 * V ^ 2 * σ⁻¹ := hge
      _ = η ^ 2 * h ^ 2 * V ^ 2 / σ := hstep.symm
  exact this

end PrimeGapNormality.Prime
