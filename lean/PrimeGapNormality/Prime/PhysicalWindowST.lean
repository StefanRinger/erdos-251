import PrimeGapNormality.Prime.PhysicalPhaseRoute
import PrimeGapNormality.Prime.StatisticalPack
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic

/-!
# v0.6 — D-free S/T bridge: modes ⇒ window count ⇒ Cesàro

`PhysicalWindowCesaro.cesaroMeanVanishing_of_physicalWindow` stays as
the old generic lemma with `IndexPassageD`. This leaf is the new
route:

1. vanishing local means of all nontrivial integer modes of a nonempty
   finite family of real coordinates ⇒ `card(I_X) → ∞`
   (finite square kernel; `H` fixed before the limit);
2. `StrictMono`, `card(I_X) → ∞`, and vanishing local means of a
   bounded `f` ⇒ Cesàro means → 0, by repeated halving of the last
   index. Lean Cesàro on `range N` ends at `a (N-1)` when 0-based.

No `log(a_N)` bound and no doubling asymptotics of the count. A thin
subsequence of good scales does not suffice: every large integer `X`
with nonempty `I_X` is required.

Source: `rounds/round108/06_grok_exact_symmetry_and_st_delta.md` §5;
`05_paper_v0_6.tex` paragraph after `eq:globalroot`.
Contract: API
Audit: GREEN
-/

open Finset Filter Polynomial
open scoped Topology

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 2000000

/-! ### Circle-character helpers -/

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem e_zero : e 0 = 1 := by
  unfold e
  simp [Complex.exp_zero]

private theorem two_pi_I_mul (x : ℝ) :
    (2 * Real.pi * Complex.I * (x : ℂ) : ℂ) =
      Complex.I * (2 * Real.pi * x : ℝ) := by
  simp [mul_comm, mul_left_comm, Complex.ofReal_mul]

private theorem st_norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [two_pi_I_mul, Complex.norm_exp_I_mul_ofReal]

private theorem star_e (x : ℝ) : star (e x) = e (-x) := by
  have hx : e x ≠ 0 := by
    have hn : ‖e x‖ = 1 := st_norm_e x
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  apply mul_right_cancel₀ hx
  have hstar : star (e x) * e x = ‖e x‖ ^ 2 := by
    rw [mul_comm]
    change e x * starRingEnd ℂ (e x) = ‖e x‖ ^ 2
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hstar, st_norm_e]
  simp
  rw [← e_add, neg_add_cancel, e_zero]

private theorem ofReal_norm_sq (w : ℂ) :
    ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rfl

/-! ### Finite square kernel -/

/-- Finite square kernel `‖∑_{h<H} e(h u)‖² / H`. Diagonal 1, value
`H` at 0. No Fejér-limit theory. -/
noncomputable def squareKernel (H : ℕ) (u : ℝ) : ℝ :=
  (‖∑ h ∈ range H, e ((h : ℝ) * u)‖ ^ 2) / (H : ℝ)

private theorem squareKernel_nonneg (H : ℕ) (u : ℝ) :
    0 ≤ squareKernel H u :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private theorem squareKernel_at_zero {H : ℕ} (hH : 0 < H) :
    squareKernel H 0 = H := by
  have he : ∀ h ∈ range H, e ((h : ℝ) * (0 : ℝ)) = 1 := by
    intro h _
    rw [mul_zero, e_zero]
  have hsum : ∑ h ∈ range H, e ((h : ℝ) * (0 : ℝ)) = (H : ℂ) := by
    rw [sum_congr rfl he, sum_const, nsmul_eq_mul, mul_one]
    simp
  unfold squareKernel
  rw [hsum, Complex.norm_natCast]
  have hH0 : (H : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)
  field_simp [hH0]

private theorem squareKernel_expansion {H : ℕ} (hH : 0 < H) (u : ℝ) :
    (squareKernel H u : ℂ) =
      (∑ h ∈ range H, ∑ k ∈ range H,
        e (((h : ℝ) - (k : ℝ)) * u)) / (H : ℂ) := by
  unfold squareKernel
  have hS :
      ((‖∑ h ∈ range H, e ((h : ℝ) * u)‖ ^ 2 : ℝ) : ℂ) =
        (∑ h ∈ range H, e ((h : ℝ) * u)) *
          star (∑ h ∈ range H, e ((h : ℝ) * u)) :=
    ofReal_norm_sq _
  have hst :
      star (∑ h ∈ range H, e ((h : ℝ) * u)) =
        ∑ k ∈ range H, star (e ((k : ℝ) * u)) :=
    map_sum (starAddEquiv : ℂ ≃+ ℂ)
      (fun k : ℕ => e ((k : ℝ) * u)) (range H)
  have hterm : ∀ h k : ℕ,
      e ((h : ℝ) * u) * star (e ((k : ℝ) * u)) =
        e (((h : ℝ) - (k : ℝ)) * u) := by
    intro h k
    rw [star_e, ← e_add]
    congr 1
    ring
  have hprod :
      (∑ h ∈ range H, e ((h : ℝ) * u)) *
          star (∑ h ∈ range H, e ((h : ℝ) * u)) =
        ∑ h ∈ range H, ∑ k ∈ range H,
          e (((h : ℝ) - (k : ℝ)) * u) := by
    rw [hst, sum_mul_sum]
    simp_rw [hterm]
  rw [Complex.ofReal_div, hS, hprod, Complex.ofReal_natCast]

/-! ### Window count and integer-mode vanishing -/

/-- `card(seqWindow a X) → ∞` as a real filter. -/
def WindowCountToInfinity (a : ℕ → ℕ) : Prop :=
  Tendsto (fun X : ℕ => ((seqWindow a X).card : ℝ)) atTop atTop

/-- Local window means of `e(k ψ)` vanish for every nonzero integer
frequency. -/
def IntegerModeWindowVanishing (a : ℕ → ℕ) (ψ : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    PhysicalWindowMeanVanishing a fun n => e ((k : ℝ) * ψ n)

/-! ### Window-average helpers -/

private theorem mem_seqWindow_iff {a : ℕ → ℕ} (ha : StrictMono a)
    {X n : ℕ} : n ∈ seqWindow a X ↔ X < a n ∧ a n ≤ 2 * X := by
  simp only [seqWindow, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨le_trans (strictMono_le_id ha n) h.2, h⟩

private theorem windowAvg_const_mul (s : Finset ℕ) (c : ℂ) (f : ℕ → ℂ) :
    windowAvg s (fun n => c * f n) = c * windowAvg s f := by
  unfold windowAvg
  rw [← mul_sum, mul_div_assoc]

private theorem windowAvg_div_nat (s : Finset ℕ) (H : ℕ) (f : ℕ → ℂ) :
    windowAvg s (fun n => f n / (H : ℂ)) =
      windowAvg s f / (H : ℂ) := by
  unfold windowAvg
  rw [← sum_div, div_div, div_div]
  rw [mul_comm (s.card : ℂ)]

private theorem windowAvg_sum {ι : Type*} (s : Finset ℕ) (t : Finset ι)
    (f : ι → ℕ → ℂ) :
    windowAvg s (fun n => ∑ j ∈ t, f j n) =
      ∑ i ∈ t, windowAvg s (f i) := by
  unfold windowAvg
  rw [sum_comm, sum_div]

private theorem windowAvg_ofReal (s : Finset ℕ) (g : ℕ → ℝ) :
    windowAvg s (fun n => (g n : ℂ)) = (windowAvgReal s g : ℂ) := by
  unfold windowAvg windowAvgReal
  rw [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

private theorem windowAvg_one {s : Finset ℕ} (hs : s.Nonempty) :
    windowAvg s (fun _ => (1 : ℂ)) = 1 := by
  unfold windowAvg
  have h0 : (s.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (card_pos.mpr hs))
  simp [sum_const, nsmul_eq_mul, h0]

private theorem windowAvg_mul_card (s : Finset ℕ) (f : ℕ → ℂ) :
    windowAvg s f * (s.card : ℂ) = ∑ n ∈ s, f n := by
  unfold windowAvg
  by_cases h0 : s.card = 0
  · have hs : s = ∅ := card_eq_zero.mp h0
    simp [h0, hs]
  · have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h0
    field_simp [hc]

private theorem norm_sum_unimodular_card (s : Finset ℕ) (g : ℕ → ℂ)
    (hg : ∀ n, ‖g n‖ ≤ 1) : ‖∑ n ∈ s, g n‖ ≤ (s.card : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ n ∈ s, ‖g n‖ ≤ ∑ n ∈ s, (1 : ℝ) :=
    sum_le_sum fun _ _ => hg _
  have hc : (∑ n ∈ s, (1 : ℝ)) = (s.card : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_one]
  exact h1.trans_eq hc

private theorem tendsto_sum_nhds {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → ℝ) (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => ∑ i ∈ s, f i X) atTop (𝓝 0) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using tendsto_const_nhds (x := (0 : ℝ))
  · intro i t hit ih hf
    have hi := hf i (mem_insert_self i t)
    have ht : ∀ j ∈ t, Tendsto (f j) atTop (𝓝 0) :=
      fun j hj => hf j (mem_insert_of_mem hj)
    simp_rw [sum_insert hit]
    simpa using hi.add (ih ht)

private theorem int_sub_ne_zero {h k : ℕ} (hne : h ≠ k) :
    ((h : ℤ) - (k : ℤ)) ≠ 0 := by
  intro hz
  exact hne (Nat.cast_inj.mp (sub_eq_zero.mp hz))

private theorem offDiag_tendsto {a : ℕ → ℕ} {ψ : ℕ → ℝ} (H : ℕ)
    (hmodes : IntegerModeWindowVanishing a ψ) :
    Tendsto (fun X : ℕ =>
      ∑ h ∈ range H, ∑ k ∈ range H,
        if h = k then (0 : ℝ)
        else ‖windowAvg (seqWindow a X) (fun n =>
          e (((h : ℝ) - (k : ℝ)) * ψ n))‖)
      atTop (𝓝 0) := by
  refine tendsto_sum_nhds (range H) _ fun h _hh =>
    tendsto_sum_nhds (range H) _ fun k _hk => ?_
  by_cases hhk : h = k
  · simp [hhk]
  · have hne := int_sub_ne_zero hhk
    have ht := hmodes ((h : ℤ) - (k : ℤ)) hne
    have heq :
        (fun n => e (((h : ℝ) - (k : ℝ)) * ψ n)) =
          fun n => e ((((h : ℤ) - (k : ℤ) : ℤ) : ℝ) * ψ n) := by
      funext n
      congr 1
      simp
    have ht' :
        Tendsto (fun X : ℕ =>
          windowAvg (seqWindow a X) (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n)))
          atTop (𝓝 0) := by
      simpa [PhysicalWindowMeanVanishing, heq] using ht
    have hn := ht'.norm
    simpa [hhk, norm_zero] using hn

private theorem windowAvg_squareKernel_eq {H : ℕ} (hH : 0 < H)
    (s : Finset ℕ) (ψ : ℕ → ℝ) (α : ℝ) :
    windowAvg s (fun n => (squareKernel H (ψ n - α) : ℂ)) =
      (∑ h ∈ range H, ∑ k ∈ range H,
        e (-(((h : ℝ) - (k : ℝ)) * α)) *
          windowAvg s (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n))) / (H : ℂ) := by
  have hexp : ∀ n,
      (squareKernel H (ψ n - α) : ℂ) =
        (∑ h ∈ range H, ∑ k ∈ range H,
          e (((h : ℝ) - (k : ℝ)) * (ψ n - α))) / (H : ℂ) :=
    fun n => squareKernel_expansion hH (ψ n - α)
  have hfun :
      windowAvg s (fun n => (squareKernel H (ψ n - α) : ℂ)) =
        windowAvg s (fun n =>
          (∑ h ∈ range H, ∑ k ∈ range H,
            e (((h : ℝ) - (k : ℝ)) * (ψ n - α))) / (H : ℂ)) :=
    windowAvg_congr s fun n _ => hexp n
  rw [hfun, windowAvg_div_nat, windowAvg_sum]
  have hinner :
      (∑ h ∈ range H,
        windowAvg s (fun n =>
          ∑ k ∈ range H, e (((h : ℝ) - (k : ℝ)) * (ψ n - α)))) =
        ∑ h ∈ range H, ∑ k ∈ range H,
          windowAvg s (fun n =>
            e (((h : ℝ) - (k : ℝ)) * (ψ n - α))) := by
    refine sum_congr (s₁ := range H) (s₂ := range H) rfl fun h _ => ?_
    exact windowAvg_sum s (range H) _
  rw [hinner]
  have hphase : ∀ (h k : ℕ) (n : ℕ),
      e (((h : ℝ) - (k : ℝ)) * (ψ n - α)) =
        e (-(((h : ℝ) - (k : ℝ)) * α)) *
          e (((h : ℝ) - (k : ℝ)) * ψ n) := by
    intro h k n
    have hsum :
        ((h : ℝ) - (k : ℝ)) * (ψ n - α) =
          ((h : ℝ) - (k : ℝ)) * ψ n +
            (-(((h : ℝ) - (k : ℝ)) * α)) := by
      ring
    rw [hsum, e_add]
    exact mul_comm _ _
  have hmul : ∀ (h k : ℕ),
      windowAvg s (fun n =>
        e (((h : ℝ) - (k : ℝ)) * (ψ n - α))) =
        e (-(((h : ℝ) - (k : ℝ)) * α)) *
          windowAvg s (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n)) := by
    intro h k
    have hcong := windowAvg_congr s (f := fun n =>
        e (((h : ℝ) - (k : ℝ)) * (ψ n - α)))
      (g := fun n =>
        e (-(((h : ℝ) - (k : ℝ)) * α)) *
          e (((h : ℝ) - (k : ℝ)) * ψ n))
      (fun n _ => hphase h k n)
    rw [hcong, windowAvg_const_mul]
  refine congrArg (fun z => z / (H : ℂ)) ?_
  refine sum_congr (s₁ := range H) (s₂ := range H) rfl fun h _ =>
    sum_congr (s₁ := range H) (s₂ := range H) rfl fun k _ => hmul h k

private theorem windowAvg_squareKernel_sub_one_le {H : ℕ} (hH : 0 < H)
    {s : Finset ℕ} (hs : s.Nonempty) (ψ : ℕ → ℝ) (α : ℝ) :
    ‖windowAvg s (fun n => (squareKernel H (ψ n - α) : ℂ)) - 1‖ ≤
      (∑ h ∈ range H, ∑ k ∈ range H,
        if h = k then (0 : ℝ)
        else ‖windowAvg s (fun n =>
          e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / H := by
  have hH0 : (H : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hH)
  have hexp := windowAvg_squareKernel_eq hH s ψ α
  have hdiag :
      (∑ h ∈ range H, ∑ k ∈ range H,
        if h = k then
          windowAvg s (fun n => e (((h : ℝ) - (k : ℝ)) * ψ n))
        else (0 : ℂ)) =
        (H : ℂ) * windowAvg s (fun _ => (1 : ℂ)) := by
    have hterm : ∀ (h k : ℕ),
        (if h = k then
          windowAvg s (fun n => e (((h : ℝ) - (k : ℝ)) * ψ n))
        else (0 : ℂ)) =
          (if h = k then (windowAvg s (fun _ => (1 : ℂ))) else (0 : ℂ)) := by
      intro h k
      by_cases hhk : h = k
      · subst hhk
        rw [if_pos rfl, if_pos rfl]
        exact windowAvg_congr s fun n _ => by simp [sub_self, e_zero]
      · simp [hhk]
    have hsum :=
      sum_congr (s₁ := range H) (s₂ := range H) rfl (fun h _ =>
        sum_congr (s₁ := range H) (s₂ := range H) rfl fun k _ =>
          hterm h k)
    rw [hsum]
    have hdiag' :
        (∑ h ∈ range H, ∑ k ∈ range H,
          (if h = k then (windowAvg s (fun _ => (1 : ℂ))) else (0 : ℂ))) =
          ∑ h ∈ range H, windowAvg s (fun _ => (1 : ℂ)) := by
      refine sum_congr (s₁ := range H) (s₂ := range H) rfl fun h hh => ?_
      have hrow :
          (∑ k ∈ range H,
            if h = k then (windowAvg s (fun _ => (1 : ℂ))) else (0 : ℂ)) =
            windowAvg s (fun _ => (1 : ℂ)) := by
        have hk : h ∈ range H := hh
        rw [sum_ite_eq (b := fun _ => windowAvg s (fun _ => (1 : ℂ)))]
        simp [hk]
      exact hrow
    rw [hdiag', sum_const, nsmul_eq_mul, card_range]
  have hsplit :
      (∑ h ∈ range H, ∑ k ∈ range H,
        e (-(((h : ℝ) - (k : ℝ)) * α)) *
          windowAvg s (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n))) =
        (∑ h ∈ range H, ∑ k ∈ range H,
          if h = k then
            windowAvg s (fun n =>
              e (((h : ℝ) - (k : ℝ)) * ψ n))
          else (0 : ℂ)) +
          ∑ h ∈ range H, ∑ k ∈ range H,
            if h = k then (0 : ℂ)
            else
              e (-(((h : ℝ) - (k : ℝ)) * α)) *
                windowAvg s (fun n =>
                  e (((h : ℝ) - (k : ℝ)) * ψ n)) := by
    have hterm : ∀ (h k : ℕ),
        e (-(((h : ℝ) - (k : ℝ)) * α)) *
            windowAvg s (fun n =>
              e (((h : ℝ) - (k : ℝ)) * ψ n)) =
          (if h = k then
            windowAvg s (fun n =>
              e (((h : ℝ) - (k : ℝ)) * ψ n))
          else (0 : ℂ)) +
            if h = k then (0 : ℂ)
            else
              e (-(((h : ℝ) - (k : ℝ)) * α)) *
                windowAvg s (fun n =>
                  e (((h : ℝ) - (k : ℝ)) * ψ n)) := by
      intro h k
      by_cases hhk : h = k
      · subst hhk
        simp [sub_self, e_zero]
      · simp [hhk]
    have hpt :=
      sum_congr (s₁ := range H) (s₂ := range H) rfl (fun h _ =>
        sum_congr (s₁ := range H) (s₂ := range H) rfl fun k _ =>
          hterm h k)
    rw [hpt]
    simp_rw [sum_add_distrib]
  have havg1 := windowAvg_one hs
  have hexp' :
      windowAvg s (fun n => (squareKernel H (ψ n - α) : ℂ)) =
        1 +
          (∑ h ∈ range H, ∑ k ∈ range H,
            if h = k then (0 : ℂ)
            else
              e (-(((h : ℝ) - (k : ℝ)) * α)) *
                windowAvg s (fun n =>
                  e (((h : ℝ) - (k : ℝ)) * ψ n))) / (H : ℂ) := by
    rw [hexp, hsplit, hdiag, havg1, mul_one, add_div]
    have : ((H : ℂ) / (H : ℂ)) = 1 := div_self hH0
    rw [this]
  have hsub :
      windowAvg s (fun n => (squareKernel H (ψ n - α) : ℂ)) - 1 =
        (∑ h ∈ range H, ∑ k ∈ range H,
          if h = k then (0 : ℂ)
          else
            e (-(((h : ℝ) - (k : ℝ)) * α)) *
              windowAvg s (fun n =>
                e (((h : ℝ) - (k : ℝ)) * ψ n))) / (H : ℂ) := by
    rw [hexp']
    abel
  rw [hsub, norm_div, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg H)
  refine (norm_sum_le _ _).trans ?_
  refine sum_le_sum fun h _ => (norm_sum_le _ _).trans ?_
  refine sum_le_sum fun k _ => ?_
  by_cases hhk : h = k
  · simp [hhk]
  · simp [hhk, norm_mul, st_norm_e]

private theorem windowAvgReal_squareKernel_ge {H : ℕ} (hH : 0 < H)
    {s : Finset ℕ} (_hs : s.Nonempty) (ψ : ℕ → ℝ) {n0 : ℕ}
    (hn0 : n0 ∈ s) :
    (H : ℝ) / s.card ≤
      windowAvgReal s (fun n => squareKernel H (ψ n - ψ n0)) := by
  have hnn : ∀ n ∈ s, 0 ≤ squareKernel H (ψ n - ψ n0) :=
    fun _ _ => squareKernel_nonneg _ _
  have hdiag : squareKernel H (ψ n0 - ψ n0) = H := by
    rw [sub_self, squareKernel_at_zero hH]
  have hsum : (H : ℝ) ≤ ∑ n ∈ s, squareKernel H (ψ n - ψ n0) := by
    have := single_le_sum hnn hn0
    rwa [hdiag] at this
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- Paper: eventual nonemptiness of `I_X` is required so a counted
coordinate exists. Off-diagonal modes alone do not forbid empty
windows. -/
theorem ModesImplyWindowCount {ι : Type*} [Fintype ι] (a : ℕ → ℕ)
    (Ψ : ι → ℕ → ℝ) :
    StrictMono a → Nonempty ι →
      (∀ᶠ X : ℕ in atTop, (seqWindow a X).Nonempty) →
        (∀ i : ι, IntegerModeWindowVanishing a (Ψ i)) →
          WindowCountToInfinity a := by
  intro _ha hι hpos hmodes
  let i : ι := Classical.choice hι
  let ψ : ℕ → ℝ := Ψ i
  have hψ : IntegerModeWindowVanishing a ψ := hmodes i
  refine Filter.tendsto_atTop.mpr fun b => ?_
  rcases le_or_gt b 0 with hb0 | hbpos
  · exact Eventually.of_forall fun _ =>
      hb0.trans (Nat.cast_nonneg _)
  · obtain ⟨K, hKb⟩ := exists_nat_gt b
    have hK1 : 1 ≤ K :=
      Nat.succ_le_of_lt (Nat.cast_pos.mp (lt_trans hbpos hKb))
    let H : ℕ := 2 * K
    have hH : 0 < H := by
      have : 0 < 2 * K := Nat.mul_pos (by norm_num : 0 < 2)
        (lt_of_lt_of_le (by norm_num : 0 < 1) hK1)
      exact this
    have hE := offDiag_tendsto (H := H) hψ
    have hE0 : Tendsto (fun X : ℕ =>
        (∑ h ∈ range H, ∑ k ∈ range H,
          if h = k then (0 : ℝ)
          else ‖windowAvg (seqWindow a X) (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / H)
        atTop (𝓝 0) := by
      simpa using hE.div_const (H : ℝ)
    have hEev := hE0.eventually (Metric.ball_mem_nhds (0 : ℝ)
      (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hpos, hEev] with X hI hE1
    obtain ⟨n0, hn0⟩ := hI
    have hs : (seqWindow a X).Nonempty := ⟨n0, hn0⟩
    have hge :=
      windowAvgReal_squareKernel_ge hH hs ψ hn0
    have hbound :=
      windowAvg_squareKernel_sub_one_le hH hs ψ (ψ n0)
    have hz :
        windowAvg (seqWindow a X)
            (fun n => (squareKernel H (ψ n - ψ n0) : ℂ)) =
          (windowAvgReal (seqWindow a X)
            (fun n => squareKernel H (ψ n - ψ n0)) : ℂ) :=
      windowAvg_ofReal _ _
    rw [hz] at hbound
    have habs :
        |windowAvgReal (seqWindow a X)
            (fun n => squareKernel H (ψ n - ψ n0)) - 1| ≤
          (∑ h ∈ range H, ∑ k ∈ range H,
            if h = k then (0 : ℝ)
            else ‖windowAvg (seqWindow a X) (fun n =>
              e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / H := by
      have hn :
          ‖((windowAvgReal (seqWindow a X)
              (fun n => squareKernel H (ψ n - ψ n0)) : ℝ) : ℂ) - 1‖ =
            |windowAvgReal (seqWindow a X)
              (fun n => squareKernel H (ψ n - ψ n0)) - 1| := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
      simpa [hn] using hbound
    have hEabs : |((∑ h ∈ range H, ∑ k ∈ range H,
          if h = k then (0 : ℝ)
          else ‖windowAvg (seqWindow a X) (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / H)| < 1 := by
      have habsdiv :
          |((∑ h ∈ range H, ∑ k ∈ range H,
              if h = k then (0 : ℝ)
              else ‖windowAvg (seqWindow a X) (fun n =>
                e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / (H : ℝ))| =
            |(∑ h ∈ range H, ∑ k ∈ range H,
              if h = k then (0 : ℝ)
              else ‖windowAvg (seqWindow a X) (fun n =>
                e (((h : ℝ) - (k : ℝ)) * ψ n))‖)| / |(H : ℝ)| :=
        abs_div _ _
      have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
      simpa [habsdiv, abs_of_nonneg hHnn, Real.dist_eq, sub_zero]
        using hE1
    have hEle1 :
        (∑ h ∈ range H, ∑ k ∈ range H,
          if h = k then (0 : ℝ)
          else ‖windowAvg (seqWindow a X) (fun n =>
            e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / H ≤ 1 :=
      (abs_le.mp (le_of_lt hEabs)).2
    have havg_le :
        windowAvgReal (seqWindow a X)
            (fun n => squareKernel H (ψ n - ψ n0)) ≤ 2 := by
      have : windowAvgReal (seqWindow a X)
          (fun n => squareKernel H (ψ n - ψ n0)) ≤
            1 + (∑ h ∈ range H, ∑ k ∈ range H,
              if h = k then (0 : ℝ)
              else ‖windowAvg (seqWindow a X) (fun n =>
                e (((h : ℝ) - (k : ℝ)) * ψ n))‖) / H := by
        have hside := (abs_le.mp habs).2
        exact (sub_le_iff_le_add').mp hside
      exact this.trans ((add_le_add_right hEle1 (1 : ℝ)).trans_eq (by ring))
    have hHcard : (H : ℝ) / (seqWindow a X).card ≤ 2 :=
      hge.trans havg_le
    have hcpos : (0 : ℝ) < (seqWindow a X).card :=
      Nat.cast_pos.mpr (card_pos.mpr hs)
    have hmul : (H : ℝ) ≤ 2 * (seqWindow a X).card :=
      (div_le_iff₀ hcpos).mp hHcard
    have hHrw : (H : ℝ) = 2 * (K : ℝ) := by
      simp [H]
    have h2K : 2 * (K : ℝ) ≤ 2 * (seqWindow a X).card := by
      rwa [← hHrw]
    have hKle : (K : ℝ) ≤ (seqWindow a X).card :=
      (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp h2K
    exact hKb.le.trans hKle

/-! ### Endpoint halving for Cesàro -/

/-- Number of halvings of `b` while `⌊b/2⌋ ≥ X0`. Stops at `b = 0`. -/
def numHalves (X0 b : ℕ) : ℕ :=
  if h0 : b = 0 then
    0
  else if hX : b / 2 < X0 then
    0
  else
    have _hlt : b / 2 < b :=
      Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num : (1 : ℕ) < 2)
    numHalves X0 (b / 2) + 1
termination_by b

private theorem numHalves_of_lt {X0 b : ℕ} (hX : b / 2 < X0) :
    numHalves X0 b = 0 := by
  unfold numHalves
  split_ifs <;> rfl

private theorem numHalves_succ {X0 b : ℕ} (hb : b ≠ 0)
    (hX : ¬ b / 2 < X0) :
    numHalves X0 b = numHalves X0 (b / 2) + 1 := by
  rw [numHalves, dif_neg hb, dif_neg hX]

private theorem drop_card_le_one {a : ℕ → ℕ} (ha : StrictMono a) (b : ℕ) :
    ((range (seqCount a b)).filter
      (fun n => 2 * (b / 2) < a n)).card ≤ 1 := by
  refine card_le_one.mpr fun n hn m hm => ?_
  have hnT : n < seqCount a b := mem_range.mp (mem_filter.mp hn).1
  have hmT : m < seqCount a b := mem_range.mp (mem_filter.mp hm).1
  have han : a n ≤ b := (seqCount_lt_iff ha).mp hnT
  have ham : a m ≤ b := (seqCount_lt_iff ha).mp hmT
  have hna : 2 * (b / 2) < a n := (mem_filter.mp hn).2
  have hma : 2 * (b / 2) < a m := (mem_filter.mp hm).2
  have hsplit := Nat.div_add_mod b 2
  have hrem : b % 2 = 0 ∨ b % 2 = 1 := by
    have : b % 2 < 2 := Nat.mod_lt b (by norm_num)
    omega
  have hvaln : a n = b := by
    rcases hrem with h0 | h1
    · have : 2 * (b / 2) = b := by omega
      omega
    · have : 2 * (b / 2) = b - 1 := by omega
      omega
  have hvalm : a m = b := by
    rcases hrem with h0 | h1
    · have : 2 * (b / 2) = b := by omega
      omega
    · have : 2 * (b / 2) = b - 1 := by omega
      omega
  exact ha.injective (hvaln.trans hvalm.symm)

private theorem seqWindow_subset_seqCount {a : ℕ → ℕ} (ha : StrictMono a)
    (b : ℕ) : seqWindow a (b / 2) ⊆ range (seqCount a b) := by
  intro n hn
  have h := (mem_seqWindow_iff ha).mp hn
  have hle : a n ≤ b :=
    le_trans h.2 (Nat.mul_div_le b 2)
  exact mem_range.mpr ((seqCount_lt_iff ha).mpr hle)

private theorem seqCount_halve_subset {a : ℕ → ℕ} (ha : StrictMono a)
    (b : ℕ) : range (seqCount a (b / 2)) ⊆ range (seqCount a b) := by
  intro n hn
  have han : a n ≤ b / 2 := (seqCount_lt_iff ha).mp (mem_range.mp hn)
  have hle : a n ≤ b := le_trans han (Nat.div_le_self b 2)
  exact mem_range.mpr ((seqCount_lt_iff ha).mpr hle)

private theorem disjoint_window_seqCount {a : ℕ → ℕ} (ha : StrictMono a)
    (b : ℕ) :
    Disjoint (seqWindow a (b / 2)) (range (seqCount a (b / 2))) := by
  refine disjoint_left.mpr ?_
  intro n hnW hnL
  have hW := (mem_seqWindow_iff ha).mp hnW
  have hL : a n ≤ b / 2 := (seqCount_lt_iff ha).mp (mem_range.mp hnL)
  exact not_le_of_gt hW.1 hL

private theorem disjoint_union_drop {a : ℕ → ℕ} (ha : StrictMono a)
    (b : ℕ) :
    Disjoint
      (seqWindow a (b / 2) ∪ range (seqCount a (b / 2)))
      ((range (seqCount a b)).filter (fun n => 2 * (b / 2) < a n)) := by
  refine disjoint_left.mpr ?_
  intro n hnU hnD
  have hD : 2 * (b / 2) < a n := (mem_filter.mp hnD).2
  rcases mem_union.mp hnU with hnW | hnL
  · have hW := (mem_seqWindow_iff ha).mp hnW
    exact not_le_of_gt hD hW.2
  · have hL : a n ≤ b / 2 := (seqCount_lt_iff ha).mp (mem_range.mp hnL)
    have hle : a n ≤ 2 * (b / 2) :=
      le_trans hL (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2))
    exact not_le_of_gt hD hle

private theorem seqCount_eq_halve_union {a : ℕ → ℕ} (ha : StrictMono a)
    (b : ℕ) :
    range (seqCount a b) =
      seqWindow a (b / 2) ∪ range (seqCount a (b / 2)) ∪
        (range (seqCount a b)).filter (fun n => 2 * (b / 2) < a n) := by
  ext n
  constructor
  · intro hn
    have han : a n ≤ b := (seqCount_lt_iff ha).mp (mem_range.mp hn)
    by_cases hL : a n ≤ b / 2
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
        (mem_range.mpr ((seqCount_lt_iff ha).mpr hL)))))
    · have hgt : b / 2 < a n := Nat.not_le.mp hL
      by_cases hW : a n ≤ 2 * (b / 2)
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
          ((mem_seqWindow_iff ha).mpr ⟨hgt, hW⟩))))
      · have hD : 2 * (b / 2) < a n := Nat.not_le.mp hW
        exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn, hD⟩))
  · intro hn
    rcases mem_union.mp hn with hUL | hD
    · rcases mem_union.mp hUL with hW | hL
      · exact seqWindow_subset_seqCount ha b hW
      · exact seqCount_halve_subset ha b hL
    · exact (mem_filter.mp hD).1

private theorem sum_seqCount_halve {a : ℕ → ℕ} (ha : StrictMono a)
    (f : ℕ → ℂ) (b : ℕ) :
    ∑ n ∈ range (seqCount a b), f n =
      ∑ n ∈ seqWindow a (b / 2), f n +
        ∑ n ∈ range (seqCount a (b / 2)), f n +
          ∑ n ∈ (range (seqCount a b)).filter
            (fun n => 2 * (b / 2) < a n), f n := by
  have hU := seqCount_eq_halve_union ha b
  have hdis1 := disjoint_window_seqCount ha b
  have hdis2 := disjoint_union_drop ha b
  conv_lhs => rw [hU]
  rw [sum_union hdis2, sum_union hdis1]

private theorem norm_sum_seqCount_halving {a : ℕ → ℕ} (ha : StrictMono a)
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    {K X0 : ℕ} (_hK : 1 ≤ K) (hX0 : 1 ≤ X0)
    (havg : ∀ X, X0 ≤ X → ‖windowAvg (seqWindow a X) f‖ ≤ δ)
    (b : ℕ) :
    ‖∑ n ∈ range (seqCount a b), f n‖ ≤
      δ * (seqCount a b : ℝ) + numHalves X0 b + seqCount a (2 * X0) := by
  refine Nat.strong_induction_on b fun b ih => ?_
  by_cases h0 : b = 0
  · subst h0
    have hq : numHalves X0 0 = 0 := by
      unfold numHalves
      simp
    have hsc : seqCount a 0 ≤ seqCount a (2 * X0) :=
      seqCount_mono (Nat.zero_le _)
    have hnorm :=
      norm_sum_unimodular_card (range (seqCount a 0)) f hf
    have hcard : ((range (seqCount a 0)).card : ℝ) = (seqCount a 0 : ℝ) :=
      by simp
    rw [hcard] at hnorm
    have hδn : 0 ≤ δ * (seqCount a 0 : ℝ) :=
      mul_nonneg hδ (Nat.cast_nonneg _)
    have hle : (seqCount a 0 : ℝ) ≤ (seqCount a (2 * X0) : ℝ) :=
      Nat.cast_le.mpr hsc
    rw [hq, Nat.cast_zero, add_zero]
    exact hnorm.trans (hle.trans (le_add_of_nonneg_left hδn))
  · by_cases hX : b / 2 < X0
    · have hq : numHalves X0 b = 0 := numHalves_of_lt hX
      have hb : b < 2 * X0 := by
        have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp hX
        rwa [mul_comm] at this
      have hsc : seqCount a b ≤ seqCount a (2 * X0) :=
        seqCount_mono (Nat.le_of_lt hb)
      have hnorm :=
        norm_sum_unimodular_card (range (seqCount a b)) f hf
      have hcard : ((range (seqCount a b)).card : ℝ) = (seqCount a b : ℝ) :=
        by simp
      rw [hcard] at hnorm
      have hδn : 0 ≤ δ * (seqCount a b : ℝ) :=
        mul_nonneg hδ (Nat.cast_nonneg _)
      have hle : (seqCount a b : ℝ) ≤ (seqCount a (2 * X0) : ℝ) :=
        Nat.cast_le.mpr hsc
      rw [hq, Nat.cast_zero, add_zero]
      exact hnorm.trans (hle.trans (le_add_of_nonneg_left hδn))
    · have hXle : X0 ≤ b / 2 := Nat.not_lt.mp hX
      have hlt : b / 2 < b :=
        Nat.div_lt_self (Nat.pos_of_ne_zero h0)
          (by norm_num : (1 : ℕ) < 2)
      have ih' := ih (b / 2) hlt
      have hsplit := sum_seqCount_halve ha f b
      have hq : numHalves X0 b = numHalves X0 (b / 2) + 1 :=
        numHalves_succ h0 hX
      have hWle : ‖∑ n ∈ seqWindow a (b / 2), f n‖ ≤
          δ * ((seqWindow a (b / 2)).card : ℝ) := by
        have hAv := havg (b / 2) hXle
        have hmul := windowAvg_mul_card (seqWindow a (b / 2)) f
        have : ‖∑ n ∈ seqWindow a (b / 2), f n‖ =
            ‖windowAvg (seqWindow a (b / 2)) f‖ *
              ((seqWindow a (b / 2)).card : ℝ) := by
          rw [← hmul, norm_mul, Complex.norm_natCast]
        rw [this]
        exact mul_le_mul_of_nonneg_right hAv (Nat.cast_nonneg _)
      have hDle : ‖∑ n ∈ (range (seqCount a b)).filter
            (fun n => 2 * (b / 2) < a n), f n‖ ≤ 1 := by
        have hc := drop_card_le_one ha b
        have hn :=
          norm_sum_unimodular_card
            ((range (seqCount a b)).filter
              (fun n => 2 * (b / 2) < a n)) f hf
        exact hn.trans ((Nat.cast_le.mpr hc).trans_eq Nat.cast_one)
      have htri :
          ‖∑ n ∈ range (seqCount a b), f n‖ ≤
            ‖∑ n ∈ seqWindow a (b / 2), f n‖ +
              ‖∑ n ∈ range (seqCount a (b / 2)), f n‖ +
                ‖∑ n ∈ (range (seqCount a b)).filter
                  (fun n => 2 * (b / 2) < a n), f n‖ := by
        rw [hsplit]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      have hcards :
          ((seqWindow a (b / 2)).card : ℝ) +
            (seqCount a (b / 2) : ℝ) ≤ (seqCount a b : ℝ) := by
        have hU := seqCount_eq_halve_union ha b
        have hdis1 := disjoint_window_seqCount ha b
        have hdis2 := disjoint_union_drop ha b
        have hcu :
            ((seqWindow a (b / 2) ∪ range (seqCount a (b / 2))).card : ℝ) =
              ((seqWindow a (b / 2)).card : ℝ) +
                (seqCount a (b / 2) : ℝ) := by
          rw [card_union_of_disjoint hdis1, card_range, Nat.cast_add]
        have hct : (seqCount a b : ℝ) =
            ((seqWindow a (b / 2) ∪ range (seqCount a (b / 2))).card : ℝ) +
              (((range (seqCount a b)).filter
                (fun n => 2 * (b / 2) < a n)).card : ℝ) := by
          have hcard := congrArg (fun t : Finset ℕ => (t.card : ℝ)) hU
          rw [card_union_of_disjoint hdis2, Nat.cast_add, card_range] at hcard
          exact hcard
        have hDnn :
            0 ≤ (((range (seqCount a b)).filter
              (fun n => 2 * (b / 2) < a n)).card : ℝ) :=
          Nat.cast_nonneg _
        have : ((seqWindow a (b / 2)).card : ℝ) +
            (seqCount a (b / 2) : ℝ) ≤ (seqCount a b : ℝ) := by
          rw [← hcu, hct]
          exact le_add_of_nonneg_right hDnn
        exact this
      have hδW : δ * ((seqWindow a (b / 2)).card : ℝ) +
          δ * (seqCount a (b / 2) : ℝ) ≤ δ * (seqCount a b : ℝ) := by
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left hcards hδ
      have hmid :
          ‖∑ n ∈ seqWindow a (b / 2), f n‖ +
              ‖∑ n ∈ range (seqCount a (b / 2)), f n‖ +
                ‖∑ n ∈ (range (seqCount a b)).filter
                  (fun n => 2 * (b / 2) < a n), f n‖ ≤
            δ * ((seqWindow a (b / 2)).card : ℝ) +
              (δ * (seqCount a (b / 2) : ℝ) + numHalves X0 (b / 2) +
                seqCount a (2 * X0)) + 1 :=
        add_le_add (add_le_add hWle ih') hDle
      have hclose :
          δ * ((seqWindow a (b / 2)).card : ℝ) +
              (δ * (seqCount a (b / 2) : ℝ) + numHalves X0 (b / 2) +
                seqCount a (2 * X0)) + 1 ≤
            δ * (seqCount a b : ℝ) + numHalves X0 b +
              seqCount a (2 * X0) := by
        have hrearr :
            δ * ((seqWindow a (b / 2)).card : ℝ) +
                (δ * (seqCount a (b / 2) : ℝ) + numHalves X0 (b / 2) +
                  seqCount a (2 * X0)) + 1 =
              (δ * ((seqWindow a (b / 2)).card : ℝ) +
                δ * (seqCount a (b / 2) : ℝ)) +
                ((numHalves X0 (b / 2) : ℝ) + 1) +
                  seqCount a (2 * X0) := by
          ring
        have hgoal :
            δ * (seqCount a b : ℝ) + numHalves X0 b +
                seqCount a (2 * X0) =
              δ * (seqCount a b : ℝ) +
                ((numHalves X0 (b / 2) : ℝ) + 1) +
                  seqCount a (2 * X0) := by
          rw [hq, Nat.cast_add, Nat.cast_one]
        rw [hrearr, hgoal]
        exact add_le_add_left (add_le_add_left hδW
            ((numHalves X0 (b / 2) : ℝ) + 1))
          (seqCount a (2 * X0) : ℝ)
      exact htri.trans (hmid.trans hclose)

private theorem numHalves_mul_K_le {a : ℕ → ℕ} (ha : StrictMono a)
    {K X0 : ℕ} (_hK : 1 ≤ K) (_hX0 : 1 ≤ X0)
    (hcard : ∀ X, X0 ≤ X → K ≤ (seqWindow a X).card) (b : ℕ) :
    numHalves X0 b * K ≤ seqCount a b := by
  refine Nat.strong_induction_on b fun b ih => ?_
  by_cases h0 : b = 0
  · subst h0
    simp [numHalves]
  · by_cases hX : b / 2 < X0
    · rw [numHalves_of_lt hX, zero_mul]
      exact Nat.zero_le _
    · have hXle : X0 ≤ b / 2 := Nat.not_lt.mp hX
      have hlt : b / 2 < b :=
        Nat.div_lt_self (Nat.pos_of_ne_zero h0)
          (by norm_num : (1 : ℕ) < 2)
      have hq : numHalves X0 b = numHalves X0 (b / 2) + 1 :=
        numHalves_succ h0 hX
      have hW : K ≤ (seqWindow a (b / 2)).card := hcard (b / 2) hXle
      have ih' := ih (b / 2) hlt
      have hU := seqCount_eq_halve_union ha b
      have hdis1 := disjoint_window_seqCount ha b
      have hdis2 := disjoint_union_drop ha b
      have hcu :
          (seqWindow a (b / 2) ∪ range (seqCount a (b / 2))).card =
            (seqWindow a (b / 2)).card + seqCount a (b / 2) := by
        rw [card_union_of_disjoint hdis1, card_range]
      have hct :
          seqCount a b =
            (seqWindow a (b / 2) ∪ range (seqCount a (b / 2))).card +
              ((range (seqCount a b)).filter
                (fun n => 2 * (b / 2) < a n)).card := by
        have hcard := congrArg Finset.card hU
        rw [card_union_of_disjoint hdis2, card_range] at hcard
        exact hcard
      have hsumle :
          (seqWindow a (b / 2)).card + seqCount a (b / 2) ≤
            seqCount a b := by
        rw [hct, hcu]
        exact Nat.le_add_right _ _
      have : (numHalves X0 (b / 2) + 1) * K ≤
          (seqWindow a (b / 2)).card + seqCount a (b / 2) := by
        rw [add_mul, one_mul]
        exact (add_le_add ih' hW).trans_eq (add_comm _ _)
      rw [hq]
      exact this.trans hsumle

/-- §5.2: growing window counts and local means give Cesàro. No
`IndexPassageD`. -/
def WindowCountToCesaro (a : ℕ → ℕ) : Prop :=
  StrictMono a →
    WindowCountToInfinity a →
      ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ 1) →
        PhysicalWindowMeanVanishing a f → CesaroMeanVanishing f

theorem windowCountToCesaro (a : ℕ → ℕ) : WindowCountToCesaro a := by
  intro ha hcount f hf hW
  unfold CesaroMeanVanishing
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε3 : (0 : ℝ) < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨K0, hK0⟩ := exists_nat_gt (3 / ε)
  let K : ℕ := max K0 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKpos : (0 : ℝ) < K :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : 0 < 1) hK1)
  have hKε : (1 : ℝ) / K < ε / 3 := by
    have hK0le : (K0 : ℝ) ≤ K := Nat.cast_le.mpr (le_max_left _ _)
    have hlt : (3 : ℝ) / ε < K := hK0.trans_le hK0le
    have : (3 : ℝ) < K * ε := (div_lt_iff₀ hε).mp hlt
    have : (1 : ℝ) * 3 < ε * K := by
      simpa [mul_comm] using this
    exact (div_lt_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 3)).mpr this
  have hcardEv :
      ∀ᶠ X : ℕ in atTop, (K : ℝ) ≤ (seqWindow a X).card :=
    Filter.tendsto_atTop.mp hcount (K : ℝ)
  have hWEv :=
    hW.eventually (Metric.ball_mem_nhds (0 : ℂ) hε3)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hcardEv
  obtain ⟨X2, hX2⟩ := eventually_atTop.mp hWEv
  let X0 : ℕ := max (max X1 X2) 1
  have hX0 : 1 ≤ X0 := le_max_right _ _
  have hX0X1 : X1 ≤ X0 := le_trans (le_max_left X1 X2) (le_max_left _ _)
  have hX0X2 : X2 ≤ X0 := le_trans (le_max_right X1 X2) (le_max_left _ _)
  have havg : ∀ X, X0 ≤ X →
      ‖windowAvg (seqWindow a X) f‖ ≤ ε / 3 := fun X hX =>
    le_of_lt (by
      have := hX2 X (le_trans hX0X2 hX)
      simpa [dist_eq_norm] using this)
  have hKnat : ∀ X, X0 ≤ X → K ≤ (seqWindow a X).card := fun X hX =>
    Nat.cast_le.mp (hX1 X (le_trans hX0X1 hX))
  have hA :=
    (tendsto_const_div_atTop_nhds_zero_nat
      (seqCount a (2 * X0) : ℝ)).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hε3)
  filter_upwards [eventually_ge_atTop 1, hA] with N hN1 hAabs
  have hNpos : 0 < N := Nat.succ_le_iff.mp hN1
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hseq : seqCount a (a (N - 1)) = N := by
    rw [seqCount_apply_self ha (N - 1), Nat.sub_add_cancel hN1]
  have hsum :=
    norm_sum_seqCount_halving ha hf (le_of_lt hε3) hK1 hX0 havg
      (a (N - 1))
  have hnum : ‖∑ n ∈ range N, f n‖ ≤
      (ε / 3) * N + numHalves X0 (a (N - 1)) +
        seqCount a (2 * X0) := by
    simpa [hseq] using hsum
  have hdiv : ‖(∑ n ∈ range N, f n) / N‖ =
      ‖∑ n ∈ range N, f n‖ / N := by
    rw [norm_div, Complex.norm_natCast]
  have hqK :
      numHalves X0 (a (N - 1)) * K ≤ N := by
    have := numHalves_mul_K_le ha hK1 hX0 hKnat (a (N - 1))
    rwa [hseq] at this
  have hqN : (numHalves X0 (a (N - 1)) : ℝ) / N ≤ 1 / K := by
    have hmul : (numHalves X0 (a (N - 1)) : ℝ) * K ≤ N := by
      rw [← Nat.cast_mul]
      exact Nat.cast_le.mpr hqK
    exact (div_le_div_iff₀ hNposR hKpos).mpr (by
      simpa [mul_comm] using hmul)
  have hAabs' :
      (seqCount a (2 * X0) : ℝ) / N < ε / 3 := by
    have hnn : 0 ≤ (seqCount a (2 * X0) : ℝ) / N :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have : dist ((seqCount a (2 * X0) : ℝ) / N) 0 < ε / 3 := hAabs
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at this
  have hbound :
      ‖(∑ n ∈ range N, f n) / N‖ ≤
        ε / 3 + (1 : ℝ) / K + (seqCount a (2 * X0) : ℝ) / N := by
    rw [hdiv]
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hNpos)
    have hdiv' :
        ((ε / 3) * N + numHalves X0 (a (N - 1)) +
            seqCount a (2 * X0)) / N =
          ε / 3 + (numHalves X0 (a (N - 1)) : ℝ) / N +
            (seqCount a (2 * X0) : ℝ) / N := by
      field_simp [hN0]
    have hle' :
        ‖∑ n ∈ range N, f n‖ / N ≤
          ((ε / 3) * N + numHalves X0 (a (N - 1)) +
            seqCount a (2 * X0)) / N :=
      div_le_div_of_nonneg_right hnum (Nat.cast_nonneg N)
    have hle'' := hle'.trans_eq hdiv'
    exact hle''.trans
      (add_le_add_left (add_le_add_right hqN (ε / 3)) _)
  have hsumlt :
      ε / 3 + (1 : ℝ) / K + (seqCount a (2 * X0) : ℝ) / N < ε := by
    have hrest : (1 : ℝ) / K + (seqCount a (2 * X0) : ℝ) / N <
        ε / 3 + ε / 3 := add_lt_add hKε hAabs'
    have hlt' : ε / 3 + ((1 : ℝ) / K + (seqCount a (2 * X0) : ℝ) / N) <
        ε / 3 + (ε / 3 + ε / 3) := add_lt_add_right hrest (ε / 3)
    have hassoc :
        ε / 3 + ((1 : ℝ) / K + (seqCount a (2 * X0) : ℝ) / N) =
          ε / 3 + (1 : ℝ) / K + (seqCount a (2 * X0) : ℝ) / N := by
      ring
    have hsplit' : ε / 3 + (ε / 3 + ε / 3) = ε := by
      ring
    rw [hassoc] at hlt'
    rwa [hsplit'] at hlt'
  have hlt := lt_of_le_of_lt hbound hsumlt
  simpa [dist_zero_right] using hlt

/-- v0.6 S/T consumer on `nthPrime`. Explicitly **omits**
`IndexPassageD`, `TruncatedPhaseWindowIndexMatch`, and
`UniformOrbitTail`. `GapTailT` is the remaining T-input. Cut transfer
is the first-`L` fragment of S. Character remainder restores the
infinite phase on the same physical window.

`WindowCountToInfinity` and `WindowCountToCesaro` are **not**
consumer hypotheses: they are proved by `ModesImplyWindowCount`
(with nonempty `I_X`) and `windowCountToCesaro`. Rank-shift is
absent. Periodic `P : ℕ → ℝ[X]` is kept only as the existing cut-
transfer input; the Weyl montage must still go through a fixed
Ψ-vector and its integer modes, not a new arithmetic rank-shift. -/
def StatisticalConsumerST (P : ℕ → ℝ[X]) (B : ℕ) (ρ : ℝ) (G : ℕ → ℝ) :
    Prop :=
  Summable (fun n : ℕ =>
      eval (primeGap n : ℝ) (P n) / (B : ℝ) ^ (n + 1)) ∧
    (∀ n, ∃ z : ℤ, eval (primeGap n : ℝ) (P n) = z) ∧
      TruncatedPhaseCutTransfer nthPrime P B ρ G ∧
        (∀ ω : ℕ → SieveMixture,
          Tendsto (fun X : ℕ => mixtureCalib (ω X) (G X)) atTop (𝓝 0) →
            ModelTruncatedPhaseVanishing P B ρ G ω) ∧
          TruncatedPhaseSpanCutVanishing nthPrime P B ρ G ∧
            PhysicalPhaseRemainderVanishing nthPrime P B
                (fun X => stdProfileL ρ (G X)) ∧
              GapTailT nthPrime ρ G

/-- Named end-contract: S/T consumer plus proved window-count/Cesàro
⇒ Weyl. Not a theorem until the remaining conjuncts and the mode
vector are filled. Rank-shift is absent, so this stays a named
`Prop`. -/
def WeylOfStatisticalConsumerST : Prop :=
  ∀ (P : ℕ → ℝ[X]) (B : ℕ) (ρ : ℝ) (G : ℕ → ℝ),
    2 ≤ B → StatisticalConsumerST P B ρ G →
      WindowCountToInfinity nthPrime →
        WindowCountToCesaro nthPrime →
          weylCriterion B (gapPolySeries P B)

/-- Forum shape under Kuperberg: remaining extra input besides
`2 ≤ B` is the S/T consumer. Window-count and Cesàro are separate
proved outputs, not D. -/
def KuperbergToWeylST (P : ℕ → ℝ[X]) (B : ℕ) (ρ : ℝ) (G : ℕ → ℝ) : Prop :=
  KuperbergConj13 → 2 ≤ B → StatisticalConsumerST P B ρ G →
    WindowCountToInfinity nthPrime → WindowCountToCesaro nthPrime →
      weylCriterion B (gapPolySeries P B)

end PrimeGapNormality.Prime
