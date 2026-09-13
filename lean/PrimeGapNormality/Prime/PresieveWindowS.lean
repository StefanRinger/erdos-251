import PrimeGapNormality.Prime.EulerProd
import PrimeGapNormality.Prime.GridWindow
import PrimeGapNormality.Prime.ResidueHoeffding
import PrimeGapNormality.Prime.StatisticalCriterion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# v0.6 — one presieve through `S` for cells and the full window

No extra sieve stage `S < p ≤ G^4`. The same `U_S` is counted on every
full `h`-cell in `(0, S']` **and** on `[1, S]`. Paper
`eq:relativegrid` / `eq:gridexception`.

CRT rounding is a count error; the Brun product remainder is first
relative to `η V(w)`, then multiplied by length. Do not replace the
exponentially small exception by the later `O(1/L)` count band.

`RelativeCellCountsOn` stays the finite-cell interface. This leaf
adds the whole-window clause. Bounded-difference product work in
`ResidueHoeffding` remains the `w < p ≤ S` engine.

Source: `rounds/round108/05_paper_v0_6.tex` after `eq:gridspan`;
`06_grok_exact_symmetry_and_st_delta.md` §4 and §7.2.
Do not import `ActualRootLaw` (Coupling is already on the
`ResidueHoeffding` chain; `bernoulliThin` would clash).
Survivors in `[1,S]` are inlined as `presieveSurvivors`.
-/

open Finset
open scoped Classical
open scoped symmDiff

namespace PrimeGapNormality.Prime

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Paper `S' = h ⌊S/h⌋`. -/
def presieveSpanEnd (S h : ℕ) : ℕ :=
  h * (S / h)

/-- Relative occupancy of one interval: count vs `v * length`. -/
def RelativeCountOnInterval (U I : Finset ℕ) (v η : ℝ) : Prop :=
  |(((U ∩ I).card : ℝ) - (I.card : ℝ) * v)| ≤ η * (I.card : ℝ) * v

/-- Full `h`-cells through `S'` together with the whole `[1, S]`. -/
def PresieveCellsAndWindow (U : Finset ℕ) (S h : ℕ) (v η : ℝ) : Prop :=
  let S' := presieveSpanEnd S h
  RelativeCellCountsOn U h v η (fullPrefixCells S' h) ∧
    RelativeCountOnInterval U (Icc 1 S) v η

/-- Paper `eq:gridexception`: bad probability
`≤ C L exp(-c (log G)^{3/2})`. -/
def GridExceptionLe (C c : ℝ) (L : ℕ) (G ε : ℝ) : Prop :=
  ε ≤ C * (L : ℝ) * Real.exp (-c * Real.log G ^ ((3 : ℝ) / 2))

/-- Survivors in `[1,S]` for one residue choice through `S`.
Same window as `ActualRootLaw.sieveSurvivorsFin S σ S`, inlined so
this file never imports `ActualRootLaw`. -/
noncomputable def presieveSurvivors (S : ℕ) (σ : ResidueChoice S) :
    Finset ℕ :=
  (Icc 1 S).filter fun n => sieveSurvives S (residueOfChoice S σ) n

/-- Residue-choice probability that cells or `[1,S]` fail.
Not `∃ U`: one good configuration does not prove high probability. -/
noncomputable def badPresieveProb (S h : ℕ) (η : ℝ) : ℝ :=
  (((univ : Finset (ResidueChoice S)).filter
      fun σ => ¬ PresieveCellsAndWindow (presieveSurvivors S σ) S h
        (eulerProdNat S) η).card : ℝ) /
    (Fintype.card (ResidueChoice S) : ℝ)

/-- Joint statement: the actual residue-choice probability of a
bad presieve is at most the grid-exception scale. Width `h > 0`
and `v = V(S)` are part of the event, not a free existential `U`. -/
def PresieveToS (S h : ℕ) (η C c : ℝ) (L : ℕ) (G ε : ℝ) : Prop :=
  0 < h ∧
    GridExceptionLe C c L G ε ∧
      badPresieveProb S h η ≤ ε

/-- Factorial occupancy moment of a concrete mass `μ` on `A`. -/
noncomputable def factorialMoment (A : Finset ℕ) (μ : Finset ℕ → ℝ)
    (j : ℕ) : ℝ :=
  ∑ E ∈ A.powerset, (Nat.choose E.card j : ℝ) * μ E

/-- Moment hull `(12 L)^j / j!` for the **actual** factorial moment of
`μ`, uniformly for `j ≤ a L + 1`. Constants `12`, `d0 > 24 e`,
`a > d0` stay. Do not instantiate this by choosing a free scalar `C`. -/
def ModelMomentHull (A : Finset ℕ) (μ : Finset ℕ → ℝ) (L a j : ℕ) :
    Prop :=
  j ≤ a * L + 1 →
    factorialMoment A μ j ≤
      (12 * (L : ℝ)) ^ j / (Nat.factorial j : ℝ)

/-! ### Paper scales `eq:gridspan` -/

/-- Paper `η = (log G)^{-1/4}`. -/
noncomputable def presieveEta (G : ℝ) : ℝ :=
  modelEta G

/-- Paper `w = ⌊(log G)^4⌋`. -/
noncomputable def presieveW (G : ℝ) : ℕ :=
  residueMcDiarmidCutoff G

theorem presieveEta_eq (G : ℝ) : presieveEta G = modelEta G :=
  rfl

theorem presieveW_eq (G : ℝ) :
    presieveW G = ⌊Real.log G ^ (4 : ℕ)⌋₊ :=
  rfl

theorem presieveEta_eq_rpow {G : ℝ} (hG : 1 < G) :
    presieveEta G = Real.log G ^ (-((1 : ℝ) / 4)) := by
  have hlog : 0 < Real.log G := Real.log_pos hG
  have hsqrt :
      Real.sqrt (Real.sqrt (Real.log G)) = Real.log G ^ ((1 : ℝ) / 4) := by
    have h1 : Real.sqrt (Real.log G) = Real.log G ^ ((1 : ℝ) / 2) :=
      Real.sqrt_eq_rpow _
    have h2 :
        Real.sqrt (Real.sqrt (Real.log G)) =
          (Real.log G ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
      rw [h1, Real.sqrt_eq_rpow]
    have hmul : ((1 : ℝ) / 2) * (1 / 2) = 1 / 4 := by norm_num
    rw [h2, ← Real.rpow_mul hlog.le, hmul]
  unfold presieveEta modelEta
  rw [hsqrt, ← Real.rpow_neg hlog.le]

theorem logThreeHalves_eq_rpow {G : ℝ} (hG : 1 < G) :
    logThreeHalves G = Real.log G ^ ((3 : ℝ) / 2) := by
  have hlog : 0 < Real.log G := Real.log_pos hG
  unfold logThreeHalves
  have hadd : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  rw [hadd, Real.rpow_add hlog, Real.rpow_one, Real.sqrt_eq_rpow]

theorem gridExceptionLe_iff_model {C c : ℝ} {L : ℕ} {G ε : ℝ}
    (hG : 1 < G) :
    GridExceptionLe C c L G ε ↔
      ε ≤ modelExceptionRate C c (L : ℝ) G := by
  unfold GridExceptionLe modelExceptionRate
  rw [logThreeHalves_eq_rpow hG]

/-! ### Span `S' = h ⌊S/h⌋` and full cells -/

theorem presieveSpanEnd_le (S h : ℕ) : presieveSpanEnd S h ≤ S := by
  unfold presieveSpanEnd
  exact Nat.mul_div_le S h

theorem presieveSpanEnd_dvd {S h : ℕ} (hh : 0 < h) :
    h ∣ presieveSpanEnd S h :=
  ⟨S / h, rfl⟩

theorem presieveSpanEnd_div {S h : ℕ} (hh : 0 < h) :
    presieveSpanEnd S h / h = S / h := by
  unfold presieveSpanEnd
  exact Nat.mul_div_cancel_left (S / h) hh

theorem mem_fullPrefixCells_iff {S h r : ℕ} (hh : 0 < h) :
    r ∈ fullPrefixCells S h ↔ (r + 1) * h ≤ S := by
  have hne : h ≠ 0 := Nat.ne_zero_of_lt hh
  constructor
  · intro hr
    rw [fullPrefixCells, if_neg hne, mem_filter] at hr
    exact hr.2
  · intro hr
    rw [fullPrefixCells, if_neg hne, mem_filter, mem_Ico]
    refine ⟨⟨Nat.zero_le r, ?_⟩, hr⟩
    have hsucc : r + 1 ≤ S / h := (Nat.le_div_iff_mul_le hh).mpr hr
    have hdiv : S / h ≤ (S + h - 1) / h :=
      Nat.div_le_div_right (by omega)
    exact Nat.lt_of_succ_le (hsucc.trans hdiv)

theorem fullPrefixCells_eq_Ico {S h : ℕ} (hh : 0 < h) :
    fullPrefixCells S h = Ico 0 (S / h) := by
  ext r
  rw [mem_fullPrefixCells_iff hh, mem_Ico]
  constructor
  · intro hr
    exact ⟨Nat.zero_le r, Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le hh).mpr hr)⟩
  · intro hr
    exact (Nat.le_div_iff_mul_le hh).mp (Nat.succ_le_of_lt hr.2)

theorem fullPrefixCells_card {S h : ℕ} (hh : 0 < h) :
    (fullPrefixCells S h).card = S / h := by
  rw [fullPrefixCells_eq_Ico hh, Nat.card_Ico, Nat.sub_zero]

theorem fullPrefixCells_presieveSpanEnd {S h : ℕ} (hh : 0 < h) :
    fullPrefixCells (presieveSpanEnd S h) h = fullPrefixCells S h := by
  rw [fullPrefixCells_eq_Ico hh, fullPrefixCells_eq_Ico hh,
    presieveSpanEnd_div hh]

theorem fullPrefixCells_presieveSpanEnd_card {S h : ℕ} (hh : 0 < h) :
    (fullPrefixCells (presieveSpanEnd S h) h).card = S / h := by
  rw [fullPrefixCells_presieveSpanEnd hh, fullPrefixCells_card hh]

/-- Number of full cells plus the window `[1, S]`. -/
theorem presieveIntervalIndexCard {S h : ℕ} (hh : 0 < h) :
    (fullPrefixCells (presieveSpanEnd S h) h).card + 1 = S / h + 1 := by
  rw [fullPrefixCells_presieveSpanEnd_card hh]

theorem presieve_cell_count_le_div {S h : ℕ} (hh : 0 < h) :
    ((fullPrefixCells (presieveSpanEnd S h) h).card : ℝ) ≤
      (S : ℝ) / (h : ℝ) := by
  rw [fullPrefixCells_presieveSpanEnd_card hh]
  exact Nat.cast_div_le

/-- Paper: `O_{δ}(L)` full cells when `S ≤ 5 L G` and `h ≥ δ G / 2`. -/
theorem presieve_cell_count_O_L {S h L : ℕ} {G δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hG : 0 < G) (hL : 0 ≤ (L : ℝ))
    (hS : (S : ℝ) ≤ 5 * (L : ℝ) * G)
    (hhG : δ * G / 2 ≤ (h : ℝ)) :
    ((fullPrefixCells (presieveSpanEnd S h) h).card : ℝ) ≤
      (10 / δ) * (L : ℝ) := by
  have hh0 : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hden : 0 < δ * G / 2 := div_pos (mul_pos hδ hG) (by norm_num)
  have hinv : (h : ℝ)⁻¹ ≤ (δ * G / 2)⁻¹ := inv_anti₀ hden hhG
  have hle := presieve_cell_count_le_div (S := S) hh
  have hSG : (S : ℝ) * (h : ℝ)⁻¹ ≤ (5 * (L : ℝ) * G) * (δ * G / 2)⁻¹ :=
    mul_le_mul hS hinv (inv_nonneg.mpr hh0.le)
      (mul_nonneg (mul_nonneg (by norm_num) hL) hG.le)
  have hsimp : (5 * (L : ℝ) * G) * (δ * G / 2)⁻¹ = (10 / δ) * (L : ℝ) := by
    have hG0 : G ≠ 0 := hG.ne'
    have hδ0 : δ ≠ 0 := hδ.ne'
    field_simp [hG0, hδ0]
    ring
  calc
    ((fullPrefixCells (presieveSpanEnd S h) h).card : ℝ)
        ≤ (S : ℝ) / (h : ℝ) := hle
    _ = (S : ℝ) * (h : ℝ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (5 * (L : ℝ) * G) * (δ * G / 2)⁻¹ := hSG
    _ = (10 / δ) * (L : ℝ) := hsimp

/-! ### Interval identifications -/

theorem Icc_one_eq_Ioc_zero (S : ℕ) : Icc 1 S = Ioc 0 S := by
  ext x
  simp only [mem_Icc, mem_Ioc]
  exact ⟨fun hx => ⟨Nat.succ_le_iff.mp hx.1, hx.2⟩,
    fun hx => ⟨Nat.succ_le_iff.mpr hx.1, hx.2⟩⟩

theorem Icc_one_eq_Ico_succ (S : ℕ) : Icc 1 S = Ico 1 (S + 1) := by
  ext x
  simp only [mem_Icc, mem_Ico, Nat.lt_succ_iff]

theorem Ico_one_add (S : ℕ) : Ico 1 (1 + S) = Icc 1 S := by
  rw [Nat.add_comm 1 S, Icc_one_eq_Ico_succ]

theorem card_Icc_one (S : ℕ) : (Icc 1 S).card = S := by
  rw [Nat.card_Icc, Nat.add_sub_cancel]

theorem cellIco_eq_Ico (r h : ℕ) :
    cellIco r h = Ico (r * h) (r * h + h) := by
  simp [cellIco, Nat.add_mul]

theorem cellIoc_eq_Ico (r h : ℕ) :
    cellIoc r h = Ico (r * h + 1) (r * h + 1 + h) := by
  ext x
  simp only [cellIoc, mem_Ioc, mem_Ico]
  have hr : (r + 1) * h = r * h + h := by
    rw [Nat.add_mul, Nat.one_mul]
  have hsucc : r * h + 1 + h = (r * h + h).succ := by
    rw [Nat.succ_eq_add_one, add_assoc, add_comm (1 : ℕ) h, add_assoc]
  constructor
  · intro hx
    refine ⟨Nat.succ_le_iff.mpr (And.left hx), ?_⟩
    have hx2 : x ≤ (r + 1) * h := And.right hx
    rw [hr] at hx2
    rw [hsucc]
    exact Nat.lt_succ_iff.mpr hx2
  · intro hx
    refine ⟨Nat.succ_le_iff.mp (And.left hx), ?_⟩
    have hx2 : x < r * h + 1 + h := And.right hx
    rw [hsucc] at hx2
    rw [hr]
    exact Nat.lt_succ_iff.mp hx2

theorem cellIoc_div {r h x : ℕ} (hh : 0 < h) (hx : x ∈ cellIoc r h) :
    (x - 1) / h = r := by
  simp only [cellIoc, mem_Ioc] at hx
  have hlo : r * h ≤ x - 1 := by omega
  have hhi : x - 1 < (r + 1) * h := by omega
  exact Nat.div_eq_of_lt_le hlo hhi

theorem cellIoc_unique {r s h x : ℕ} (hh : 0 < h)
    (hr : x ∈ cellIoc r h) (hs : x ∈ cellIoc s h) : r = s :=
  (cellIoc_div hh hr).symm.trans (cellIoc_div hh hs)

theorem cellIoc_pairwise_disjoint {h : ℕ} (hh : 0 < h) (s : Finset ℕ) :
    Set.PairwiseDisjoint ↑s (fun r => cellIoc r h) := by
  intro r _ s' _ hrs
  refine disjoint_left.mpr fun x hxr hxs => ?_
  exact hrs (cellIoc_unique hh hxr hxs)

private theorem presieveSpanEnd_pred_div {S h : ℕ} (hh : 0 < h)
    (hq : 1 ≤ S / h) :
    (presieveSpanEnd S h - 1) / h = S / h - 1 := by
  unfold presieveSpanEnd
  have hh1 : 1 ≤ h := Nat.succ_le_of_lt hh
  have hdecomp : h * (S / h) - 1 = (h - 1) + (S / h - 1) * h := by
    have hmul : h * (S / h) = h * (S / h - 1 + 1) :=
      congrArg (fun n => h * n) (Nat.sub_add_cancel hq).symm
    calc
      h * (S / h) - 1
          = h * (S / h - 1 + 1) - 1 := by rw [hmul]
        _ = h * (S / h - 1) + h * 1 - 1 := by rw [Nat.mul_add]
        _ = h * (S / h - 1) + h - 1 := by rw [Nat.mul_one]
        _ = h * (S / h - 1) + (h - 1) := Nat.add_sub_assoc hh1 _
        _ = (S / h - 1) * h + (h - 1) := by rw [Nat.mul_comm]
        _ = (h - 1) + (S / h - 1) * h := by rw [Nat.add_comm]
  rw [hdecomp, Nat.add_mul_div_right (h - 1) (S / h - 1) hh]
  have : (h - 1) / h = 0 := Nat.div_eq_of_lt (Nat.sub_lt hh Nat.zero_lt_one)
  rw [this, Nat.zero_add]

theorem mem_cellIoc_of_div {h x : ℕ} (hh : 0 < h) (hx : 1 ≤ x) :
    x ∈ cellIoc ((x - 1) / h) h := by
  simp only [cellIoc, mem_Ioc]
  set r := (x - 1) / h
  have hlo : r * h ≤ x - 1 := Nat.div_mul_le_self (x - 1) h
  have hlo' : r * h < x := by omega
  have hmod : x - 1 = r * h + (x - 1) % h := by
    rw [Nat.mul_comm]
    exact Eq.symm (Nat.div_add_mod (x - 1) h)
  have hmodlt : (x - 1) % h < h := Nat.mod_lt _ hh
  have hhi : x ≤ (r + 1) * h := by
    have : x - 1 < r * h + h := by omega
    have hr : r * h + h = (r + 1) * h := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  exact ⟨hlo', hhi⟩

theorem cellIoc_biUnion_eq_Ioc {S h : ℕ} (hh : 0 < h) :
    (fullPrefixCells S h).biUnion (fun r => cellIoc r h) =
      Ioc 0 (presieveSpanEnd S h) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hx'⟩ := mem_biUnion.mp hx
    have hrS : (r + 1) * h ≤ S := (mem_fullPrefixCells_iff hh).mp hr
    simp only [cellIoc, mem_Ioc] at hx' ⊢
    have hx0 : 0 < x := lt_of_le_of_lt (Nat.zero_le (r * h)) hx'.1
    have hsucc : r + 1 ≤ S / h := (Nat.le_div_iff_mul_le hh).mpr hrS
    have hmul : (r + 1) * h ≤ (S / h) * h := Nat.mul_le_mul_right h hsucc
    have hS' : (S / h) * h = presieveSpanEnd S h := by
      unfold presieveSpanEnd
      rw [Nat.mul_comm]
    exact ⟨hx0, hx'.2.trans (hmul.trans_eq hS')⟩
  · intro hx
    have hx' := mem_Ioc.mp hx
    have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx'.1
    set r := (x - 1) / h
    have hq : 1 ≤ S / h := by
      have hS'pos : 0 < presieveSpanEnd S h :=
        lt_of_lt_of_le hx'.1 hx'.2
      unfold presieveSpanEnd at hS'pos
      have hne : S / h ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hS'pos
        exact Nat.lt_irrefl _ hS'pos
      exact Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hne)
    have hrle : r ≤ S / h - 1 := by
      have hxle : x - 1 ≤ presieveSpanEnd S h - 1 :=
        Nat.sub_le_sub_right hx'.2 1
      have hdiv : (x - 1) / h ≤ (presieveSpanEnd S h - 1) / h :=
        Nat.div_le_div_right hxle
      have hpred := presieveSpanEnd_pred_div hh hq
      simpa [r, hpred] using hdiv
    have hrS : (r + 1) * h ≤ S := by
      have : r + 1 ≤ S / h := by omega
      exact (Nat.le_div_iff_mul_le hh).mp this
    have hrMem : r ∈ fullPrefixCells S h :=
      (mem_fullPrefixCells_iff hh).mpr hrS
    exact mem_biUnion.mpr ⟨r, hrMem, mem_cellIoc_of_div hh hx1⟩

theorem Ioc_union_Ioc {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Ioc a b ∪ Ioc b c = Ioc a c := by
  ext x
  simp only [mem_union, mem_Ioc]
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hx.1, hx.2.trans hbc⟩
    · exact ⟨lt_of_le_of_lt hab hx.1, hx.2⟩
  · intro hx
    rcases le_or_gt x b with hxb | hxb
    · exact Or.inl ⟨hx.1, hxb⟩
    · exact Or.inr ⟨hxb, hx.2⟩

/-- Paper interface: `[1, S]` is the full `h`-cells in `(0, S']` together
with the remainder `(S', S]`. The window count is **not** deduced from
the cells; both are concentrated separately. -/
theorem Icc_one_eq_cells_union_remainder {S h : ℕ} (hh : 0 < h) :
    Icc 1 S =
      (fullPrefixCells S h).biUnion (fun r => cellIoc r h) ∪
        Ioc (presieveSpanEnd S h) S := by
  rw [Icc_one_eq_Ioc_zero, cellIoc_biUnion_eq_Ioc hh]
  exact (Ioc_union_Ioc (Nat.zero_le _) (presieveSpanEnd_le S h)).symm

theorem presieveSpanEnd_mod {S h : ℕ} (hh : 0 < h) :
    S - presieveSpanEnd S h = S % h := by
  have hdecomp : S = h * (S / h) + S % h := (Nat.div_add_mod S h).symm
  unfold presieveSpanEnd
  omega

theorem remainder_card_lt {S h : ℕ} (hh : 0 < h) :
    (Ioc (presieveSpanEnd S h) S).card < h := by
  have hle : presieveSpanEnd S h ≤ S := presieveSpanEnd_le S h
  rw [Nat.card_Ioc, presieveSpanEnd_mod hh]
  exact Nat.mod_lt S hh

/-! ### Relative counts: cells ↔ intervals -/

theorem presieveCellsAndWindow_iff {U : Finset ℕ} {S h : ℕ} {v η : ℝ} :
    PresieveCellsAndWindow U S h v η ↔
      RelativeCellCountsOn U h v η
          (fullPrefixCells (presieveSpanEnd S h) h) ∧
        RelativeCountOnInterval U (Icc 1 S) v η :=
  Iff.rfl

theorem relativeCountOnInterval_bounds {U I : Finset ℕ} {v η : ℝ}
    (hrel : RelativeCountOnInterval U I v η) :
    (1 - η) * (I.card : ℝ) * v ≤ ((U ∩ I).card : ℝ) ∧
      ((U ∩ I).card : ℝ) ≤ (1 + η) * (I.card : ℝ) * v := by
  have hle := abs_le.mp hrel
  constructor
  · linarith
  · linarith

theorem relativeCountOnInterval_of_cell {U : Finset ℕ} {h : ℕ} {v η : ℝ}
    {R : Finset ℕ} {r : ℕ} (hcell : RelativeCellCountsOn U h v η R)
    (hr : r ∈ R) :
    RelativeCountOnInterval U (cellIco r h) v η := by
  have hfilter := filter_cell_eq_inter U r h
  have hcard := cellIco_card r h
  have hmain := hcell r hr
  unfold RelativeCountOnInterval
  have hinter : U ∩ cellIco r h = U.filter (cell r h) := by
    rw [hfilter, cellIco]
  have hlen : ((cellIco r h).card : ℝ) * v = v * h := by
    rw [hcard, mul_comm]
  have hrhs : η * ((cellIco r h).card : ℝ) * v = η * v * h := by
    rw [hcard, mul_assoc, mul_comm (h : ℝ) v, ← mul_assoc]
  simpa [hinter, hlen, hrhs, mul_comm] using hmain

theorem relativeCellCountsOn_of_intervals {U : Finset ℕ} {h : ℕ} {v η : ℝ}
    {R : Finset ℕ}
    (hI : ∀ r ∈ R, RelativeCountOnInterval U (cellIco r h) v η) :
    RelativeCellCountsOn U h v η R := by
  intro r hr
  have hrel := hI r hr
  have hfilter := filter_cell_eq_inter U r h
  have hcard := cellIco_card r h
  unfold RelativeCountOnInterval at hrel
  have hinter : U ∩ cellIco r h = U.filter (cell r h) := by
    rw [hfilter, cellIco]
  have hlen : ((cellIco r h).card : ℝ) * v = v * h := by
    rw [hcard, mul_comm]
  have hrhs : η * ((cellIco r h).card : ℝ) * v = η * v * h := by
    rw [hcard, mul_assoc, mul_comm (h : ℝ) v, ← mul_assoc]
  simpa [hinter, hlen, hrhs] using hrel

theorem relativeCountOnInterval_cellIoc {U : Finset ℕ} {r h : ℕ} {v η : ℝ}
    (hrel : RelativeCountOnInterval U (cellIoc r h) v η) :
    |(((U ∩ cellIoc r h).card : ℝ) - v * h)| ≤ η * v * h := by
  have hcard := cellIoc_card r h
  unfold RelativeCountOnInterval at hrel
  have hlen : ((cellIoc r h).card : ℝ) * v = v * h := by
    rw [hcard, mul_comm]
  have hrhs : η * ((cellIoc r h).card : ℝ) * v = η * v * h := by
    rw [hcard, mul_assoc, mul_comm (h : ℝ) v, ← mul_assoc]
  simpa [hlen, hrhs] using hrel

/-! ### Brun density remainder first, then × length; CRT on the count -/

/-- Reciprocal-product remainder as a relative **density** error against
`V(w)`. Not yet multiplied by length. -/
def BrunDensityErrorLe (ρ Vw ε : ℝ) : Prop :=
  |ρ - Vw| ≤ ε * Vw

/-- CRT progression rounding as an additive **count** error. -/
def CrtRoundingCountLe (U I : Finset ℕ) (ρ R : ℝ) : Prop :=
  |(((U ∩ I).card : ℝ) - (I.card : ℝ) * ρ)| ≤ R

/-- Density error becomes a count error only after multiplying by
length. Do not mix this with CRT rounding. -/
theorem count_error_of_density {I : Finset ℕ} {ρ Vw ε : ℝ}
    (hdens : BrunDensityErrorLe ρ Vw ε) :
    |((I.card : ℝ) * ρ - (I.card : ℝ) * Vw)| ≤ ε * (I.card : ℝ) * Vw := by
  unfold BrunDensityErrorLe at hdens
  have hmul :
      |((I.card : ℝ) * ρ - (I.card : ℝ) * Vw)| =
        (I.card : ℝ) * |ρ - Vw| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hmul]
  have hmul' :
      (I.card : ℝ) * |ρ - Vw| ≤ (I.card : ℝ) * (ε * Vw) :=
    mul_le_mul_of_nonneg_left hdens (Nat.cast_nonneg _)
  have hcomm : (I.card : ℝ) * (ε * Vw) = ε * (I.card : ℝ) * Vw := by
    ring
  exact hmul'.trans_eq hcomm

/-- Triangle: CRT count error plus length × density error. -/
theorem count_abs_le_round_add_density {U I : Finset ℕ} {ρ Vw R D : ℝ}
    (hround : CrtRoundingCountLe U I ρ R)
    (hdens : |((I.card : ℝ) * ρ - (I.card : ℝ) * Vw)| ≤ D) :
    |(((U ∩ I).card : ℝ) - (I.card : ℝ) * Vw)| ≤ R + D :=
  (abs_sub_le _ _ _).trans (add_le_add hround hdens)

/-- Closing a relative `η`-band: rounding is a fraction of `length V(w)`,
separately from the density relative error. -/
theorem relativeCountOnInterval_of_split {U I : Finset ℕ}
    {ρ Vw R η₁ η₂ η : ℝ}
    (hV : 0 ≤ Vw) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hη : η₁ + η₂ ≤ η)
    (hround : CrtRoundingCountLe U I ρ R)
    (hR : R ≤ η₁ * (I.card : ℝ) * Vw)
    (hdens : BrunDensityErrorLe ρ Vw η₂) :
    RelativeCountOnInterval U I Vw η := by
  have hD := count_error_of_density (I := I) hdens
  have hsum := count_abs_le_round_add_density hround hD
  have hnn : 0 ≤ (I.card : ℝ) * Vw :=
    mul_nonneg (Nat.cast_nonneg _) hV
  have hband : R + η₂ * (I.card : ℝ) * Vw ≤ η * (I.card : ℝ) * Vw := by
    have h1 : R + η₂ * (I.card : ℝ) * Vw ≤
        η₁ * (I.card : ℝ) * Vw + η₂ * (I.card : ℝ) * Vw :=
      add_le_add hR le_rfl
    have h2 :
        η₁ * (I.card : ℝ) * Vw + η₂ * (I.card : ℝ) * Vw =
          (η₁ + η₂) * ((I.card : ℝ) * Vw) := by
      ring
    have hηassoc :
        η * (I.card : ℝ) * Vw = η * ((I.card : ℝ) * Vw) := by
      ring
    have h3 : (η₁ + η₂) * ((I.card : ℝ) * Vw) ≤ η * ((I.card : ℝ) * Vw) :=
      mul_le_mul_of_nonneg_right hη hnn
    calc
      R + η₂ * (I.card : ℝ) * Vw
          ≤ η₁ * (I.card : ℝ) * Vw + η₂ * (I.card : ℝ) * Vw := h1
      _ = (η₁ + η₂) * ((I.card : ℝ) * Vw) := h2
      _ ≤ η * ((I.card : ℝ) * Vw) := h3
      _ = η * (I.card : ℝ) * Vw := hηassoc.symm
  unfold RelativeCountOnInterval
  exact hsum.trans hband

/-- Paper Brun truncation order `s ≍ log G / (8 log w)`. Named scale. -/
noncomputable def brunTruncationOrder (G : ℝ) : ℝ :=
  Real.log G / (8 * Real.log (presieveW G : ℝ))

/-- Named Brun/CRT smallness through `w` (not unfolded). Rounding stays
a count; the product remainder stays a density against `η V(w)`. -/
def BrunCrtSmall (G : ℝ) (ℓ : ℕ) : Prop :=
  let w := presieveW G
  let η := presieveEta G
  let Vw := eulerProdNat w
  ∃ ρ R η₁ η₂ : ℝ,
    0 ≤ η₁ ∧ 0 ≤ η₂ ∧ η₁ + η₂ ≤ η ∧
      R ≤ η₁ * (ℓ : ℝ) * Vw ∧
        BrunDensityErrorLe ρ Vw η₂

/-! ### Ico / Ioc occupancy: pay the two endpoints -/

private theorem abs_card_cast_sub_le_sdiff {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    |(s.card : ℝ) - (t.card : ℝ)| ≤
      ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := by
  have hs : (s.card : ℝ) =
      ((s \ t).card : ℝ) + ((s ∩ t).card : ℝ) := by
    exact_mod_cast (card_sdiff_add_card_inter s t).symm
  have ht : (t.card : ℝ) =
      ((t \ s).card : ℝ) + ((s ∩ t).card : ℝ) := by
    have hinter : s ∩ t = t ∩ s := inter_comm _ _
    rw [hinter]
    exact_mod_cast (card_sdiff_add_card_inter t s).symm
  have hdiff : (s.card : ℝ) - t.card =
      ((s \ t).card : ℝ) - (t \ s).card := by
    rw [hs, ht]
    ring
  rw [hdiff]
  have ha : 0 ≤ ((s \ t).card : ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ ((t \ s).card : ℝ) := Nat.cast_nonneg _
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem abs_inter_card_le_symmDiff {U A B : Finset ℕ} :
    |(((U ∩ A).card : ℝ) - ((U ∩ B).card : ℝ))| ≤ ((A ∆ B).card : ℝ) := by
  classical
  have hAB : (U ∩ A) \ (U ∩ B) ⊆ A \ B := by
    intro x hx
    obtain ⟨hxUA, hnot⟩ := mem_sdiff.mp hx
    obtain ⟨hxU, hxA⟩ := mem_inter.mp hxUA
    exact mem_sdiff.mpr ⟨hxA, fun hxB => hnot (mem_inter.mpr ⟨hxU, hxB⟩)⟩
  have hBA : (U ∩ B) \ (U ∩ A) ⊆ B \ A := by
    intro x hx
    obtain ⟨hxUB, hnot⟩ := mem_sdiff.mp hx
    obtain ⟨hxU, hxB⟩ := mem_inter.mp hxUB
    exact mem_sdiff.mpr ⟨hxB, fun hxA => hnot (mem_inter.mpr ⟨hxU, hxA⟩)⟩
  have hle := abs_card_cast_sub_le_sdiff (U ∩ A) (U ∩ B)
  have h1 : (((U ∩ A) \ (U ∩ B)).card : ℝ) ≤ ((A \ B).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hAB)
  have h2 : (((U ∩ B) \ (U ∩ A)).card : ℝ) ≤ ((B \ A).card : ℝ) :=
    Nat.cast_le.mpr (card_le_card hBA)
  have hsd : ((A ∆ B).card : ℝ) = ((A \ B).card : ℝ) + ((B \ A).card : ℝ) := by
    have heq : A ∆ B = A \ B ∪ B \ A := by
      ext x
      simp only [mem_symmDiff, mem_union, mem_sdiff]
    have hdisj : Disjoint (A \ B) (B \ A) := by
      refine disjoint_left.mpr fun x hx hx' => ?_
      exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hx').1
    rw [heq, card_union_of_disjoint hdisj]
    exact_mod_cast rfl
  linarith [hle, h1, h2, hsd]

theorem abs_occupancy_Ico_Ioc {U : Finset ℕ} {r h : ℕ} :
    |(((U ∩ cellIco r h).card : ℝ) - ((U ∩ cellIoc r h).card : ℝ))| ≤ 2 := by
  have hsd := cellIco_cellIoc_symmDiff_card_le_two r h
  have hmain := abs_inter_card_le_symmDiff (U := U) (A := cellIco r h)
    (B := cellIoc r h)
  have : ((cellIco r h ∆ cellIoc r h).card : ℝ) ≤ 2 := by exact_mod_cast hsd
  exact hmain.trans this

/-- Transfer paper `Ioc` counts to Lean `Ico` cells, paying 2. -/
theorem relativeCount_Ico_of_Ioc {U : Finset ℕ} {r h : ℕ} {v η η' : ℝ}
    (hv : 0 ≤ v) (hη : η ≤ η')
    (hI : RelativeCountOnInterval U (cellIoc r h) v η)
    (hpay : 2 ≤ (η' - η) * h * v) :
    RelativeCountOnInterval U (cellIco r h) v η' := by
  have hIoc := relativeCountOnInterval_cellIoc hI
  have h2 := abs_occupancy_Ico_Ioc (U := U) (r := r) (h := h)
  have hcard := cellIco_card r h
  have htri :
      |(((U ∩ cellIco r h).card : ℝ) - v * h)| ≤
        |(((U ∩ cellIco r h).card : ℝ) - ((U ∩ cellIoc r h).card : ℝ))| +
          |(((U ∩ cellIoc r h).card : ℝ) - v * h)| :=
    abs_sub_le _ _ _
  have hsum : |(((U ∩ cellIco r h).card : ℝ) - v * h)| ≤ 2 + η * v * h :=
    htri.trans (add_le_add h2 hIoc)
  have hband : 2 + η * v * h ≤ η' * v * h := by
    have : 2 + η * v * h ≤ (η' - η) * h * v + η * v * h :=
      add_le_add hpay le_rfl
    have hring : (η' - η) * h * v + η * v * h = η' * v * h := by ring
    exact this.trans_eq hring
  unfold RelativeCountOnInterval
  have hlen : ((cellIco r h).card : ℝ) * v = v * h := by
    rw [hcard, mul_comm]
  have hrhs : η' * ((cellIco r h).card : ℝ) * v = η' * v * h := by
    rw [hcard, mul_assoc, mul_comm (h : ℝ) v, ← mul_assoc]
  simpa [hlen, hrhs] using hsum.trans hband

/-! ### Rooted middle product `∏_{w<p≤S}(1-1/(p-1)) = V(S)/V(w)(1+O(1/w))` -/

private theorem inv_pred_sq_le_four_inv_sq {p : ℕ} (hp : 2 ≤ p) :
    (((p : ℝ) - 1)⁻¹) ^ 2 ≤ 4 * ((p : ℝ)⁻¹) ^ 2 := by
  have hpR : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (p : ℝ) / 2 := div_pos hp0 (by norm_num)
  have hinv : ((p : ℝ) - 1)⁻¹ ≤ ((p : ℝ) / 2)⁻¹ :=
    inv_anti₀ hden hhalf
  have htwo : ((p : ℝ) / 2)⁻¹ = 2 * (p : ℝ)⁻¹ := by
    field_simp [hp0.ne']
  have hle : ((p : ℝ) - 1)⁻¹ ≤ 2 * (p : ℝ)⁻¹ := hinv.trans_eq htwo
  have hnn : 0 ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hpow := pow_le_pow_left₀ hnn hle 2
  have hsq : (2 * (p : ℝ)⁻¹) ^ 2 = 4 * ((p : ℝ)⁻¹) ^ 2 := by ring
  exact hpow.trans_eq hsq

private theorem one_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ 1) →
      1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i := by
  refine s.induction_on ?_ ?_
  · intro _ _
    simp
  · intro a s ha ih hf0 hf1
    rw [prod_insert ha, sum_insert ha]
    have ih' : 1 - ∏ i ∈ s, (1 - f i) ≤ ∑ i ∈ s, f i :=
      ih (fun i hi => hf0 i (mem_insert_of_mem hi))
        (fun i hi => hf1 i (mem_insert_of_mem hi))
    have ha0 : 0 ≤ f a := hf0 a (mem_insert_self _ _)
    have hP1 : ∏ i ∈ s, (1 - f i) ≤ 1 :=
      prod_le_one (fun i hi => sub_nonneg.mpr (hf1 i (mem_insert_of_mem hi)))
        (fun i hi => sub_le_self _ (hf0 i (mem_insert_of_mem hi)))
    have hexp :
        1 - (1 - f a) * ∏ i ∈ s, (1 - f i) =
          (1 - ∏ i ∈ s, (1 - f i)) + f a * ∏ i ∈ s, (1 - f i) := by
      ring
    rw [hexp]
    have h2 : f a * ∏ i ∈ s, (1 - f i) ≤ f a :=
      mul_le_of_le_one_right ha0 hP1
    linarith

theorem sum_inv_pred_sq_le {w S : ℕ} (hw : 2 ≤ w) :
    ∑ p ∈ Nat.primesLE S \ Nat.primesLE w,
        (((p : ℝ) - 1)⁻¹) ^ 2 ≤ 4 / w := by
  have hsub := primesLE_sdiff_subset_Icc w S
  have hpt : ∀ p ∈ Nat.primesLE S \ Nat.primesLE w,
      (((p : ℝ) - 1)⁻¹) ^ 2 ≤ 4 * ((p : ℝ)⁻¹) ^ 2 := fun p hp =>
    inv_pred_sq_le_four_inv_sq (Nat.two_le_of_mem_primesLE (sdiff_subset hp))
  have hsum := sum_le_sum hpt
  have h4 :
      ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, 4 * ((p : ℝ)⁻¹) ^ 2 ≤
        ∑ n ∈ Icc (w + 1) S, 4 * ((n : ℝ)⁻¹) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
      mul_nonneg (by norm_num) (sq_nonneg _)
  have hrew :
      ∑ n ∈ Icc (w + 1) S, 4 * ((n : ℝ)⁻¹) ^ 2 =
        4 * ∑ n ∈ Icc (w + 1) S, ((n : ℝ)⁻¹) ^ 2 :=
    (mul_sum _ _ _).symm
  have hinv :=
    sum_inv_sq_Icc_succ_le (w := w) (y := S)
      (le_trans (by omega : (1 : ℕ) ≤ 2) hw)
  have hfour : 4 * ∑ n ∈ Icc (w + 1) S, ((n : ℝ)⁻¹) ^ 2 ≤ 4 / w := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4)
    have heq : (4 : ℝ) * (w : ℝ)⁻¹ = 4 / w := (div_eq_mul_inv _ _).symm
    exact hmul.trans_eq heq
  exact hsum.trans (h4.trans (hrew.trans_le hfour))

/-- Paper: `∏_{w<p≤S}(1-1/(p-1)) = V(S)/V(w)(1+O(1/w))`. -/
theorem rootedEulerProdNat_rel_div {w S : ℕ} (hw : 2 ≤ w) (hS : w ≤ S) :
    |rootedEulerProdNat w S - eulerProdNat S / eulerProdNat w| ≤
      (4 / w) * (eulerProdNat S / eulerProdNat w) := by
  have heq := rootedEulerProdNat_eq hS
  set P :=
    ∏ p ∈ Nat.primesLE S \ Nat.primesLE w, (1 - ((p : ℝ) - 1)⁻¹ ^ 2)
  have hf0 : ∀ p ∈ Nat.primesLE S \ Nat.primesLE w,
      0 ≤ ((p : ℝ) - 1)⁻¹ ^ 2 := fun _ _ => sq_nonneg _
  have hf1 : ∀ p ∈ Nat.primesLE S \ Nat.primesLE w,
      ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 := fun p hp => by
    have hp3 : 3 ≤ p := by
      have hp' := (mem_primesLE_sdiff).mp hp
      have : w + 1 ≤ p := Nat.succ_le_of_lt hp'.2.1
      exact le_trans (Nat.succ_le_succ hw) this
    have hpR : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    have hden : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have hinv : ((p : ℝ) - 1)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hden
    have hsq : ((p : ℝ) - 1)⁻¹ ^ 2 ≤ (2 : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) hinv 2
    have : ((2 : ℝ)⁻¹) ^ 2 = 1 / 4 := by norm_num
    linarith
  have hPle : 1 - P ≤
      ∑ p ∈ Nat.primesLE S \ Nat.primesLE w, ((p : ℝ) - 1)⁻¹ ^ 2 :=
    one_sub_prod_le_sum _ _ hf0 hf1
  have hPsum := sum_inv_pred_sq_le (w := w) (S := S) hw
  have hP1 : 1 - P ≤ 4 / w := hPle.trans hPsum
  have hV : 0 ≤ eulerProdNat S / eulerProdNat w :=
    div_nonneg (eulerProdNat_pos S).le (eulerProdNat_pos w).le
  have hdiff :
      eulerProdNat S / eulerProdNat w - rootedEulerProdNat w S =
        (eulerProdNat S / eulerProdNat w) * (1 - P) := by
    rw [heq]
    ring
  have hnn : 0 ≤ eulerProdNat S / eulerProdNat w - rootedEulerProdNat w S := by
    have hPnonneg : 0 ≤ P :=
      prod_nonneg fun p hp => sub_nonneg.mpr (hf1 p hp)
    have hPle1 : P ≤ 1 :=
      prod_le_one (fun p hp => sub_nonneg.mpr (hf1 p hp))
        (fun p hp => sub_le_self _ (hf0 p hp))
    have : 0 ≤ 1 - P := sub_nonneg.mpr hPle1
    rw [hdiff]
    exact mul_nonneg hV this
  have habs :
      |rootedEulerProdNat w S - eulerProdNat S / eulerProdNat w| =
        eulerProdNat S / eulerProdNat w - rootedEulerProdNat w S := by
    rw [abs_sub_comm, abs_of_nonneg hnn]
  rw [habs, hdiff]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hP1 hV

/-! ### Exception: exponential grid vs later `O(1/L)` count band -/

/-- Later Chebyshev count band. Distinct from `GridExceptionLe`. -/
def CountBandExceptionLe (C : ℝ) (L : ℕ) (ε : ℝ) : Prop :=
  ε ≤ C / (L : ℝ)

theorem countBandExceptionLe_self {C : ℝ} {L : ℕ} (hL : 0 < L) :
    CountBandExceptionLe C L (C / (L : ℝ)) :=
  le_rfl

/-- The two exceptions add. The exponential grid event is not replaced
by the `O(1/L)` band. -/
theorem exception_add_grid_and_count {Cgrid c Cband : ℝ} {L : ℕ}
    {G εgrid εband : ℝ}
    (hgrid : GridExceptionLe Cgrid c L G εgrid)
    (hband : CountBandExceptionLe Cband L εband) :
    εgrid + εband ≤
      Cgrid * (L : ℝ) * Real.exp (-c * Real.log G ^ ((3 : ℝ) / 2)) +
        Cband / (L : ℝ) :=
  add_le_add hgrid hband

theorem gridExceptionLe_mul_card {C c K : ℝ} {L n : ℕ} {G ε : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hL : 0 ≤ (L : ℝ))
    (hn : (n : ℝ) ≤ K * (L : ℝ))
    (hε : ε ≤ C * Real.exp (-c * Real.log G ^ ((3 : ℝ) / 2))) :
    GridExceptionLe (K * C) c L G ((n : ℝ) * ε) := by
  unfold GridExceptionLe
  set e := Real.exp (-c * Real.log G ^ ((3 : ℝ) / 2))
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have hCe : 0 ≤ C * e := mul_nonneg hC he0
  have hKL : 0 ≤ K * (L : ℝ) := mul_nonneg hK hL
  have h1 : (n : ℝ) * ε ≤ (K * (L : ℝ)) * (C * e) := by
    rcases le_or_gt ε 0 with hε0 | hε0
    · have hleft : (n : ℝ) * ε ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε0
      exact hleft.trans (mul_nonneg hKL hCe)
    · exact mul_le_mul hn hε hε0.le hKL
  have h2 : (K * (L : ℝ)) * (C * e) = (K * C) * (L : ℝ) * e := by ring
  exact h1.trans_eq h2

/-! ### Hoeffding exponent `(log G)^{3/2}` from `η`, `w`, `V` -/

theorem hoeffding_exponent_three_halves {η ℓ V σ K t cV : ℝ}
    (ht : 0 < t) (hℓ : 0 < ℓ) (hK : 0 < K) (hσ : 0 < σ) (hc : 0 < cV)
    (hηeq : η = (Real.sqrt (Real.sqrt t))⁻¹)
    (hσle : σ ≤ K * ℓ ^ 2 / t ^ 4) (hV : cV / t ≤ V) :
    η ^ 2 * ℓ ^ 2 * V ^ 2 / σ ≥ (cV ^ 2 / K) * t * Real.sqrt t :=
  middle_deviation_sq_ratio ht hℓ hK hσ hc hηeq hσle hV

theorem hoeffding_exponent_grid {η ℓ V σ K G cV : ℝ}
    (hG : 1 < G) (hℓ : 0 < ℓ) (hK : 0 < K) (hσ : 0 < σ) (hc : 0 < cV)
    (hηeq : η = presieveEta G)
    (hσle : σ ≤ K * ℓ ^ 2 / Real.log G ^ (4 : ℕ))
    (hV : cV / Real.log G ≤ V) :
    η ^ 2 * ℓ ^ 2 * V ^ 2 / σ ≥
      (cV ^ 2 / K) * Real.log G ^ ((3 : ℝ) / 2) := by
  have hlog : 0 < Real.log G := Real.log_pos hG
  have hη : η = (Real.sqrt (Real.sqrt (Real.log G)))⁻¹ := by
    rw [hηeq, presieveEta_eq]
    rfl
  have hmain :=
    hoeffding_exponent_three_halves hlog hℓ hK hσ hc hη hσle hV
  have hrhs :
      (cV ^ 2 / K) * Real.log G * Real.sqrt (Real.log G) =
        (cV ^ 2 / K) * Real.log G ^ ((3 : ℝ) / 2) := by
    have h32 := logThreeHalves_eq_rpow hG
    unfold logThreeHalves at h32
    rw [mul_assoc, h32]
  rwa [← hrhs]

theorem tail_le_grid_exp {c u σ G : ℝ} (hG : 1 < G) (hσ : 0 < σ)
    (hexp : c * Real.log G ^ ((3 : ℝ) / 2) ≤ u ^ 2 / σ) :
    Real.exp (-u ^ 2 / σ) ≤
      Real.exp (-c * Real.log G ^ ((3 : ℝ) / 2)) := by
  rw [neg_div, neg_mul]
  exact Real.exp_monotone (neg_le_neg hexp)

/-! ### Bounded differences: same `piFin` engine for cells and `[1,S]` -/

theorem piExpect_neg {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)]
    (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ) :
    piExpect μ (fun x => -F x) = -piExpect μ F := by
  simp [piExpect, mul_neg, sum_neg_distrib]

theorem residuePiAvoidCount_window {n : ℕ} (moduli : Fin n → ℕ) (S : ℕ)
    (σ : ∀ i, Fin (moduli i - 1)) :
    residuePiAvoidCount moduli 1 S σ =
      (residueAvoidCount moduli (Icc 1 S) (decodeResidue moduli σ) : ℝ) := by
  unfold residuePiAvoidCount
  rw [Ico_one_add]

theorem residuePiAvoidCount_cellIco {n : ℕ} (moduli : Fin n → ℕ)
    (r h : ℕ) (σ : ∀ i, Fin (moduli i - 1)) :
    residuePiAvoidCount moduli (r * h) h σ =
      (residueAvoidCount moduli (cellIco r h) (decodeResidue moduli σ) : ℝ) := by
  unfold residuePiAvoidCount
  rw [cellIco_eq_Ico]

theorem residuePiAvoidCount_cellIoc {n : ℕ} (moduli : Fin n → ℕ)
    (r h : ℕ) (σ : ∀ i, Fin (moduli i - 1)) :
    residuePiAvoidCount moduli (r * h + 1) h σ =
      (residueAvoidCount moduli (cellIoc r h) (decodeResidue moduli σ) : ℝ) := by
  unfold residuePiAvoidCount
  rw [cellIoc_eq_Ico]

/-- Window `[1,S] = Ico 1 (1+S)` uses the existing cell Lipschitz
`residuePi_uniform_one_sided`, not a second McDiarmid leaf. -/
theorem residuePi_window_one_sided {n : ℕ} (moduli : Fin n → ℕ)
    (S : ℕ) {u : ℝ} (hp : ∀ i, 2 ≤ moduli i) (hu : 0 < u) :
    ∑ σ ∈ univ.filter (fun σ : (∀ i, Fin (moduli i - 1)) =>
        u ≤ residuePiAvoidCount moduli 1 S σ -
          piExpect (fun i => uniformFin)
            (residuePiAvoidCount moduli 1 S)),
      piMass (fun i => uniformFin) σ
    ≤ if ∑ i : Fin n, residueWidth (S : ℝ) (moduli i) ^ 2 = 0 then 0
      else Real.exp (-u ^ 2 /
        ∑ i : Fin n, residueWidth (S : ℝ) (moduli i) ^ 2) :=
  residuePi_uniform_one_sided moduli 1 S hp hu

/-- Full Lean cell `[rh, (r+1)h)` on the same engine. -/
theorem residuePi_cellIco_one_sided {n : ℕ} (moduli : Fin n → ℕ)
    (r h : ℕ) {u : ℝ} (hp : ∀ i, 2 ≤ moduli i) (hu : 0 < u) :
    ∑ σ ∈ univ.filter (fun σ : (∀ i, Fin (moduli i - 1)) =>
        u ≤ residuePiAvoidCount moduli (r * h) h σ -
          piExpect (fun i => uniformFin)
            (residuePiAvoidCount moduli (r * h) h)),
      piMass (fun i => uniformFin) σ
    ≤ if ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2 = 0 then 0
      else Real.exp (-u ^ 2 /
        ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2) :=
  residuePi_uniform_one_sided moduli (r * h) h hp hu

/-- Paper cell `(rh, (r+1)h]` on the same engine. -/
theorem residuePi_cellIoc_one_sided {n : ℕ} (moduli : Fin n → ℕ)
    (r h : ℕ) {u : ℝ} (hp : ∀ i, 2 ≤ moduli i) (hu : 0 < u) :
    ∑ σ ∈ univ.filter (fun σ : (∀ i, Fin (moduli i - 1)) =>
        u ≤ residuePiAvoidCount moduli (r * h + 1) h σ -
          piExpect (fun i => uniformFin)
            (residuePiAvoidCount moduli (r * h + 1) h)),
      piMass (fun i => uniformFin) σ
    ≤ if ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2 = 0 then 0
      else Real.exp (-u ^ 2 /
        ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2) :=
  residuePi_uniform_one_sided moduli (r * h + 1) h hp hu

set_option maxHeartbeats 2000000 in
theorem piFin_bounded_diff_two_sided {n : ℕ} {α : Fin n → Type}
    [∀ i, Fintype (α i)] (μ : ∀ i, α i → ℝ) (F : (∀ i, α i) → ℝ)
    (c : Fin n → ℝ) {u : ℝ}
    (hμ0 : ∀ i a, 0 ≤ μ i a) (hμ1 : ∀ i, ∑ a : α i, μ i a = 1)
    (hc : ∀ i, 0 ≤ c i)
    (hLip : ∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
      |F (Function.update x i a) - F (Function.update x i b)| ≤ c i)
    (hu : 0 < u) :
    ∑ x ∈ univ.filter
        (fun x : (∀ i, α i) => u ≤ |F x - piExpect μ F|),
      piMass μ x
    ≤ if ∑ i : Fin n, c i ^ 2 = 0 then 0
      else 2 * Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  classical
  have hmass0 : ∀ x, 0 ≤ piMass μ x := fun x =>
    prod_nonneg fun i _ => hμ0 i (x i)
  have hpos :=
    piFin_bounded_diff_one_sided μ F c hμ0 hμ1 hc hLip hu
  have hLipNeg :
      ∀ (x : ∀ i, α i) (i : Fin n) (a b : α i),
        |(-F (Function.update x i a)) - (-F (Function.update x i b))| ≤
          c i := fun x i a b => by
    have heq :
        |(-F (Function.update x i a)) - (-F (Function.update x i b))| =
          |F (Function.update x i a) - F (Function.update x i b)| := by
      rw [neg_sub_neg, abs_sub_comm]
    rw [heq]
    exact hLip x i a b
  have hneg :=
    piFin_bounded_diff_one_sided μ (fun x => -F x) c hμ0 hμ1 hc hLipNeg hu
  have hE : piExpect μ (fun x => -F x) = -piExpect μ F := piExpect_neg μ F
  set E := piExpect μ F
  set spos := univ.filter (fun x : (∀ i, α i) => u ≤ F x - E)
  set sneg := univ.filter (fun x : (∀ i, α i) => u ≤ -F x - -E)
  set sall := univ.filter (fun x : (∀ i, α i) => u ≤ |F x - E|)
  have hsub : sall ⊆ spos ∪ sneg := by
    intro x hx
    have hu' : u ≤ |F x - E| := (mem_filter.mp hx).2
    rcases le_or_gt 0 (F x - E) with hsign | hsign
    · have : u ≤ F x - E := by rwa [abs_of_nonneg hsign] at hu'
      exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ x, this⟩))
    · have : u ≤ -(F x - E) := by rwa [abs_of_neg hsign] at hu'
      have : u ≤ -F x - -E := by
        convert this using 1
        ring
      exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ x, this⟩))
  have hsum_all :
      ∑ x ∈ sall, piMass μ x ≤ ∑ x ∈ spos ∪ sneg, piMass μ x :=
    sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hmass0 x
  have hunion :
      ∑ x ∈ spos ∪ sneg, piMass μ x ≤
        ∑ x ∈ spos, piMass μ x + ∑ x ∈ sneg, piMass μ x := by
    have heq :
        ∑ x ∈ spos ∪ sneg, piMass μ x + ∑ x ∈ spos ∩ sneg, piMass μ x =
          ∑ x ∈ spos, piMass μ x + ∑ x ∈ sneg, piMass μ x :=
      sum_union_inter
    have hinter : 0 ≤ ∑ x ∈ spos ∩ sneg, piMass μ x :=
      sum_nonneg fun x _ => hmass0 x
    exact (le_add_of_nonneg_right hinter).trans_eq heq
  have hpos' :
      ∑ x ∈ spos, piMass μ x ≤
        if ∑ i : Fin n, c i ^ 2 = 0 then (0 : ℝ)
        else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
    simpa [spos, E] using hpos
  have hneg' :
      ∑ x ∈ sneg, piMass μ x ≤
        if ∑ i : Fin n, c i ^ 2 = 0 then (0 : ℝ)
        else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
    simpa [sneg, E, hE] using hneg
  have hbound :=
    (hsum_all.trans hunion).trans (add_le_add hpos' hneg')
  have hite :
      (if ∑ i : Fin n, c i ^ 2 = 0 then (0 : ℝ)
        else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2)) +
        (if ∑ i : Fin n, c i ^ 2 = 0 then 0
          else Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2)) =
        if ∑ i : Fin n, c i ^ 2 = 0 then 0
        else 2 * Real.exp (-u ^ 2 / ∑ i : Fin n, c i ^ 2) := by
    split_ifs <;> ring
  exact hbound.trans_eq hite

set_option maxHeartbeats 2000000 in
theorem residuePi_uniform_two_sided {n : ℕ} (moduli : Fin n → ℕ)
    (a h : ℕ) {u : ℝ} (hp : ∀ i, 2 ≤ moduli i) (hu : 0 < u) :
    ∑ σ ∈ univ.filter (fun σ : (∀ i, Fin (moduli i - 1)) =>
        u ≤ |residuePiAvoidCount moduli a h σ -
          piExpect (fun i => uniformFin)
            (residuePiAvoidCount moduli a h)|),
      piMass (fun i => uniformFin) σ
    ≤ if ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2 = 0 then 0
      else 2 * Real.exp (-u ^ 2 /
        ∑ i : Fin n, residueWidth (h : ℝ) (moduli i) ^ 2) := by
  have hμ0 : ∀ i (b : Fin (moduli i - 1)), 0 ≤ uniformFin b :=
    fun _ b => uniformFin_nonneg b
  have hμ1 : ∀ i, ∑ a : Fin (moduli i - 1), uniformFin a = 1 :=
    fun i => uniformFin_sum (moduli_pred_pos (hp i))
  have hc : ∀ i, 0 ≤ residueWidth (h : ℝ) (moduli i) :=
    fun i => residueWidth_nonneg (Nat.cast_nonneg h)
      (Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) (hp i)))
  have hLip :
      ∀ (σ : ∀ i, Fin (moduli i - 1)) (i : Fin n)
        (b₁ b₂ : Fin (moduli i - 1)),
        |residuePiAvoidCount moduli a h (Function.update σ i b₁) -
            residuePiAvoidCount moduli a h (Function.update σ i b₂)| ≤
          residueWidth (h : ℝ) (moduli i) :=
    fun σ i b₁ b₂ =>
      residuePiAvoidCount_lipschitz moduli a h σ i b₁ b₂
        (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) (hp i))
  exact piFin_bounded_diff_two_sided (fun i => uniformFin)
      (residuePiAvoidCount moduli a h)
      (fun i => residueWidth (h : ℝ) (moduli i)) hμ0 hμ1 hc hLip hu

/-- Two-sided window tail: same `piFin` leaf as the cells. -/
theorem residuePi_window_two_sided {n : ℕ} (moduli : Fin n → ℕ)
    (S : ℕ) {u : ℝ} (hp : ∀ i, 2 ≤ moduli i) (hu : 0 < u) :
    ∑ σ ∈ univ.filter (fun σ : (∀ i, Fin (moduli i - 1)) =>
        u ≤ |residuePiAvoidCount moduli 1 S σ -
          piExpect (fun i => uniformFin)
            (residuePiAvoidCount moduli 1 S)|),
      piMass (fun i => uniformFin) σ
    ≤ if ∑ i : Fin n, residueWidth (S : ℝ) (moduli i) ^ 2 = 0 then 0
      else 2 * Real.exp (-u ^ 2 /
        ∑ i : Fin n, residueWidth (S : ℝ) (moduli i) ^ 2) :=
  residuePi_uniform_two_sided moduli 1 S hp hu

/-! ### Moment hull: keep `12`, `d0 > 24 e`, `a > d0` -/

/-- Paper: `d0 > 24 e`. -/
def PresieveD0Large (d0 : ℝ) : Prop :=
  24 * Real.exp 1 < d0

/-- Paper: `a > d0`. -/
def PresieveALarge (d0 : ℝ) (a : ℕ) : Prop :=
  d0 < a

def PresieveMomentConstants (d0 : ℝ) (a : ℕ) : Prop :=
  PresieveD0Large d0 ∧ PresieveALarge d0 a

/-- Numeric comparison used by a later moment-hull proof. This is
not `ModelMomentHull` for a free scalar. -/
theorem factorialMoment_le_twelve_of_six_exception
    {A : Finset ℕ} {μ : Finset ℕ → ℝ} {L a j : ℕ} {ε C1 logS : ℝ}
    (hL : 0 ≤ (L : ℝ)) (hε : 0 ≤ ε) (hC1 : 0 ≤ C1) (hlog : 0 ≤ logS)
    (hj : 1 ≤ j) (hsmall : ε * (C1 * logS / 6) ^ j ≤ 1)
    (hval : factorialMoment A μ j ≤
      ((6 * (L : ℝ)) ^ j + ε * (C1 * (L : ℝ) * logS) ^ j) /
        (Nat.factorial j : ℝ)) :
    ModelMomentHull A μ L a j := by
  intro _
  have halg :=
    exception_add_le_twelve_pow (L := (L : ℝ)) hL hε hC1 hlog hj hsmall
  exact hval.trans (div_le_div_of_nonneg_right halg (Nat.cast_nonneg _))

/-! ### `PresieveToS`: named paper target, sorry-free -/

/-- Paper `eq:relativegrid`--`eq:gridexception` with `v = V(S)` and
`η = (log G)^{-1/4}`. Brun/CRT numerical smallness for large `G` is not
unfolded; the bound shape is exact. -/
def PresieveToSPaper (S h L : ℕ) (G C c ε : ℝ) : Prop :=
  PresieveToS S h (presieveEta G) C c L G ε

theorem presieveToSPaper_iff {S h L : ℕ} {G C c ε : ℝ} :
    PresieveToSPaper S h L G C c ε ↔
      PresieveToS S h (presieveEta G) C c L G ε :=
  Iff.rfl

theorem presieveToS_pos_h {S h : ℕ} {η C c : ℝ} {L : ℕ} {G ε : ℝ}
    (hP : PresieveToS S h η C c L G ε) : 0 < h :=
  hP.1

theorem presieveToS_gridException {S h : ℕ} {η C c : ℝ} {L : ℕ} {G ε : ℝ}
    (hP : PresieveToS S h η C c L G ε) :
    GridExceptionLe C c L G ε :=
  hP.2.1

theorem presieveToS_bad_le {S h : ℕ} {η C c : ℝ} {L : ℕ} {G ε : ℝ}
    (hP : PresieveToS S h η C c L G ε) :
    badPresieveProb S h η ≤ ε :=
  hP.2.2

end PrimeGapNormality.Prime
