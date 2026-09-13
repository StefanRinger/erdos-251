import PrimeGapNormality.Prime.CoreCyclicNormalForm

/-!
The concrete rooted normal form. Dropping the first gap variable kills
monomials divisible by `u₀` and shifts all surviving variables down. Together
with the inverse cyclic label this is a left inverse `drop` to `shift`.
Finite polynomial support makes repeated dropping eventually constant.
-/

namespace PrimeGapNormality.Prime.CoreCyclic

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- Delete the first `n` gap variables, then lower the surviving indices. -/
def stripPoly (n : ℕ) : LocalPoly →ₐ[ℚ] LocalPoly :=
  aeval fun i ↦ if i < n then 0 else X (i - n)

@[simp] theorem stripPoly_X (n i : ℕ) :
    stripPoly n (X i) = if i < n then 0 else X (i - n) := by
  simp [stripPoly]

@[simp] theorem stripPoly_C (n : ℕ) (c : ℚ) : stripPoly n (C c) = C c := by
  simp [stripPoly]

@[simp] theorem stripPoly_zero (p : LocalPoly) : stripPoly 0 p = p := by
  have h : stripPoly 0 = AlgHom.id ℚ LocalPoly := by
    ext i
    simp
  exact AlgHom.congr_fun h p

theorem stripPoly_succ (n : ℕ) (p : LocalPoly) :
    stripPoly 1 (stripPoly n p) = stripPoly (n + 1) p := by
  have h : (stripPoly 1).comp (stripPoly n) = stripPoly (n + 1) := by
    ext i
    simp only [AlgHom.comp_apply, stripPoly_X]
    by_cases hi : i < n
    · simp [hi, show i < n + 1 by omega]
    · by_cases he : i = n
      · subst i
        simp
      · have hn : ¬i < n + 1 := by omega
        have hd : ¬i - n < 1 := by omega
        simp [hi, hn, hd, stripPoly_X, Nat.sub_sub]
  exact AlgHom.congr_fun h p

theorem stripPoly_shift (p : LocalPoly) : stripPoly 1 (rename Nat.succ p) = p := by
  have h : (stripPoly 1).comp (rename Nat.succ) = AlgHom.id ℚ LocalPoly := by
    ext i
    simp
  exact AlgHom.congr_fun h p

/-- This is Mathlib's coefficient-selecting `killCompl`, not a substitution
that identifies distinct surviving monomials. -/
theorem stripPoly_one_eq_killCompl :
    stripPoly 1 = killCompl Nat.succ_injective := by
  ext i
  cases i with
  | zero => simp [killCompl]
  | succ i =>
    rw [← rename_X Nat.succ i, stripPoly_shift, killCompl_rename_app]

/-- A finite variable bound gives an actual constant after enough drops. -/
theorem stripPoly_eq_constant_of_vars (p : LocalPoly) (n : ℕ)
    (hvars : ∀ i ∈ p.vars, i < n) :
    stripPoly n p = C (constantCoeff p) := by
  apply aeval_eq_constantCoeff_of_vars
  intro i hi
  simp [hvars i hi]

def predecessor {k : ℕ} (hk : 0 < k) : Fin k → Fin k :=
  (cyclicSuccEquiv hk).symm

@[simp] theorem successor_predecessor {k : ℕ} (hk : 0 < k) (r : Fin k) :
    cyclicSucc hk (predecessor hk r) = r :=
  (cyclicSuccEquiv hk).apply_symm_apply r

@[simp] theorem predecessor_successor {k : ℕ} (hk : 0 < k) (r : Fin k) :
    predecessor hk (cyclicSucc hk r) = r :=
  (cyclicSuccEquiv hk).symm_apply_apply r

/-- Reverse the component shift and drop the first gap. -/
def drop {k : ℕ} (hk : 0 < k) : PeriodicLocal k →ₗ[ℚ] PeriodicLocal k :=
  LinearMap.pi fun r ↦ (stripPoly 1).toLinearMap.comp
    (LinearMap.proj (predecessor hk r) : PeriodicLocal k →ₗ[ℚ] LocalPoly)

@[simp] theorem drop_apply {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) (r : Fin k) :
    drop hk F r = stripPoly 1 (F (predecessor hk r)) := rfl

@[simp] theorem drop_shift {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    drop hk (shift hk F) = F := by
  ext r
  simp [stripPoly_shift]

def dropPower {k : ℕ} (hk : 0 < k) : ℕ → PeriodicLocal k →ₗ[ℚ] PeriodicLocal k
  | 0 => LinearMap.id
  | n + 1 => (drop hk).comp (dropPower hk n)

@[simp] theorem dropPower_zero {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    dropPower hk 0 F = F := rfl

@[simp] theorem dropPower_succ {k : ℕ} (hk : 0 < k) (n : ℕ)
    (F : PeriodicLocal k) :
    dropPower hk (n + 1) F = drop hk (dropPower hk n F) := rfl

theorem dropPower_apply {k : ℕ} (hk : 0 < k) (n : ℕ)
    (F : PeriodicLocal k) (r : Fin k) :
    dropPower hk n F r = stripPoly n (F ((predecessor hk)^[n] r)) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [dropPower_succ, drop_apply, ih, stripPoly_succ,
      Function.iterate_succ_apply]

theorem dropPower_drop {k : ℕ} (hk : 0 < k) (n : ℕ) (F : PeriodicLocal k) :
    dropPower hk n (drop hk F) = dropPower hk (n + 1) F := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (drop hk) ih

/-- The actual finite-support termination statement for every local tuple. -/
theorem exists_dropPower_constant {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    ∃ n : ℕ, ∃ c : Fin k → ℚ, dropPower hk n F = constantTuple c := by
  classical
  let w : ℕ := Finset.univ.sup fun r : Fin k ↦ (F r).vars.sup id
  refine ⟨w + 1, fun r ↦ constantCoeff (F ((predecessor hk)^[w + 1] r)), ?_⟩
  funext r
  rw [dropPower_apply]
  apply stripPoly_eq_constant_of_vars
  intro i hi
  have hiw : i ≤ (F ((predecessor hk)^[w + 1] r)).vars.sup id :=
    Finset.le_sup (f := id) hi
  have hrw : (F ((predecessor hk)^[w + 1] r)).vars.sup id ≤ w :=
    Finset.le_sup (f := fun r : Fin k ↦ (F r).vars.sup id) (Finset.mem_univ _)
  exact Nat.lt_succ_of_le (hiw.trans hrw)

/-- Concrete rooted remainder: discard every monomial not involving `u₀`. -/
def rootPart {k : ℕ} (hk : 0 < k) : PeriodicLocal k →ₗ[ℚ] PeriodicLocal k :=
  LinearMap.id - (shift hk).comp (drop hk)

@[simp] theorem rootPart_apply {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    rootPart hk F = F - shift hk (drop hk F) := rfl

@[simp] theorem drop_rootPart {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    drop hk (rootPart hk F) = 0 := by
  simp

theorem drop_constantTuple {k : ℕ} (hk : 0 < k) (c : Fin k → ℚ) :
    drop hk (constantTuple c) = constantTuple (fun r ↦ c (predecessor hk r)) := by
  ext r
  simp [constantTuple]

/-- A constant tuple cannot be a nonzero rooted remainder. -/
theorem constantTuple_eq_zero_of_drop_eq_zero {k : ℕ} (hk : 0 < k)
    (c : Fin k → ℚ) (hc : drop hk (constantTuple c) = 0) :
    constantTuple c = 0 := by
  funext r
  have h := congrFun hc (cyclicSucc hk r)
  simpa [constantTuple] using h

theorem monomial_mem_shift_range_iff (m : ℕ →₀ ℕ) :
    m ∈ Set.range (Finsupp.mapDomain Nat.succ) ↔ m 0 = 0 := by
  rw [Finsupp.mem_range_mapDomain_iff Nat.succ Nat.succ_injective m]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h i hi
    cases i with
    | zero => exact h
    | succ i => exact False.elim (hi ⟨i, rfl⟩)

/-- The concrete zero-`u₀` coefficient criterion: every surviving monomial
must contain `u₀`. This includes exclusion of the constant monomial. -/
theorem drop_eq_zero_iff_rooted {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    drop hk F = 0 ↔ ∀ r : Fin k, ∀ m : ℕ →₀ ℕ,
      m 0 = 0 → (F r).coeff m = 0 := by
  constructor
  · intro h r m hm
    obtain ⟨d, hd⟩ := (monomial_mem_shift_range_iff m).2 hm
    have hc := congrArg (MvPolynomial.coeff d) (congrFun h (cyclicSucc hk r))
    simpa [stripPoly_one_eq_killCompl, coeff_killCompl, hd] using hc
  · intro h
    ext r d
    simp only [drop_apply, stripPoly_one_eq_killCompl, coeff_killCompl,
      Pi.zero_apply, coeff_zero]
    apply h
    exact (monomial_mem_shift_range_iff _).1 ⟨d, rfl⟩

theorem drop_telescope (B : ℕ) {k : ℕ} (hk : 0 < k) (H : PeriodicLocal k) :
    drop hk (cyclicTelescope B hk H) = (B : ℚ) • drop hk H - H := by
  simp [telescope_eq]

theorem one_step_decomposition (B : ℕ) {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k) :
    F = rootPart hk F + (B : ℚ) • drop hk F - cyclicTelescope B hk (drop hk F) := by
  rw [rootPart_apply, telescope_eq]
  module

/-- Finite elimination terminates with a rooted remainder and an actual
polynomial primitive. The only base restriction is the paper's `B ≥ 2`. -/
theorem exists_rooted_decomposition {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    ∃ R H : PeriodicLocal k, drop hk R = 0 ∧ F = R + cyclicTelescope B hk H := by
  obtain ⟨n, c, hc⟩ := exists_dropPower_constant hk F
  suffices ∀ n : ℕ, ∀ F : PeriodicLocal k, ∀ c : Fin k → ℚ,
      dropPower hk n F = constantTuple c →
      ∃ R H : PeriodicLocal k, drop hk R = 0 ∧ F = R + cyclicTelescope B hk H by
    exact this n F c hc
  intro n
  induction n with
  | zero =>
    intro F c hc
    refine ⟨0, constantPrimitive B hk c, by simp, ?_⟩
    simpa [telescope_constantPrimitive hB hk] using hc
  | succ n ih =>
    intro F c hc
    have htail : dropPower hk n (drop hk F) = constantTuple c := by
      rw [dropPower_drop]
      exact hc
    obtain ⟨R, H, hR, hF⟩ := ih (drop hk F) c htail
    refine ⟨rootPart hk F + (B : ℚ) • R, (B : ℚ) • H - drop hk F, ?_, ?_⟩
    · simp [hR]
    · calc
        F = rootPart hk F + (B : ℚ) • drop hk F -
            cyclicTelescope B hk (drop hk F) := one_step_decomposition B hk F
        _ = rootPart hk F + (B : ℚ) • R +
            cyclicTelescope B hk ((B : ℚ) • H - drop hk F) := by
          rw [map_sub, map_smul]
          rw [hF]
          module

theorem smul_constantTuple {k : ℕ} (a : ℚ) (c : Fin k → ℚ) :
    a • constantTuple c = constantTuple (fun r ↦ a * c r) := by
  ext r
  simp [constantTuple, smul_eq_C_mul]

theorem telescope_constantTuple (B : ℕ) {k : ℕ} (hk : 0 < k) (c : Fin k → ℚ) :
    cyclicTelescope B hk (constantTuple c) =
      constantTuple (fun r ↦ (B : ℚ) * c r - c (cyclicSucc hk r)) := by
  ext r
  simp [cyclicTelescope_apply, constantTuple]

theorem eq_smul_dropPower_of_eq_smul_drop (B : ℕ) {k : ℕ} (hk : 0 < k)
    (H : PeriodicLocal k) (hH : H = (B : ℚ) • drop hk H) (n : ℕ) :
    H = (B : ℚ) ^ n • dropPower hk n H := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := congrArg (dropPower hk n) hH
    rw [map_smul, dropPower_drop] at hn
    calc
      H = (B : ℚ) ^ n • dropPower hk n H := ih
      _ = (B : ℚ) ^ (n + 1) • dropPower hk (n + 1) H := by
        rw [hn, smul_smul, pow_succ]

/-- The recurrence produced by a normal telescope forces its primitive to
be a constant tuple, because repeated dropping reaches actual constants. -/
theorem exists_constant_of_drop_telescope_eq_zero (B : ℕ) {k : ℕ} (hk : 0 < k)
    (H : PeriodicLocal k) (hH : drop hk (cyclicTelescope B hk H) = 0) :
    ∃ c : Fin k → ℚ, H = constantTuple c := by
  rw [drop_telescope] at hH
  have heq : H = (B : ℚ) • drop hk H := (sub_eq_zero.mp hH).symm
  obtain ⟨n, c, hc⟩ := exists_dropPower_constant hk H
  refine ⟨fun r ↦ (B : ℚ) ^ n * c r, ?_⟩
  rw [← smul_constantTuple, ← hc]
  exact eq_smul_dropPower_of_eq_smul_drop B hk H heq n

/-- A rooted tuple in the telescope range is zero. -/
theorem telescope_eq_zero_of_drop_eq_zero (B : ℕ) {k : ℕ} (hk : 0 < k)
    (H : PeriodicLocal k) (hH : drop hk (cyclicTelescope B hk H) = 0) :
    cyclicTelescope B hk H = 0 := by
  obtain ⟨c, hc⟩ := exists_constant_of_drop_telescope_eq_zero B hk H hH
  rw [hc, telescope_constantTuple] at hH ⊢
  exact constantTuple_eq_zero_of_drop_eq_zero hk _ hH

/-- Uniqueness concerns the explicit rooted subspace, not a chosen complement. -/
theorem rooted_remainder_unique (B : ℕ) {k : ℕ} (hk : 0 < k)
    (F R₁ R₂ H₁ H₂ : PeriodicLocal k) (hR₁ : drop hk R₁ = 0)
    (hR₂ : drop hk R₂ = 0)
    (h₁ : F = R₁ + cyclicTelescope B hk H₁)
    (h₂ : F = R₂ + cyclicTelescope B hk H₂) : R₁ = R₂ := by
  have hdiff : cyclicTelescope B hk (H₂ - H₁) = R₁ - R₂ := by
    rw [map_sub]
    have heq := h₁.symm.trans h₂
    exact (sub_eq_sub_iff_add_eq_add).2 (by simpa [add_comm] using heq.symm)
  have hdrop : drop hk (cyclicTelescope B hk (H₂ - H₁)) = 0 := by
    rw [hdiff, map_sub, hR₁, hR₂, sub_self]
  have hz := telescope_eq_zero_of_drop_eq_zero B hk (H₂ - H₁) hdrop
  rw [hdiff] at hz
  exact sub_eq_zero.mp hz

/-- The canonical rooted remainder, selected from a proved unique
decomposition in actual finite-support polynomial tuples. -/
def normalForm {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) :
    PeriodicLocal k :=
  Classical.choose (exists_rooted_decomposition hB hk F)

theorem normalForm_spec {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    ∃ H : PeriodicLocal k, drop hk (normalForm hB hk F) = 0 ∧
      F = normalForm hB hk F + cyclicTelescope B hk H :=
  Classical.choose_spec (exists_rooted_decomposition hB hk F)

theorem drop_normalForm {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) :
    drop hk (normalForm hB hk F) = 0 := (normalForm_spec hB hk F).choose_spec.1

theorem normalForm_eq_of_decomposition {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F R H : PeriodicLocal k) (hR : drop hk R = 0)
    (hF : F = R + cyclicTelescope B hk H) : normalForm hB hk F = R := by
  obtain ⟨H', hR', hF'⟩ := normalForm_spec hB hk F
  exact rooted_remainder_unique B hk F _ R H' H hR' hR hF' hF

@[simp] theorem normalForm_of_rooted {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (hF : drop hk F = 0) : normalForm hB hk F = F :=
  normalForm_eq_of_decomposition hB hk F F 0 hF (by simp)

@[simp] theorem normalForm_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    normalForm hB hk 0 = 0 := normalForm_of_rooted hB hk 0 (by simp)

@[simp] theorem normalForm_telescope {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (H : PeriodicLocal k) : normalForm hB hk (cyclicTelescope B hk H) = 0 :=
  normalForm_eq_of_decomposition hB hk _ 0 H (by simp) (by simp)

theorem normalForm_add {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F G : PeriodicLocal k) :
    normalForm hB hk (F + G) = normalForm hB hk F + normalForm hB hk G := by
  obtain ⟨H, hR, hF⟩ := normalForm_spec hB hk F
  obtain ⟨J, hS, hG⟩ := normalForm_spec hB hk G
  apply normalForm_eq_of_decomposition hB hk (F + G) _ (H + J)
  · simp [hR, hS]
  · rw [map_add]
    calc
      F + G = (normalForm hB hk F + cyclicTelescope B hk H) +
          (normalForm hB hk G + cyclicTelescope B hk J) := congrArg₂ (· + ·) hF hG
      _ = _ := by abel

theorem normalForm_smul {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (a : ℚ) (F : PeriodicLocal k) :
    normalForm hB hk (a • F) = a • normalForm hB hk F := by
  obtain ⟨H, hR, hF⟩ := normalForm_spec hB hk F
  apply normalForm_eq_of_decomposition hB hk (a • F) _ (a • H)
  · simp [hR]
  · rw [map_smul, ← smul_add]
    exact congrArg (a • ·) hF

@[simp] theorem normalForm_neg {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) : normalForm hB hk (-F) = -normalForm hB hk F := by
  simpa using normalForm_smul hB hk (-1) F

/-- The canonical normal form is a rational linear map. -/
def normalFormLinear {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    PeriodicLocal k →ₗ[ℚ] PeriodicLocal k where
  toFun := normalForm hB hk
  map_add' := normalForm_add hB hk
  map_smul' := normalForm_smul hB hk

theorem normalForm_eq_zero_iff {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    normalForm hB hk F = 0 ↔ F ∈ LinearMap.range (cyclicTelescope B hk) := by
  constructor
  · intro h
    obtain ⟨H, _, hF⟩ := normalForm_spec hB hk F
    exact ⟨H, by simpa [h] using hF.symm⟩
  · rintro ⟨H, rfl⟩
    exact normalForm_telescope hB hk H

theorem normalForm_ker {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    LinearMap.ker (normalFormLinear hB hk) = LinearMap.range (cyclicTelescope B hk) := by
  ext F
  exact normalForm_eq_zero_iff hB hk F

@[simp] theorem normalForm_idempotent {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    normalForm hB hk (normalForm hB hk F) = normalForm hB hk F :=
  normalForm_of_rooted hB hk _ (drop_normalForm hB hk F)

/-- The exact weighted-root rule of the paper on every actual rooted chain. -/
theorem normalForm_shiftPower_rooted {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (hF : drop hk F = 0) (j : ℕ) :
    normalForm hB hk (shiftPower hk j F) = (B : ℚ) ^ j • F := by
  apply normalForm_eq_of_decomposition hB hk _ _ (-geometricPrimitive B hk j F)
  · simp [hF]
  · exact shiftPower_decomposition B hk j F

theorem normalForm_shift {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    normalForm hB hk (shift hk F) = (B : ℚ) • normalForm hB hk F := by
  have h := shiftPower_decomposition B hk 1 F
  have hn := congrArg (normalForm hB hk) h
  simpa [normalForm_add, normalForm_smul] using hn

@[simp] theorem normalForm_constantTuple {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (c : Fin k → ℚ) : normalForm hB hk (constantTuple c) = 0 := by
  rw [← telescope_constantPrimitive hB hk c]
  exact normalForm_telescope hB hk _

/-- There is also no ambiguity in the polynomial primitive. -/
theorem telescope_injective {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) :
    Function.Injective (cyclicTelescope B hk) := by
  apply (LinearMap.ker_eq_bot (f := cyclicTelescope B hk)).1
  apply LinearMap.ker_eq_bot'.2
  intro H hH
  obtain ⟨c, hc⟩ := exists_constant_of_drop_telescope_eq_zero B hk H (by simp [hH])
  have hs : shift hk H = (B : ℚ) • H := by
    rw [telescope_eq] at hH
    exact (sub_eq_zero.mp hH).symm
  have hp (n : ℕ) : shiftPower hk n H = (B : ℚ) ^ n • H := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [shiftPower_succ, ih, map_smul, hs, smul_smul, pow_succ]
  have hperiod : shiftPower hk k H = H := by
    rw [hc, shiftPower_period_constantTuple]
  have hscale : ((B : ℚ) ^ k - 1) • H = 0 := by
    have heq := (hp k).symm.trans hperiod
    rw [sub_smul, one_smul, heq, sub_self]
  have hb : (1 : ℚ) < B := Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide) hB)
  have hn : (B : ℚ) ^ k - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_pow₀ hb (Nat.ne_of_gt hk)).ne'
  exact (smul_eq_zero.mp hscale).resolve_left hn

theorem normalForm_decomposition_unique {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) :
    ∃! H : PeriodicLocal k, F = normalForm hB hk F + cyclicTelescope B hk H := by
  obtain ⟨H, _, hF⟩ := normalForm_spec hB hk F
  refine ⟨H, hF, ?_⟩
  intro J hJ
  exact telescope_injective hB hk (add_left_cancel (hJ.symm.trans hF))

theorem stripPoly_one_totalDegree_le (p : LocalPoly) :
    (stripPoly 1 p).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_le_of_support_subset
    (support_rename_killCompl_subset (p := p) Nat.succ_injective)
  rw [cycSh_totalDegree] at h
  simpa [stripPoly_one_eq_killCompl] using h

theorem drop_totalDegree_le {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (d : ℕ) (hF : ∀ r, (F r).totalDegree ≤ d) :
    ∀ r, (drop hk F r).totalDegree ≤ d := by
  intro r
  exact (stripPoly_one_totalDegree_le _).trans (hF (predecessor hk r))

theorem rootPart_totalDegree_le {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (d : ℕ) (hF : ∀ r, (F r).totalDegree ≤ d) :
    ∀ r, (rootPart hk F r).totalDegree ≤ d := by
  intro r
  change (F r - rename Nat.succ (drop hk F (cyclicSucc hk r))).totalDegree ≤ d
  apply (totalDegree_sub _ _).trans
  apply max_le (hF r)
  rw [cycSh_totalDegree]
  exact drop_totalDegree_le hk F d hF _

/-- The finite elimination preserves every uniform gap-degree bound. -/
theorem exists_rooted_decomposition_degree {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (d : ℕ) (hF : ∀ r, (F r).totalDegree ≤ d) :
    ∃ R H : PeriodicLocal k, drop hk R = 0 ∧ F = R + cyclicTelescope B hk H ∧
      ∀ r, (R r).totalDegree ≤ d := by
  obtain ⟨n, c, hc⟩ := exists_dropPower_constant hk F
  suffices ∀ n : ℕ, ∀ F : PeriodicLocal k, ∀ c : Fin k → ℚ,
      dropPower hk n F = constantTuple c → (∀ r, (F r).totalDegree ≤ d) →
      ∃ R H : PeriodicLocal k, drop hk R = 0 ∧ F = R + cyclicTelescope B hk H ∧
        ∀ r, (R r).totalDegree ≤ d by
    exact this n F c hc hF
  intro n
  induction n with
  | zero =>
    intro F c hc hF
    refine ⟨0, constantPrimitive B hk c, by simp, ?_, ?_⟩
    · simpa [telescope_constantPrimitive hB hk] using hc
    · intro r
      simp
  | succ n ih =>
    intro F c hc hF
    have htail : dropPower hk n (drop hk F) = constantTuple c := by
      rw [dropPower_drop]
      exact hc
    obtain ⟨R, H, hR, hD, hdeg⟩ := ih (drop hk F) c htail (drop_totalDegree_le hk F d hF)
    refine ⟨rootPart hk F + (B : ℚ) • R, (B : ℚ) • H - drop hk F, ?_, ?_, ?_⟩
    · simp [hR]
    · calc
        F = rootPart hk F + (B : ℚ) • drop hk F -
            cyclicTelescope B hk (drop hk F) := one_step_decomposition B hk F
        _ = rootPart hk F + (B : ℚ) • R +
            cyclicTelescope B hk ((B : ℚ) • H - drop hk F) := by
          rw [map_sub, map_smul, hD]
          module
    · intro r
      apply (totalDegree_add _ _).trans
      apply max_le (rootPart_totalDegree_le hk F d hF r)
      exact (totalDegree_smul_le (B : ℚ) (R r)).trans (hdeg r)

theorem normalForm_totalDegree_le {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (F : PeriodicLocal k) (d : ℕ) (hF : ∀ r, (F r).totalDegree ≤ d) :
    ∀ r, (normalForm hB hk F r).totalDegree ≤ d := by
  obtain ⟨R, H, hR, hD, hdeg⟩ := exists_rooted_decomposition_degree hB hk F d hF
  rw [normalForm_eq_of_decomposition hB hk F R H hR hD]
  exact hdeg

/-- The unique polynomial primitive associated with canonical reduction. -/
def primitive {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) :
    PeriodicLocal k := Classical.choose (normalForm_spec hB hk F)

theorem decomposition {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (F : PeriodicLocal k) :
    F = normalForm hB hk F + cyclicTelescope B hk (primitive hB hk F) :=
  (Classical.choose_spec (normalForm_spec hB hk F)).2

/-- A polynomial in a single period component: the paper's `eᵣ p`. -/
def labelled {k : ℕ} (r : Fin k) (p : LocalPoly) : PeriodicLocal k :=
  fun s ↦ if s = r then p else 0

theorem shiftPower_apply_polynomial {k : ℕ} (hk : 0 < k) (j : ℕ)
    (F : PeriodicLocal k) (r : Fin k) :
    shiftPower hk j F r =
      rename (fun i ↦ i + j) (F ((cyclicSucc hk)^[j] r)) := by
  induction j generalizing r with
  | zero =>
    change F r = rename id (F r)
    exact (rename_id_apply (F r)).symm
  | succ j ih =>
    simp only [shiftPower_succ, shift_apply, ih, rename_rename,
      Function.iterate_succ_apply, Function.comp_def, Nat.add_succ]

/-- This explicitly tracks the paper's opposing component and gap shifts. -/
theorem shiftPower_labelled {k : ℕ} (hk : 0 < k) (j : ℕ)
    (r : Fin k) (p : LocalPoly) :
    shiftPower hk j (labelled ((cyclicSucc hk)^[j] r) p) =
      labelled r (rename (fun i ↦ i + j) p) := by
  funext s
  rw [shiftPower_apply_polynomial]
  by_cases hs : s = r
  · subst s
    simp [labelled]
  · have hinj : Function.Injective ((cyclicSucc hk)^[j]) :=
      (cyclicSuccEquiv hk).injective.iterate j
    have hne := hinj.ne hs
    simp [labelled, hs, hne]

theorem labelled_monomial_rooted {k : ℕ} (hk : 0 < k) (r : Fin k)
    (m : ℕ →₀ ℕ) (c : ℚ) (hm : m 0 ≠ 0) :
    drop hk (labelled r (monomial m c)) = 0 := by
  rw [drop_eq_zero_iff_rooted]
  intro s d hd
  have hmd : m ≠ d := by
    intro h
    apply hm
    rw [h]
    exact hd
  by_cases hs : s = r
  · simp [labelled, hs, coeff_monomial, hmd, Ne.symm hmd]
  · simp [labelled, hs]

/-- The literal labelled-monomial normal-form formula from the frozen paper:
`N(eᵣ Sʲ M) = Bʲ e_(r+j) M` when the monomial `M` contains `u₀`.
The label `r+j` is represented by `j` applications of cyclic successor. -/
theorem normalForm_labelled_monomial {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (r : Fin k) (j : ℕ) (m : ℕ →₀ ℕ) (c : ℚ) (hm : m 0 ≠ 0) :
    normalForm hB hk (labelled r (rename (fun i ↦ i + j) (monomial m c))) =
      (B : ℚ) ^ j • labelled ((cyclicSucc hk)^[j] r) (monomial m c) := by
  rw [← shiftPower_labelled hk j r (monomial m c)]
  exact normalForm_shiftPower_rooted hB hk _
    (labelled_monomial_rooted hk _ m c hm) j

end

end PrimeGapNormality.Prime.CoreCyclic
