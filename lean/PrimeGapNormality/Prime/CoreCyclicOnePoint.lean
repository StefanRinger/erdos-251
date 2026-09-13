import PrimeGapNormality.Prime.CoreCyclicCanonical
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Positivity

/-!
The one-point action from the frozen paper, in actual signed gap variables.
Index `-1` is the moving coordinate `v`; index `0` becomes the fixed span
`W` after the invertible substitution `u₀ = W-v`.
-/

namespace PrimeGapNormality.Prime.CoreCyclic.OnePoint

open MvPolynomial
open scoped BigOperators

noncomputable section

abbrev SignedPoly := MvPolynomial ℤ ℚ

/-- The local polynomial window whose initial gap has signed index `-j`. -/
def signedShift (j : ℕ) : LocalPoly →ₐ[ℚ] SignedPoly :=
  rename fun i ↦ (i : ℤ) - (j : ℤ)

theorem signedShift_injective (j : ℕ) : Function.Injective (signedShift j) := by
  apply rename_injective
  intro a b h
  change (a : ℤ) - (j : ℤ) = (b : ℤ) - (j : ℤ) at h
  omega

/-- The finite action before replacing the adjacent gaps by `v` and `W-v`. -/
def preAction (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ) (s : Fin k)
    (F : PeriodicLocal k) : SignedPoly :=
  ∑ j ∈ Finset.range (w + 2), (B : ℚ) ^ j • signedShift j
    (F ((predecessor hk)^[j] (cyclicSucc hk s)))

def moveSubst : SignedPoly →ₐ[ℚ] SignedPoly :=
  aeval fun i ↦ if i = 0 then X 0 - X (-1) else X i

def unmoveSubst : SignedPoly →ₐ[ℚ] SignedPoly :=
  aeval fun i ↦ if i = 0 then X 0 + X (-1) else X i

@[simp] theorem moveSubst_X (i : ℤ) :
    moveSubst (X i) = if i = 0 then X 0 - X (-1) else X i := by
  simp [moveSubst]

@[simp] theorem unmoveSubst_X (i : ℤ) :
    unmoveSubst (X i) = if i = 0 then X 0 + X (-1) else X i := by
  simp [unmoveSubst]

theorem unmove_move (p : SignedPoly) : unmoveSubst (moveSubst p) = p := by
  have h : unmoveSubst.comp moveSubst = AlgHom.id ℚ SignedPoly := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp
    · simp [hi]
  exact AlgHom.congr_fun h p

theorem moveSubst_injective : Function.Injective moveSubst :=
  (show Function.LeftInverse unmoveSubst moveSubst from unmove_move).injective

/-- The polynomial `πₛ(v;y)` itself, with `v=X(-1)` and `W=X0`. -/
def action (B : ℕ) {k : ℕ} (hk : 0 < k) (w : ℕ) (s : Fin k)
    (F : PeriodicLocal k) : SignedPoly := moveSubst (preAction B hk w s F)

/-- Moving one point differentiates the left gap positively and the right
gap negatively. The equality is proved on polynomial generators. -/
theorem pderiv_moveSubst (p : SignedPoly) :
    pderiv (-1) (moveSubst p) = moveSubst (pderiv (-1) p - pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [moveSubst, pderiv_C]
  | add p q hp hq => simp [map_add, map_sub, hp, hq]; ring
  | mul_X p i hp =>
    by_cases hi : i = 0
    · subst i
      simp [map_mul, map_sub, pderiv_mul, hp] <;> ring
    · by_cases hv : i = -1
      · subst i
        simp [map_mul, map_sub, pderiv_mul, hp] <;> ring
      · simp [map_mul, map_sub, pderiv_mul, hp, hi, hv, pderiv_X, Pi.single_apply] <;> ring

theorem action_pderiv_ne_zero_iff (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (F : PeriodicLocal k) :
    pderiv (-1) (action B hk w s F) ≠ 0 ↔
      pderiv (-1) (preAction B hk w s F) - pderiv 0 (preAction B hk w s F) ≠ 0 := by
  rw [action, pderiv_moveSubst]
  constructor
  · intro h he
    exact h (by simp [he])
  · intro h he
    apply h
    apply moveSubst_injective
    simpa using he

/-- A nonzero coefficient with positive exponent survives formal
differentiation over `ℚ`. -/
theorem pderiv_ne_zero_of_coeff {σ : Type*} (p : MvPolynomial σ ℚ)
    (m : σ →₀ ℕ) (i : σ) (hm : p.coeff m ≠ 0) (hi : m i ≠ 0) :
    pderiv i p ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (m - Finsupp.single i 1)) hzero
  rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi, coeff_zero] at hcoeff
  let n : ℕ := (m - Finsupp.single i 1 : σ →₀ ℕ) i
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  exact (mul_ne_zero hm hn) hcoeff

theorem pderiv_ne_zero_of_mem_vars {σ : Type*} (p : MvPolynomial σ ℚ)
    (i : σ) (hi : i ∈ p.vars) : pderiv i p ≠ 0 := by
  obtain ⟨m, hm, hi⟩ := (mem_vars_iff_mem_support i).1 hi
  exact pderiv_ne_zero_of_coeff p m i (MvPolynomial.mem_support_iff.1 hm)
    (Finsupp.mem_support_iff.1 hi)

/-- Differentiation in another variable preserves the rooted coefficient
condition, so a nonzero derivative still genuinely depends on `u₀`. -/
theorem pderiv_zero_pderiv_ne_zero_of_rooted (p : LocalPoly) (h : ℕ)
    (hh : h ≠ 0) (hroot : ∀ m : ℕ →₀ ℕ, m 0 = 0 → p.coeff m = 0)
    (hp : pderiv h p ≠ 0) : pderiv 0 (pderiv h p) ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hp
  have hm0 : m 0 ≠ 0 := by
    intro heq
    rw [coeff_pderiv, hroot, zero_mul] at hm
    · exact hm rfl
    · simp [heq, hh, Ne.symm hh]
  exact pderiv_ne_zero_of_coeff (pderiv h p) m 0 hm hm0

/-- Homogeneous truncation preserves the actual rooted coefficient condition. -/
theorem rooted_homogeneousComponent {k : ℕ} (hk : 0 < k) (F : PeriodicLocal k)
    (hF : drop hk F = 0) (d : ℕ) :
    drop hk (fun r ↦ homogeneousComponent d (F r)) = 0 := by
  rw [drop_eq_zero_iff_rooted] at hF ⊢
  intro r m hm
  simp [coeff_homogeneousComponent, hF r m hm]

theorem preAction_isHomogeneous (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (F : PeriodicLocal k) (d : ℕ)
    (hF : ∀ r, (F r).IsHomogeneous d) :
    (preAction B hk w s F).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro j hj
  rw [smul_eq_C_mul]
  exact (hF _).rename_isHomogeneous.C_mul _

theorem moveSubst_isHomogeneous (p : SignedPoly) (d : ℕ) (hp : p.IsHomogeneous d) :
    (moveSubst p).IsHomogeneous d := by
  have hlin : ∀ i : ℤ, (if i = 0 then (X 0 - X (-1) : SignedPoly) else X i).IsHomogeneous 1 := by
    intro i
    split_ifs
    · exact (isHomogeneous_X ℚ 0).sub (isHomogeneous_X ℚ (-1))
    · exact isHomogeneous_X ℚ i
  simpa [moveSubst] using hp.aeval _ hlin

theorem action_isHomogeneous (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (F : PeriodicLocal k) (d : ℕ)
    (hF : ∀ r, (F r).IsHomogeneous d) :
    (action B hk w s F).IsHomogeneous d :=
  moveSubst_isHomogeneous _ d (preAction_isHomogeneous B hk w s F d hF)

theorem pderiv_comm {σ : Type*} (p : MvPolynomial σ ℚ) (i j : σ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · ext m
    simp [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij,
      add_comm, add_left_comm, add_assoc, mul_comm] <;> ring

theorem signedShift_pderiv (j i : ℕ) (p : LocalPoly) :
    pderiv ((i : ℤ) - (j : ℤ)) (signedShift j p) = signedShift j (pderiv i p) := by
  apply pderiv_rename
  intro a b h
  change (a : ℤ) - (j : ℤ) = (b : ℤ) - (j : ℤ) at h
  omega

theorem signedShift_pderiv_eq_zero_of_lt (j : ℕ) (p : LocalPoly) (a : ℤ)
    (ha : a < -(j : ℤ)) : pderiv a (signedShift j p) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨i, _, hi⟩ := mem_vars_rename (fun i : ℕ ↦ (i : ℤ) - j) p hmem
  omega

theorem signedShift_pderiv_eq_zero_of_gt (j h : ℕ) (p : LocalPoly)
    (hp : ∀ i ∈ p.vars, i ≤ h) (a : ℤ) (ha : (h : ℤ) - j < a) :
    pderiv a (signedShift j p) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨i, hi, heq⟩ := mem_vars_rename (fun i : ℕ ↦ (i : ℤ) - j) p hmem
  have := hp i hi
  omega

/-- The unique leftmost mixed-partial contribution. This calculation also
works at `h=0`, where it becomes a second derivative in `u₀`. -/
theorem shifted_mixedPartial (h j : ℕ) (p : LocalPoly)
    (hp : ∀ i ∈ p.vars, i ≤ h) :
    pderiv (-(h : ℤ) - 1)
      (pderiv (-1) (signedShift j p) - pderiv 0 (signedShift j p)) =
      if j = h + 1 then signedShift j (pderiv 0 (pderiv h p)) else 0 := by
  by_cases hj : j = h + 1
  · subst j
    rw [if_pos rfl]
    have hright : pderiv 0 (signedShift (h + 1) p) = 0 :=
      signedShift_pderiv_eq_zero_of_gt (h + 1) h p hp 0 (by omega)
    have hleft : pderiv (-1) (signedShift (h + 1) p) =
        signedShift (h + 1) (pderiv h p) := by
      convert signedShift_pderiv (h + 1) h p using 1 <;> push_cast <;> ring
    rw [hright, sub_zero, hleft]
    convert signedShift_pderiv (h + 1) 0 (pderiv h p) using 1 <;> push_cast <;> ring
  · rw [if_neg hj]
    by_cases hjlt : j < h + 1
    · have hz : pderiv (-(h : ℤ) - 1) (signedShift j p) = 0 :=
        signedShift_pderiv_eq_zero_of_lt j p _ (by omega)
      rw [map_sub, pderiv_comm _ (-(h : ℤ) - 1) (-1),
        pderiv_comm _ (-(h : ℤ) - 1) 0]
      simp [hz]
    · have hz₁ : pderiv (-1) (signedShift j p) = 0 :=
        signedShift_pderiv_eq_zero_of_gt j h p hp (-1) (by omega)
      have hz₂ : pderiv 0 (signedShift j p) = 0 :=
        signedShift_pderiv_eq_zero_of_gt j h p hp 0 (by omega)
      rw [hz₁, hz₂, sub_self, map_zero]

theorem preAction_mixedPartial (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w h : ℕ) (hhw : h ≤ w) (s : Fin k) (F : PeriodicLocal k)
    (hF : ∀ r i, i ∈ (F r).vars → i ≤ h) :
    pderiv (-(h : ℤ) - 1)
      (pderiv (-1) (preAction B hk w s F) - pderiv 0 (preAction B hk w s F)) =
      (B : ℚ) ^ (h + 1) • signedShift (h + 1)
        (pderiv 0 (pderiv h (F ((predecessor hk)^[h + 1] (cyclicSucc hk s))))) := by
  unfold preAction
  simp only [map_sum, Derivation.map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  simp only [map_sum, Derivation.map_smul, shifted_mixedPartial h _ _ (hF _)]
  rw [Finset.sum_eq_single (h + 1)]
  · simp
  · intro j hj hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

/-- A nonzero top mixed partial produces a genuinely moving local action. -/
theorem exists_action_of_mixedPartial {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w h : ℕ) (hhw : h ≤ w) (F : PeriodicLocal k)
    (hF : ∀ r i, i ∈ (F r).vars → i ≤ h) (r : Fin k)
    (hr : pderiv 0 (pderiv h (F r)) ≠ 0) :
    ∃ s : Fin k, pderiv (-1) (action B hk w s F) ≠ 0 := by
  have hsurj : Function.Surjective
      (fun s : Fin k ↦ (predecessor hk)^[h + 1] (cyclicSucc hk s)) :=
    ((cyclicSuccEquiv hk).symm.surjective.iterate (h + 1)).comp
      (cyclicSuccEquiv hk).surjective
  obtain ⟨s, hs⟩ := hsurj r
  change (predecessor hk)^[h + 1] (cyclicSucc hk s) = r at hs
  refine ⟨s, (action_pderiv_ne_zero_iff B hk w s F).2 ?_⟩
  intro hzero
  have hm := preAction_mixedPartial B hk w h hhw s F hF
  rw [hzero, map_zero, hs] at hm
  have hb : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hr' : signedShift (h + 1) (pderiv 0 (pderiv h (F r))) ≠ 0 := by
    intro hz
    apply hr
    apply signedShift_injective (h + 1)
    simpa using hz
  exact (smul_ne_zero (pow_ne_zero (h + 1) hb) hr') hm.symm

/-- The `h≥1` case of the paper's normal nonzero one-point test. -/
theorem exists_action_of_positive_maxVar {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w h : ℕ) (hh : 0 < h) (hhw : h ≤ w) (F : PeriodicLocal k)
    (hroot : drop hk F = 0) (hF : ∀ r i, i ∈ (F r).vars → i ≤ h)
    (r : Fin k) (hr : h ∈ (F r).vars) :
    ∃ s : Fin k, pderiv (-1) (action B hk w s F) ≠ 0 := by
  apply exists_action_of_mixedPartial hB hk w h hhw F hF r
  apply pderiv_zero_pderiv_ne_zero_of_rooted (F r) h (Nat.ne_of_gt hh)
    ((drop_eq_zero_iff_rooted hk F).1 hroot r)
  exact pderiv_ne_zero_of_mem_vars (F r) h hr

theorem homogeneous_eq_monomial_of_vars_le_zero (p : LocalPoly) (d : ℕ)
    (hp : p.IsHomogeneous d) (hv : ∀ i ∈ p.vars, i ≤ 0) :
    p = monomial (Finsupp.single 0 d) (p.coeff (Finsupp.single 0 d)) := by
  apply eq_monomial_of_support_subset_singleton
  intro m hm
  have hs : m = Finsupp.single 0 (m 0) := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · have hnot : i ∉ p.vars := by
        intro him
        have := hv i him
        omega
      simp [hi, mem_support_notMem_vars_zero hm hnot]
  have hd : m.degree = d := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (hp.coeff_eq_zero hne)
  rw [hs, Finsupp.degree_single] at hd
  simpa [hd] using hs

theorem pderiv_twice_ne_zero_of_coeff (p : LocalPoly) (m : ℕ →₀ ℕ) (i : ℕ)
    (hm : p.coeff m ≠ 0) (hi : 2 ≤ m i) : pderiv i (pderiv i p) ≠ 0 := by
  have hi0 : m i ≠ 0 := by omega
  have hm' : (pderiv i p).coeff (m - Finsupp.single i 1) ≠ 0 := by
    rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi0]
    apply mul_ne_zero hm
    positivity
  apply pderiv_ne_zero_of_coeff (pderiv i p) _ i hm'
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
  omega

theorem linear_shift_derivative (j : ℕ) (a : ℚ) :
    pderiv (-1) (signedShift j (C a * X 0)) - pderiv 0 (signedShift j (C a * X 0)) =
      (if j = 1 then C a else 0) - (if j = 0 then C a else 0) := by
  cases j with
  | zero => simp [signedShift, pderiv_mul, pderiv_C, rename_C]
  | succ j =>
    cases j with
    | zero => simp [signedShift, pderiv_mul, pderiv_C, rename_C]
    | succ j =>
      have hv : ∀ i ∈ (C a * X 0 : LocalPoly).vars, i ≤ 0 := by
        intro i hi
        have hs : (C a * X 0 : LocalPoly).vars ⊆ {0} := by
          simpa using (vars_mul (C a : LocalPoly) (X 0))
        simpa using hs hi
      have h₁ := signedShift_pderiv_eq_zero_of_gt (j + 1 + 1) 0 (C a * X 0) hv (-1) (by omega)
      have h₂ := signedShift_pderiv_eq_zero_of_gt (j + 1 + 1) 0 (C a * X 0) hv 0 (by omega)
      rw [h₁, h₂]
      simp [show j + 1 + 1 ≠ 1 by omega, show j + 1 + 1 ≠ 0 by omega]

theorem linear_preAction_derivative (B : ℕ) {k : ℕ} (hk : 0 < k)
    (w : ℕ) (s : Fin k) (F : PeriodicLocal k) (a : Fin k → ℚ)
    (hF : ∀ r, F r = C (a r) * X 0) :
    pderiv (-1) (preAction B hk w s F) - pderiv 0 (preAction B hk w s F) =
      C ((B : ℚ) * a s - a (cyclicSucc hk s)) := by
  unfold preAction
  simp only [map_sum, Derivation.map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
  simp_rw [hF, linear_shift_derivative, smul_sub, smul_ite, smul_zero]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq', smul_eq_C_mul]

theorem exists_action_of_linear {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w : ℕ) (F : PeriodicLocal k) (a : Fin k → ℚ)
    (hF : ∀ r, F r = C (a r) * X 0) (hF0 : F ≠ 0) :
    ∃ s : Fin k, pderiv (-1) (action B hk w s F) ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have ht : cyclicTelescope B hk (constantTuple a) = 0 := by
    funext s
    rw [telescope_constantTuple]
    change C ((B : ℚ) * a s - a (cyclicSucc hk s)) = 0
    apply C_eq_zero.mpr
    have hp : pderiv (-1) (preAction B hk w s F) -
        pderiv 0 (preAction B hk w s F) = 0 := by
      apply moveSubst_injective
      simpa [action, pderiv_moveSubst] using hnone s
    have hc : (C ((B : ℚ) * a s - a (cyclicSucc hk s)) : SignedPoly) = 0 :=
      (linear_preAction_derivative B hk w s F a hF).symm.trans hp
    exact C_eq_zero.mp hc
  have ha : constantTuple a = 0 := telescope_injective hB hk (by simpa using ht)
  apply hF0
  funext r
  have har := congrFun ha r
  simp only [constantTuple, Pi.zero_apply, C_eq_zero] at har
  simp [hF, har]

theorem exists_action_of_homogeneous_vars_zero {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w d : ℕ) (F : PeriodicLocal k) (hroot : drop hk F = 0) (hF0 : F ≠ 0)
    (hhom : ∀ r, (F r).IsHomogeneous d)
    (hv : ∀ r i, i ∈ (F r).vars → i ≤ 0) :
    ∃ s : Fin k, pderiv (-1) (action B hk w s F) ≠ 0 := by
  have hmono := fun r ↦ homogeneous_eq_monomial_of_vars_le_zero (F r) d (hhom r) (hv r)
  by_cases hd0 : d = 0
  · subst d
    exfalso
    apply hF0
    have hc : F = constantTuple (fun r ↦ (F r).coeff 0) := by
      funext r
      simpa [constantTuple] using hmono r
    rw [hc] at hroot ⊢
    exact constantTuple_eq_zero_of_drop_eq_zero hk _ hroot
  · by_cases hd1 : d = 1
    · subst d
      apply exists_action_of_linear hB hk w F (fun r ↦ (F r).coeff (Finsupp.single 0 1)) _ hF0
      intro r
      rw [C_mul_X_eq_monomial]
      exact hmono r
    · have hd2 : 2 ≤ d := by omega
      obtain ⟨r, hr⟩ : ∃ r, F r ≠ 0 := by
        by_contra hn
        push_neg at hn
        exact hF0 (funext hn)
      have hc : (F r).coeff (Finsupp.single 0 d) ≠ 0 := by
        intro h
        apply hr
        rw [hmono r, h, monomial_zero]
      apply exists_action_of_mixedPartial hB hk w 0 (Nat.zero_le _) F hv r
      apply pderiv_twice_ne_zero_of_coeff (F r) (Finsupp.single 0 d) 0 hc
      simpa using hd2

/-- Every nonzero rooted homogeneous tuple has some genuinely moving action.
The width is a proved variable bound on the actual input polynomials. -/
theorem exists_action_of_normal_homogeneous {B k : ℕ} (hB : 2 ≤ B) (hk : 0 < k)
    (w d : ℕ) (F : PeriodicLocal k) (hroot : drop hk F = 0) (hF0 : F ≠ 0)
    (hhom : ∀ r, (F r).IsHomogeneous d)
    (hw : ∀ r i, i ∈ (F r).vars → i ≤ w) :
    ∃ s : Fin k, pderiv (-1) (action B hk w s F) ≠ 0 := by
  classical
  let V : Finset ℕ := Finset.univ.biUnion fun r : Fin k ↦ (F r).vars
  have hV : V.Nonempty := by
    obtain ⟨r, hr⟩ : ∃ r, F r ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hF0 (funext hn)
    obtain ⟨m, hm⟩ := exists_coeff_ne_zero hr
    have hm0 : m 0 ≠ 0 := by
      intro hz
      exact hm ((drop_eq_zero_iff_rooted hk F).1 hroot r m hz)
    refine ⟨0, Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, ?_⟩⟩
    exact (mem_vars_iff_mem_support 0).2
      ⟨m, MvPolynomial.mem_support_iff.2 hm, Finsupp.mem_support_iff.2 hm0⟩
  let h : ℕ := V.max' hV
  have hhmem : h ∈ V := Finset.max'_mem V hV
  obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hhmem
  have hbound : ∀ r i, i ∈ (F r).vars → i ≤ h := by
    intro r i hi
    exact Finset.le_max' V i (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hi⟩)
  have hhw : h ≤ w := hw r h hr
  by_cases hh : h = 0
  · apply exists_action_of_homogeneous_vars_zero hB hk w d F hroot hF0 hhom
    simpa [hh] using hbound
  · exact exists_action_of_positive_maxVar hB hk w h (Nat.pos_of_ne_zero hh) hhw F hroot hbound r hr

end

end PrimeGapNormality.Prime.CoreCyclic.OnePoint
