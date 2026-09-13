/-
Vendored source candidate from https://github.com/alexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
Pinned commit: a5154676af9aa3095150ee410cdda80555aa0642 (2026-08-30). Upstream license: Apache-2.0.
Only the module path is relocated under PrimeGapNormality.ClassicalPNT.
This candidate has not yet been compiled or axiom-audited on Lean/mathlib 4.33.1.
-/

import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
