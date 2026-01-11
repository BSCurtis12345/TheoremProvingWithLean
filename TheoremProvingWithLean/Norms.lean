import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.Seminorm
import Init.Prelude
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Algebra.Order.Group.Unbundled.Abs

set_option linter.style.longLine false

open scoped BigOperators


namespace Norms

-- Definining the concept of ℝ^n for our project
abbrev Rn (n : ℕ) := Fin n → ℝ

-- We use Mathlibs definition of a Seminorm to represent our Norms. A seminorm is a norm without the property N x = 0 → x = 0
-- Where this property is required we introduce it as an assumption h_def
theorem reverse_triangle_ineq {n : ℕ} (x y : Rn n) (N : Seminorm ℝ (Rn n)) :
  |N x- N y| ≤ N (x-y) := by
  /-
  This theorem proves the reverse triangle inequality for normed additive commutative groups |‖x‖-‖y‖| ≤ ‖x-y‖.

  Mathlib results used :
    • abs_of_nonneg : proves (0 ≤ a → |a| = a). This is definitional for the absolute value on the reals
    • norm_add_le : proves the triangle inequality. This is definitional for norms
    • not_le : proves that in a totally ordered set (¬a ≤ b ↔ b < a). Happy to assume this for our purposes
    • abs_of_neg: proves (a < 0 → |a| = -a). This is definitional for the absolute value on the reals
  -/
  by_cases h : 0 ≤ N x - N y
  · apply abs_of_nonneg at h
    rw [h]
    have h : N x ≤ N y + N (x - y) :=
    by
      simpa using N.add_le' y (x - y)
    exact tsub_le_iff_left.mpr h
  · apply not_le.mp at h
    apply abs_of_neg at h
    simp at h
    rw [h]
    have h' : N y ≤ N x + N (y - x) :=
    by
      simpa using N.add_le' x (y - x)
    have h'' : N (x - y) = N (y - x) :=
    by
      simpa using N.neg' (y - x)
    have h''' : N y ≤ N x + N (x - y) :=
    by
      simpa [h''.symm] using h'
    exact tsub_le_iff_left.mpr h'''

end Norms
