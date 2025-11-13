import Mathlib.Algebra.Order.Group.Unbundled.Abs
--import Mathlib.Order.Defs.LinearOrder
--import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Module.Basic

variable {K V : Type*} [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]

theorem reverse_triangle_ineq (x y : V) : |‖x‖-‖y‖| ≤ ‖x-y‖ := by
/-
This theorem proves the reverse triangle inequality for normed additive commutative groups |‖x‖-‖y‖| ≤ ‖x-y‖.

Mathlib results used :
  • abs_of_nonneg : proves (0 ≤ a → |a| = a). This is definitional for the absolute value on the reals
  • norm_add_le : proves the triangle inequality. This is definitional for norms
  • not_le : proves that in a totally ordered set (¬a ≤ b ↔ b < a). Happy to assume this for our purposes
  • abs_of_neg: proves (a < 0 → |a| = -a). This is definitional for the absolute value on the reals
-/

  by_cases h : 0 ≤ ‖x‖-‖y‖
  · apply abs_of_nonneg at h
    rw [h]
    simpa using norm_add_le (x-y) y
  · apply not_le.mp at h
    apply abs_of_neg at h
    simp at h
    rw [h, norm_sub_rev] -- norm_sub_rev not directly equivalent to anything in the NMT definition of a norm: requires additional proof?
    simpa using norm_add_le (y-x) x

  done
