import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.Seminorm
import Init.Prelude
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Algebra.Order.Group.Unbundled.Abs

-- Disable the linter warning for long lines
set_option linter.style.longLine false

-- Enable notation for big operators such as ∑
open scoped BigOperators

namespace Norms

-- Defining the concept of ℝⁿ as functions from Fin n → ℝ
-- This is a coordinate-wise representation of finite-dimensional real vectors
abbrev Rn (n : ℕ) := Fin n → ℝ

-- We use mathlib's definition of a Seminorm to represent our "norms".
-- A seminorm satisfies all norm axioms except definiteness:
--   N x = 0 does NOT necessarily imply x = 0.
-- Whenever definiteness is required, it is introduced separately as an assumption (h_def).

-- Reverse triangle inequality for a seminorm on ℝⁿ
theorem reverse_triangle_ineq {n : ℕ} (x y : Rn n) (N : Seminorm ℝ (Rn n)) :
  |N x - N y| ≤ N (x - y) := by
  /-
  This theorem proves the reverse triangle inequality:
    |N x - N y| ≤ N (x - y)

  The proof proceeds by a case split on the sign of (N x - N y),
  converting the absolute value into either (N x - N y) or (N y - N x),
  and then applying the triangle inequality for seminorms.

  Mathlib results used:

    • abs_of_nonneg :
        If 0 ≤ a, then |a| = a.
        This unfolds the absolute value in the nonnegative case.

    • abs_of_neg :
        If a < 0, then |a| = -a.
        This unfolds the absolute value in the negative case.

    • not_le :
        In a linear order, ¬a ≤ b ↔ b < a.
        Used to convert ¬(0 ≤ a) into a < 0.

    • N.add_le' :
        The triangle inequality for seminorms:
        N (x + y) ≤ N x + N y.

    • N.neg' :
        Seminorm invariance under negation:
        N (-x) = N x.

    • tsub_le_iff_left :
        Rewrites inequalities of the form a - b ≤ c
        into a ≤ b + c.
  -/
  -- Case split on whether N x - N y is nonnegative
  by_cases h : 0 ≤ N x - N y
  · -- Nonnegative case: |N x - N y| = N x - N y
    apply abs_of_nonneg at h
    rw [h]
    -- Apply the triangle inequality in the form:
    -- N x ≤ N y + N (x - y)
    have h : N x ≤ N y + N (x - y) := by
      simpa using N.add_le' y (x - y)
    -- Rearrange to obtain N x - N y ≤ N (x - y)
    exact tsub_le_iff_left.mpr h
  · -- Negative case: N x - N y < 0
    apply not_le.mp at h
    apply abs_of_neg at h
    simp at h
    rw [h]
    -- Triangle inequality with x and y swapped:
    -- N y ≤ N x + N (y - x)
    have h' : N y ≤ N x + N (y - x) := by
      simpa using N.add_le' x (y - x)
    -- Seminorm symmetry under negation:
    -- N (x - y) = N (y - x)
    have h'' : N (x - y) = N (y - x) := by
      simpa using N.neg' (y - x)
    -- Rewrite h' using the symmetry of subtraction
    have h''' : N y ≤ N x + N (x - y) := by
      simpa [h''.symm] using h'
    -- Rearrange to obtain N y - N x ≤ N (x - y)
    exact tsub_le_iff_left.mpr h'''

end Norms
