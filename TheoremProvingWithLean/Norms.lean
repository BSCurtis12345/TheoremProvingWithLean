import TheoremProvingWithLean.UpperBound

-- Disable the linter warning for long lines
set_option linter.style.longLine false

set_option linter.flexible false

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
-- For more explanation, please see README.md.

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


-- A seminorm on ℝⁿ is continuous provided:
--  • it is definite (N x = 0 ↔ x = 0)
--  • the dimension n is positive (we provide these assumptions)
-- The proof proceeds by showing that the seminorm is Lipschitz,
-- and then use the fact that Lipschitz maps are continuous.
lemma norm_continuous (n : ℕ) (N : Seminorm ℝ (Rn n))
  (h_def : ∀ x : Rn n, N x = 0 ↔ x = 0) (h_dim : 0 < n) :
  Continuous (fun x : Rn n => N x) :=
  by
    -- First, we establish the existence of a global Lipschitz-type bound:
    -- ∃ C, ∀ x y, |N x - N y| ≤ C * ‖x - y‖
    have h : ∃ (C : ℝ), ∀ (x y : Rn n), |N x - N y| ≤ C * ‖x - y‖ :=
    by
      -- Use the Upper_Bound theorem previously proved:
      -- It provides a constant C > 0 such that N z ≤ C * ‖z‖ for all z
      rcases UpperBound.Upper_Bound n N h_def h_dim with ⟨C, hCpos, hBound⟩
      -- We choose this same constant C for the Lipschitz estimate
      refine ⟨C, ?_⟩
      intro x y
      -- Apply the reverse triangle inequality for seminorms:
      -- |N x - N y| ≤ N (x - y)
      have h1 : |N x - N y| ≤ N (x - y) := by
        exact Norms.reverse_triangle_ineq x y N
      -- Apply the global upper bound on the seminorm:
      -- N (x - y) ≤ C * ‖x - y‖
      have h2 : N (x - y) ≤ C * ‖x - y‖ := by
        exact hBound (x - y)
      -- Combine the two inequalities by transitivity
      exact le_trans h1 h2
    -- Extract the constant C and its bound from the existential statement
    rcases h with ⟨C, hC⟩
    -- Re-introduce the Upper_Bound result explicitly,
    -- this time keeping track of positivity of the constant
    rcases UpperBound.Upper_Bound n N h_def h_dim with ⟨C₀, hC₀pos, hBound⟩
    -- We now show that N is Lipschitz with constant C₀
    have hLip : LipschitzWith ⟨C₀, le_of_lt hC₀pos⟩ (fun x : Rn n => N x) :=
    by
      -- Use the characterisation of Lipschitz maps in terms of distances
      refine (lipschitzWith_iff_dist_le_mul).2 ?_
      intro x y
      -- Reverse triangle inequality again:
      -- |N x - N y| ≤ N (x - y)
      have h1 : |N x - N y| ≤ N (x - y) := by
        exact Norms.reverse_triangle_ineq x y N
      -- Upper bound on the seminorm:
      -- N (x - y) ≤ C₀ * ‖x - y‖
      have h2 : N (x - y) ≤ C₀ * ‖x - y‖ := by
        exact hBound (x - y)
      -- Rewrite distances using:
      --   dist_eq_norm : dist x y = ‖x - y‖
      --   Real.dist_eq : dist a b = |a - b|
      -- to match the Lipschitz inequality format
      simpa [Real.dist_eq, dist_eq_norm] using (le_trans h1 h2)
    -- Lipschitz maps between metric spaces are continuous
    exact hLip.continuous

end Norms
