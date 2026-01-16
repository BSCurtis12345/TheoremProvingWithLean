import TheoremProvingWithLean.UpperBound
import TheoremProvingWithLean.Norms
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Basic

namespace Continuity
-- Coordinate definition of ℝⁿ as functions Fin n → ℝ
abbrev Rn (n : ℕ) := Fin n → ℝ

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
end Continuity
