import TheoremProvingWithLean.UpperBound
import TheoremProvingWithLean.Norms
import mathlib

abbrev Rn (n : ℕ) := Fin n → ℝ

lemma seminorm_continuous (n : ℕ) (N : Seminorm ℝ (Rn n))
  (h_def : ∀ x : Rn n, N x = 0 ↔ x = 0) (h_dim : 0 < n) :
  Continuous (fun x : Rn n => N x) :=
  by
    have h : ∃ (C : ℝ), ∀ (x y : Rn n), |N x - N y| ≤ C * ‖x - y‖ :=
    by
      rcases UpperBound.Upper_Bound n N h_def h_dim with ⟨C, hCpos, hBound⟩
      refine ⟨C, ?_⟩
      intro x y
      have h1 : |N x - N y| ≤ N (x - y) := by
        exact Norms.reverse_triangle_ineq x y N
      have h2 : N (x - y) ≤ C * ‖x - y‖ := by
        exact hBound (x - y)
      exact le_trans h1 h2
    rcases h with ⟨C, hC⟩
    rcases UpperBound.Upper_Bound n N h_def h_dim with ⟨C₀, hC₀pos, hBound⟩
    have hLip : LipschitzWith ⟨C₀, le_of_lt hC₀pos⟩ (fun x : Rn n => N x) :=
    by
      refine (lipschitzWith_iff_dist_le_mul).2 ?_
      intro x y
      have h1 : |N x - N y| ≤ N (x - y) := by
        exact Norms.reverse_triangle_ineq x y N
      have h2 : N (x - y) ≤ C₀ * ‖x - y‖ := by
        exact hBound (x - y)
      simpa [Real.dist_eq, dist_eq_norm] using (le_trans h1 h2)
    exact hLip.continuous
