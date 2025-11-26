import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Module.Basic
import TheoremProvingWithLean.Definitions

open RnNorm

variable {n : ℕ}
variable (N : RnNorm n) (x : Rn n)

set_option linter.style.longLine false

/-
variable {K V : Type*} [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]
-/

lemma N_sub_swap (x y : Rn n) : N (y - x) = N (x - y) := by
  have h' : N (-(x - y)) = N (x - y) := by
    have h := N.homogeneity (-1) (x - y)
    simpa using h
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

theorem reverse_triangle_ineq (x y : Rn n) : |N x - N y| ≤ N (x - y) := by

  by_cases h : 0 ≤ N x - N y
  · apply abs_of_nonneg at h
    rw [h]
    -- Goal prive that N x + N y ≤ N(x + y), by using triangle inequality on x = (x - y) + y
    have hx: N x ≤ N (x - y) + N y := by
      have := N.triangle (x-y) y
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hx' : N x - N y ≤ N (x - y) := by
      exact (sub_le_iff_le_add).2 hx

    exact hx'

  · apply not_le.mp at h
    apply abs_of_neg at h
    simp at h
    rw [h]
    have hx: N y ≤ N (y - x) + N x := by
      have := N.triangle (y - x) x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hx' : N y - N x ≤ N (y - x) := by
      exact (sub_le_iff_le_add).2 hx

    have hx'' : N y - N x ≤ N (x - y) := by
      simpa [N_sub_swap] using hx'

    exact hx''
