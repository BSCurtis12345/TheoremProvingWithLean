import Mathlib
import TheoremProvingWithLean.Norms
import TheoremProvingWithLean.Topology.ProductSpaces
import TheoremProvingWithLean.Topology.HeineBorel
import TheoremProvingWithLean.UpperBound
import TheoremProvingWithLean.continuity
import TheoremProvingWithLean.EVT

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

namespace LowerBound

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev unit_Icc_pow (n : ℕ) := {x : Rn n | ∀ i, x i ∈ Set.Icc (-1) 1}
abbrev closed_ball_sup (n : ℕ) := {x : Rn n | ‖x‖ ≤ 1}
abbrev S_infinity (n : ℕ) := {x : Rn n | ‖x‖ = 1}

variable (n : ℕ)
set_option linter.unusedTactic false

lemma closed_ball_sup_eq_pow : closed_ball_sup n = unit_Icc_pow n := by
  /-
  This lemma proves that the closed unit ball w.r.t. the supremum norm in ℝⁿ is equal to [-1,1]ⁿ.
  -/
  ext x -- Prove by extensionality
  constructor
  · -- Assume x is in the closed ball
    intro hx
    simp [norm, nnnorm] at hx -- Unpack the definition of the ball and sup norm
    intro i -- Let i be an arbitrary natural < n

    -- Specialise hx for i, unpack definitions further using simp
    specialize hx i
    simp

    exact abs_le.mp hx -- Result follows precisely from the definition of the abs value
  · -- Assume x is in the interval to the nth power
    -- Unpack definitions of ball and norm and let i be arbitrary
    intro hx
    simp [norm, nnnorm]; intro i

    -- Unpack definition of power of interval, apply to i, conclude with converse to above
    simp at hx
    specialize hx i
    exact abs_le.mpr hx

  done

open HeineBorel

lemma IsCompact_closed_ball_sup : IsCompact (closed_ball_sup n) := by
  /-
  Proves that the closed unit ball in ℝⁿ w.r.t. the supremum norm is compact w.r.t. the product topology.
  -/
  rw [closed_ball_sup_eq_pow] -- Rewrite the closed ball as [-1,1]ⁿ
  apply IsCompact_pow_compact -- Use that a finite power of a compact set is compact theorem
  · exact IsCompact_Icc (-1) (1) (by simp) -- By theorem, [-1,1] is compact
  · use 0; simp -- 0 ∈ [-1,1] so [-1,1] is non-empty
  done


theorem Lower_Bound (n : ℕ) (N : Seminorm ℝ (Rn n))
  (h_def : ∀ x : Rn n, N x = 0 ↔ x = 0) (h_dim : 0 < n) :
  ∃ c > 0, ∀ x : Rn n, c * ‖x‖ ≤ N x :=
  by
    classical
    have hS_compact : IsCompact (S_infinity n) :=
    by
      sorry
    have hN_cont : Continuous (fun x : Rn n => (N x : ℝ)) :=
    by
      exact Continuity.norm_continuous n N h_def h_dim
    have hmin : ∃ x0 ∈ S_infinity n, ∀ y ∈ S_infinity n, N x0 ≤ N y :=
    by
      exact EVT.extreme_value_theorem_min n (S_infinity n) N hS_compact hN_cont
    rcases hmin with ⟨x0, hx0S, hx0min⟩
    have hx0_ne0 : x0 ≠ 0 :=
    by
      have definiteness : ‖x0‖ = (1 : ℝ) :=
      by
        exact hx0S
      exact (norm_ne_zero_iff).1 (by simp [definiteness])
    have hNx0_ne0 : N x0 ≠ 0 :=
    by
      intro hzero
      have : x0 = 0 := (h_def x0).1 hzero
      exact hx0_ne0 this
    have hNx0_pos : 0 < N x0 :=
    by
      have hN_non_neg : 0 ≤ N x0 :=
      by
        exact UpperBound.Norm_Nonneg N x0
      exact Std.lt_of_le_of_ne hN_non_neg (id (Ne.symm hNx0_ne0))
    refine ⟨N x0, hNx0_pos, ?_⟩
    intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · have hxnorm_pos : 0 < ‖x‖ :=
      by
        exact norm_pos_iff.mpr hx
      have hxnorm_ne0 : ‖x‖ ≠ (0 : ℝ) :=
      by
        exact ne_of_gt hxnorm_pos
      let y : Rn n := (‖x‖)⁻¹ • x
      have hyS : y ∈ S_infinity n :=
      by
        simp [S_infinity, y, norm_smul, hxnorm_ne0]
      have hx0_le_Ny : N x0 ≤ N y :=
        hx0min y hyS
      have hNy : N y = |(‖x‖)⁻¹| * N x :=
      by
        simpa [y] using (N.smul' ((‖x‖)⁻¹) x)
      have hmain : N x0 ≤ (‖x‖)⁻¹ * N x :=
      by
        simpa [hNy, abs_of_pos (inv_pos.mpr hxnorm_pos)] using hx0_le_Ny
      have hxnorm_nonneg : 0 ≤ ‖x‖ := le_of_lt hxnorm_pos
      have hmain' : ‖x‖ * N x0 ≤ ‖x‖ * ((‖x‖)⁻¹ * N x) :=
        mul_le_mul_of_nonneg_left hmain hxnorm_nonneg
      have : (N x0) * ‖x‖ ≤ N x :=
      by
        simpa [mul_assoc, hxnorm_ne0, mul_inv_cancel, mul_left_comm, mul_comm] using hmain'
      exact this

end LowerBound
