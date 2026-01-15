import Mathlib
import TheoremProvingWithLean.Norms
import TheoremProvingWithLean.Topology.ProductSpaces
import TheoremProvingWithLean.Topology.HeineBorel

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev unit_Icc_pow (n : ℕ) := {x : Rn n | ∀ i, x i ∈ Set.Icc (-1) 1}
abbrev closed_ball_sup (n : ℕ) := {x : Rn n | ‖x‖ ≤ 1}

variable (n : ℕ)

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
  ∃ C > 0, ∀ x : Rn n, c * ‖x‖ ≤ N x :=
  by
    sorry
