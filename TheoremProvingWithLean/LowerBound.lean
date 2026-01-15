import Mathlib
import TheoremProvingWithLean.Norms

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev unit_Icc_pow (n : ℕ) := {x : Rn n | ∀ i, x i ∈ Set.Icc (-1) 1}
abbrev closed_ball_sup (n : ℕ) := {x : Rn n | ‖x‖ ≤ 1}

variable (n : ℕ)

#check (inferInstance : Norm (Rn n))

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
