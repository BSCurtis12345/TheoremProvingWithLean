import Mathlib
import TheoremProvingWithLean.Norms

set_option linter.style.longLine false
set_option linter.flexible false

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev unit_Icc_pow (n : ℕ) := {x : Rn n | ∀ i, x i ∈ Set.Icc (-1) 1}
abbrev closed_ball_sup (n : ℕ) := {x : Rn n | ‖x‖ ≤ 1}

variable (n : ℕ)

#check (inferInstance : Norm (Rn n))

lemma closed_ball_sup_eq_pow : closed_ball_sup n = unit_Icc_pow n := by
  /-
  This lemma proves that the closed unit ball w.r.t. the supremum norm in ℝⁿ is equal to [-1,1]ⁿ.
  -/
  ext x
  constructor
  · intro hx
    simp [norm, nnnorm] at hx
    intro i
    specialize hx i
    simp
    replace hx : |x i| ≤ 1 := by simpa [hx]
    exact abs_le.mp hx
  · sorry

  done
