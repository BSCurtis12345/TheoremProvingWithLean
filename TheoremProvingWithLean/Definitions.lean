import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Normed.Module.Basic


/-
In this section we will define ℝ^n and a general norm on R^n.

We will use Leans understanding of ℝ and consider ℝ^n as an n tuple of ℝ.

Next we consider the function toFun (our norm), and add the parameters of a norm.

Finally we simplify the code so we can simply use N as our norm.
-/



abbrev Rn (n : ℕ) := Fin n → ℝ
variable {n : ℕ}


structure RnNorm (n : ℕ) where
  toFun : Rn n → ℝ
  nonneg : ∀ x : Rn n, 0 ≤ toFun x
  zero_iff : ∀ x : Rn n, toFun x = 0 ↔ x = 0
  homogeneity :
    ∀ (a : ℝ) (x : Rn n), toFun (a • x) = |a| * toFun x
  triangle :
    ∀ x y : Rn n, toFun (x + y) ≤ toFun x + toFun y


namespace RnNorm

instance (n : ℕ) : CoeFun (RnNorm n) (fun _ => Rn n → ℝ) where
  coe N := N.toFun

end RnNorm
