import Mathlib.Data.Finset.Basic

variable {I : Type} [DecidableEq I]

def exampledef (t₁ t₂ : Finset I) : Finset I :=
  t₁ ∪ t₂
