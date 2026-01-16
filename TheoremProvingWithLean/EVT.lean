import mathlib

abbrev Rn (n : ℕ) := Fin n → ℝ

theorem extreme_value_theorem_max
  (n : ℕ)
  (s : Set (Rn n))
  (f : Rn n → ℝ)
  (hs : IsCompact s)
  (hf : Continuous f) :
  ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  by
    sorry
