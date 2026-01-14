import mathlib
import TheoremProvingWithLean.UpperBound

-- Definition of ℝⁿ as functions Fin n → ℝ
abbrev Rn (n : ℕ) := Fin n → ℝ

-- Main theorem: any two norms on Rn are equivalent.
-- We use lean's Seminorm with the added property of definiteness (N x = 0 ↔ x = 0)
theorem All_Norms_On_Rn_Equivalent
  (n : ℕ) (N M : Seminorm ℝ (Rn n))
  (h_def_N : ∀ x : Rn n, N x = 0 ↔ x = 0)
  (h_def_M : ∀ x : Rn n, M x = 0 ↔ x = 0)
  (h_dim  : n > 0) :
  (∃ c C : ℝ, C > c ∧ c > 0 ∧ ∀x, c * N x ≤ M x ∧ M x ≤ C * N x) :=
  by
    classical
    --------------------------------------------------------------------
    -- Take that every norm is equivalent to the supremum norm
    -- The upper bounds come from `UpperBound.Upper_Bound` lemma:
    -- ∃ C>0, ∀x, N x ≤ C * ‖x‖
    --------------------------------------------------------------------
    have h1 : (∃ C > 0, ∀ x : Rn n, N x ≤ C * ‖x‖) :=
    by
      simpa using (UpperBound.Upper_Bound (n := n) (N := N) h_def_N h_dim)
    have h2 : (∃ C > 0, ∀ x : Rn n, M x ≤ C * ‖x‖) :=
    by
      simpa using (UpperBound.Upper_Bound (n := n) (N := M) h_def_M h_dim)
    --------------------------------------------------------------------
    -- The lower bounds: TO BE PROVED
    -- ∃ c>0, ∀x, N x ≥ c * ‖x‖   and similarly for M.
    --------------------------------------------------------------------
    have h3 : (∃ c > 0, ∀ x : Rn n, N x ≥ c * ‖x‖) :=
    by
      sorry
    have h4 : (∃ c > 0, ∀ x : Rn n, M x ≥ c * ‖x‖) :=
    by
      sorry
    --------------------------------------------------------------------
    -- Converting to the following form
    -- (1/C) * N x ≤ ‖x‖
    --------------------------------------------------------------------
    have h5 : (∃ C > 0, ∀ x : Rn n, 1/C * N x ≤ ‖x‖) :=
    by
      -- Choose the constant C coming from the upper bound for N
      rcases h1 with ⟨C, hCpos, hNle⟩
      refine ⟨C, hCpos, ?_⟩
      intro x
      -- Start from the inequality given by the UpperBound lemma
      have hx : N x ≤ C * ‖x‖ := hNle x
      -- Proving C ≠ 0 so we can divide by C
      have hCne : C ≠ 0 := ne_of_gt hCpos
      -- Multiply the inequality by (1/C) on the left (1/C ≥ 0)
      have hx' : (1/C) * N x ≤ (1/C) * (C * ‖x‖) :=
        mul_le_mul_of_nonneg_left hx (le_of_lt (one_div_pos.2 hCpos))
      -- Simplify the right-hand side: (1/C) * (C * ‖x‖) = ‖x‖
      have rhs : C⁻¹ * (C * ‖x‖) = ‖x‖ := by
        simpa [mul_assoc] using (inv_mul_cancel_left₀ hCne ‖x‖)
      -- Replace the RHS using `rhs`
      simpa [rhs] using hx'
    --------------------------------------------------------------------
    -- Converting lower bound h4 for M into
    -- (1/c) * M x ≥ ‖x‖
    --------------------------------------------------------------------
    have h6 : (∃ c > 0, ∀ x : Rn n, (1 / c) * M x ≥ ‖x‖) :=
    by
      -- Use the constant c coming from the lower bound for M
      rcases h4 with ⟨c, hcpos, hMle⟩
      refine ⟨c, hcpos, ?_⟩
      intro x
      -- Start from the inequality given by the lower bound for M
      have hx : M x ≥ c * ‖x‖ := hMle x
      -- Proving c ≠ 0 so we can divide by it
      have hcne : c ≠ 0 := ne_of_gt hcpos
      -- Multiply both sides by (1/c) on the left, 1/c > 0
      have hx' : 1 / c * (c * ‖x‖) ≤ 1 / c * M x :=
        mul_le_mul_of_nonneg_left hx (le_of_lt (one_div_pos.2 hcpos))
      -- Simplify (1/c) * (c * ‖x‖) = ‖x‖
      have rhs : c⁻¹ * (c * ‖x‖) = ‖x‖ := by
        simpa [mul_assoc] using (inv_mul_cancel_left₀ hcne ‖x‖)
      -- Rewrite with rhs
      simpa [rhs] using hx'

    --------------------------------------------------------------------
    -- Combine h5 and h6 to relate N and M:
    -- (1/C) N x ≤ ‖x‖ ≤ (1/c) M x,
    --------------------------------------------------------------------
    have h7 : (∃c > 0, ∃C > 0, ∀x : Rn n, (1/C) * N x ≤ (1/c) * M x) :=
    by
      rcases h5 with ⟨C, hCpos, h5x⟩
      rcases h6 with ⟨c, hcpos, h6x⟩
      refine ⟨c, hcpos, C, hCpos, ?_⟩
      intro x
      -- First inequality: (1/C)N x ≤ ‖x‖
      have hx1 : (1 / C) * N x ≤ ‖x‖ := h5x x
      -- Second inequality: ‖x‖ ≤ (1/c)M x (Rewrite inequality the other way round using `linarith`)
      have hx2 : ‖x‖ ≤ (1 / c) * M x :=
      by
        linarith [h6x x]
      -- Chain them together
      exact le_trans hx1 hx2
    --------------------------------------------------------------------
    -- The next step is showing there exists c < C with
    -- (1/c) M x ≤ ‖x‖ ≤ (1/C) N x,
    -- This is the exact same process as proving the other direction
    -- This step is showing that 1/C * N x ≥ ‖x‖
    --------------------------------------------------------------------
    have h8 : (∃ C > 0, ∀ x : Rn n, 1/C * N x ≥ ‖x‖) :=
    by
      rcases h3 with ⟨C, hCpos, hNle⟩
      refine ⟨C, hCpos, ?_⟩
      intro x
      -- Start from the inequality given by the lower bound for N
      have hx : N x ≥ C * ‖x‖ := hNle x
      -- We need C ≠ 0 for inverse simplification
      have hCne : C ≠ 0 := ne_of_gt hCpos
      -- Dividing by C
      have hx' : (1/C) * N x ≥ (1/C) * (C * ‖x‖) :=
        mul_le_mul_of_nonneg_left hx (le_of_lt (one_div_pos.2 hCpos))
      -- Simplifying
      have rhs : C⁻¹ * (C * ‖x‖) = ‖x‖ := by
        simpa [mul_assoc] using (inv_mul_cancel_left₀ hCne ‖x‖)
      -- Rewriting
      simpa [rhs] using hx'
    --------------------------------------------------------------------
    -- Start from M x ≤ c‖x‖ and showing (1 / c) * M x ≤ ‖x‖
    --------------------------------------------------------------------
    have h9 : (∃ c > 0, ∀ x : Rn n, (1 / c) * M x ≤ ‖x‖) :=
    by
      rcases h2 with ⟨c, hcpos, hMle⟩
      refine ⟨c, hcpos, ?_⟩
      intro x
      -- Start from the inequality given by the UpperBound lemma for M
      have hx : M x ≤ c * ‖x‖ := hMle x
      -- Need c ≠ 0
      have hcne : c ≠ 0 := ne_of_gt hcpos
      -- Dividing by c
      have hx' : 1 / c * (c * ‖x‖) ≥ 1 / c * M x :=
        mul_le_mul_of_nonneg_left hx (le_of_lt (one_div_pos.2 hcpos))
      -- Simplifying
      have rhs : c⁻¹ * (c * ‖x‖) = ‖x‖ := by
        simpa [mul_assoc] using (inv_mul_cancel_left₀ hcne ‖x‖)
      -- Rewriting
      simpa [rhs] using hx'
    --------------------------------------------------------------------
    -- Combine h8 and h9 to get (1/c) M x ≤ (1/C) N x
    --------------------------------------------------------------------
    have h10 : (∃c > 0, ∃C > 0, ∀x : Rn n, (1/c) * M x ≤ (1/C) * N x) :=
    by
      rcases h8 with ⟨C, hCpos, h8x⟩
      rcases h9 with ⟨c, hcpos, h9x⟩
      refine ⟨c, hcpos, C, hCpos, ?_⟩
      intro x
      -- Second half: ‖x‖ ≤ (1/C) N x
      have hx1 : ‖x‖ ≤ (1 / C) * N x  := h8x x
      -- First half: (1/c) M x ≤ ‖x‖
      have hx2 : (1 / c) * M x ≤ ‖x‖ := h9x x
      -- Chain them together
      exact le_trans hx2 hx1
    --------------------------------------------------------------------
    -- Unpacking h7 and h10 - the two inequalities we need
    --------------------------------------------------------------------
    rcases h7 with ⟨c₁, hc₁pos, C₁, hC₁pos, h7x⟩
    rcases h10 with ⟨c₂, hc₂pos, C₂, hC₂pos, h10x⟩
    -- Showing all constants are non-zero (again)
    have hc₁ne : (c₁ : ℝ) ≠ 0 := ne_of_gt hc₁pos
    have hC₁ne : (C₁ : ℝ) ≠ 0 := ne_of_gt hC₁pos
    have hc₂ne : (c₂ : ℝ) ≠ 0 := ne_of_gt hc₂pos
    have hC₂ne : (C₂ : ℝ) ≠ 0 := ne_of_gt hC₂pos
    --------------------------------------------------------------------
    -- Defining the final constants
    -- We require C = C0 + c + 1 as c₂ / C₂ > c₁ / C₁ isn't necessarily true
    -- However we don't need C to be C = c₂ / C₂, we just need C > c and C >  and C > c₂ / C₂
    -- So C  := C0 + c + 1
    --------------------------------------------------------------------
    let c : ℝ := c₁ / C₁
    let C0 : ℝ := c₂ / C₂
    let C : ℝ := C0 + c + 1
    -- c > 0 as c₁, C₁ > 0
    have hcpos : c > 0 := by
      dsimp [c]
      exact div_pos hc₁pos hC₁pos
    -- C > c because C = C0 + c + 1 and C0, 1 > 0
    have hCgtc : C > c := by
      dsimp [C]
      linarith [div_pos hc₂pos hC₂pos]
    --------------------------------------------------------------------
    -- Derive the lower inequality c * N x ≤ M x
    --------------------------------------------------------------------
    have h_lower : ∀ x : Rn n, c * N x ≤ M x := by
      intro x
      have h := h7x x
      -- Multiply by c1
      have h' : c₁ * ((1 / C₁) * N x) ≤ c₁ * ((1 / c₁) * M x) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hc₁pos)
      -- Simplify
      simpa [c, one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hc₁ne] using h'
    --------------------------------------------------------------------
    -- Derive the preliminary upper inequality M x ≤ C0 * N x
    --------------------------------------------------------------------
    have h_upper0 : ∀ x : Rn n, M x ≤ C0 * N x := by
      intro x
      have h := h10x x
      -- Multiply by C2
      have h' : c₂ * (1 / c₂ * M x) ≤ c₂ * (1 / C₂ * N x) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hc₂pos)
      -- Simplify
      simpa [C0, one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hc₂ne] using h'
    --------------------------------------------------------------------
    -- Upgrade M x ≤ C0 * N x to M x ≤ C * N x using C ≥ C0 and N x ≥ 0
    --------------------------------------------------------------------
    have h_upper : ∀ x : Rn n, M x ≤ C * N x := by
      intro x
      -- Seminorms are nonnegative: 0 ≤ N x.
      have hNx : 0 ≤ N x :=
      by
        simp only [apply_nonneg]
      -- By construction, C0 ≤ C
      have hC0leC : C0 ≤ C := by
        dsimp [C]
        linarith
      -- Chain M x ≤ C0 * N x ≤ C * N x
      exact le_trans (h_upper0 x) (by
        -- Monotonicity of multiplication by nonnegative N x
        exact mul_le_mul_of_nonneg_right hC0leC hNx)
    --------------------------------------------------------------------
    -- Put everything into the final statemtent
    --------------------------------------------------------------------
    refine ⟨c, C, hCgtc, hcpos, ?_⟩
    intro x
    refine ⟨?_, ?_⟩
    · exact h_lower x
    · exact h_upper x
