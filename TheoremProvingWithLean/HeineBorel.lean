import Mathlib -- will specify imports later

theorem Icc_Compact_R (a b : ℝ) (h : a ≤ b) : IsCompact (Set.Icc a b) := by
/-
This theorem proves that every (non-degenerate) closed interval in R is compact (with the usual topology).

Mathlib results used:
  • isCompact_iff_finite_subcover : proves that Mathlib definition for a compact set is equivalent to definition using open coverings
  • Set.mem_iUnion : proves that something is in a union iff it is in one of the sets the union is over. Happy to use without justification
-/
  rw [isCompact_iff_finite_subcover]
  intros I U hUopen hcover
  let A : Set ℝ := {x ∈ Set.Icc a b | ∃ (t : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t, U i}
  have haInA : a ∈ A := by
    simp [A] -- note: uses Set.mem_sep_iff, Set.mem_Icc

    constructor
    · exact h

    · have haCover : a ∈ ⋃ i, U i := by
        apply hcover
        simpa

      rw [Set.mem_iUnion] at haCover
      rcases haCover with ⟨j, hj⟩
      let J : Set I := {x | x=j}
      use J -- problem: switching to Finset



done
