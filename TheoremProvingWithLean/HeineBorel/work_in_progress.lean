import Mathlib -- will specify imports later
import TheoremProvingWithLean.HeineBorel.lemmas

open Simple

theorem Icc_Compact_R (a b : ℝ) (h : a ≤ b) : IsCompact (Set.Icc a b) := by
/-
This theorem proves that every (non-degenerate) closed interval in R is compact (with the usual topology).

Mathlib results used:
  • isCompact_iff_finite_subcover : proves that Mathlib definition for a compact set is equivalent to definition using open coverings
  • Set.mem_iUnion : proves that something is in a union iff it is in one of the sets the union is over. Happy to use without justification
-/
  rw [isCompact_iff_finite_subcover]

  -- Let {U_i} for i ∈ I be an open cover, A be the set of x's s.t. [a,x] has a finite subcover
  intros I U hUopen hcover
  let A : Set ℝ := {x ∈ Set.Icc a b | ∃ (t : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t, U i}

  have hAsubIcc : A ⊆ Set.Icc a b := by
  -- Proves A is a subset of [a,b] for later convenience
    intros x hx
    exact hx.1

  have haInA : a ∈ A := by exact lower_singleton_Icc_fin_cover h hUopen hcover
  have hsup : sSup A ∈ Set.Icc a b := by exact sup_subset_Icc_in_Icc ⟨a, haInA⟩ hAsubIcc

  apply in_elt_cover hcover (sSup A) at hsup

  rcases hsup with ⟨j, hj⟩
  have hcNhd : ∃ ε > 0, Set.Ioo (sSup A - ε) (sSup A + ε) ⊆ U j := by
  -- Proves there is an ε > 0 with (sup A - ε, sup A + ε) ⊆ U_j
    sorry -- show this later (from openness of U j)

  rcases hcNhd with ⟨ε, hε⟩

  have hx : ∃ x ∈ A, (sSup A - ε) < x := by
  -- Proves there is an x > sup A - ε in A
    apply exists_lt_of_lt_csSup
    · use a
    · simp [hε]
  rcases hx with ⟨x, hx⟩

  have hunion : Set.Icc a x ∪ Set.Ioo (sSup A - ε) (sSup A + ε) = Set.Ico a (sSup A + ε) := by -- this could be made a separate lemma
  -- Proves [a,x] ∪ (sup A - ε, sup A + ε) = [a, sup A + ε)
    sorry -- do this later

  have hfinCoverε : ∃ (t : Finset I), Set.Ico a (sSup A + ε) ⊆ ⋃ i ∈ t, U i := by
  -- Proves that [a, sup A + ε) is finitely coverable
    rw [← hunion]
    have ht₁ : ∃ (t₁ : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t₁, U i := by
      exact hx.1.2
    have ht₂ : ∃ (t₂ : Finset I), Set.Ioo (sSup A - ε) (sSup A + ε) ⊆ ⋃ i ∈ t₂, U i := by
      let J : Finset I := {j}
      use J
      intros y hy
      apply hε.2 at hy
      have : j ∈ J := by simp [J]
      exact Set.mem_biUnion this hy
    exact union_fin_cover ht₁ ht₂
