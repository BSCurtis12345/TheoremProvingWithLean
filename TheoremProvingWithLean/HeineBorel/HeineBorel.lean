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

  have haInA : a ∈ A := by
  -- Proves a ∈ A
    simp [A] -- note: uses Set.mem_sep_iff, Set.mem_Icc
    constructor
    · exact h
    · have ha : a ∈ Set.Icc a b := by simpa
      apply elt_in_cover_elt U hcover a at ha
      rcases ha with ⟨j, hj⟩
      let J : Finset I := {j}
      use J
      use j
      simp [J, hj]

  have hsup : sSup A ∈ Set.Icc a b := by
  -- Proves sup A ∈ [a,b]
    simp
    constructor
    · apply le_csSup
      apply subset_Icc.bdd_above hAsubIcc
      exact haInA
    · apply csSup_le
      · use a
      · intros y hy
        apply hAsubIcc at hy
        exact hy.2

  apply elt_in_cover_elt U hcover (sSup A) at hsup -- sup A ∈ U_j for some j
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
  have hunion : Set.Icc a x ∪ Set.Ioo (sSup A - ε) (sSup A + ε) = Set.Ico a (sSup A + ε) := by
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

    obtain ⟨t₁, ht₁⟩ := ht₁  -- inside the above proof probably need to obtain witnesses anyway so no need for the subproofs or this line
    obtain ⟨t₂, ht₂⟩ := ht₂



    let T : Finset I := t₁ ∪ t₂ -- why doesnt this work???
    --#check t₁
    --#check t₂
    --#check t₁ ∪ t₂

    --refine ⟨t₁ ∪ t₂, _⟩
