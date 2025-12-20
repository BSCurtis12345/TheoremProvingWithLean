--import Mathlib -- will specify imports later
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Compactness.Compact
import TheoremProvingWithLean.Topology.Covers
import TheoremProvingWithLean.Topology.OpenSets

set_option linter.style.longLine false
set_option linter.flexible false

section Icc_basic

lemma subset_Icc_bdd_above {a b : ℝ} {S : Set ℝ} (h : S ⊆ Set.Icc a b) : BddAbove S := by
/-
Proves that a subset of a closed interval in ℝ is bounded above.
-/
  refine ⟨b, fun x hx => ?_⟩
  have : x ∈ Set.Icc a b := h hx
  exact this.2
  done

lemma sup_subset_in_Icc {a b : ℝ} {S : Set ℝ} (hS : S.Nonempty) (hsub : S ⊆ Set.Icc a b) : sSup S ∈ Set.Icc a b := by
/-
Proves that if ∅ ≠ S ⊆ [a,b] non-degenerate, then sup S ∈ [a,b].
-/
  constructor
  · obtain ⟨x, hx⟩ := hS
    have : a ≤ x := (hsub hx).1
    apply le_csSup (subset_Icc_bdd_above hsub) at hx
    exact this.trans hx
  · rw [csSup_le_iff (subset_Icc_bdd_above hsub) hS]
    intros c hc; exact (hsub hc).2
  done

end Icc_basic


open Covers

section Icc_finCover

variable {ι : Type u} {U : ι → Set ℝ} {a b : ℝ}

lemma lower_singleton_Icc_fin_cover
  (h : a ≤ b) (hcover : Set.Icc a b ⊆ ⋃ i, U i) :
  a ∈ {x ∈ Set.Icc a b | ∃ (t : Finset ι), Set.Icc a x ⊆ ⋃ i ∈ t, U i} := by
  /-
  Proves that if [a,b] covered by U, then a ∈ {x ∈ [a,b] : [a,x] is covered by a finite subcover of U}.
  (Basically that the singleton {a} can be finitely covered but in the form we want for later).
  -/
  simp
  constructor
  · exact h
  · have ha : a ∈ Set.Icc a b := by simpa
    apply in_elt_cover hcover a at ha
    rcases ha with ⟨j, hj⟩
    let J : Finset ι := {j}
    use J
    use j
    simp [J, hj]
  done

end Icc_finCover


theorem Icc_compact (a b : ℝ) (h : a ≤ b) : IsCompact (Set.Icc a b) := by
/-
This theorem proves that every (non-degenerate) closed interval in R is compact (with the usual topology).

Mathlib results used:
  • isCompact_iff_finite_subcover : proves that Mathlib definition for a compact set is equivalent to definition using open coverings
  • Set.mem_iUnion : proves that something is in a union iff it is in one of the sets the union is over. Happy to use without justification
-/
  rw [isCompact_iff_finite_subcover]

  intros I U hUopen hcover
  let A : Set ℝ := {x ∈ Set.Icc a b | ∃ (t : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t, U i}
  -- Let U = {U_i} for i ∈ I be an open cover, A = {x ∈ [a,b] : [a,x] is covered by a finite subcover of U}

  have hA : A ⊆ Set.Icc a b := by intros x hx; exact hx.1
  have ha : a ∈ A := by exact lower_singleton_Icc_fin_cover h hcover
  have hsup : sSup A ∈ Set.Icc a b := by exact sup_subset_in_Icc ⟨a, ha⟩ hA
  -- Proves A ⊆ [a,b]; a ∈ A; sup A ∈ [a,b] for later convenience

  apply in_elt_cover hcover (sSup A) at hsup
  rcases hsup with ⟨j, hj⟩
  -- Proves sup A ∈ U_i for some i, takes j as the witness to this

  rcases exists_Ioo_sub_open (hUopen j) hj with ⟨ε, hε⟩
  -- Takes an ε > 0 s.t. (sup A - ε, sup A + ε) ⊆ U_j

  have hfinCoverε : ∃ (t : Finset I), Set.Ico a (sSup A + ε) ⊆ ⋃ i ∈ t, U i := by
  -- Proves that [a, sup A + ε) is finitely coverable
    have hx : ∃ x ∈ A, (sSup A - ε) < x := by -- could make this a lemma
    -- Proves there is an x > sup A - ε in A
      apply exists_lt_of_lt_csSup
      · use a
      · simp [hε]

    rcases hx with ⟨x, hx⟩
    -- Takes a witness x of the above

    have hunion : Set.Icc a x ∪ Set.Ioo (sSup A - ε) (sSup A + ε) = Set.Ico a (sSup A + ε) := by -- could make this a lemma
    -- Proves [a,x] ∪ (sup A - ε, sup A + ε) = [a, sup A + ε)
      sorry -- do this later
    rw [← hunion]

    have ht₁ : ∃ (t₁ : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t₁, U i := hx.1.2
    -- [a,x] is finitely coverable by definition of A
    have ht₂ : ∃ (t₂ : Finset I), Set.Ioo (sSup A - ε) (sSup A + ε) ⊆ ⋃ i ∈ t₂, U i := by
      let J : Finset I := {j}
      use J
      intros y hy
      apply hε.2 at hy
      have : j ∈ J := by simp [J]
      exact Set.mem_biUnion this hy
    -- [sup A - ε, sup A + ε] is finitely coverable since it is a subset of U_j ∈ U

    exact union_fin_cover ht₁ ht₂

  have hsupEqb : (sSup A) = b := by
  -- Proves that sup A = b
    classical by_contra hneg;
    apply ne_iff_lt_or_gt.mp at hneg
    cases hneg with
    -- By contradiction: break in to less than and greater than cases

    | inl hl => -- Less than case

      have : min b (sSup A + ε/2) ∈ A := by
      -- Proves min{b, sup A + ε/2} ∈ A
        change min b (sSup A + ε/2) ∈ {x | x ∈ Set.Icc a b ∧ ∃ t, Set.Icc a x ⊆ ⋃ i ∈ t, U i}
        have : Set.Icc a (min b (sSup A + ε/2)) ⊆ Set.Ico a (sSup A + ε) := by
        -- Proves [a, min{...}] ⊆ [a, sup A + ε)
          have : (min b (sSup A + ε/2)) < sSup A + ε := by simp [hε.1]
          exact Set.Icc_subset_Ico_right this

        apply subset_fin_cover hfinCoverε at this
        -- Then [a, min{...}] is finitely coverable
        simp [h, this]
        have : a - ε/2 ≤ a := by apply le_of_lt; simp [hε]
        rw [← sub_le_iff_le_add]
        exact le_csSup_of_le (subset_Icc_bdd_above hA) ha this

      apply le_csSup (subset_Icc_bdd_above hA) at this
      simp at this
      cases this with
      | inl hl₁ => contrapose! hl; exact hl₁
      | inr hr₁ => contrapose! hr₁; simp [hε]
      -- We get then min{...} ≤ sup A so b ≤ sup A or ε/2 ≤ 0 : both yield contradictions

    | inr hr => -- Greater than case
      contrapose! hr
      rw [← csSup_Icc h]
      exact csSup_le_csSup bddAbove_Icc ⟨a, ha⟩ hA
      -- Clearly sup A ≤ b

  rw [hsupEqb] at hfinCoverε
  have : b < b + ε := by simp [hε]
  exact subset_fin_cover hfinCoverε (Set.Icc_subset_Ico_right this)
  -- Now [a,b+ε) is finitely coverable, hence so must be [a,b]
  done
