import Mathlib.Topology.Compactness.Compact
import TheoremProvingWithLean.Topology.Covers
import TheoremProvingWithLean.Topology.OpenSets

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

section Icc_basic

lemma subset_Icc_bdd_above {a b : ℝ} {S : Set ℝ} (h : S ⊆ Set.Icc a b) : BddAbove S := by
/-
Proves that a subset of a closed interval in ℝ is bounded above.
-/
  refine ⟨b, fun x hx => ?_⟩ -- Take b as a witness, let x ∈ S
  have : x ∈ Set.Icc a b := h hx -- x ∈ [a,b]
  exact this.2 -- x ≤ b by definition
  done

lemma sup_subset_in_Icc {a b : ℝ} {S : Set ℝ} (hS : S.Nonempty) (hsub : S ⊆ Set.Icc a b) : sSup S ∈ Set.Icc a b := by
/-
Proves that if ∅ ≠ S ⊆ [a,b], then sup S ∈ [a,b].
-/
  constructor
  · -- a ≤ sup S
    obtain ⟨x, hx⟩ := hS -- Let x ∈ S
    have : a ≤ x := (hsub hx).1 -- Then a ≤ x
    apply le_csSup (subset_Icc_bdd_above hsub) at hx -- x ≤ sup S
    exact this.trans hx -- Transitivity
  · -- sup S ≤ b - true iff every b₁ ∈ S has b₁ ≤ b
    rw [csSup_le_iff (subset_Icc_bdd_above hsub) hS]
    intros c hc; exact (hsub hc).2
  done

end Icc_basic


open Covers

section Icc_finCover

-- Let U be a family of sets indexed over ι, a, b ∈ ℝ
variable {ι : Type u} {U : ι → Set ℝ} {a b : ℝ}

lemma lower_singleton_Icc_fin_cover
  (h : a ≤ b) (hcover : Set.Icc a b ⊆ ⋃ i, U i) :
  a ∈ {x ∈ Set.Icc a b | ∃ (t : Finset ι), Set.Icc a x ⊆ ⋃ i ∈ t, U i} := by
  /-
  Proves that if [a,b] covered by U, then a ∈ {x ∈ [a,b] : [a,x] is covered by a finite subcover of U}.
  (Basically that the singleton {a} can be finitely covered but in the form we want for later).
  -/
  simp -- Unfold definition of the set
  constructor
  · exact h -- a ≤ b by assumption
  · -- ∃ a finite t in ι s.t. a ∈ Uᵢ for some i ∈ t
    -- a ∈ [a,b] covered by U, so a belongs to an element of U
    have ha : a ∈ Set.Icc a b := by simpa
    apply in_elt_cover hcover a at ha
    -- Choose as the finite t the singleton containing the index of the set containing a
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
-/
  rw [isCompact_iff_finite_subcover] -- Rewrite goal in terms of finite subcover definition

  intros I U hUopen hcover -- Let U be an open cover indexed over I

  by_cases ha_eq_b : a = b
  -- In the case that a=b, [a,b] = {a}, and a must belong to a cover element, say Uⱼ, so use {Uⱼ} as the finite subcover
  · have : ∃ j, a ∈ U j := Set.mem_iUnion.mp (hcover (by simpa using h))
    rcases this with ⟨j, hj⟩
    use {j}
    simpa [ha_eq_b] using hj

  -- In the case a ≠ b, then a < b
  replace h : a < b := lt_of_le_of_ne h ha_eq_b

  -- Let A = {x ∈ [a,b] : [a,x] is covered by a finite subcover of U}
  let A : Set ℝ := {x ∈ Set.Icc a b | ∃ (t : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t, U i}

  -- Get A ⊆ [a,b]; a ∈ A; sup A ∈ [a,b] for later convenience
  have hA : A ⊆ Set.Icc a b := by intros x hx; exact hx.1
  have ha : a ∈ A := by exact lower_singleton_Icc_fin_cover (le_of_lt h) hcover

  have hsup : sSup A ∈ Set.Icc a b := by exact sup_subset_in_Icc ⟨a, ha⟩ hA

  -- Get sup A ∈ U_i for some i, takes j as the witness to this
  apply in_elt_cover hcover (sSup A) at hsup
  rcases hsup with ⟨j, hj⟩

  -- Take an ε > 0 s.t. (sup A - ε, sup A + ε) ⊆ U_j

  have hδ : ∃ δ > 0, Set.Ioo (sSup A - δ) (sSup A + δ) ⊆ U j ∧ a ≤ sSup A - δ := by
    rcases exists_Ioo_sub_open (hUopen j) hj with ⟨ε, hε⟩
    have : ∃ j, a ∈ U j := Set.mem_iUnion.mp (hcover (by simpa using le_of_lt h))
    rcases this with ⟨k, hk⟩
    rcases exists_Ioo_sub_open (hUopen k) hk with ⟨ε', hε'⟩
    let δ := min (min ((b-a)/2) (ε/2)) (ε'/2)
    have : δ > 0 ∧ δ < ε ∧ δ < ε' := by simp [δ, hε.1, h, hε'.1]
    have hδ' : a + δ ∈ A := by
      simp [A]
      constructor
      · refine And.intro (le_of_lt this.1) ?_
        have : a+((b-a)/2) ≤ b := by
          have h' : (b - a) / 2 ≤ b - a :=
            half_le_self (le_of_lt (sub_pos.mpr h))
          have := add_le_add_left h' a
          simpa [add_comm, add_left_comm, add_assoc, add_sub_cancel] using this
        apply ge_trans this
        simp [δ]
      · use {k}
        simp
        refine subset_trans ?_ hε'.2
        intro x hx -- could make this a separate
        simp; simp at hx
        refine And.intro (lt_of_lt_of_le ((sub_lt_self a) hε'.1) hx.1) ?_
        exact lt_of_le_of_lt hx.2 (add_lt_add_right this.2.2 a)

    use δ
    refine And.intro this.1 ?_
    constructor
    · refine subset_trans ?_ hε.2
      intro x hx; simp; simp at hx -- same as above - could make separate lemma
      refine And.intro (lt_trans (sub_lt_sub_left this.2.1 (sSup A)) hx.1) ?_
      exact lt_trans hx.2 (add_lt_add_right this.2.1 (sSup A))
    · rw [le_sub_iff_add_le]
      exact le_csSup (subset_Icc_bdd_above hA) hδ'

  rcases hδ with ⟨ε,hε⟩

  have hfinCoverε : ∃ (t : Finset I), Set.Ico a (sSup A + ε) ⊆ ⋃ i ∈ t, U i := by
  -- Proves that [a, sup A + ε) is finitely coverable
    have hx : ∃ x ∈ A, (sSup A - ε) < x := by
    -- Proves there is an x > sup A - ε in A
      apply exists_lt_of_lt_csSup
      · use a
      · simp [hε]

    -- Take x as a witness of the above
    rcases hx with ⟨x, hx⟩

    have hunion : Set.Icc a x ∪ Set.Ioo (sSup A - ε) (sSup A + ε) = Set.Ico a (sSup A + ε) := by -- could make this a lemma
    -- Proves [a,x] ∪ (sup A - ε, sup A + ε) = [a, sup A + ε)
      ext y; constructor -- By extensionality
      · intro hy
        simp; simp at hy
        cases hy with
        | inl hy₁ =>  -- x ∈ A => x ≤ sup A => y ≤ x < sup A + ε
          refine And.intro hy₁.1 ?_
          apply lt_of_le_of_lt hy₁.2
          refine lt_of_le_of_lt (le_csSup (subset_Icc_bdd_above hA) hx.1) ?_
          simp [hε.1]
        | inr hy₂ =>
          refine And.intro ?_ hy₂.2
          have ha_le : a ≤ sSup A :=
            le_csSup (subset_Icc_bdd_above hA) ha
          exact le_trans hε.2.2 (le_of_lt hy₂.1)

      · intro hy
        simp; simp at hy
        by_cases hy' : sSup A - ε < y
        · right; exact And.intro hy' hy.2
        · simp at hy'; left
          exact And.intro hy.1 (le_trans hy' (le_of_lt hx.2))

       -- do this later
    rw [← hunion]

    have ht₁ : ∃ (t₁ : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t₁, U i := hx.1.2
    -- [a,x] is finitely coverable by definition of A
    have ht₂ : ∃ (t₂ : Finset I), Set.Ioo (sSup A - ε) (sSup A + ε) ⊆ ⋃ i ∈ t₂, U i := by
      let J : Finset I := {j}
      use J
      intros y hy
      apply hε.2.1 at hy
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
        simp [le_of_lt h, this]
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
      rw [← csSup_Icc (le_of_lt h)]
      exact csSup_le_csSup bddAbove_Icc ⟨a, ha⟩ hA
      -- Clearly sup A ≤ b

  rw [hsupEqb] at hfinCoverε
  have : b < b + ε := by simp [hε]
  exact subset_fin_cover hfinCoverε (Set.Icc_subset_Ico_right this)
  -- Now [a,b+ε) is finitely coverable, hence so must be [a,b]
  done
