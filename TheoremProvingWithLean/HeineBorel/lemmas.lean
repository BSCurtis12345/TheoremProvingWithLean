import Mathlib -- refine imports later

set_option linter.style.longLine false
set_option linter.style.commandStart false
namespace Simple

lemma subset_Icc_bdd_above {a b : ℝ} {S : Set ℝ} (h : S ⊆ Set.Icc a b) : BddAbove S := by
/-
Proves that a subset of a closed interval in ℝ is bounded above.
-/
  refine ⟨b, fun x hx => ?_⟩
  have : x ∈ Set.Icc a b := h hx
  exact this.2
  done


lemma sup_subset_Icc_in_Icc {a b : ℝ} {S : Set ℝ} (hS : S.Nonempty) (hsub : S ⊆ Set.Icc a b) : sSup S ∈ Set.Icc a b := by
/-
Proves that if ∅ ≠ S ⊆ [a,b] non-degenerate, then sup S ∈ [a,b]
-/
  constructor
  · obtain ⟨x, hx⟩ := hS
    have : a ≤ x := (hsub hx).1
    apply le_csSup (subset_Icc_bdd_above hsub) at hx
    exact this.trans hx
  · rw [csSup_le_iff (subset_Icc_bdd_above hsub) hS]
    intros c hc; exact (hsub hc).2
  done


section FinCover
/-
This section is primarily concerned with lemmas regarding finitely coverable subsets of compact intervals.
-/

  variable {X : Type} {ι : Type u} {U : ι → Set X}

--def A {a b : ℝ} : Set ℝ :=
--  {x ∈ Set.Icc a b | ∃ (t : Finset ι), Set.Icc a x ⊆ ⋃ i ∈ t, U i}

  lemma in_elt_cover
    {S : Set X} (hcover : S ⊆ ⋃ i, U i) (s : X) (hs : s ∈ S) : ∃ i, s ∈ U i := by
  /-
  Proves that if s ∈ S ⊆ ∪ (i ∈ ι) U i, then ∃ i ∈ ι such that s ∈ U i.
  -/
    have hsCover : s ∈ ⋃ i, U i := by exact hcover hs
    rw [Set.mem_iUnion] at hsCover
    exact hsCover
    done

  lemma subset_fin_cover
    {S T : Set X}
    (hs : ∃ (n : Finset ι), S ⊆ ⋃ i ∈ n, U i) (ht : T ⊆ S) :
    ∃ (n : Finset ι), T ⊆ ⋃ i ∈ n, U i := by
    /-
    Proves that the subset of a finitely covered set is finitely covered.
    -/
    obtain ⟨n, hn⟩ := hs
    apply ht.trans at hn
    use n
    done

  lemma union_fin_cover
    {S T : Set X}
    (hs : ∃ (n : Finset ι), S ⊆ ⋃ i ∈ n, U i) (ht : ∃ (n : Finset ι), T ⊆ ⋃ i ∈ n, U i) :
    ∃ (n : Finset ι), S ∪ T ⊆ ⋃ i ∈ n, U i := by
    /-
    Proves that if two sets admit a finite subcover of a given cover U, then so does their union.
    -/
    obtain ⟨n, hn⟩ := hs
    obtain ⟨m, hm⟩ := ht
    classical
    let k := n ∪ m
    use k
    apply Set.union_subset
    · sorry
    · sorry
    -- This lemma currently unfinished as not majorly important in the grand scheme of the project - may return to later
    done

end FinCover


section Icc_finCover

  variable {ι : Type u} {U : ι → Set ℝ} {a b : ℝ}

  --def A : Set ℝ :=
  --  {x ∈ Set.Icc a b | ∃ (t : Finset ι), Set.Icc a x ⊆ ⋃ i ∈ t, U i}

  lemma lower_singleton_Icc_fin_cover
    (h : a ≤ b) (hUopen : ∀ (i : ι), IsOpen (U i)) (hcover : Set.Icc a b ⊆ ⋃ i, U i) :
    a ∈ {x ∈ Set.Icc a b | ∃ (t : Finset ι), Set.Icc a x ⊆ ⋃ i ∈ t, U i} := by
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


end Simple
