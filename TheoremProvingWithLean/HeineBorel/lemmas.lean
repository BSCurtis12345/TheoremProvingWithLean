import Mathlib -- refine imports later

namespace Simple

lemma subset_Icc.bdd_above {a b : ℝ} {S : Set ℝ} (h : S ⊆ Set.Icc a b) : BddAbove S := by
/-
Proves that a subset of a closed interval in ℝ is bounded above.
-/
  refine ⟨b, fun x hx => ?_⟩
  have : x ∈ Set.Icc a b := h hx
  exact this.2
  done


lemma elt_in_cover_elt
  {X : Type u} {S : Set X} {ι : Type u}
  (U : ι → Set X)
  (hcover : S ⊆ ⋃ i, U i)
  (s : X) (hs : s ∈ S) :
  ∃ i, s ∈ U i := by
/-
Proves that if s ∈ S ⊆ ∪ (i ∈ ι) U i, then ∃ i ∈ ι such that s ∈ U i.
-/
  have hsCover : s ∈ ⋃ i, U i := by -- this can definitely be made shorter
    apply hcover
    exact hs

  rw [Set.mem_iUnion] at hsCover
  exact hsCover
  done


--open scoped Classical
open Finset

lemma union_fin_cover_fin_cover
  {X : Type u} {S T : Set X} {ι : Type u} [DecidableEq ι] -- why should decidable ι be necessary here
  (U : ι → Set X)
  (hs : ∃ (n : Finset ι), S ⊆ ⋃ i ∈ n, U i) (ht : ∃ (n : Finset ι), T ⊆ ⋃ i ∈ n, U i) :
  ∃ (n : Finset ι), S ∪ T ⊆ ⋃ i ∈ n, U i := by
  /-
  Proves that if two sets admit a finite subcover of a given cover U, then so does their union.
  -/
  obtain ⟨n, hn⟩ := hs
  obtain ⟨m, hm⟩ := ht
  --classical
  let k := n ∪ m
  use k
  apply Set.union_subset
  · sorry
  · sorry

  done



end Simple
