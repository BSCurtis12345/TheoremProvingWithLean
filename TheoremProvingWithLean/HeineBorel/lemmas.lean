import Mathlib -- refine imports later

namespace Simple

lemma elt_in_cover_elt -- this may be an unnecessary lemma
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


lemma subset_Icc.bdd_above {a b : ℝ} {S : Set ℝ} (h : S ⊆ Set.Icc a b) : BddAbove S := by
/-
Proves that a subset of a closed interval in ℝ is bounded above.
-/
  refine ⟨b, fun x hx => ?_⟩
  have : x ∈ Set.Icc a b := h hx
  exact this.2

end Simple
