--import Mathlib -- refine imports later
import Mathlib.Data.Set.Defs
import Mathlib.Order.SetNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Set.Basic

set_option linter.style.longLine false

namespace Covers

variable {X : Type} {ι : Type u} {U : ι → Set X}

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

end Covers
