import Mathlib.Data.Set.Defs
import Mathlib.Order.SetNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Set.Basic

set_option linter.style.longLine false
set_option linter.flexible false

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
  obtain ⟨n, hn⟩ := hs -- Get a finite subcover of U covering S, indexed over n
  obtain ⟨m, hm⟩ := ht -- Get a finite subcover of U covering T, indexed over m
  classical
  let k := n ∪ m
  use k -- Take n ∪ m to be finite cover of S ∪ T
  apply Set.union_subset
  · -- S ⊆ the union over k
    intro x hx
    apply hn at hx
    simp; simp at hx
    obtain ⟨j, hj⟩ := hx
    use j
    exact And.intro (by simp [hj.1, k]) hj.2
  · -- T ⊆ the union over k
    intro x hx
    apply hm at hx
    simp; simp at hx
    obtain ⟨j, hj⟩ := hx
    use j
    exact And.intro (by simp [hj.1, k]) hj.2
  done

end Covers
