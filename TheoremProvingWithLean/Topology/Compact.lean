import Mathlib.Data.Finset.Option
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences

open Set
open scoped Topology

set_option linter.style.emptyLine false
set_option linter.flexible false

namespace Compact

section Covers

variable {X : Type} {ι : Type u} {U : ι → Set X}

lemma in_elt_cover
  {S : Set X} (hcover : S ⊆ ⋃ i, U i) (s : X) (hs : s ∈ S) : ∃ i, s ∈ U i := by
  /-
  Proves that if s ∈ S ⊆ ∪ (i ∈ ι) U i, then ∃ i ∈ ι such that s ∈ U i.
  -/
  have hsCover : s ∈ ⋃ i, U i := by exact hcover hs
  rw [Set.mem_iUnion] at hsCover
  exact hsCover

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
    obtain ⟨j, hj⟩ := by simpa using hx
    simp; use j
    exact And.intro (by simp [hj.1, k]) hj.2
  · -- T ⊆ the union over k
    intro x hx
    apply hm at hx
    simp; simp at hx
    obtain ⟨j, hj⟩ := hx
    use j
    exact And.intro (by simp [hj.1, k]) hj.2

end Covers

universe u v w
variable {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
variable {s : Set α} {f : α → β}

theorem continuous_image_compact_def
    (hs : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := by
  classical
  -- prove compactness using the open-cover characterization
  refine isCompact_iff_finite_subcover.2 ?_
  intro (ι : Type v) (U : ι → Set β) hUopen hcover

  -- pull back the cover along f
  have hpreopen : ∀ i : ι, IsOpen (f ⁻¹' (U i)) := by
    intro i
    exact hf.isOpen_preimage _ (hUopen i)

  have hprecover : s ⊆ iUnion (fun i : ι => f ⁻¹' (U i)) := by
    intro x hx
    have : f x ∈ iUnion U := by
      apply hcover
      exact ⟨x, hx, rfl⟩
    rcases mem_iUnion.mp this with ⟨i, hfxUi⟩
    exact mem_iUnion.mpr ⟨i, hfxUi⟩

  rcases hs.elim_finite_subcover (fun i : ι => f ⁻¹' (U i)) hpreopen hprecover with ⟨t, ht⟩

  -- push forward the finite subcover
  refine ⟨t, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' := ht hx
  -- rewrite subtype into set union
  simpa [iUnion_subtype] using hx'

open Set
open scoped Topology

theorem isCompact_of_isClosed_subset
    {K S : Set α}
    (hK : IsCompact K)
    (hS : IsClosed S)
    (hSK : S ⊆ K) :
    IsCompact S := by
  classical

  -- open cover characterisation on S
  refine (@isCompact_iff_finite_subcover _ _ S).2 ?_
  intro ι U hUopen hcover

  -- extend the cover of S to a cover of K
  let V : Option ι → Set α
    | some i => U i
    | none   => Sᶜ

  have hVopen : ∀ i, IsOpen (V i) := by
    intro i; cases i with
    | some i => simpa using hUopen i
    | none =>
      change IsOpen Sᶜ
      simpa using hS.isOpen_compl

  have hVcover : K ⊆ ⋃ i, V i := by
    intro x hxK
    by_cases hxS : x ∈ S
    · rcases mem_iUnion.1 (hcover hxS) with ⟨i, hi⟩
      exact mem_iUnion.2 ⟨some i, hi⟩
    · exact mem_iUnion.2 ⟨none, hxS⟩

  -- compactness of K -> finite subcover
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover V hVopen hVcover

  refine ⟨t.eraseNone, ?_⟩
  intro x hxS

  have hxK : x ∈ K := hSK hxS
  have : x ∈ ⋃ i ∈ t, V i := ht hxK

  rcases mem_iUnion₂.1 this with ⟨i, hi, hxi⟩
  cases i with
  | none =>
      exact (hxi hxS).elim
  | some i =>
      refine mem_iUnion.2 ⟨i, mem_iUnion.2 ?_⟩
      exact ⟨by
        simpa [Finset.mem_eraseNone] using hi,
        hxi⟩

end Compact
