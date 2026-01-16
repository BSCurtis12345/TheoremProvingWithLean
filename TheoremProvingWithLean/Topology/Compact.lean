import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Option

open Set
open scoped Topology

universe u v w
variable {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
variable {s : Set α} {f : α → β}

theorem continuous_image_compact_def
    (hs : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := by
  classical
  -- Prove compactness using the open-cover characterization
  refine isCompact_iff_finite_subcover.2 ?_
  intro (ι : Type v) (U : ι → Set β) hUopen hcover

  -- Pull back the cover along f
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

  -- KEY: use the eliminator from the docs (avoids the metavariable ι problem)
  rcases hs.elim_finite_subcover (fun i : ι => f ⁻¹' (U i)) hpreopen hprecover with ⟨t, ht⟩

  -- Push forward the finite subcover
  refine ⟨t, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' := ht hx
  -- rewrite subtype-union into set-coe union
  simpa [iUnion_subtype] using hx'

#check continuous_image_compact_def


open Set
open scoped Topology

variable {α : Type u} [TopologicalSpace α] [T2Space α]

theorem compact_isClosed
    {K : Set α} (hK : IsCompact K) : IsClosed K := by
  -- A set is closed if its complement is open
  -- The complement of a compact set is open in a Hausdorff space
  have h : IsClosed K := hK.isClosed
  exact h

-- We stop the expansion here.
-- In mathlib, the fact that compact subsets of Hausdorff spaces are closed
-- is already formalised as `IsCompact.isClosed`.
-- Re-deriving the open-cover / separation argument would require
-- substantial additional infrastructure (filters, finite subcovers, choice),
-- and is orthogonal to the goal of this development.

--“compact ⇒ complement open”
--“compact ⇒ contains cluster points”
--Those are internal to IsCompact.isClosed

#check compact_isClosed



open Set
open scoped Topology

universe u
variable {α : Type u} [TopologicalSpace α]

theorem isCompact_of_isClosed_subset
    {K S : Set α}
    (hK : IsCompact K)
    (hS : IsClosed S)
    (hSK : S ⊆ K) :
    IsCompact S := by
  classical

  -- Use the open-cover characterisation on S
  refine (@isCompact_iff_finite_subcover _ _ S).2 ?_
  intro ι U hUopen hcover

  -- Extend the cover of S to a cover of K
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
    ·
      rcases mem_iUnion.1 (hcover hxS) with ⟨i, hi⟩
      exact mem_iUnion.2 ⟨some i, hi⟩
    ·
      exact mem_iUnion.2 ⟨none, hxS⟩

  -- Compactness of K gives a finite subcover
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover V hVopen hVcover

  -- Remove `none` and restrict back to S
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

#check isCompact_of_isClosed_subset
