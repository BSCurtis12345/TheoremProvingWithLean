import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Option

open Set
open scoped Topology

set_option linter.style.emptyLine false

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

#check continuous_image_compact_def


open Set
open scoped Topology

variable {α : Type u} [TopologicalSpace α] [T2Space α]

theorem compact_implies_closed
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


/-
theorem compact_isClosed_notfromMathlib
--proof in a hausdorff space K (we prove for R specifically) then compact set in K implies closed without using hk.isClosed
    {K : Set α} (hK : IsCompact K) : IsClosed K := by
  -- A set is closed if its complement is open
  -- We will show that for any point x not in K, there is an open neighborhood around x that does not intersect K
  have h : IsClosed K := by
    rw [isClosed_iff_nhds]
    intro x hxKc
    -- For each point y in K, we can find disjoint open neighborhoods around x and y
    let U := ⋃ (y ∈ K), (nhds x).filter (fun V => V ∩ (nhds y).nonempty)
    have hUopen : IsOpen U := isOpen_iUnion fun y hy => isOpen_filter

    -- Show that U does not intersect K
    have hUcapK : U ∩ K = ∅ := by
      intro z hz
      rcases mem_iUnion.1 hz.1 with ⟨y, hyK, hzy⟩
      rcases mem_filter.1 hzy with ⟨V, hVx, hVy⟩
      have : z ∈ V := hVy.some_spec
      have : z ∈ K := hz.2
      -- This contradicts the disjointness of neighborhoods around x and y
      exact (hVx.some_spec ∩ hVy.some_spec).elim

    -- Thus, U is an open neighborhood of x that does not intersect K
    exact ⟨U, hUopen, by simp [hUcapK]⟩

  exact h
-/


open Set
open scoped Topology

variable {α : Type u} [TopologicalSpace α]

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
    ·
      rcases mem_iUnion.1 (hcover hxS) with ⟨i, hi⟩
      exact mem_iUnion.2 ⟨some i, hi⟩
    ·
      exact mem_iUnion.2 ⟨none, hxS⟩

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

#check isCompact_of_isClosed_subset
