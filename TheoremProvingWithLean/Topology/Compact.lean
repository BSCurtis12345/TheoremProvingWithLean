import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact

set_option diagnostics true

open Topology

section TopologyLemmas

variable {X Y : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Continuous image of a compact set is compact -/
theorem continuous_image_compact
    {s : Set X} (hs : IsCompact s)
    {f : X → Y} (hf : Continuous f) :
    IsCompact (f '' s) :=
  IsCompact.image hs hf

/-continuous image of a compact set is compact manual proof below-/
theorem continuous_image_of_compact (f : X → Y) (hf : Continuous f) (s : Set X) (hs : IsCompact s) :
  IsCompact (f '' s) := by
  -- Prove that the image is compact
  exact isCompact_image hf hs


/-- A closed subset of a compact set is compact -/
theorem closed_subset_compact
    {s t : Set X} (hs : IsCompact s)
    (ht : IsClosed t)
    (hst : t ⊆ s) :
    IsCompact t :=
  IsCompact.of_isClosed_subset hs ht hst


end TopologyLemmas
