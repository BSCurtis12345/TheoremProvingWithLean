import Mathlib.Analysis.Real.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

import TheoremProvingWithLean.Topology.CompactImage
import TheoremProvingWithLean.Topology.CompactClosed

namespace EVT

abbrev Rn (n : ℕ) := Fin n → ℝ

theorem extreme_value_theorem_min
  (n : ℕ)
  (s : Set (Rn n))
  (f : Rn n → ℝ)
  (hs : IsCompact s)
  (hf : Continuous f) :
  ∃ x ∈ s, ∀ y ∈ s, f y ≥ f x :=
  by
    classical

    ------------------------------------------------------------------
    -- Step 1: continuous image of a compact set is compact (your lemma)
    ------------------------------------------------------------------
    have hImgCompact : IsCompact (f '' s) :=
      continuous_image_compact_def hs hf

    ------------------------------------------------------------------
    -- Step 2: Heine–Borel consequence:
    -- compact subsets of ℝ are closed
    ------------------------------------------------------------------
    have hImgClosed : IsClosed (f '' s) :=
      compact_isClosed hImgCompact

    ------------------------------------------------------------------
    -- Step 3: compact subsets of ℝ are bounded below
    ------------------------------------------------------------------
    have hImgBddBelow : BddBelow (f '' s) :=
      hImgCompact.bddBelow

    ------------------------------------------------------------------
    -- Step 4: non-emptiness (from compactness of s)
    ------------------------------------------------------------------
    obtain ⟨x₀, hx₀⟩ := hs.nonempty
    have hNonempty : (f '' s).Nonempty :=
      ⟨f x₀, ⟨x₀, hx₀, rfl⟩⟩

    ------------------------------------------------------------------
    -- Step 5: define the minimum value
    ------------------------------------------------------------------
    let m := sInf (f '' s)

    ------------------------------------------------------------------
    -- Step 6: closed + bounded ⇒ infimum is attained
    ------------------------------------------------------------------
    have hm_mem : m ∈ f '' s :=
      hImgClosed.mem_of_inf_mem hNonempty hImgBddBelow

    ------------------------------------------------------------------
    -- Step 7: pull minimiser back to s
    ------------------------------------------------------------------
    rcases hm_mem with ⟨x, hxS, hfx⟩
    refine ⟨x, hxS, ?_⟩

    ------------------------------------------------------------------
    -- Step 8: minimality
    ------------------------------------------------------------------
    intro y hy
    have : m ≤ f y :=
      csInf_le hImgBddBelow ⟨y, hy, rfl⟩
    linarith


end EVT

#check EVT.extreme_value_theorem_min
