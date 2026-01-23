import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Option

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import TheoremProvingWithLean.Topology.Compact


import Mathlib



namespace EVT

abbrev Rn (n : ℕ) := Fin n → ℝ

theorem extreme_value_theorem_min
  (n : ℕ)
  (s : Set (Rn n))
  (f : Rn n → ℝ)
  (hs : IsCompact s)
  (hs_nonempty : s.Nonempty)
  (hf : Continuous f) :
  ∃ x ∈ s, ∀ y ∈ s, f y ≥ f x :=
by
  classical

  ----------------------------------------------------------------
  -- STEP 1: define g = -f
  ----------------------------------------------------------------
  let g : Rn n → ℝ := fun x => -f x
  have hg_cont : Continuous g := hf.neg

  ----------------------------------------------------------------
  -- STEP 2: image of compact set is compact (YOUR lemma)
  ----------------------------------------------------------------
  have hcomp : IsCompact (g '' s) :=
    continuous_image_compact_def hs hg_cont

  ----------------------------------------------------------------
  -- STEP 3: compact subset of ℝ is closed and bounded
  ----------------------------------------------------------------
  have hclosed : IsClosed (g '' s) := hcomp.isClosed
  have hbounded : BddAbove (g '' s) := hcomp.bddAbove

  --have hcb : IsClosed (g '' s) ∧ BddAbove (g '' s) :=
  --HeineBorel.compact_closed_bounded (g '' s) hcomp
  --have hclosed : IsClosed (g '' s) := hcb.1
  --have hbounded : BddAbove (g '' s) := hcb.2

  have hne : (g '' s).Nonempty :=
    hs_nonempty.image g

  ----------------------------------------------------------------
  -- STEP 4: define the supremum
  ----------------------------------------------------------------
  let m : ℝ := sSup (g '' s)

  ----------------------------------------------------------------
  -- STEP 5: supremum is IN the set (closedness!)
  ----------------------------------------------------------------
  have hm_mem : m ∈ g '' s :=
    hclosed.csSup_mem hne hbounded

  ----------------------------------------------------------------
  -- STEP 6: unpack the witness x ∈ s
  ----------------------------------------------------------------
  --rcases hm_mem with ⟨x, hx_s, rfl⟩
  rcases hm_mem with ⟨x, hx_s, hx_eq⟩

  ----------------------------------------------------------------
  -- STEP 7: show minimality
  ----------------------------------------------------------------
  refine ⟨x, hx_s, ?_⟩
  intro y hy_s

  -- y is in the image
  have hy : g y ∈ g '' s := ⟨y, hy_s, rfl⟩

  -- element ≤ supremum
  have hgy_le_sup : g y ≤ sSup (g '' s) :=
    le_csSup hbounded hy

  -- rewrite supremum as g x
  have hgy_le_gx : g y ≤ g x := by
    simpa [hx_eq] using hgy_le_sup

  -- translate back to f
  dsimp [g] at hgy_le_gx
  linarith


end EVT

#check EVT.extreme_value_theorem_min
