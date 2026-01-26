--import mathlib
import Mathlib.Data.Finset.Option
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Ring.Real

import TheoremProvingWithLean.Topology.Compact
import TheoremProvingWithLean.Topology.HeineBorel

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

  -- define g = -f
  let g : Rn n → ℝ := fun x => -f x
  have hg_cont : Continuous g := hf.neg

  -- image of compact set is compact, imported from Topology.Compact.ContinuousImageCompact
  have hcomp : IsCompact (g '' s) :=
    continuous_image_compact_def hs hg_cont

  -- compact subset of R is closed and bounded using lemmas from Compact.lean and HeineBorel.lean
  have hclosed : IsClosed (g '' s) := by
    exact compact_implies_closed (K := (g '' s)) hcomp


  have hbounded : BddAbove (g '' s) := by
    rcases HeineBorel.compact_implies_bounded (s := (g '' s)) hcomp with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro x hx
    -- x ≤ |x| ≤ R
    exact le_trans (le_abs_self x) (hR x hx)

  have hne : (g '' s).Nonempty :=
    hs_nonempty.image g

  -- define the sup
  let m : ℝ := sSup (g '' s)

  -- supremum in the set
  have hm_mem : m ∈ g '' s :=
    hclosed.csSup_mem hne hbounded

  -- unpack x ∈ s
  rcases hm_mem with ⟨x, hx_s, hx_eq⟩

  -- show minimality
  refine ⟨x, hx_s, ?_⟩
  intro y hy_s

  -- y is in the image
  have hy : g y ∈ g '' s := ⟨y, hy_s, rfl⟩

  -- element <= supremum
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
