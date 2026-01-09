import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Order.Interval.Set.Defs

lemma exists_Ioo_sub_open {U : Set ℝ} {x : ℝ} (hUopen : IsOpen U) (hx : x ∈ U) :
  ∃ ε > 0, Set.Ioo (x-ε) (x+ε) ⊆ U := by
/-
Uses from mathlib: isOpen_iff_mem_nhds, Metric.mem_nhds_iff, Real.ball_eq_Ioo
Real.ball_eq_Ioo is fine as (x-ε,x+ε) & B(x,ε) are definitially equivalent anyway
!! isOpen_iff_mem_nhds & Metric.mem_nhds_iff could both be formalised if time-permitting
-/
  have : U ∈ nhds x := (isOpen_iff_mem_nhds.mp hUopen) x hx
  rw [Metric.mem_nhds_iff] at this
  obtain ⟨ε, hεpos, hball⟩ := this
  rw [Real.ball_eq_Ioo] at hball
  exact ⟨ε, hεpos, hball⟩
  done
