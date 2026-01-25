import mathlib
import TheoremProvingWithLean.Norms
import TheoremProvingWithLean.Topology.ProductSpaces
import TheoremProvingWithLean.Topology.HeineBorel
import TheoremProvingWithLean.UpperBound
import TheoremProvingWithLean.continuity
import TheoremProvingWithLean.EVT
import TheoremProvingWithLean.UpperBound
import TheoremProvingWithLean.Topology.Compact

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

namespace LowerBound

abbrev Rn (n : ℕ) := Fin n → ℝ
abbrev unit_Icc_pow (n : ℕ) := {x : Rn n | ∀ i, x i ∈ Set.Icc (-1) 1}
abbrev closed_ball_sup (n : ℕ) := {x : Rn n | ‖x‖ ≤ 1}
abbrev S_infinity (n : ℕ) := {x : Rn n | ‖x‖ = 1}

variable (n : ℕ)
set_option linter.unusedTactic false

lemma closed_ball_sup_eq_pow : closed_ball_sup n = unit_Icc_pow n := by
  /-
  This lemma proves that the closed unit ball w.r.t. the supremum norm in ℝⁿ is equal to [-1,1]ⁿ.
  -/
  ext x -- Prove by extensionality
  constructor
  · -- Assume x is in the closed ball
    intro hx
    simp [norm, nnnorm] at hx -- Unpack the definition of the ball and sup norm
    intro i -- Let i be an arbitrary natural < n

    -- Specialise hx for i, unpack definitions further using simp
    specialize hx i
    simp

    exact abs_le.mp hx -- Result follows precisely from the definition of the abs value
  · -- Assume x is in the interval to the nth power
    -- Unpack definitions of ball and norm and let i be arbitrary
    intro hx
    simp [norm, nnnorm]; intro i

    -- Unpack definition of power of interval, apply to i, conclude with converse to above
    simp at hx
    specialize hx i
    exact abs_le.mpr hx

  done

open HeineBorel

lemma IsCompact_closed_ball_sup : IsCompact (closed_ball_sup n) := by
  /-
  Proves that the closed unit ball in ℝⁿ w.r.t. the supremum norm is compact w.r.t. the product topology.
  -/
  rw [closed_ball_sup_eq_pow] -- Rewrite the closed ball as [-1,1]ⁿ
  apply IsCompact_pow_compact -- Use that a finite power of a compact set is compact theorem
  · exact IsCompact_Icc (-1) (1) (by simp) -- By theorem, [-1,1] is compact
  · use 0; simp -- 0 ∈ [-1,1] so [-1,1] is non-empty
  done

open Continuity

lemma IsCompact_closed_sphere_sup (hn : 0 < n) : IsCompact (S_infinity n) := by
  /-
  Proves that the unit sphere in ℝⁿ w.r.t. the supremum norm is compact.

  Notable Mathlib results used:
    • IsClosed.preimage :
        This states that the preimage under a continuous function of a closed set is closed.
        We use this for now as it is very close to definition of continuity.
        Time-permitting, this can be expanded to reduce dependence on Mathlib results further.
  -/

  -- First get that the sphere is a subset of the closed ball
  have hSub : S_infinity n ⊆ closed_ball_sup n := by
    intro x hx
    simp at hx
    simp [hx]

  -- Refine by isCompact_of_isClosed_subset from Compact file - remains to show that S_infinity is closed
  refine isCompact_of_isClosed_subset (IsCompact_closed_ball_sup n) ?_ hSub

  -- Get that S_infinity is the preimage of {1} under the sup norm ‖·‖
  have hPreimage : S_infinity n = (fun x : Rn n => ‖x‖) ⁻¹' {1} := by
    ext x
    constructor
    -- We prove by extensionality - in both cases the hypothesis and goal simplify to ‖x‖=1
    · intro hx
      simp at hx; simp [hx]
    · intro hx
      simp at hx; simp [hx]

  rw [hPreimage]

  -- We will get that S_infinity is closed given that it is the preimage of a closed set under a continuous function
  apply IsClosed.preimage

  · -- Prove that ‖·‖ is continuous:
    -- We will do this by using our lemma norm_continuous
    -- This works with seminorms with the added definiteness property, so we define a seminorm equivalent to ‖·‖
    have hdef : ∀ x : Rn n, ‖x‖ = 0 ↔ x = 0 := by simp
    let supNorm.toSeminorm (n : ℕ) : Seminorm ℝ (Rn n) :=
    { toFun := fun x => ‖x‖,
      map_zero' := by simp,
      smul' := by simp [norm_smul],
      add_le' := by simp [norm_add_le],
      neg' := by simp [norm_neg] }
    exact (norm_continuous n (supNorm.toSeminorm n) hdef hn)
  · -- Prove that {1} is closed
    simp

lemma hs_nonempty (n : ℕ) (h_dim : 0 < n) : (S_infinity n).Nonempty :=
by
  classical
  -- Pick x = (1, 1, ..., 1)
  let x : Rn n := fun _ => (1 : ℝ)
  -- Pick an index so we can evaluate a coordinate
  let i : Fin n := ⟨0, h_dim⟩
  -- Show that x ≠ (0, 0, ..., 0)
  have hx : x ≠ (0 : Rn n) :=
  by
    intro h
    -- Do this by showing the first coordinate isn't of x isnt 0 but the first coordinate of (0, ..., 0) is 0
    have hcoord : x i = 0 := by
      simpa using congrArg (fun f => f i) h
    have : (1 : ℝ) = 0 :=
    by
      simp [x] at hcoord
    exact one_ne_zero this
  -- Show that ‖x‖ ≠ 0 so we can divide by it
  have h : ‖x‖ ≠ 0 :=
  by
    exact norm_ne_zero_iff.mpr hx
  -- Let y be the normalised x (which is the same as x but lean is weird and doesn't just accept x)
  let y : Rn n := (‖x‖)⁻¹ • x
  -- Show that y is in S_infinity
  have hyS : y ∈ S_infinity n :=
  by
    simp [S_infinity, y, norm_smul, h]
  -- Show S_infinity is nonempty
  exact Set.nonempty_of_mem hyS



theorem Lower_Bound (n : ℕ) (N : Seminorm ℝ (Rn n))
  (h_def : ∀ x : Rn n, N x = 0 ↔ x = 0) (h_dim : 0 < n) :
  ∃ c > 0, ∀ x : Rn n, c * ‖x‖ ≤ N x :=
  by
    classical
    -- We will use compactness of the unit sphere (wrt the sup norm) and EVT to get a minimum of N on it
    have hS_compact : IsCompact (S_infinity n) :=
    by
      exact IsCompact_closed_sphere_sup (n := n) h_dim
    -- The seminorm N is continuous as a function Rn n → ℝ
    have hN_cont : Continuous (fun x : Rn n => (N x : ℝ)) :=
    by
      exact Continuity.norm_continuous n N h_def h_dim
    -- Apply the extreme value theorem (minimum form) to get the value of x0 that minimises N on S_infinity
    have hmin : ∃ x0 ∈ S_infinity n, ∀ y ∈ S_infinity n, N x0 ≤ N y :=
    by
      exact EVT.extreme_value_theorem_min n (S_infinity n) N hS_compact (hs_nonempty n h_dim) hN_cont
    -- Unpack the value of x0 and its properties
    rcases hmin with ⟨x0, hx0S, hx0min⟩
    -- Show x0 ≠ 0, (On S_infinity n, the norm is 1, so it can't be the zero vector)
    have hx0_ne0 : x0 ≠ 0 :=
    by
      have definiteness : ‖x0‖ = (1 : ℝ) :=
      by
        exact hx0S
      exact (norm_ne_zero_iff).1 (by simp [definiteness])
    -- Show N x0 ≠ 0: if N x0 = 0 then by definiteness of the seminorm, x0 = 0
    have hNx0_ne0 : N x0 ≠ 0 :=
    by
      intro hzero
      have : x0 = 0 := (h_def x0).1 hzero
      exact hx0_ne0 this
    -- Deduce 0 < N x0 using nonnegativity of seminorms and N x0 ≠ 0
    have hNx0_pos : 0 < N x0 :=
    by
      have hN_non_neg : 0 ≤ N x0 :=
      by
        exact UpperBound.Norm_Nonneg N x0
      exact Std.lt_of_le_of_ne hN_non_neg (id (Ne.symm hNx0_ne0))
    -- We will take c := N x0 (the minimum value on the unit sphere), which is strictly positive
    refine ⟨N x0, hNx0_pos, ?_⟩
    -- Introduce x in ℝⁿ
    intro x
    -- Split into the trivial case x = 0 and the nontrivial case x ≠ 0
    by_cases hx : x = 0
    · -- If x = 0, the inequality c * ‖x‖ ≤ N x is immediate by simp
      subst hx
      simp
    ·-- If x ≠ 0, then ‖x‖ > 0, so we can scale x onto the unit sphere
      have hxnorm_pos : 0 < ‖x‖ :=
      by
        exact norm_pos_iff.mpr hx
      -- Show ‖x‖ ≠ 0 for simplification later
      have hxnorm_ne0 : ‖x‖ ≠ (0 : ℝ) :=
      by
        exact ne_of_gt hxnorm_pos
      -- Define the normalised vector y = x / ‖x‖, i.e. y := (‖x‖)⁻¹ • x
      let y : Rn n := (‖x‖)⁻¹ • x
      -- Show that the normalised vector lies on the unit sphere S_infinity n
      have hyS : y ∈ S_infinity n :=
      by
        simp [S_infinity, y, norm_smul, hxnorm_ne0]
      -- Since x0 minimises N on the sphere, we get N x0 ≤ N y
      have hx0_le_Ny : N x0 ≤ N y :=
        hx0min y hyS
      -- Use homogeneity of the seminorm: N ((‖x‖)⁻¹ • x) = |(‖x‖)⁻¹| * N x
      have hNy : N y = |(‖x‖)⁻¹| * N x :=
      by
        simpa [y] using (N.smul' ((‖x‖)⁻¹) x)
      -- Rewrite N y and simplify |(‖x‖)⁻¹| to (‖x‖)⁻¹ (since ‖x‖ > 0).
      -- This gives the key inequality N x0 ≤ (‖x‖)⁻¹ * N x
      have hmain : N x0 ≤ (‖x‖)⁻¹ * N x :=
      by
        simpa [hNy, abs_of_pos (inv_pos.mpr hxnorm_pos)] using hx0_le_Ny
      -- Multiply both sides by ‖x‖ ≥ 0 to remove the inverse
      have hxnorm_nonneg : 0 ≤ ‖x‖ := le_of_lt hxnorm_pos
      -- Multiply the inequality by ‖x‖ on the left (allowed because ‖x‖ ≥ 0)
      have hmain' : ‖x‖ * N x0 ≤ ‖x‖ * ((‖x‖)⁻¹ * N x) :=
        mul_le_mul_of_nonneg_left hmain hxnorm_nonneg
      -- Simplify the right-hand side using ‖x‖ * (‖x‖)⁻¹ = 1 (since ‖x‖ ≠ 0),
      -- and commute/associate multiplication to end up with (N x0) * ‖x‖ ≤ N x.
      have : (N x0) * ‖x‖ ≤ N x :=
      by
        simpa [mul_assoc, hxnorm_ne0, mul_inv_cancel, mul_left_comm, mul_comm] using hmain'
      -- This is exactly the desired inequality with c = N x0
      exact this
end LowerBound
