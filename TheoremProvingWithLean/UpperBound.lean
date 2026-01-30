import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Seminorm

-- Enable ∑ notation over finite types
open scoped BigOperators

namespace UpperBound

-- Definition of ℝⁿ as functions Fin n → ℝ
abbrev Rn (n : ℕ) := Fin n → ℝ

-- Definition of the standard basis vector eᵢ ∈ ℝⁿ
-- Pi.basisFun gives the function which is 1 at index i and 0 elsewhere
noncomputable def e (n : ℕ) (i : Fin n) : Rn n := Pi.basisFun ℝ (Fin n) i

-- Basic fact: a seminorm is always nonnegative
-- This follows from subadditivity applied to x + (-x)
lemma Norm_Nonneg {n : ℕ} (N : Seminorm ℝ (Rn n)) :
  ∀ x : Rn n, N x ≥ 0 :=
  by
    intro x
    -- Triangle inequality gives N(x + (-x)) ≤ N x + N (-x)
    have h := N.add_le' x (-x)
    -- Simplifies to 0 ≤ 2 * N x
    have h' : 0 ≤ 2 * N x :=
    by
      simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, apply_nonneg]
    -- Since 2 > 0, divide through to obtain N x ≥ 0
    have hpos2 : (0 : ℝ) < 2 := by norm_num
    exact nonneg_of_mul_nonneg_right h' hpos2

-- Any vector x ∈ ℝⁿ can be written as a finite linear combination
-- of standard basis vectors with coefficients x i
lemma Vector_As_Weighted_Sum_Of_Standard_Basis (n : ℕ) (x : Rn n) :
  x = ∑ i : Fin n, x i • (Pi.basisFun ℝ (Fin n) i) := by
  funext j
  -- Pointwise evaluation using properties of basisFun / single
  simp [Pi.basisFun, Pi.single_apply]

-- Finite version of subadditivity for seminorms:
-- the seminorm of a finite sum is bounded by the sum of seminorms
lemma Seminorm_sum_le_finite {n' : ℕ} (N : Seminorm ℝ (Rn n')) :
  ∀ n (Kn : Fin n → Rn n'),
    N (∑ i : Fin n, Kn i) ≤ ∑ i : Fin n, N (Kn i) :=
  by
    classical
    intro n
    induction n with
    | zero =>
      -- Trivial case: sum over empty type
      intro Kn
      simp
    | succ n ih =>
      intro Kn
      -- Apply triangle inequality to split off the first term
      have h1 :
        N (∑ (i : Fin (n+1)), Kn i) ≤ N (Kn 0) + N (∑ i : Fin n, Kn i.succ) := by
        have := N.add_le' (Kn 0) (∑ i : Fin n, Kn i.succ)
        simpa [Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] using this
      -- Induction hypothesis on the tail sum
      have h2 :
        N (∑ i : Fin n, Kn i.succ) ≤ ∑ i : Fin n, N (Kn i.succ) :=
        ih (fun i => Kn i.succ)
      -- Add N (Kn 0) to both sides
      have h2' :
        N (Kn 0) + N (∑ i : Fin n, Kn i.succ)
          ≤ N (Kn 0) + ∑ i : Fin n, N (Kn i.succ) := by
        have := add_le_add_right h2 (N (Kn 0))
        simpa [add_comm] using this
      -- Combine inequalities
      have h3 :
        N (∑ i : Fin (n+1), Kn i) ≤ N (Kn 0) + ∑ i : Fin n, N (Kn i.succ) :=
        le_trans h1 h2'
      simpa [Fin.sum_univ_succ] using h3

-- Homogeneity of a seminorm distributes over finite sums
-- N (xᵢ • eᵢ) = |xᵢ| * N (eᵢ)
lemma Finite_Norm_Homogeneity {n : ℕ} {n' : ℕ} (N : Seminorm ℝ (Rn n'))
  (x : Fin n → ℝ) (e : Fin n → Rn n') :
  ∑ i : Fin n, N (x i • e i) = ∑ i : Fin n, |x i| * N (e i) :=
  by
    classical
    have h_term :
      ∀ i : Fin n, N (x i • e i) = |x i| *  N (e i) :=
      by
        intro i
        -- Homogeneity of seminorms
        have := N.smul' (x i) (e i)
        simpa using this
    simp [h_term]

-- Each standard basis vector is nonzero
lemma e_ne_zero (n : ℕ) (i : Fin n) : e n i ≠ (0 : Rn n) := by
  classical
  intro h
  have hi := congrArg (fun f => f i) h
  -- Evaluating eᵢ at i gives 1
  have : (1 : ℝ) = 0 := by
    simp [e] at hi
  exact one_ne_zero this

-- Main result:
-- Any definite seminorm on ℝⁿ is bounded above by a constant times the norm
theorem Upper_Bound (n : ℕ) (N : Seminorm ℝ (Rn n))
  (h_def : ∀ x : Rn n, N x = 0 ↔ x = 0) (h_dim : 0 < n) :
  ∃ C > 0, ∀ x : Rn n, N x ≤ C * ‖x‖ := by
  classical
  -- Define the constant as the sum of seminorms of basis vectors
  let C : ℝ := ∑ i : Fin n, N (e n i)
  -- Show C > 0 using positivity of each term
  have C_Positive : 0 < C := by
    have inst_nonempty : Nonempty (Fin n) := ⟨⟨0, h_dim⟩⟩
    -- Each term is nonnegative
    have h_nonneg_terms : ∀ i : Fin n, 0 ≤ N (e n i) := by
      intro i
      exact Norm_Nonneg N (e n i)
    -- Each term is nonzero using definiteness
    have h_nonzero_terms : ∀ i : Fin n, N (e n i) ≠ 0 := by
      intro i
      have he_ne : e n i ≠ 0 := by
        exact e_ne_zero n i
      intro hN
      have he0 : e n i = 0 := (h_def (e n i)).1 hN
      exact he_ne he0
    -- Hence each term is strictly positive
    have h_positive_terms : ∀ i : Fin n, 0 < N (e n i) :=
    by
      exact fun i ↦ Std.lt_of_le_of_ne (h_nonneg_terms i)
        fun a ↦ h_nonzero_terms i (id (Eq.symm a))
    -- Sum of positive terms is positive
    apply Finset.sum_pos
    · intro i hi
      exact h_positive_terms i
    · exact Finset.univ_nonempty
  refine ⟨C, C_Positive, ?_⟩
  intro x
  -- Rewrite x in the standard basis expansion
  have hx : x = ∑ i : Fin n, x i • e n i :=
    Vector_As_Weighted_Sum_Of_Standard_Basis n x
  have hx' : N x  = N (∑ i : Fin n, x i • e n i) := by
    simpa using congrArg N hx
  rw [hx']
  -- Apply subadditivity over the finite sum
  have h_sum_le : N (∑ i, x i • e n i) ≤ ∑ i, N (x i • e n i) := by
    simpa using Seminorm_sum_le_finite (n' := n) N n (fun i => x i • e n i)
  refine le_trans h_sum_le ?_
  -- Use homogeneity to rewrite terms
  have h_homogeneity : ∑ i, N (x i • e n i) = ∑ i, |x i| * N (e n i) :=
  by
    simpa using Finite_Norm_Homogeneity  N (fun i => x i) (fun i => e n i)
  rw [h_homogeneity]
  -- Each coordinate is bounded by the norm
  have h_coord_less_than_max :
    ∀ i : Fin n, |x i| ≤ ‖x‖ :=
    by
      intro i
      simpa using (norm_le_pi_norm x i)
  -- Multiply inequalities by nonnegative N (eᵢ)
  have h_term_less_than_max_term :
    ∀ i : Fin n, |x i| * N (e n i) ≤ ‖x‖ * N (e n i) :=
    by
      intro i
      have h_N_nonneg : 0 ≤ N (e n i) :=
        Norm_Nonneg N (e n i)
      exact mul_le_mul_of_nonneg_right (h_coord_less_than_max i) h_N_nonneg
  -- Lift pointwise bounds to a sum
  have h_sum : ∑ i : Fin n, |x i| * N (e n i) ≤ ∑ i : Fin n, ‖x‖ * N (e n i) :=
  by
    classical
    have h : ∑ i : (Finset.univ : Finset (Fin n)), |x i| * N (e n i)
      ≤ ∑ i : (Finset.univ : Finset (Fin n)), ‖x‖ * N (e n i) :=
    by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact h_term_less_than_max_term i
    simpa using h
  -- Factor out ‖x‖ to obtain C * ‖x‖
  have final_equality : ∑ i : Fin n, ‖x‖ * N (e n i) = C * ‖x‖ :=
  by
    have h : ∑ i : Fin n, ‖x‖ * N (e n i) = ‖x‖ * ∑ i : Fin n, N (e n i) :=
    by
      classical
      have h' := (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin n)))
        (a := ‖x‖)
        (f := fun i => N (e n i)))
      simpa using h'.symm
    simpa [C, mul_comm] using h
  rw [final_equality.symm]
  exact h_sum

end UpperBound
