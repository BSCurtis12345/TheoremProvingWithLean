import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TheoremProvingWithLean.Topology.Covers
--import TheoremProvingWithLean.Topology.OpenSets

set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false

namespace HeineBorel

abbrev Rn (n : ℕ) := Fin n → ℝ

lemma subset_Icc_bdd_above {a b : ℝ} {S : Set ℝ} (h : S ⊆ Set.Icc a b) : BddAbove S := by
/-
Proves that a subset of a closed interval in ℝ is bounded above.
-/
  refine ⟨b, fun x hx => ?_⟩ -- Take b as a witness, let x ∈ S
  have : x ∈ Set.Icc a b := h hx -- x ∈ [a,b]
  exact this.2 -- x ≤ b by definition
  done

lemma sup_subset_in_Icc {a b : ℝ} {S : Set ℝ} (hS : S.Nonempty) (hsub : S ⊆ Set.Icc a b) : sSup S ∈ Set.Icc a b := by
/-
Proves that if ∅ ≠ S ⊆ [a,b], then sup S ∈ [a,b].
-/
  constructor
  · -- a ≤ sup S
    obtain ⟨x, hx⟩ := hS -- Let x ∈ S
    have : a ≤ x := (hsub hx).1 -- Then a ≤ x
    apply le_csSup (subset_Icc_bdd_above hsub) at hx -- x ≤ sup S
    exact this.trans hx -- Transitivity
  · -- sup S ≤ b - true iff every b₁ ∈ S has b₁ ≤ b
    rw [csSup_le_iff (subset_Icc_bdd_above hsub) hS]
    intros c hc; exact (hsub hc).2
  done

lemma exists_Ioo_sub_open {U : Set ℝ} {x : ℝ} (hUopen : IsOpen U) (hx : x ∈ U) :
  ∃ ε > 0, Set.Ioo (x-ε) (x+ε) ⊆ U := by
/-
Proves that if x ∈ U ⊆ ℝ, U open, then ∃ ε > 0 s.t. (x-ε,x+ε).
This result is essentially the definition of what makes a set open in the standard topology on ℝ.
Thus we use Metric.isOpen_iff to do most the work here.
-/
  rw [Metric.isOpen_iff] at hUopen
  specialize hUopen x hx
  obtain ⟨ε, hε⟩ := hUopen
  use ε
  rw [← Real.ball_eq_Ioo x ε]
  exact hε
  done

open Covers

section Icc_finCover

-- Let U be a family of sets indexed over ι, a, b ∈ ℝ
variable {ι : Type u} {U : ι → Set ℝ} {a b : ℝ}

lemma lower_singleton_Icc_fin_cover
  (h : a ≤ b) (hcover : Set.Icc a b ⊆ ⋃ i, U i) :
  a ∈ {x ∈ Set.Icc a b | ∃ (t : Finset ι), Set.Icc a x ⊆ ⋃ i ∈ t, U i} := by
  /-
  Proves that if [a,b] covered by U, then a ∈ {x ∈ [a,b] : [a,x] is covered by a finite subcover of U}.
  (Basically that the singleton {a} can be finitely covered but in the form we want for later).
  -/
  simp -- Unfold definition of the set
  constructor
  · exact h -- a ≤ b by assumption
  · -- ∃ a finite t in ι s.t. a ∈ Uᵢ for some i ∈ t
    -- a ∈ [a,b] covered by U, so a belongs to an element of U
    have ha : a ∈ Set.Icc a b := by simpa
    apply in_elt_cover hcover a at ha
    -- Choose as the finite t the singleton containing the index of the set containing a
    rcases ha with ⟨j, hj⟩
    let J : Finset ι := {j}
    use J
    use j
    simp [J, hj]
  done

end Icc_finCover


theorem IsCompact_Icc (a b : ℝ) (h : a ≤ b) : IsCompact (Set.Icc a b) := by
/-
This theorem proves that every (non-degenerate) closed interval in R is compact (with the usual topology).

Notable Mathlib results used:
  • isCompact_iff_finite_subcover : proves that Mathlib definition for a compact set is equivalent to definition using open coverings
-/
  rw [isCompact_iff_finite_subcover] -- Rewrite goal in terms of finite subcover definition

  intros I U hUopen hcover -- Let U be an open cover indexed over I

  by_cases ha_eq_b : a = b
  -- In the case that a=b, [a,b] = {a}, and a must belong to a cover element, say Uⱼ, so use {Uⱼ} as the finite subcover
  · have : ∃ j, a ∈ U j := Set.mem_iUnion.mp (hcover (by simpa using h))
    rcases this with ⟨j, hj⟩
    use {j}
    simpa [ha_eq_b] using hj

  -- In the case a ≠ b, then a < b
  replace h : a < b := lt_of_le_of_ne h ha_eq_b

  -- Let A = {x ∈ [a,b] : [a,x] is covered by a finite subcover of U}
  let A : Set ℝ := {x ∈ Set.Icc a b | ∃ (t : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t, U i}

  -- Get A ⊆ [a,b]; a ∈ A; sup A ∈ [a,b] for later convenience
  have hA : A ⊆ Set.Icc a b := by intros x hx; exact hx.1
  have ha : a ∈ A := by exact lower_singleton_Icc_fin_cover (le_of_lt h) hcover

  have hsup : sSup A ∈ Set.Icc a b := by exact sup_subset_in_Icc ⟨a, ha⟩ hA

  -- Get sup A ∈ Uᵢ for some i, takes j as the witness to this
  apply in_elt_cover hcover (sSup A) at hsup
  rcases hsup with ⟨j, hj⟩

  have hδ : ∃ δ > 0, Set.Ioo (sSup A - δ) (sSup A + δ) ⊆ U j ∧ a ≤ sSup A - δ := by
  -- Proves that ∃ δ > 0 s.t. (sup A - δ, sup A + δ) ⊆ Uⱼ and a ≤ sup A - δ
    -- Get from openness of Uⱼ and sup A ∈ Uⱼ, that there is an ε-ball around sup A contained in Uⱼ
    rcases exists_Ioo_sub_open (hUopen j) hj with ⟨ε, hε⟩ -- !!! Comment on validity of this mathlib lemma

    -- Get that a belongs to some cover element, say k, and apply the same as above to get (a - ε', a + ε') ⊆ Uₖ
    have : ∃ j, a ∈ U j := Set.mem_iUnion.mp (hcover (by simpa using le_of_lt h))
    rcases this with ⟨k, hk⟩
    rcases exists_Ioo_sub_open (hUopen k) hk with ⟨ε', hε'⟩

    -- Let δ = min {(b-a)/2, ε/2, ε'/2}, get that δ > 0, δ < ε, ε'
    let δ := min (min ((b-a)/2) (ε/2)) (ε'/2)
    have : δ > 0 ∧ δ < ε ∧ δ < ε' := by simp [δ, hε.1, h, hε'.1]

    -- We get that a + δ ∈ A in order to to prove later that sup A - δ ≥ a
    have hδ' : a + δ ∈ A := by
      simp [A] -- Simplify goals by unpacking definition of A
      constructor
      · -- 0 ≤ δ ≤ b-a
        refine And.intro (le_of_lt this.1) ?_ -- LHS follows from δ > 0

        -- Unpack def of δ using min, carry out arithmetic, use transitivity of ≤
        have : a+((b-a)/2) ≤ b := by
          have h' : (b - a) / 2 ≤ b - a :=
            half_le_self (le_of_lt (sub_pos.mpr h))
          have := add_le_add_left h' a
          simpa [add_comm, add_left_comm, add_assoc, add_sub_cancel] using this
        apply ge_trans this
        simp [δ]
      · -- [a, a + δ] is finitely coverable from U
        -- Since δ < ε', [a, a+δ] ⊆ (a-ε',a+ε') ⊆ Uₖ, so {k} works as witness to finite index set
        use {k}
        simp
        refine subset_trans ?_ hε'.2
        intro x hx
        simp; simp at hx
        refine And.intro (lt_of_lt_of_le ((sub_lt_self a) hε'.1) hx.1) ?_
        exact lt_of_le_of_lt hx.2 (add_lt_add_right this.2.2 a)

    use δ
    refine And.intro this.1 ?_
    constructor
    · refine subset_trans ?_ hε.2
      intro x hx; simp; simp at hx -- same as above - could make separate lemma
      refine And.intro (lt_trans (sub_lt_sub_left this.2.1 (sSup A)) hx.1) ?_
      exact lt_trans hx.2 (add_lt_add_right this.2.1 (sSup A))
    · rw [le_sub_iff_add_le]
      exact le_csSup (subset_Icc_bdd_above hA) hδ'

  -- Get an ε satisfying the existential above
  rcases hδ with ⟨ε,hε⟩

  have hfinCoverε : ∃ (t : Finset I), Set.Ico a (sSup A + ε) ⊆ ⋃ i ∈ t, U i := by
  -- Proves that [a, sup A + ε) is finitely coverable
    have hx : ∃ x ∈ A, (sSup A - ε) < x := by
    -- Proves there is an x > sup A - ε in A
      apply exists_lt_of_lt_csSup
      · use a
      · simp [hε]

    -- Take x as a witness of the above
    rcases hx with ⟨x, hx⟩

    have hunion : Set.Icc a x ∪ Set.Ioo (sSup A - ε) (sSup A + ε) = Set.Ico a (sSup A + ε) := by -- could make this a lemma
    -- Proves [a,x] ∪ (sup A - ε, sup A + ε) = [a, sup A + ε)
      ext y; constructor -- By extensionality
      · intro hy -- Let y be in the union
        simp; simp at hy -- Unpack definitions
        cases hy with -- Split hy into its two disjuncts
        | inl hy₁ => -- Case 1: y ∈ [a,x] i.e. a ≤ y ≤ x
          refine And.intro hy₁.1 ?_ -- Reduce goal to only y < sup A + ε
          apply lt_of_le_of_lt hy₁.2 -- Since y ≤ x, suffices that x < sup A + ε

          -- Since x ∈ A, by def of sup, x < sup A + ε
          refine lt_of_le_of_lt (le_csSup (subset_Icc_bdd_above hA) hx.1) ?_
          simp [hε.1]

        | inr hy₂ => -- Case 2: y ∈ (sup A - ε, sup A + ε), i.e. sup A - ε < y < sup A + ε
          refine And.intro ?_ hy₂.2 -- Reduce goal to only a ≤ y
          exact le_trans hε.2.2 (le_of_lt hy₂.1) -- Conclude by transitivity of ≤ with assumptions on ε and y

      · intro hy -- Now let y ∈ [a, sup A + ε)
        simp; simp at hy -- Unpack definitions
        by_cases hy' : sSup A - ε < y -- Split into cases : sup A - ε < y or sup A - ε ≥ y
        · -- In the case that sup A - ε < y, we show that y ∈ (sup A - ε, sup A + ε), hence in the union
          right; exact And.intro hy' hy.2
        · -- Otherwise we show that y ∈ [a,x] by condition on x
          simp at hy'; left
          exact And.intro hy.1 (le_trans hy' (le_of_lt hx.2))

    rw [← hunion] -- Rewrite the goal with the equality above

    -- Get explicitly that [a,x] finitely coverable by unpacking A and using x ∈ A
    have ht₁ : ∃ (t₁ : Finset I), Set.Icc a x ⊆ ⋃ i ∈ t₁, U i := hx.1.2

    have ht₂ : ∃ (t₂ : Finset I), Set.Ioo (sSup A - ε) (sSup A + ε) ⊆ ⋃ i ∈ t₂, U i := by
    -- Proves that (sup A - ε, sup A + ε) is finitely coverable from U
      -- Since ε was chosen s.t. (sup A - ε, sup A + ε) ⊆ Uⱼ ∈ U, we can use {j} as witness finite index set
      let J : Finset I := {j}
      use J
      intros y hy
      apply hε.2.1 at hy
      have : j ∈ J := by simp [J]
      exact Set.mem_biUnion this hy

    -- Since both are finitely coverable, so is their union
    exact union_fin_cover ht₁ ht₂

  have hsupEqb : (sSup A) = b := by
  -- Proves that sup A = b
    -- Prove by contradiction: assume sup A ≠ b, then split into cases
    classical by_contra hneg;
    apply ne_iff_lt_or_gt.mp at hneg
    cases hneg with

    | inl hl => -- Case sup A < b

      have : min b (sSup A + ε/2) ∈ A := by
      -- Proves min{b, sup A + ε/2} ∈ A
        change min b (sSup A + ε/2) ∈ {x | x ∈ Set.Icc a b ∧ ∃ t, Set.Icc a x ⊆ ⋃ i ∈ t, U i}
        have : Set.Icc a (min b (sSup A + ε/2)) ⊆ Set.Ico a (sSup A + ε) := by
        -- Proves [a, min{...}] ⊆ [a, sup A + ε)
          have : (min b (sSup A + ε/2)) < sSup A + ε := by simp [hε.1]
          exact Set.Icc_subset_Ico_right this

        -- Then [a, min{...}] is finitely coverable
        apply subset_fin_cover hfinCoverε at this


        simp [le_of_lt h, this] -- Reduce goal to a ≤ sup A + ε/2

        -- Basic arithmetic
        have : a - ε/2 ≤ a := by apply le_of_lt; simp [hε]
        rw [← sub_le_iff_le_add]
        exact le_csSup_of_le (subset_Icc_bdd_above hA) ha this

      apply le_csSup (subset_Icc_bdd_above hA) at this -- min{...} ≤ sup A
      simp at this -- So b ≤ sup A or ε/2 ≤ 0
      cases this with
      | inl hl₁ => contrapose! hl; exact hl₁ -- If b ≤ sup A, this contradicts our condition that sup A < b
      | inr hr₁ => contrapose! hr₁; simp [hε] -- If ε/2 ≤ 0, this contradicts our condition that ε > 0

    | inr hr => -- Case sup A > b
      contrapose! hr -- Contrapose -- changes goal to sup A ≤ b
      rw [← csSup_Icc (le_of_lt h)] -- Then sup A ≤ sup [a,b]
      exact csSup_le_csSup bddAbove_Icc ⟨a, ha⟩ hA -- Conclude from A ⊆ [a,b]

  -- Now [a, b+ε) is finitely coverable, so clearly so must be [a,b]
  rw [hsupEqb] at hfinCoverε
  have : b < b + ε := by simp [hε]
  exact subset_fin_cover hfinCoverε (Set.Icc_subset_Ico_right this)
  done


lemma compact_implies_bounded (s : Set ℝ) (hs : IsCompact s) :
  ∃ R : ℝ, ∀ x, x ∈ s → |x| ≤ R :=
  by
    -- We will cover s by open balls centred at 0 with radii (n : ℝ) + 1
    have hcover : s ⊆ ⋃ n : ℕ, Metric.ball 0 ((n : ℝ) + 1)  :=
    by
      -- First show the same union covers all of ℝ (i.e. Set.univ), then restrict to s
      have hcoverR : (Set.univ : Set ℝ) ⊆ ⋃ n : ℕ, Metric.ball 0 ((n : ℝ) + 1) :=
      by
        -- Take any real x
        intro x hx
        -- Choose n = ceil(|x|) so that |x| ≤ n
        let n := Nat.ceil |x|
        have h1 : |x| ≤ (n : ℝ) :=
        by
          exact Nat.le_ceil _
        -- Hence |x| < n + 1, which means x us inside the ball of radius n + 1
        have h2 : |x| < (n : ℝ) + 1 :=
        by
          linarith
        -- Prove x ∈ ⋃ n, ball 0 (n+1)
        refine Set.mem_iUnion.mpr ?_
        refine ⟨n, ?_⟩
        simp [Metric.ball, Real.dist_eq] at *
        exact h2
      -- Prove s ⊆ ℝ
      have RcoverS : s ⊆ (Set.univ : Set ℝ) :=
      by
        exact fun ⦃a⦄ a_1 ↦ trivial
      -- Restrict the universal cover to a cover of s
      exact fun ⦃a⦄ a_1 ↦ hcoverR (RcoverS a_1)

    -- Each ball is open
    have hopen : ∀ n : ℕ, IsOpen (Metric.ball (0 : ℝ) ((n : ℝ) + 1)) :=
      fun n => Metric.isOpen_ball
    -- Name the covering sets as a function U : ℕ → Set ℝ
    let U : ℕ → Set ℝ := fun n => Metric.ball (0 : ℝ) ((n : ℝ) + 1)
    -- Restate openness in terms of U
    have hopen : ∀ n : ℕ, IsOpen (U n) :=
    by
      intro n
      simp [U]
    classical
    -- Compactness gives a finite subcover: some finite index set t so that ⋃ i ∈ t, U i covers s
    obtain ⟨t, htcover⟩ := hs.elim_finite_subcover U hopen hcover
    -- Split on whether s is empty or not
    by_cases hsEmpty : s = ∅
    · -- If s = ∅, take R = 0
      refine ⟨0, ?_⟩
      intro x hx
      exfalso
      simp [hsEmpty] at hx
    · -- If s ≠ ∅, pick an x0 ∈ s.
      have hsNonempty : s.Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hsEmpty
      rcases hsNonempty with ⟨x0, hx0⟩
      -- Show the finite index set t is nonempty
      have htNonempty : t.Nonempty :=
      by
        -- Since x0 ∈ s, the finite subcover means x0 is in ⋃ i ∈ t, U i
        have : x0 ∈ ⋃ i ∈ t, U i := htcover hx0
        -- Unpack membership in the union twice to obtain an i ∈ t
        rcases Set.mem_iUnion.1 this with ⟨i, hi⟩
        rcases Set.mem_iUnion.1 hi with ⟨hiT, _hxUi⟩
        exact ⟨i, hiT⟩
      -- Let N be the maximum element of the finite index set t
      let N : ℕ := t.max' htNonempty
      -- Claim the bound is R = (N : ℝ) + 1
      refine ⟨(N : ℝ) + 1, ?_⟩
      -- Now show every x ∈ s satisfies |x| ≤ (N : ℝ) + 1
      intro x hx
      -- Put x into the finite union: x ∈ ⋃ i ∈ t, U i
      have hxcover : x ∈ ⋃ i ∈ t, U i := htcover hx
      -- Extract an index i with i ∈ t and x ∈ U i
      rcases Set.mem_iUnion.1 hxcover with ⟨i, hi⟩
      rcases Set.mem_iUnion.1 hi with ⟨hiT, hxUi⟩
      -- From x ∈ U i = ball 0 (i+1), get |x| < (i : ℝ) + 1
      have hxlt : |x| < (i : ℝ) + 1 :=
      by
        simpa [U, Metric.mem_ball, Real.dist_eq] using hxUi
      -- Since N is the max of t and i ∈ t, we have i ≤ N
      have hi_le_N : i ≤ N := by
        exact Finset.le_max' t i hiT
      -- Change i ≤ N from naturals to reals
      have hi_le_N' : (i : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hi_le_N
      -- Combine |x| < i+1 and i ≤ N to get |x| < N+1
      have hxltN : |x| < (N : ℝ) + 1 := by
        linarith
      -- Convert strict inequality to the required non-strict inequality
      exact le_of_lt hxltN


end HeineBorel
