import Mathlib

set_option linter.flexible false
set_option linter.style.longLine false

variable {X : Type} [TopologicalSpace X]

theorem power_compact {K : Set X} (hK : IsCompact K) :
  ∀ n : ℕ, IsCompact {v : Fin n → X | ∀ i, v i ∈ K} := by

  classical
  intro n
  induction n with
  -- Prove by induction on n
  | zero => -- Base case : n = 0

    rw [isCompact_iff_finite_subcover]
    intro I U hopen hcover
    -- Rewrite goal in terms of finite subcover definition, let U be an open cover

    simp
    let f : Fin 0 → X := fun i => i.elim0
    have : f ∈ {v | ∀ (i : Fin 0), v i ∈ K} := by simp
    have : f ∈ ⋃ i, U i := Set.mem_of_mem_of_subset this hcover
    -- Let f be the trivial "only member" of X⁰, deduce that it is in K⁰ and the cover

    rcases Set.mem_iUnion.1 this with ⟨i, hi⟩
    refine ⟨{i}, ?_⟩
    -- Let i be s.t. f ∈ Uᵢ ∈ U, take {i} as witness to existential

    ext v
    constructor
    · intro _
      trivial
    · intro _
      have hv : v = f := Subsingleton.elim _ _
      subst hv
      -- Get that every v ∈ X⁰ is equal to f

      have : f ∈ ⋃ i_1 ∈ ({i} : Finset I), U i_1 := by
        simp [hi]
      exact this

  | succ n ih =>

    rw [isCompact_iff_finite_subcover]
    intro I U hopen hcover
    rw [isCompact_iff_finite_subcover] at hK
    rw [isCompact_iff_finite_subcover] at ih
    -- Change everything to be in terms of finite subcovers, take open cover U

    let head (v : Fin (n+1) → X) : X :=
      v 0
    let tail (v : Fin (n + 1) → X) : Fin n → X :=
      fun i => v (i.succ)
    -- For each v ∈ Xⁿ⁺¹, define a 'head' (the first co-ordinate), and 'tail' (the remaining n co-ordinates)

    let glue (x : X) (w : Fin n → X) : Fin (n+1) → X :=
      fun k =>
        match k with
        | ⟨0, _⟩     => x
        | ⟨m+1, hk⟩ => w ⟨m, Nat.lt_of_succ_lt_succ hk⟩
    -- Define a function that glues some x ∈ X to w ∈ Xⁿ
    let V (x : X) (i : I) : Set (Fin n → X) :=
      { w | glue x w ∈ U i }
    -- Define V(x,i), the set of w ∈ Xⁿ which when glued to x are in Uᵢ

    -- Now we want to show that:
    -- (1a) V(x,i), i ∈ I is a cover of the tails for each fixed x ∈ X
    have cover_tails : ∀ x ∈ K, {w : Fin n → X | ∀ j, w j ∈ K} ⊆ ⋃ i, V x i := by
      intro x hx w hw
      let v : Fin (n+1) → X := glue x w
      -- Let x ∈ K, w ∈ Kⁿ, v = (x,w)

      -- Now we show that vᵢ ∈ K for each i (essentially v ∈ Kⁿ⁺¹)
      have hvK : ∀ i : Fin (n+1), v i ∈ K := by
        intro i
        rcases i with ⟨k, hk⟩
        -- Take i and break it down into k with hk : k < n+1
        cases k using Nat.casesOn with
        | zero => -- k = 0
            simp [v, glue] at *
            exact hx
        | succ m => -- k = m+1
            have : w ⟨m, Nat.lt_of_succ_lt_succ hk⟩ ∈ K := hw ⟨m, Nat.lt_of_succ_lt_succ hk⟩
            simp at this
            simpa [v, glue] using this

      have hvU : v ∈ ⋃ i, U i := by
        have : v ∈ {v | ∀ (i : Fin (n + 1)), v i ∈ K} := hvK
        exact Set.mem_of_mem_of_subset this hcover
      -- Get that v is covered

      rcases Set.mem_iUnion.1 hvU with ⟨i0, hvi0⟩
      -- Let i0 be member of cover containing v

      have hwV : w ∈ V x i0 := by
        change glue x w ∈ U i0
        simpa [v] using hvi0
      exact Set.mem_iUnion.2 ⟨i0, hwV⟩
      -- Then w ∈ V(x,i0) so Kⁿ covered by the V(x,i), i ∈ I

    have hopen_V : ∀ x, x ∈ K → ∀ i, IsOpen (V x i) := by
      intro x hx i
      -- V(x,i) is the preimage of U i under the continuous map w ↦ glue x w
      sorry -- do this later

    -- (1b) By IH, for each x there is a finite subcover V x i, i ∈ t_x
    have finCover_tails : ∀ x ∈ K, ∃ t_x : Finset I, {w : Fin n → X | ∀ j, w j ∈ K} ⊆ ⋃ i ∈ t_x, V x i := by
      intro x hx
      apply ih
      · apply hopen_V; exact hx
      · apply cover_tails; exact hx

    -- (2a) By hK there is a finite subcover of heads x ∈ K
    let W : Finset I → Set X :=
      fun t => {x | x ∈ K ∧ {w : Fin n → X | ∀ j, w j ∈ K} ⊆ ⋃ i ∈ t, V x i}




    sorry


  done
