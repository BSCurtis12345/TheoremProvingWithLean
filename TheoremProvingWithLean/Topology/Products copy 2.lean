import Mathlib
import TheoremProvingWithLean.Topology.Covers

set_option linter.flexible false
set_option linter.style.longLine false

open Covers

variable {X : Type} [TopologicalSpace X]

def f_prod (f : α → β → γ) : α × β → γ :=
  fun p => f p.1 p.2

theorem power_compact {K : Set X} (hK : IsCompact K) (hNonempty : K.Nonempty) :
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
    --rw [isCompact_iff_finite_subcover] at ih
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

    have hnhd_fin_cover : ∀ x ∈ K, ∃ (𝓝ₓ : Set X), ( (IsOpen 𝓝ₓ) ∧
      (∃ (t : Finset I), (f_prod glue) '' (𝓝ₓ ×ˢ {v : Fin n → X | ∀ i, v i ∈ K})
        ⊆ ⋃ i ∈ t, U i)) := by
    -- For x ∈ K, ∃ an open neighbourhoud 𝓝(x) ⊆ K s.t. 𝓝(x)×Kⁿ can be covered by a finite subfamily of U
      intro x hx
      have hglue_in_cover : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, ∃ j, glue x v ∈ U j := by
      -- For v ∈ Kⁿ, ∃ Uⱼ ∈ U s.t. (x,v) ∈ Uⱼ.
        intro v hv
        apply in_elt_cover hcover
        simp; intro i; rcases i with ⟨k, hk⟩
        cases k using Nat.casesOn with
        | zero => -- k = 0
            simp [glue]
            exact hx
        | succ m => -- k = m+1
            simp [glue]
            simp at hv; exact hv ⟨m, Nat.lt_of_succ_lt_succ hk⟩

      choose j hj using hglue_in_cover

      have : ∀ v (hv : v ∈ {v : Fin n → X | ∀ i, v i ∈ K}), ∃ Uᵥ ∈ nhds x, ∃ Vᵥ ∈ nhds v,
        (x,v) ∈ Uᵥ ×ˢ Vᵥ ∧ f_prod glue '' Uᵥ ×ˢ Vᵥ ⊆ U (j v hv) := by
        intro v hv

        sorry



      sorry

    let N := fun x : X =>
      if hx : x ∈ K then (hnhd_fin_cover x hx).choose else ∅
    -- Defines a choice function that takes an x ∈ X to a neighbourhood of x s.t. N(x)×Kⁿ is finitely coverable

    have hN : ∀ x ∈ K, IsOpen (N x) ∧ (∃ (t : Finset I), (f_prod glue) '' (N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K})
      ⊆ ⋃ i ∈ t, U i) := by
      intro x hx
      simp only [N, hx]
      exact (hnhd_fin_cover x hx).choose_spec
    -- Proves that the cover property of each neighbourhood N(x) given by the choice function holds

    have hfin_sub_coverN : ∃ (t : Finset X), K ⊆ ⋃ i ∈ t, N i := by
    -- ∃ a finite subcover of {N(x)}ₓ covering K - follows from compactness
      sorry

    obtain ⟨t₁, ht₁⟩ := hfin_sub_coverN -- Gives us a particular finite subcover

    replace ht₁ : K ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ (⋃ i ∈ t₁, N i) ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} := Set.prod_mono_left ht₁
    replace ht₁ : K ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
      have : (⋃ i ∈ t₁, N i) ×ˢ {v | ∀ (i : Fin n), v i ∈ K} = ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
        have : ⋃ i ∈ t₁, N i = ⋃ p : {i // i ∈ t₁}, N p.1 := by
          simp [Set.iUnion_subtype]
        simp [this, Set.iUnion_prod_const]
        have : ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) = ⋃ p : {i // i ∈ t₁}, (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this]
      rw [← this]; exact ht₁
    -- Adds cartesian product with Kⁿ to the finite subcover hypothesis, then exchanges the union and the product

    replace ht₁ : (f_prod glue) '' K ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ (f_prod glue) '' ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
      exact Set.image_mono ht₁
    -- Takes the image under the 'glue' function in the finite subcover hypothesis

    replace ht₁ : f_prod glue '' K ×ˢ {v | ∀ (i : Fin n), v i ∈ K} ⊆ ⋃ i ∈ t₁, (f_prod glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} := by
      have : ⋃ i ∈ t₁, (f_prod glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} = (f_prod glue) '' ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
        have : ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) = ⋃ p : {i // i ∈ t₁}, (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this, Set.image_iUnion]
        have : ⋃ i ∈ t₁, (f_prod glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} = ⋃ p : {i // i ∈ t₁}, (f_prod glue) '' (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this]
      rw [this]; exact ht₁
    -- Similarly painstaking process as with the product above to exchange the image and union

    have hnhd_fin_cover' : ∀ (x : X), ∃ (t : Finset I), (f_prod glue) '' N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ ⋃ j ∈ t, U j := by
    -- ∀ x ∈ X, there is a finite subcover of U covering N(x)×Kⁿ
      sorry

    have hnhd_prod_fin_cover : ∃ (t : Finset I), ⋃ i ∈ t₁, f_prod glue '' N i ×ˢ {v | ∀ (i : Fin n), v i ∈ K} ⊆
      ⋃ j ∈ t, U j := by
    -- The union over t₁ of N(i)×Kⁿ is covering by some finite subcover of U

      choose T hT using hnhd_fin_cover'
      -- Defines a choice function T from x ∈ X to some finite subcover of U covering N(x)×Kⁿ

      refine ⟨t₁.biUnion T, ?_⟩ -- Takes as witness the union over t₁ of T(x)

      intro v hv
      rcases Set.mem_iUnion.1 hv with ⟨i, hv⟩
      rcases Set.mem_iUnion.1 hv with ⟨hi₁, hAi⟩
      -- Unpack subset, set membership and union definitions

      have hv' : v ∈ ⋃ j ∈ T i, U j := hT i hAi
      rcases Set.mem_iUnion.1 hv' with ⟨j, hv'⟩
      rcases Set.mem_iUnion.1 hv' with ⟨hjTi, hvUj⟩
      -- Get that v is in a union over some cover T(i) for some i ∈ t₁, unpack further

      have hjt : j ∈ t₁.biUnion T := Finset.mem_biUnion.2 ⟨i, hi₁, hjTi⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjt, hvUj⟩⟩

    rcases hnhd_prod_fin_cover with ⟨t, ht⟩
    apply subset_trans ht₁ at ht
    -- Take t as a witness to the existential above, get from it that K×Kⁿ is covered by t

    have hglue_eq_Kn : f_prod glue '' K ×ˢ {v | ∀ (i : Fin n), v i ∈ K} = {v | ∀ (i : Fin (n + 1)), v i ∈ K} := by
    /-
    At this point we are basically done.
    We just need to show that the '×ˢ' definition and 'Fin (n+1) → X' definitions of Kⁿ we have been using are the same.
    In our mathematical 'meta-proof' this follows directly from definitions.
    The following is essentially just a series of simple manipulations.
    -/

      ext v
      constructor
      · intro hv
        simp; intro i
        simp at hv
        rcases hv with ⟨x, ⟨w, ⟨⟨hxK, hwK⟩, hv⟩⟩⟩
        subst hv
        rcases i with ⟨j,hj⟩
        cases j using Nat.casesOn with
        | zero => -- j = 0
          simp [glue, f_prod]
          exact hxK
        | succ m => -- m = j+1
          simp [glue, f_prod]
          exact hwK ⟨m, Nat.lt_of_succ_lt_succ hj⟩

      · intro hv
        simp; simp at hv
        let w (i : Fin n) : X :=
          v (i.succ)
        use v 0; use w
        constructor; constructor
        · exact hv 0
        · simp [w, hv]
        · simp [glue, f_prod, w]
          ext i
          rcases i with ⟨j,hj⟩
          cases j using Nat.casesOn with
          | zero => simp
          | succ m => simp

    refine ⟨t, ?_⟩
    simpa [hglue_eq_Kn] using ht

  done
