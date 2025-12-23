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

    have hnhd_fin_cover : ∀ x ∈ K, ∃ 𝓝ₓ ∈ nhds x, (
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

      --have hglue_in_prod : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, ∃ Uᵥ ∈ nhds x, ∃ Vᵥ ∈ nhds v,
      --  (f_prod glue) '' (Uᵥ ×ˢ Vᵥ) ⊆
      sorry

    --let x : X := hNonempty.choose; have hx : x ∈ K := hNonempty.choose_spec
    --let U₁ : X → Set X :=

    --choose N hN using nhd_fin_cover
    --#check N
    let N := fun x : X =>
      if hx : x ∈ K then (hnhd_fin_cover x hx).choose else ∅

    have hN : ∀ x ∈ K, N x ∈ nhds x ∧ (∃ (t : Finset I), (f_prod glue) '' (N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K})
      ⊆ ⋃ i ∈ t, U i) := by
      intro x hx
      simp only [N, hx]
      exact (hnhd_fin_cover x hx).choose_spec

    have hfin_sub_coverN : ∃ (t : Finset X), K ⊆ ⋃ i ∈ t, N i := by
      sorry

    obtain ⟨t₁, ht₁⟩ := hfin_sub_coverN

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

    replace ht₁ : (f_prod glue) '' K ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ (f_prod glue) '' ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
      exact Set.image_mono ht₁

    replace ht₁ : f_prod glue '' K ×ˢ {v | ∀ (i : Fin n), v i ∈ K} ⊆ ⋃ i ∈ t₁, (f_prod glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} := by
      have : ⋃ i ∈ t₁, (f_prod glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} = (f_prod glue) '' ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
        have : ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) = ⋃ p : {i // i ∈ t₁}, (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this, Set.image_iUnion]
        have : ⋃ i ∈ t₁, (f_prod glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} = ⋃ p : {i // i ∈ t₁}, (f_prod glue) '' (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this]
      rw [this]; exact ht₁

    have hnhd_fin_cover' : ∀ (x : X), ∃ (t : Finset I), (f_prod glue) '' N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ ⋃ j ∈ t, U j := by
      sorry


    sorry


  done
