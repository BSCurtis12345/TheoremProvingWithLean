import Mathlib
import TheoremProvingWithLean.Topology.Covers

set_option linter.flexible false
set_option linter.style.longLine false

/-
Potential code cleaning:
· Change to use Set.univ.pi instead of annoying definitions
-/

open Covers

variable {X : Type} [TopologicalSpace X]

def f_prod (f : α → β → γ) : α × β → γ :=
  fun p => f p.1 p.2

theorem power_compact {K : Set X} (hK : IsCompact K) (hNonempty : K.Nonempty) :
  ∀ n : ℕ, IsCompact {v : Fin n → X | ∀ i, v i ∈ K} := by


  classical
  intro n
  --#check TopologicalSpace (Fin n → X)
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

    have hnhd_fin_cover : ∀ x ∈ K, ∃ (𝓝ₓ : Set X), ( (IsOpen 𝓝ₓ ∧ x ∈ 𝓝ₓ) ∧
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

      let W := fun v : Fin n → X =>
        if hv : v ∈ {v : Fin n → X | ∀ i, v i ∈ K} then U (hglue_in_cover v hv).choose
        else ∅

      have hW : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, glue x v ∈ W v := by
        intro v hv
        simp only [W]
        simpa [W, hv] using (hglue_in_cover v hv).choose_spec

      have hWopen : ∀ (v : Fin n → X), IsOpen (W v) := by
        intro v
        simp only [W]
        by_cases hv : v ∈ {v | ∀ (i : Fin n), v i ∈ K}
        · simp [hv, hopen]
        · simp [hv]

      have hTV : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, ∃ Tᵥ, ∃ Vᵥ,
        IsOpen Tᵥ ∧ IsOpen Vᵥ ∧ (x,v) ∈ Tᵥ ×ˢ Vᵥ ∧ (f_prod glue) '' (Tᵥ ×ˢ Vᵥ) ⊆ W v := by

        intro v hv
        specialize hWopen v
        rw [isOpen_pi_iff'] at hWopen -- isOpen_pi_iff' okay?
        have hWopen' :  glue x v ∈ W v → ∃ u, (∀ (a : Fin (n + 1)), IsOpen (u a) ∧ glue x v a ∈ u a) ∧ Set.univ.pi u ⊆ W v := hWopen (glue x v)
        --specialize hWopen (glue x v)
        replace hWopen' : ∃ u, (∀ (a : Fin (n + 1)), IsOpen (u a) ∧ glue x v a ∈ u a) ∧ Set.univ.pi u ⊆ W v := by
          exact hWopen' (hW v hv)

        obtain ⟨u, hu⟩ := hWopen'
        have hu0 : IsOpen (u 0) ∧ glue x v 0 ∈ u 0 := hu.1 0
        have hu_tail : IsOpen {w : Fin n → X | ∀ (a : Fin n), w a ∈ u a.succ} ∧ tail (glue x v) ∈ {w : Fin n → X | ∀ (a : Fin n), w a ∈ u a.succ} := by
          constructor
          · rw [isOpen_pi_iff']
            intro f hf
            -- Should be able to use u as witness? With index shifted or something
            -- Note f ∈ W v → tail f ∈ {...} and vice versa?
            let u_tail : (Fin n) → Set X :=
              fun i => u i.succ
            use u_tail
            constructor
            · intro a
              rcases hu with ⟨hu_all, hu_sub⟩
              refine And.intro ?h_open ?h_mem
              · have : IsOpen (u a.succ) := (hu_all a.succ).1
                simp at this
                exact this
              · have hf' : ∀ i : Fin n, f i ∈ u i.succ := by
                  simpa using hf
                have : f a ∈ u a.succ := hf' a
                dsimp [u_tail]
                exact this
            · intro w hw
              change ∀ a : Fin n, w a ∈ u a.succ
              have hw' : ∀ a : Fin n, w a ∈ u_tail a := by
                simpa [u_tail] using hw
              intro a
              simpa [u_tail] using hw' a

          · change ∀ a : Fin n, tail (glue x v) a ∈ u a.succ
            intro a
            simp [tail]
            exact (hu.1 a.succ).2

        use u 0
        use {w : Fin n → X | ∀ (a : Fin n), w a ∈ u a.succ}
        refine And.intro hu0.1 ⟨hu_tail.1, ?_⟩
        constructor
        · constructor
          · have : glue x v 0 ∈ u 0 := hu0.2
            simpa [glue] using this
          · have : tail (glue x v) ∈ {w | ∀ a : Fin n, w a ∈ u a.succ} := hu_tail.2
            have hcoords : ∀ a : Fin n, tail (glue x v) a ∈ u a.succ := by
              simpa using this
            simpa using hcoords
        · intro y hy
          rcases hy with ⟨⟨x', w⟩, hmem, rfl⟩
          rcases hmem with ⟨hx', hw'⟩
          have hcoords : ∀ a : Fin n, w a ∈ u a.succ := by
            simpa using hw'
          have hpi : f_prod glue (x', w) ∈ Set.univ.pi u := by
            refine Set.mem_univ_pi.2 ?_
            intro k
            refine Fin.cases ?h0 ?_ k
            · simpa [glue] using hx'
            · intro i
              have : w i ∈ u i.succ := hcoords i
              simpa [glue] using this
          exact hu.2 hpi

      let V := fun v : Fin n → X =>
        if hv : v ∈ {w | ∀ (i : Fin n), w i ∈ K} then
          (hTV v hv).choose_spec.choose
        else ∅

      let T := fun v : Fin n → X =>
        if hv : v ∈ {w | ∀ (i : Fin n), w i ∈ K} then
          (hTV v hv).choose
        else ∅

      have hV_open_cover : (∀ v, IsOpen (V v)) ∧ {w | ∀ (i : Fin n), w i ∈ K} ⊆ ⋃ v, (V v) := by
        constructor
        · intro v
          by_cases hv : v ∈ {w | ∀ (i : Fin n), w i ∈ K}
          · simp only [V, hv]
            exact (hTV v hv).choose_spec.choose_spec.2.1
          · simp only [V, hv]
            simp
        · intro w hw
          rw [Set.mem_iUnion]
          use w
          simp only [V, hw]
          exact (hTV w hw).choose_spec.choose_spec.2.2.1.2

      have hV_fin_cover : ∃ (t : Finset (Fin n → X)), {w | ∀ (i : Fin n), w i ∈ K} ⊆ ⋃ i ∈ t, V i ∧ ∀ v ∈ t, v ∈ {w : Fin n → X | ∀ (i : Fin n), w i ∈ K} := by
        have : ∃ (t : Finset (Fin n → X)), {w | ∀ (i : Fin n), w i ∈ K} ⊆ ⋃ i ∈ t, V i := by
          rw [isCompact_iff_finite_subcover] at ih
          exact ih V hV_open_cover.1 hV_open_cover.2
        obtain ⟨t',ht'⟩ := this
        let t := t'.filter (fun v => v ∈ {w : Fin n → X | ∀ (i : Fin n), w i ∈ K})
        use t
        constructor
        · intro v hv
          have hv' : ∃ i ∈ t', v ∈ V i := by simpa using (Set.mem_of_mem_of_subset hv ht')
          obtain ⟨j, hj⟩ := hv'
          simp; use j
          refine And.intro ?_ hj.2
          simp [t]
          refine And.intro hj.1 ?_
          by_contra hj_neg
          replace hj_neg : j ∉ {w | ∀ (i : Fin n), w i ∈ K} := by simpa using hj_neg
          have hVj_empty : V j = ∅ := by simp only [V, hj_neg]; simp
          rw [← Set.mem_empty_iff_false v]
          simpa [hVj_empty] using hj.2
        · intro v hv
          exact (Finset.mem_filter.mp (by simpa [t] using hv)).2

      obtain ⟨t, ht⟩ := hV_fin_cover

      use ⋂ i ∈ t, T i
      constructor
      · constructor
        · apply isOpen_biInter_finset
          intro j hj
          simp only [T, ht.2 j hj]
          exact (hTV j (ht.2 j hj)).choose_spec.choose_spec.1
        · simp
          intro j hj
          simp only [T, ht.2 j hj]
          exact (hTV j (ht.2 j hj)).choose_spec.choose_spec.2.2.1.1
      · let J (v : Fin n → X) (hv : v ∈ t) : I :=
          (hglue_in_cover v (ht.2 v hv)).choose
        -- go from J to a Finset I by taking image of t under it somehow

        sorry



    let N := fun x : X =>
      if hx : x ∈ K then (hnhd_fin_cover x hx).choose else ∅
    -- Defines a choice function that takes an x ∈ X to a neighbourhood of x s.t. N(x)×Kⁿ is finitely coverable

    have hN : ∀ x ∈ K, (IsOpen (N x) ∧ x ∈ N x) ∧ (∃ (t : Finset I), (f_prod glue) '' (N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K})
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
