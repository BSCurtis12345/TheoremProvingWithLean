import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import TheoremProvingWithLean.Topology.Covers

set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.commandStart false

/-
Potential polishing to be done:
· Change to use Set.univ.pi instead of annoying definitions
· Get rid of W inside hnhd_fin_cover and only use J throughout
-/

namespace ProductSpaces

open Covers

variable {X : Type} --[TopologicalSpace X]

-- Defines a function which takes a "curried" function - i.e. one taking one arg at a time - and changes it into a on a product
def uncurry (f : α → β → γ) : α × β → γ :=
  fun p => f p.1 p.2

-- For each v ∈ Xⁿ⁺¹, define a 'tail' (the last n co-ordinates)
def tail (v : Fin (n + 1) → X) : Fin n → X :=
  fun i => v (i.succ)

-- Define a function that glues some x ∈ X to w ∈ Xⁿ
def glue (x : X) (w : Fin n → X) : Fin (n+1) → X :=
  fun k =>
    match k with
    | ⟨0, _⟩     => x
    | ⟨m+1, hk⟩ => w ⟨m, Nat.lt_of_succ_lt_succ hk⟩

section lemmas

variable {ι : Type} {U : ι → Set (Fin (n+1) → X)} {K : Set X}


lemma glue_in_cover (hcover : {v : Fin (n+1) → X | ∀ i, v i ∈ K} ⊆ ⋃ i, U i) :
  ∀ x ∈ K, ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, ∃ j, glue x v ∈ U j := by
-- For v ∈ Kⁿ, ∃ Uⱼ ∈ U s.t. (x,v) ∈ Uⱼ.
  intros x hx v hv -- Let v ∈ Kⁿ
  apply in_elt_cover hcover -- If we can show (x,v) ∈ Kⁿ⁺¹, it is in the cover

  -- Simplify to that for to each co-ordinate k (with hk : k < n+1), (x,v)ₖ ∈ K
  simp; intro i; rcases i with ⟨k, hk⟩

  -- The zero and successor cases both follow immediately from definition of glue and assumptions on x and v
  cases k using Nat.casesOn with
  | zero => -- k = 0
      simp [glue]
      exact hx
  | succ m => -- k = m+1
      simp [glue]
      simp at hv; exact hv ⟨m, Nat.lt_of_succ_lt_succ hk⟩
  done

variable [TopologicalSpace X]

lemma exists_nhd_fin_cover_prod
  (hK : IsCompact K) (hNonempty : K.Nonempty)
  (hKn : IsCompact {v : Fin n → X | ∀ (i : Fin n), v i ∈ K}) :
  ∀ x ∈ K, ∃ (Nx : Set X), ( (IsOpen Nx ∧ x ∈ Nx) ∧
  (∃ (t : Finset ι),
  (uncurry glue) '' (Nx ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) ⊆ ⋃ i ∈ t, U i)) := by

  intro x hx


  sorry
  done

end lemmas

variable [TopologicalSpace X]

theorem IsCompact_pow_compact {K : Set X} (hK : IsCompact K) (hNonempty : K.Nonempty) :
  ∀ n : ℕ, IsCompact {v : Fin n → X | ∀ i, v i ∈ K} := by
  /-
  Proves that for any (non-empty) compact K in X, Kⁿ is compact in Xⁿ w.r.t. the product (pi in mathlib) topology.

  Mathlib results used:
  · isCompact_iff_finite_subcover : proves that Mathlib definition for a compact set is equivalent to definition using open coverings
  · isOpen_pi_iff' :
      This results states that a set S is open in a finite product space iff for each of its elements...
      - Every co-ordinate belongs to an open set in the space of the corresponding co-ordinate
      - The product of these (a "box neighbourhood") open sets is a subset of S
      This is not ideal to use unjustified since we want to use either a basis-of-products-of-open-sets or coarsest-topology-making-projections-continuous definition.
      However, from basis definition we get open => box quite simply...
      ...and from the coarsest topology definition we get box => open quite simply.
      Time-permitting, we will come back to this to formalise it ourselves...
      ...but in the interests of progressing elsewhere in the project, it is left as yet unformalised.
  -/
  classical
  intro n
  induction n with -- Prove by induction on n
  | zero => -- Base case : n = 0

    -- Rewrite goal in terms of finite subcover definition, let U be an open cover, indexed over I
    rw [isCompact_iff_finite_subcover]
    intro I U hopen hcover

    -- Define f using .elim0 since Fin 0 is uninhabited, get f in K⁰ and the cover trivially
    simp
    let f : Fin 0 → X := fun i => i.elim0
    have : f ∈ {v | ∀ (i : Fin 0), v i ∈ K} := by simp
    have : f ∈ ⋃ i, U i := Set.mem_of_mem_of_subset this hcover

    -- Let i be s.t. f ∈ Uᵢ ∈ U, take {i} as witness to existential
    rcases Set.mem_iUnion.1 this with ⟨i, hi⟩
    refine ⟨{i}, ?_⟩

    -- Next prove by extensionality that the union over {i} = X⁰
    ext v
    constructor
    · intro _ -- First direction is trivial since everything is an element of the universal set
      trivial
    · intro _ -- Get that any element of X⁰ must be equal to f, and since f ∈ Uᵢ, f is in the union
      have hv : v = f := Subsingleton.elim _ _
      subst hv
      simp [hi]

  | succ n ih => -- Induction step : n+1

    -- Rewrite the goal in terms of finite subcover defintion, take an open cover U, indexed over I
    rw [isCompact_iff_finite_subcover]
    intro I U hopen hcover
    rw [isCompact_iff_finite_subcover] at hK -- Rewrite goal in terms of finite subcover definition


    have hnhd_fin_cover : ∀ x ∈ K, ∃ (𝓝ₓ : Set X), ( (IsOpen 𝓝ₓ ∧ x ∈ 𝓝ₓ) ∧
      (∃ (t : Finset I), (uncurry glue) '' (𝓝ₓ ×ˢ {v : Fin n → X | ∀ i, v i ∈ K})
        ⊆ ⋃ i ∈ t, U i)) := by
    -- For x ∈ K, ∃ an open neighbourhoud 𝓝(x) ⊆ K s.t. 𝓝(x)×Kⁿ can be covered by a finite subfamily of U

      intro x hx -- Let x ∈ K

      have hglue_in_cover : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, ∃ j, glue x v ∈ U j := by
      -- For v ∈ Kⁿ, ∃ Uⱼ ∈ U s.t. (x,v) ∈ Uⱼ.

        intro v hv -- Let v ∈ Kⁿ
        apply in_elt_cover hcover -- If we can show (x,v) ∈ Kⁿ⁺¹, it is in the cover

        -- Simplify to that for to each co-ordinate k (with hk : k < n+1), (x,v)ₖ ∈ K
        simp; intro i; rcases i with ⟨k, hk⟩

        -- The zero and successor cases both follow immediately from definition of glue and assumptions on x and v
        cases k using Nat.casesOn with
        | zero => -- k = 0
            simp [glue]
            exact hx
        | succ m => -- k = m+1
            simp [glue]
            simp at hv; exact hv ⟨m, Nat.lt_of_succ_lt_succ hk⟩

      -- Define a choice function W taking v ∈ Kⁿ to a cover element containing (x,v), or ∅ if v ∉ Kⁿ
      let W := fun v : Fin n → X =>
        if hv : v ∈ {v : Fin n → X | ∀ i, v i ∈ K} then U (hglue_in_cover v hv).choose
        else ∅

      -- Get that (x,v) ∈ W(v) for all v
      have hW : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, glue x v ∈ W v := by
        intro v hv
        simp only [W]
        simpa [W, hv] using (hglue_in_cover v hv).choose_spec

      -- Get that W(v) is open for all v
      have hWopen : ∀ (v : Fin n → X), IsOpen (W v) := by
        intro v
        simp only [W]
        by_cases hv : v ∈ {v | ∀ (i : Fin n), v i ∈ K}
        · simp [hv, hopen] -- In this case W(v) is an element of an open cover so open
        · simp [hv] -- Otherwise W(v) = ∅ also open

      have hTV : ∀ v ∈ {v : Fin n → X | ∀ i, v i ∈ K}, ∃ Tᵥ, ∃ Vᵥ,
        IsOpen Tᵥ ∧ IsOpen Vᵥ ∧ (x,v) ∈ Tᵥ ×ˢ Vᵥ ∧ (uncurry glue) '' (Tᵥ ×ˢ Vᵥ) ⊆ W v := by
      -- Proves ∀ v ∈ Kⁿ, ∃ open neighbourhoods Tᵥ of x, Vᵥ of v s.t. Tᵥ×Vᵥ ⊆ W(v)

        intro v hv -- Let v ∈ Kⁿ
        specialize hWopen v -- W(v) is open

        -- Rewrite that W(v) in terms of "box neighbourhoods" (see theorem preamble)
        rw [isOpen_pi_iff'] at hWopen

        -- Get that there is a family of open sets whose product contains (x,v) and is contained in W(v)
        have hWopen' : glue x v ∈ W v → ∃ u, (∀ (a : Fin (n + 1)), IsOpen (u a) ∧ glue x v a ∈ u a)
          ∧ Set.univ.pi u ⊆ W v := hWopen (glue x v)
        replace hWopen' : ∃ u, (∀ (a : Fin (n + 1)), IsOpen (u a) ∧ glue x v a ∈ u a) ∧ Set.univ.pi u ⊆ W v := by
          exact hWopen' (hW v hv)

        obtain ⟨u, hu⟩ := hWopen' -- Take a family of sets u as a witness to the above
        have hu0 : IsOpen (u 0) ∧ glue x v 0 ∈ u 0 := hu.1 0 -- Get that u(0) is open and x ∈ u(0)

        have hu_tail : IsOpen {w : Fin n → X | ∀ (a : Fin n), w a ∈ u a.succ} ∧ tail (glue x v) ∈ {w : Fin n → X | ∀ (a : Fin n), w a ∈ u a.succ} := by
        -- Proves that the product of the last n co-ordinates of u is open and contains v

          constructor
          · rw [isOpen_pi_iff'] -- For the openness part, rewrite in terms of "box neighbhourhoods"
            intro f hf -- Let f ∈ Π 0 < i < n+1, u(i) (prod of last n co-ord of u)

            -- For simplicity, define u_tail a new family of sets, being the sets at the last n co-ords of u
            let u_tail : (Fin n) → Set X :=
              fun i => u i.succ

            use u_tail -- Take u_tail as a witness to the existential in the goal - the "box neighbourhood" of f
            constructor -- Break the goal into two parts
            · -- First part: ∀ a < n, u_tail(a) is open and f(a) ∈ u_tail(a)
              intro a -- Let a < n

              -- Change the hu hypothesis from openness of W(v) into its two conjuncts
              rcases hu with ⟨hu_all, hu_sub⟩

              constructor -- Split the goal up again
              · -- Get for every a, u(a+1) is open, then simplify
                have : IsOpen (u a.succ) := (hu_all a.succ).1
                simp at this
                exact this
              · -- Again, move things to be in terms of u, then simp with u_tail
                have hf' : ∀ i : Fin n, f i ∈ u i.succ := by simpa using hf
                have : f a ∈ u a.succ := hf' a
                dsimp [u_tail]
                exact this

            · -- Second part: product over u_tail is contained essentially itself - just involves unpacking the two different definitions
              intro w hw
              change ∀ a : Fin n, w a ∈ u a.succ
              have hw' : ∀ a : Fin n, w a ∈ u_tail a := by
                simpa [u_tail] using hw
              intro a
              simpa [u_tail] using hw' a

          · -- Now we just have the contains v part - again just an unpacking of definitions
            change ∀ a : Fin n, tail (glue x v) a ∈ u a.succ
            intro a
            simp [tail]
            exact (hu.1 a.succ).2

        -- Take u(0) as witness to Tᵥ and u_tail as witness to Vᵥ
        use u 0
        use {w : Fin n → X | ∀ (a : Fin n), w a ∈ u a.succ}
        refine And.intro hu0.1 ⟨hu_tail.1, ?_⟩ -- Openness of the two comes straight from the hypotheses we just got
        constructor -- Break apart goal
        · -- First part: (x,v) ∈ u(0)×u_tail
          constructor
          · -- x ∈ u(0) follows simply from hu0 and definition of glue
            have : glue x v 0 ∈ u 0 := hu0.2
            simpa [glue] using this
          · -- Similar for v ∈ u_tail by also unpacking definiton of tail
            have : tail (glue x v) ∈ {w | ∀ a : Fin n, w a ∈ u a.succ} := hu_tail.2
            have hcoords : ∀ a : Fin n, tail (glue x v) a ∈ u a.succ := by
              simpa using this
            simpa using hcoords

        · -- Second part: u(0)×u_tail ⊆ W(v)
          intro y hy -- Let y ∈ u(0)×u_tail

          -- Set y as a glue of some x' in u(0) and w in u_tail, i.e. let y=(x',w)
          rcases hy with ⟨⟨x', w⟩, hmem, rfl⟩
          rcases hmem with ⟨hx', hw'⟩

          -- Change w indexing in terms of u
          have hcoords : ∀ a : Fin n, w a ∈ u a.succ := by
            simpa using hw'

          -- Get that (x',w) ∈ product over u
          have hpi : uncurry glue (x', w) ∈ Set.univ.pi u := by
            refine Set.mem_univ_pi.2 ?_ -- Change goal to every index i of (x',w) in u(i)
            intro k -- Let k < n+1
            refine Fin.cases ?h0 ?_ k
            · simpa [glue] using hx' -- Case k=0 follows from hx' and glue definition
            · intro i -- Rejigging of co-ords of w before solves successor case
              have : w i ∈ u i.succ := hcoords i
              simpa [glue] using this

          -- Close goal by subset transitivty
          exact hu.2 hpi

      -- Define a choice function taking v ∈ Kⁿ to a Vᵥ as in hTV, and to ∅ if v ∉ Kⁿ
      let V := fun v : Fin n → X =>
        if hv : v ∈ {w | ∀ (i : Fin n), w i ∈ K} then
          (hTV v hv).choose_spec.choose
        else ∅

      -- Define a choice function taking v ∈ Kⁿ to a Tᵥ as in hTV, and to ∅ if v ∉ Kⁿ
      let T := fun v : Fin n → X =>
        if hv : v ∈ {w | ∀ (i : Fin n), w i ∈ K} then
          (hTV v hv).choose
        else ∅

      have hV_open_cover : (∀ v, IsOpen (V v)) ∧ {w | ∀ (i : Fin n), w i ∈ K} ⊆ ⋃ v, (V v) := by
      -- Proves that {V(v)}ᵥ is an open cover of Kⁿ
        constructor
        · -- Openness part
          intro v -- Take any v

          -- Complete by cases: if v ∈ Kⁿ, V(v) open by defintion from hTV, otherwise V(v) = ∅ also open
          by_cases hv : v ∈ {w | ∀ (i : Fin n), w i ∈ K}
          · simp only [V, hv]
            exact (hTV v hv).choose_spec.choose_spec.2.1
          · simp only [V, hv]
            simp

        · -- Cover part
          intro w hw -- Let w ∈ Kⁿ
          rw [Set.mem_iUnion] -- Change goal to w in an element of the cover
          use w -- Take w as witness since by definition w ∈ V(w)
          simp only [V, hw]
          exact (hTV w hw).choose_spec.choose_spec.2.2.1.2

      have hV_fin_cover : ∃ (t : Finset (Fin n → X)), {w | ∀ (i : Fin n), w i ∈ K} ⊆ ⋃ i ∈ t, V i ∧ ∀ v ∈ t, v ∈ {w : Fin n → X | ∀ (i : Fin n), w i ∈ K} := by
      -- Proves there is a finite subcover of {V(v)}ᵥ covering Kⁿ, with indexes only beloning to Kⁿ

        have : ∃ (t : Finset (Fin n → X)), {w | ∀ (i : Fin n), w i ∈ K} ⊆ ⋃ i ∈ t, V i := by
        -- Proves that there is a finite subcover of {V(v)}ᵥ (indexes not necessarily in Kⁿ)
        -- Follows from induction hypothesis rewritten in terms of finite subcovers
          rw [isCompact_iff_finite_subcover] at ih
          exact ih V hV_open_cover.1 hV_open_cover.2

        -- Take t' as the index set for finite subcover with indexes not necessarily in Kⁿ
        obtain ⟨t',ht'⟩ := this

        -- Let t = t' ∩ Kⁿ, take this as witness to goal
        -- This works because for i ∉ Kⁿ, V(i) = ∅ so removing it doesn't remove any elements from the union
        let t := t'.filter (fun v => v ∈ {w : Fin n → X | ∀ (i : Fin n), w i ∈ K})
        use t

        constructor
        · -- First part: Kⁿ covered by cover indexed over t
          intro v hv -- Let v ∈ Kⁿ

          -- Get that v ∈ V(i), for some i ∈ t', take j to be a witness, use j for the goal
          have hv' : ∃ i ∈ t', v ∈ V i := by simpa using (Set.mem_of_mem_of_subset hv ht')
          obtain ⟨j, hj⟩ := hv'
          simp; use j

          -- Need that j ∈ t (so j ∈ Kⁿ) and v ∈ V(j); the latter follows by definition of j
          refine And.intro ?_ hj.2
          simp [t]
          refine And.intro hj.1 ?_

          -- Prove j ∈ Kⁿ by contradiction
          by_contra hj_neg
          replace hj_neg : j ∉ {w | ∀ (i : Fin n), w i ∈ K} := by simpa using hj_neg
          have hVj_empty : V j = ∅ := by simp only [V, hj_neg]; simp -- V(j) = ∅ by definition of V
          rw [← Set.mem_empty_iff_false v] -- v ∈ ∅ is always false
          simpa [hVj_empty] using hj.2
        · -- Second part: t ⊆ Kⁿ follows from definition of t
          intro v hv
          exact (Finset.mem_filter.mp (by simpa [t] using hv)).2

      obtain ⟨t, ht⟩ := hV_fin_cover -- Take t as witness to above

      use ⋂ i ∈ t, T i -- Use as our neighbourhood of x, the intersection of T(i)'s over t
      constructor -- Break apart goal
      · constructor
        · -- First part: the intersection is open
          apply isOpen_biInter_finset -- Intersection is finite so suffices each T(i), i ∈ t open
          intro j hj -- Let j ∈ t

          -- Follows from definition of T in hTV that T(i) open for i ∈ Kⁿ
          simp only [T, ht.2 j hj]
          exact (hTV j (ht.2 j hj)).choose_spec.choose_spec.1
        · -- Second part: x is in the intersection
          -- Show from definition of T from hTV that x ∈ T j for j ∈ Kⁿ
          simp
          intro j hj
          simp only [T, ht.2 j hj]
          exact (hTV j (ht.2 j hj)).choose_spec.choose_spec.2.2.1.1

      · -- Third part: there is a finite subcover of U covering the intersection crossed with Kⁿ
        -- Define a choice function J taking an index from t to a corresponding index in I
        -- This does the same as W did before, but gives the index j of the chosen U(j), rather than the set itself
        -- Could possibly change this to have no W defined, and just use U (J ·) throughout?
        let J (v : Fin n → X) : I :=
          if hv : v ∈ t then (hglue_in_cover v (ht.2 v hv)).choose
          else -- For v ∉ t, we take the index given by an arbitrary (c,c,...) ∈ Kⁿ (can do since K non-empty)
            let c : Fin n → X := fun i => hNonempty.choose
            have : c ∈ {w : Fin n → X | ∀ i, w i ∈ K} := by
              intro j
              simp [c]
              exact hNonempty.choose_spec
            (hglue_in_cover c this).choose

        -- Use s, the image of t under J, as our finite index set in I for our finite subcover of U
        let s := t.image J -- Automatically get Finset type for s by using Finset.image
        use s

        -- Unpack the definition of uncurry, intro on all bound variables and hypotheses
        simp [uncurry]
        intros x' hx' y hy

        -- Now need to show that (x',y) is in a cover element of the finite subcover indexed by s
        -- Change s back into definition in terms of t and J
        simp [s]

        have : ∃ a ∈ t, y ∈ V a := by
        -- Proves that ∃ a ∈ t s.t. y ∈ V(a)
          -- First get that y ∈ Kⁿ
          have : y ∈ {w | ∀ (i : Fin n), w i ∈ K} := by simp [hy]

          -- Get that y belongs to the union over t of V's, thus belongs to one of the V(i)'s, i ∈ t
          have hyUnion : y ∈ ⋃ i ∈ t, V i := ht.1 this
          rcases Set.mem_iUnion.mp hyUnion with ⟨a, ha⟩
          rcases Set.mem_iUnion.mp ha with ⟨ha_mem_t, hyVa⟩
          exact ⟨a, ha_mem_t, hyVa⟩

        -- Take an a ∈ t s.t. y ∈ V(a) by the above, then use that as witness for the goal
        obtain ⟨a, ha⟩ := this
        use a

        -- a ∈ t by assumption so only remains to show that (x',y) ∈ U (J a)
        refine And.intro ha.1 ?_

        -- Get that x' ∈ t a
        specialize hx' a ha.1

        have : W a = U (J a) := by
        -- Proves that W(a) = U(J(a)) - follows from definitions
        -- As discussed earlier, maybe worth removing definition of W altogether to avoid this extra step
          simp only [W, ht.2 a ha.1]
          simp only [J, ha.1]
          simp

        -- Change goal to that (x',y) ∈ W(a)
        rw [← this]

        -- Get that T(a)×V(a) ⊆ W(a) from definitions as witnesses to hTV
        have : uncurry glue '' T a ×ˢ V a ⊆ W a := by
          simp only [T, V, ht.2 a ha.1]
          exact (hTV a (ht.2 a ha.1)).choose_spec.choose_spec.2.2.2

        -- Finally unpack definition of uncurry in hypothesis, apply it to other hypotheses
        simp [uncurry] at this
        exact this x' hx' y ha.2

    -- Define a choice function that takes an x ∈ X to a neighbourhood of x s.t. N(x)×Kⁿ is finitely coverable
    let N := fun x : X =>
      if hx : x ∈ K then (hnhd_fin_cover x hx).choose else ∅

    -- Prove that the cover property of each neighbourhood N(x) given by the choice function holds
    have hN : ∀ x ∈ K, (IsOpen (N x) ∧ x ∈ N x) ∧ (∃ (t : Finset I), (uncurry glue) '' (N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K})
      ⊆ ⋃ i ∈ t, U i) := by
      intro x hx
      simp only [N, hx]
      exact (hnhd_fin_cover x hx).choose_spec

    have hfin_sub_coverN : ∃ (t : Finset X), K ⊆ ⋃ i ∈ t, N i := by
    -- ∃ a finite subcover of {N(x)}ₓ covering K - follows from compactness
      apply hK -- Applies compactness of K - need now show that {N(x)}ₓ is an open cover
      · -- Openness part
        intro x
        by_cases hx : x ∈ K
        · exact (hN x hx).1.1 -- If x ∈ K, N(x) is open by definition
        · simp [N, hx] -- Otherwise N(x) = ∅ open also
      · -- Cover part
        intro x hx
        simp
        use x
        exact (hN x hx).1.2 -- x ∈ N(x) by definition

    obtain ⟨t₁, ht₁⟩ := hfin_sub_coverN -- Gives a particular finite subcover

    -- Add cartesian product with Kⁿ to the finite subcover hypothesis, then exchanges the union and the product
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

    -- Takes the image under the 'glue' function in the finite subcover hypothesis
    replace ht₁ : (uncurry glue) '' K ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ (uncurry glue) '' ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
      exact Set.image_mono ht₁

    -- Similarly painstaking process as with the product above to exchange the image and union
    replace ht₁ : uncurry glue '' K ×ˢ {v | ∀ (i : Fin n), v i ∈ K} ⊆ ⋃ i ∈ t₁, (uncurry glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} := by
      have : ⋃ i ∈ t₁, (uncurry glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} = (uncurry glue) '' ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
        have : ⋃ i ∈ t₁, (N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) = ⋃ p : {i // i ∈ t₁}, (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this, Set.image_iUnion]
        have : ⋃ i ∈ t₁, (uncurry glue) '' N i ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} = ⋃ p : {i // i ∈ t₁}, (uncurry glue) '' (N p.1 ×ˢ {v : Fin n → X | ∀ i, v i ∈ K}) := by
          simp [Set.iUnion_subtype]
        simp [this]
      rw [this]; exact ht₁

    have hnhd_fin_cover' : ∀ (x : X), ∃ (t : Finset I), (uncurry glue) '' N x ×ˢ {v : Fin n → X | ∀ i, v i ∈ K} ⊆ ⋃ j ∈ t, U j := by
    -- ∀ x ∈ X, there is a finite subcover of U covering N(x)×Kⁿ
      intro x
      by_cases hx : x ∈ K
      · simp only [N, hx]
        exact (hnhd_fin_cover x hx).choose_spec.2 -- If x ∈ K result follows from definition of N by hnhd_fin_cover
      · simp [N, hx] -- Otherwise N(x) = ∅ so the product is empty and trivially covered


    have hnhd_prod_fin_cover : ∃ (t : Finset I), ⋃ i ∈ t₁, uncurry glue '' N i ×ˢ {v | ∀ (i : Fin n), v i ∈ K} ⊆
      ⋃ j ∈ t, U j := by
    -- Proves that the union over t₁ of N(i)×Kⁿ is covering by some finite subcover of U

      -- Defines a choice function T from x ∈ X to some finite subcover of U covering N(x)×Kⁿ
      choose T hT using hnhd_fin_cover'

      refine ⟨t₁.biUnion T, ?_⟩ -- Takes as witness the union over t₁ of T(x)

      -- Unpack subset, set membership and union definitions
      intro v hv
      rcases Set.mem_iUnion.1 hv with ⟨i, hv⟩
      rcases Set.mem_iUnion.1 hv with ⟨hi₁, hAi⟩

      -- Get that v is in a union over some cover T(i) for some i ∈ t₁, unpack further
      have hv' : v ∈ ⋃ j ∈ T i, U j := hT i hAi
      rcases Set.mem_iUnion.1 hv' with ⟨j, hv'⟩
      rcases Set.mem_iUnion.1 hv' with ⟨hjTi, hvUj⟩

      -- Get that j ∈ the union of T's over t₁, close goal since v ∈ U(j)
      have hjt : j ∈ t₁.biUnion T := Finset.mem_biUnion.2 ⟨i, hi₁, hjTi⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjt, hvUj⟩⟩

    -- Take t as a witness to the existential above, get from it that K×Kⁿ is covered by t since K covered by N's
    rcases hnhd_prod_fin_cover with ⟨t, ht⟩
    apply subset_trans ht₁ at ht

    have hglue_eq_Kn : uncurry glue '' K ×ˢ {v | ∀ (i : Fin n), v i ∈ K} = {v | ∀ (i : Fin (n + 1)), v i ∈ K} := by
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
          simp [glue, uncurry]
          exact hxK
        | succ m => -- m = j+1
          simp [glue, uncurry]
          exact hwK ⟨m, Nat.lt_of_succ_lt_succ hj⟩
      · intro hv
        simp; simp at hv
        let w (i : Fin n) : X :=
          v (i.succ)
        use v 0; use w
        constructor; constructor
        · exact hv 0
        · simp [w, hv]
        · simp [uncurry, w]
          ext i
          rcases i with ⟨j,hj⟩
          cases j using Nat.casesOn with
          | zero => simp [glue]
          | succ m => simp [glue]
    refine ⟨t, ?_⟩
    simpa [hglue_eq_Kn] using ht

  done

end ProductSpaces
