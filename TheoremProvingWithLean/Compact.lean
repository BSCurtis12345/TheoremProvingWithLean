import Mathlib.Topology.Basic
import Mathlib.Data.Set.Finite.Basic

open Set

/-
    - `TopologicalSpace` typeclass
    - definition of `IsOpen`
    - notation for preimages: `f ⁻¹' U`
    - `Finset`
    - conversion `(V : Set (Set X))`
    - `Finset.image`, `Finset.mem_image`, `Finset.attach`
-/
variable {X Y : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]

def myCompact (K : Set X) : Prop :=
  ∀ (U : Set (Set X)),
    (∀ u, u ∈ U → IsOpen u) →
    K ⊆ sUnion U →
    ∃ (V : Finset (Set X)),
      (∀ v, v ∈ V → v ∈ U) ∧
      K ⊆ sUnion (V : Set (Set X))

def myContinuous (f : X → Y) : Prop :=
  ∀ W : Set Y, IsOpen W → IsOpen (f ⁻¹' W)

/-- Given an open cover `W` of `f(K)`, we construct an open cover `U` of `K`
    by taking preimages: `U = {f⁻¹(w) | w ∈ W}`. -/
lemma preimage_open_cover
  {f : X → Y} (hf : myContinuous f)
  {K : Set X} {W : Set (Set Y)}
  (hW_open : ∀ w, w ∈ W → IsOpen w)
  (hCover : f '' K ⊆ sUnion W) :
  ∃ U : Set (Set X),
    (∀ u, u ∈ U → IsOpen u) ∧
    K ⊆ sUnion U ∧
    (∀ u ∈ U, ∃ w ∈ W, u = f ⁻¹' w) :=
by
  classical
  let U : Set (Set X) := { s | ∃ w ∈ W, s = f ⁻¹' w }

  have hU_open : ∀ u, u ∈ U → IsOpen u :=
  by
    intro u hu
    rcases hu with ⟨w, hwW, rfl⟩
    exact hf w (hW_open w hwW)

  have hKU : K ⊆ sUnion U :=
  by
    intro x hxK
    have hx_fx : f x ∈ f '' K := ⟨x, hxK, rfl⟩
    have hxW : f x ∈ sUnion W := hCover hx_fx
    rcases hxW with ⟨w, hwW, hx_in_w⟩
    refine ⟨f ⁻¹' w, ?_, ?_⟩
    · exact ⟨w, hwW, rfl⟩
    · exact hx_in_w

  refine ⟨U, hU_open, hKU, ?_⟩
  intro u huU
  rcases huU with ⟨w, hwW, rfl⟩
  exact ⟨w, hwW, rfl⟩

lemma finite_subcover
  {K : Set X} (hK : myCompact K)
  {U : Set (Set X)}
  (hU_open : ∀ u, u ∈ U → IsOpen u)
  (hKU : K ⊆ sUnion U) :
  ∃ V : Finset (Set X),
    (∀ v, v ∈ V → v ∈ U) ∧
    K ⊆ sUnion (V : Set (Set X)) :=
hK U hU_open hKU


lemma image_subcover
  {f : X → Y} {K : Set X}
  {V : Finset (Set X)} {W : Set (Set Y)}
  (hMatch : ∀ v ∈ V, ∃ w ∈ W, v = f ⁻¹' w)
  (hV_cover : K ⊆ sUnion (V : Set (Set X))) :
  ∃ W0 : Finset (Set Y),
    (∀ w, w ∈ W0 → w ∈ W) ∧
    f '' K ⊆ sUnion (W0 : Set (Set Y)) :=
by
  classical
  choose w hwW hw_eq using hMatch

  let W0 : Finset (Set Y) := V.attach.image (fun v => w v.1 v.2)

  have hW0_W : ∀ t ∈ W0, t ∈ W :=
  by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨v, hvV, rfl⟩
    exact hwW v.1 v.2

  have hCover_image : f '' K ⊆ sUnion (W0 : Set (Set Y)) :=
  by
    intro y hy
    rcases hy with ⟨x, hxK, rfl⟩
    have hxV : x ∈ sUnion (V : Set (Set X)) := hV_cover hxK
    rcases hxV with ⟨v, hvV, hxv⟩
    have hv_eq : v = f ⁻¹' w v (by exact hvV) := hw_eq v hvV
    have hx_pre : x ∈ f ⁻¹' w v (by exact hvV) := by simpa [hv_eq] using hxv
    have hv_in_W0 : w v (by exact hvV) ∈ W0 :=
      by
        exact Finset.mem_image.mpr ⟨⟨v, hvV⟩, by simp, rfl⟩
    exact ⟨_, hv_in_W0, hx_pre⟩

  exact ⟨W0, hW0_W, hCover_image⟩


/-- A continuous image of a compact set is compact (beginner version). -/
theorem myCompact_image
  {f : X → Y} (hf : myContinuous f)
  {K : Set X} (hK : myCompact K) :
  myCompact (f '' K) :=
by
  intro W hW hCover
  classical

  -- Build open cover of K from preimages.
  obtain ⟨U, hU_open, hKU, hLift⟩ :=
    preimage_open_cover hf hW hCover

  -- Use compactness of K → finite cover V.
  obtain ⟨V, hV_U, hV_cover⟩ :=
    finite_subcover hK hU_open hKU

  -- Match each v ∈ V to a w ∈ W such that v = f⁻¹(w).
  have hMatch : ∀ v ∈ V, ∃ w ∈ W, v = f ⁻¹' w :=
  by intro v hvV; exact hLift v (hV_U v hvV)

  -- Get a finite cover of f(K)
  rcases image_subcover hMatch hV_cover with ⟨W0, hW0W, hW0cover⟩
  exact ⟨W0, hW0W, hW0cover⟩
