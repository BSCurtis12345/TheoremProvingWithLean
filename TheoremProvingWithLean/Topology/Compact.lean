import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Option
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Sequences

open Set
open scoped Topology

set_option linter.style.emptyLine false

universe u v w
variable {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
variable {s : Set α} {f : α → β}

theorem continuous_image_compact_def
    (hs : IsCompact s) (hf : Continuous f) :
    IsCompact (f '' s) := by
  classical
  -- prove compactness using the open-cover characterization
  refine isCompact_iff_finite_subcover.2 ?_
  intro (ι : Type v) (U : ι → Set β) hUopen hcover

  -- pull back the cover along f
  have hpreopen : ∀ i : ι, IsOpen (f ⁻¹' (U i)) := by
    intro i
    exact hf.isOpen_preimage _ (hUopen i)

  have hprecover : s ⊆ iUnion (fun i : ι => f ⁻¹' (U i)) := by
    intro x hx
    have : f x ∈ iUnion U := by
      apply hcover
      exact ⟨x, hx, rfl⟩
    rcases mem_iUnion.mp this with ⟨i, hfxUi⟩
    exact mem_iUnion.mpr ⟨i, hfxUi⟩

  rcases hs.elim_finite_subcover (fun i : ι => f ⁻¹' (U i)) hpreopen hprecover with ⟨t, ht⟩

  -- push forward the finite subcover
  refine ⟨t, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' := ht hx
  -- rewrite subtype into set union
  simpa [iUnion_subtype] using hx'

#check continuous_image_compact_def


open Set
open scoped Topology
open Filter

variable {α : Type u} [TopologicalSpace α] [T2Space α]

theorem compact_implies_closed {K : Set ℝ} (hK : IsCompact K) : IsClosed K := by
  classical
  by_contra hClosed

  -- From ¬IsClosed K, we get ¬(closure K ⊆ K)
  have h_not_closure : ¬ closure K ⊆ K := by
    intro hsub
    -- If closure K ⊆ K then closure K = K
    have hEq : closure K = K := subset_antisymm hsub subset_closure
    -- But closure K is closed so K is closed
    have hKclosed : IsClosed K := by
      simpa [hEq] using (isClosed_closure : IsClosed (closure K))
    exact hClosed hKclosed

  -- from ¬(closure K ⊆ K) get x ∈ closure K \ K
  have hx_exists : ∃ x, x ∈ closure K ∧ x ∉ K := by
    simpa [Set.subset_def] using h_not_closure
  rcases hx_exists with ⟨x, hx_closure, hx_notin⟩

  -- from x ∈ closure K we build a sequence y n ∈ K with dist < 1/(n+1)

  have hx_closure' :
      ∀ ε : ℝ, 0 < ε → ∃ y, y ∈ K ∧ dist y x < ε := by
    intro ε hε
    have hx' : ∀ ε : ℝ, 0 < ε → ∃ b ∈ K, dist x b < ε := by
      have : x ∈ closure K ↔ ∀ ε : ℝ, 0 < ε → ∃ b ∈ K, dist x b < ε := by
        simp [Metric.mem_closure_iff]
      exact (this.1 hx_closure)

    rcases hx' ε hε with ⟨y, hyK, hyDist⟩
    refine ⟨y, hyK, ?_⟩
    simpa [dist_comm] using hyDist

  have hchoose :
      ∀ n : ℕ, ∃ y, y ∈ K ∧ dist y x < (1 : ℝ) / (n + 1) := by
    intro n
    have hpos : 0 < (1 : ℝ) / (n + 1) := by
      have : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
      exact one_div_pos.2 this
    exact hx_closure' ((1 : ℝ) / (n + 1)) hpos

  classical
  choose y hyK hyDist using hchoose


  -- show y → x using epsilon-N
  have hyT : Tendsto y atTop (nhds x) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    -- choose N such that 1/(N+1) < ε
    obtain ⟨N, hNε⟩ : ∃ N : ℕ, (1 : ℝ) / (N + 1) < ε := by
      simpa using (exists_nat_one_div_lt hε)

    refine ⟨N, ?_⟩
    intro n hn
    -- dist(y n, x) < 1/(n+1) ≤ 1/(N+1) < ε
    have h1 : dist (y n) x < (1 : ℝ) / (n + 1) := hyDist n

    have hle_den : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hpos_den : 0 < (N + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos N)

    have h2 : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (N + 1) := by
      simpa [one_div] using (one_div_le_one_div_of_le hpos_den hle_den)

    have : dist (y n) x < ε :=
      lt_of_lt_of_le h1 (le_trans h2 (le_of_lt hNε))
    simpa using this

  -- all subsequence tend to x
  have hyT_subseq :
      ∀ φ : ℕ → ℕ, StrictMono φ → Tendsto (y ∘ φ) atTop (nhds x) := by
    intro φ hmono
    have hφ : Tendsto φ atTop atTop := hmono.tendsto_atTop
    exact hyT.comp hφ

  -- contradict sequential compactness
  -- extract a convergent subsequence with limit a ∈ K
  rcases hK.tendsto_subseq hyK with ⟨a, haK, φ, hmono, hya⟩
  -- subsequence also tends to x
  have hyx : Tendsto (y ∘ φ) atTop (nhds x) := hyT_subseq φ hmono
  -- uniqueness of limits gives a = x
  have hax : a = x := tendsto_nhds_unique hya hyx
  -- contradiction a ∈ K but x ∉ K
  exact hx_notin (by simpa [hax] using haK)

#check compact_implies_closed


open Set
open scoped Topology

variable {α : Type u} [TopologicalSpace α]

theorem isCompact_of_isClosed_subset
    {K S : Set α}
    (hK : IsCompact K)
    (hS : IsClosed S)
    (hSK : S ⊆ K) :
    IsCompact S := by
  classical

  -- open cover characterisation on S
  refine (@isCompact_iff_finite_subcover _ _ S).2 ?_
  intro ι U hUopen hcover

  -- extend the cover of S to a cover of K
  let V : Option ι → Set α
    | some i => U i
    | none   => Sᶜ

  have hVopen : ∀ i, IsOpen (V i) := by
    intro i; cases i with
    | some i => simpa using hUopen i
    | none =>
      change IsOpen Sᶜ
      simpa using hS.isOpen_compl

  have hVcover : K ⊆ ⋃ i, V i := by
    intro x hxK
    by_cases hxS : x ∈ S
    ·
      rcases mem_iUnion.1 (hcover hxS) with ⟨i, hi⟩
      exact mem_iUnion.2 ⟨some i, hi⟩
    ·
      exact mem_iUnion.2 ⟨none, hxS⟩

  -- compactness of K -> finite subcover
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover V hVopen hVcover

  refine ⟨t.eraseNone, ?_⟩
  intro x hxS

  have hxK : x ∈ K := hSK hxS
  have : x ∈ ⋃ i ∈ t, V i := ht hxK

  rcases mem_iUnion₂.1 this with ⟨i, hi, hxi⟩
  cases i with
  | none =>
      exact (hxi hxS).elim
  | some i =>
      refine mem_iUnion.2 ⟨i, mem_iUnion.2 ?_⟩
      exact ⟨by
        simpa [Finset.mem_eraseNone] using hi,
        hxi⟩

#check isCompact_of_isClosed_subset
