module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology

private theorem eventually_on_compact_spatial_set {M : Type*} [TopologicalSpace M]
    {K : Set M} (compact : IsCompact K) {O : Set (ℝ × M)}
    (localAtZero : ∀ x ∈ K, O ∈ 𝓝 ((0:ℝ),x)) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ x ∈ K, (s,x) ∈ O := by
  have inside : ({0} : Set ℝ) ×ˢ K ⊆ interior O := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    have eq : s=0 := hs
    rw [eq]
    exact mem_interior_iff_mem_nhds.mpr (localAtZero x hx)
  obtain ⟨U,V,ou,_,zu,kv,inc⟩ := generalized_tube_lemma isCompact_singleton compact isOpen_interior inside
  filter_upwards [ou.mem_nhds (zu (mem_singleton _))] with s hs
  exact fun x hx => interior_subset (inc ⟨hs,kv hx⟩)

/-- A compact core meeting its image prevents a reflected parameter from
escaping. Only the central slice is proper. The nearby slices need no
uniform properness and their homeomorphisms have no time regularity. -/
theorem compact_core_confines_reflected_parameter {M E : Type*}
    [TopologicalSpace M] [MetricSpace E] [ProperSpace E] (o : E)
    {X : ℝ → M → E} (joint : ∀ z, ContinuousAt (fun a : ℝ × M => X a.1 a.2) (0,z))
    (proper : IsProperMap (X 0)) {R : E → E} (contR : Continuous R)
    {p : M} {K : Set M} (compact : IsCompact K) (conn : IsConnected K) (pin : p ∈ K)
    (meets : ∀ d : M ≃ₜ M, ∃ a ∈ K, d a ∈ K) (d : ℝ → M ≃ₜ M)
    (acts : ∀ᶠ s in 𝓝 (0:ℝ), ∀ x, X s (d s x) = R (X s x)) :
    ∃ H : Set M, IsCompact H ∧ ∀ᶠ s in 𝓝 (0:ℝ), d s p ∈ H := by
  obtain ⟨B,hB⟩ := (compact.image (contR.comp proper.continuous)).isBounded.subset_ball o
  have upper : ∀ᶠ s in 𝓝 (0:ℝ), ∀ a ∈ K, R (X s a) ∈ ball o B :=
    eventually_on_compact_spatial_set compact (fun a ha => (contR.continuousAt.comp (joint a)).eventually
      (isOpen_ball.mem_nhds (hB ⟨a,ha,rfl⟩)))
  obtain ⟨L,less,inL⟩ := (compact.image proper.continuous).isBounded.subset_ball_lt B o
  let level := X 0 ⁻¹' sphere o L
  have compactLevel : IsCompact level := proper.isCompact_preimage (isCompact_sphere _ _)
  have barrier : ∀ᶠ s in 𝓝 (0:ℝ), ∀ z ∈ level, B < dist (X s z) o := by
    apply eventually_on_compact_spatial_set compactLevel
      (O := {a : ℝ × M | B < dist (X a.1 a.2) o})
    intro z hz
    have far : B < dist (X 0 z) o := (show dist (X 0 z) o = L from hz).symm ▸ less
    have dc : ContinuousAt (fun a : ℝ × M => dist (X a.1 a.2) o) (0,z) :=
      (joint z).dist continuousAt_const
    exact dc.eventually (Ioi_mem_nhds far)
  refine ⟨X 0 ⁻¹' closedBall o L,proper.isCompact_preimage (isCompact_closedBall _ _),?_⟩
  filter_upwards [upper,barrier,acts] with s low high reflect
  obtain ⟨a,ha,da⟩ := meets (d s)
  change dist (X 0 (d s p)) o ≤ L
  by_contra! bad
  have first : dist (X 0 (d s a)) o < L := inL ⟨_,da,rfl⟩
  have contRadius : Continuous (fun z : M => dist (X 0 (d s z)) o) :=
    (proper.continuous.comp (d s).continuous).dist continuous_const
  have sweep := conn.isPreconnected.intermediate_value ha pin contRadius.continuousOn
  obtain ⟨z,hz,eq⟩ := sweep (show L ∈ Icc (dist (X 0 (d s a)) o) (dist (X 0 (d s p)) o)
    from ⟨first.le,bad.le⟩)
  have far := high (d s z) eq
  rw [reflect z] at far
  exact (not_lt_of_ge far.le) (low z hz)

/-- A confined lift of a continuous moving spatial point is continuous
at zero if its central position has a unique central preimage. -/
theorem continuousAt_of_compact_moving_preimage {M E : Type*} [TopologicalSpace M]
    [TopologicalSpace E] [T2Space E] {X : ℝ → M → E} {r : ℝ → M} {y : ℝ → E}
    (joint : ∀ z, ContinuousAt (fun a : ℝ × M => X a.1 a.2) (0,z)) (cy : ContinuousAt y 0)
    (inj : Function.Injective (X 0)) (track : ∀ᶠ s in 𝓝 (0:ℝ), X s (r s)=y s)
    {H : Set M} (compact : IsCompact H) (confined : ∀ᶠ s in 𝓝 (0:ℝ), r s ∈ H) :
    ContinuousAt r 0 := by
  apply _root_.tendsto_nhds.mpr
  intro U ou base
  have reject : ∀ᶠ s in 𝓝 (0:ℝ), ∀ z ∈ H ∩ Uᶜ, X s z ≠ y s := by
    apply eventually_on_compact_spatial_set (compact.inter_right ou.isClosed_compl)
      (O := {a : ℝ × M | X a.1 a.2 ≠ y a.1})
    intro z hz
    have different : X 0 z ≠ y 0 := by
      intro eq
      apply hz.2
      rw [inj (eq.trans track.self_of_nhds.symm)]
      exact base
    have pair : ContinuousAt (fun a : ℝ × M => (X a.1 a.2,y a.1)) (0,z) :=
      (joint z).prodMk (cy.comp (f := (Prod.fst : ℝ × M → ℝ)) (x := ((0:ℝ),z))
        continuous_fst.continuousAt)
    have op : IsOpen {a : E × E | a.1 ≠ a.2} := isOpen_ne_fun continuous_fst continuous_snd
    exact pair.eventually (op.mem_nhds different)
  filter_upwards [confined,track,reject] with s hs hit excluded
  by_contra no
  exact excluded (r s) ⟨hs,no⟩ hit

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_core_confines_reflected_parameter
#print axioms TwoAxisHelicoid.continuousAt_of_compact_moving_preimage
