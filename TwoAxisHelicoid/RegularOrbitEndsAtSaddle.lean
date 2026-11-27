import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Set Filter Function Topology
open scoped Topology

/-- A nonperiodic orbit in a partition by open real flow orbits is
properly embedded in the regular locus. -/
theorem nonperiodic_open_orbit_closed_embedding {Y : Type*} [TopologicalSpace Y]
    (Φ : ℝ → Y → Y) (start : ∀ y, Φ 0 y=y) (add : ∀ s t y, Φ (s+t) y=Φ s (Φ t y))
    (cont : ∀ y, Continuous (fun t => Φ t y)) (op : ∀ y, IsOpenMap (fun t => Φ t y))
    (x : Y) (noReturn : ∀ t>0, Φ t x≠x) : IsClosedEmbedding (fun t => Φ t x) := by
  let A := range (fun t => Φ t x)
  have apart {s t : ℝ} (lt : s<t) (eq : Φ t x=Φ s x) : False := by
    apply noReturn (t-s) (sub_pos.mpr lt)
    rw [sub_eq_neg_add,add,eq,← add,neg_add_cancel,start]
  have inj : Injective (fun t => Φ t x) := by
    intro s t eq
    rcases lt_trichotomy s t with l|same|r
    · exact (apart l eq.symm).elim
    · exact same
    · exact (apart r eq).elim
  have openC : IsOpen Aᶜ := isOpen_iff_forall_mem_open.mpr (by
    intro y outside
    refine ⟨range (fun t => Φ t y),?_,(op y).isOpen_range,0,start y⟩
    rintro _ ⟨t,rfl⟩ ⟨s,eq⟩
    apply outside
    refine ⟨(-t)+s,?_⟩
    change Φ ((-t)+s) x=y
    change Φ s x=Φ t y at eq
    rw [add,eq,← add,neg_add_cancel,start])
  exact ⟨(IsOpenEmbedding.of_continuous_injective_isOpenMap (cont x) inj (op x)).isEmbedding,
    isOpen_compl_iff.mp openC⟩

/-- In a compact level, a proper real traversal of the complement of
one point approaches that point at both temporal ends. -/
theorem proper_orbit_two_ends_at_missing_point {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (p : Y) (γ : ℝ → ({p}ᶜ : Set Y)) (prop : IsProperMap γ) :
    Tendsto (fun t => (γ t).1) atTop (𝓝 p) ∧ Tendsto (fun t => (γ t).1) atBot (𝓝 p) := by
  have compact (U : Set Y) (op : IsOpen U) (mem : p∈U) :
      IsCompact ((fun t => (γ t).1) ⁻¹' Uᶜ) := by
    apply prop.isCompact_preimage (K:=(Subtype.val : ({p}ᶜ : Set Y) → Y) ⁻¹' Uᶜ)
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [Subtype.image_preimage_coe,inter_eq_right.mpr (show Uᶜ⊆{p}ᶜ from
      compl_subset_compl.mpr (singleton_subset_iff.mpr mem))]
    exact op.isClosed_compl.isCompact
  constructor
  · apply tendsto_nhds.mpr
    intro U oU mem
    obtain ⟨B,upper⟩ := (compact U oU mem).bddAbove
    filter_upwards [eventually_gt_atTop B] with t gt
    by_contra outside
    exact (not_le_of_gt gt) (upper (show t∈(fun r => (γ r).1) ⁻¹' Uᶜ from outside))
  · apply tendsto_nhds.mpr
    intro U oU mem
    obtain ⟨B,lower⟩ := (compact U oU mem).bddBelow
    filter_upwards [eventually_lt_atBot B] with t lt
    by_contra outside
    exact (not_le_of_gt lt) (lower (show t∈(fun r => (γ r).1) ⁻¹' Uᶜ from outside))

/-- On the connected level component of an isolated singular point,
every other regular orbit returns to that same singular point at both
ends. A periodic orbit would be a disjoint clopen circle component. -/
theorem regular_orbit_in_singular_component {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (p : Y) (Φ : ℝ → ({p}ᶜ : Set Y) → ({p}ᶜ : Set Y)) (start : ∀ y, Φ 0 y=y)
    (add : ∀ s t y, Φ (s+t) y=Φ s (Φ t y))
    (cont : ∀ y, Continuous (fun t => Φ t y)) (op : ∀ y, IsOpenMap (fun t => Φ t y))
    (x : ({p}ᶜ : Set Y)) (same : x.1∈connectedComponent p) :
    IsClosedEmbedding (fun t => Φ t x) ∧
      Tendsto (fun t => (Φ t x).1) atTop (𝓝 p) ∧ Tendsto (fun t => (Φ t x).1) atBot (𝓝 p) := by
  let f := fun t => (Φ t x).1
  have never (t : ℝ) (pos : 0<t) (ret : Φ t x=x) : False := by
    have per : Periodic f t := fun s => by dsimp only [f];rw [add,ret]
    have cc : IsClosed (range f) :=
      (per.compact_of_continuous pos.ne' (continuous_subtype_val.comp (cont x))).isClosed
    have oo : IsOpen (range f) := (isClosed_singleton.isOpen_compl.isOpenMap_subtype_val.comp (op x)).isOpen_range
    have pMiss : p∉range f := by
      rintro ⟨s,eq⟩
      exact (Φ s x).2 eq
    have avoids := (show IsClopen (range f) from ⟨cc,oo⟩).compl.connectedComponent_subset pMiss same
    exact avoids ⟨0,congrArg Subtype.val (start x)⟩
  have emb := nonperiodic_open_orbit_closed_embedding Φ start add cont op x never
  exact ⟨emb,proper_orbit_two_ends_at_missing_point p _ emb.isProperMap⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonperiodic_open_orbit_closed_embedding
#print axioms TwoAxisHelicoid.regular_orbit_in_singular_component
