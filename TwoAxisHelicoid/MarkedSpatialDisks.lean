import TwoAxisHelicoid.HoffmanWhiteWindingReduction
import TwoAxisHelicoid.RhombicPrimitivePatches
import TwoAxisHelicoid.RhombicOpenDisk
import TwoAxisHelicoid.RhombicPhysicalAxisPreimages
import TwoAxisHelicoid.TwoAxisComponentSides

namespace TwoAxisHelicoid
open Complex Set Topology

theorem marked_cell_spatial_open_disk {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsEmbedding (harmonicTorusImmersion hX)) (a : ℝ) (ha : a= -2 ∨ a= -1) :
    Nonempty ((X '' rhombicAxisRectangle a t) ≃ₜ Metric.ball (0:ℂ) 1) := by
  let L := rhombicPeriodPair t ht
  let U := rhombicAxisRectangle a t
  let f : U → PuncturedPeriodTorus L := fun z => ⟨periodTorusProjection L z.1,
    fun e => rhombic_horizontal_strip_not_mem ht z.2.2 ((periodTorusProjection_eq_zero L z).mp e)⟩
  have emp : IsEmbedding f := (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp
    (rhombic_axis_cell_topology ht a ha).1.isEmbedding
  have pos : harmonicTorusImmersion hX ∘ f=(fun z : U => X z.1) := funext fun z =>
    harmonicTorusImmersion_projection hX (rhombic_horizontal_strip_not_mem ht z.2.2)
  have ex : IsEmbedding (fun z : U => X z.1) := pos ▸ hE.comp emp
  have range_eq : range (fun z : U => X z.1)=X '' U := by
    ext p
    exact ⟨fun ⟨z,hz⟩ => ⟨z.1,z.2,hz⟩,fun ⟨z,hz,e⟩ => ⟨⟨z,hz⟩,e⟩⟩
  exact ⟨((Homeomorph.setCongr range_eq).symm.trans ex.toHomeomorph.symm).trans (rhombicRectangleOpenDisk a ht)⟩

private theorem component_on_disjoint_sides {E : Type*} [TopologicalSpace E]
    {A B C : Set E} {s : E → ℝ} (cont : Continuous s) (cover : C=A∪B)
    (ha : A⊆{p | 0<s p}) (hb : B⊆{p | s p<0}) (ca : IsSimplyConnected A) :
    ∀ p∈A, connectedComponentIn C p=A := by
  let P := {p | 0<s p}
  let N := {p | s p<0}
  have pos : IsOpen P := isOpen_lt continuous_const cont
  have neg : IsOpen N := isOpen_lt cont continuous_const
  have dis : Disjoint P N := by
    apply disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (show 0<s x from hx) (show s x<0 from hy)
  have sub : A⊆C := cover ▸ subset_union_left
  have signs : C⊆P∪N := cover ▸ union_subset_union ha hb
  intro p hp
  have allpos : connectedComponentIn C p⊆P := isPreconnected_connectedComponentIn.subset_left_of_subset_union
    pos neg dis ((connectedComponentIn_subset C p).trans signs) ⟨p,mem_connectedComponentIn (sub hp),ha hp⟩
  apply Subset.antisymm
  · intro x hx
    rcases cover ▸ connectedComponentIn_subset C p hx with h | h
    · exact h
    · exact (disjoint_left.mp dis (allpos hx) (hb h)).elim
  · exact ca.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn hp sub

/-- The components of the physical surface after the comparison helicoid
is removed are two contractible, congruent spatial sets on opposite
sides. The half-turn is the actual Euclidean half-turn about the z-axis. -/
theorem marked_spatial_complement_of_intersection {t α : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsEmbedding (harmonicTorusImmersion hX))
    (hinter : ∀ z∉(rhombicPeriodPair t ht).lattice, X z∈range (axisRuledHelicoid I α 0) →
      (X z 1=0 ∧ X z 2=0) ∨ (X z 0=0 ∧ X z 1=0)) :
    let A := X '' rhombicAxisRectangle (-2) t
    let B := X '' rhombicAxisRectangle (-1) t
    let C := range (harmonicTorusImmersion hX) \ range (axisRuledHelicoid I α 0)
    let s := axisHelicoidSide I α 0
    C=A∪B ∧ Disjoint A B ∧ ContractibleSpace A ∧ ContractibleSpace B ∧
      (∀ p∈A, connectedComponentIn C p=A) ∧ (∀ p∈B, connectedComponentIn C p=B) ∧
      (fun p : Fin 3 → ℝ => ![-p 0,-p 1,p 2]) '' A=B ∧
      ((A⊆{p | 0<s p} ∧ B⊆{p | s p<0}) ∨ (A⊆{p | s p<0} ∧ B⊆{p | 0<s p})) := by
  let A := X '' rhombicAxisRectangle (-2) t
  let B := X '' rhombicAxisRectangle (-1) t
  let C := range (harmonicTorusImmersion hX) \ range (axisRuledHelicoid I α 0)
  let s := axisHelicoidSide I α 0
  let L := rhombicPeriodPair t ht
  have sides := two_axis_components_on_opposite_sides ht hX hE.injective hinter
  have ss : Continuous s := by change Continuous (axisHelicoidSide I α 0); unfold axisHelicoidSide; fun_prop
  have on (p) : s p=0 ↔ p ∈ range (axisRuledHelicoid I α 0) := axisHelicoidSide_eq_zero_iff (by simp) α 0 p
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro p ha hb
    rcases sides with h | h
    · exact lt_asymm (show 0<s p from h.1 ha) (show s p<0 from h.2 hb)
    · exact lt_asymm (show 0<s p from h.2 hb) (show s p<0 from h.1 ha)
  have cover : C=A∪B := by
    ext p
    constructor
    · rintro ⟨mem,off⟩
      rw [harmonicTorusImmersion_range hX] at mem
      obtain ⟨z,hz,rfl⟩ := mem
      have ax := rhombic_physical_axes_preimages ht hX hE.injective hz
      have noH : ¬ (X z 1=0 ∧ X z 2=0) := fun h => off ((on _).mp (by simp [s,axisHelicoidSide,h.1,h.2]))
      have noV : ¬ (X z 0=0 ∧ X z 1=0) := fun h => off ((on _).mp (by simp [s,axisHelicoidSide,h.1,h.2]))
      have reg : rhombicHorizontalReflection ht (periodTorusProjection L z)≠periodTorusProjection L z ∧
          rhombicVerticalReflection ht (periodTorusProjection L z)≠periodTorusProjection L z :=
        ⟨fun e => noH (ax.2.mpr ((rhombic_horizontal_fixed_projection_height ht z).mp e)),
         fun e => noV (ax.1.mpr ((rhombic_vertical_fixed_projection_iff ht z).mp e))⟩
      have lift {a : ℝ} {w : ℂ} (hw : w∈rhombicAxisRectangle a t) (eq : periodTorusProjection L w=periodTorusProjection L z) :
          X z∈X '' rhombicAxisRectangle a t :=
        ⟨w,hw,(marked_torus_spatial_eq_iff_projection_eq hX hE.injective (rhombic_horizontal_strip_not_mem ht hw.2) hz).mpr eq⟩
      rcases (rhombic_off_axes_iff_rectangle ht _).mp reg with ⟨w,hw,e⟩ | ⟨w,hw,e⟩
      · exact Or.inl (lift hw e)
      · exact Or.inr (lift hw e)
    · intro mem
      have nz : s p≠0 := by
        rcases sides with h | h <;> rcases mem with a | b
        · exact (h.1 a).ne'
        · exact (h.2 b).ne
        · exact (h.1 a).ne
        · exact (h.2 b).ne'
      refine ⟨?_,fun e => nz ((on _).mpr e)⟩
      rw [harmonicTorusImmersion_range hX]
      rcases mem with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩ <;> exact ⟨w,rhombic_horizontal_strip_not_mem ht hw.2,rfl⟩
  have dc : ContractibleSpace (Metric.ball (0:ℂ) 1) := Homeomorph.unitBall.contractibleSpace_iff.mp inferInstance
  have ca : ContractibleSpace A := (marked_cell_spatial_open_disk ht hX hE _ (Or.inl rfl)).some.contractibleSpace_iff.mpr dc
  have cb : ContractibleSpace B := (marked_cell_spatial_open_disk ht hX hE _ (Or.inr rfl)).some.contractibleSpace_iff.mpr dc
  have sa : IsSimplyConnected A := inferInstanceAs (SimplyConnectedSpace A)
  have sb : IsSimplyConnected B := inferInstanceAs (SimplyConnectedSpace B)
  have rev := cover.trans (union_comm A B)
  have flip {P : Set (Fin 3 → ℝ)} : (P⊆{p | s p<0} ↔ P⊆{p | 0< -s p}) ∧
      (P⊆{p | 0<s p} ↔ P⊆{p | -s p<0}) := by simp
  refine ⟨cover,dis,ca,cb,?_,?_,two_axis_component_half_turn ht hX,sides⟩
  · rcases sides with h | h
    · exact component_on_disjoint_sides ss cover h.1 h.2 sa
    · exact component_on_disjoint_sides ss.neg cover (flip.1.mp h.1) (flip.2.mp h.2) sa
  · rcases sides with h | h
    · exact component_on_disjoint_sides ss.neg rev (flip.1.mp h.2) (flip.2.mp h.1) sb
    · exact component_on_disjoint_sides ss rev h.2 h.1 sb

/-- The full spatial partition of the complement of the helicoid by two
open disks on opposite sides, interchanged by the vertical half-turn. -/
def HasSpatialTwoDiskPartition (S : Set (Fin 3 → ℝ)) (α : ℝ) : Prop :=
  let C := S \ range (axisRuledHelicoid I α 0)
  let s := axisHelicoidSide I α 0
  ∃ A B : Set (Fin 3 → ℝ), C=A∪B ∧ Disjoint A B ∧ Nonempty (A ≃ₜ Metric.ball (0:ℂ) 1) ∧
    Nonempty (B ≃ₜ Metric.ball (0:ℂ) 1) ∧
    (∀ p∈A, connectedComponentIn C p=A) ∧ (∀ p∈B, connectedComponentIn C p=B) ∧
    (fun p : Fin 3 → ℝ => ![-p 0,-p 1,p 2]) '' A=B ∧
    ((A⊆{p | 0<s p} ∧ B⊆{p | s p<0}) ∨ (A⊆{p | s p<0} ∧ B⊆{p | 0<s p}))

theorem marked_two_disk_partition {t α : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsEmbedding (harmonicTorusImmersion hX))
    (hinter : ∀ z∉(rhombicPeriodPair t ht).lattice, X z∈range (axisRuledHelicoid I α 0) →
      (X z 1=0 ∧ X z 2=0) ∨ (X z 0=0 ∧ X z 1=0)) :
    HasSpatialTwoDiskPartition (range (harmonicTorusImmersion hX)) α := by
  obtain ⟨cover,dis,_,_,first,second,exchange,sides⟩ := marked_spatial_complement_of_intersection ht hX hE hinter
  exact ⟨_,_,cover,dis,marked_cell_spatial_open_disk ht hX hE _ (Or.inl rfl),
    marked_cell_spatial_open_disk ht hX hE _ (Or.inr rfl),first,second,exchange,sides⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_spatial_complement_of_intersection
#print axioms TwoAxisHelicoid.marked_two_disk_partition
