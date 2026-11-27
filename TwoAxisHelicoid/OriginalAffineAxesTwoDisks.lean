import TwoAxisHelicoid.OriginalHorizontalRuling
import TwoAxisHelicoid.RulingFrameDiskPartition
import TwoAxisHelicoid.OriginalGraphTwoDiskTheorem
import TwoAxisHelicoid.PositionalBoundedCurvatureGraph

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- Proposition 2.2 in the original spatial coordinates, with the two
affine lines actually supplied by the representative. The ruling
height and horizontal direction need not have been normalized. -/
theorem original_affine_axes_intersection_and_disks (s : OriginalHelicoidRepresentative) :
    let P := s.axes.horizontalPoint
    let d := s.axes.horizontalDirection
    let T := range (axisRuledHelicoid I s.axes.pitch 0)
    range s.position ∩ T=range (fun r : ℝ => P+r • ![d.re,d.im,0]) ∪
      range (fun r : ℝ => (![0,0,r] : Fin 3 → ℝ)) ∧
      HasSpatialTwoDiskPartition (range s.position) s.axes.pitch := by
  intro P d T
  let α := s.axes.pitch
  let h := P 2
  let R := referenceRulingFrame α h
  let N := axisSpatialNormalization s.axes.pitch_ne ![0,0,0]
  let Y := R ∘ s.position
  let line := range (fun r : ℝ => P+r • ![d.re,d.im,0])
  let X := range (fun r : ℝ => (![r,0,0] : Fin 3 → ℝ))
  let Z := range (fun r : ℝ => (![0,0,r] : Fin 3 → ℝ))
  have eqLine : line=range (fun r : ℝ => axisRuledHelicoid I α 0 ⟨r,h⟩) :=
    original_horizontal_line_equals_ruling s.toPositional
  have rx : R '' line=X := by
    rw [eqLine,← range_comp]
    exact congrArg range (funext (referenceRulingFrame_ruling α h))
  have rz : R '' Z=Z := by
    ext p
    constructor
    · rintro ⟨_,⟨r,rfl⟩,rfl⟩
      exact ⟨r-h,(referenceRulingFrame_vertical α h r).symm⟩
    · rintro ⟨r,rfl⟩
      exact ⟨![0,0,r+h],⟨r+h,rfl⟩,by rw [referenceRulingFrame_vertical,add_sub_cancel_right]⟩
  have rangeY : range Y=R '' range s.position := range_comp _ _
  have horizontal (r : ℝ) : (![r,0,0] : Fin 3 → ℝ)∈range Y := by
    rw [rangeY]
    have sub : line⊆range s.position := by rintro _ ⟨v,rfl⟩; exact s.axes.horizontal v
    exact image_mono sub (rx.symm ▸ (show (![r,0,0]:Fin 3 → ℝ)∈X from ⟨r,rfl⟩))
  have vertical (r : ℝ) : (![0,0,r] : Fin 3 → ℝ)∈range Y := by
    rw [rangeY]
    have sub : Z⊆range s.position := by rintro _ ⟨v,rfl⟩; exact s.axes.vertical v
    exact image_mono sub (rz.symm ▸ (show (![0,0,r]:Fin 3 → ℝ)∈Z from ⟨r,rfl⟩))
  have graph : HasHelicoidC1End (coordinateToTube ∘ N ∘ Y) := by
    have eq : coordinateToTube ∘ N ∘ Y=
        helicoidScrewMove (-(α*h)) ∘ (coordinateToTube ∘ N ∘ s.position) :=
      funext (fun q => referenceRulingFrame_normalized s.axes.pitch_ne h (s.position q))
    rw [eq]
    exact s.graphEnd.screw_motion (coordinateToTube_isProperMap (N.isClosedEmbedding.comp s.closedEmbedding).isProperMap) _
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas
    s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus s.modelTorus)
  let _ : NoncompactSpace s.carrier := ⟨fun k => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using k.image s.topologicalType.continuous)⟩
  have form : ∀ e∈atlas ℂ s.carrier, HarmonicImmersionChart Y e := by
    intro e he z hz
    obtain ⟨hh,hc,hi⟩ := charts e he z hz
    exact lineAxisCoordinates_harmonic_chart _ _ _ hh hc hi
  have nf : ∀ e∈atlas ℂ s.carrier, HarmonicImmersionChart (N ∘ Y) e := by
    intro e he z hz
    obtain ⟨hh,hc,hi⟩ := form e he z hz
    exact reference_frame_harmonic_chart (X:=Y ∘ e.symm) hh hc hi s.axes.pitch_ne
  have closed : Topology.IsClosedEmbedding Y := R.isClosedEmbedding.comp s.closedEmbedding
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling (N.isClosedEmbedding.comp closed) nf graph
    topological_plane_uniformization_proved
  obtain ⟨cut,disks⟩ := conformally_filled_two_axes_intersection_and_disks s.topologicalType
    (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _)
    Y closed form E hol s.axes.pitch_ne 0 horizontal vertical graph
    (graph_axis_determines_comparison closed.continuous s.axes.pitch_ne 0 horizontal graph)
  have coord : {p : Fin 3 → ℝ | (p 1=0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1=0)}=X∪Z := by
    ext p
    constructor
    · rintro (⟨y,z⟩|⟨x,y⟩)
      · exact Or.inl ⟨p 0,by ext j; fin_cases j <;> simp [y,z]⟩
      · exact Or.inr ⟨p 2,by ext j; fin_cases j <;> simp [x,y]⟩
    · rintro (⟨r,rfl⟩|⟨r,rfl⟩)
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
  refine ⟨?_,two_disk_partition_in_original_ruling_frame _ α h (rangeY ▸ disks)⟩
  calc range s.position ∩ T=R ⁻¹' (range Y ∩ T) := by
          ext p
          change (p∈range s.position ∧ p∈T) ↔ R p∈range Y ∧ R p∈T
          rw [rangeY,R.injective.mem_set_image,referenceRulingFrame_mem_helicoid]
       _=line∪Z := by
          have transported : R '' (line∪Z)=X∪Z := by rw [image_union,rx,rz]
          rw [cut,coord,← transported,R.preimage_image]

/-- The very same original axes conclusion applies to one-sided positional
candidates once their physical end curvature is known to be bounded. -/
theorem positional_affine_axes_intersection_and_disks (s : OriginalPositionallyAsymptoticHelicoid)
    (bounded : HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) :
    let P := s.axes.horizontalPoint
    let d := s.axes.horizontalDirection
    range s.position ∩ range (axisRuledHelicoid I s.axes.pitch 0)=
      range (fun r : ℝ => P+r • ![d.re,d.im,0]) ∪ range (fun r : ℝ => (![0,0,r] : Fin 3 → ℝ)) ∧
      HasSpatialTwoDiskPartition (range s.position) s.axes.pitch :=
  original_affine_axes_intersection_and_disks
    { s.toOriginalSmoothHelicoid with graphEnd := positional_c1_graph_of_bounded_shape s bounded }

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_affine_axes_intersection_and_disks
#print axioms TwoAxisHelicoid.positional_affine_axes_intersection_and_disks
