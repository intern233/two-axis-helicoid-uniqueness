import TwoAxisHelicoid.GeometricIntersectionFromFilling
import TwoAxisHelicoid.PhysicalGraphPunctureFilling
import TwoAxisHelicoid.ReferenceFrameHarmonic
import TwoAxisHelicoid.PuncturedTorusRealOrientation

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

private theorem offset_reference_harmonic {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) (hc : ConformalCoordinateDerivatives X z)
    (hi : Function.Injective (fderiv ℝ X z)) {α : ℝ} (ha : α≠0) (B : Fin 3 → ℝ) :
    let Y := axisSpatialNormalization ha B ∘ X
    (∀ j, HarmonicAt (fun w => Y w j) z) ∧ ConformalCoordinateDerivatives Y z ∧
      Function.Injective (fderiv ℝ Y z) := by
  let Z := fun w => -B+X w
  obtain ⟨hh',hc',hi'⟩ := orthogonal_affine_harmonic_immersion (LinearEquiv.refl ℝ _) (fun _ _ => rfl) (-B) hh hc hi
  have frame : axisSpatialNormalization ha B ∘ X=axisSpatialNormalization ha ![0,0,0] ∘ Z := by
    funext w
    have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
    simp only [Function.comp_apply,axisSpatialNormalization_apply,zero,map_zero,Z,map_add,map_neg,sub_eq_add_neg,neg_zero,add_zero]
    rw [add_comm]
  rw [frame]
  exact reference_frame_harmonic_chart (X := Z) hh' hc' hi' ha

/-- Proposition 2.2 for the original surface in any aligned vertical frame.
The C¹ end constructs the conformal puncture used in the comparison. -/
theorem original_graph_axes_intersection_and_disks (s : OriginalSmoothHelicoid)
    (uni : SimplyConnectedNoncompactUniformization.{0}) {α : ℝ} (ha : α≠0) (b : ℝ)
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range s.position)
    (vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range s.position)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,b] ∘ s.position))
    (aligned : (axisSpatialNormalization ha ![0,0,b]) ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)=range (axisRuledHelicoid I α 0)) :
    (range s.position ∩ range (axisRuledHelicoid I α 0)={p | (p 1=0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1=0)}) ∧
      HasSpatialTwoDiskPartition (range s.position) α := by
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  have hman : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := man
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus s.modelTorus)
  have non : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  let R := axisSpatialNormalization ha ![0,0,b]
  have harmonic : ∀ d∈atlas ℂ s.carrier, HarmonicImmersionChart (R ∘ s.position) d :=
    fun d hd z hz => offset_reference_harmonic (charts d hd z hz).1 (charts d hd z hz).2.1 (charts d hd z hz).2.2 ha _
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling (R.isClosedEmbedding.comp s.closedEmbedding) harmonic graph
    (topological_plane_uniformization_of_classical uni)
  exact conformally_filled_two_axes_intersection_and_disks s.topologicalType (compact_genus_one_uniformization_of_classical uni _)
    s.position s.closedEmbedding charts E hol ha b horizontal vertical graph aligned

theorem geometric_two_axis_intersection_from_classical_uniformization (uni : SimplyConnectedNoncompactUniformization.{0}) :
    GeometricTwoAxisIntersectionTheorem := by
  intro s α ha b A H _ _ horizontal vertical graph aligned
  rw [aligned]
  exact (original_graph_axes_intersection_and_disks s uni ha b horizontal vertical graph aligned).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_axes_intersection_and_disks
#print axioms TwoAxisHelicoid.geometric_two_axis_intersection_from_classical_uniformization
