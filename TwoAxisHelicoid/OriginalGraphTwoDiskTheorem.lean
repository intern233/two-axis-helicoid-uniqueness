import TwoAxisHelicoid.GraphGeometricIntersection
import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.GenusOneFromAnnularUniformization
import TwoAxisHelicoid.OriginalRotatedExteriorReduction

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- A complete horizontal axis of a continuous normal graph determines
the phase of its comparison helicoid, including a translated end
coordinate whose vertical offset was initially unspecified. -/
theorem graph_axis_determines_comparison {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (cx : Continuous X) {α : ℝ} (ha : α≠0) (b : ℝ)
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range X)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,b] ∘ X)) :
    (axisSpatialNormalization ha ![0,0,b]) ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)=
      range (axisRuledHelicoid I α 0) := by
  let R := axisSpatialNormalization ha ![0,0,b]
  let Y := coordinateToTube ∘ R ∘ X
  have line (x : ℝ) : ((x,0),α*(0-b))∈range Y := by
    obtain ⟨q,hq⟩ := horizontal (-x/α)
    refine ⟨q,?_⟩
    change coordinateToTube (axisSpatialNormalization ha ![0,0,b] (X q))=_
    rw [hq,axis_normalized_tube_vector]
    change ((-α*(-x/α),-α*0),α*(0-b))=_
    rw [mul_zero,show -α*(-x/α)=x by field_simp]
  have hsin := graph.horizontal_line_is_ruling (coordinateToTube.continuous.comp (R.continuous.comp cx)) line
  have unit : (![1,0,0] : Fin 3 → ℝ)∈range (axisRuledHelicoid I α b) := by
    apply (axisHelicoidSide_eq_zero_iff (by simp : normSq I=1) _ _ _).mp
    let θ := α*(0-b)
    change (I*Complex.exp (I*(θ : ℂ))).re*1+(I*Complex.exp (I*(θ : ℂ))).im*0=0
    rw [mul_one,mul_zero,add_zero,mul_comm I (θ:ℂ),Complex.mul_re,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_sub,Complex.exp_ofReal_mul_I_im,show Real.sin θ=0 from hsin,neg_zero]
  exact (inverse_image_standardHelicoid_axisNormalization ha b).trans
    (axisRuledHelicoid_range_of_horizontal_unit (by simp : normSq I=1) α b unit)

/-- Proposition 2.2 on the original physical surface. The puncture
chart, genus-one uniformization and comparison phase are constructed
from the given smooth minimal embedding, its graph end and its
actual axes. The two components are open disks interchanged by the
Euclidean half-turn and lying on opposite sides of the helicoid. -/
theorem original_graph_two_axes_and_open_disks (s : OriginalSmoothHelicoid)
    {α : ℝ} (ha : α≠0) (b : ℝ)
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range s.position)
    (vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range s.position)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,b] ∘ s.position)) :
    (range s.position ∩ range (axisRuledHelicoid I α 0)={p | (p 1=0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1=0)}) ∧
      HasSpatialTwoDiskPartition (range s.position) α := by
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas
    s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus s.modelTorus)
  let _ : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  let B : Fin 3 → ℝ := ![0,0,b]
  let R := axisSpatialNormalization ha B
  let Z := fun x => -B+s.position x
  have shifted := orthogonal_affine_harmonic_charts s.position charts (LinearEquiv.refl ℝ _) (fun _ _ => rfl) (-B)
  have eq : R ∘ s.position=axisSpatialNormalization ha ![0,0,0] ∘ Z := by
    funext x
    have zero : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
    simp only [R,Function.comp_apply,axisSpatialNormalization_apply,zero,map_zero,Z,map_add,map_neg,
      sub_eq_add_neg,neg_zero,add_zero]
    rw [add_comm]
  have harm : ∀ d∈atlas ℂ s.carrier, HarmonicImmersionChart (R ∘ s.position) d := by
    rw [eq]
    intro d hd z hz
    obtain ⟨hh,conf,imm⟩ := shifted d hd z hz
    exact reference_frame_harmonic_chart (X:=Z ∘ d.symm) hh conf imm ha
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling
    (R.isClosedEmbedding.comp s.closedEmbedding) harm graph topological_plane_uniformization_proved
  exact conformally_filled_two_axes_intersection_and_disks s.topologicalType
    (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _)
    s.position s.closedEmbedding charts E hol ha b horizontal vertical graph
    (graph_axis_determines_comparison s.closedEmbedding.continuous ha b horizontal graph)

/-- The geometric comparison principle used in the original reduction,
with the asymptotic surface and the spatial image in the same frame. -/
theorem geometric_two_axis_intersection_proved : GeometricTwoAxisIntersectionTheorem := by
  intro s α ha b A H _ _ horizontal vertical graph aligned
  rw [aligned]
  exact (original_graph_two_axes_and_open_disks s ha b horizontal vertical graph).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_axis_determines_comparison
#print axioms TwoAxisHelicoid.original_graph_two_axes_and_open_disks
#print axioms TwoAxisHelicoid.geometric_two_axis_intersection_proved
