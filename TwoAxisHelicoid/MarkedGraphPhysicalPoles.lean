import TwoAxisHelicoid.MarkedGraphIntrinsicOrders
import TwoAxisHelicoid.HorizontalGraphScrewPlacement
import TwoAxisHelicoid.ReferenceFrameEndOrders
import TwoAxisHelicoid.OriginalHelicoidRepresentative

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology

/-- The original pitch, horizontal line and spatial frame are arbitrary.
Both pole orders follow from the physical normal graph on the given
embedded marked torus. -/
theorem marked_graph_physical_poles (L : PeriodPair) (Y : PeriodTorus L → Fin 3 → ℝ)
    (closed : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1))
    (axes : OriginalHelicoidAxes (range (fun q : PuncturedPeriodTorus L => Y q.1)))
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z))
    (graph : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (axisSpatialNormalization axes.pitch_ne ![0,0,0] (Y q.1)))) :
    meromorphicOrderAt (fun w => immersionComplexCoefficient (Y ∘ periodTorusProjection L) w 2) 0=(-2:ℤ) ∧
    meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0=(-2:ℤ) := by
  let R := axisSpatialNormalization axes.pitch_ne ![0,0,0]
  let F := R ∘ Y
  have image : range (fun q : PuncturedPeriodTorus L => F q.1)=R '' range (fun q : PuncturedPeriodTorus L => Y q.1) := by
    rw [← range_comp]
    rfl
  obtain ⟨line,ver⟩ := reference_frame_maps_straight_axes axes.pitch_ne axes.horizontalDirection axes.horizontalPoint axes.horizontal axes.vertical
  have reg' (z : ℂ) (hz : z∉L.lattice) := reference_frame_harmonic_chart (reg z hz).1 (reg z hz).2.1 (reg z hz).2.2 axes.pitch_ne
  obtain ⟨cl,hor,vertical,harm,asymptote,height,gauss⟩ := horizontal_graph_screw_placement L F
    (R.isClosedEmbedding.comp closed) axes.horizontalDirection axes.unit (R axes.horizontalPoint) (image.symm ▸ line)
    (image.symm ▸ ver) reg' graph
  obtain ⟨a,b⟩ := marked_straight_graph_intrinsic_end_orders L _ cl hor vertical harm asymptote
  obtain ⟨c,d⟩ := reference_frame_end_orders (X := Y ∘ periodTorusProjection L) axes.pitch_ne
    ((punctured_lattice_regular_near_zero L).mono fun z hz =>
      (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((reg z hz).1 j)).differentiableAt)
  exact ⟨c.symm.trans (height.symm.trans a),d.symm.trans (gauss.symm.trans b)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_graph_physical_poles
