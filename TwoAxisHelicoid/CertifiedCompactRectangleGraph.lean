import TwoAxisHelicoid.CertifiedRectangleProjectionBridge
import TwoAxisHelicoid.CertifiedCentralBandEmbedding
import TwoAxisHelicoid.RectangleShapeLeftCover
import TwoAxisHelicoid.RectangleShapeRightCover

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Projection onto a vertical plane embeds this entire closed rectangle
of the certified model, at every height, including its four edges. -/
theorem certified_compact_rectangle_vertical_graph :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let K := {z : ℂ | z.re∈Icc (1/2:ℝ) (5/8) ∧ z.im∈Icc (1/8:ℝ) (3/8)}
    IsClosedEmbedding (fun z : K => (X z.1 2,X z.1 0)) ∧
    InjOn certifiedTorusImmersion (puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' K)) :=
  certified_closed_rectangle_of_eight_edges centralBandLeftHeightCover centralBandRightHeightCover
    centralBandLeftGaussCover centralBandRightGaussCover centralBandBottomGaussCover centralBandTopGaussCover
    rectangleShapeLeftCover rectangleShapeRightCover

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_compact_rectangle_vertical_graph
