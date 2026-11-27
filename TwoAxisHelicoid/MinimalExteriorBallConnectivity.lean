import TwoAxisHelicoid.HarmonicBallConvexHull
import TwoAxisHelicoid.OneEndedBallExterior
import TwoAxisHelicoid.OriginalGeometricTopology

namespace TwoAxisHelicoid
open Set Metric

/-- The original one-ended minimal surface has a nonempty connected
exterior beyond every closed Euclidean ball. -/
theorem original_exterior_of_closed_ball_connected (s : OriginalSmoothHelicoid)
    (o : EuclideanSpace ℝ (Fin 3)) (r : ℝ) : IsConnected {x : s.carrier | r<dist (s.euclideanPosition x) o} := by
  let K := s.euclideanPosition ⁻¹' closedBall o r
  have kc : IsCompact K := s.euclidean_proper.isCompact_preimage (isCompact_closedBall _ _)
  obtain ⟨T,_,con,_,avoid⟩ := s.one_topological_end K kc
  obtain ⟨x,hx⟩ := con.nonempty
  exact ⟨⟨x,lt_of_not_ge fun h => disjoint_left.mp avoid hx (mem_closedBall.mpr h)⟩,s.ball_exterior_preconnected o r⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_exterior_of_closed_ball_connected
