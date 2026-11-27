import TwoAxisHelicoid.OriginalHelicoidMetric
import TwoAxisHelicoid.UnorientedIsothermalChartHarmonic
import TwoAxisHelicoid.OriginalGeometricExteriorInput
import TwoAxisHelicoid.ReferenceHelicoidEnd

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The class of complete proper embedded smooth minimal surfaces of the
stated topological type and with the prescribed lines and a helicoidal C¹
end. The coordinate frame normalizes the reference vertical axis. -/
structure OriginalHelicoidRepresentative extends OriginalSmoothHelicoid where
  graphEnd : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization axes.pitch_ne ![0,0,0] ∘ position)

theorem OriginalHelicoidRepresentative.positional (surface : OriginalHelicoidRepresentative) :
    ApproachesSetAtInfinity (range surface.position) (range (axisRuledHelicoid I surface.axes.pitch 0)) ∧
      ApproachesSetAtInfinity (range (axisRuledHelicoid I surface.axes.pitch 0)) (range surface.position) :=
  reference_graph_positional_asymptote surface.position surface.closedEmbedding.continuous surface.axes.pitch_ne surface.graphEnd

theorem OriginalHelicoidRepresentative.nonplanar (surface : OriginalHelicoidRepresentative) :
    ¬ ∃ (n : Fin 3 → ℝ) (b : ℝ), n ≠ 0 ∧ ∀ p ∈ range surface.position, n ⬝ᵥ p = b :=
  helicoid_asymptotic_surface_nonplanar surface.axes.pitch_ne surface.positional.2 ⟨_,surface.axes.vertical 0⟩

/-- The analytic exterior input from the geometric end theorem, including
the induced complex atlas and a rigid frame chosen by that theorem. -/
def OriginalHelicoidExteriorPrinciple : Prop :=
  ∀ surface : OriginalHelicoidRepresentative, ∃ (S : ChartedSpace ℂ surface.carrier), let _ := S
    IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧ (∀ e ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position e) ∧
      Nonempty (GeometricExteriorInSomeFrame surface.position)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalHelicoidRepresentative.nonplanar
