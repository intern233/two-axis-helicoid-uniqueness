import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.OriginalHandleTopology

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- One-sided positional asymptotics are enough at the geometric entry.
There is no end graph, tangent estimate or end coordinate in this class. -/
structure OriginalPositionallyAsymptoticHelicoid extends OriginalSmoothHelicoid where
  approaches : ApproachesSetAtInfinity (range position) (range (axisRuledHelicoid I axes.pitch 0))

def OriginalHelicoidRepresentative.toPositional (s : OriginalHelicoidRepresentative) :
    OriginalPositionallyAsymptoticHelicoid :=
  {s.toOriginalSmoothHelicoid with approaches := s.positional.1}

/-- Bernstein--Breiner's exterior and C⁰ asymptotic conclusions in the
chosen rigid frame, for the original smooth genus-one surface. -/
def OneHandleGeometricExteriorPrinciple : Prop :=
  ∀ surface : OriginalSmoothHelicoid, ¬ SimplyConnectedSpace surface.carrier →
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧ (∀ e ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position e) ∧
      Nonempty (GeometricExteriorInSomeFrame surface.position)

theorem one_handle_exterior_implies_original_exterior (bbc : OneHandleGeometricExteriorPrinciple) :
    OriginalHelicoidExteriorPrinciple := fun s => bbc s.toOriginalSmoothHelicoid s.not_simply_connected

/-- Recover an actual harmonic marking of the entire original C⁰ candidate.
Its parameter homeomorphism identifies each original point and both intrinsic
end orders in the specified geometric frame. -/
theorem positional_original_marked_torus (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : OneHandleGeometricExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} s.modelTorus) :
    ∃ (L : PeriodPair) (f : s.carrier ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ),
      (∀ x, Y (f x).1 = s.position x) ∧ IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Y q.1) ∧
      range (fun q : PuncturedPeriodTorus L => Y q.1) = range s.position ∧
      (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
        ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧
        Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient (Y ∘ periodTorusProjection L) z 2) 0 = (-2:ℤ) ∧
      meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0 = (-2:ℤ) := by
  have transfer {e : OpenPartialHomeomorph s.carrier ℂ} (he : InducedIsothermalChart s.position e) :
      HarmonicImmersionChart s.position e :=
    real_minimal_isothermal_chart_harmonic s.smooth s.immersion s.minimal he
  obtain ⟨S,hs,hc,⟨A⟩⟩ := bbc s.toOriginalSmoothHelicoid s.not_simply_connected
  let := S
  let := hs
  obtain ⟨L,f,Y,_,_,hf,hclosed,him,hhi,hh,hg⟩ := original_surface_from_arbitrary_exterior_frame s.topologicalType
    uniform s.position s.closedEmbedding (fun e he => transfer (hc e he)) A s.axes.pitch_ne s.approaches
  exact ⟨L,f,Y,hf,hclosed,him,hhi,hh,hg⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.positional_original_marked_torus
