import TwoAxisHelicoid.OriginalPositionalHelicoid
import TwoAxisHelicoid.PositionalMarkedC1End

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Starting with only one-sided C⁰ approach of the original real surface,
the two analytic exterior inputs suffice for the actual C¹ normal graph.
In particular this step precedes the Hoffman--White intersection result. -/
theorem positional_original_has_helicoidal_graph (s : OriginalPositionallyAsymptoticHelicoid)
    (bbc : OneHandleGeometricExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} s.modelTorus) :
    HasHelicoidalC1End s.position := by
  obtain ⟨L,f,Y,hf,hclosed,him,hhi,hh,hg⟩ := positional_original_marked_torus s bbc uniform
  have h := positional_marked_torus_has_helicoidal_graph L Y hclosed s.axes.horizontalDirection s.axes.unit s.axes.horizontalPoint
    (him.symm ▸ s.axes.horizontal) (him.symm ▸ s.axes.vertical) s.axes.pitch_ne (him.symm ▸ s.approaches) hhi hh hg
  have eq : (fun q : PuncturedPeriodTorus L => Y q.1) ∘ f = s.position := funext hf
  exact eq ▸ h.comp_homeomorph f

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_original_has_helicoidal_graph
