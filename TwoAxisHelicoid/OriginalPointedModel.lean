import TwoAxisHelicoid.OriginalHelicoidRepresentative
import TwoAxisHelicoid.ArbitraryConformalModel
import TwoAxisHelicoid.PuncturedBiholomorphicFilling

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace Matrix
open scoped Topology Manifold ContDiff OnePoint

/-- The end and the intersection of the originally specified straight lines
correspond to 0 and 1 in the certified compact complex torus. -/
def HasCertifiedPointedNormalization (surface : OriginalSmoothHelicoid) : Prop :=
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧
      (∀ d ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position d) ∧
      ∃ (U : surface.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair) (k : ℝ)
        (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)) (b : EuclideanSpace ℝ (Fin 3)),
        ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U.symm ∧
        0 < k ∧ (∀ x, certifiedTorusImmersion (U x) = k • E (surface.euclideanPosition x)+b) ∧
        (∃ r : ℝ, surface.axes.horizontalPoint+r • ![surface.axes.horizontalDirection.re,surface.axes.horizontalDirection.im,0] =
          ![0,0,surface.axes.horizontalPoint 2]) ∧
        surface.position (U.symm (rhombicAxisPoint certifiedClosedParameters.height_pos)) = ![0,0,surface.axes.horizontalPoint 2] ∧
        ∃ S' : ChartedSpace ℂ (OnePoint surface.carrier), let _ := S'
          IsManifold 𝓘(ℂ,ℂ) ω (OnePoint surface.carrier) ∧
          ∃ H : OnePoint surface.carrier ≃ₜ PeriodTorus certifiedPeriodPair, H OnePoint.infty = 0 ∧
            ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm ∧
            ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : surface.carrier → OnePoint surface.carrier) ∧
            ∀ x : surface.carrier, H (x : OnePoint surface.carrier) = (U x).1

/-- A one-sided positional asymptote and a geometric exterior chart are
enough for the full pointed normalization of the original surface. -/
theorem original_pointed_model_from_exterior (surface : OriginalSmoothHelicoid)
    (positional : ApproachesSetAtInfinity (range surface.position) (range (axisRuledHelicoid I surface.axes.pitch 0)))
    (exterior : ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧ (∀ e ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position e) ∧
      Nonempty (GeometricExteriorInSomeFrame surface.position))
    (uniform : CompactGenusOneUniformization.{0} surface.modelTorus) (hw : RhombicHelicoidIntersectionPrinciple) :
    HasCertifiedPointedNormalization surface := by
  have transfer {e : OpenPartialHomeomorph surface.carrier ℂ} (he : InducedIsothermalChart surface.position e) :
      HarmonicImmersionChart surface.position e :=
    real_minimal_isothermal_chart_harmonic surface.smooth surface.immersion surface.minimal he
  obtain ⟨S,hs,hchart,⟨Aend⟩⟩ := exterior
  refine ⟨S,hs,hchart,?_⟩
  let := S
  let := hs
  obtain ⟨L,f,Y,hfhol,hfinv,hf,hclosed,him,hhi,hh,hg⟩ := original_surface_from_arbitrary_exterior_frame
    surface.topologicalType uniform surface.position surface.closedEmbedding (fun e he => transfer (hchart e he))
    Aend surface.axes.pitch_ne positional
  obtain ⟨_,V,k,E,b,_,_,_,hv,hi,_,hc,hx,hk,hpt⟩ := marked_arbitrary_axes_biholomorphic_to_certified hw L Y hclosed
    surface.axes.horizontalDirection surface.axes.unit surface.axes.horizontalPoint (him.symm ▸ surface.axes.horizontal)
    (him.symm ▸ surface.axes.vertical) surface.axes.pitch_ne (him.symm ▸ positional) hhi hh hg
  let U := f.trans V
  have han : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω U := hv.comp hfhol
  refine ⟨U,k,E,b,han,hfinv.comp hi,hk,fun x => (hpt (f x)).trans (by simp only [hf,OriginalSmoothHelicoid.euclideanPosition,Function.comp_apply]),hc,?_,
    punctured_biholomorphic_identification_fills U han⟩
  change surface.position (f.symm (V.symm _)) = _
  rw [← hf,f.apply_symm_apply]
  exact hx


theorem original_representative_certified_pointed_model (surface : OriginalHelicoidRepresentative)
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} surface.modelTorus)
    (hw : RhombicHelicoidIntersectionPrinciple) : HasCertifiedPointedNormalization surface.toOriginalSmoothHelicoid :=
  original_pointed_model_from_exterior surface.toOriginalSmoothHelicoid surface.positional.1 (bbc surface) uniform hw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_representative_certified_pointed_model
