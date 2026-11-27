import TwoAxisHelicoid.OriginalSurfaceJacobiFields
import TwoAxisHelicoid.PublishedGeometricClassification

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Appendix D.1 on the original surface from its positional asymptote, the
published conformal filling and two double poles, and classical uniformization. -/
theorem positional_helicoid_seven_jacobi_fields (surface : OriginalPositionallyAsymptoticHelicoid)
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0}) :
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧ (∀ d ∈ atlas ℂ surface.carrier, InducedIsothermalChart surface.position d) ∧
      ∃ (L : PeriodPair) (f : surface.carrier ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ)
        (N : surface.carrier → Fin 3 → ℝ) (J : (Fin 7 → ℝ) →ₗ[ℝ] (surface.carrier → ℝ)),
        ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧ (∀ x, Y (f x).1 = surface.position x) ∧
        (∀ (z : ℂ) (hz : z ∉ L.lattice), N (f.symm (puncturedPlaneProjection L ⟨z,hz⟩)) =
          harmonicChartNormal (Y ∘ periodTorusProjection L) z) ∧
        Function.Injective J ∧ LinearIndependent ℝ (fun i : Fin 7 => J (Pi.basisFun ℝ (Fin 7) i)) ∧
        ∀ p, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (J p) ∧ IsSmoothMarkedJacobiField L Y ((J p) ∘ f.symm) ∧
          ∀ x, J p x = similarityField ![p 0,p 1,p 2] ![p 3,p 4,p 5] (p 6) (surface.position x) ⬝ᵥ N x := by
  obtain ⟨A⟩ := bbc surface.toOriginalSmoothHelicoid surface.intrinsic_complete surface.one_topological_end surface.image_ne_embedded_plane
  obtain ⟨S,hs,hchart,L,f,hY,hf,hfi,hpos,hc,_,hreg,_,_⟩ :=
    original_smooth_surface_published_poles_to_torus surface.toOriginalSmoothHelicoid
      (compact_genus_one_uniformization_of_classical poincare surface.modelTorus) A surface.approaches
  let _ := S
  let _ := hs
  obtain ⟨N,J,hn,hi,hl,hj⟩ := marked_jacobi_fields_on_original L f hf surface.position hY hpos hc hreg
  exact ⟨S,hs,fun d hd => (hchart d hd).1,L,f,hY,N,J,hf,hfi,hpos,hn,hi,hl,hj⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_helicoid_seven_jacobi_fields
