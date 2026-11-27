import TwoAxisHelicoid.OriginalSurfaceCertifiedRigidity
import TwoAxisHelicoid.SpatialSimilarityClasses
import TwoAxisHelicoid.OriginalHelicoidRepresentative

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- Every original representative agrees pointwise with the same certified
immersion under a Euclidean similarity and a homeomorphism of its full
domain, conditional on the three named geometric inputs. -/
theorem original_representative_similarity_to_certified (surface : OriginalHelicoidRepresentative)
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : CompactGenusOneUniformization.{0} surface.modelTorus)
    (hw : RhombicHelicoidIntersectionPrinciple) :
    ∃ (U : surface.carrier ≃ₜ PuncturedPeriodTorus certifiedPeriodPair)
      (scale : ℝ) (E : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
      (v : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧ ∀ x,
        certifiedTorusImmersion (U x) = scale • E (surface.euclideanPosition x)+v := by
  have transfer {e : OpenPartialHomeomorph surface.carrier ℂ} (he : InducedIsothermalChart surface.position e) :
      HarmonicImmersionChart surface.position e :=
    real_minimal_isothermal_chart_harmonic surface.smooth surface.immersion surface.minimal he
  obtain ⟨S,hs,hchart,⟨Aend⟩⟩ := bbc surface
  let := S
  let := hs
  obtain ⟨L,f,Y,_,_,hf,hclosed,him,hhi,hh,hg⟩ := original_surface_from_arbitrary_exterior_frame surface.topologicalType
    uniform surface.position surface.closedEmbedding (fun e he => transfer (hchart e he)) Aend surface.axes.pitch_ne surface.positional.1
  obtain ⟨U,k,E,b,hk,he⟩ := marked_arbitrary_horizontal_line_similarity_to_certified hw L Y hclosed
    surface.axes.horizontalDirection surface.axes.unit surface.axes.horizontalPoint (him.symm ▸ surface.axes.horizontal)
    (him.symm ▸ surface.axes.vertical) surface.axes.pitch_ne (him.symm ▸ surface.positional.1) hhi hh hg
  exact ⟨f.trans U,k,E,b,hk,fun x => (he (f x)).trans (by simp only [hf,OriginalSmoothHelicoid.euclideanPosition,Function.comp_apply])⟩

/-- The geometric existence input supplies only a representative. Compact
genus-one uniformization, BBC and Hoffman--White are recorded individually.
The quotient uses actual images and all positive Euclidean similarities. -/
theorem original_candidate_class_unique_of_geometric_inputs
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : ∀ L, CompactGenusOneUniformization.{0} L)
    (hw : RhombicHelicoidIntersectionPrinciple) (whw : Nonempty OriginalHelicoidRepresentative) :
    ∃! c : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))),
      ∃ surface : OriginalHelicoidRepresentative,
        Quotient.mk (spatialSimilaritySetoid _) surface.image = c := by
  apply unique_spatial_image_class_of_common_model (fun surface : OriginalHelicoidRepresentative => surface.image)
    (range certifiedTorusImmersion) whw
  intro surface
  obtain ⟨U,k,E,v,hk,h⟩ := original_representative_similarity_to_certified surface bbc (uniform _) hw
  exact image_similarity_of_surjective_parameters surface.euclideanPosition certifiedTorusImmersion U U.surjective k E v hk h

/-- Under the same inputs, the global embedding of the actual certified
model follows by transferring a given embedded representative. -/
theorem original_existence_implies_certified_embedding
    (bbc : OriginalHelicoidExteriorPrinciple) (uniform : ∀ L, CompactGenusOneUniformization.{0} L)
    (hw : RhombicHelicoidIntersectionPrinciple) (whw : Nonempty OriginalHelicoidRepresentative) :
    IsClosedEmbedding certifiedTorusImmersion := by
  obtain ⟨surface⟩ := whw
  obtain ⟨U,k,E,v,hk,h⟩ := original_representative_similarity_to_certified surface bbc (uniform _) hw
  let F := E.toDilationEquiv.trans (DilationEquiv.smulTorsor v hk.ne')
  have he : certifiedTorusImmersion = F ∘ surface.euclideanPosition ∘ U.symm := by
    funext p
    change certifiedTorusImmersion p = k • E (surface.euclideanPosition (U.symm p))+v
    simpa only [U.apply_symm_apply] using h (U.symm p)
  rw [he]
  exact F.toHomeomorph.isClosedEmbedding.comp (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp
    surface.closedEmbedding).comp U.symm.isClosedEmbedding)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_candidate_class_unique_of_geometric_inputs
#print axioms TwoAxisHelicoid.original_existence_implies_certified_embedding
