import TwoAxisHelicoid.CompactRootAttachmentEmbedding
import TwoAxisHelicoid.PlacedGraphPointedConclusion

namespace TwoAxisHelicoid.PdfVertical
open Set Topology

/-- For any closed parameter pair in the original root interval, the
physical centered image at signed scale c is a dilation and a translation
of the certified Euclidean image. The dilation has ratio |c|. -/
theorem compact_root_centered_image_similarity (p : ClosedPeriodParameters)
    (hp : p.t∈Icc (rootTLower:ℝ) rootTUpper) {c : ℝ} (hc : c≠0) :
    (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))).r (range certifiedTorusImmersion)
      (range (centeredActualEuclideanImmersion p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed)) := by
  obtain rfl := compact_root_closed_parameters_eq_certified p hp
  let p := certifiedClosedParameters
  let b := -(c • coordinateToEuclidean (actualGlobalImmersion p.t p.a 1 p.height_pos 1))
  let D := DilationEquiv.smulTorsor b hc
  have point (q : PuncturedPeriodTorus certifiedPeriodPair) :
      D (certifiedTorusImmersion q)=
        centeredActualEuclideanImmersion p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed q := by
    change c • certifiedTorusImmersion q + b = coordinateToEuclidean (centeredActualTorusImmersion _ _ hc _ _ q)
    rw [centered_closed_torus_scale p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed q]
    let x := actualTorusImmersion p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed q.1
    let origin := actualGlobalImmersion p.t p.a 1 p.height_pos 1
    change c • coordinateToEuclidean x + -(c • coordinateToEuclidean origin) =
      coordinateToEuclidean (c • (x-origin))
    rw [map_smul,map_sub,smul_sub,sub_eq_add_neg]
  refine ⟨D,?_⟩
  rw [← range_comp]
  exact congrArg range (funext point)

/-- The raw root attachment gives an embedded geometric representative of
the manuscript's physical similarity class at every nonzero scale. -/
theorem compact_root_attachment_represents_all_graph_surfaces :
    ∃ p : ClosedPeriodParameters, p.t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      p.a∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ∀ (c : ℝ) (hc : c≠0),
        IsClosedEmbedding (centeredActualTorusImmersion p.height_pos p.abscissa_mem hc
          p.vertical_closed p.horizontal_closed) ∧
        ∀ s : PlacedGraphHelicoid, ∃ (k : ℝ) (e : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
          0<k ∧ (fun x => k • e x) '' s.1.image=range (centeredActualEuclideanImmersion
            p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed) := by
  obtain ⟨p,ht,ha,geometry⟩ := compact_root_attachment_centered_embeddings
  refine ⟨p,ht,ha,fun c hc => ⟨(geometry c hc).2,?_⟩⟩
  intro s
  let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
  obtain ⟨uniqueClass,certifiedRep⟩ := graph_similarity_from_certified_embedding certified_global_closed_embedding
  have same : Quotient.mk Q s.normalizedGraph.image=Quotient.mk Q (range certifiedTorusImmersion) :=
    uniqueClass.unique ⟨s.normalizedGraph,rfl⟩ certifiedRep
  exact (spatial_similarity_iff_positive_scale_isometry _ _).mp
    (Q.trans s.1.image_equivalent_normalized (Q.trans (Quotient.exact same)
      (compact_root_centered_image_similarity p ⟨ht.1.le,ht.2.le⟩ hc)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_root_attachment_represents_all_graph_surfaces
