import TwoAxisHelicoid.PdfOriginalTablesClosedParameters
import TwoAxisHelicoid.ClosedParameterWitness
import TwoAxisHelicoid.CompactRootAttachmentSpatialClass

namespace TwoAxisHelicoid.PdfVertical
open Set Topology

/-- The positive, negative, derivative, right-end and root attachments
select one parameter pair among all positive heights. Its centered
embedding at any signed scale represents every physical surface in §2.1. -/
theorem original_tables_classify_period_models :
    ∃ p : ClosedPeriodParameters, (∀ q : ClosedPeriodParameters, q=p) ∧
      p.t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      p.a∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ∀ (c : ℝ) (hc : c≠0), IsClosedEmbedding (centeredActualTorusImmersion
        p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed) ∧
        ∀ s : PlacedGraphHelicoid, ∃ (k : ℝ) (e : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
          0<k ∧ (fun x => k • e x) '' s.1.image=range (centeredActualEuclideanImmersion
            p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed) :=
  exists_unique_parameter_witness original_attachments_subsingleton_closed_parameters
    compact_root_attachment_represents_all_graph_surfaces

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_tables_classify_period_models
