import TwoAxisHelicoid.UniqueWitnessAllMarkings
import TwoAxisHelicoid.PdfOriginalTablesSpatialConclusion
import TwoAxisHelicoid.PhysicalClosedSpinMarking

namespace TwoAxisHelicoid.PdfVertical
open Set Topology

/-- Every physical marking selects the same pair measured by the original
attachments. Its actual embedded Euclidean images represent every placement
at every signed scale. The root, marked puncture, axes, divisor, and physical
models all use the same existential witness. -/
theorem original_table_root_common_physical_marking :
    ∃ p : ClosedPeriodParameters, (∀ q : ClosedPeriodParameters, q=p) ∧
      (∀ s : OriginalHelicoidRepresentative, PhysicalClosedSpinMarking p s.toPositional) ∧
      p.t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      p.a∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ∀ (c : ℝ) (hc : c≠0), IsClosedEmbedding (centeredActualTorusImmersion
        p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed) ∧
        ∀ s : PlacedGraphHelicoid, ∃ (k : ℝ) (e : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
          0<k ∧ (fun x => k • e x) '' s.1.image=range (centeredActualEuclideanImmersion
            p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed) :=
  unique_witness_with_all_markings (M:=fun s : OriginalHelicoidRepresentative => fun p =>
    PhysicalClosedSpinMarking p s.toPositional) original_tables_classify_period_models
      original_graph_realizes_closed_period_solution

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_table_root_common_physical_marking
