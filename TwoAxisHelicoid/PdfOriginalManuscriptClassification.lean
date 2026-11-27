import TwoAxisHelicoid.PdfOriginalRootCommonPhysicalMarking
import TwoAxisHelicoid.ManuscriptClassificationAssembly
import TwoAxisHelicoid.ManuscriptCertifiedImageGeometryWitness
import TwoAxisHelicoid.UniqueMarkedModelClassification

namespace TwoAxisHelicoid.PdfVertical
open Set Topology

/-- The parameters selected by the original period tables give the marking
of every surface with the compact-complement C¹ end in §2.1, in its own
axis frame. The compactifying map, axial crossing, and simple Gauss divisor
in each marking refer to this same pair. -/
theorem original_tables_classify_manuscript_C1_surfaces :
    ∃ p : ClosedPeriodParameters,
      p = certifiedClosedParameters ∧ (∀ q : ClosedPeriodParameters, q = p) ∧
      p.t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      p.a ∈ Ioo (4409686737850678150959633307219/7427640235712281649394745344000 : ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ManuscriptClassificationWithMarking (PhysicalClosedSpinMarking p) ∧
      ∀ (c : ℝ) (hc : c ≠ 0), IsClosedEmbedding (centeredActualTorusImmersion
        p.height_pos p.abscissa_mem hc p.vertical_closed p.horizontal_closed) :=
  classify_unique_marked_models certifiedClosedParameters original_table_root_common_physical_marking
    (fun p => original_property_of_all_manuscript_C1_surfaces (PhysicalClosedSpinMarking p))
    (fun p => manuscript_classification_of_geometry_and_markings (PhysicalClosedSpinMarking p))
    manuscript_certified_image_geometry

end TwoAxisHelicoid.PdfVertical

#print axioms TwoAxisHelicoid.PdfVertical.original_tables_classify_manuscript_C1_surfaces
