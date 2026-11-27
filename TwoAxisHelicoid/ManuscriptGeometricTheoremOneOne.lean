import TwoAxisHelicoid.ManuscriptClassificationAssembly
import TwoAxisHelicoid.ManuscriptCertifiedImageGeometryWitness
import TwoAxisHelicoid.ManuscriptC1MarkedGraphWitnesses

namespace TwoAxisHelicoid

/-- The C¹ manuscript theorem, including the actual global model, rigid map
and positive scale for each physical image, its exact parameters and both
simple Gauss divisor points in one common marking. -/
def ManuscriptGeometricTheoremOneOne : Prop :=
  ManuscriptClassificationWithMarking HasCertifiedSpinCapGaussMarking

theorem manuscript_geometric_theorem_one_one : ManuscriptGeometricTheoremOneOne :=
  manuscript_classification_of_geometry_and_markings HasCertifiedSpinCapGaussMarking
    manuscript_certified_image_geometry manuscript_C1_certified_spin_cap_gauss_marking
    placed_manuscript_C1_certified_spin_cap_gauss_marking

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscript_geometric_theorem_one_one
