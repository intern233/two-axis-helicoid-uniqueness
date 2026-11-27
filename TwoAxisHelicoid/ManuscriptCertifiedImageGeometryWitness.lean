import TwoAxisHelicoid.ManuscriptCertifiedImageGeometry
import TwoAxisHelicoid.GraphTheoremByContactAndSpin

namespace TwoAxisHelicoid

/-- The images of all manuscript candidates are related to the certified
model by an actual Euclidean isometry and positive scaling. The model is
globally embedded and carries the rational parameters of Theorem 1.1. -/
theorem manuscript_certified_image_geometry : ManuscriptCertifiedImageGeometry :=
  manuscript_certified_image_geometry_of_classification
    original_graph_one_one_by_contact_and_spin.1
    original_graph_one_one_by_contact_and_spin.2.1
    original_graph_one_one_by_contact_and_spin.2.2.1
    original_graph_one_one_by_contact_and_spin.2.2.2.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_certified_image_geometry
