import TwoAxisHelicoid.ManuscriptC1PredicateTransport
import TwoAxisHelicoid.OriginalSpinCapGaussMarking

namespace TwoAxisHelicoid

/-- The cap, physical immersion and two Gauss divisor points use one marking
on each normalized manuscript surface. -/
theorem manuscript_C1_certified_spin_cap_gauss_marking :
    AllManuscriptC1Surfaces HasCertifiedSpinCapGaussMarking :=
  (original_property_of_all_manuscript_C1_surfaces HasCertifiedSpinCapGaussMarking
    original_graph_certified_spin_cap_gauss_marking).1

/-- The same marking exists for the normalization of every physical placement
whose single graph is specified outside the manuscript's compact sets. -/
theorem placed_manuscript_C1_certified_spin_cap_gauss_marking :
    AllPlacedManuscriptC1Surfaces HasCertifiedSpinCapGaussMarking :=
  (original_property_of_all_manuscript_C1_surfaces HasCertifiedSpinCapGaussMarking
    original_graph_certified_spin_cap_gauss_marking).2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_C1_certified_spin_cap_gauss_marking
#print axioms TwoAxisHelicoid.placed_manuscript_C1_certified_spin_cap_gauss_marking
