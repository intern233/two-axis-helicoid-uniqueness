import TwoAxisHelicoidManuscript

set_option autoImplicit false

open Topology

/-!
Small reproducible statement check for the accompanying paper.
These declarations add no geometric premises to the imported closed theorems.
This is a check of the recorded entrypoint, not a replacement for the full audit.
-/

namespace TwoAxisHelicoid.PaperReview

theorem geometric_statement : ManuscriptGeometricTheoremOneOne :=
  manuscript_geometric_theorem_one_one

theorem normalized_statement : ManuscriptC1TheoremOneOne :=
  manuscript_theorem_one_one

theorem physical_statement : PlacedManuscriptC1TheoremOneOne :=
  placed_manuscript_theorem_one_one

theorem embedded_representative : IsClosedEmbedding certifiedTorusImmersion :=
  certified_global_closed_embedding

theorem spherical_fibers_on_same_cap :
    AllManuscriptC1Surfaces HasMarkedQuotientGaussFibers ∧
    AllPlacedManuscriptC1Surfaces HasMarkedQuotientGaussFibers :=
  manuscript_C1_same_cap_quotient_gauss_fibers

end TwoAxisHelicoid.PaperReview

#print axioms TwoAxisHelicoid.PaperReview.geometric_statement
#print axioms TwoAxisHelicoid.PaperReview.normalized_statement
#print axioms TwoAxisHelicoid.PaperReview.physical_statement
#print axioms TwoAxisHelicoid.PaperReview.embedded_representative
#print axioms TwoAxisHelicoid.PaperReview.spherical_fibers_on_same_cap
