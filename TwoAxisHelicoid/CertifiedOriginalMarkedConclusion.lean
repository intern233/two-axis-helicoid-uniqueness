import TwoAxisHelicoid.CertifiedGlobalEmbeddedHelicoid
import TwoAxisHelicoid.OriginalSpinCapGaussMarking

namespace TwoAxisHelicoid

/-- The quantifiers in the C¹ graph version of Theorem 1.1 can use a single
certified marking per physical surface for the Gauss divisor, the two axes,
the cap and the puncture. The explicitly constructed period solution is
the representative of the unique similarity class. -/
theorem original_graph_one_one_same_marking :
    OriginalGraphTheoremOneOne ∧ ∀ s : OriginalHelicoidRepresentative,
      HasCertifiedSpinCapGaussMarking s.toPositional :=
  ⟨original_graph_pointed_one_one,original_graph_certified_spin_cap_gauss_marking⟩

theorem placed_graph_one_one_same_marking :
    PlacedGraphTheoremOneOne ∧ ∀ s : PlacedGraphHelicoid,
      HasCertifiedSpinCapGaussMarking s.normalizedGraph.toPositional :=
  ⟨placed_graph_pointed_one_one,fun s => original_graph_certified_spin_cap_gauss_marking s.normalizedGraph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_one_one_same_marking
#print axioms TwoAxisHelicoid.placed_graph_one_one_same_marking
