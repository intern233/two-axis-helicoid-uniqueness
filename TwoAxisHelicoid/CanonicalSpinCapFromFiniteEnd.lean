import TwoAxisHelicoid.OriginalTorusSpinUniformization
import TwoAxisHelicoid.FiniteTopologyCanonicalConsequences

namespace TwoAxisHelicoid
open Complex Set Topology

/-- On the original unmarked smooth surface the finite-topology end
input and the two canonical-divisor identities yield the actual
pointed cap with even Arf invariant, the basic branch and the marked
Gauss divisor. This works for each candidate without an existence
input. -/
theorem original_canonical_cap_from_finite_end (bbc : PublishedFiniteOneEndDifferentialGeometry)
    (rr : GenusOneCanonicalDivisorFormula.{0}) (s : OriginalPositionallyAsymptoticHelicoid) :
    HasPointedOriginalSpinBranchCap s ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  obtain ⟨A⟩ := classical_finite_topology_gives_published_one_handle_model bbc s.toOriginalSmoothHelicoid
    s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  have cap := original_pointed_spin_cap_of_torus_uniformization s A (genus_one_period_uniformization_from_canonical_divisor rr _)
  have normal := (pointed_spin_cap_certifies_original s cap).2
  exact ⟨cap,normal,original_pointed_gauss_divisor_of_normalization _ normal⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_canonical_cap_from_finite_end
