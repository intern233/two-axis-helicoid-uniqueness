import TwoAxisHelicoid.OriginalPointedContactSpin
import TwoAxisHelicoid.CertifiedGlobalEmbeddedHelicoid
import TwoAxisHelicoid.PlacedPositionalJointMarking
import TwoAxisHelicoid.PositionalCurvatureFromDiskEstimate

namespace TwoAxisHelicoid
open Set Topology

private theorem positional_one_one_of_winding_caps
    (caps : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasPointedOriginalSpinBranchCap s) :
    OriginalPositionalTheoremOneOne := by
  have marked (s : OriginalPositionallyAsymptoticHelicoid) :=
    (pointed_spin_cap_certifies_original s (caps s)).2
  obtain ⟨s,_⟩ := certified_original_representative_of_injective certified_global_closed_embedding.injective
  obtain ⟨unique,rep,_⟩ := positional_classification_of_pointed_models marked ⟨s.toPositional⟩
  refine ⟨unique,rep,certified_global_closed_embedding,fun t =>
    ⟨caps t,marked t,original_pointed_gauss_divisor_of_normalization _ (marked t)⟩,rfl,rfl,?_,?_⟩
  · convert certifiedClosedParameters_bounds.1 using 1
    norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1
    norm_num [rootALower,rootAUpper]

/-- The weak positional end and the published finite-topology end
theorem give the manuscript classification by the contact and spin
argument on each original surface. Its certified representative is
constructed by the global spatial embedding proof. -/
theorem positional_contact_spin_from_finite_topology (bbc : PublishedFiniteOneEndDifferentialGeometry) :
    OriginalPositionalTheoremOneOne ∧ PlacedPositionalJointTheoremOneOne := by
  have caps (s : OriginalPositionallyAsymptoticHelicoid) : HasPointedOriginalSpinBranchCap s := by
    obtain ⟨poles⟩ := classical_finite_topology_gives_published_one_handle_model bbc s.toOriginalSmoothHelicoid
      s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
    exact original_pointed_cap_by_contact_and_spin s poles
      (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _)
  have main := positional_one_one_of_winding_caps caps
  exact ⟨main,placed_positional_joint_of_original main⟩

/-- A physical shape bound suffices for exactly the same manuscript
route. The graphification uses the original end, prior to any choice of
the meromorphic data or the integer branch. -/
theorem positional_contact_spin_of_end_shape
    (bounds : ∀ s : OriginalPositionallyAsymptoticHelicoid, HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid) :
    OriginalPositionalTheoremOneOne ∧ PlacedPositionalJointTheoremOneOne := by
  have caps (s : OriginalPositionallyAsymptoticHelicoid) : HasPointedOriginalSpinBranchCap s :=
    (original_graph_cap_by_contact_and_spin (s.graphRepresentative (bounds s))).1
  have main := positional_one_one_of_winding_caps caps
  exact ⟨main,placed_positional_joint_of_original main⟩

theorem positional_contact_spin_from_gaussian_curvature (mp : PublishedFiniteTopologyGaussianCurvature) :
    OriginalPositionalTheoremOneOne ∧ PlacedPositionalJointTheoremOneOne := by
  apply positional_contact_spin_of_end_shape
  intro s
  obtain ⟨C,cp,bd⟩ := original_gaussian_bound_of_finite_topology_publication mp s.toOriginalSmoothHelicoid
  exact original_physical_shape_bound_of_gaussian _ cp bd

theorem positional_contact_spin_from_disk_estimate (cm : OneSidedEmbeddedMinimalDiskEstimate) :
    OriginalPositionalTheoremOneOne ∧ PlacedPositionalJointTheoremOneOne :=
  positional_contact_spin_of_end_shape (positional_end_curvature_from_disk_estimate cm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_contact_spin_from_finite_topology
#print axioms TwoAxisHelicoid.positional_contact_spin_from_gaussian_curvature
#print axioms TwoAxisHelicoid.positional_contact_spin_from_disk_estimate
