import TwoAxisHelicoid.OriginalPointedContactSpin
import TwoAxisHelicoid.CertifiedGlobalEmbeddingFromCertificates
import TwoAxisHelicoid.PlacedGraphPointedConclusion

namespace TwoAxisHelicoid
open Set Topology

/-- Theorem 1.1 in the graph-ended class, using the manuscript winding
and capped-spin selection for every surface and an independently
constructed, globally embedded representative at the certified root. -/
theorem original_graph_one_one_by_contact_and_spin : OriginalGraphTheoremOneOne := by
  have marked := original_graph_cap_by_contact_and_spin
  have image (s : OriginalHelicoidRepresentative) := (pointed_original_embedding_and_similarity
    s.toOriginalSmoothHelicoid (marked s).2.2.1).2
  obtain ⟨s,_⟩ := certified_original_representative_of_injective certified_global_closed_embedding.injective
  exact ⟨unique_spatial_image_class_of_common_model (fun s : OriginalHelicoidRepresentative => s.image)
    (range certifiedTorusImmersion) ⟨s⟩ image,⟨s,Quotient.sound (image s)⟩,certified_global_closed_embedding,
    fun t => ⟨(marked t).1,(marked t).2.2⟩,rfl,rfl,
    by convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper],
    by convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]⟩

theorem placed_graph_one_one_by_contact_and_spin : PlacedGraphTheoremOneOne :=
  placed_pointed_graph_of_normalized original_graph_one_one_by_contact_and_spin

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_one_one_by_contact_and_spin
#print axioms TwoAxisHelicoid.placed_graph_one_one_by_contact_and_spin

