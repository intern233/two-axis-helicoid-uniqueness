import TwoAxisHelicoid.PlaneFillInsideDomain
import TwoAxisHelicoid.ConnectedCompactNeighborhoods
import TwoAxisHelicoid.ConnectedFrontierCompactTail
import TwoAxisHelicoid.ConnectedPlanarFrontier
import TwoAxisHelicoid.BoundedOneEndedPlaneDisk

namespace TwoAxisHelicoid
open Set Metric Bornology Topology

/-- A bounded connected plane domain with connected complement has a
connected tail outside every compact set. The surrounding frontier is
built strictly inside the domain and requires no boundary regularity. -/
theorem bounded_connected_plane_complement_tails {D : Set ℂ} (op : IsOpen D) (conn : IsConnected D)
    (bounded : IsBounded D) (outside : IsPreconnected Dᶜ) : HasConnectedCompactTails D := by
  let _ : LocallyCompactSpace D := op.locallyCompactSpace
  let _ : LocallyConnectedSpace D := op.locallyConnectedSpace
  let _ : PathConnectedSpace D := isPathConnected_iff_pathConnectedSpace.mp (op.isConnected_iff_isPathConnected.mp conn)
  intro K ck
  obtain ⟨z,hz⟩ := conn.nonempty
  obtain ⟨V,vo,vc,vk,_,inside⟩ := compact_in_connected_open_neighborhood (⟨z,hz⟩ : D) ck
  let i := (Subtype.val : D → ℂ)
  let A := i '' V
  let B := i '' closure V
  have openi : IsOpenMap i := op.isOpenEmbedding_subtypeVal.isOpenMap
  have ci : Continuous i := continuous_subtype_val
  have ab : A⊆B := image_mono subset_closure
  have bd : B⊆D := by rintro _ ⟨w,_,rfl⟩; exact w.2
  have kb : IsCompact B := vk.image ci
  obtain ⟨kb',bd'⟩ := boundedPlaneFill_compact_inside kb bd bounded outside
  let F := boundedPlaneFill A
  have all := boundedPlaneFill_properties (kb.isBounded.subset ab)
  have oa : IsOpen A := openi _ vo
  have ca := vc.image i ci.continuousOn
  have fo : IsOpen F := all.2.2.2.1 oa
  have fc : IsConnected F := all.2.2.2.2 oa ca
  have fb : closure F⊆boundedPlaneFill B := closure_minimal (boundedPlaneFill_mono ab) kb'.isClosed
  have cF : IsCompact (closure F) := kb'.of_isClosed_subset isClosed_closure fb
  have inD : closure F⊆D := fb.trans bd'
  have nfull : F≠univ := by
    intro full
    rw [full,closure_univ] at cF
    exact noncompact_univ ℂ cF
  have edge : IsConnected (frontier F) := ⟨nonempty_frontier_iff.mpr ⟨fc.nonempty,nfull⟩,
    connected_open_plane_frontier fo fc.isPreconnected all.2.2.1⟩
  let W := i ⁻¹' F
  have lifted {S : Set ℂ} (inD : S⊆D) : i '' (i ⁻¹' S)=S :=
    image_preimage_eq_of_subset fun x hx => ⟨⟨x,inD hx⟩,rfl⟩
  have fe : i '' frontier W=frontier F := by
    rw [show frontier W=i ⁻¹' frontier F from (openi.preimage_frontier_eq_frontier_preimage ci F).symm]
    exact lifted (frontier_subset_closure.trans inD)
  have cw : IsCompact (closure W) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [show closure W=i ⁻¹' closure F from (openi.preimage_closure_eq_closure_preimage ci F).symm]
    change IsCompact (i '' (i ⁻¹' closure F))
    rwa [lifted inD]
  have imageConnected : IsConnected (i '' frontier W) := fe.symm ▸ edge
  have connectedEdge : IsConnected (frontier W) := ⟨image_nonempty.mp imageConnected.nonempty,
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp imageConnected.isPreconnected⟩
  exact connected_tail_of_enclosing_frontier ck (fun x hx => all.1 (mem_image_of_mem i (inside hx)))
    (fo.preimage ci) cw connectedEdge

/-- The open disk parametrization follows from the proven Riemann
mapping argument on this actual bounded plane domain. -/
theorem bounded_connected_plane_complement_open_disk {D : Set ℂ} (op : IsOpen D) (conn : IsConnected D)
    (bounded : IsBounded D) (outside : IsPreconnected Dᶜ) : Nonempty (D ≃ₜ complexUnitDisk) :=
  bounded_one_ended_plane_open_disk op conn bounded (bounded_connected_plane_complement_tails op conn bounded outside)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_connected_plane_complement_tails
#print axioms TwoAxisHelicoid.bounded_connected_plane_complement_open_disk
