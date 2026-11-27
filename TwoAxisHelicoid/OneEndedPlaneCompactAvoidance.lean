import TwoAxisHelicoid.ExteriorHeightEscape
import Mathlib.Topology.Connected.LocallyPathConnected

namespace TwoAxisHelicoid
open Complex Set Topology Metric

/-- Connected tails persist under a change of topological coordinates.
The compact core and the same connected complement are transported
together. -/
theorem connected_compact_tails_homeomorph {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (h : M ≃ₜ N) (tails : HasConnectedCompactTails M) : HasConnectedCompactTails N := by
  intro k compact
  obtain ⟨u,connected,core,away⟩ := tails (h ⁻¹' k) (h.isCompact_preimage.mpr compact)
  refine ⟨h '' u,connected.image _ h.continuous.continuousOn,?_,?_⟩
  · rw [← h.image_compl]
    exact core.image h.continuous
  · apply disjoint_left.mpr
    rintro _ ⟨x,ux,rfl⟩ kx
    exact disjoint_left.mp away ux kx

/-- In an open planar domain with one topological end, every omitted
point can be joined to every sufficiently distant point while avoiding
a prescribed compact subset of the domain. The path stays in the plane.
This conclusion also applies to each open planar embedding of the domain. -/
theorem one_ended_plane_compact_avoidance {V : Set ℂ} (op : IsOpen V) (tails : HasConnectedCompactTails V)
    {K : Set ℂ} (compact : IsCompact K) (inside : K⊆V) (non : K.Nonempty) :
    ∃ R : ℝ, ∀ a∉V, ∀ b : ℂ, R<‖b‖ → JoinedIn Kᶜ a b := by
  let k := (Subtype.val : V → ℂ) ⁻¹' K
  have ck : IsCompact k := Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (by
    rw [show Subtype.val '' k=K by change Subtype.val '' ((Subtype.val : V → ℂ) ⁻¹' K)=K; rw [Subtype.image_preimage_coe,inter_eq_right.mpr inside]]
    exact compact)
  obtain ⟨u,cu,cc,apart⟩ := tails k ck
  let S := (Subtype.val : V → ℂ) '' u
  let B := (Subtype.val : V → ℂ) '' uᶜ
  have cb : IsCompact B := cc.image continuous_subtype_val
  have bs : B⊆V := fun z ⟨w,_,eq⟩ => eq ▸ w.2
  have kb : K⊆B := fun z hz => ⟨⟨z,inside hz⟩,fun m => disjoint_left.mp apart m hz,rfl⟩
  have tail {z : ℂ} (vz : z∈V) (outside : z∉B) : z∈S := by
    let w : V := ⟨z,vz⟩
    exact ⟨w,by by_contra h; exact outside ⟨w,h,rfl⟩,rfl⟩
  have away : S⊆Kᶜ := by
    rintro z ⟨w,wu,rfl⟩ h
    exact disjoint_left.mp apart wu h
  have connected : IsPreconnected S := cu.image _ continuous_subtype_val.continuousOn
  have oc := compact.isClosed.isOpen_compl
  have meet (q : ℂ) (out : q∉B) : ∃ z∈S, z∈connectedComponentIn Kᶜ q := by
    let C := connectedComponentIn Kᶜ q
    have qc : q∈C := mem_connectedComponentIn (fun h => out (kb h))
    have cs : C⊆Kᶜ := connectedComponentIn_subset _ _
    have openC : IsOpen C := oc.connectedComponentIn
    have connC : IsPreconnected C := isPreconnected_connectedComponentIn
    have nonVC : (C∩V).Nonempty := by
      by_contra miss
      have sub : C⊆Vᶜ := fun z hz hv => miss ⟨z,hz,hv⟩
      have sub' : closure C⊆Kᶜ := (closure_minimal sub op.isClosed_compl).trans (compl_subset_compl.mpr inside)
      have cl : IsClosed C := isClosed_of_closure_subset
        (connC.closure.subset_connectedComponentIn (subset_closure qc) sub')
      have all := (isClopen_iff.mp (show IsClopen C from ⟨cl,openC⟩)).resolve_left (nonempty_of_mem qc).ne_empty
      obtain ⟨z,hz⟩ := non
      exact (cs (all ▸ mem_univ z)) hz
    by_contra miss
    have split := isPreconnected_iff_subset_of_disjoint.mp connC V Bᶜ op cb.isClosed.isOpen_compl
      (fun z _ => by by_cases h : z∈B; exact Or.inl (bs h); exact Or.inr h) (by
        apply eq_empty_iff_forall_notMem.mpr
        rintro z ⟨zc,zv,outside⟩
        exact miss ⟨z,tail zv outside,zc⟩)
    rcases split with all|all
    · exact miss ⟨q,tail (all qc) out,qc⟩
    · obtain ⟨z,zc,zv⟩ := nonVC
      exact miss ⟨z,tail zv (all zc),zc⟩
  obtain ⟨R,bd⟩ := cb.isBounded.exists_norm_le
  refine ⟨R,fun a outsidePoint b far => ?_⟩
  have oa : a∉B := fun h => outsidePoint (bs h)
  have ob : b∉B := fun h => far.not_ge (bd b h)
  obtain ⟨z,zs,za⟩ := meet a oa
  obtain ⟨w,ws,wb⟩ := meet b ob
  have eq : connectedComponentIn Kᶜ a=connectedComponentIn Kᶜ b :=
    (connectedComponentIn_eq za).trans ((connectedComponentIn_eq (connected.subset_connectedComponentIn zs away ws)).trans
      (connectedComponentIn_eq wb).symm)
  have qb : b∈connectedComponentIn Kᶜ a := eq ▸ mem_connectedComponentIn (fun h => ob (kb h))
  have qa : a∈connectedComponentIn Kᶜ a := mem_connectedComponentIn (fun h => oa (kb h))
  exact ((oc.connectedComponentIn.isConnected_iff_isPathConnected.mp ⟨⟨a,qa⟩,isPreconnected_connectedComponentIn⟩).joinedIn
    a qa b qb).mono (connectedComponentIn_subset _ _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.connected_compact_tails_homeomorph
#print axioms TwoAxisHelicoid.one_ended_plane_compact_avoidance
