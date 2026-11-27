import TwoAxisHelicoid.OriginalRegularBallPatches
import TwoAxisHelicoid.JordanPatchDisk

namespace TwoAxisHelicoid
open Set Metric Topology
open scoped Topology RealInnerProductSpace

/-- The same distant ball cuts out a compact disk of the original
surface. Its open interior is the entire selected component of the
open ball and its boundary circle is mapped to the cutting sphere. -/
theorem positional_regular_one_sided_disk_patches (circle : CompactRealCurveClassification)
    (schoen : PlanarSchoenfliesTheorem) (s : OriginalPositionallyAsymptoticHelicoid) {ε : ℝ} (ep : 0<ε) :
    let X := coordinateToEuclidean ∘ centeredHelicoidNormalization s.axes.pitch_ne ∘ s.position
    ∃ r B : ℝ, 0<r ∧ ∀ p : s.carrier, B≤‖X p‖ → ∃ c n : SurfaceEuclideanSpace,
      ‖n‖=1 ∧ dist (X p) c<min ε 1*r ∧
      let V := connectedComponentIn (X ⁻¹' ball c (2*r)) p
      p∈V ∧ (∀ q∈closure V, 0<⟪X q-c,n⟫) ∧
      (∀ q∈frontier V, X q∈sphere c (2*r)) ∧
      ∃ D : closedBall (0:ℂ) 1 ≃ₜ closure V, ∀ z, z.1∈ball (0:ℂ) 1 ↔ (D z).1∈V := by
  intro X
  let R := centeredHelicoidNormalization s.axes.pitch_ne
  have proper : IsProperMap X := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp
    (R.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding)).isProperMap
  let _ : LocallyConnectedSpace s.carrier := ChartedSpace.locallyConnectedSpace ℂ _
  let _ : T2Space s.carrier := s.closedEmbedding.isEmbedding.t2Space
  let _ : LocallyCompactSpace s.carrier := ChartedSpace.locallyCompactSpace ℂ _
  obtain ⟨r,B,j,rp,ej,_,all⟩ := positional_one_sided_regular_planar_components s ep
  refine ⟨r,B,rp,?_⟩
  intro p far
  obtain ⟨c,n,unit,near,above,⟨W,ow,cw,kw,outside,eq⟩,regular⟩ := all p far
  let U := X ⁻¹' ball c (2*r)
  let V := connectedComponentIn U p
  have ov : IsOpen V := (isOpen_ball.preimage proper.continuous).connectedComponentIn
  let K := X ⁻¹' closedBall c (2*r)
  have ck : IsCompact K := proper.isCompact_preimage (isCompact_closedBall _ _)
  have vk : closure V⊆K := closure_minimal ((connectedComponentIn_subset U p).trans (preimage_mono ball_subset_closedBall)) ck.isClosed
  have kv : IsCompact (closure V) := ck.of_isClosed_subset isClosed_closure vk
  have model := bounded_planar_cut_boundary_model ej.isEmbedding OnePoint.isOpenEmbedding_coe.isEmbedding
    ow cw kw outside ov kv eq (fun q h => by obtain ⟨e,qe,_,_,_,bdy⟩ := regular q h; exact ⟨e,qe,bdy⟩)
  obtain ⟨boundary,_,atlas,H,image⟩ := model
  obtain ⟨D,interior⟩ := jordan_patch_is_closed_disk circle schoen ow cw.nonempty kw boundary atlas
  have close := near.trans_le (show min ε 1*r≤r by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right ε 1) rp.le)
  exact ⟨c,n,unit,near,mem_connectedComponentIn (show dist (X p) c<2*r by linarith),
    fun q h => above _ ⟨mem_range_self q,vk h⟩,
    fun _ h => component_frontier_lies_on_level (proper.continuous.dist continuous_const) h,
    D.trans H,fun z => (interior z).trans (image (D z)).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_regular_one_sided_disk_patches
