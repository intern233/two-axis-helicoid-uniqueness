import TwoAxisHelicoid.OriginalRegularBallPatches
import TwoAxisHelicoid.RegularPlanarPatchClosedDisk

namespace TwoAxisHelicoid
open Set Metric Topology
open scoped RealInnerProductSpace

/-- Every fixed-radius far ball whose sphere is transverse to the
original surface cuts out closed disks. This applies to every component,
with its actual boundary and interior in the original smooth surface. -/
theorem original_transverse_ball_closed_disks (s : OriginalSmoothHelicoid)
    (R : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) {r : ℝ} (rp : 0<r) :
    let Y := R ∘ s.position
    let X := coordinateToEuclidean ∘ Y
    ∃ T : ℝ, ∀ c : SurfaceEuclideanSpace, T≤‖c‖ →
      (∀ q : s.carrier, dist (X q) c=r → ∃ a : s.carrier, q∈(chartAt ℂ a).source ∧
        ∃ v : ℂ, ⟪coordinateToEuclidean (fderiv ℝ (Y ∘ (chartAt ℂ a).symm) ((chartAt ℂ a) q) v),c-X q⟫≠0) →
      ∀ p : s.carrier, X p∈ball c r →
        let V := connectedComponentIn (X ⁻¹' ball c r) p
        (∀ q∈frontier V, X q∈sphere c r) ∧
        ∃ D : closedBall (0:ℂ) 1 ≃ₜ closure V, ∀ z, z.1∈ball (0:ℂ) 1 ↔ (D z).1∈V := by
  intro Y X
  let _ : LocallyConnectedSpace s.carrier := ChartedSpace.locallyConnectedSpace ℂ _
  let _ : LocallyCompactSpace s.carrier := ChartedSpace.locallyCompactSpace ℂ _
  have proper : IsProperMap X := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp
    (R.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding)).isProperMap
  obtain ⟨j,T,ej,_,cuts⟩ := original_far_ball_components_are_planar s R r
  refine ⟨T,?_⟩
  intro c far transverse p inside V
  obtain ⟨W,ow,cw,kw,outside,image⟩ := cuts c far p inside
  have regular := original_regular_sphere_component_charts s R c rp transverse p
  have ov : IsOpen V := (isOpen_ball.preimage proper.continuous).connectedComponentIn
  have ck := proper.isCompact_preimage (isCompact_closedBall c r)
  have kv : IsCompact (closure V) := ck.of_isClosed_subset isClosed_closure (closure_minimal
    ((connectedComponentIn_subset (X ⁻¹' ball c r) p).trans (preimage_mono ball_subset_closedBall)) ck.isClosed)
  obtain ⟨D,interior⟩ := regular_planar_patch_closed_disk ej OnePoint.isOpenEmbedding_coe ow cw kw outside ov kv image
    (fun q h => by obtain ⟨e,qe,_,side,_,_⟩ := regular q h; exact ⟨e,qe,side⟩)
  exact ⟨fun _ h => component_frontier_lies_on_level (proper.continuous.dist continuous_const) h,D,interior⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_transverse_ball_closed_disks
