import TwoAxisHelicoid.OriginalIntrinsicBallDisks
import TwoAxisHelicoid.OneSidedDiskCurvature

namespace TwoAxisHelicoid
open Set Metric Topology Matrix
open scoped RealInnerProductSpace ContDiff Manifold

/-- One-sided positional approximation to the reference helicoid gives
a uniform end curvature bound using the one-sided minimal disk estimate.
All disk, transversality, component, boundary, and half-space hypotheses
are verified on the original physical surface. -/
theorem positional_end_curvature_from_disk_estimate
    (cm : OneSidedEmbeddedMinimalDiskEstimate) (s : OriginalPositionallyAsymptoticHelicoid) :
    HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid := by
  obtain ⟨ε,ep,estimate⟩ := cm
  let R := centeredHelicoidNormalization s.axes.pitch_ne
  let Y := R ∘ s.position
  let X := coordinateToEuclidean ∘ Y
  obtain ⟨emb,regular,minimal⟩ := physical_frame_regular_minimal s.toOriginalSmoothHelicoid
  have proper : IsProperMap X := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp emb).isProperMap
  let _ : LocallyConnectedSpace s.carrier := ChartedSpace.locallyConnectedSpace ℂ _
  obtain ⟨r,B,rp,balls⟩ := original_exterior_regular_one_sided_balls s ep
  obtain ⟨T,disks⟩ := original_transverse_ball_closed_disks s.toOriginalSmoothHelicoid R
    (r:=2*r) (by positivity)
  let K := X ⁻¹' closedBall 0 (max B (T+r))
  refine ⟨K,r⁻¹,proper.isCompact_preimage (isCompact_closedBall _ _), (inv_pos.mpr rp).le,?_⟩
  intro p away v
  have far : max B (T+r)≤‖X p‖ := (lt_of_not_ge (fun h => away (mem_closedBall_zero_iff.mpr h))).le
  obtain ⟨c,n,unit,near,above,transverse⟩ := balls (X p) (mem_range_self p) ((le_max_left _ _).trans far)
  have near1 : dist (X p) c<r := near.trans_le (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right ε 1) rp.le)
  have nearε : dist (X p) c<ε*r := near.trans_le (mul_le_mul_of_nonneg_right (min_le_left ε 1) rp.le)
  have center : T≤‖c‖ := by
    have h := norm_sub_norm_le (X p) c
    rw [← dist_eq_norm] at h
    linarith [(le_max_right B (T+r)).trans far]
  have inside : X p∈ball c (2*r) := show dist (X p) c<2*r by linarith
  obtain ⟨edge,disk⟩ := disks c center transverse p inside
  let U := X ⁻¹' ball c (2*r)
  let V := connectedComponentIn U p
  have ov : IsOpen V := (isOpen_ball.preimage proper.continuous).connectedComponentIn
  have contained : V⊆U := connectedComponentIn_subset U p
  have subset : closure V⊆X ⁻¹' closedBall c (2*r) := closure_minimal
    (contained.trans (preimage_mono ball_subset_closedBall)) (isClosed_closedBall.preimage proper.continuous)
  have hit : p∈V ∩ X ⁻¹' ball c r := ⟨mem_connectedComponentIn inside,near1⟩
  have hs := estimate s.carrier Y emb regular minimal V c n r rp unit ov contained edge
    (fun q h => transverse q (edge q h)) disk (fun q h => above _ ⟨mem_range_self q,subset h⟩) p hit
    ⟨p,mem_connectedComponentIn hit,nearε⟩
  exact minimal_disk_shape_operator_bound (regular p) ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    (minimal p) (inv_pos.mpr rp).le hs v

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_end_curvature_from_disk_estimate
