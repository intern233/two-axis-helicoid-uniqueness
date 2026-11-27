import TwoAxisHelicoid.OriginalTransverseEndDisks
import TwoAxisHelicoid.MinimalDiskShapeNorm
import TwoAxisHelicoid.PhysicalMinimalSimilarity

namespace TwoAxisHelicoid
open Set Metric Topology Matrix
open scoped RealInnerProductSpace ContDiff Manifold

/-- Colding--Minicozzi, Annals of Mathematics 160 (2004), Theorem 0.2,
in real charts on a smooth embedded minimal surface. The disk is the
actual compact closure of its indicated open interior. The numerator
below is the squared Hilbert--Schmidt norm on an orthonormal tangent
basis. The intersection with the small ball concerns the same component
of the radius-r portion on which the estimate is asserted. -/
def OneSidedEmbeddedMinimalDiskEstimate : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ,ℂ) ∞ M] (Y : M → Fin 3 → ℝ),
    let X := coordinateToEuclidean ∘ Y
    IsClosedEmbedding Y → (∀ p, RegularImmersionChart Y (chartAt ℂ p)) →
    (∀ p, coordinateMeanCurvature (Y ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)=0) →
    ∀ (V : Set M) (c n : SurfaceEuclideanSpace) (r : ℝ), 0<r → ‖n‖=1 →
      IsOpen V → MapsTo X V (ball c (2*r)) →
      (∀ q∈frontier V, X q∈sphere c (2*r)) →
      (∀ q∈frontier V, ∃ a : M, q∈(chartAt ℂ a).source ∧
        ∃ v : ℂ, ⟪coordinateToEuclidean (fderiv ℝ (Y ∘ (chartAt ℂ a).symm) ((chartAt ℂ a) q) v),c-X q⟫≠0) →
      (∃ H : closedBall (0:ℂ) 1 ≃ₜ closure V, ∀ z, z.1∈ball (0:ℂ) 1 ↔ (H z).1∈V) →
      (∀ q∈closure V, 0<⟪X q-c,n⟫) →
      ∀ p∈V ∩ X ⁻¹' ball c r,
        (connectedComponentIn (V ∩ X ⁻¹' ball c r) p ∩ X ⁻¹' ball c (ε*r)).Nonempty →
        let e := chartAt ℂ p
        let D := fderiv ℝ (Y ∘ e.symm) (e p)
        let N := fderiv ℝ (euclideanUnitChartNormal (Y ∘ e.symm)) (e p)
        ∀ u v : ℂ, D u ⬝ᵥ D u=1 → D v ⬝ᵥ D v=1 → D u ⬝ᵥ D v=0 → ‖N u‖^2+‖N v‖^2≤r⁻¹^2

/-- One-sided positional approximation to the reference helicoid gives
a uniform end curvature bound using the one-sided minimal disk estimate.
All disk, transversality, component, boundary, and half-space hypotheses
are verified on the original physical surface. -/
theorem positional_shape_bound_of_one_sided_disks (schoen : PlanarSchoenfliesTheorem)
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
  obtain ⟨T,disks⟩ := distant_transverse_ball_components_are_disks s.toOriginalSmoothHelicoid R schoen
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
#print axioms TwoAxisHelicoid.positional_shape_bound_of_one_sided_disks
