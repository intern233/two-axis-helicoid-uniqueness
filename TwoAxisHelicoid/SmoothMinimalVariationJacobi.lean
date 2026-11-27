import TwoAxisHelicoid.SmoothFamilySpatialJets
import TwoAxisHelicoid.CurvatureJacobiLinearization

namespace TwoAxisHelicoid
open Filter Complex Matrix Topology InnerProductSpace
open scoped Topology ContDiff

/-- Appendix D.1. In an isothermal chart of the central surface, the normal
component of the actual velocity of any jointly C³ family of minimal immersions
satisfies the scalar Jacobi equation. The varying charts need not be isothermal. -/
theorem smooth_minimal_variation_normal_jacobi {F : ℝ → ℂ → Fin 3 → ℝ} {z : ℂ}
    (smooth : ContDiffAt ℝ 3 (fun q : ℝ × ℂ => F q.1 q.2) (0,z))
    (regular : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun p => F 0 p j) w) ∧
      ConformalCoordinateDerivatives (F 0) w ∧ Function.Injective (fderiv ℝ (F 0) w))
    (minimal : ∀ᶠ s in 𝓝 (0:ℝ), coordinateMeanCurvature (F s) z = 0) :
    conformalSurfaceJacobi (F 0)
      (fun w => deriv (fun s => F s w) 0 ⬝ᵥ harmonicChartNormal (F 0) w) z = 0 := by
  obtain ⟨velocity,first,second⟩ := joint_c3_spatial_jet_velocity smooth
  have curvature := derivative_mean_curvature_from_spatial_jets regular velocity first second
  have zero : HasDerivAt (fun s => coordinateMeanCurvature (F s) z) 0 0 :=
    (hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq minimal
  exact (div_eq_zero_iff.mp (curvature.unique zero)).resolve_right (by norm_num)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smooth_minimal_variation_normal_jacobi
